import java.sql.{Connection, DriverManager}
import java.util.Properties
import org.apache.calcite.adapter.jdbc.JdbcSchema
import org.apache.calcite.jdbc.CalciteConnection
import org.apache.calcite.plan.RelOptUtil
import org.apache.calcite.plan.hep.HepPlanner
import org.apache.calcite.plan.hep.HepProgramBuilder
import org.apache.calcite.rel.core.Join
import org.apache.calcite.rel.logical.LogicalAggregate
import org.apache.calcite.rel.logical.LogicalFilter
import org.apache.calcite.rel.logical.LogicalProject
import org.apache.calcite.rel.logical.LogicalTableScan
import org.apache.calcite.rel.rel2sql.RelToSqlConverter
import org.apache.calcite.rel.RelNode
import org.apache.calcite.rel.rules.FilterJoinRule
import org.apache.calcite.rex._
import org.apache.calcite.sql.dialect.Db2SqlDialect
import org.apache.calcite.sql.parser.SqlParser
import org.apache.calcite.sql.SqlKind
import org.apache.calcite.tools.{Frameworks, Planner, RelBuilder, RelBuilderFactory}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.jdk.CollectionConverters._
import scala.collection.mutable.HashMap
import upickle.default._

import java.nio.file.{Files, Paths}
import java.io.PrintWriter
import py4j.GatewayServer

case class JsonOutput(original_query: String, rewritten_query: List[String],
                      features: String, time: Double, acyclic: Boolean)
object JsonOutput {
  implicit val rw: ReadWriter[JsonOutput] = macroRW
}

object QueryRewriter {
  private var planner: Option[Planner] = None

  // The state after hypergraph extraction is needed for creating the final output
  private var schemaName: String = null
  private var hg: Hypergraph = null
  private var aggAttributes: Seq[RexNode] = null
  private var indexToName: Map[RexInputRef, String] = null
  private var relNodeFiltered: RelNode = null
  private var attributes: Seq[RexInputRef] = null
  private var items: Seq[RelNode] = null

  private val gatewayServer: GatewayServer = new GatewayServer(this)

  def connect(jdbcUrl: String, schemaName: String, jdbcUser: String, jdbcPassword: String): Unit = {
    // connect to the postgresql database
    val connection = DriverManager.getConnection("jdbc:calcite:")
    // val connection = DriverManager.getConnection("jdbc:calcite:", info)
    val calciteConnection = connection.unwrap(classOf[CalciteConnection])
    val rootSchema = calciteConnection.getRootSchema
    // val ds = JdbcSchema.dataSource("jdbc:postgresql://localhost:5432/stats", "org.postgresql.Driver", "stats", "stats")
    val ds = JdbcSchema.dataSource(jdbcUrl, "org.postgresql.Driver", jdbcUser, jdbcPassword)
    rootSchema.add(schemaName, JdbcSchema.create(rootSchema, schemaName, ds, null, null))

    val outputDir = "output"

    print(rootSchema)
    // build a framework for the schema the query corresponds to
    val subSchema = rootSchema.getSubSchema(schemaName)
    val parserConfig = SqlParser.Config.DEFAULT.withCaseSensitive(false)
    val config = Frameworks.newConfigBuilder
      .defaultSchema(subSchema)
      .parserConfig(parserConfig)
      .build

    planner = Option(Frameworks.getPlanner(config))
    this.schemaName = schemaName
  }

  def main(args: Array[String]): Unit = {
    Class.forName("org.apache.calcite.jdbc.Driver")
    // use the schema information and file locations specified in model.json
    // val info = new Properties
    // info.put("model", "model.json")


    if (args.length >= 4) {
      val jdbcUrl = args(0)
      val schemaName = args(1)
      val jdbcUser = args(2)
      val jdbcPassword = args(3)

      connect(jdbcUrl, schemaName, jdbcUser, jdbcPassword)

      if (args.length == 5) {
        val query = args(4)
        rewrite(query)
      }
    }

    gatewayServer.start
    println("Py4j server started")
  }

  def stopServer(): Unit = {
    gatewayServer.shutdown()
  }

  def getHypergraph(query: String): Hypergraph = {
    assert(planner.nonEmpty)

    val sqlNode = planner.get.parse(query)
    val validatedSqlNode = planner.get.validate(sqlNode)

    // get the logical query plan
    val relRoot = planner.get.rel(validatedSqlNode)
    val relNode = relRoot.project

    // push the filters in the logical query plan down
    relNodeFiltered = pushDownFilters(relNode)
    // print the logical query plan as string
    val relNodeString = RelOptUtil.toString(relNodeFiltered)
    println(relNodeString)

    // get the references for all attributes
    val att = mutable.Set[RexInputRef]()
    extractInputRefsRecursive(relNode, att)
    att.toSet
    attributes = att.toSeq
    println("attributes: " + attributes)

    // get the aggregation attributes
    aggAttributes = relNodeFiltered match {
      case aggregate: LogicalAggregate =>
        val input = aggregate.getInput
        val aggCalls = aggregate.getAggCallList.asScala
        val hasNonCountAgg = aggCalls.exists(_.getAggregation.getName != "COUNT")
        if (hasNonCountAgg) {
          input match {
            case project: LogicalProject => project.getProjects.asScala.toSeq
            case _ => Seq.empty
          }
        } else { // count(*) case
          Seq.empty
        }
      case _ => // no aggregate case
        Seq.empty
    }
    println("aggAttributes: " + aggAttributes)

    // extract all items and conditions of the joins in the logical plan
    val (items, conditions) = extractInnerJoins(relNodeFiltered)
    this.items = items
    //println("items: " + items)
    println("conditions: " + conditions)

    // get the column names for each attribute index
    val names = items.flatMap { i =>
      val fieldNames = i.getRowType().getFieldNames().asScala.toList
      fieldNames
    }
    indexToName = attributes.zip(names).toMap
    //println("indexToName: " + indexToName)

    // build the hypergraph
    hg = new Hypergraph(items, conditions, attributes)

    return hg
  }

  def rewrite(query: String): Unit = {
    val startTime = System.nanoTime()

    getHypergraph(query)

    // calculate the join tree
    val jointree = hg.flatGYO

    val resultsDir = "output"
    Files.createDirectories(Paths.get(resultsDir))

    def writeResults(fileName: String, content: String) = {
      val filePath = resultsDir + "/" + fileName
      val filewriter = new PrintWriter(filePath)
      filewriter.print(content)
      filewriter.close()
    }

    writeResults("hypergraph.txt", hg.toString)

    // there is no jointree, the query is cyclic
    if (jointree == null) {
      println("join is cyclic")
      val jsonOutput = JsonOutput(query, null, null, 0, false)
      val json: String = write(jsonOutput)
      writeResults("output.json", json.toString)
    }
    else {
      // First check if there is a single tree node, i.e., relation that contains all attributes
      // contained in the aggregate functions -> Query 0MA
      if (aggAttributes.isEmpty){
        println("query has no attributes")
      }
      else {
        val findNodeContainingAttributes = jointree.findNodeContainingAttributes(aggAttributes)
        val nodeContainingAttributes = findNodeContainingAttributes._1
        println("nodeContaining: " + nodeContainingAttributes)
        aggAttributes = findNodeContainingAttributes._2
        println("aggAttofRoot: " + aggAttributes)

        if (nodeContainingAttributes == null) {
          println("query is not 0MA")
        }
        else {
          println("query is 0MA")

          // reroot the tree, such that the root contains all attributes
          val root = nodeContainingAttributes.reroot
          println("new root: " + root + " b: " + root.edges.head.planReference.getRowType)

          // get the aggregate, which are applied at the end on the rerooted root
          val stringAtt = aggAttributes.map{a => indexToName(a.asInstanceOf[RexInputRef])}
          val allAgg: String = relNodeFiltered match {
            case aggregate: LogicalAggregate =>
              val namedAggCalls = aggregate.getNamedAggCalls.asScala
              val zippedResults = namedAggCalls.zip(stringAtt)
              val formattedAgg = zippedResults.map { case (aggCall, att) =>
                val aggStr = aggCall.left.getAggregation
                val name = aggCall.left.name
                s"$aggStr($att) AS $name"
              }
              formattedAgg.mkString(", ")
          }

          // Get the output strings for the Bottom Up traversal
          var resultString = ""
          var dropString = ""
          val stringOutput = root.BottomUp(indexToName, resultString, dropString)
          val stringForJson = stringOutput._2.replace(schemaName + ".", "")
          val listForJson = stringForJson.split("\n").toList

          // add the aggregate to the last CREATE
          val listForJsonLast = listForJson.last
          val modifiedLastString = listForJsonLast.replace("*", allAgg)
          val listForJsonAgg = listForJson.init :+ modifiedLastString

          // write a SELECT of the final table
          val keyword = "TABLE "
          val substringAfterKeyword = listForJsonLast.substring(listForJsonLast.indexOf(keyword) + keyword.length)
          val table = substringAfterKeyword.split("\\s+").headOption.getOrElse("")
          table.trim
          val selectString = "SELECT * FROM " + table

          val finalList = listForJsonAgg ++ List(selectString)
          // val finalList = listForJsonAgg ++ List(selectString) ++ listDrop

          // stop the time for the whole program in seconds and give it to the json
          val endTime = System.nanoTime()
          val executionTime = (endTime - startTime) / 1e9

          /// for the column Date, we needed \\\"Date\\\" for this scala, but now we want Date again
          val original = query.replace("\"Date\"", "Date")

          // GET FEATURES OF THE JOIN TREE
          // get the tree depth
          var treeDepth = root.getTreeDepth(root,0)
          println("depth: " + treeDepth)
          // get the item lifetimes
          var containerCounts = root.getContainerCount(hg.getEquivalenceClasses, attributes)
          println("container counts: " + containerCounts)
          // get the branching factor
          var branchingFactors = root.getBranchingFactors(root)
          println("branching factors: " + branchingFactors)
          // get the balancedness factor
          var balancednessFactors = root.getBalancednessFactors(root)
          var balancednessFactor = balancednessFactors._2.sum / balancednessFactors._2.length
          println("balancedness factor: " + balancednessFactors + "  " + balancednessFactor)
          // save all features in one list
          var features = List(treeDepth, containerCounts, branchingFactors, balancednessFactor).toString



          // write a txt file with a visulization of the join tree
          println(root.treeToString(0))
          writeResults("jointree.txt", root.treeToString(0))

          // GET THE HYPERGRAPH REPRESENTATION
          var edgeStart = 0
          val edgeResult = ListBuffer[List[String]]()
          for (i <- items) {
            val edgeCount = i.getRowType().getFieldCount()
            var edgeAtt = attributes.slice(edgeStart,edgeStart + edgeCount)
            val edgeKeys = edgeAtt.map{ e =>
              val keyString = root.edges.head.attributeToVertex.getOrElse(e, e).toString.tail
              keyString
            }
            edgeResult += edgeKeys.toList
            edgeStart = edgeStart + edgeCount
          }
          println("hypergraph representation: " + edgeStart + " " + edgeResult.toString)
          // write a txt file with the edges and the number of vertices of the hypergraph

          // write a json file with the original and the rewritten query

          val jsonOutput = JsonOutput(original, finalList, features, executionTime, true)
          val json: String = write(jsonOutput)
          writeResults("output.json", json.toString)

          // write a file, which makes dropping the tables after creating them easy
          val listDrop = stringOutput._3.split("\n").toList
          val jsonOutputDrop = JsonOutput("", listDrop, "", 0, true)
          val jsonDrop: String = write(jsonOutputDrop)
          writeResults("drop.json", jsonDrop.toString)
        }
      }
    }
  }

  // define the function, which pushes the filters down
  private def pushDownFilters(root: RelNode): RelNode = {
    val f: RelBuilderFactory = RelBuilder.proto()
    val programBuilder = new HepProgramBuilder
    programBuilder.addRuleInstance(new FilterJoinRule.FilterIntoJoinRule(true, f, FilterJoinRule.TRUE_PREDICATE))
    programBuilder.addRuleInstance(new FilterJoinRule.JoinConditionPushRule(f, FilterJoinRule.TRUE_PREDICATE))
    val program = programBuilder.build
    val planner = new HepPlanner(program)
    planner.setRoot(root)
    planner.findBestExp
  }

  // helper function for extracteInnerJoins, which splits the conjunctive predicates
  def splitConjunctivePredicates(condition: RexNode): Seq[RexNode] = condition match {
    case call: RexCall if call.getKind == SqlKind.AND =>
      val left = call.getOperands.get(0)
      val right = call.getOperands.get(1)
      splitConjunctivePredicates(left) ++ splitConjunctivePredicates(right)
    case predicate if predicate.getKind == SqlKind.EQUALS =>
      Seq(predicate)
    case _ => Seq.empty[RexNode]
  }

  // get the RexInputRefs for all attributes
  private def extractInputRefsRecursive(relNode: RelNode, inputRefs: mutable.Set[RexInputRef]): Unit = {
    val rowType = relNode.getRowType
    val fieldCount = rowType.getFieldCount
    for (i <- 0 until fieldCount) {
      val inputRef = new RexInputRef(i, rowType)
      inputRefs.add(inputRef)
    }
    relNode.getInputs.asScala.foreach { child =>
      extractInputRefsRecursive(child, inputRefs)
    }
  }

  //Extracts items of consecutive inner joins and join conditions
  def extractInnerJoins(plan: RelNode): (Seq[RelNode], Seq[RexNode]) = {
    plan match {
      case join: Join if join.getJoinType == org.apache.calcite.rel.core.JoinRelType.INNER =>
        val left = join.getLeft
        val right = join.getRight
        val cond = join.getCondition
        val (leftPlans, leftConditions) = extractInnerJoins(left)
        val (rightPlans, rightConditions) = extractInnerJoins(right)
        (leftPlans ++ rightPlans, leftConditions ++ rightConditions ++ splitConjunctivePredicates(cond))
      case project: LogicalProject =>
        val input = project.getInput
        val (childPlans, childConditions) = extractInnerJoins(input)
        (childPlans, childConditions)
      case aggregate: LogicalAggregate =>
        val input = aggregate.getInput
        val (childPlans, childConditions) = extractInnerJoins(input)
        (childPlans, childConditions)
      case x =>
        (Seq(plan), Seq.empty[RexNode])
    }
  }

  // define a class for hypergraph edges
  class HGEdge(val vertices: Set[RexNode], var name: String, var nameJoin: String, val planReference: RelNode,
               val attributeToVertex: mutable.Map[RexNode, RexNode], val attIndex: Int,
               val attributes: Seq[RexNode]){

    // get a map between the vertices and attributes
    val vertexToAttribute = HashMap[RexNode, RexNode]()
    val planReferenceAttributes = planReference.getRowType.getFieldList
    planReferenceAttributes.forEach { case att =>
      var index = att.getIndex + attIndex
      var key = attributes(index)
      val keyString = attributeToVertex.getOrElse(key, null)
      val valueString = key
      if (keyString != null) vertexToAttribute.put(keyString, valueString)
    }
    //println("vertexToAttribute: " + vertexToAttribute)

    // check if the vertices of an edge occur in the vertices of another edge
    def contains(other: HGEdge): Boolean = {
      other.vertices subsetOf vertices
    }

    // check if the vertices of two edges are different
    def containsNotEqual(other: HGEdge): Boolean = {
      contains(other) && !(vertices subsetOf other.vertices)
    }

    def copy(newVertices: Set[RexNode] = vertices,
             newName: String = name,
             newPlanReference: RelNode = planReference): HGEdge =
      new HGEdge(newVertices, newName, newName, newPlanReference, attributeToVertex, attIndex, attributes)

    override def toString: String = s"""${name}(${vertices.mkString(", ")})"""
  }

  // define a class for hypertree nodes
  class HTNode(val edges: Set[HGEdge], var children: Set[HTNode], var parent: HTNode){

    // get the SQL statements of the bottom up traversal
    def BottomUp(indexToName: scala.collection.immutable.Map[RexInputRef, String], resultString: String,
                 dropString: String): (RelNode, String, String) = {
      val edge = edges.head
      val scanPlan = edge.planReference
      val vertices = edge.vertices
      var prevJoin: RelNode = scanPlan

      // create the filtered single tables
      val dialect = Db2SqlDialect.DEFAULT
      val relToSqlConverter = new RelToSqlConverter(dialect)
      val res = relToSqlConverter.visitRoot(scanPlan)
      val sqlNode1 = res.asQueryOrValues()
      var result = sqlNode1.toSqlString(dialect, false).getSql()
      result = "CREATE VIEW " + edge.name + " AS " + result
      var resultString1 = resultString + result.replace("\n", " ") + "\n"
      var dropString1 = "DROP VIEW " + edge.name + "\n" + dropString

      // create semi joins with all children
      for (c <- children) {
        val childEdge = c.edges.head
        val childVertices = childEdge.vertices
        val overlappingVertices = vertices.intersect(childVertices)

        val cStringOutput = c.BottomUp(indexToName, resultString1, dropString1)
        resultString1 = cStringOutput._2
        dropString1 = cStringOutput._3
        val newName = edge.nameJoin + childEdge.nameJoin
        var result1 = "CREATE UNLOGGED TABLE " + newName + " AS SELECT * FROM " + edge.nameJoin +
          " WHERE EXISTS (SELECT 1 FROM " + childEdge.nameJoin + " WHERE "
        val joinConditions = overlappingVertices.map { vertex =>
          val att1 = edge.vertexToAttribute(vertex)
          val att2 = childEdge.vertexToAttribute(vertex)
          val att1_name = indexToName.getOrElse(att1.asInstanceOf[RexInputRef], "")
          val att2_name = indexToName.getOrElse(att2.asInstanceOf[RexInputRef], "")
          result1 = result1 + edge.nameJoin + "." + att1_name + "=" + childEdge.nameJoin + "." + att2_name + " AND "
        }
        result1 = result1.dropRight(5) + ")"
        resultString1 = resultString1 + result1 + "\n"
        dropString1 = "DROP TABLE " + newName + "\n" + dropString1
        edge.nameJoin = newName
        childEdge.nameJoin = newName
      }
      (prevJoin, resultString1, dropString1)
    }

    // define a given root as the new root of the tree
    def reroot: HTNode = {
      if (parent == null) {
        this
      } else {
        var current = this
        var newCurrent = this.copy(newParent = null)
        val root = newCurrent
        while (current.parent != null) {
          val p = current.parent
          val newChild = p.copy(newChildren = p.children - current, newParent = null)
          newCurrent.children += newChild
          current = p
          newCurrent = newChild
        }
        root.setParentReferences
        root
      }
    }

    // check if there is a node containing all aggregation attributes (and find it)
    def findNodeContainingAttributes(aggAttributes: Seq[RexNode]): (HTNode, Seq[RexNode]) = {
      var aggAtt = Seq[RexNode]()
      var nodeAtt = List[RexNode]()

      // get the node attributes and the agg attributes, with the same mappings
      val e = edges.head
      val nodeAttributes = e.planReference.getRowType.getFieldList
      nodeAttributes.forEach { case x =>
        var index = x.getIndex + e.attIndex
        var key = e.attributes(index)
        nodeAtt = nodeAtt :+ e.attributeToVertex.getOrElse(key, key)
      }
      aggAtt = aggAttributes.map(key => e.attributeToVertex.getOrElse(key, key))

      // Check if all aggregates are present in this node
      val allInSet = aggAtt.forall(nodeAtt.contains)

      if (allInSet) {
        println("All elements are present in " + this)
        aggAtt = aggAtt.map{a => edges.head.vertexToAttribute.getOrElse(a,a)}
        (this, aggAtt)
      } else {
        for (c <- children) {
          val node = c.findNodeContainingAttributes(aggAttributes)
          if (node != null) {
            return node
          }
        }
        null
      }
    }

    // set references between child-parent relationships in the tree
    def setParentReferences: Unit = {
      for (c <- children) {
        c.parent = this
        c.setParentReferences
      }
    }

    // get the join tree's depth
    def getTreeDepth(root: HTNode, depth: Int): Int = {
      if (root.children.isEmpty) {
        depth
      } else {
        root.children.map(c => getTreeDepth(c, depth + 1)).max
      }
    }

    // get a list of the item lifetimes of all attributes in the join tree
    def getContainerCount(equivalenceClasses: Set[Set[RexNode]], attributes: Seq[RexNode]): List[Int] = {
      // number of the items, which occure several times, are those being joined on
      // how often they appear can be retrived of the size of their equivalence class
      var containerCount = equivalenceClasses.map(_.size).toList
      // the number of attributes only occuring once, are the number of all attribute minus
        // the attributes occuring more often
      val occuringOnce = attributes.size - containerCount.sum
      val occuringOnceList = List.fill(occuringOnce)(1)
      containerCount = occuringOnceList ::: containerCount
      containerCount.sorted
    }

    // get the branching factors of the join tree
    def getBranchingFactors(root: HTNode): List[Int] = {
      if (root.children.isEmpty) {
        List.empty[Int]
      } else {
        var sizes = List.empty[Int]
        for (child <- root.children) {
          sizes = sizes ++ getBranchingFactors(child)
        }
        sizes ::: List(root.children.size)
      }
    }

    // get the balancedness factor of the join tree
    def getBalancednessFactors(root: HTNode): (Int, List[Double]) = {
      if (root.children.isEmpty){
        return (0, List.empty[Double])
      } else if (root.children.size == 1){
        val balanceOneChild = getBalancednessFactors(root.children.head)
        return (balanceOneChild._1, balanceOneChild._2)
      } else {
        val childrenResults = root.children.toList.map(c => getBalancednessFactors(c))
        val firstElements = childrenResults.map(_._1).map(_ + 1)
        val secondElements = childrenResults.map(_._2)
        val combinedSecondElements = secondElements.flatten
        val elementsCount = firstElements.sum
        val balancedness = firstElements.min.toDouble / firstElements.max
        return (elementsCount, combinedSecondElements ::: List(balancedness))
      }
    }

    def copy(newEdges: Set[HGEdge] = edges, newChildren: Set[HTNode] = children,
             newParent: HTNode = parent): HTNode =
      new HTNode(newEdges, newChildren, newParent)

    // define a function to be able to print the join tree
    def treeToString(level: Int = 0): String = {
      s"""${"-- ".repeat(level)}TreeNode(${edges})""" +
        s"""[${edges.map {
          case e if e.planReference.isInstanceOf[LogicalTableScan] =>
            e.planReference.getTable.getQualifiedName
          case e if e.planReference.isInstanceOf[LogicalFilter] =>
            e.planReference.getInputs.get(0).getTable.getQualifiedName
          case _ => "_"
        }}] [[parent: ${parent != null}]]
           |${children.map(c => c.treeToString(level + 1)).mkString("\n")}""".stripMargin
    }

    //override def toString: String = toString(0)
  }
}