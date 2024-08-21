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
import org.apache.calcite.tools.{FrameworkConfig, Frameworks, Planner, RelBuilder, RelBuilderFactory}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.jdk.CollectionConverters._
import scala.collection.mutable.HashMap
import upickle.default._

import java.nio.file.{Files, Paths}
import java.io.PrintWriter
import py4j.GatewayServer
import upickle.core.Types

case class JsonOutput(original_query: String, rewritten_query: List[String],
                      features: String, time: Double, acyclic: Boolean)

object JsonOutput {
  implicit val rw: ReadWriter[JsonOutput] = macroRW
}

object QueryRewriter {
  // The state after hypergraph extraction is needed for creating the final output
  private var frameworkConfig: FrameworkConfig = null
  private var planner: Planner = null
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
    frameworkConfig = Frameworks.newConfigBuilder
      .defaultSchema(subSchema)
      .parserConfig(parserConfig)
      .build

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
    planner = Frameworks.getPlanner(frameworkConfig)

    val sqlNode = planner.parse(query)
    val validatedSqlNode = planner.validate(sqlNode)

    // get the logical query plan
    val relRoot = planner.rel(validatedSqlNode)
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

    hg
  }

  case class JSONEdge(name: String, vertices: List[String])
  case class JSONNode(bag: List[String], cover: List[JSONEdge], children: List[JSONNode])

  implicit val edgeRw: ReadWriter[JSONEdge] = macroRW
  implicit val nodeRw: ReadWriter[JSONNode] = macroRW

  def hdStringToHTNode(hdJSON: String): HTNode = {
    def jsonNodeToHTNode(jsonNode: JSONNode): HTNode = {
      jsonNode match {
        case JSONNode(bag, cover, children) => {
          val edges = cover.map(jsonEdge => hg.getEdgeByName(jsonEdge.name).get).toSet
          val childNodes = children.map(jsonNodeToHTNode).toSet

          new HTNode(edges, childNodes, null)
        }
      }
    }

    val jsonNode = read[JSONNode](hdJSON)
    jsonNodeToHTNode(jsonNode)
  }

  def rewriteCyclicJSON(hdJSON: String): String = {
    val ht = hdStringToHTNode(hdJSON)

    rewriteCyclic(ht)
    return ht.treeToString()
  }

  def rewriteCyclic(ht: HTNode): Unit = {

  }

  /**
   * If the query is acyclic, constructs a Yannakakis rewriting.
   * If the query is cyclic, writes out the hypergraph
   * @param query - SQL query string
   */
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

}