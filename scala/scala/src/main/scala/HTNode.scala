import org.apache.calcite.rel.RelNode
import org.apache.calcite.rel.logical.{LogicalFilter, LogicalTableScan}
import org.apache.calcite.rel.rel2sql.RelToSqlConverter
import org.apache.calcite.rex.{RexInputRef, RexNode}
import org.apache.calcite.sql.dialect.Db2SqlDialect

import scala.collection.IterableOnce.iterableOnceExtensionMethods
import scala.jdk.CollectionConverters.CollectionHasAsScala

class HTNode(val edges: Set[HGEdge], var children: Set[HTNode], var parent: HTNode){
  // For each vertex, select one edge in which an attribute it maps to is contained
  val vertexToEdge: Map[RexNode, HGEdge] = edges.flatMap(e => e.vertices)
    .map(v => (v, edges.find(e => e.vertices.contains(v)).get)).toMap
  val vertexToAttribute = vertexToEdge map {case (v, e) => (v, e.vertexToAttribute(v))}

  def vertexName(vertex: RexNode, indexToName: scala.collection.immutable.Map[RexInputRef, String]) = {
    vertexToEdge(vertex).name + "_" + indexToName.getOrElse(vertexToAttribute(vertex).asInstanceOf[RexInputRef], "")
  }

  // Returns just the SELECT query, while getCoverJoin returns the CREATE TABLE statements as well
  def getCoverJoinSelect(indexToName: scala.collection.immutable.Map[RexInputRef, String]): String = {
    val edgeNames = edges.map(e => e.name)
    val edgeNamesStr = edgeNames.toList.mkString(", ")
    val coverJoins = edges.flatMap(e => e.vertices).map(v => {
      val edgesContainingVariable = edges.filter(e => e.vertices.contains(v)).toList
      if (edgesContainingVariable.isEmpty) {
        ""
      }
      else {
        edgesContainingVariable.indices.dropRight(1).map(i => {
          val edge1 = edgesContainingVariable(i)
          val edge2 = edgesContainingVariable(i+1)
          val att1 = edge1.vertexToAttribute(v)
          val att2 = edge2.vertexToAttribute(v)
          val att1Name = indexToName.getOrElse(att1.asInstanceOf[RexInputRef], "")
          val att2Name = indexToName.getOrElse(att2.asInstanceOf[RexInputRef], "")
          f"${edge1.name}_$att1Name = ${edge2.name}_$att2Name"
        }).mkString(" AND ")
      }
    }).filter(s => s.nonEmpty).toList.mkString(" AND ")
    val coverJoinsStr = if (coverJoins.isEmpty) {
      ""
    }
    else {
      f"WHERE $coverJoins"
    }
    val projections = edges.flatMap(e => e.vertices).map(v => vertexName(v, indexToName)).mkString(", ")
    //val coverJoinStr = f"SELECT ${vertexToAttribute.values.mkString(",")} FROM $edgeNamesStr $coverJoinsStr"
    val coverJoinStr = f"SELECT $projections FROM $edgeNamesStr $coverJoinsStr"

    coverJoinStr
  }

  def getCoverJoin(indexToName: scala.collection.immutable.Map[RexInputRef, String]): (String, String) = {
    val coverJoinStr = getCoverJoinSelect(indexToName)

    val joinString = f"CREATE OR REPLACE VIEW $getIdentifier AS $coverJoinStr"
    val dropString = f"DROP VIEW IF EXISTS $getIdentifier"
    (joinString, dropString)
  }

  def getIdentifier(): String = {
    edges.map(e => e.name).toList.sorted.mkString("")
  }

  // get the SQL statements of the bottom up traversal
  def BottomUp(indexToName: scala.collection.immutable.Map[RexInputRef, String], resultString: String,
               dropString: String, projectJoinAttributes: Set[RexNode]): (String, String) = {
    val vertices = edges.flatMap(e => e.vertices) //edge.vertices

    var resultString1 = resultString
    var dropString1 = dropString

    // create semi joins with all children
    var joinIndex = 1
    for (c <- children) {
      //val childEdge = c.edges.head
      val childVertices = c.edges.flatMap(e => e.vertices)//childEdge.vertices
      val overlappingVertices = vertices.intersect(childVertices)

      val cStringOutput = c.BottomUp(indexToName, resultString1, dropString1, projectJoinAttributes)
      resultString1 = cStringOutput._1
      dropString1 = cStringOutput._2

//      val newName = if (edge.nameJoin.contains("stage1_")) {
//        """(E\d+)(_stage1_)(\d+)""".r.replaceAllIn(edge.nameJoin, m => s"${m.group(1)}${m.group(2)}${m.group(3).toInt + 1}")
//      } else {edge.nameJoin + "_stage1_0"}
      val joinSuffix: String = if (joinIndex == children.size) "final" else joinIndex.toString
      val lastName = if (joinIndex == 1) f"${getIdentifier}" else f"${getIdentifier}_stage1_${joinIndex - 1}"
      val newName = f"${getIdentifier}_stage1_$joinSuffix"

      val childIdentifier = if (c.children.nonEmpty) f"${c.getIdentifier}_stage1_final" else c.getIdentifier()
      var result1 = "CREATE UNLOGGED TABLE " + newName + " AS SELECT * FROM " + lastName +
        " WHERE EXISTS (SELECT 1 FROM " + childIdentifier + " WHERE "
      overlappingVertices.foreach { vertex =>
        val att1Name = vertexName(vertex, indexToName)
        val att2Name = c.vertexName(vertex, indexToName)
//        result1 = result1 + getIdentifier() + "." + edge.nameJoin.split("_")(0) + "_" + att1_name +
//          "=" + c.getIdentifier() + "." + childEdge.nameJoin.split("_")(0) + "_" + att2_name + " AND "
        result1 = result1 + lastName + "." + att1Name +
          "=" + childIdentifier + "." + att2Name + " AND "
      }
      result1 = result1.dropRight(5) + ")"
      resultString1 = resultString1 + result1 + "\n"
      dropString1 = "DROP TABLE  IF EXISTS " + newName + "\n" + dropString1
      println("DROP: " + dropString1)
      joinIndex += 1
      //edge.nameJoin = newName
    }
    (resultString1, dropString1)
  }

  // get the SQL statements of the top down traversal
  def TopDown(indexToName: scala.collection.immutable.Map[RexInputRef, String], resultString: String,
              dropString: String): (RelNode, String, String) = {
    val edge = edges.head
    val scanPlan = edge.planReference
    val vertices = edge.vertices
    var prevJoin: RelNode = scanPlan

    var resultString1 = resultString
    var dropString1 = dropString

    // create semi joins with all parents
    for (c <- children) {
      val childEdge = c.edges.head
      val childVertices = childEdge.vertices
      val overlappingVertices = vertices.intersect(childVertices)

      val newName = if (childEdge.nameJoin.contains("stage2_")) {
        """(E\d+)(_stage1_)(\d+)""".r.replaceAllIn(childEdge.nameJoin, m => s"${m.group(1)}${m.group(2)}${m.group(3).toInt + 1}")
      } else {childEdge.nameJoin.replaceAll("""(E\d+)(_stage1_\d+)?""", "$1_stage2_0")}

      var result1 = "CREATE UNLOGGED TABLE " + newName + " AS SELECT * FROM " + childEdge.nameJoin +
        " WHERE EXISTS (SELECT 1 FROM " + edge.nameJoin + " WHERE "
      val joinConditions = overlappingVertices.map { vertex =>
        val att1 = edge.vertexToAttribute(vertex)
        val att2 = childEdge.vertexToAttribute(vertex)
        val att1_name = indexToName.getOrElse(att1.asInstanceOf[RexInputRef], "")
        val att2_name = indexToName.getOrElse(att2.asInstanceOf[RexInputRef], "")
        result1 = result1 + edge.nameJoin + "." + edge.nameJoin.split("_")(0) + "_" + att1_name +
          "=" + childEdge.nameJoin + "." + childEdge.nameJoin.split("_")(0) + "_" + att2_name + " AND "
      }
      childEdge.nameJoin = newName
      result1 = result1.dropRight(5) + ")"
      resultString1 = resultString1 + result1 + "\n"
      dropString1 = "DROP TABLE " + newName + "\n" + dropString1
      val cStringOutput = c.TopDown(indexToName, resultString1, dropString1)
      resultString1 = cStringOutput._2
      dropString1 = cStringOutput._3
      println("DROP: " + dropString1)
    }
    (prevJoin, resultString1, dropString1)
  }

  // get the SQL statements of the bottom up joins
  def BottomUpJoin(indexToName: scala.collection.immutable.Map[RexInputRef, String], tablesString: String,
                   conditionsString: String, projectionString: String, projectAttributes: Set[RexNode],
                   root: Boolean): (RelNode, String, String, String) = {
    val edge = edges.head
    val scanPlan = edge.planReference
    val vertices = edge.vertices
    var prevJoin: RelNode = scanPlan

    var tables = tablesString
    var conditions = conditionsString
    var projections = projectionString

    if (root) {
      tables = tables + edge.nameJoin + ", "

      val planReferenceAttributes = edge.planReference.getRowType.getFieldList
      val tableAttributes = planReferenceAttributes.asScala.map { case att =>
        var index = att.getIndex + edge.attIndex
        edge.attributes(index)
      }.toSet
      val projection = tableAttributes.intersect(projectAttributes).map { vertex =>
        val att1 = edge.vertexToAttribute.getOrElse(vertex, vertex)
        val att1_name = indexToName.getOrElse(att1.asInstanceOf[RexInputRef], "")
        edge.nameJoin + "."  + edge.name + "_" + att1_name + " AS " + edge.name + "_" + att1_name
      }.mkString(", ")
      projections = projections + projection + (if (projection.nonEmpty) ", " else "")
    }

    // create joins with all children
    for (c <- children) {
      val childEdge = c.edges.head
      tables = tables + childEdge.nameJoin + ", "

      val planReferenceAttributes = childEdge.planReference.getRowType.getFieldList
      val tableAttributes = planReferenceAttributes.asScala.map { case att =>
        var index = att.getIndex + childEdge.attIndex
        childEdge.attributes(index)
      }.toSet
      val projection = tableAttributes.intersect(projectAttributes).map { vertex =>
        val att1 = childEdge.vertexToAttribute.getOrElse(vertex, vertex)
        val att1_name = indexToName.getOrElse(att1.asInstanceOf[RexInputRef], "")
        childEdge.nameJoin + "." + childEdge.name + "_" + att1_name + " AS " + childEdge.name + "_" + att1_name
      }.mkString(", ")
      projections = projections + projection + (if (projection.nonEmpty) ", " else "")

      val childVertices = childEdge.vertices
      val overlappingVertices = vertices.intersect(childVertices)

      val cStringOutput = c.BottomUpJoin(indexToName, tables, conditions, projections, projectAttributes, false)
      conditions = cStringOutput._3
      tables = cStringOutput._2

      val joinConditions = overlappingVertices.map { vertex =>
        val att1 = edge.vertexToAttribute(vertex)
        val att2 = childEdge.vertexToAttribute(vertex)
        val att1_name = indexToName.getOrElse(att1.asInstanceOf[RexInputRef], "")
        val att2_name = indexToName.getOrElse(att2.asInstanceOf[RexInputRef], "")
        conditions = conditions + edge.nameJoin + "." + edge.nameJoin.split("_")(0) + "_" + att1_name +
          "=" + childEdge.nameJoin + "." + childEdge.nameJoin.split("_")(0) + "_" + att2_name + " AND "
      }
    }
    (prevJoin, tables, conditions, projections)
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
    //val e = edges.head
    // val nodeAttributes = e.planReference.getRowType.getFieldList


//    nodeAttributes.forEach { case x =>
//      var index = x.getIndex + e.attIndex
//      var key = e.attributes(index)
//      nodeAtt = nodeAtt :+ e.attributeToVertex.getOrElse(key, key)
//    }
    edges.foreach(e => {
      val nodeAttributes = e.planReference.getRowType.getFieldList
      nodeAttributes.forEach { x =>
        var index = x.getIndex + e.attIndex
        var key = e.attributes(index)
        nodeAtt = nodeAtt :+ e.attributeToVertex.getOrElse(key, key)
      }
      // TODO is this necessary
      aggAtt = aggAttributes.map(key => e.attributeToVertex.getOrElse(key, key))
    })


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

  def getAllNodes: List[HTNode] = {
    return List(this) ++ children.flatMap(c => c.getAllNodes)
  }

  // set references between child-parent relationships in the tree
  def setParentReferences: Unit = {
    for (c <- children) {
      c.parent = this
      c.setParentReferences
    }
  }

  def appendContainedEdges(hg: Hypergraph): HTNode = {
    val vertices = edges.flatMap(_.vertices)
    val newChildren = children.map(_.appendContainedEdges(hg)) ++
      hg.edges.filter(e => (e.vertices subsetOf vertices) && !edges.exists(e2 => e2.name.equals(e.name)))
        .map(e => new HTNode(Set(e), Set(), null))
    val newNode = copy(newChildren = newChildren)
    newNode
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