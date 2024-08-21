import org.apache.calcite.rel.RelNode
import org.apache.calcite.rel.logical.{LogicalFilter, LogicalTableScan}
import org.apache.calcite.rel.rel2sql.RelToSqlConverter
import org.apache.calcite.rex.{RexInputRef, RexNode}
import org.apache.calcite.sql.dialect.Db2SqlDialect

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