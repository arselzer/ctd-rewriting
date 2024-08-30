import org.apache.calcite.rel.RelNode
import org.apache.calcite.rel.rel2sql.RelToSqlConverter
import org.apache.calcite.rex.{RexCall, RexInputRef, RexNode}
import org.apache.calcite.sql.SqlKind
import org.apache.calcite.sql.dialect.Db2SqlDialect
import org.apache.calcite.sql.fun.SqlStdOperatorTable

import scala.collection.mutable
import scala.jdk.CollectionConverters._

class Hypergraph(private val items: Seq[RelNode], private val conditions: Seq[RexNode],
                   private val attributes: Seq[RexNode]){
                   //private val att_map: HashMap[String, String]) {
    val vertices: mutable.Set[RexNode] = mutable.Set.empty
    val edges: mutable.Set[HGEdge] = mutable.Set.empty
    private val attributeToVertex: mutable.Map[RexNode, RexNode] = mutable.Map.empty
    private var equivalenceClasses: Set[Set[RexNode]] = Set.empty

    // Get the actual join attribute, which might be contained
    // in a CAST statement (RexCall)
    def getAttribute(node: RexNode): RexNode = {
      node match {
        case n: RexCall => {
          n.getOperands.asScala.map(o => getAttribute(o))
            .filter(o => o != null).head
        }
        case n: RexInputRef => {
          n
        }
        case _ => null
      }
    }

    // add all equality conditions to the equivalence classes
    for (cond <- conditions) {
      cond match {
        case call: RexCall if call.getOperator == SqlStdOperatorTable.EQUALS =>
          val operands = call.getOperands.asScala.toList
          if (operands.size == 2) {
            val lAtt = getAttribute(operands.head)
            val rAtt = getAttribute(operands(1))
            equivalenceClasses += Set(lAtt, rAtt)
          }
        case _ => println("other")
      }
    }

    // combine all pairs with common columns/attributes
    // e.g. (col1, col2),(col1, col3),(col4,col5) -> (col1, col2, col3),(col4,col5)
    while (combineEquivalenceClasses) {}
    println("combined equivalence classes: " + equivalenceClasses)

    // design an efficient mapping between the attributes and vertices
    // e.g. vertexToAttributes: col1 -> (col1,col2,col3); col4 -> (col4,col5)
    //      attributeToVertex: col1->col1, col2->col1, col3->col1, col4->col4, col5->col4
    for (equivalenceClass <- equivalenceClasses) {
      val attName = equivalenceClass.head
      vertices.add(attName)
      for (equivAtt <- equivalenceClass) {
        attributeToVertex.put(equivAtt, attName)
      }
    }
    println("attribute to vertex mapping: " + attributeToVertex)

    var tableIndex = 1
    var attIndex = 0
    // iterate over all subtrees
    for (item <- items) {
      //println("join item: " + item)

      // get the attributes for this subtree
      // check if it is in the attributeToVertex list and get consistent naming
      val projectAttributes = item.getRowType.getFieldList
      //println("projectAttributes: " + projectAttributes)

      var projectAtt = List[RexNode]()
      projectAttributes.forEach { case x =>
        var index = x.getIndex + attIndex
        var key = attributes(index)
        projectAtt = projectAtt :+ attributeToVertex.getOrElse(key, null)
        //projectAtt = projectAtt :+ attributeToVertex.getOrElse(key, key)
      }

      // get the hyperedges (were join partners have the same name now)
      val hyperedgeVertices = projectAtt.filter(_ != null).toSet
      val hyperedge = new HGEdge(hyperedgeVertices, s"E${tableIndex}", s"E${tableIndex}", item, attributeToVertex, attIndex, attributes)
      //println("hyperedge: " + hyperedge)
      tableIndex += 1
      attIndex += projectAttributes.size
      //println("he: " + hyperedge + hyperedge.planReference.getTable)
      edges.add(hyperedge)
    }
    println("hyperedges: " + edges)

    // helper function to combine all pairs with common columns
    private def combineEquivalenceClasses: Boolean = {
      for (set <- equivalenceClasses) {
        for (otherSet <- equivalenceClasses - set) {
          if ((set intersect otherSet).nonEmpty) {
            val unionSet = (set union otherSet)
            equivalenceClasses -= set
            equivalenceClasses -= otherSet
            equivalenceClasses += unionSet
            return true
          }
        }
      }
      false
    }

    // get the equivalence classes
    def getEquivalenceClasses: Set[Set[RexNode]] = equivalenceClasses

    // check if the query is acyclic (<=> having a join tree)
    def isAcyclic: Boolean = {
      flatGYO == null
    }

    // compute the join tree
    def flatGYO: HTNode = {
      var gyoEdges: mutable.Set[HGEdge] = mutable.Set.empty
      var mapping: mutable.Map[String, HGEdge] = mutable.Map.empty
      var root: HTNode = null
      var treeNodes: mutable.Map[String, HTNode] = mutable.Map.empty

      for (edge <- edges) {
        mapping.put(edge.name, edge)
        gyoEdges.add(edge.copy())
      }
      //println("mapping: " + mapping)
      //println("GYO edges: " + gyoEdges)

      var progress = true
      while (gyoEdges.size > 1 && progress) {
        for (e <- gyoEdges) {
          val allOtherVertices = (gyoEdges - e).map(o => o.vertices)
            .reduce((o1, o2) => o1 union o2)
          val singleNodeVertices = e.vertices -- allOtherVertices

          val eNew = e.copy(newVertices = e.vertices -- singleNodeVertices)
          gyoEdges = (gyoEdges - e) + eNew

        }

        var nodeAdded = false
        for (e <- gyoEdges) {
          val supersets = gyoEdges.filter(o => o containsNotEqual e)

          if (supersets.isEmpty) {
            val containedEdges = gyoEdges.filter(o => (e contains o) && (e.name != o.name))
            val parentNode = treeNodes.getOrElse(e.name, new HTNode(Set(e), Set(), null))
            val childNodes = containedEdges
              .map(c => treeNodes.getOrElse(c.name, new HTNode(Set(c), Set(), null)))
              .toSet

            parentNode.children ++= childNodes
            if (childNodes.nonEmpty) {
              nodeAdded = true
            }

            treeNodes.put(e.name, parentNode)
            childNodes.foreach(c => treeNodes.put(c.edges.head.name, c))
            root = parentNode
            root.setParentReferences
            gyoEdges --= containedEdges
          }
        }
        if (!nodeAdded) progress = false
      }

      if (gyoEdges.size > 1) {
        return null
      }
      root
    }

  def getEdgeByName(name: String): Option[HGEdge] = {
    return edges.find(e => e.name equals name)
  }

    override def toString: String = {
      edges.map(e => e.name + "(" + e.vertices.map(v => v.toString.replace("$", "")).mkString(",") + ")").mkString("\n")
    }
  }