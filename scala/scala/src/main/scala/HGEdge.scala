import org.apache.calcite.rel.RelNode
import org.apache.calcite.rex.RexNode

import scala.collection.mutable
import scala.collection.mutable.HashMap

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