package strsolver.preprop

import scala.collection.mutable.{
  ArrayBuffer,
  Set => MSet,
  Stack => MStack,
  Queue => MQueue,
  HashMap => MHashMap
}
import scala.language.implicitConversions
import scala.math.min

class BFSVisitor[N](val graph: RichGraph[N], val startNode: N)
    extends Iterator[N] {

  private val nodeUnseen = MSet(graph.allNodes: _*)
  private val toVisit = MQueue[N](startNode)
  nodeUnseen -= startNode

  override def hasNext = !toVisit.isEmpty
  override def next() = {
    val thisNode = toVisit.dequeue
    for (neighbour <- graph.neighbours(thisNode)
         if nodeUnseen contains neighbour) {
      nodeUnseen -= neighbour
      toVisit enqueue neighbour
    }

    thisNode
  }
  def unvisited() = nodeUnseen.to[Set]
}

trait Graphable[Node] {
  type Label
  type Edge = (Node, Label, Node)

  def neighbours(node: Node): Seq[Node]
  def allNodes(): Seq[Node]
  def edges(): Seq[(Node, Label, Node)]
  def subgraph(selectedNodes: Set[Node]): RichGraph[Node]
}

trait RichGraph[Node] extends Graphable[Node] {
  type Cycle = Set[Node]

  def startBFSFrom(startNode: Node) = new BFSVisitor[Node](this, startNode)

  // Apply is what you'd expect
  def apply(n: Node) = neighbours(n)

  def minCut(source: Node, drain: Node): Set[Edge] = Set()

  def unreachableFrom(startNode: Node) = {
    val it = startBFSFrom(startNode)
    it.foreach(identity) // perform iteration
    it.unvisited.to[Set]
  }

  // Find the strongly connected components of a graph using Tarjan's
  // algorithm, adapted from Wikipedia's pseudocode.
  // FIXME this code is SO. UGLY.
  def stronglyConnectedComponents() = {
    var smallestFreeIndex = 0
    val depthIndex = new MHashMap[Node, Int]
    val lowLink = new MHashMap[Node, Int]
    val inCurrentComponent = new MHashMap[Node, Boolean]
    val currentComponent = new MStack[Node]
    val components = new ArrayBuffer[Set[Node]]

    def unvisited(node: Node) = !(depthIndex contains node)

    for (node <- allNodes if unvisited(node)) {
      strongConnect(node)
    }

    def strongConnect(node: Node): Unit = {
      import scala.util.control.Breaks._

      depthIndex(node) = smallestFreeIndex
      lowLink(node) = smallestFreeIndex
      smallestFreeIndex += 1
      currentComponent.push(node)
      inCurrentComponent(node) = true

      for (successor <- neighbours(node)) {
        if (unvisited(successor)) {
          strongConnect(successor)
          lowLink(node) = min(lowLink(node), lowLink(successor))
        } else if (inCurrentComponent.getOrElse(successor, false)) {
          // successor is in the current SCC, but if it is not on the stack,
          // then (v, w) is a cross-edge and must be ignored.
          lowLink(node) = min(lowLink(node), depthIndex(successor))
        }
      }

      // Generate a SCC!
      if (lowLink(node) == depthIndex(node)) {
        // pop everything from the stack, set onStack to inCurrentComponent to false
        val component = new ArrayBuffer[Node]

        breakable {
          while (!currentComponent.isEmpty) {
            val w = currentComponent.pop
            inCurrentComponent(w) = false
            component += w

            if (w == node) {
              break
            }
          }
        }

        components += component.toSet
      }

    }
    components.toSet

  }

  // Find all simple cycles in the graph. Uses Johnson's algorithm. Adapted from
  // networkx's Python version.
  def simpleCycles(): Set[Cycle] = {
    def unblock(
        thisNode: Node,
        blocked: MSet[Node],
        noCircuit: MHashMap[Node, MSet[Node]]
    ) = {
      val stack = MStack(thisNode)
      while (!stack.isEmpty) {
        val node = stack.pop
        if (blocked contains node) {
          blocked -= node
          stack pushAll noCircuit.getOrElse(node, Set())
          noCircuit -= node
        }
      }
    }

    val cycles: ArrayBuffer[Cycle] = ArrayBuffer()

    // handle self-edges first; Johnson's ignores them
    for ((from, _, to) <- edges) {
      if (to == from)
        cycles += Set(from)
    }

    val sccs = stronglyConnectedComponents.to[MStack]

    while (!sccs.isEmpty) {
      val component = sccs.pop
      val componentGraph = subgraph(component)

      val startNode = component.head

      val closed = MSet[Node]()
      val blocked = MSet(startNode)
      val path = MStack(startNode)
      val noCircuit = MHashMap[Node, MSet[Node]]()

      def neighbourStack(node: Node) =
        MStack(componentGraph(node).filter(node.!=): _*)

      val stack = MStack((startNode, neighbourStack(startNode)))

      def scheduleVisitNext(node: Node) = {
        path push node
        stack push ((node, neighbourStack(node)))
        closed -= node
        blocked += node
      }

      def tieUpCycle(node: Node) = {
        if (closed contains node) {
          unblock(node, blocked, noCircuit)
        } else {
          for (neighbour <- componentGraph neighbours node) {
            noCircuit.getOrElse(neighbour, MSet[Node]()) += node
          }
        }
        stack.pop

        path.pop // Drop thisNode
      }

      while (!stack.isEmpty) {
        // Note: we only pop the stack when we have finished walking all neighbours
        val (thisNode, neighbours) = stack.top
        var thisNodeNextOnStack = true
        if (!neighbours.isEmpty) {
          val nextNode = neighbours.pop

          if (nextNode == startNode) {
            closed ++= path
            cycles += path.to

          } else if (!(blocked contains nextNode)) {
            scheduleVisitNext(nextNode)
            thisNodeNextOnStack = false
          }
        }

        if (neighbours.isEmpty && thisNodeNextOnStack) {
          tieUpCycle(thisNode)
        }

      }

      for (component <- (componentGraph subgraph component.tail).stronglyConnectedComponents
           if component.size > 1) {

        sccs push component
      }

    }

    cycles.toSet
  }

}

class MapGraph[N](val underlying: Map[N, List[N]])
    extends Graphable[N]
    with RichGraph[N] {

  type Label = Unit

  def allNodes() = underlying.keys.to
  def neighbours(node: N) = underlying.getOrElse(node, Set()).to
  def subgraph(selectedNodes: Set[N]) =
    new MapGraph[N](
      underlying
        .filterKeys(selectedNodes contains _)
        .mapValues(nexts => nexts.filter(selectedNodes contains _))
    )
  def edges() =
    underlying.flatMap { case (v, ws) => ws.map(w => (v, (), w)) }.toSeq
  override def toString = underlying.toString

}

object MapGraph {
  implicit def mapToGraph[N](m: Map[N, List[N]]): MapGraph[N] = new MapGraph(m)
}
