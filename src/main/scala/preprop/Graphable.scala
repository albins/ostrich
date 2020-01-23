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

class BFSVisitor[N](val graph: Graphable[N, Any], val startNode: N)
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

trait Graphable[N, L] {
  def neighbours(node: N): Seq[N]
  def allNodes(): Seq[N]
  def edges(): Seq[(N, L, N)]
  def subgraph(selectedNodes: Set[N]): RichGraph[N, L]
}

trait GraphTraversable[N] extends Graphable[N, Any] {
  def startBFSFrom(startNode: N) = new BFSVisitor[N](this, startNode)
}

trait RichGraph[N, L] extends GraphTraversable[N] {

  // TODO make this a newtype?
  type Cycle = Set[N]

  // Apply is what you'd expect
  def apply(n: N) = neighbours(n)

  def unreachableFrom(startNode: N) = {
    val it = startBFSFrom(startNode)
    it.foreach(identity) // perform iteration
    it.unvisited.to[Set]
  }

  // Find the strongly connected components of a graph using Tarjan's
  // algorithm, adapted from Wikipedia's pseudocode.
  // FIXME this code is SO. UGLY.
  def stronglyConnectedComponents() = {
    var smallestFreeIndex = 0
    val depthIndex = new MHashMap[N, Int]
    val lowLink = new MHashMap[N, Int]
    val inCurrentComponent = new MHashMap[N, Boolean]
    val currentComponent = new MStack[N]
    val components = new ArrayBuffer[Set[N]]

    def unvisited(node: N) = !(depthIndex contains node)

    for (node <- allNodes if unvisited(node)) {
      strongConnect(node)
    }

    def strongConnect(node: N): Unit = {
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
        val component = new ArrayBuffer[N]

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
        thisNode: N,
        blocked: MSet[N],
        noCircuit: MHashMap[N, MSet[N]]
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

      val closed = MSet[N]()
      val blocked = MSet(startNode)
      val path = MStack(startNode)
      val noCircuit = MHashMap[N, MSet[N]]()
      val stack = MStack((startNode, MStack(componentGraph(startNode): _*)))

      def scheduleVisitNext(node: N) = {
        path push node
        stack push ((node, MStack(componentGraph(node).filter(node.!=): _*)))
        closed -= node
        blocked += node
      }

      def tieUpCycle(node: N) = {
        if (closed contains node) {
          unblock(node, blocked, noCircuit)
        } else {
          for (neighbour <- componentGraph neighbours node) {
            noCircuit.getOrElse(neighbour, MSet[N]()) += node
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
    extends Graphable[N, Any]
    with RichGraph[N, Any] {
  def allNodes() = underlying.keys.to
  def neighbours(node: N) = underlying.getOrElse(node, Set()).to
  def subgraph(selectedNodes: Set[N]) =
    new MapGraph(
      underlying
        .filterKeys(selectedNodes contains _)
        .mapValues(nexts => nexts.filter(selectedNodes contains _))
    )
  def edges() =
    underlying.flatMap { case (v, ws) => ws.map(w => (v, (), w)) }.toSeq
  override def toString = underlying.toString

}

object MapGraph {
  implicit def mapToGraph[N](m: Map[N, List[N]]) = new MapGraph(m)
}
