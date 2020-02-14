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
import scala.annotation.tailrec
import EdgeWrapper._

class BFSVisitor[N, L](val graph: RichGraph[N, L], val startNode: N)
    extends Iterator[N] {

  private val nodeUnseen = MSet(graph.allNodes: _*)
  private val toVisit = MQueue[N](startNode)
  private val connectingEdge = MHashMap[N, Option[(N, L, N)]](startNode -> None)

  nodeUnseen -= startNode

  override def hasNext = !toVisit.isEmpty

  override def next() = {
    val thisNode = toVisit.dequeue

    for (edge @ (_, label, neighbour) <- graph.transitionsFrom(thisNode)
         if nodeUnseen contains neighbour) {
      nodeUnseen -= neighbour
      toVisit enqueue neighbour
      connectingEdge(neighbour) = Some(edge)
    }

    thisNode
  }
  def unvisited() = nodeUnseen.to[Set]
  def nodeVisited(node: N) = !(nodeUnseen contains node)
  def pathTo(endNode: N): Option[Seq[(N, L, N)]] = {
    if (!(graph hasNode endNode)) {
      println("Graph doesn't have end node " + endNode)
      return None
    }

    this.takeWhile(endNode.!=).foreach(identity)
    if (nodeVisited(endNode)) {

      @tailrec
      def walkBackwards(
          currentNode: N,
          path: List[(N, L, N)]
      ): List[(N, L, N)] = connectingEdge(currentNode) match {
        case None                      => path
        case Some(edge @ (from, _, _)) => walkBackwards(from, (edge :: path))
      }

      Some(walkBackwards(endNode, List()))
    } else {
      None
    }
  }
  def visitAll() = {
    this.foreach(identity)
    this
  }
}

trait Graphable[Node, Label] {
  def transitionsFrom(node: Node): Seq[(Node, Label, Node)]
  def allNodes(): Seq[Node]
  def edges(): Seq[(Node, Label, Node)]
  def subgraph(selectedNodes: Set[Node]): RichGraph[Node, Label]
  def hasNode(node: Node): Boolean = allNodes contains node
  def dropEdges(edges: Set[(Node, Label, Node)]): RichGraph[Node, Label]
}

trait RichGraph[Node, Label] extends Graphable[Node, Label] {
  type Cycle = Set[Node]

  def startBFSFrom(startNode: Node) =
    new BFSVisitor[Node, Label](this, startNode)

  def neighbours(node: Node): Seq[Node] = transitionsFrom(node).map(_.to)

  // Apply is what you'd expect
  def apply(n: Node) = neighbours(n)

  // Calculate the min-cut between the unweighted flow network between
  // source and drain. This uses Edmonds-Karp.
  def minCut(source: Node, drain: Node): Set[(Node, Label, Node)] = {
    println(s"Computing min-cut between ${source} and ${drain}")

    @tailrec
    def findResidual(
        residual: MapGraph[Node, Label]
    ): MapGraph[Node, Label] =
      residual.startBFSFrom(source).pathTo(drain) match {
        case None => residual
        case Some(augmentingPath) => {
          println("Removing augmenting path " + augmentingPath)
          findResidual(residual.dropEdges(augmentingPath.to))
        }
      }

    val residual = findResidual(
      new MapGraph(this.edges.filter(!_.isSelfEdge))
    )

    println("final residual " + residual)

    val visitor = residual.startBFSFrom(source).visitAll

    val reachableInResidual: Set[Node] =
      residual.allNodes.filter(visitor.nodeVisited(_)).toSet

    println("reachable nodes in residual: " + reachableInResidual)

    this.edges
      .filter(
        e =>
          (reachableInResidual contains e.from) &&
            !(reachableInResidual contains e.to)
      )
      .to
  }

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

  // Create a new homomorphic graph by merging the given nodes, returning both
  // the new graph and the resulting composite node in that graph.
  def mergeNodes(nodesToMerge: Iterable[Node]): RichGraph[Node, Label] =
    new CompositeGraph(this, nodesToMerge.to)

}

class MapGraph[N, L](val underlying: Map[N, List[(N, L)]])
    extends Graphable[N, L]
    with RichGraph[N, L] {

  def this(edges: Seq[(N, L, N)]) {
    this(
      edges.map((_._3 -> List())).toMap ++
        edges.groupBy(_._1).mapValues(_.map(v => (v._3, v._2)).toList).toMap
    )
  }

  override def hasNode(node: N) = underlying contains node

  def allNodes() = underlying.keys.to
  def transitionsFrom(node: N) =
    underlying
      .getOrElse(node, Set())
      .map { case (to, label) => (node, label, to) }
      .to
  def subgraph(selectedNodes: Set[N]) =
    new MapGraph[N, L](
      underlying
        .filterKeys(selectedNodes contains _)
        .mapValues(nexts => nexts.filter(selectedNodes contains _._1))
    )

  // NOTE: Maintains all nodes
  def dropEdges(edgesToRemove: Set[(N, L, N)]) = {
    val res = MHashMap[N, List[(N, L)]](underlying.toSeq: _*)

    for ((from, label, to) <- edgesToRemove) {
      // TODO this is *not* efficient
      res(from) = res(from).filter((to, label).!=)
    }

    new MapGraph(res.toMap)
  }

  def edges() =
    underlying.flatMap { case (v, ws) => ws.map(w => (v, w._2, w._1)) }.toSeq
  override def toString = underlying.toString
}

object MapGraph {
  implicit def mapToLabellessGraph[N](m: Map[N, List[N]]): MapGraph[N, Unit] =
    new MapGraph(m.mapValues(_.map(v => (v, ()))))
  implicit def mapToGraph[N, L](m: Map[N, List[(N, L)]]): MapGraph[N, L] =
    new MapGraph(m)
}

class EdgeWrapper[N, L](val underlying: (N, L, N)) {
  def isSelfEdge() = underlying._1 == underlying._3
  def from() = underlying._1
  def to() = underlying._3
}

object EdgeWrapper {
  implicit def tupleToEdgeWrapper[N, L](t: (N, L, N)): EdgeWrapper[N, L] =
    new EdgeWrapper(t)
}

// Generate a graph with an equivalence class of nodes merged into one, while
// still preserving identity for transitions, except self-looping edges to/from
// the equivalent nodes. This means that e.g. transitionsFrom(n) might return
// edges not actually starting in n!
class CompositeGraph[N, L](
    val underlying: RichGraph[N, L],
    val equivalentNodes: Set[N]
) extends Graphable[N, L]
    with RichGraph[N, L] {

  val representativeNode: N = equivalentNodes.head

  // Keep only the representative node for the equivalence class
  def allNodes() =
    ((underlying.allNodes.to[Set] -- equivalentNodes) + representativeNode).to

  private def toEqClass(edge: (N, L, N)) = edge match {
    case (_, _, to) => equivalentNodes contains to
  }

  private def fromEqClass(edge: (N, L, N)) = edge match {
    case (from, _, _) => equivalentNodes contains from
  }

  // Keep all edges not both from and to nodes in equivalentNodes
  // TODO in a real implementation we might not actually want this!
  def edges = underlying.edges.filter(e => !fromEqClass(e) || !toEqClass(e))

  // - for any node not in the equivalence class: just its transitions
  // - for any node in the equivalence class: all transitions from any
  //   node in that class not going into the class itself
  def transitionsFrom(fromNode: N) =
    if (equivalentNodes contains fromNode) {
      equivalentNodes
        .flatMap(underlying.transitionsFrom(_).filter(!toEqClass(_)))
        .to
    } else {
      underlying transitionsFrom fromNode
    }

  // generate a new underlying, and instantiate a copy of self with same
  // parameters after performing the operation.
  def dropEdges(edges: Set[(N, L, N)]) =
    new CompositeGraph(underlying.dropEdges(edges), equivalentNodes)

  def subgraph(nodes: Set[N]) =
    new CompositeGraph(underlying.subgraph(nodes), equivalentNodes)

}
