package strsolver

import org.scalatest.FunSuite
import org.scalatest.Assertions._
import strsolver.preprop.{Graphable, BFSVisitor, MapGraph}
import strsolver.preprop.MapGraph._

class TestGraphOperations extends FunSuite {

  def bfsToEnd(g: MapGraph[Int, Unit], startNode: Int) = {
    val it = (g startBFSFrom 1)
    it.foreach(identity)
    it
  }

  val allConnected =
    Map(1 -> List(1, 2, 3, 4), 2 -> List(2), 3 -> List(3, 2, 4), 4 -> List())

  val twoNodeCycle = Map(1 -> List(2), 2 -> List(1))

  test("Simple BFS with cycle iterates over all nodes") {
    assert((allConnected startBFSFrom 1).toSeq == List((1, (), 2), (1, (), 3), (1, (), 4)))
  }

  test("BFS marks all nodes visited") {
    val it = bfsToEnd(allConnected, 1)
    assert(it.unvisited.isEmpty)
  }

  test("BFS misses disconnected bit") {
    val g =
      Map(1 -> List(1, 2, 3), 2 -> List(2), 3 -> List(3, 2), 4 -> List())

    val it = bfsToEnd(g, 1)
    assert(it.unvisited == Set(4))

  }

  test("connectedComponent finds components in SCC-less graph") {
    val sccs = allConnected.stronglyConnectedComponents
    assert(sccs == Set(Set(1), Set(2), Set(3), Set(4)))
  }

  test("connectedComponent finds simple 2-node component") {
    assert(twoNodeCycle.stronglyConnectedComponents == Set(Set(1, 2)))
  }

  test(
    "connectedComponent reproduces first graph from Wikipedia:Strongly_connected_component"
  ) {
    val ex1 = Map(
      'a' -> List('b'),
      'b' -> List('c', 'e', 'f'),
      'c' -> List('d', 'g'),
      'e' -> List('a', 'f'),
      'f' -> List('g'),
      'g' -> List('f'),
      'd' -> List('h', 'c'),
      'h' -> List('d', 'g')
    )

    assert(
      ex1.stronglyConnectedComponents == Set(
        Set('a', 'b', 'e'),
        Set('f', 'g'),
        Set('c', 'd', 'h')
      )
    )
  }

  test("simpleCycle finds a minimal cycle") {
    assert(twoNodeCycle.simpleCycles == Set(Set(1, 2)))
  }

  test("simpleCycle finds a self-loop") {
    assert(Map(1 -> List(1)).simpleCycles == Set(Set(1)))
  }

  test("simpleCycle finds a minimal cycle and a self-loop") {
    assert(
      Map(1 -> List(1, 2), 2 -> List(1)).simpleCycles == Set(Set(1), Set(1, 2))
    )
  }

  test("simpleCycle finds two cycles") {
    val g = Map(1 -> List(2, 4), 2 -> List(3), 3 -> List(1), 4 -> List(1))

    assert(g.simpleCycles == Set(Set(1, 2, 3), Set(1, 4)))
  }

  test("BFS finds last node of connected graph") {
    assert(allConnected.startBFSFrom(1).pathTo(4) == Some(Seq((1, (), 4))))
  }

  test("BFS does not find disconnected node") {
    val g = Map(1 -> List(2, 3),
            2 -> List(2),
            3 -> List(3),
            4 -> List(4))

    assert(g.startBFSFrom(1).pathTo(4) == None)
  }

  // test("minCut finds min cut of simple graph") {
  //   val g = Map(1 -> List(2, 3), 2 -> List(4), 3 -> List(4), 4 -> List(5))

  //   assert(g.minCut(1, 5) == List((4, (), 5)))

  // }

}
// TODO property-based tests for "union of connected components contains all nodes"
