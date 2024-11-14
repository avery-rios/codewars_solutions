class TreeSpec extends org.scalatest.flatspec.AnyFlatSpec {
  "treeByLevels" should "pass basic tests" in {
    val testCases = Seq[(Node, Seq[Int])](
      (Node(None, None, 1),
       Seq(1)),
      
      (Node(
        Some(Node(None, None, 2)), 
        Some(Node(None, None, 3)), 
        1), 
       Seq(1, 2, 3)),
      
      (Node(
        Some(Node(
          Some(Node(
            None, 
            None, 
            1)), 
          Some(Node(
            None, 
            None, 
            3)), 
          8)),
        Some(Node(
          Some(Node(
            None, 
            None, 
            4)), 
          Some(Node(
            None, 
            None, 
            5)), 
          9)),   
        2),
       Seq(2, 8, 9, 1, 3, 4, 5)),
      
      (Node(
        Some(Node(
          None, 
          Some(Node(
            None, 
            None,
            3)), 
          8)), 
        Some(Node(
          None, 
          Some(Node(
            None, 
            Some(Node(
              None, 
              None, 
              7)), 
            5)), 
          4)), 
        1),
       Seq(1,8,4,3,5,7))
    )
    
    testCases.foreach {
      (node, expected) =>
        assertResult(expected, s"\nInput:\n node = $node")(treeByLevels(node))
    }
  }
}