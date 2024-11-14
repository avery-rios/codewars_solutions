import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ArrayDeque

def treeByLevels(node: Node): Seq[Int] =
  var ret = ArrayBuffer[Int]()
  var q = ArrayDeque[Node]()
  q.prepend(node)
  while !q.isEmpty do
    val h = q.removeHead()
    ret.append(h.value)
    h.left match
      case Some(l) => q.append(l)
      case None    =>
    h.right match
      case Some(r) => q.append(r)
      case None    =>
  ret.toSeq
