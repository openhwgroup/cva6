import scala.sys.process._
object MMGen {
  implicit def i2s(i: Int) = i.toString
  def writeFile(name: String, contents: String) = {
    val f = new java.io.FileWriter(name)
    f.write(contents)
    f.close
  }

  var indent = 0
  def spacing = "  " * indent
  def assign(lhs: String, rhs: String) =
    spacing + lhs + " = " + rhs + ";\n"
  def init(t: String, n: String, v: String) =
    assign(t+" "+n, v)
  def open_block(s: String = "") = {
    val result = (if (s != "") spacing + s else "") + spacing + "{\n"
    indent = indent + 1
    result
  }
  def close_block = {
    indent = indent - 1
    spacing + "}\n"
  }

  def ar(m: String, i: String) = m+"["+i+"]"
  def r(a: String, b: String*) = (a :: b.toList).reduceLeft(_+"_"+_)

  def rb(m: Int, n: Int, p: Int) = {
    var s = open_block("static inline void kloop(size_t p, t* a0, size_t lda, t* b0, size_t ldb, t* c, size_t ldc)\n")

    for (i <- 0 until m)
      s += init("t*", r("c", i), "&"+ar("c", "ldc*"+i))
    for (i <- 0 until m; j <- 0 until n)
      s += init("t", r("c", i, j), ar(r("c", i), j))

    def doit(m: Int, n: Int, p: Int) = {
      for (i <- 0 until m)
        s += init("t*", r("a", i), "&"+ar("a", "lda*"+i))
      for (k <- 0 until p)
        s += init("t*", r("b", k), "&"+ar("b", "ldb*"+k))
      for (k <- 0 until p; i <- 0 until m; j <- 0 until n)
        s += assign(r("c", i, j), "fma(" + ar(r("a", i), k) + ", " + ar(r("b", k), j) + ", " + r("c", i, j) + ")")
    }

    s += open_block("for (t *a = a0, *b = b0; a < a0 + p/RBK*RBK; a += RBK, b += RBK*ldb)\n")
    doit(m, n, p)
    s += close_block

    s += open_block("for (t *a = a0 + p/RBK*RBK, *b = b0 + p/RBK*RBK*ldb; a < a0 + p; a++, b += ldb)\n")
    doit(m, n, 1)
    s += close_block

    for (i <- 0 until m; j <- 0 until n)
      s += assign(ar(r("c", i), j), r("c", i, j))
    s += close_block

    s
  }
  def gcd(a: Int, b: Int): Int = if (b == 0) a else gcd(b, a%b)
  def lcm(a: Int, b: Int): Int = a*b/gcd(a, b)
  def lcm(a: Seq[Int]): Int = {
    if (a.tail.isEmpty) a.head
    else lcm(a.head, lcm(a.tail))
  }
  def test1(m: Int, n: Int, p: Int, m1: Int, n1: Int, p1: Int) = {
    val decl = "static const int RBM = "+m+", RBN = "+n+", RBK = "+p+";\n" +
               "static const int CBM = "+m1+", CBN = "+n1+", CBK = "+p1+";\n"
    writeFile("rb.h", decl + rb(m, n, p))
    //"make"!!

    "make run"!

    ("cp a.out " + Seq("b", m, n, p, m1, n1, p1, "run").reduce(_+"."+_))!
  }
  def main(args: Array[String]): Unit = {
    test1(4, 5, 6, 24, 25, 24)
    //for (i <- 4 to 6; j <- 4 to 6; k <- 4 to 6)
    //  test1(i, j, k, if (i == 5) 35 else 36, if (j == 5) 35 else 36, if (k == 5) 35 else 36)
  }
}
