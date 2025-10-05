#!/usr/bin/env scala
!#

val m = args(0).toInt
val n = args(1).toInt
val approx_nnz = args(2).toInt

val pnnz = approx_nnz.toDouble/(m*n)
val idx = collection.mutable.ArrayBuffer[Int]()
val p = collection.mutable.ArrayBuffer(0)

for (i <- 0 until m) {
  for (j <- 0 until n) {
    if (util.Random.nextDouble < pnnz)
      idx += j
  }
  p += idx.length
}

val nnz = idx.length
val v = Array.tabulate(n)(i => util.Random.nextInt(1000))
val d = Array.tabulate(nnz)(i => util.Random.nextInt(1000))

def printVec(t: String, name: String, data: Seq[Int]) = {
  println("const " + t + " " + name + "[" + data.length + "] = {")
  println("  "+data.map(_.toString).reduceLeft(_+",\n  "+_))
  println("};")
}

def spmv(p: Seq[Int], d: Seq[Int], idx: Seq[Int], v: Seq[Int]) = {
  val y = collection.mutable.ArrayBuffer[Int]()
  for (i <- 0 until p.length-1) {
    var yi = 0
    for (k <- p(i) until p(i+1))
      yi = yi + d(k)*v(idx(k))
    y += yi
  }
  y
}

println("#define R " + m)
println("#define C " + n)
println("#define NNZ " + nnz)
printVec("double", "val", d)
printVec("int", "idx", idx)
printVec("double", "x", v)
printVec("int", "ptr", p)
printVec("double", "verify_data", spmv(p, d, idx, v))
