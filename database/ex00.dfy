method double(x : int) returns (r : int)
  requires x > 0
  ensures r > 0
  ensures r == x * 2
{
  return x * 2;
}

function id<T>(x: T): T { x }
class A { function B(): int { 0 } }

method use_double(y : int) returns (r : int)
  requires y > 0
  ensures {:ipm} r == y * 2
  /*
     x > 0
     temp > 0
     r == temp
     ---------/
     r == x * 2
     ---------/
     */
{
//  var temp := double(identitate(y));
  var temp := double(y + 1);
  return temp;
  var x := id(2);
  var a := new A;
  var xf := id(a.B);
  // var y := id(double)(2);
  var z := id(id)(2);
}
