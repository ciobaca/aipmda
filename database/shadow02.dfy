lemma asdf(x : int, y : int)
  requires x + y > 7
  ensures
    var x := 18;
    x > 10
{
  var x := 10;
  assert {:ipm} x > 8;
}
// lemma asdf(x : int, y : int)
//   requires x + y > 7
// {
//   var x := 10;
//   assert {:ipm} x > 8;
///  assert protectToProve(x > 8, "x > 8", [ _protectScope(x, "x"), _protectScope(y, "y") ])
//   assert protectToProve(x > 8, "x > 8", [ _protectScope(x#1, "x"), _protectScope(y#0, "y") ])
// }
