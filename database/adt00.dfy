datatype MyBool = MyTrue | MyFalse

lemma asdf(x : MyBool, y : MyBool, z : MyBool)
  requires x == MyTrue
  ensures {:ipm} x == z
{
}
