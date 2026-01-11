function mydiv(x : int) : int
  requires x != 0
{
  10 / x
}

lemma triangle(x : int)
  requires x > 10
  ensures {:ipm} mydiv(x) * x % 2 == 0
{
}
