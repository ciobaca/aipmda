function {:fuel 4} sum(x : int) : int
  requires x >= 0
{
  if x == 0 then
    0
  else
    x + sum(x - 1)
}

lemma {:induction false} triangle(x : int)
  requires x > -10
  ensures {:ipm} sum(x) % 2 == 0
{
}
