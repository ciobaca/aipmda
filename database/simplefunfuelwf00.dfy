function {:fuel 4,8} inc(x : int) : int
{
  x + 1
}

lemma {:isolate_assertions} triangle(x : int)
  ensures {:ipm} (inc(10 / x) * x) % 2 == 0
{
}
