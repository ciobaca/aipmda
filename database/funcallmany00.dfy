function inc(x : int, y: int) : int
{
  x + 1
}

lemma {:isolate_assertions} triangle(x : int, y: int)
  ensures {:ipm} (inc(x, y) * x) % 2 == 0
{
}
