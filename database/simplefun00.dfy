function inc(x : int) : int
{
  x + 1
}

lemma {:isolate_assertions} triangle(x : int)
  ensures {:ipm} (inc(x) * x) % 2 == 0
{
}
