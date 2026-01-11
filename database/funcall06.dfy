function inc(x : int) : int
{
  x + 1
}

lemma {:isolate_assertions} triangle(x : int)
  ensures {:ipm} (inc(x) * x) % 2 == 0
{
  assert (inc(x) == x + 1);
  var x : int := 7;
  assert x == 7;
}
