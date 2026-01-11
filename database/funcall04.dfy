function inc(x : int) : int
{
  x + 1
}

lemma triangle(x : int)
  ensures {:ipm} (inc(x) * x) % 2 == 0
{
  if (x % 2 == 0) {
    assert (x + 1) * x == (2 * ((x + 1) * (x / 2)));
    //assert (0 == (((x + 1) * x) % 2));
  } else {
    assert (x + 1) % 2 == 0;
    assert (x + 1) * x == 2 * (((x + 1) / 2) * x);
    //assume false;
  }
}
