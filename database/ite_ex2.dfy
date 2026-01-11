ghost predicate even(x : int)
{
  x % 2 == 0
}

lemma asdf1(x : int)
  ensures even(x * (x + 1))
{
  if (even(x)) {
    assert x * (x + 1) ==
      2 * ((x / 2) * (x + 1));
  } else {
    assert //x * (x + 1) ==
      x * (2 * (x / 2) + 2) == 2 * (x * ((x / 2) + 1));
  }
}
