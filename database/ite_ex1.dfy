ghost predicate even(x : int)
{
  exists half : int :: x == half * 2
}


lemma asdf1(x : int)
  ensures even(x * (x + 1))
{
  if (x % 2 == 1) {
    assert x * (x + 1) == x * (x / 2 + 1) * 2;
  } else {
    assert x * (x + 1) == (x / 2) * 2 * (x + 1) == (x / 2) * (x + 1) * 2;
  }
}
