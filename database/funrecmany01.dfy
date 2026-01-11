function {:fuel 4,8} asdf(x : int, y : int) : int
{
  if x <= 0 then
    7
  else
    1 + asdf(x - 1, y)
}

lemma test1(x : int, y: int)
  requires x >= 100
  requires asdf(x, y) == 500
{
  //assert asdf(x) == 1 + asdf(x - 1);   // 1, 2, 3, ...
  assert {:ipm} asdf(x, y) == 1 + (0 + asdf(x - 2, y)); // 1, 2, 3, ...
  //assert asdf(x) == 1 + (1 + (1 + asdf(x - 3))); // 2, 3, ..
  //assert asdf(x) == 1 + (1 + (1 + (1 + asdf(x - 3)))); // 3, ...

  // by {
  //   assert asdf(x) == 1 + asdf(x - 1);
  //   //assert asdf(x) == 1 + (1 + asdf(x - 2));
  // }
}

