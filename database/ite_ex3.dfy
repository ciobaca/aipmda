lemma {:isolate_assertions} asdf1(x : int)
  ensures {:ipm} x * (x + 1) % 2 == 0
{
  // if (x % 2 == 0) {
  //   assert x * (x + 1) ==
  //     2 * ((x / 2) * (x + 1));
  // } else {
  //   assert //x * (x + 1) ==
  //     x * (2 * (x / 2) + 2) == 2 * (x * ((x / 2) + 1));
  // }
}
