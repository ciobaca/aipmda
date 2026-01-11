/*
   Example for IPM.
   Line (A) works.
   If replaced by calculation (B), it does not work (weird).
   Calculation (C) works.
   If replaced by an equivalent assertion, it does not work (not so weird).
   */
  
lemma {:only} {:induction false} {:isolate_assertions} mult_add(x : nat, y : nat)
  requires y != 0
  //ensures (x + y) / y == x / y + 1
{
  var q := (x + y) / y;
  var r := (x + y) % y;
  assert q * y + r == x + y;
  var q' := x / y;
  var r' := x % y;
  assert q' * y + r' == x;
  assert (q - q') * y + (r - r') == y;
  assert (q - q' - 1) * y == r' - r;
  assert -(y as int) < r' - r < y;
  if (q - q' - 1 <= -1) {
    assert (q - q' - 1) * y <= -(y as int); // (A)
    // calc { // (B)
    //   (q - q' - 1) * y;
    //   <=
    //     (-1) * y;
    //     ==
    //       - (y as int);
    // }
  } else if (q - q' - 1 >= 1) {
    calc { // (C)
      (q - q' - 1) * y;
      >=
        1 * y;
        ==
          y;
    }
  }
  //assert x + y == ((x + y) / y) * y + (x + y) % y;
}
