@IsolateAssertions
lemma wf_check(x: int, y: int := 0)
  requires y % 4 == 3
//
  ensures
    var q := y / 4;
    // y^2 = (4q + 3)^2 = 16q^2 + 24q + 9 = 4 * (4q^2 + 6q + 2) + 1
    // y^2 % 4 = (4 * (4q^2 + 6q + 2) + 1) % 4 = 1 % 4 = 1
    // assert y == 4 * q + 3;
    // assert y * y == (4 * q + 3) * (4 * q + 3);
    // assert y * y == 16 * q * q + 24 * q + 9;
    
    assert y * y == 4 * (4 * q * q + 6 * q + 2) + 1;
    // luckily, we don't need a lemma to prove that `forall x: int :: (4 * x + 1) % 4 == 1`
    (x / ((y * y % 4))) == x
{}