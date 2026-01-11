lemma asdf1(x : int)
  ensures
  var y := x + 1;
  assert y > x;
  y > x
  ensures x * (x + 1) % 2 == 0
{
  assert (x * (x + 1)) % 2 == (x % 2) * ((x + 1) % 2) by {
    assume false;
  }
}

lemma asdf2(x : nat)
  ensures
    assert x >= 0;
    x >= 0
  ensures x * (x + 1) % 2 == 0
{
  assert (x * (x + 1)) % 2 == (x % 2) * ((x + 1) % 2) by {
    assume false;
  }
}




ensures A by P
  ===>

ensures
  P;
  A

