type nonzero = x : nat | x != 0 witness 1

function asdf(x : nonzero := 10, y : nat := 10 / x + 10) : nat
  requires x != 0
{
  x + 10
}

lemma {:isolate_assertions} asdf1()
{
  assert {:ipm} asdf() == 20;
  assert asdf(13) == 23;

  
}



