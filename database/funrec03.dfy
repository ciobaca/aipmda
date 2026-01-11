function asdf(x : nat := 10) : nat
{
  x + 10
}

lemma {:isolate_assertions} asdf1()
{
  assert {:ipm} asdf() == 20;
  assert asdf(13) == 23;
}



