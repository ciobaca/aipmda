lemma asdf1(x : int)
  ensures x * (x + 1) % 2 == 0
{
  assert {:ipm} x * (x + 1) % 2 == 0;
}




