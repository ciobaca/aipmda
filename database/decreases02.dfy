lemma asdf1(n : nat)
  decreases {:ipm} n, 0
{
  if (n != 0) {
    asdf2(n - 1);
  }
}

lemma asdf2(n : nat)
  decreases {:ipm} n, 1
{
  asdf1(n);
}
