lemma A(n : nat)
  decreases {:ipm} 5 * n + 1
{
  if (n > 0) {
    B(n - 1);    // B.decreases(n - 1) < A.decreases(n)
    // 7 * (n - 1) + 3 < 3 * n + 1
  }
}

lemma B(n : nat)
  decreases 3 * n + 3
{
  if (n > 0) {
    A(n - 1);       // 5 * (n - 1) + 1 < 3 * n + 3
  }
}

