const z : int := 0;
  
lemma asdf(n : int)
  decreases {:ipm} n / z;
{
  assert {:ipm} true; // protectToProve(scope)
  asdf(n);

  //

  assert {:ipm} true; // protectToProve(scope)
  asdf(n / 2);
}

/*

   wf check: z != 0

   termination check: n < n / z

*/
