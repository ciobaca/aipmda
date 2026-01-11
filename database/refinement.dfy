module IPM
  {
module X
{
  lemma asdf(x : int)
    requires x % 4 == 0
    ensures x % 2 == 0
  {
    assert x == (x / 4) * 4;
    assert x == 2 * ((x / 4) * 2);
  }
}
}

module IPMPrim
{
  import opened IPM
    
module Y refines IPM.X
{
  lemma asdf ...
    //requires x % 5 == 0
    ensures x % 4 == 0
  {
  }
}
}
