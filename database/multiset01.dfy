/*
   well-formedness check for decomp(x / p) fails
   */
ghost function decomp(x : nat) : multiset<nat>
  requires x >= 1
{
  if (x == 1) then
    multiset{ 1 }
  else if exists p :: 2 <= p < x && x % p == 0 then
    var p :| 2 <= p < x && x % p == 0;
    assert x / p >= 1;
    assert x / p < x;
    var r := decomp(x / p);
    r + multiset{ p }
  else
    multiset{ x }
}
