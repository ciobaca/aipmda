predicate arrayPrefixContainsSet(a : array<int>, s : set<int>, k : int)
  reads a
  requires 0 <= k < a.Length
{
  forall e :: e in s ==> (exists i :: 0 <= i < k && a[i] == e)
}
  
method putZero(a: array<int>, k: nat)
    modifies a
    requires 0 < k < a.Length
{
//  var s: set<int> := (set i | 0 <= i < k :: a[i]);
//  assert arrayPrefixContainsSet(a, s, k);
  a[k] := 0;
  assert {:ipm} a.Length > 10 && 1 != k ==> old(a[1]) == a[1];
  // assert forall i :: 0 <= i < k ==> a[i] == old(a[i]);
  // assert arrayPrefixContainsSet(a, s, k);
  // assert s == (set i | 0 <= i < k :: a[i]);
}
