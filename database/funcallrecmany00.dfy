function even(x : nat, y: nat) : bool
{
  if (x == 0) then
    true
  else if (x == 1) then
    false
  else
    even(x - 2, y)
}

lemma {:isolate_assertions} triangle(x : nat, y: nat)
  ensures {:ipm} even(x, y)
{
 //==> x % 2 == 0
}
