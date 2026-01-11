function even(x : nat) : bool
{
  if (x == 0) then
    true
  else if (x == 1) then
    false
  else
    even(x - 2)
}

lemma {:induction false} {:isolate_assertions} triangle(x : nat)
  ensures {:ipm} even(x)
{
 //==> x % 2 == 0
}
