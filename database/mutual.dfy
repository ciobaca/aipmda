predicate even(x : nat)
  decreases x
{
  if (x == 0) then
    true
  else
    !odd(x)
}

predicate odd(x : nat)
  decreases x
{
  if (x == 0) then
    false
  else
    even(x - 1)
}

