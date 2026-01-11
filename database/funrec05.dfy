function inc(x : nat) : int
{
  if (x == 0) then
    0
  else
    x + x + inc(x - 1)
}

function my(x : int) : int
{
  x
}

lemma {:isolate_assertions} triangle(x : nat)
  ensures {:ipm} inc(0) == 0 && my(inc(0)) == 0 && (inc(x) * x) % 2 == 0
{
}
