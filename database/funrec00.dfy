function inc(x : nat) : int
{
  if (x == 0) then
    0
  else
    x + x + inc(x - 1)
}

lemma {:isolate_assertions} triangle(x : nat)
  ensures {:ipm} (inc(x) * x) % 2 == 0
{

}
