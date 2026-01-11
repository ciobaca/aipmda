function inc(x : nat) : int
  requires x > 7
{
  x + 1
}

lemma {:isolate_assertions} triangle(x : nat)
  ensures {:ipm} (inc(x) * x) % 2 == 0
{

}
