function mydiv(x : int) : int
  requires x != 0
{
  10 / x     // wf check: x != 0 => x != 0
}

lemma triangle(x : int)
  requires x > -10
  
  ensures {:ipm} mydiv(x) * x % 2 == 0
             //  ^^^^^^^^
             // wf x > -10 => x != 0
{
}
