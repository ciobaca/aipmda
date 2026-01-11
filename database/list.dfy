datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat
{
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
  case Nil => ys
  case Cons(h, t) => Cons(h, Append(t, ys))
}

function Reverse<T>(xs: List<T>): List<T>
{
  match xs
  case Nil => Nil
  case Cons(h, t) => Append(Reverse(t), Cons(h, Nil))
}

lemma AppendNil<T>(xs: List<T>)
  ensures Append(xs, Nil) == xs
{}

lemma LengthAppend<T>(xs: List<T>, ys: List<T>)
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{}

lemma ReverseLength<T>(xs: List<T>)
  ensures Length(Reverse(xs)) == Length(xs)
{}

lemma ReverseReverse<T>(xs: List<T>)
  ensures Reverse(Reverse(xs)) == xs
{}

lemma ConsInjectiveHead<T>(x: T, y: T, xs: List<T>, ys: List<T>)
  requires Cons(x, xs) == Cons(y, ys)
  ensures {:ipm} x == y
{}