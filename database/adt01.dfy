datatype List = Empty | Cons_q(head : int, tail : List)

lemma asdf(list : List)
  requires list.Cons_q?
  requires list.tail.Cons_q?
  requires list.tail.head % 2 == 0
  ensures {:ipm} list != Empty
{
}

