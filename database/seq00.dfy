lemma {:isolate_assertions} asdf(s : seq<int>)
  requires |s| >= 10
  requires s[0] == s[1]
  ensures {:ipm} s[0] * (s[1] + 1) % 2 == 0
{
}
