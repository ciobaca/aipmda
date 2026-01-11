lemma {:isolate_assertions} asdf<T>(s : seq<T>)
  requires |s| >= 10
  requires s[0] == s[2]
  ensures {:ipm} s[0] == s[1]
{
}
