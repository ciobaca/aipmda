type Int = bv8
type Char = char
lemma cast(c: Char)
//
  ensures
    // assert 0 < c && c <= 1 << 8; // from "insert explicit failing assertion"
    // assert 0 < c as int && c as int <= (1 as bv9 << 8) as int; // now semantically sound
    assert 0 <= c as int && c as int < (1 as bv9 << 8) as int; // now helps in proving well-formedness
    c as Int is Int
{}