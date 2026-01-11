ghost function {:isolate_assertions} productMultiset(x : multiset<int>) : int
{
  if x == multiset{} then
    1
  else
    var y : int :| y in x;
    y * productMultiset(x - multiset{ y })
}

lemma {:induction false} whichElement(x : multiset<int>) returns (y : int)
  requires x != multiset{}
  ensures y in x && productMultiset(x) == y * productMultiset(x - multiset{ y })
{
  assert exists y :: y in x && productMultiset(x) == y * productMultiset(x - multiset{ y });
  y :| y in x && productMultiset(x) == y * productMultiset(x - multiset{ y });
}

lemma {:induction false} {:isolate_assertions} productMultisetAddOne(x : multiset<int>, y : int)
  ensures productMultiset(x + multiset{ y }) == y * productMultiset(x)
{
  var e := whichElement(x + multiset{ y });
  if e == y {
    assert x + multiset{ y } - multiset{ y } == x;
  } else {
    calc {
      productMultiset(x + multiset{ y });
      ==
        e * productMultiset(x + multiset{ y } - multiset{ e });
        ==
          { assert x + multiset{ y } - multiset{ e } == (x - multiset{e}) + multiset{ y }; }
          e * productMultiset((x - multiset{e}) + multiset{ y });
          ==
            { productMultisetAddOne(x - multiset{e}, y); }
            e * (y * productMultiset(x - multiset{e}));
            ==
              { multiplication_assoc_2(e, y, productMultiset(x - multiset{e})); }
              y * (e * productMultiset(x - multiset{e}));
              ==
                {
                  productMultisetAddOne(x - multiset{ e }, e);
                  assert x - multiset{ e } + multiset{ e } == x;
                  assert productMultiset(x) == e * productMultiset(x - multiset{ e });
                }
                y * productMultiset(x);
    }
  }
}

lemma {:induction false} productMultisetRemoveOne(x : multiset<int>, y : int)
  requires y in x
  ensures productMultiset(x) == y * productMultiset(x - multiset{ y })
{
  productMultisetAddOne(x - multiset{ y }, y);
  assert x - multiset{ y } + multiset{ y } == x;
}

lemma {:induction false} multisetUnionDiffLeft(x : multiset<int>, y : multiset<int>, e : int)
  requires e in x
  ensures (x + y) - multiset{e} == (x - multiset{e}) + y
{
}

lemma {:induction false} multisetUnionDiffRight(x : multiset<int>, y : multiset<int>, e : int)
  requires e in y
  ensures (x + y) - multiset{e} == x + (y - multiset{ e })
{
}

lemma multiplication_assoc(a : int, b : int, c : int)
  ensures a * (b * c) == (a * b) * c
{
}

lemma multiplication_assoc_2(a : int, b : int, c : int)
  ensures a * (b * c) ==  b * (a * c)
{
}

lemma {:induction false} {:isolate_assertions} productMultisetUnion(x : multiset<int>, y : multiset<int>)
ensures productMultiset(x + y) == productMultiset(x) * productMultiset(y)
{
  if x + y == multiset{} {
  } else {
    var e := whichElement(x + y);
    if (e in x) {
      calc {
        productMultiset(x + y);
        ==
          e * productMultiset((x + y) - multiset{ e });
          ==
            { multisetUnionDiffLeft(x, y, e); }
            e * productMultiset((x - multiset{ e }) + y);
            ==
              { productMultisetUnion(x - multiset{ e }, y); }
              e * (productMultiset(x - multiset{ e }) * productMultiset(y));
              ==
                { multiplication_assoc(e, productMultiset(x - multiset{ e }), productMultiset(y)); }
                (e * productMultiset(x - multiset{ e })) * productMultiset(y);
                ==
                  { productMultisetRemoveOne(x, e); }
                  productMultiset(x) * productMultiset(y);
      }
    } else if (e in y) {
      calc {
        productMultiset(x + y);
        ==
          e * productMultiset((x + y) - multiset{ e });
          ==
            { multisetUnionDiffRight(x, y, e); }
            e * productMultiset(x + (y - multiset{ e }));
            ==
              { productMultisetUnion(x, y - multiset{ e }); }
              e * (productMultiset(x) * productMultiset(y - multiset{ e }));
              ==
                { multiplication_assoc_2(e, productMultiset(x), productMultiset(y - multiset{ e })); }
                productMultiset(x) * (e * productMultiset(y - multiset{ e }));
                ==
                  { productMultisetRemoveOne(y, e); }
                  productMultiset(x) * productMultiset(y);
      }
    } else {
      assert false;
    }
  }
}

// lemma productMultisetSingleton(x : int)
//   ensures productMultiset(multiset{ x }) == x
// {
//   var y : int :|
//     y in multiset{ x } &&

//     productMultiset(multiset{ x }) == y * productMultiset(multiset{ x } - multiset{ y });
// }

lemma div_less(x : int, y : int)
  requires x >= 2
  requires 2 <= y
  ensures x / y < x
{
  if (x / y >= x)
  {
    assert x >= (x / y) * y;
  }
}

ghost function decomp(x : int) : multiset<int>
  requires x >= 1
  //ensures forall y :: y in decomp(x) ==> isPrime(y)
  ensures forall y :: y in decomp(x) ==> y >= 1
{
  if (x == 1) then
    multiset{ }
  else if exists p :: 2 <= p < x && x % p == 0 then
    var p :| 2 <= p < x && x % p == 0;
    ///assert x / p >= 1;
    assert x / p < x by { div_less(x, p); }
    //assert p >= 1;
    //assert p < x;
    var d1 := decomp(x / p);
    var d2 := decomp(p);
    d1 + d2
  else
    multiset{ x }
}

lemma {:induction false} {:isolate_assertions} productDecomp(x : int)
  requires x >= 1
  ensures productMultiset(decomp(x)) == x
{
  if (x == 1) {
    assert decomp(x) == multiset{ };
    assert productMultiset(decomp(x)) == 1;
  } else if (exists p :: 2 <= p < x && x % p == 0) {
    var p :| 2 <= p < x && x % p == 0 && decomp(x) == decomp(x / p) + decomp(p);
    assert x == (x / p) * p + (x % p);
    assert x == (x / p) * p;
    // div_less(x, p);
    // assume x / p < x;
    var {:ipm_wf} d1 := decomp(x / p);
    productMultisetUnion(d1, decomp(p));
    assert productMultiset(decomp(x / p)) == x / p by { productDecomp(x / p); }
    assert productMultiset(decomp(p)) == p by { productDecomp(p); }
  } else {
    assert decomp(x) == multiset{ x };
    //productMultisetSingleton(x);
  }
}

function exam(x : int, y : int) : int
  requires y >= 2
  decreases {:ipm} x
{
  if (x <= 2) then
    10
  else
    // assume 0 <= x / y < x;
    1 + exam(x / y, y)
}



