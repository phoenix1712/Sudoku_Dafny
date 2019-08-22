method FindMax(a: array<int>) returns (i: int) 
    requires 0 < a.Length 
    ensures forall k :: 0 <= k < a.Length ==> a[k] <= i
{
    i := a[0];
    var k := 0;
    while k < a.Length
        invariant 0 <= k <= a.Length
        invariant forall j :: 0 <= j < k ==> a[j] <= i
        decreases  a.Length - k
  {
        if i < a[k] {i := a[k]; }
        k := k + 1;
    }
}

method SetExample()
{
    var s1: set<int> := {};
    var s2 := {1, 2, 3};
    assert s2 == {1,1,2,3,3,3,3};
    var s3, s4 := {1,2}, {1,4};

    assert s2 + s4 == {1,2,3,4};
    assert s2*s3 == {1,2} && s2*s4 == {1};
    assert s2 - s3 == {3};
    assert s3 - s4 == {2};

    assert {1} <= {1,2} && {1,2} <= {1,2};
    assert {} < {1,2} && !({1} < {1});
    assert !({1,2} <= {1,4}) && !({1,4} <= {1,2});
    assert {1,2} == {1,2} && {1,2} != {1,3};

    assert 5 in {1,5};
    // assert forall x :: x !in {};
    // assert (set x | x in {0,1,2} :: x * 1) == {0,1,2};
    // assert (set x | x in {0,1,2,3,4,5} && x < 3) == {0,1,2};
    // assert (set x | x in {0,1,2} :: x + 1) == {1,2,3};
}

predicate sorted2(s: seq<int>)
  decreases s
{
   0 < |s| ==> (forall i :: 0 < i < |s| ==> s[0] <= s[i]) &&
               sorted2(s[1..])
}

function update(s: seq<int>, i: int, v: int): seq<int>
   requires 0 <= i < |s|
   ensures update(s, i, v) == s[i := v]
{
   s[..i] + [v] + s[i+1..]
}

method maps()
{
    var m := map[3 := 5, 4 := 6, 1 := 4];
    var l := map i | i in m && i != 3 :: m[i];
    assert l == map[4:= 6, 1 := 4];
}