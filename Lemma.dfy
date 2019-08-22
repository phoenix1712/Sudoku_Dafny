lemma SkippingLemma(a : array<int>, j : int)
   requires 0 < a.Length
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
   var i := j;
   while i < j + a[j] && i < a.Length
      invariant i < a.Length ==> a[j] - (i-j) <= a[i]
      invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
      decreases  j + a[j] - i
   {
      i := i + 1;
   }
}
method FindZero(a: array<int>) returns (index: int)
   requires 0 < a.Length
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
{
   index := 0;
   while index < a.Length
      invariant 0 <= index
      invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
      decreases  a.Length - index
   {
        if a[index] == 0 { return; }
        SkippingLemma(a, index );
        index := index + a[index];
   }
   index := -1;
}

//========================================================================================================

lemma {:induction a,b} DistributiveLemma(a: seq<bool>, b: seq<bool>)
    ensures count(a + b) == count(a) + count(b)
    decreases  a, b
{
   if a == []
   {
      assert a + b == b;
   }
   else
   {
      DistributiveLemma(a[1..], b);
      assert a + b == [a[0]] + (a[1..] + b);
   }
}
function count(a: seq<bool>): nat
    decreases  a
{
   if |a| == 0 then 0 else
   (if a[0] then 1 else 0) + count(a[1..])
}

//========================================================================================================
//========================================================================================================
//========================================================================================================


datatype Nat = Zero | Succ(next: Nat)

function method Nat2nat(a: Nat) : nat
    decreases a
{
    if a == Zero then 0 else 1 + Nat2nat(a.next)
}

function method plus(a: Nat, b: Nat) : Nat
    decreases a
{
    if a == Zero then b else Succ(plus(a.next, b))
}

function method nat2Nat(a: nat): Nat
    decreases a
{
    if a == 0 then Zero else Succ(nat2Nat(a-1)) 
}

method check(n: nat)
{
    assert forall i  {:induction i}  :: 0 <= i < n ==> i == Nat2nat(nat2Nat(i));
    var a := nat2Nat(3);
    var b := nat2Nat(4);
    assert Nat2nat(plus(a,b)) == Nat2nat(a) + Nat2nat(b);

}

lemma {:induction false} plusCorrect(a: Nat, b:Nat) 
    ensures Nat2nat(plus(a,b)) == Nat2nat(a) + Nat2nat(b)
    decreases a
{
    if a != Zero 
    {
        plusCorrect(a.next, b);
    }
}

lemma {:induction false} plusAsociative(a: Nat, b:Nat, c:Nat)
    ensures plus(a, plus(b,c)) == plus(plus(a,b), c)
    decreases a
{
    if a != Zero
    {
        plusAsociative(a.next, b, c);
    }
}

lemma  {:induction false} plusZero(x: Nat)
    ensures plus(x, Zero) == x
    decreases  x
{
    if x != Zero
    {
        plusZero(x.next);
    }
} 

lemma {:induction false} plusCommZero(x: Nat)
    ensures plus(x, Zero) == plus(Zero, x)
{
    plusZero(x);
    assert plus(x, Zero) == plus(Zero, x);
}

lemma {:induction false} plusSucc(x: Nat, y: Nat)
    ensures Succ(plus(x,y)) == plus(x, Succ(y))
    decreases x
{
    if x != Zero
    {
        plusSucc(x.next, y);
    } 
}

lemma {:induction false} plusComm(x: Nat, y: Nat)
    ensures plus(x,y) == plus(y,x)
    decreases x
{
    if x == Zero
    {
        plusCommZero(y);
    } 
    else 
    {
        calc {
                plus(x, y);
            ==  
                plus(Succ(x.next), y);
            == 
                Succ(plus(x.next, y));
            ==  { plusComm(x.next, y); }
                Succ(plus(y,x.next));
            ==  { plusSucc(y, x.next); }
                plus(y, Succ(x.next));
            ==
                plus(y,x);                
        }

        // assert plus(x,y) == plus(Succ(x.next), y) == Succ(plus(x.next, y));
        // plusComm(x.next, y);
        // assert Succ(plus(x.next, y)) == Succ(plus(y, x.next));
        // plusSucc(y,x.next);
        // assert Succ(plus(y, x.next)) == plus(y, Succ(x.next));
    }
}