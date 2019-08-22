module Helpers {
  export Spec provides addOne, addOne_result
  export Body reveals addOne
  export extends Spec
  function method addOne(n: nat): nat 
  {
    n + 1
  }
  lemma addOne_result(n : nat)
     ensures addOne(n) == n + 1
  { }
}

module Mod1 {
  import A = Helpers`Body
  method m() {
    assert A.addOne(5) == 6; // succeeds, we have access to addOne's body
  }
  method m2() {
    //A.addOne_result(5); // error, addOne_result is not exported from Body
    assert A.addOne(5) == 6;
  }
}

module Mod2 {
  import A = Helpers`Spec
  method m() {
    //assert A.addOne(5) == 6; // fails, we don't have addOne's body
  }
  method m2() {
    A.addOne_result(5);
    assert A.addOne(5) == 6; // succeeds due to result from addOne_result
    // coz even though body is not revealed the post-condition from lemma returns context to the value of A.addOne(5)
  }
}

module Mod3 {
  import A = Helpers
  method m() {
    //assert A.addOne(5) == 6; // fails, we don't have addOne's body
  }
}

module Mod4 {
    import opened Helpers`Body //by using opened we don't need to use alias for the module,
                               //we can directly use the method names from Helper module as such
    method m() {
        assert addOne(5) == 6;
    }
}


module Mod {
    import opened Helpers`Body
    function addOne(n: nat): nat {
        n
    }
    method m() {
        assert addOne(5) == 5; // this is now false,
            // as this is the function just defined 
        assert Helpers.addOne(5) == 6; // this is still true
    } 
}

module Interface {
  function method addSome(n: nat): nat 
    ensures addSome(n) > n
}

module Mod5 {
  import A : Interface
  method m() {
    assert 6 <= A.addSome(5);
  }
}

module Implementation refines Interface {
  function method addSome(n: nat): nat 
    ensures addSome(n) == n + 1
  {
    n + 1
  }
}

module Mod6 refines Mod5 {
  import A = Implementation
  method m1() {
      assert 6 == A.addSome(5);
  }
}

method makeArray() returns (a: array<int>)
  ensures a.Length > 0
  ensures fresh(a)
{
  return new int[10];
}

method Main() 
{
  var a := makeArray();
  a[0] := 0;
}