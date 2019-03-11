type Element;
type effType;               //effector type for the implementation. It is either add or rem (remove)

const unique rem:effType;
const unique add:effType;

var AImp:[Element]bool;     //A set of the implementation state
var RImp:[Element]bool;     //R set of the implementation state
var S:[Element]bool;        //State of the spec


//This is an invariant that must be preserved by the implementation.
//It is necassary for proving refinement of the add operations.
//We will show that every implementation step preserves it.
function impInv(A:[Element]bool, R:[Element]bool) returns (ret:bool);
axiom (forall A:[Element]bool, R:[Element]bool :: impInv(A,R) <==>
            (forall x:Element :: R[x] ==> A[x]  )
);

//Refinement relation : S = A\R
function refinementMapping(A:[Element]bool, R:[Element]bool, S:[Element]bool) returns (ret:bool);
axiom (forall A:[Element]bool, R:[Element]bool, S:[Element]bool::  refinementMapping(A,R,S) <==> 
            (forall x:Element  :: S[x] <==> A[x] && !R[x] )
);


//apply method for the implementation. It can be used for both add and rem effectors
procedure apply(eff:effType, a:Element);
requires eff == add || eff == rem;
modifies AImp, RImp;
ensures eff == add ==> AImp == old(AImp)[a := true];
ensures eff == add ==> RImp == old(RImp);
ensures eff == rem ==> RImp == old(RImp)[a := true];
ensures eff == rem ==> AImp == old(AImp);

//Add method description for the specification
procedure addSpec(a:Element);
modifies S;
ensures S == old(S)[a := true];

//Remove method description for the specification
procedure removeSpec(a:Element);
modifies S;
ensures S == old(S)[a := false];

//Read method description for the implementation
procedure readImp() returns (l:[Element]bool);
ensures (forall x:Element :: l[x] <==> AImp[x] && !RImp[x] );

//Read method description for the specification
procedure readSpec() returns (l:[Element]bool);
ensures (forall x:Element :: l[x] <==> S[x] );

//Merge method description for the implementation
procedure merge(A:[Element]bool, R:[Element]bool );
modifies AImp, RImp;
ensures (forall x:Element :: AImp[x] <==> old(AImp)[x] || A[x] );
ensures (forall x:Element :: RImp[x] <==> old(RImp)[x] || R[x] );

//Refinemenet proof for add operations
//Assume (sigma, add(a), sigma') is the step of the implementation
//We show that (refMap(sigma), add(a), refMap(sigma')) is a valid step of the specification
//We also show that appy preserves impInv for add operations
procedure refAdd(a:Element)
requires impInv(AImp, RImp) && refinementMapping(AImp, RImp, S);
requires !RImp[a];                                                  //We assume that A is not added again after it is removed (see Shapiro et.al.)
modifies AImp, RImp, S;
ensures impInv(AImp, RImp) && refinementMapping(AImp, RImp, S);
{
    call apply(add, a);
    call addSpec(a);
    //assert false;
}

//Refinemenet proof for remove operations
//Assume (sigma, remove(a), sigma') is the step of the implementation
//We show that (refMap(sigma), remove(a), refMap(sigma')) is a valid step of the specification
//We also show that appy preserves impInv for remove operations
procedure refRemove(a:Element)
requires impInv(AImp, RImp) && refinementMapping(AImp, RImp, S);
requires AImp[a] && !RImp[a];                                       //Precondition of remove implementation
modifies AImp, RImp, S;
ensures impInv(AImp, RImp) && refinementMapping(AImp, RImp, S);
{
    call apply(rem, a);
    call removeSpec(a);

    //assert false;
}

//Refinemenet proof for read operations
//Assume (sigma, read()=>l, sigma') is the step of the implementation
//We show that (refMap(sigma), read()=>l, refMap(sigma')) is a valid step of the specification
//We also show that read preserves impInv for the implementation
procedure refRead()
requires impInv(AImp, RImp) && refinementMapping(AImp, RImp, S);
ensures impInv(AImp, RImp) && refinementMapping(AImp, RImp, S);
{
    var l1:[Element]bool, l2:[Element]bool;

    call l1 := readImp();
    call l2 := readSpec();

    assert (forall x:Element :: l1[x] == l2[x]);
    //assert false;
}

//This method shows that merge operation preserves impInv invariant
procedure mergePreservesImpInv(A:[Element]bool, R:[Element]bool)
requires impInv(AImp, RImp) && impInv(A,R);
modifies AImp, RImp;
ensures impInv(AImp, RImp);
{
    call merge(A, R);
    //assert false;
}