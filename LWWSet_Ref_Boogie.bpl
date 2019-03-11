type Element;
type Timestamp = int;
type effType;                         //effector type for the implementation. It is either add or rem (remove)

const unique rem:effType;
const unique add:effType;

var AImp:[Element][Timestamp]bool;     //A set of the implementation state
var RImp:[Element][Timestamp]bool;     //R set of the implementation state
var S:[Element]bool;                   //State of the specification

//P1 acts as the linearization condition. At the point it is linearized, its timestamp is greater than the every operation applied on this replica
function P1(A:[Element][Timestamp]bool, R:[Element][Timestamp]bool, eff:effType, a:Element, ts:Timestamp) returns (ret:bool);
axiom (  forall A:[Element][Timestamp]bool, R:[Element][Timestamp]bool, eff:effType, a:Element, ts:Timestamp :: P1(A, R, eff, a, ts) <==>
            (forall b:Element, tb:Timestamp :: A[b][tb] || R[b][tb] ==> tb < ts )
);

//Refinement relation : a in S iff a in AImp and its timestamp is greater than all t' s.t. (a, t') in RImp
function refinementMapping(A:[Element][Timestamp]bool, R:[Element][Timestamp]bool, SS:[Element]bool) returns (ret:bool);
axiom (forall A:[Element][Timestamp]bool, R:[Element][Timestamp]bool, SS:[Element]bool::  refinementMapping(A,R,SS) <==> 
            (forall x:Element :: SS[x] <==> (exists t:Timestamp :: A[x][t] && (forall tt:Timestamp :: R[x][tt] ==> tt < t ) ) )
);

//apply method for the implementation. It can be used for both add and rem effectors
procedure apply(eff:effType, a:Element, ts:Timestamp);
requires eff == add || eff == rem;
modifies AImp, RImp;
ensures eff == add ==> AImp == old(AImp)[a := old(AImp[a])[ts := true] ];
ensures eff == add ==> RImp == old(RImp);
ensures eff == rem ==> RImp == old(RImp)[a := old(RImp[a])[ts := true] ];
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
ensures (forall x:Element :: l[x] <==> (exists t:Timestamp :: AImp[x][t] && (forall tt:Timestamp :: RImp[x][tt] ==> tt < t ) ) );

//Read method description for the specification
procedure readSpec() returns (l:[Element]bool);
ensures (forall x:Element :: l[x] <==> S[x] );

//Refinemenet proof for add operations
//Assume (sigma, add(a), sigma') is the step of the implementation
//We show that (refMap(sigma), add(a), refMap(sigma')) is a valid step of the specification
procedure refAdd(a:Element, ta:Timestamp)
requires refinementMapping(AImp, RImp, S);
requires P1(AImp, RImp, add, a, ta);                    //We assume that A linearizes according to its timestamp
modifies AImp, RImp, S;
ensures (forall x:Element :: S[x] <==> (exists t:Timestamp :: AImp[x][t] && (forall tt:Timestamp :: RImp[x][tt] ==> tt < t ) ) );// refinementMapping(AImp, RImp, S);
{
    
    call apply(add, a, ta);
    call addSpec(a);

    assert (forall x:Element, t:Timestamp :: x != a ==> (AImp[x][t] <==> old(AImp[x][t]) ) );
}

//Refinemenet proof for remove operations
//Assume (sigma, remove(a), sigma') is the step of the implementation
//We show that (refMap(sigma), remove(a), refMap(sigma')) is a valid step of the specification
procedure refRem(a:Element, ta:Timestamp)
requires refinementMapping(AImp, RImp, S);
requires P1(AImp, RImp, rem, a, ta);                    //We assume that A linearizes according to its timestamp
modifies AImp, RImp, S;
ensures (forall x:Element :: S[x] <==> (exists t:Timestamp :: AImp[x][t] && (forall tt:Timestamp :: RImp[x][tt] ==> tt < t ) ) ); //refinementMapping(AImp, RImp, S);
{
    
    call apply(rem, a, ta);
    call removeSpec(a);

    assert (forall x:Element, t:Timestamp :: x != a ==> (RImp[x][t] <==> old(RImp[x][t]) ) );
}

//Refinemenet proof for read operations
//Assume (sigma, read()=>l, sigma') is the step of the implementation
//We show that (refMap(sigma), read()=>l, refMap(sigma')) is a valid step of the specification
procedure refRead()
requires refinementMapping(AImp, RImp, S);
ensures refinementMapping(AImp, RImp, S);
{
    var l1:[Element]bool, l2:[Element]bool;

    call l1 := readImp();
    call l2 := readSpec();

    assert (forall x:Element :: l1[x] == l2[x]);
}