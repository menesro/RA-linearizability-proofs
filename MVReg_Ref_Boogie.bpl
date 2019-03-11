type Element;
type Replica;
type VecClk = [Replica]int;

//State: set of pairs (a, VC), where a is an element and VC is a vector clock, a map of the form: Replica -> int
var S:[Element][VecClk]bool;            //State of the implementation
var F:[Element][VecClk]bool;            //State of the specification

//A function that defines a partial order on vector clocks
function less(v1:VecClk, v2:VecClk) returns (ret:bool);
axiom (forall v1:VecClk, v2:VecClk :: less(v1,v2) <==>
        (forall r:Replica :: v1[r] <= v2[r]) &&
        (exists r:Replica :: v1[r] < v2[r])
);

//Refinement relation : S = F
function refinementMapping(SS:[Element][VecClk]bool, FF:[Element][VecClk]bool) returns (ret:bool);
axiom (forall SS:[Element][VecClk]bool, FF:[Element][VecClk]bool::  refinementMapping(SS, FF) <==> 
            (forall x:Element, v:VecClk  :: SS[x][v] <==> FF[x][v] )
);

//Apply method description for the implementation
//Since only effector type is write, it is implicitly determined
procedure apply(a:Element, V:VecClk);
modifies S;
ensures S[a][V];
ensures (forall x:Element, v:VecClk :: less(v, V) ==> !S[x][v]);
ensures (forall x:Element, v:VecClk :: !(a == x && v == V) && !less(v,V) ==> S[x][v] == old(S)[x][v] );

//Write method description for the specification
procedure writeSpec(a:Element, V:VecClk);
modifies F;
ensures F[a][V];
ensures (forall x:Element, v:VecClk :: less(v, V) ==> !F[x][v]);
ensures (forall x:Element, v:VecClk :: !(a == x && v == V) && !less(v,V) ==> F[x][v] == old(F)[x][v] );

//Read method description for the implementation
procedure readImp() returns (l:[Element]bool);
ensures (forall x:Element :: l[x] <==> (exists v:VecClk :: S[x][v] )  );

//Read method description for the specification
procedure readSpec() returns (l:[Element]bool);
ensures (forall x:Element :: l[x] <==> (exists v:VecClk :: F[x][v] )  );

//Refinemenet proof for write operations
//Assume (sigma, write(a, Va), sigma') is the step of the implementation
//We show that (refMap(sigma), write(a, Va), refMap(sigma')) is a valid step of the specification
procedure refWrite(a:Element, Va:VecClk)
requires refinementMapping(S, F);
modifies S, F;
ensures refinementMapping(S, F);
{
    call apply(a, Va);
    call writeSpec(a, Va);
}

//Refinemenet proof for read operations
//Assume (sigma, read()=>l, sigma') is the step of the implementation
//We show that (refMap(sigma), read()=>l, refMap(sigma')) is a valid step of the specification
procedure refRead()
requires refinementMapping(S, F);
ensures refinementMapping(S, F);
{
    var l1:[Element]bool, l2:[Element]bool;

    call l1 := readImp();
    call l2 := readSpec();

    assert (forall x:Element :: l1[x] <==> l2[x] );
}