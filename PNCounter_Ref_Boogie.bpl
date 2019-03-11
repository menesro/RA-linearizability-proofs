type Replica;
type effType;               //effector type for the implementation. It is either inc or dec

const unique inc:effType;
const unique dec:effType;

var P:[Replica]int;         //P set of the implementation state
var N:[Replica]int;         //N set of the implementation state
var cnt:int;                //state of the specification

//A function that calculates sum_{r in Replica} M[r] for an M:[Replica]int
function count(M:[Replica]int) returns (i:int);
axiom (forall i:int, r:Replica, M:[Replica]int :: count(M[r := i]) == count(M) - M[r] + i);

//Refinement relation : cnt == sum_{r in Replica} P[r] - sum_{r in Replica} N[r]
function refinementMapping(PP:[Replica]int, NN:[Replica]int, c:int ) returns (ret:bool);
axiom (forall PP:[Replica]int, NN:[Replica]int, c:int :: refinementMapping(PP, NN, c) <==>
            count(PP) - count (NN) == c
);

//apply method for the implementation. It can be used for both inc and dec effectors
procedure apply(eff:effType, r:Replica);
requires eff == inc || eff == dec;
modifies P, N;
ensures eff == inc ==> P == old(P)[r := old(P)[r]+1 ];
ensures eff == inc ==> N == old(N);
ensures eff == dec ==> P == old(P);
ensures eff == dec ==> N == old(N)[r := old(N)[r]+1 ];

//Increment method description for the specification
procedure incSpec();
modifies cnt;
ensures cnt == old(cnt) + 1;

//Decrement method description for the specification
procedure decSpec();
modifies cnt;
ensures cnt == old(cnt) - 1;

//Read method description for the implementation
procedure readImp() returns (k:int);
ensures k == count(P) - count(N);

//Read method description for the specification
procedure readSpec() returns (k:int);
ensures k == cnt;

//Refinemenet proof for inc operations
//Assume (sigma, inc(r), sigma') is the step of the implementation
//We show that (refMap(sigma), inc(), refMap(sigma')) is a valid step of the specification
procedure refInc(r:Replica)
requires refinementMapping(P, N, cnt);
modifies P, N, cnt;
ensures refinementMapping(P, N, cnt);
{
    call apply(inc, r);
    call incSpec();

    //assert false;
}

//Refinemenet proof for dec operations
//Assume (sigma, dec(r), sigma') is the step of the implementation
//We show that (refMap(sigma), dec(), refMap(sigma')) is a valid step of the specification
procedure refDec(r:Replica)
requires refinementMapping(P, N, cnt);
modifies P, N, cnt;
ensures refinementMapping(P, N, cnt);
{
    call apply(dec, r);
    call decSpec();

    //assert false;
}

//Refinemenet proof for read operations
//Assume (sigma, read()=>l, sigma') is the step of the implementation
//We show that (refMap(sigma), read()=>l, refMap(sigma')) is a valid step of the specification
procedure refRead()
requires refinementMapping(P, N, cnt);
ensures refinementMapping(P, N, cnt);
{
    var k1:int, k2:int;

    call k1 := readImp();
    call k2 := readSpec();
    assert k1 == k2;
    //assert false;
}