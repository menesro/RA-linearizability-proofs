type Element;
type Timestamp = int;
type effType;                //effector type for the implementation. It is either add or rem (remove)

const unique rem:effType;
const unique add:effType;

//Various implementation state declarations for proving properties
//Each (Ai, Ri) pair corresponds to to the state sigmai
//Each (AiP, RiP) pair corresponds to to the state sigmai'
var A1:[Element][Timestamp]bool;
var R1:[Element][Timestamp]bool;
var A2:[Element][Timestamp]bool;
var R2:[Element][Timestamp]bool;

var A1P:[Element][Timestamp]bool;
var R1P:[Element][Timestamp]bool;
var A2P:[Element][Timestamp]bool;
var R2P:[Element][Timestamp]bool;

//P1 condition description
function P1(A:[Element][Timestamp]bool, R:[Element][Timestamp]bool, eff:effType, a:Element, ts:Timestamp) returns (ret:bool);
axiom (  forall A:[Element][Timestamp]bool, R:[Element][Timestamp]bool, eff:effType, a:Element, ts:Timestamp :: P1(A, R, eff, a, ts) <==>
            (forall b:Element, tb:Timestamp :: A[b][tb] || R[b][tb] ==> tb < ts )
);

//Apply method description for sigma1
procedure apply1(eff:effType, a:Element, ts:Timestamp);
requires eff == add || eff == rem;
modifies A1, R1;
ensures eff == add ==> A1 == old(A1)[a := old(A1[a])[ts := true] ];
ensures eff == add ==> R1 == old(R1);
ensures eff == rem ==> R1 == old(R1)[a := old(R1[a])[ts := true] ];
ensures eff == rem ==> A1 == old(A1);

//Apply method description for sigma2
procedure apply2(eff:effType, a:Element, ts:Timestamp);
requires eff == add || eff == rem;
modifies A2, R2;
ensures eff == add ==> A2 == old(A2)[a := old(A2[a])[ts := true] ];
ensures eff == add ==> R2 == old(R2);
ensures eff == rem ==> R2 == old(R2)[a := old(R2[a])[ts := true] ];
ensures eff == rem ==> A2 == old(A2);

//Apply method description for sigma1P
procedure apply1P(eff:effType, a:Element, ts:Timestamp);
requires eff == add || eff == rem;
modifies A1P, R1P;
ensures eff == add ==> A1P == old(A1P)[a := old(A1P[a])[ts := true] ];
ensures eff == add ==> R1P == old(R1P);
ensures eff == rem ==> R1P == old(R1P)[a := old(R1P[a])[ts := true] ];
ensures eff == rem ==> A1P == old(A1P);

//Apply method description for sigma2P
procedure apply2P(eff:effType, a:Element, ts:Timestamp);
requires eff == add || eff == rem;
modifies A2P, R2P;
ensures eff == add ==> A2P == old(A2P)[a := old(A2P[a])[ts := true] ];
ensures eff == add ==> R2P == old(R2P);
ensures eff == rem ==> R2P == old(R2P)[a := old(R2P[a])[ts := true] ];
ensures eff == rem ==> A2P == old(A2P);

//Merge method description for sigma1
procedure merge1(A:[Element][Timestamp]bool, R:[Element][Timestamp]bool );
modifies A1, R1;
ensures (forall x:Element, ts:Timestamp :: A1[x][ts] <==> old(A1)[x][ts] || A[x][ts] );
ensures (forall x:Element, ts:Timestamp :: R1[x][ts] <==> old(R1)[x][ts] || R[x][ts] );

//Merge method description for sigma2
procedure merge2(A:[Element][Timestamp]bool, R:[Element][Timestamp]bool );
modifies A2, R2;
ensures (forall x:Element, ts:Timestamp :: A2[x][ts] <==> old(A2)[x][ts] || A[x][ts] );
ensures (forall x:Element, ts:Timestamp :: R2[x][ts] <==> old(R2)[x][ts] || R[x][ts] );

//Merge method description for sigma1P
procedure merge1P(A:[Element][Timestamp]bool, R:[Element][Timestamp]bool );
modifies A1P, R1P;
ensures (forall x:Element, ts:Timestamp :: A1P[x][ts] <==> old(A1P)[x][ts] || A[x][ts] );
ensures (forall x:Element, ts:Timestamp :: R1P[x][ts] <==> old(R1P)[x][ts] || R[x][ts] );

//Merge method description for sigma2P
procedure merge2P(A:[Element][Timestamp]bool, R:[Element][Timestamp]bool );
modifies A2P, R2P;
ensures (forall x:Element, ts:Timestamp :: A2P[x][ts] <==> old(A2P)[x][ts] || A[x][ts] );
ensures (forall x:Element, ts:Timestamp :: R2P[x][ts] <==> old(R2P)[x][ts] || R[x][ts] );

//State-based add method description for sigma1
//It is divided into two submethods: genAdd(a) generates the timestamp
procedure genAdd(a:Element) returns (ta:Timestamp);
ensures P1(A1, R1, add, a, ta);

//effAdd(a,ta) adds this pair to A1
procedure effAdd(a:Element, ta:Timestamp);
modifies A1;
ensures A1 == old(A1)[ a := old(A1[a])[ta := true] ];

//State-based remove method description for sigma1
//It is divided into two submethods: genRem(a) generates the timestamp
procedure genRem(a:Element) returns (ta:Timestamp);
ensures P1(A1, R1, rem, a, ta);

//effRem(a,ta) adds this pair to R1
procedure effRem(a:Element, ta:Timestamp);
modifies R1;
ensures R1 == old(R1)[ a := old(R1[a])[ta := true] ];

//Property 1

//We aim to show that apply(apply(sigma, (eff1, a, ta) ), (eff2, b, tb)) == apply(apply(sigma, (eff2, b, tb) ), (eff1, a, ta)) where eff1, eff2 in {add, rem}
//when two methods are concurrent (this does not bring any extra assumptions) 
//i.e., effectors commute.
//We assume that initially sigma1 == sigma2
//We apply (eff1, a, ta) and (eff2, b, tb) to sigma1 (in that order) and obtain a new sigma1
//We apply (eff2, b, tb) and (eff1, a, ta) to sigma2 (in that order) and obtain a new sigma2
//We show that sigma1 == sigma2 afterwards
procedure property1(eff1:effType, a:Element, ta:Timestamp, eff2:effType, b:Element, tb:Timestamp)
requires (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
requires eff1 == add || eff1 == rem;
requires eff2 == add || eff2 == rem;
modifies A1, R1, A2, R2;
ensures (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
{
    //apply(apply(sigma1, (eff1, a, ta) ), (eff2, b, tb)) 
    call apply1(eff1, a, ta);
    call apply1(eff2, b, tb);

    //apply(apply(sigma2, (eff2, b, tb) ), (eff1, a, ta))
    call apply2(eff2, b, tb);
    call apply2(eff1, a, ta);

    //assert false;
}

//Property 2

//We aim to show merge(sigma, apply(sigma', (eff, a, ta) ) ) == apply(merge(sigma, sigma'), (eff,a, ta) ) where eff in {add,rem}
//when P1(sigma1, eff, a, ta) and P1(sigma1', eff, a, ta) holds
//We assume that initially sigma1 == sigma2 and sigma1' == sigma2'
//We apply merge(sigma1, apply(sigma1',(eff,a,ta) )) and obtaina a new sigma1
//We apply apply(merge(sigma2, sigma2'), (eff,a,ta)) and obtain a new sigma2
//We show sigma1 == sigma2 at the end.
procedure property2(eff:effType, a:Element, ta:Timestamp)
requires (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
requires (forall x:Element, t:Timestamp ::  A1P[x][t] == A2P[x][t] && R1P[x][t] == R2P[x][t]);
requires P1(A1, R1, eff, a, ta) && P1(A1P, R1P, eff, a, ta) && P1(A2, R2, eff, a, ta) && P1(A2P, R2P, eff, a, ta);
requires eff == add || eff == rem;
modifies A1, R1, A2, R2, A1P, A2P, R1P, R2P;
ensures (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
{
    //merge(sigma1, apply(sigma1',(eff,a, ta) ))
    call apply1P(eff, a, ta);
    call merge1(A1P, R1P);

    //apply(merge(sigma2, sigma2'), (eff,a, ta))
    call merge2(A2P, R2P);
    call apply2(eff, a, ta);

    //assert false;
}

//Property 3

//We aim to show merge(apply(sigma, (eff, a, ta) ), apply(sigma', (eff, a, ta) ) ) == apply(merge(sigma,sigma'), (eff,a, ta) ) where eff in {add,rem}
//when P1(sigma1, eff, a, ta) and P1(sigma1', eff, a, ta) holds
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(apply(sigma1, (eff,a,ta)), apply(sigma1', (eff,a,ta))) and obtain a new sigma1
//We apply apply(merge(sigma2,sigma2'), (eff,a,ta)) and obtain a new sigma2
//We show that sigma1 == sigma2 at the end
procedure property3(eff:effType, a:Element, ta:Timestamp)
requires (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
requires (forall x:Element, t:Timestamp ::  A1P[x][t] == A2P[x][t] && R1P[x][t] == R2P[x][t]);
requires P1(A1, R1, eff, a, ta) && P1(A1P, R1P, eff, a, ta) && P1(A2, R2, eff, a, ta) && P1(A2P, R2P, eff, a, ta);
requires eff == add || eff == rem;
modifies A1, R1, A2, R2, A1P, A2P, R1P, R2P;
ensures (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
{
    //merge(apply(sigma1, (eff, a, ta)), apply(sigma1', (eff, a, ta)))
    call apply1(eff, a, ta);
    call apply1P(eff, a, ta);
    call merge1(A1P, R1P);

    //apply(merge(sigma2, sigma2'), (eff, a, ta))
    call merge2(A2P, R2P);
    call apply2(eff, a, ta);

    //assert false;
}

//Property 4

//First, we show merge(sigma, sigma) == sigma
procedure property4a()
modifies A1, R1;
ensures (forall x:Element, t:Timestamp :: A1[x][t] == old(A1)[x][t] && R1[x][t] == old(R1)[x][t]);
{
    call merge1(A1,R1);

    //assert false;
}

//Next, we aim to show merge(sigma, sigma') == merge(sigma', sigma)
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(sigma1, sigma1') and obtain a new sigma1
//We apply merge(sigma2', sigma2) and obtain a new sigma2'
//We show that sigma1 == sigma2'
procedure property4b()
requires (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
requires (forall x:Element, t:Timestamp ::  A1P[x][t] == A2P[x][t] && R1P[x][t] == R2P[x][t]);
modifies A1, R1, A2P, R2P;
ensures (forall x:Element, t:Timestamp ::  A1[x][t] == A2P[x][t] && R1[x][t] == R2P[x][t]);
{
    //merge(sigma1, sigma1')
    call merge1(A1P, R1P);

    //merge(sigma2', sigma2)
    call merge2P(A2, R2);

    //assert false;
}


//Property 5

//We aim to show that the state after applying genAdd(a);effAdd(a,ts) to sigma is the same as apply(sigma,(add, a))
//We assume that initially sigma1 == sigma2 
//We apply genAdd(a);effadd(a,ts) to sigma1 and obtain a new sigma1
//We apply apply(sigma2, (add,a,ta)) and obtain a new sigma2
//We show that sigma1 == sigma2 after applying the operations
procedure property5Add(a:Element)
requires (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
modifies A1, A2, R2;
ensures (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
{
    var ta:Timestamp;
    //add(a) == genAdd(a):ta; effAdd(a, ta);
    call ta := genAdd(a);
    call effAdd(a, ta);

    //apply(sigma2, (add, a, ta) )
    call apply2(add, a, ta);

    //assert false;
}

//We aim to show that the state after applying genRem(a);effRem(a,ts) to sigma is the same as apply(sigma,(rem, a))
//We assume that sigma1 == sigma2 
//We apply genRem(a);effRem(a,ts) to sigma1 and obtain a new sigma1
//We apply apply(sigma2, (rem,a,ta)) and obtain a new sigma2
//We show that sigma1 == sigma2 afterwards
procedure property5Rem(a:Element)
requires (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
modifies R1, A2, R2;
ensures (forall x:Element, t:Timestamp ::  A1[x][t] == A2[x][t] && R1[x][t] == R2[x][t]);
{
    var ta:Timestamp;
    //remove(a) == genRem(a):ta; effRem(a, ta);
    call ta := genRem(a);
    call effRem(a, ta);

    //apply(sigma2, (rem, a, ta) )
    call apply2(rem, a, ta);

    //assert false;
}

//Proof of P2 
//Goal: Let sigma1=(A1,R1) be obtained by applying a set S of local effectors to
//the initial state (i.e., both A and R are empty sets) and (eff, a, ta) be a local effector next to be applied. 
//We claim that: ta > t for all (x,t) in A1 union R1
//Proof is based on induction on the size of S.

//Base case: |S| == 0. So, A1 and R1 are empty sets.
procedure proofP1Base(eff:effType, a:Element, ta:Timestamp)
requires eff == add || eff == rem;
requires (forall x:Element, t:Timestamp :: !A1[x][t] && !R1[x][t]);
ensures P1(A1, R1, eff, a, ta);
{
    //assert false;
}

//Inductive case: Assume P1(sigma1, eff, a, ta) holds.
//If we apply (eff2, b, tb) to sigma1 s.t. (eff2, b, tb) != (eff, a, ta),
//then P2(sigma1, eff, a, ta) holds after applying (eff2, b, tb) as well.
procedure proofP1Induction(eff:effType, a:Element, ta:Timestamp)
requires eff == add || eff == rem;
requires P1(A1, R1, eff, a, ta);
modifies A1, R1;
ensures P1(A1, R1, eff, a, ta);
{
    var eff2:effType, b:Element, tb:Timestamp;

    assume eff2 == add || eff2 == rem;
    assume !(eff == eff2 && a== b) && tb < ta;
    call apply1(eff2, b, tb); 

    //assert false;
}