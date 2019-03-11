type Element;
type effType;                //effector type for the implementation. It is either add or rem (remove)

const unique rem:effType;
const unique add:effType;

//Various implementation state definitions for proving properties
//Each (Ai, Ri) pair corresponds to sigmai
//Each (AiP, RiP) pair corresponds to sigmai'
var A1:[Element]bool;
var R1:[Element]bool;
var A2:[Element]bool;
var R2:[Element]bool;

var A1P:[Element]bool;
var R1P:[Element]bool;
var A2P:[Element]bool;
var R2P:[Element]bool;

//P2 conditiond description
function P2(A:[Element]bool, R:[Element]bool, eff:effType, a:Element) returns (ret:bool);
axiom (   
    forall A:[Element]bool, R:[Element]bool, eff:effType, a:Element :: P2(A,R,eff,a) <==>
        (eff == add || eff == rem) &&
        (eff == add ==> !A[a] ) &&
        (eff == rem ==> !R[a])
);

//Apply method description for sigma1
procedure apply1(eff:effType, a:Element);
requires eff == add || eff == rem;
modifies A1, R1;
ensures eff == add ==> A1 == old(A1)[a := true];
ensures eff == add ==> R1 == old(R1);
ensures eff == rem ==> R1 == old(R1)[a := true];
ensures eff == rem ==> A1 == old(A1);

//Apply method description for sigma2
procedure apply2(eff:effType, a:Element);
requires eff == add || eff == rem;
modifies A2, R2;
ensures eff == add ==> A2 == old(A2)[a := true];
ensures eff == add ==> R2 == old(R2);
ensures eff == rem ==> R2 == old(R2)[a := true];
ensures eff == rem ==> A2 == old(A2);

//Apply method description for sigma1P
procedure apply1P(eff:effType, a:Element);
requires eff == add || eff == rem;
modifies A1P, R1P;
ensures eff == add ==> A1P == old(A1P)[a := true];
ensures eff == add ==> R1P == old(R1P);
ensures eff == rem ==> R1P == old(R1P)[a := true];
ensures eff == rem ==> A1P == old(A1P);

//Apply method description for sigma2P
procedure apply2P(eff:effType, a:Element);
requires eff == add || eff == rem;
modifies A2P, R2P;
ensures eff == add ==> A2P == old(A2P)[a := true];
ensures eff == add ==> R2P == old(R2P);
ensures eff == rem ==> R2P == old(R2P)[a := true];
ensures eff == rem ==> A2P == old(A2P);

//Merge method description for sigma1
procedure merge1(A:[Element]bool, R:[Element]bool );
modifies A1, R1;
ensures (forall x:Element :: A1[x] <==> old(A1)[x] || A[x] );
ensures (forall x:Element :: R1[x] <==> old(R1)[x] || R[x] );

//Merge method description for sigma2
procedure merge2(A:[Element]bool, R:[Element]bool );
modifies A2, R2;
ensures (forall x:Element :: A2[x] <==> old(A2)[x] || A[x] );
ensures (forall x:Element :: R2[x] <==> old(R2)[x] || R[x] );

//Merge method description for sigma1P
procedure merge1P(A:[Element]bool, R:[Element]bool );
modifies A1P, R1P;
ensures (forall x:Element :: A1P[x] <==> old(A1P)[x] || A[x] );
ensures (forall x:Element :: R1P[x] <==> old(R1P)[x] || R[x] );

//Merge method description for sigma2P
procedure merge2P(A:[Element]bool, R:[Element]bool );
modifies A2P, R2P;
ensures (forall x:Element :: A2P[x] <==> old(A2P)[x] || A[x] );
ensures (forall x:Element :: R2P[x] <==> old(R2P)[x] || R[x] );

//State-based add method description for sigma1
procedure add(a:Element);
modifies A1;
ensures A1 == old(A1)[a := true];

//State-based remove method description for sigma1
procedure remove(a:Element);
modifies R1;
ensures R1 == old(R1)[a := true];


//Property 1

//We aim to show that apply(apply(sigma, (eff1, a) ), (eff2, b)) == apply(apply(sigma, (eff2, b) ), (eff1, a)) where eff1, eff2 in {add, rem}
//i.e., effectors commute.
//We assume that initially sigma1 == sigma2
//We apply (eff1, a) and (eff2, b) to sigma1 (in that order) and obtain a new sigma1
//We apply (eff2, b) and (eff1, a) to sigma2 (in that order) and obtain a new sigma2
//We show that sigma1 == sigma2 afterwards
procedure property1(eff1:effType, a:Element, eff2:effType, b:Element)
requires (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
requires eff1 == add || eff1 == rem;
requires eff2 == add || eff2 == rem;
modifies A1, R1, A2, R2;
ensures (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
{
    //apply(apply(sigma1, (eff1, a) ), (eff2, b)) 
    call apply1(eff1, a);
    call apply1(eff2, b);

    //apply(apply(sigma2, (eff2, b) ), (eff1, a))
    call apply2(eff2, b);
    call apply2(eff1, a);
}

//Property 2

//We aim to show merge(sigma, apply(sigma', (eff,a) ) ) == apply(merge(sigma, sigma'), (eff,a) ) where eff in {add,rem}
//We assume that initially sigma1 == sigma2 and sigma1' == sigma2'
//We apply merge(sigma1, apply(sigma1',(eff,a) )) and obtaina a new sigma1
//We apply apply(merge(sigma2, sigma2'), (eff,a)) and obtain a new sigma2
//We show sigma1 == sigma2 at the end.
procedure property2(eff:effType, a:Element)
requires (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
requires (forall x:Element ::  A1P[x] == A2P[x] && R1P[x] == R2P[x]);
requires P2(A1, R1, eff, a) && P2(A1P, R1P, eff, a) && P2(A2, R2, eff, a) && P2(A2P, R2P, eff, a);
requires eff == add || eff == rem;
modifies A1, R1, A2, R2, A1P, A2P, R1P, R2P;
ensures (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
{
    //merge(sigma1, apply(sigma1',(eff,a) ))
    call apply1P(eff,a);
    call merge1(A1P, R1P);

    //apply(merge(sigma2, sigma2'), (eff,a))
    call merge2(A2P, R2P);
    call apply2(eff,a);
}

//Property 3

//We aim to show merge(apply(sigma, (eff,a) ), apply(sigma', (eff,a) ) ) == apply(merge(sigma,sigma'), (eff,a) ) where eff in {add,rem}
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(apply(sigma1, (eff,a)), apply(sigma1', (eff,a))) and obtain a new sigma1
//We apply apply(merge(sigma2,sigma2'), (eff,a)) and obtain a new sigma2
//We show that sigma1 == sigma2 at the end
procedure property3(eff:effType, a:Element)
requires (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
requires (forall x:Element ::  A1P[x] == A2P[x] && R1P[x] == R2P[x]);
requires eff == add || eff == rem;
modifies A1, R1, A2, R2, A1P, A2P, R1P, R2P;
ensures (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
{
    //merge(apply(sigma1, (eff,a)), apply(sigma1', (eff,a)))
    call apply1(eff, a);
    call apply1P(eff, a);
    call merge1(A1P, R1P);

    //apply(merge(sigma2,sigma2'), (eff,a))
    call merge2(A2P, R2P);
    call apply2(eff, a);
}

//Property4

//First, we show merge(sigma, sigma) == sigma
procedure property4a()
modifies A1, R1;
ensures (forall x:Element :: A1[x] == old(A1)[x] && R1[x] == old(R1)[x]);
{
    call merge1(A1,R1);
}

//Next, we aim to show merge(sigma, sigma') == merge(sigma', sigma)
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(sigma1, sigma1') and obtain a new sigma1
//We apply merge(sigma2', sigma2) and obtain a new sigma2'
//We show that sigma1 == sigma2'
procedure property4b()
requires (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
requires (forall x:Element ::  A1P[x] == A2P[x] && R1P[x] == R2P[x]);
modifies A1, R1, A2P, R2P;
ensures (forall x:Element :: A1[x] == A2P[x] && R1[x] == R2P[x] );
{
    //merge(sigma1, sigma1')
    call merge1(A1P, R1P);

    //merge(sigma2', sigma2)
    call merge2P(A2, R2);
}

//Property 5

//We aim to show that the state after applying add(a) to sigma is the same as apply(sigma,(add, a))
//We assume that sigma1 == sigma2 
//We apply add(a) to sigma1 and obtain a new sigma1
//We apply apply(sigma2, (add,a)) and obtain a new sigma2
//We show that sigma1 == sigma2 afterwards
procedure property5Add(a:Element)
requires (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
modifies A1, A2, R2;
ensures (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
{
    //add(a)
    call add(a);

    //apply(sigma2, (add,a) )
    call apply2(add, a);
}

//We aim to show that the state after applying remove(a) to sigma is the same as apply(sigma,(rem, a))
//We assume that sigma1 == sigma2 
//We apply remove(a) to sigma1 and obtain a new sigma1
//We apply apply(sigma2, (rem,a)) and obtain a new sigma2
//We show that sigma1 == sigma2 afterwards
procedure property5Rem(a:Element)
requires (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
modifies R1, A2, R2;
ensures (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
{
    //add(a)
    call remove(a);

    //apply(sigma2, (add,a) )
    call apply2(rem, a);
}


//Property 6

//We aim to show that apply(apply(sigma, (eff,a) ), (eff, a) ) == apply(sigma, (eff, a)) where eff in {add,rem}
//We assume sigma1 == sigma2 initially
//We apply apply(apply(sigma1, (eff, a)), (eff,a) ) and obtain a new sigma1
//We apply apply(sigma2, (eff,a)) and obtain a new sigma2 
//We show that sigma1 == sigma2 afterwards
procedure property6(eff:effType, a:Element)
requires (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
requires eff == add || eff == rem;
modifies A1, R1, A2, R2;
ensures (forall x:Element ::  A1[x] == A2[x] && R1[x] == R2[x]);
{
    //apply(apply(sigma1, (eff, a)), (eff,a) )
    call apply1(eff,a);
    call apply1(eff,a);

    //apply(sigma2, (eff,a))
    call apply2(eff,a);
}


//Proof of P2 
//Goal: Let sigma1=(A1,R1) be obtained by applying a set S of local effectors to
//the initial state (i.e., both A and R are empty sets) and (eff, a) be a local effector. We claim that:
//a not in A1 iff for all (eff', x') in S, (eff', x') != (eff, a) (for the case eff == add )
//a not in R1 iff for all (eff', x') in S, (eff', x') != (eff, a) (for the case eff == rem )
//Proof is based on induction on the size of S.

//Base case: |S| == 0. So, A1 and R1 are empty sets.
procedure proofP2Base(eff:effType, a:Element)
requires eff == add || eff == rem;
requires (forall x:Element :: !A1[x] && !R1[x]);
ensures P2(A1, R1, eff, a);
{

}

//Inductive case: Assume P2(sigma1, eff, a) holds.
//If we apply (eff2, b) to sigma1 s.t. (eff2, b) != (eff, a),
//then P2(sigma1, eff, a) holds after applying (eff2, b) as well.
procedure proofP2Induction(eff:effType, a:Element)
requires eff == add || eff == rem;
requires P2(A1, R1, eff, a);
modifies A1, R1;
ensures P2(A1, R1, eff, a);
{
    var eff2:effType, b:Element;

    assume eff2 == add || eff2 == rem;
    assume !(eff == eff2 && a== b);
    call apply1(eff2, b); 
}