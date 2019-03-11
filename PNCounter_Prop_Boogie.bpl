type Replica;
type effType;               //effector type for the implementation. It is either inc or dec

const unique inc:effType;
const unique dec:effType;

//Various implementation state declarations for proving properties
//Each (Pi, Ni) pair corresponds to the state sigmai
//Each (PiP, NiP) pair corresponds to the state sigmai'
var P1:[Replica]int;
var N1:[Replica]int;
var P2:[Replica]int;
var N2:[Replica]int;

var P1P:[Replica]int;
var N1P:[Replica]int;
var P2P:[Replica]int;
var N2P:[Replica]int;

//P2 condition description
function Pred2(P:[Replica]int, N:[Replica]int, eff:effType, r:Replica) returns (ret:bool);
axiom (forall P:[Replica]int, N:[Replica]int, eff:effType, r:Replica :: Pred2(P,N,eff,r) <==> 
            (eff == inc || eff == dec) &&
            (eff == inc ==> P[r] == 0) &&
            (eff == dec ==> N[r] == 0)
);

//Apply method description for sigma1
procedure apply1(eff:effType, r:Replica);
requires eff == inc || eff == dec;
modifies P1, N1;
ensures eff == inc ==> P1 == old(P1)[r := old(P1)[r]+1 ];
ensures eff == inc ==> N1 == old(N1);
ensures eff == dec ==> P1 == old(P1);
ensures eff == dec ==> N1 == old(N1)[r := old(N1)[r]+1 ];

//Apply method description for sigma2
procedure apply2(eff:effType, r:Replica);
requires eff == inc || eff == dec;
modifies P2, N2;
ensures eff == inc ==> P2 == old(P2)[r := old(P2)[r]+1 ];
ensures eff == inc ==> N2 == old(N2);
ensures eff == dec ==> P2 == old(P2);
ensures eff == dec ==> N2 == old(N2)[r := old(N2)[r]+1 ];

//Apply method description for sigma1'
procedure apply1P(eff:effType, r:Replica);
requires eff == inc || eff == dec;
modifies P1P, N1P;
ensures eff == inc ==> P1P == old(P1P)[r := old(P1P)[r]+1 ];
ensures eff == inc ==> N1P == old(N1P);
ensures eff == dec ==> P1P == old(P1P);
ensures eff == dec ==> N1P == old(N1P)[r := old(N1P)[r]+1 ];

//Apply method description for sigma2'
procedure apply2P(eff:effType, r:Replica);
requires eff == inc || eff == dec;
modifies P2P, N2P;
ensures eff == inc ==> P2P == old(P2P)[r := old(P2P)[r]+1 ];
ensures eff == inc ==> N2P == old(N2P);
ensures eff == dec ==> P2P == old(P2P);
ensures eff == dec ==> N2P == old(N2P)[r := old(N2P)[r]+1 ];

//Merge method description for sigma1
procedure merge1(P:[Replica]int, N:[Replica]int );
modifies P1, N1;
ensures (forall r:Replica :: (old(P1)[r] < P[r] ==> P1[r] == P[r]) && (old(P1)[r] >= P[r] ==> P1[r] == old(P1)[r]  ) );
ensures (forall r:Replica :: (old(N1)[r] < N[r] ==> N1[r] == N[r]) && (old(N1)[r] >= N[r] ==> N1[r] == old(N1)[r]  ) );

//Merge method description for sigma2
procedure merge2(P:[Replica]int, N:[Replica]int );
modifies P2, N2;
ensures (forall r:Replica :: (old(P2)[r] < P[r] ==> P2[r] == P[r]) && (old(P2)[r] >= P[r] ==> P2[r] == old(P2)[r]  ) );
ensures (forall r:Replica :: (old(N2)[r] < N[r] ==> N2[r] == N[r]) && (old(N2)[r] >= N[r] ==> N2[r] == old(N2)[r]  ) );

//Merge method description for sigma1'
procedure merge1P(P:[Replica]int, N:[Replica]int );
modifies P1P, N1P;
ensures (forall r:Replica :: (old(P1P)[r] < P[r] ==> P1P[r] == P[r]) && (old(P1P)[r] >= P[r] ==> P1P[r] == old(P1P)[r]  ) );
ensures (forall r:Replica :: (old(N1P)[r] < N[r] ==> N1P[r] == N[r]) && (old(N1P)[r] >= N[r] ==> N1P[r] == old(N1P)[r]  ) );

//Merge method description for sigma2'
procedure merge2P(P:[Replica]int, N:[Replica]int );
modifies P2P, N2P;
ensures (forall r:Replica :: (old(P2P)[r] < P[r] ==> P2P[r] == P[r]) && (old(P2P)[r] >= P[r] ==> P2P[r] == old(P2P)[r]  ) );
ensures (forall r:Replica :: (old(N2P)[r] < N[r] ==> N2P[r] == N[r]) && (old(N2P)[r] >= N[r] ==> N2P[r] == old(N2P)[r]  ) );

//State-based inc method description for sigma1
//r argument is the ghost unique identifier for this replica
procedure inc1(r:Replica);
modifies P1;
ensures P1[r] == old(P1[r]) + 1;
ensures (forall rr:Replica :: r != rr ==> P1[rr] == old(P1[rr]));

//State-based dec method description for sigma1
//r argument is the ghost unique identifier for this replica
procedure dec1(r:Replica);
modifies N1;
ensures N1[r] == old(N1[r]) + 1;
ensures (forall rr:Replica :: r != rr ==> N1[rr] == old(N1[rr]));

//Property 1

//We aim to show that apply(apply(sigma, (eff1, r1) ), (eff2, r2)) == apply(apply(sigma, (eff2, r2) ), (eff1, r1)) where eff1, eff2 in {inc, dec}
//i.e., effectors commute.
//We assume that initially sigma1 == sigma2
//We apply (eff1, r1) and (eff2, r2) to sigma1 (in that order) and obtain a new sigma1
//We apply (eff2, r2) and (eff1, r1) to sigma2 (in that order) and obtain a new sigma2
//We show that sigma1 == sigma2 afterwards
procedure property1(eff1:effType, r1:Replica, eff2:effType, r2:Replica)
requires (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
requires eff1 == inc || eff1 == dec;
requires eff2 == inc || eff2 == dec;
modifies P1, N1, P2, N2;
ensures (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
{
    //apply(apply(sigma1, (eff1, r1) ), (eff2, r2)) 
    call apply1(eff1, r1);
    call apply1(eff2, r2);

    //apply(apply(sigma2, (eff2, r2) ), (eff1, r1))
    call apply2(eff2, r2);
    call apply2(eff1, r1);
}


//Property 2

//We aim to show merge(sigma, apply(sigma', (eff,r1) ) ) == apply(merge(sigma, sigma'), (eff,r1) ) where eff in {inc,dec}
//We assume that initially sigma1 == sigma2 and sigma1' == sigma2'
//We apply merge(sigma1, apply(sigma1',(eff,r1) )) and obtaina a new sigma1
//We apply apply(merge(sigma2, sigma2'), (eff,r1)) and obtain a new sigma2
//We show sigma1 == sigma2 at the end.
procedure property2(eff:effType, r1:Replica)
requires (forall r:Replica ::  P1[r] == P2[r] && N1[r] == N2[r]);
requires (forall r:Replica ::  P1P[r] == P2P[r] && N1P[r] == N2P[r]);
requires Pred2(P1, N1, eff, r1) && Pred2(P1P, N1P, eff, r1) && Pred2(P2, N2, eff, r1) && Pred2(P2P, N2P, eff, r1);
requires eff == inc || eff == dec;
modifies P1, N1, P2, N2, P1P, P2P, N1P, N2P;
ensures (forall r:Replica ::  P1[r] == P2[r] && N1[r] == N2[r]);
{
    //merge(sigma1, apply(sigma1',(eff,r1))
    call apply1P(eff,r1);
    call merge1(P1P, N1P);

    //apply(merge(sigma2, sigma2'), (eff,r1))
    call merge2(P2P, N2P);
    call apply2(eff,r1);
}

//Property 3

//We aim to show merge(apply(sigma, (eff,r1) ), apply(sigma', (eff,r1) ) ) == apply(merge(sigma,sigma'), (eff,r1) ) where eff in {inc,dec}
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(apply(sigma1, (eff,r1)), apply(sigma1', (eff,r1))) and obtain a new sigma1
//We apply apply(merge(sigma2,sigma2'), (eff,r1)) and obtain a new sigma2
//We show that sigma1 == sigma2 at the end
procedure property3(eff:effType, r1:Replica)
requires (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
requires (forall r:Replica :: P1P[r] == P2P[r] && N1P[r] == N2P[r]);
requires eff == inc || eff == dec;
modifies P1, N1, P2, N2, P1P, P2P, N1P, N2P;
ensures (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
{
    //merge(apply(sigma1, (eff,r1)), apply(sigma1', (eff,r1)))
    call apply1(eff, r1);
    call apply1P(eff, r1);
    call merge1(P1P, N1P);

    //apply(merge(sigma2,sigma2'), (eff,r1))
    call merge2(P2P, N2P);
    call apply2(eff, r1);
}

//Property 4

//First, we show merge(sigma, sigma) == sigma
procedure property4a()
modifies P1, N1;
ensures (forall r:Replica :: P1[r] == old(P1)[r] && N1[r] == old(N1)[r]);
{
    call merge1(P1,N1);
}

//Next, we aim to show merge(sigma, sigma') == merge(sigma', sigma)
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(sigma1, sigma1') and obtain a new sigma1
//We apply merge(sigma2', sigma2) and obtain a new sigma2'
//We show that sigma1 == sigma2'
procedure property4b()
requires (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
requires (forall r:Replica :: P1P[r] == P2P[r] && N1P[r] == N2P[r]);
modifies P1, N1, P2P, N2P;
ensures (forall r:Replica :: P1[r] == P2P[r] && N1[r] == N2P[r]);
{
    //merge(sigma1, sigma1')
    call merge1(P1P, N1P);

    //merge(sigma2', sigma2)
    call merge2P(P2, N2);
}

//Property 5

//We aim to show that the state after applying inc(r1) to sigma is the same as apply(sigma,(inc, r1))
//We assume that initially sigma1 == sigma2 
//We apply inc(r1) to sigma1 and obtain a new sigma1
//We apply apply(sigma2, (inc,r1)) and obtain a new sigma2
//We show that sigma1 == sigma2 after applying the operations
procedure property5Inc(r1:Replica)
requires (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
modifies P1, P2, N2;
ensures (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
{
    //inc(r1)
    call inc1(r1);

    //apply(sigma2, (inc,r1) )
    call apply2(inc, r1);
}

//We aim to show that the state after applying dec(r1) to sigma is the same as apply(sigma,(dec, r1))
//We assume that initially sigma1 == sigma2 
//We apply dec(r1) to sigma1 and obtain a new sigma1
//We apply apply(sigma2, (dec,r1)) and obtain a new sigma2
//We show that sigma1 == sigma2 after applying the operations
procedure property5Dec(r1:Replica)
requires (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
modifies N1, P2, N2;
ensures (forall r:Replica :: P1[r] == P2[r] && N1[r] == N2[r]);
{
    //dec(r1)
    call dec1(r1);

    //apply(sigma2, (dec,r1) )
    call apply2(dec, r1);
}

//Proof of Pred2 (P2 in the paper)
//Goal: Let sigma1=(P1,N1) be obtained by applying a sequence S of local effectors to
//the initial state (i.e., both P and N counters are 0 for all replicas) and (eff, r1) be a local effector. We claim that:
//P1[r1] == 0 iff for all (eff', x') in S, (eff', x') != (eff, r1) (for the case eff == inc )
//N1[r1] == 0 iff for all (eff', x') in S, (eff', x') != (eff, r1) (for the case eff == dec )
//Proof is based on induction on the length of S.


//Base case: length(S) == 0. So, P1[r] and N1[r] are zero for all replicas r.
procedure proofPred2Base(eff:effType, r1:Replica)
requires eff == inc || eff == dec;
requires (forall r:Replica :: P1[r] == 0 && N1[r] == 0);
ensures Pred2(P1, N1, eff, r1);
{
}

//Inductive case: Assume Pred2(sigma1, eff, r1) holds.
//If we apply (eff2, r2) to sigma1 s.t. (eff2, r2) != (eff, r1),
//then Pred2(sigma1, eff, r1) holds after applying (eff2, r2) as well.
procedure proofPred2Induction(eff:effType, r1:Replica)
requires eff == inc || eff == dec;
requires Pred2(P1, N1, eff, r1);
modifies P1, N1;
ensures Pred2(P1, N1, eff, r1);
{
    var eff2:effType, r2:Replica;

    assume eff2 == inc || eff2 == dec;
    assume !(eff == eff2 && r1 == r2);
    call apply1(eff2, r2); 
}