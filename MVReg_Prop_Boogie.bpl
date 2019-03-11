type Element;
type Replica;
type VecClk = [Replica]int;

//Implementation state: set of pairs (a, VC), where a is an element and VC is a vector clock, a map of the form: Replica -> int
//Each Si corresponds to the state sigmai
//Each SiP corresponds to the state sigmai'
var S1:[Element][VecClk]bool;
var S2:[Element][VecClk]bool;
var S1P:[Element][VecClk]bool;
var S2P:[Element][VecClk]bool;

//A function that defines a partial order on vector clocks
function less(v1:VecClk, v2:VecClk) returns (ret:bool);
axiom (forall v1:VecClk, v2:VecClk :: less(v1,v2) <==>
        (forall r:Replica :: v1[r] <= v2[r]) &&
        (exists r:Replica :: v1[r] < v2[r])
);

//P1 predicate description
function P1(S:[Element][VecClk]bool, a:Element, v:VecClk ) returns (ret:bool);
axiom (forall S:[Element][VecClk]bool, a:Element, v:VecClk :: P1(S,a,v) <==>
            (forall x:Element, vv:VecClk :: S[x][vv] ==> !less(v,vv) )
);

//Apply method description for sigma1
//Since only effector type is write, it is implicitly determined
procedure apply1(a:Element, V:VecClk);
modifies S1;
ensures S1[a][V];
ensures (forall x:Element, v:VecClk :: less(v, V) ==> !S1[x][v]);
ensures (forall x:Element, v:VecClk :: !(a == x && v == V) && !less(v,V) ==> S1[x][v] == old(S1)[x][v] );

//Apply method description for sigma2
//Since only effector type is write, it is implicitly determined
procedure apply2(a:Element, V:VecClk);
modifies S2;
ensures S2[a][V];
ensures (forall x:Element, v:VecClk :: less(v, V) ==> !S2[x][v]);
ensures (forall x:Element, v:VecClk :: !(a == x && v == V) && !less(v,V) ==> S2[x][v] == old(S2)[x][v] );

//Apply method description for sigma1'
//Since only effector type is write, it is implicitly determined
procedure apply1P(a:Element, V:VecClk);
modifies S1P;
ensures S1P[a][V];
ensures (forall x:Element, v:VecClk :: less(v, V) ==> !S1P[x][v]);
ensures (forall x:Element, v:VecClk :: !(a == x && v == V) && !less(v,V) ==> S1P[x][v] == old(S1P)[x][v] );

//Apply method description for sigma2'
//Since only effector type is write, it is implicitly determined
procedure apply2P(a:Element, V:VecClk);
modifies S2P;
ensures S2P[a][V];
ensures (forall x:Element, v:VecClk :: less(v, V) ==> !S2P[x][v]);
ensures (forall x:Element, v:VecClk :: !(a == x && v == V) && !less(v,V) ==> S2P[x][v] == old(S2P)[x][v] );

//Merge method description for sigma1
procedure merge1(S:[Element][VecClk]bool);
modifies S1;
ensures (forall x:Element, v:VecClk :: S1[x][v] <==> (old(S1)[x][v] && (forall xx:Element, vv:VecClk :: S[xx][vv] ==> !less(v, vv) ) ) ||
                                                     (S[x][v] && (forall xx:Element, vv:VecClk :: old(S1)[xx][vv] ==> !less(v, vv) ) )
);

//Merge method description for sigma2
procedure merge2(S:[Element][VecClk]bool);
modifies S2;
ensures (forall x:Element, v:VecClk :: S2[x][v] <==> (old(S2)[x][v] && (forall xx:Element, vv:VecClk :: S[xx][vv] ==> !less(v, vv) ) ) ||
                                                     (S[x][v] && (forall xx:Element, vv:VecClk :: old(S2)[xx][vv] ==> !less(v, vv) ) )
);

//Merge method description for sigma1P
procedure merge1P(S:[Element][VecClk]bool);
modifies S1P;
ensures (forall x:Element, v:VecClk :: S1P[x][v] <==> (old(S1P)[x][v] && (forall xx:Element, vv:VecClk :: S[xx][vv] ==> !less(v, vv) ) ) ||
                                                     (S[x][v] && (forall xx:Element, vv:VecClk :: old(S1P)[xx][vv] ==> !less(v, vv) ) )
);

//Merge method description for sigma2P
procedure merge2P(S:[Element][VecClk]bool);
modifies S2P;
ensures (forall x:Element, v:VecClk :: S2P[x][v] <==> (old(S2P)[x][v] && (forall xx:Element, vv:VecClk :: S[xx][vv] ==> !less(v, vv) ) ) ||
                                                     (S[x][v] && (forall xx:Element, vv:VecClk :: old(S2P)[xx][vv] ==> !less(v, vv) ) )
);


//State-based write(a, r) method description for sigma1 
//It is split into genWrite(a, r):Va and effWrite(a, Va)
//genWrite(a,r) generates the vector clock 
procedure genWrite(a:Element, r:Replica) returns (Va:VecClk);
ensures (forall x:Element, v:VecClk, rr:Replica :: S1[x][v] && rr != r ==> v[rr] <= Va[rr] );
ensures (forall x:Element, v:VecClk :: S1[x][v] ==> v[r] < Va[r] );

//eff(a, Va) adds this pair to S1 and removes all the other elements from S1
procedure effWrite(a:Element, Va:VecClk);
modifies S1;
ensures (forall x:Element, v:VecClk :: !(x == a && v == Va) ==> !S1[x][v] );
ensures S1[a][Va];

//Property 1

//We aim to show that apply(apply(sigma, (a, Va) ), (b, Vb)) == apply(apply(sigma, (b, Vb) ), (a, Va))
//when two methods are concurrent (Va and Vb are incomparable)
//i.e., effectors commute.
//We assume that initially sigma1 == sigma2
//We apply (a, Va) and (b, Vb) to sigma1 (in that order) and obtain a new sigma1
//We apply (b, Vb) and (a, Va) to sigma2 (in that order) and obtain a new sigma2
//We show that sigma1 == sigma2 afterwards
procedure property1(a:Element, Va:VecClk, b:Element, Vb:VecClk)
requires (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
requires !less(Va, Vb) && !less(Vb, Va);                        //Since these effectors are concurrent their clocks must be incomparable
modifies S1, S2;
ensures (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
{
    //apply(apply(sigma1, (a, Va) ), (b, Vb)) 
    call apply1(a, Va);
    call apply1(b, Vb);

    //apply(apply(sigma2, (b, Vb) ), (a, Va))
    call apply2(b, Vb);
    call apply2(a, Va);
}

//Property 2

//We aim to show merge(sigma, apply(sigma', (a, Va) ) ) == apply(merge(sigma, sigma'), (a, Va) )
//when P1(Sigma1, a, Va) and P1(Sigma1', a, Va) holds
//We assume that initially sigma1 == sigma2 and sigma1' == sigma2'
//We apply merge(sigma1, apply(sigma1',(a, Va) )) and obtaina a new sigma1
//We apply apply(merge(sigma2, sigma2'), (a,  Va)) and obtain a new sigma2
//We show sigma1 == sigma2 at the end.
procedure property2(a:Element, Va:VecClk)
requires (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
requires (forall x:Element, v:VecClk :: S1P[x][v] == S2P[x][v]);
requires P1(S1, a, Va) && P1(S2, a, Va) && P1(S1P, a, Va) && P1(S2P, a, Va);
modifies S1, S2, S1P, S2P;
ensures (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
{
    //merge(sigma1, apply(sigma1',(a, Va))
    call apply1P(a, Va);
    call merge1(S1P);

    //apply(merge(sigma2, sigma2'), (a, Va))
    call merge2(S2P);
    call apply2(a, Va);
}

//Property 3

//We aim to show merge(apply(sigma, (a, Va) ), apply(sigma', (a, Va) ) ) == apply(merge(sigma,sigma'), (a, Va) )
//when P1(sigma1, eff, a, ta) and P1(sigma1', eff, a, ta) holds
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(apply(sigma1, (a, Va)), apply(sigma1', (a, Va))) and obtain a new sigma1
//We apply apply(merge(sigma2,sigma2'), (a, Va)) and obtain a new sigma2
//We show that sigma1 == sigma2 at the end
procedure property3(a:Element, Va:VecClk)
requires (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
requires (forall x:Element, v:VecClk :: S1P[x][v] == S2P[x][v]);
requires P1(S1, a, Va) && P1(S2, a, Va) && P1(S1P, a, Va) && P1(S2P, a, Va);
modifies S1, S2, S1P, S2P;
ensures (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
{
    //merge(apply(sigma1, (a, Va)), apply(sigma1', (a, Va)))
    call apply1(a, Va);
    call apply1P(a, Va);
    call merge1(S1P);

    //apply(merge(sigma2,sigma2'), (a, Va))
    call merge2(S2P);
    call apply2(a, Va);
}

//First, we show merge(sigma, sigma) == sigma for the initial state
procedure property4a()
requires (forall x:Element, v:VecClk :: !S1[x][v]);               
modifies S1;
ensures (forall x:Element, v:VecClk :: S1[x][v] == old(S1)[x][v]);
{
    call merge1(S1);
}

//Next, we aim to show merge(sigma, sigma') == merge(sigma', sigma)
//We assume that sigma1 == sigma2 && sigma1' == sigma2'
//We apply merge(sigma1, sigma1') and obtain a new sigma1
//We apply merge(sigma2', sigma2) and obtain a new sigma2'
//We show that sigma1 == sigma2'
procedure property4b()
requires (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
requires (forall x:Element, v:VecClk :: S1P[x][v] == S2P[x][v]);
modifies S1, S2P;
ensures (forall x:Element, v:VecClk :: S1[x][v] == S2P[x][v]);
{
    //merge(sigma1, sigma1')
    call merge1(S1P);

    //merge(sigma2', sigma2)
    call merge2P(S2);
}

//We aim to show that the state after applying genWrite(a, r):Va;effWrite(a, Va) to sigma is the same as apply(sigma, (a, Va))
//We assume that initially sigma1 == sigma2 
//We apply genWrite(a, r1);effadd(a,Va) to sigma1 and obtain a new sigma1
//We apply apply(sigma2, (a, Va)) and obtain a new sigma2
//We show that sigma1 == sigma2 after applying the operations
procedure property5Write(a:Element, r1:Replica)
requires (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
modifies S1, S2;
ensures (forall x:Element, v:VecClk :: S1[x][v] == S2[x][v]);
{
    var Va:VecClk;

    //write(a, r1) == genWrite(a, r1):Va; effWrite(a, Va);
    call Va := genWrite(a, r1);
    call effWrite(a, Va);

    //apply(sigma2, (a, Va) )
    call apply2(a, Va);
}

//Proof of P1 
//Goal: Let sigma1=S1 be obtained by applying a set S of local effectors to
//the initial state (i.e., S is an empty set) and (a, Va) be a local effector next to be applied. 
//We claim that: !(V > Va) for all (x, V) in S1
//Proof is based on induction on the size of S.

//Base case: |S| == 0. So, S1 is an set.
procedure proofP1Base(a:Element, Va:VecClk)
requires (forall x:Element, v:VecClk :: !S1[x][v]);      
ensures P1(S1, a, Va);
{
}

//Inductive case: Assume P1(sigma1, a, Va) holds.
//If we apply (b, Vb) to sigma1 s.t. !(Va < Vb),
//then P1(sigma1, a, Va) holds after applying (b, Vb) as well.
procedure proofP1Induction(a:Element, Va:VecClk)
requires P1(S1, a, Va);
modifies S1;
ensures P1(S1, a, Va);
{
    var b:Element, Vb:VecClk;

    assume !less(Va, Vb);
    call apply1(b, Vb);
}