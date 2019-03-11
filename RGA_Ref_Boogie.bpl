type Element;
type Timestamp = int;   //Timestamps are assumed to be integers for the sake of total order among them

const root:Element;     //root of the TI-tree. We assume that it is included in the spec as the initial element as well to simplify proofs


var tree:[Element][Timestamp][Element]bool;     //TI-tree of the implementation (Set of triples)
var tomb:[Element]bool;                         //Tombstone set of the implementation
var list:[Element][Element]bool;                //List of the specification (Set of pairs)
var tombS:[Element]bool;                        //Tombstone of the specification

//Implementation invariants (all about the TI-tree)

//An auxiliary function that shows whether two Elements are reachable in a TI-tree
function reachable(a:Element, b:Element, next:[Element][Timestamp][Element]bool) returns (ret:bool);
axiom (forall a:Element, b:Element, next:[Element][Timestamp][Element]bool :: reachable(a, b, next) <==> 
            (exists t:Timestamp :: next[a][t][b]) || (exists t:Timestamp, c:Element :: reachable(a,c,next) && next[c][t][b]));

//Trees are acyclic
function acyclic( next:[Element][Timestamp][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Timestamp][Element]bool :: acyclic(next) <==>
                (forall a:Element, b:Element :: reachable(a,b,next) ==> !reachable(b,a,next)) );

//We assume that each element can be inserted to the tree at most once
//This  also prevents our graph to be a DAG
//In addition, no edge can end up at root
function uniqueElements(next:[Element][Timestamp][Element]bool) returns (ret:bool); 
axiom (forall next:[Element][Timestamp][Element]bool :: uniqueElements(next) <==> 
                (forall a:Element, t:Timestamp, b:Element :: next[a][t][b] ==> (forall aa:Element, tt:Timestamp :: aa != a || tt != t ==> !next[aa][tt][b])  ) &&
                (forall a:Element, t:Timestamp :: ! next[a][t][root]) );


//An auxiliary function to check whether an element is a member of the tree
function isTreeElement(a:Element, next:[Element][Timestamp][Element]bool) returns (ret:bool);
axiom (forall a:Element, next:[Element][Timestamp][Element]bool :: isTreeElement(a, next) <==> a == root || (exists b:Element, t:Timestamp :: next[b][t][a]));

//Every element of the tree must be reachable from root.
//This also implies that they every pair has a common least element
function rootReachable(next:[Element][Timestamp][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Timestamp][Element]bool :: rootReachable(next) <==> (forall a:Element :: a != root && isTreeElement(a,next) ==> reachable(root,a,next)));

//Each timestamp can be used at most once
function uniqueTimestamps(next:[Element][Timestamp][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Timestamp][Element]bool :: uniqueTimestamps(next) <==> 
                (forall a1:Element, b1:Element, t1:Timestamp, a2:Element, b2:Element, t2:Timestamp :: next[a1][t1][b1] && next[a2][t2][b2] && (a1 != a2 || b1 != b2) ==> t1 != t2  ) );


//Invariant of the implementation consists of four properties
function impInv(next:[Element][Timestamp][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Timestamp][Element]bool :: impInv(next) <==> 
                acyclic(next) && uniqueElements(next) && rootReachable(next) && uniqueTimestamps(next));


//Specification (Linear List) Properties

//An auxiliary function for checking reachability in a list. Redefinition for lists (since they are set of pairs, not triples)
function reachableList(a:Element, b:Element, next:[Element][Element]bool) returns (ret:bool);
axiom (forall a:Element, b:Element, next:[Element][Element]bool ::reachableList(a,b,next) <==> next[a][b] || (exists c:Element :: reachableList(a,c,next) && next[c][b]) );

//Lists are acyclic as well. Redefinition for lists
function acyclicList(next:[Element][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Element]bool :: acyclicList(next) <==> (forall a:Element, b:Element :: reachableList(a,b,next) ==> !reachableList(b,a,next) ) );

//Each element can have at most one outgoing edge and one incoming edge in a list.
//Root is at the beginning of the list. No edge can end up at the root.
function uniqueListElements(next:[Element][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Element]bool :: uniqueListElements(next) <==>
                (forall a:Element, b:Element :: next[a][b] ==> (forall c:Element :: (c != a ==> !next[c][b]) && (c != b ==> !next[a][c]) ) ) &&
                (forall a:Element :: !next[a][root]) );

//An auxiliary function for checking membership in a list. Redefinition for lists.
function isListElement(a:Element, next:[Element][Element]bool) returns (ret:bool);
axiom (forall a:Element, next:[Element][Element]bool :: isListElement(a,next) <==> (exists b:Element :: next[b][a]) || a == root);

//Lists are totally ordered. Every pair of elements are comparable (i.e., one is reachable from the other)
//root is ordered before all the other elements (it can reach every member of the list)
function totalOrder(next:[Element][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Element]bool :: totalOrder(next) <==> 
                (forall a:Element, b:Element :: isListElement(a, next) && isListElement(b,next) && a != b ==> reachableList(a,b,next) || reachableList(b,a,next)) &&
                (forall a:Element :: isListElement(a, next) && a != root ==> reachableList(root,a,next)) );

//Invariant for the specification consists of the properties defined above.
function specInv(next:[Element][Element]bool) returns (ret:bool);
axiom (forall next:[Element][Element]bool :: specInv(next) <==> 
                acyclicList(next) && uniqueListElements(next) && totalOrder(next) );

//Functions describing the refinement relation

//Both the TI-tree of the implementation and the list of the specification must contain the same set of elements (they have the same elements)
//Tombstones of the implementation and the specification are the same as well.
function sameElements(nextImp:[Element][Timestamp][Element]bool, tombImp:[Element]bool, nextSpec:[Element][Element]bool, tombSpec:[Element]bool) returns (ret:bool);
axiom (forall  nextImp:[Element][Timestamp][Element]bool, tombImp:[Element]bool, nextSpec:[Element][Element]bool, tombSpec:[Element]bool :: sameElements(nextImp,tombImp,nextSpec,tombSpec) <==>
                (forall a:Element :: (tombImp[a] <==> tombSpec[a])) && (forall a:Element :: isTreeElement(a,nextImp) <==> isListElement(a,nextSpec))) ;

//Corresponding list of the TI- tree is described with respect to order (reachability) relation:
//- x comes before y in the linearization iff either y is reachable from x, or 
//      there exists a common ancestor z of x and y in the TI-tree such that 
//      timestamp of the  first node after z on the path to x is bigger than the timestamp of the first node after z on the path to y.
//Above definition is equivalent to the pre-order traversal of members of the tree.
function correctLinearization(nextImp:[Element][Timestamp][Element]bool, nextSpec:[Element][Element]bool) returns (ret:bool);
axiom (forall nextImp:[Element][Timestamp][Element]bool, nextSpec:[Element][Element]bool :: correctLinearization(nextImp, nextSpec) <==> 
                    (forall x:Element, y:Element :: reachableList(x,y,nextSpec) <==> reachable(x,y,nextImp) || 
                                                                                    (exists z:Element, t:Element, u:Element, tt:Timestamp, tu:Timestamp ::   
                                                                                     nextImp[z][tt][t] && nextImp[z][tu][u] && (reachable(t,x,nextImp) || t ==x) && (reachable(u,y,nextImp) || u == y) && tt>tu    )   ) );

//Refinement relation consists of the two properties defined above.
function refinementMapping(nextImp:[Element][Timestamp][Element]bool, tombImp:[Element]bool, nextSpec:[Element][Element]bool, tombSpec:[Element]bool) returns (ret:bool);
axiom (forall  nextImp:[Element][Timestamp][Element]bool, tombImp:[Element]bool, nextSpec:[Element][Element]bool, tombSpec:[Element]bool :: refinementMapping(nextImp,tombImp,nextSpec,tombSpec) <==> 
                sameElements(nextImp,tombImp,nextSpec,tombSpec) && correctLinearization(nextImp, nextSpec));


//Desciptions of the methods of the implementation and the specification

//addafter(a,ts,b) of the Implementation
procedure addAfterImp(a:Element, ts:Timestamp, b:Element);
requires isTreeElement(a, tree) && !isTreeElement(b, tree) && (forall aa:Element, t:Timestamp, bb:Element :: tree[aa][t][bb] ==> t < ts);
modifies tree;
ensures tree[a][ts][b];
ensures (forall aa:Element, tt:Timestamp, bb:Element :: aa != a || tt != ts || bb != b ==> tree[aa][tt][bb] == old(tree)[aa][tt][bb]);

//addafter(a,b) of the Specification
procedure addAfterSpec(a:Element, b:Element);
requires isListElement(a, list) && !isListElement(b, list);
modifies list;
ensures list[a][b];
ensures (forall c:Element :: old(list)[a][c] ==> list[b][c] && !list[a][c]);
ensures (forall x:Element, y:Element :: !((x == a && old(list)[x][y]) || (x == a && y == b) || (x == b && old(list)[a][y])) ==> old(list)[x][y] == list[x][y] );

//remove(a) of the Implementation
procedure removeImp(a:Element);
modifies tomb;
ensures tomb[a];
ensures (forall aa:Element :: aa != a ==> tomb[aa] == old(tomb)[aa]);

//remove(a) of the Specification
procedure removeSpec(a:Element);
modifies tombS;
ensures tombS[a];
ensures (forall aa:Element :: aa != a ==> tombS[aa] == old(tombS)[aa]);

//read()  of the Implementation 
//descibes the returned list in terms of the order (reachability) of its members to be compatible with linearization
procedure readImp() returns (l:[Element][Element]bool);
ensures (forall x:Element, y:Element :: reachableList(x,y,l) <==> !tomb[x] && !tomb[y] && 
                                                (reachable(x,y,tree) || 
                                                    (exists z:Element, t:Element, u:Element, tt:Timestamp, tu:Timestamp ::
                                                        tree[z][tt][t] && tree[z][tu][u] && (reachable(t,x,tree)|| t==x) && (reachable(u,y,tree) || u == y) && tt > tu ) ) );

//read()  of the Specification 
//descibes the returned list in terms of the order (reachability) of its members to be compatible with the implementation
//descibes the returned list in terms of the order (reachability) of its members
procedure readSpec() returns (l:[Element][Element]bool);
ensures (forall x:Element, y:Element :: reachableList(x,y,l) <==> !tombS[x] && !tombS[y] && reachableList(x,y,list)  );

//LEMMATA
//Below are lemmas that are used for the refinement proofs later and that have inductive proofs (based on the inductive definition of reachability).
//Proving induction directly is not possible. Hence, we do proofs using pre-, post-conditions and recursion
//Each lemma is represented as a postcondition of a method.
//Immediately next method models and proves lemma using recursive calls.

//t2 is a tree obtained from t1 by applying addafter(a,t,b).
//Lemma states that every pair satisfying the reachability condition in t1 also satisfies this condition in t2.
procedure preserveReachability(a:Element, t:Timestamp, b:Element, t1:[Element][Timestamp][Element]bool, t2:[Element][Timestamp][Element]bool);
requires (forall aa:Element, bb:Element, tt:Timestamp :: aa != a || bb != b || t != tt ==> t1[aa][tt][bb] == t2[aa][tt][bb]);
requires !t1[a][t][b] && t2[a][t][b];
ensures (forall aa:Element, bb:Element :: reachable(aa,bb,t1) ==> reachable(aa,bb,t2) );

//aa and bb above are unrestrained inputs to this method. We assume reachable(aa,bb,t1) and show reachable(aa,bb,t2)
procedure preserveReachabilityRec(aaa:Element, bbb:Element, a:Element, t:Timestamp, b:Element, t1:[Element][Timestamp][Element]bool, t2:[Element][Timestamp][Element]bool)
requires (forall aa:Element, bb:Element, tt:Timestamp :: aa != a || bb != b || t != tt ==> t1[aa][tt][bb] == t2[aa][tt][bb]);
requires !t1[a][t][b] && t2[a][t][b];
requires reachable(aaa,bbb,t1);
ensures reachable(aaa,bbb,t2);
{
    var c:Element, tt:Timestamp;

    if(*)
    {
        assume t1[aaa][tt][bbb];
        assert reachable(aaa,bbb,t2);
    }
    else
    {
        assume reachable(aaa,c,t1) && t1[c][tt][bbb];
        call preserveReachabilityRec(aaa,c,a,t,b,t1,t2);
        assert reachable(aaa,bbb,t2);
    }
}

//t2 is a tree obtained from t1 by applying addafter(a,t,b).
//Lemma states that if bb is reachable from aa in t2, then it is also reachable in t1 or bb is b.
procedure preserveReachability2(a:Element, t:Timestamp, b:Element, t1:[Element][Timestamp][Element]bool, t2:[Element][Timestamp][Element]bool);
requires (forall aa:Element, tt:Timestamp :: !t2[b][tt][aa] );
requires (forall aa:Element, bb:Element, tt:Timestamp :: aa != a || bb != b || t != tt ==> t1[aa][tt][bb] == t2[aa][tt][bb]);
requires !t1[a][t][b] && t2[a][t][b];
ensures (forall aa:Element, bb:Element :: reachable(aa,bb,t2) ==> reachable(aa,bb,t1) || bb == b );

//aa and bb above are unrestrained inputs to this method. We assume reachable(aa,bb,t2) and show  either reachable(aa,bb,t1) or bb == b
procedure preserveReachability2Rec(aaa:Element, bbb:Element, a:Element, t:Timestamp, b:Element, t1:[Element][Timestamp][Element]bool, t2:[Element][Timestamp][Element]bool)
requires (forall aa:Element, tt:Timestamp :: !t2[b][tt][aa] );
requires (forall aa:Element, bb:Element, tt:Timestamp :: aa != a || bb != b || t != tt ==> t1[aa][tt][bb] == t2[aa][tt][bb]);
requires !t1[a][t][b] && t2[a][t][b];
requires reachable(aaa,bbb,t2);
ensures reachable(aaa,bbb,t1) || bbb == b;
{
    var c:Element, tt:Timestamp;

    if(*)
    {
        assume t2[aaa][tt][bbb];
        assert reachable(aaa,bbb,t1) || bbb == b;
    }
    else
    {
        assume reachable(aaa,c,t2) && t2[c][tt][bbb];
        call preserveReachability2Rec(aaa,c,a,t,b,t1,t2);
        assert reachable(aaa,bbb,t1) || bbb == b;
    }
}

//t1 is a tree satisfying impInv (we use this lemma on the TI-tree before the modification).
//This lemma states that  if b is reachable from a and a is not the root, then a is reachable from the root as well
//This lemma is necessary (rootReachable does not directly imply) because isTreeMember is defined such that only elements that have an incoming edge are members.
procedure treeLemma1(t1:[Element][Timestamp][Element]bool);
requires impInv(t1);
ensures (forall a:Element, b:Element :: reachable(a,b,t1) && a != root ==> reachable(root,a,t1));

//a and b above are unrestrained inputs to this method. 
// P && Q ==> R is equiavalent to P ==> R || not Q
// So I change the post condition of treeLemma1 as: if b is reachable from a, then a is reachable as well or a is root.
procedure treeLemma1Rec(a:Element, b:Element, t1:[Element][Timestamp][Element]bool)
requires impInv(t1);
requires reachable(a,b,t1);
ensures reachable(root,a,t1) || root == a;
{
    var c:Element, tx:Timestamp;

    if(*)
    {
        assume t1[a][tx][b];      
        assert reachable(root, b, t1); 
        assert reachable(root,a,t1) || root == a;
    }
    else
    {
        assume reachable(a,c,t1) && t1[c][tx][b];
        call treeLemma1Rec(a,c,t1);
        assert reachable(root,a,t1) || root == a;
    }
}

//Same as preserveReachability. This time we do it for lists.
procedure preserveListReachability(a:Element, b:Element, t1:[Element][Element]bool, t2:[Element][Element]bool);
requires isListElement(a, t1) && !isListElement(b, t1);
requires t2[a][b];
requires (forall c:Element :: t1[a][c] ==> t2[b][c] && !t2[a][c]);
requires (forall x:Element, y:Element :: !((x == a && t1[x][y]) || (x == a && y == b) || (x == b && t1[a][y])) ==> t1[x][y] == t2[x][y] );
ensures (forall aa:Element, bb:Element :: reachableList(aa,bb,t1) ==> reachableList(aa,bb,t2));

//Same as preserveReachabilityRec. This time we do it for lists.
procedure preserveListReachabilityRec(aa:Element, bb:Element, a:Element, b:Element, t1:[Element][Element]bool, t2:[Element][Element]bool)
requires isListElement(a, t1) && !isListElement(b, t1);
requires t2[a][b];
requires (forall c:Element :: t1[a][c] ==> t2[b][c] && !t2[a][c]);
requires (forall x:Element, y:Element :: !((x == a && t1[x][y]) || (x == a && y == b) || (x == b && t1[a][y])) ==> t1[x][y] == t2[x][y] );
requires reachableList(aa,bb,t1);
ensures reachableList(aa,bb,t2);
{
    var c:Element;

    if(*)
    {
        assume t1[a][b];
        assert reachableList(aa,bb,t2);
    }
    else
    {
        assume reachableList(aa,c,t1) && t1[c][bb];
        call preserveListReachabilityRec(aa,c,a,b,t1,t2);
        assert reachableList(aa,bb,t2);
    }
}

//Similar to preserveReachability2.
//t2 is a list obtained by applying addAfter(a,b) to t1.
//If bb is reachable from aa in t2, then either same is true for t1, or bb is b and a is reachable from (or the same as) aa, or aa is b and bb is reachable from a.
procedure preserveListReachability2(a:Element, b:Element, t1:[Element][Element]bool, t2:[Element][Element]bool);
requires isListElement(a, t1) && !isListElement(b, t1);
requires t2[a][b];
requires (forall c:Element :: t1[a][c] ==> t2[b][c] && !t2[a][c]);
requires (forall x:Element, y:Element :: !((x == a && t1[x][y]) || (x == a && y == b) || (x == b && t1[a][y])) ==> t1[x][y] == t2[x][y] );
requires specInv(t1);
ensures (forall aa:Element, bb:Element :: reachableList(aa,bb,t2) ==> reachableList(aa,bb,t1) || (reachableList(aa,a,t1) && bb == b) || (reachableList(a,bb,t1) && aa == b) || (aa == a && bb == b));

//Similar to preserveListReachability2Rec
procedure preserveListReachability2Rec(aa: Element, bb:Element, a:Element, b:Element, t1:[Element][Element]bool, t2:[Element][Element]bool)
requires isListElement(a, t1) && !isListElement(b, t1);
requires t2[a][b];
requires (forall c:Element :: t1[a][c] ==> t2[b][c] && !t2[a][c]);
requires (forall x:Element, y:Element :: !((x == a && t1[x][y]) || (x == a && y == b) || (x == b && t1[a][y])) ==> t1[x][y] == t2[x][y] );
//requires (forall x:Element :: !reachableList(b,x,t1));
requires specInv(t1);
requires reachableList(aa,bb,t2);
ensures reachableList(aa,bb,t1) || (reachableList(aa,a,t1) && bb == b) || (reachableList(a,bb,t1) && aa == b) || (aa == a && bb == b);
{
    var c:Element;

    if(*)
    {
        assume t2[aa][bb];
        assert reachableList(aa,bb,t1) || (reachableList(aa,a,t1) && bb == b) || (reachableList(a,bb,t1) && aa == b) || (aa == a && bb == b);
    }
    else
    {
        assume reachableList(aa,c,t2) && t2[c][bb];
        call preserveListReachability2Rec(aa,c,a,b,t1,t2);
        assert c == b ==> reachableList(aa,bb,t1);
        assert reachableList(aa,bb,t1) || (reachableList(aa,a,t1) && bb == b) || (reachableList(a,bb,t1) && aa == b) || (aa == a && bb == b);
    }
}

//Same as treeLemma1
procedure listLemma1(t1:[Element][Element]bool);
requires specInv(t1);
ensures (forall a:Element, b:Element :: reachableList(a,b,t1) && a != root ==> reachableList(root,a,t1));

//Same as treeLemma1Rec
//We prove that if reachableList(a,b,t1), then reachableList(root,a,t1) or a == root;
procedure listLemma1Rec(a:Element, b:Element, t1:[Element][Element]bool)
requires specInv(t1);
requires reachableList(a,b,t1);
ensures reachableList(root,a,t1) || a == root;
{
    var c:Element;

    if(*)
    {
        assume t1[a][b];
        assert reachableList(root,a,t1) || a == root;
    }
    else
    {
        assume reachableList(a,c,t1) && t1[c][b];
        call listLemma1Rec(a,c,t1);
        assert reachableList(root,a,t1) || a == root;

    }
}

//Assuming that b is the immediate next element after a in the list t2 and
//t2 satisfies the total order (every node has at most one incoming and outgoing edges),
//we show that if aa is reachable from a and aa is not b, then aa is reachable from b in t2 too.
//This lemma is needed on the list after addAfter(a,b) method is applied
procedure listLemma2(a:Element, b:Element, t2:[Element][Element]bool);
requires t2[a][b];
requires uniqueListElements(t2);
ensures (forall  aa:Element :: aa != b && reachableList(a,aa,t2) ==> reachableList(b,aa,t2));


//We prove the equivalent version: reachableList(a,aa,t2) ==> reachableList(b,aa,t2) || aa == b;
//aa is an unconstrained input to this method now.
procedure listLemma2Rec(aa:Element, a:Element, b:Element, t2:[Element][Element]bool)
requires t2[a][b];
requires uniqueListElements(t2);
requires reachableList(a,aa,t2);
ensures reachableList(b,aa,t2) || aa == b;
{
    var c:Element;

    if(*)
    {
        assume t2[a][aa];
        assert aa == b;
    }
    else
    {
        assume reachableList(a,c,t2) && t2[c][aa];
        call listLemma2Rec(c,a,b,t2);
        assert reachableList(b,aa,t2) || aa == b;
    }
}

//t1 is a tree satisfying impInv.
//This lemma proves that if y is reachable from x, either it is immmediately after x or there exists a z immediately after x that can reach to y.
//It proves that defining the reachability in other way is implied by this definition.
procedure refLemma1(t1:[Element][Timestamp][Element]bool);
requires impInv(t1);
ensures (forall x:Element, y:Element :: reachable(x,y,t1) ==> (exists z:Element, tz:Timestamp :: t1[x][tz][z] && (z == y || reachable(z,y,t1)) )  );

//x and y above are unconstrained inputs to this program. We show either y is immediately after x or there exists an immediate successor z of x that can reach to y.
procedure refLemma1Rec(x:Element, y:Element, t1:[Element][Timestamp][Element]bool)
requires impInv(t1);
requires reachable(x,y,t1);
ensures  (exists z:Element, tz:Timestamp :: t1[x][tz][z] && (z == y || reachable(z,y,t1)) );
{
    var a:Element, tt:Timestamp;

    if(*)
    {
        assume t1[x][tt][y];
        assert  (exists z:Element, tz:Timestamp :: t1[x][tz][z] && (z == y || reachable(z,y,t1)) );
    }
    else
    {
        assume reachable(x,a,t1) && t1[a][tt][y];
        call refLemma1Rec(x,a,t1);
        assert  (exists z:Element, tz:Timestamp :: t1[x][tz][z] && (z == y || reachable(z,y,t1)) );
    }
}

//REFINEMENT PROOFS

//This method shows that refinement relation is preserved after applying addAfter method.
//We assume invariants of the implementation, specification and the refinement relation holds at the entry.
//We show that invariants of the implemantation, specification and the refinement relation holds after both the implementation and the specification apply
//addAfter(a,t,b) and addAfter(a,b) methods, respectively.
procedure refAddAfter(a:Element, t:Timestamp, b:Element)
requires impInv(tree) && specInv(list) && refinementMapping(tree, tomb, list, tombS);
requires isTreeElement(a, tree) && !isTreeElement(b, tree) && (forall aa:Element, ts:Timestamp, bb:Element :: tree[aa][ts][bb] ==> ts < t);
requires (forall x:Element, tx:Timestamp :: !tree[b][tx][x]  ); 
modifies tree, list;
ensures impInv(tree);
ensures specInv(list);
ensures refinementMapping(tree,tomb,list,tombS);
{
    var oldTree:[Element][Timestamp][Element]bool;
    var oldList:[Element][Element]bool;

    //We keep old states to reason about them after the operations.
    oldTree := tree;   
    oldList := list;

    //apply addAfter of the implemantation
    call addAfterImp(a,t,b);

    //use the lemmas above to prove invariant of the implementation
    call preserveReachability(a,t,b,oldTree,tree);
    call treeLemma1(oldTree);
    call preserveReachability2(a,t,b,oldTree,tree);
    assert impInv(tree);

    //apply addAfter of the specification
    call addAfterSpec(a,b);
    
    //use the lemmas above to prove invariant of the specification
    call preserveListReachability(a,b,oldList, list);
    call listLemma1(oldList);
    call preserveListReachability2(a,b,oldList,list);   
    call listLemma2(a,b,list); 
    assert specInv(list);

    //some auxiliary assertions that help making the proof of refinement relation faster
    assert (forall x:Element, y:Element :: x != b && y !=b ==> (reachableList(x,y,list) <==> reachable(x,y,tree) ||  
                                                                                    (exists z:Element, tr:Element, u:Element, tt:Timestamp, tu:Timestamp ::   
                                                                                     tree[z][tt][tr] && tree[z][tu][u] && (reachable(tr,x,tree) || tr == x)  && (reachable(u,y,tree) || y == u) && tt>tu    )     )  );

    
    assert (forall x:Element, y:Element :: x != b && y ==b ==> (reachableList(x,y,list) <==> reachable(x,y,tree) ||  
                                                                                    (exists z:Element, tr:Element, u:Element, tt:Timestamp, tu:Timestamp ::   
                                                                                     tree[z][tt][tr] && tree[z][tu][u] &&(reachable(tr,x,tree) || tr == x) && (reachable(u,y,tree) || y == u) && tt>tu    )     )  );
    
    call refLemma1(tree);

    assert (forall x:Element, y:Element :: reachableList(x,y,list) <==> reachable(x,y,tree) ||  
                                                                                    (exists z:Element, tr:Element, u:Element, tt:Timestamp, tu:Timestamp ::   
                                                                                     tree[z][tt][tr] && tree[z][tu][u] && (reachable(tr,x,tree) || tr == x)  && (reachable(u,y,tree) || y == u) && tt>tu )  );
}

//This method shows that refinement relation is preserved after applying remove method.
//We assume invariants of the implementation, specification and the refinement relation holds at the entry.
//We show that invariants of the implemantation, specification and the refinement relation holds after both the 
//implementation and the specification apply remove(a) method.
procedure refRemove(a:Element)
requires impInv(tree) && specInv(list) && refinementMapping(tree, tomb, list, tombS);
modifies tomb, tombS;
ensures impInv(tree) && specInv(list) && refinementMapping(tree, tomb, list, tombS);
{
    call removeImp(a);
    call removeSpec(a);
}

//This method shows that refinement relation is preserved after applying read() method and both methods return the same list.
//We assume invariants of the implementation, specification and the refinement relation holds at the entry.
//We show that invariants of the implemantation, specification and the refinement relation holds after both the 
//implementation and the specification apply read() method.
//We show that order of the elements are the same for both lists returned by the read() methods to infer that they are the same.
procedure refRead()
requires impInv(tree) && specInv(list) && refinementMapping(tree, tomb, list, tombS);
ensures impInv(tree) && specInv(list) && refinementMapping(tree, tomb, list, tombS);
{
    var l1:[Element][Element]bool, l2:[Element][Element]bool;

    call l1 := readImp();
    call l2 := readSpec();

    assert (forall x:Element, y:Element :: reachableList(x,y,l1) <==> reachableList(x,y,l2)  );
}