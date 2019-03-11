type Element;
type Timestamp = int;                           //Timestamps are assumed to be integers for the sake of total order among them

const root:Element;                             //Root of the TI-tree. We assume that it is included in the spec as the initial element as well to simplify proofs

//We use two implementation states (sigma1 and sigma2) for the commutatitivity proofs
//Each sigmai is a pair of the form (treei, tombi)
var tree1:[Element][Timestamp][Element]bool;
var tomb1:[Element]bool;
var tree2:[Element][Timestamp][Element]bool;
var tomb2:[Element]bool;

//addAfter method description for sigma1
procedure addAfter1(a:Element, ts:Timestamp, b:Element);
modifies tree1;
ensures tree1[a][ts][b];
ensures (forall aa:Element, tt:Timestamp, bb:Element :: aa != a || tt != ts || bb != b ==> tree1[aa][tt][bb] == old(tree1)[aa][tt][bb]);

//addAfter method description for sigma2
procedure addAfter2(a:Element, ts:Timestamp, b:Element);
modifies tree2;
ensures tree2[a][ts][b];
ensures (forall aa:Element, tt:Timestamp, bb:Element :: aa != a || tt != ts || bb != b ==> tree2[aa][tt][bb] == old(tree2)[aa][tt][bb]);

//remove method description for sigma1
procedure remove1(a:Element);
modifies tomb1;
ensures tomb1[a];
ensures (forall aa:Element :: aa != a ==> tomb1[aa] == old(tomb1)[aa]);

//addAfter method description for sigma1
procedure remove2(a:Element);
modifies tomb2;
ensures tomb2[a];
ensures (forall aa:Element :: aa != a ==> tomb2[aa] == old(tomb2)[aa]);

//Commutativity check between two addAfter methods.
//We assume that sigma1 == sigma2 initially.
//We apply addAfter(a1, ts1, b1) and addAfter(a2, ts2, b2) (in that order) to sigma1 and obtain the new sigma1
//We apply addAfter(a2, ts2, b2) and addAfter(a1, ts1, b1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comAddAdd(a1:Element, ts1:Timestamp, b1:Element, a2:Element, ts2:Timestamp, b2:Element)
requires (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
requires (forall a:Element :: tomb1[a] == tomb2[a] );
modifies tree1, tree2;
ensures (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
ensures (forall a:Element :: tomb1[a] == tomb2[a] );
{
    //addAfter(a1, ts1, b1); adfAfter(a2, ts2, b2);
    call addAfter1(a1, ts1, b1);
    call addAfter1(a2, ts2, b2);

    //addAfter(a2, ts2, b2); adfAfter(a1, ts1, b1);
    call addAfter2(a2, ts2, b2);
    call addAfter2(a1, ts1, b1);
}

//Commutativity check between an addAfter and a remove method.
//We assume that sigma1 == sigma2 initially.
//We apply addAfter(a1, ts1, b1) and remove(a2) (in that order) to sigma1 and obtain the new sigma1
//We apply remove(a2) and addAfter(a1, ts1, b1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comAddRemove(a1:Element, ts1:Timestamp, b1:Element, a2:Element)
requires (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
requires (forall a:Element :: tomb1[a] == tomb2[a] );
modifies tree1, tree2, tomb1, tomb2;
ensures (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
ensures (forall a:Element :: tomb1[a] == tomb2[a] );
{
    //addAfter(a1, ts1, b1); remove(a2);
    call addAfter1(a1, ts1, b1);
    call remove1(a2);

    //remove(a2); adfAfter(a1, ts1, b1);
    call remove2(a2);
    call addAfter2(a1, ts1, b1);
}

//Commutativity check between a remove and an addAfter method.
//We assume that sigma1 == sigma2 initially.
//We apply remove(a1) and addAfter(a2, ts2, b2) (in that order) to sigma1 and obtain the new sigma1
//We apply addAfter(a2, ts2, b2) and remove(a1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comRemoveAdd(a1:Element, a2:Element, ts2:Timestamp, b2:Element)
requires (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
requires (forall a:Element :: tomb1[a] == tomb2[a] );
modifies tree1, tree2, tomb1, tomb2;
ensures (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
ensures (forall a:Element :: tomb1[a] == tomb2[a] );
{
    //remove(a1); adfAfter(a2, ts2, b2);
    call remove1(a1);
    call addAfter1(a2, ts2, b2);

    //addAfter(a2, ts2, b2); remove(a1);
    call addAfter2(a2, ts2, b2);
    call remove2(a1);
}

//Commutativity check between two remove methods.
//We assume that sigma1 == sigma2 initially.
//We apply remove(a1) and remove(a2) (in that order) to sigma1 and obtain the new sigma1
//We apply remove(a2) and remove(a1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comRemoveRemove(a1:Element, a2:Element)
requires (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
requires (forall a:Element :: tomb1[a] == tomb2[a] );
modifies tomb1, tomb2;
ensures (forall a:Element, ts:Timestamp, b:Element :: tree1[a][ts][b] == tree2[a][ts][b] );
ensures (forall a:Element :: tomb1[a] == tomb2[a] );
{
    //remove(a1); remove(a2);
    call remove1(a1);
    call remove1(a2);

    //remove(a2); remove(a1);
    call remove2(a2);
    call remove2(a1);
}