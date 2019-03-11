type Element;

//We use two implementation states (sigma1 and sigma2) for the commutatitivity proofs
//Each sigmai is a set of pairs (element, id)
var elements:[Element][int]bool;
var otherElements:[Element][int]bool;

//Commutativity check between two add methods.
//We assume that sigma1 == sigma2 initially.
//We apply addAfter(a1, k1) and addAfter(a2, k2) (in that order) to sigma1 and obtain the new sigma1
//We apply addAfter(a2, k2) and addAfter(a1, k1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comAddAdd(a1:Element, a2:Element, k1:int, k2:int)
requires (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
modifies elements, otherElements;
ensures (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
{
    //add1;add2
    //eff add1
    elements[a1][k1] := true;
    //eff add2
    elements[a2][k2] := true;

    //add2;add1
    //eff add2
    otherElements[a2][k2] := true;
    //eff add1 
    otherElements[a1][k1] := true;
}

//Commutativity check between an add and a remove method.
//We assume that sigma1 == sigma2 initially.
//We apply addAfter(a1, k1) and remove(R2) (in that order) to sigma1 and obtain the new sigma1
//We apply remove(R2) and addAfter(a1, k1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
//R2 is represented as R2 size (size of the set) and sequences of elements and IDs
procedure comAddRemove(a1:Element, k1:int, R2Size:int, R2Elt:[int]Element, R2ID:[int]int)
requires (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
requires R2Size >= 0;
requires (forall i:int :: i>=0 && i<R2Size ==> !(R2Elt[i] == a1 && R2ID[i] == k1));     //Required precondition: (a1,k1) not in R2
modifies elements, otherElements;
ensures (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
{
    var i:int; 

    //add1;rem2
    //eff add1
    elements[a1][k1] := true;

    //eff rem2
    i := 0;
    while(i < R2Size)
    invariant i <= R2Size;
    invariant (forall k:int :: k>=0 && k < i ==> !elements[R2Elt[k]][R2ID[k]] );
    invariant elements[a1][k1];
    invariant (forall a:Element, k:int :: !(a == a1 && k == k1) && (forall j:int :: j>=0 && j <i ==> R2Elt[j] != a || R2ID[j] != k ) ==> elements[a][k] == otherElements[a][k] ); //Other elements are still the same
    {
        elements[R2Elt[i] ][R2ID[i]] := false;
        i := i+1;
    }

    //rem2;add1
    //eff rem2    
    i := 0;
    while(i < R2Size)
    invariant (forall a:Element, k:int :: !(a == a1 && k == k1) && (forall j:int :: j>=i && j <R2Size ==> R2Elt[j] != a || R2ID[j] != k ) ==> elements[a][k] == otherElements[a][k] ); //Only remaining elements are different
    {
        otherElements[R2Elt[i] ][R2ID[i]] := false;
        i := i+1;
    }

    //eff add1
    otherElements[a1][k1] := true;

}

//Commutativity check between a remove and an add method.
//We assume that sigma1 == sigma2 initially.
//We apply remove(R1) and add(a2, k2) (in that order) to sigma1 and obtain the new sigma1
//We apply add(a2, k2) and remove(R1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
//R1 is represented as R1 size (size of the set) and sequences of elements and IDs
procedure comRemoveAdd(R1Size:int, R1Elt:[int]Element, R1ID:[int]int, a2:Element, k2:int)
requires (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
requires (forall i:int :: i>=0 && i<R1Size ==> !(R1Elt[i] == a2 && R1ID[i] == k2));     //Required precondition: (a2,k2) not in R1
requires R1Size >= 0;
modifies elements, otherElements;
ensures (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
{
    var i:int;

    //rem1;add2
    //eff rem1
    i := 0;
    while(i < R1Size)
    invariant i <= R1Size;
    invariant (forall k:int :: k>=0 && k < i ==> !elements[R1Elt[k]][R1ID[k]] );
    invariant (forall a:Element, k:int :: (forall j:int :: j>=0 && j <i ==> R1Elt[j] != a || R1ID[j] != k ) ==> elements[a][k] == otherElements[a][k]);
    {
        elements[R1Elt[i]][R1ID[i]] := false;
        i := i+1;
    }

    //eff add2
    elements[a2][k2] := true;

    //add2; rem1
    //add2;
    otherElements[a2][k2] := true;

    //rem1
    i := 0;
    while(i < R1Size)
    invariant (forall a:Element, k:int :: (forall j:int :: j>=i && j <R1Size ==> R1Elt[j] != a || R1ID[j] != k ) ==> elements[a][k] == otherElements[a][k] );
    {
        otherElements[R1Elt[i]][R1ID[i]] := false;
        i := i+1;
    }

}

//Commutativity check between two remove methods.
//We assume that sigma1 == sigma2 initially.
//We apply remove(R1) and remove(R2) (in that order) to sigma1 and obtain the new sigma1
//We apply remove(R2) and remove(R1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
//R1 is represented as R1 size (size of the set) and sequences of elements and IDs
//R2 is represented as R2 size (size of the set) and sequences of elements and IDs
procedure comRemoveRemove(R1Size:int, R1Elt:[int]Element, R1ID:[int]int, R2Size:int, R2Elt:[int]Element, R2ID:[int]int)
requires R1Size >= 0 && R2Size >= 0;
requires (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
modifies elements, otherElements;
ensures (forall a:Element, k:int :: elements[a][k] == otherElements[a][k]);
{
    var i:int;

    //rem1;rem2
    //eff rem1
    i := 0;
    while(i < R1Size)
    invariant i <= R1Size;
    invariant (forall k:int :: k>=0 && k < i ==> !elements[R1Elt[k]][R1ID[k]] );
    invariant (forall a:Element, k:int :: (forall j:int :: j>=0 && j<i ==> a != R1Elt[j] || k != R1ID[j]) ==> elements[a][k] == otherElements[a][k]);
    {
        elements[R1Elt[i]][R1ID[i]] := false;
        i := i+1;
    }

    //eff rem2
    i := 0;
    while(i < R2Size)
    invariant i <= R2Size;
    invariant (forall k:int :: k>=0 && k < R1Size ==> !elements[R1Elt[k]][R1ID[k]] );
    invariant (forall k:int :: k>=0 && k < i ==> !elements[R2Elt[k]][R2ID[k]] );
    invariant (forall a:Element, k:int :: (forall j:int :: j>=0 && j<R1Size ==> a != R1Elt[j] || k != R1ID[j]) && (forall j:int :: j>=0 && j < i ==> a != R2Elt[j] || k != R2ID[j])==> elements[a][k] == otherElements[a][k]);
    {
        elements[R2Elt[i]][R2ID[i]] := false;
        i := i+1;
    }

    //rem2;rem1
    //eff rem2
    i := 0;
    while(i < R2Size)
    invariant (forall a:Element, k:int :: (forall j:int :: j>=0 && j<R1Size ==> a != R1Elt[j] || k != R1ID[j]) && (forall j:int :: j>=i && j < R2Size ==> a != R2Elt[j] || k != R2ID[j]) ==> elements[a][k] == otherElements[a][k]);
    {
        otherElements[R2Elt[i]][R2ID[i]] := false;
        i := i+1;
    }

    //eff rem1
    i := 0;
    while(i < R1Size)
    invariant (forall a:Element, k:int :: (forall j:int :: j>=i && j<R1Size ==> a != R1Elt[j] || k != R1ID[j]) ==> elements[a][k] == otherElements[a][k]);
    {
        otherElements[R1Elt[i]][R1ID[i]] := false;
        i := i+1;
    }
}

