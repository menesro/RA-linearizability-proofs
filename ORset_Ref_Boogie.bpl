type Element;

var setImpl:[Element][int]bool;                     //A state variable for the OR Set: Contains (element, id) pairs
var setSpec:[Element][int]bool;                     //A state variable for the specification: Contains (element, id) pairs as well 

//add method description for the implementation
procedure addORset(a:Element, k:int);
requires (forall aa:Element :: !setImpl[aa][k]);
modifies setImpl;
ensures setImpl[a][k];
ensures (forall aa:Element, kk:int :: aa != a || kk != k ==> setImpl[aa][kk] == old(setImpl[aa][kk]));

//add method description for the specification
procedure addSpec(a:Element, k:int);
requires (forall aa:Element :: !setSpec[aa][k]);
modifies setSpec;
ensures setSpec[a][k];
ensures (forall aa:Element, kk:int :: aa != a || kk != k ==> setSpec[aa][kk] == old(setSpec[aa][kk]));

//readIDs method description for the implementation
procedure readIdsImpl(a:Element) returns (R:[Element][int]bool);
ensures (forall aa:Element, kk:int :: a != aa ==> !R[aa][kk]);
ensures (forall k:int :: R[a][k] <==> setImpl[a][k]);

//readIds method description for the specification
procedure readIdsSpec(a:Element) returns (S:[Element][int]bool);
ensures (forall aa:Element, kk:int :: a != aa ==> !S[aa][kk]);
ensures (forall k:int :: S[a][k] <==> setSpec[a][k]);

//remove method description for the implementation
procedure removeImpl(a:Element, R:[Element][int]bool);
modifies setImpl;
ensures (forall aa:Element, kk:int :: R[aa][kk] ==> !setImpl[aa][kk]);
ensures (forall aa:Element, kk:int :: !R[aa][kk] ==> setImpl[aa][kk] == old(setImpl[aa][kk]));

//add method description for the specification
procedure removeSpec(a:Element, S:[Element][int]bool);
modifies setSpec;
ensures (forall aa:Element, kk:int :: S[aa][kk] ==> !setSpec[aa][kk]);
ensures (forall aa:Element, kk:int :: !S[aa][kk] ==> setSpec[aa][kk] == old(setSpec[aa][kk]));

//read method description for the implementation
procedure readImpl() returns (A:[Element]bool);
ensures (forall a:Element :: A[a] <==> (exists k:int :: setImpl[a][k]));

///read method description for the specification
procedure readSpec() returns (A:[Element]bool);
ensures (forall a:Element :: A[a] <==> (exists k:int :: setSpec[a][k]));

//This method shows that refinement relation is preserved for the add method
//Assume (sigma, add(a, k), sigma') is a valid step of the implementation
//We show that (refMap(sigma), add(a,k), refMap(sigma')) is a valid step of the specification as well
//refMap(sigma) == sigma (i.e., it is the identity function)
procedure refAdd(a:Element, k:int)
requires (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
requires (forall aa:Element :: !setImpl[aa][k] && !setSpec[aa][k]);
modifies setImpl, setSpec;
ensures (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
{
    call addORset(a,k);
    call addSpec(a,k);
}

//This method shows that refinement relation is preserved for the readIds method
//Assume (sigma, readIds(a)=>S, sigma') is a valid step of the implementation
//We show that (refMap(sigma), readIds(a)=>S, refMap(sigma')) is a valid step of the specification as well
//refMap(sigma) == sigma (i.e., it is the identity function)
procedure refReadIds(a:Element)
requires (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
ensures (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
{
    var R:[Element][int]bool, S:[Element][int]bool;
    call R := readIdsImpl(a);
    call S := readIdsSpec(a);

    assert (forall aa:Element, kk:int :: R[aa][kk] <==> S[aa][kk]);
}

//This method shows that refinement relation is preserved for the remove method
//Assume (sigma, remove(a, RS), sigma') is a valid step of the implementation
//We show that (refMap(sigma), remove(a,RS), refMap(sigma')) is a valid step of the specification as well
//refMap(sigma) == sigma (i.e., it is the identity function)
procedure refRemove(a:Element, RS:[Element][int]bool)
requires (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
modifies setImpl, setSpec;
ensures (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
{
    call removeImpl(a, RS);
    call removeSpec(a, RS);
}


//This method shows that refinement relation is preserved for the read method
//Assume (sigma, read()=>A, sigma') is a valid step of the implementation
//We show that (refMap(sigma), read()=>A, refMap(sigma')) is a valid step of the specification as well
//refMap(sigma) == sigma (i.e., it is the identity function)
procedure refRead()
requires (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
ensures (forall aa:Element, kk:int :: setImpl[aa][kk] == setSpec[aa][kk]);
{
    var A1:[Element]bool, A2:[Element]bool;

    call A1 := readImpl();
    call A2 := readSpec();

    assert (forall a:Element :: A1[a] == A2[a]);
}