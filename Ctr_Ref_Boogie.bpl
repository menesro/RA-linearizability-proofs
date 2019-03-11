var ctrImpl:int;                //State of the implementation
var ctrSpec:int;                //State of the specification

//This method shows that refinement relation is preserved for the inc method
//Assume (sigma, inc(), sigma') is a valid step of the implementation
//We show that (refMap(sigma), inc(), refMap(sigma')) is a valid step of the specification as well
//refMap(sigma) == sigma (i.e., it is the identity function)
procedure refInc()
requires ctrImpl == ctrSpec;
modifies ctrImpl, ctrSpec;
ensures ctrImpl == ctrSpec;
{
    //inc ctrImpl
    ctrImpl := ctrImpl + 1;
    //inc ctrSpec
    ctrSpec := ctrSpec + 1;
}

//This method shows that refinement relation is preserved for the dec method
//Assume (sigma, dec(), sigma') is a valid step of the implementation
//We show that (refMap(sigma), dec(), refMap(sigma')) is a valid step of the specification as well
//refMap(sigma) == sigma (i.e., it is the identity function)
procedure refDec()
requires ctrImpl == ctrSpec;
modifies ctrImpl, ctrSpec;
ensures ctrImpl == ctrSpec;
{
    //dec ctrImpl
    ctrImpl := ctrImpl - 1;
    //dec ctrSpec
    ctrSpec := ctrSpec - 1;
}

//This method shows that refinement relation is preserved for the read method
//Assume (sigma, read()=>c, sigma') is a valid step of the implementation
//We show that (refMap(sigma), read()=>c, refMap(sigma')) is a valid step of the specification as well
//refMap(sigma) == sigma (i.e., it is the identity function)
procedure refRead()
requires ctrImpl == ctrSpec;
ensures ctrImpl == ctrSpec;
{
    var r1:int, r2:int;
    //read ctrImpl
    r1 := ctrImpl;
    //dec ctrSpec
    r2 := ctrSpec;

    assert r1 == r2;
}


