type X;
type Timestamp = int;                   //Timestamps are assumed to be integers to ensure a total order.

var xImp:X;                             //x field of the implementation state
var tsImp:Timestamp;                    //Timestamp field of the implementation state
var xSpec:X;                            //Specification state

//write method description for the implementation
procedure writeImp(a:X, ts:Timestamp);
modifies xImp, tsImp;
ensures tsImp < ts ==> xImp == a && tsImp == ts;
ensures tsImp >= ts ==> xImp == old(xImp) && tsImp == old(tsImp);

//write method description for the specification
procedure writeSpec(a:X);
modifies xSpec;
ensures xSpec == a;

//read method description for the implementation
procedure readImp() returns (a:X);
ensures a == xImp;

//read method description for the specification
procedure readSpec() returns (a:X);
ensures a == xSpec;

//This method shows that refinement relation is preserved for the write method
//Assume (sigma, write(a, ts), sigma') is a valid step of the implementation
//We show that (refMap(sigma), write(a), refMap(sigma')) is a valid step of the specification as well
//refMap projects the implementation state onto the first component i.e., refMap((a,ts)) == a
procedure refWrite(a:X, ts:Timestamp)
requires xImp == xSpec;
requires ts > tsImp;
modifies xImp, tsImp, xSpec;
ensures xImp == xSpec;
{
    call writeImp(a, ts);
    call writeSpec(a);
}

//This method shows that refinement relation is preserved for the read method
//Assume (sigma, read()=>x, sigma') is a valid step of the implementation
//We show that (refMap(sigma), read()=>x, refMap(sigma')) is a valid step of the specification as well
//refMap projects the implementation state onto the first component i.e., refMap((a,ts)) == a
procedure refRead()
requires xImp == xSpec;
ensures xImp == xSpec;
{
    var r1:X, r2:X;

    call r1 := readImp();
    call r2 := readSpec();

    assert r1 == r2;
}