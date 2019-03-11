type X;
type Timestamp = int;                               //Timestamps are assumed to be integers to ensure a total order.

//We use two implementation states (sigma1 and sigma2) for the commutatitivity proofs
//Each sigmai is a pair (xi, tsi)
var x1:X;
var ts1:Timestamp;
var x2:X;
var ts2:Timestamp;

//write method description for sigma1
procedure write1(a:X, ts:Timestamp);
modifies x1, ts1;
ensures ts1 < ts ==> x1 == a && ts1 == ts;
ensures ts1 >= ts ==> x1 == old(x1) && ts1 == old(ts1);

//write method description for sigma2
procedure write2(a:X, ts:Timestamp);
modifies x2, ts2;
ensures ts2 < ts ==> x2 == a && ts2 == ts;
ensures ts2 >= ts ==> x2 == old(x2) && ts2 == old(ts2);

//Commutativity check between two write methods
//We assume that sigma1 == sigma2 initially.
//We apply write(a1, t1) and write(a2, t2) (in that order) to sigma1 and obtain the new sigma1
//We apply write(a2, t2) and write(a1, t1) (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comWriteWrite(a1:X, t1:Timestamp, a2:X, t2:Timestamp)
requires x1 == x2 && ts1 == ts2;
modifies x1, ts1, x2, ts2;
ensures x1 == x2 && ts1 == ts2;
{
    //write(a1,t1); write(a2,t2);
    call write1(a1,t1);
    call write1(a2,t2);

    //write(a2,t2); write(a1,t1);
    call write2(a2,t2);
    call write2(a1,t1);
}
