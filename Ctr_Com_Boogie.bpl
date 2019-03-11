//We use two implementation states (sigma1 and sigma2) for the commutatitivity proofs
//Each sigmai is an integer ctri
var ctr1:int;
var ctr2:int;

//Commutativity check between two add methods.
//We assume that sigma1 == sigma2 initially.
//We apply inc() and inc() (in that order) to sigma1 and obtain the new sigma1
//We apply inc() and inc() (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comIncInc()
requires ctr1 == ctr2;
modifies ctr1, ctr2;
ensures ctr1 == ctr2;
{
    //inc();inc()
    //eff inc()
    ctr1 := ctr1+1;
    //eff inc()
    ctr1 := ctr1+1;

    //inc();inc()
    //eff inc()
    ctr2 := ctr2 + 1;
    //eff inc()
    ctr2 := ctr2 + 1;
}

//Commutativity check between an inc and a dec method.
//We assume that sigma1 == sigma2 initially.
//We apply inc() and dec() (in that order) to sigma1 and obtain the new sigma1
//We apply dec() and inc() (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comIncDec()
requires ctr1 == ctr2;
modifies ctr1, ctr2;
ensures ctr1 == ctr2;
{
    //inc();dec()
    //eff inc()
    ctr1 := ctr1+1;
    //eff dec()
    ctr1 := ctr1-1;

    //dec();inc()
    //eff dec()
    ctr2 := ctr2 - 1;
    //eff inc()
    ctr2 := ctr2 + 1;
}

//Commutativity check between a dec and an inc() method.
//We assume that sigma1 == sigma2 initially.
//We apply dec() and inc() (in that order) to sigma1 and obtain the new sigma1
//We apply inc() and dec() (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comDecInc()
requires ctr1 == ctr2;
modifies ctr1, ctr2;
ensures ctr1 == ctr2;
{
    //dec();inc()
    //eff dec()
    ctr1 := ctr1-1;
    //eff inc()
    ctr1 := ctr1+1;

    //inc();dec()
    //eff inc()
    ctr2 := ctr2 + 1;
    //eff dec()
    ctr2 := ctr2 - 1;
}

//Commutativity check between two add dec.
//We assume that sigma1 == sigma2 initially.
//We apply dec() and dec() (in that order) to sigma1 and obtain the new sigma1
//We apply dec() and dec() (in that order) to sigma2 and obtain the new sigma2
//We show that still sigma1 == sigma2 
procedure comDecDec()
requires ctr1 == ctr2;
modifies ctr1, ctr2;
ensures ctr1 == ctr2;
{
    //dec();dec()
    //eff dec()
    ctr1 := ctr1-1;
    //eff dec()
    ctr1 := ctr1-1;

    //dec();dec()
    //eff dec()
    ctr2 := ctr2 - 1;
    //eff dec()
    ctr2 := ctr2 - 1;
}


