var ctr1:int;
var ctr2:int;

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


