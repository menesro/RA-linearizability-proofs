//Since every timestamp and element uniquely occurs in Wooki, we merge these two fields for simplifying the proofs and 
//impose less burden on the prover.
//Basically, we can think of it as the timestamp. But it can be used in place of the corresponding element as well.
type Estamp = int;

//CONSTANTS
const unique BEGIN:Estamp;         //First element marker of a string. We assume that it is included in the spec as the initial element as well to simplify proofs
const unique END:Estamp;           //Last element marker of a string. We assume that it is included in the spec as the last element as well to simplify proofs
axiom BEGIN < END;

//VARIABLES
//Implementation state:
var string1:[Estamp][Estamp]bool;   //String is a set of pairs. Each pair shows an element and its immediate successor
var degree1:[Estamp]int;            //Each element in the string has a degree.
var flag1:[Estamp]bool;             //Each element in the string has a flag field showing whether it is removed or not.

//Specification state:
var stringS:[Estamp][Estamp]bool;   //String is a set of pairs. Each pair shows an element and its immediate successor
var tomb:[Estamp]bool;              //Whether an element in the string is removed or not.

//FUNCTIONS

//An auxiliary function that shows whether an element occurs before another in the string.
function before(a:Estamp, b:Estamp, next:[Estamp][Estamp]bool) returns (ret:bool);
axiom (forall a:Estamp, b:Estamp, next:[Estamp][Estamp]bool :: before(a,b,next) <==>
            next[a][b] || (exists c:Estamp :: before(a,c,next) && next[c][b] ) 
      );

//Strings are acyclic
function acyclicBefore(next:[Estamp][Estamp]bool) returns (ret:bool);
axiom (forall next:[Estamp][Estamp]bool :: acyclicBefore(next) <==> 
            (forall a:Estamp, b:Estamp :: before(a,b,next) ==> !before(b,a,next) )  
      );

//Each element in the string can have at most one immediate predecessor or successor 
function uniquePreNext(next:[Estamp][Estamp]bool) returns (ret:bool);
axiom (forall next:[Estamp][Estamp]bool :: uniquePreNext(next) <==>  
            (forall a:Estamp, b:Estamp :: next[a][b] ==> (forall c:Estamp :: (c != a ==> !next[c][b]) && (c != b ==> !next[a][c]) ) 
            )
      );

//No element can come before BEGIN and after END in the string
function endsOfTheString(next:[Estamp][Estamp]bool) returns (ret:bool);
axiom (forall next:[Estamp][Estamp]bool ::  endsOfTheString(next) <==>
            (forall x:Estamp :: !next[x][BEGIN] && !next[END][x]  )
      );

//An auxiliary function that shows whether an element occurs in the string or not
function isElement(a:Estamp, next:[Estamp][Estamp]bool) returns (ret:bool);
axiom (forall a:Estamp, next:[Estamp][Estamp]bool :: isElement(a,next) <==>
            a == BEGIN || (exists b:Estamp :: next[b][a])
      );

//All pairs of elements in a string are ordered (i.e., one comes before the other)
function totallyOrderedBefore(next:[Estamp][Estamp]bool ) returns (ret:bool);
axiom (forall next:[Estamp][Estamp]bool :: totallyOrderedBefore(next) <==>
            (forall a:Estamp, b:Estamp :: isElement(a,next) && isElement(b,next) && a != b ==> before(a,b,next) || before(b,a,next) )
      );

//BEGIN comes before all the other elements and END comes after all the other elements 
function orderOfEnds(next:[Estamp][Estamp]bool) returns (ret:bool);
axiom ( forall next:[Estamp][Estamp]bool :: orderOfEnds(next) <==>
            (forall a:Estamp :: a != BEGIN && isElement(a,next) ==> before(BEGIN,a,next)  ) &&
            (forall a:Estamp :: a != END && isElement(a,next) ==> before(a,END,next)  )
      );

//A correct string obeys the above defined properties
function correctLinearString(next:[Estamp][Estamp]bool) returns (ret:bool);
axiom ( forall next:[Estamp][Estamp]bool :: correctLinearString(next) <==>
            acyclicBefore(next) && uniquePreNext(next) &&endsOfTheString(next) && totallyOrderedBefore(next) && orderOfEnds(next)
      );

//Each element is assigned a nonnegative degree
function degreeCond(deg:[Estamp]int) returns (ret:bool);
axiom ( forall deg:[Estamp]int :: degreeCond(deg) <==>
            (forall a:Estamp :: deg[a] >= 0) && deg[BEGIN] == 0 && deg[END] == 0
);

//Refinement function projects a state onto its first and negative of third fields i.e., RefMap((id,degree,flag)) == (id, !flag)
function refinementMapping(stringImp:[Estamp][Estamp]bool, stringSpec:[Estamp][Estamp]bool, flag:[Estamp]bool, tomb:[Estamp]bool ) returns (ret:bool);
axiom ( forall stringImp:[Estamp][Estamp]bool, stringSpec:[Estamp][Estamp]bool, flag:[Estamp]bool, tomb:[Estamp]bool :: refinementMapping(stringImp,stringSpec,flag,tomb) <==>
            (forall x:Estamp, y:Estamp :: before(x,y,stringImp) <==> before(x,y,stringSpec)  ) &&
            (forall x:Estamp :: flag[x] <==> !tomb[x]  )
      );

//LEMMATA
//Below are lemmas that are used for the refinement proofs later and that have inductive proofs (based on the inductive definition of reachability).
//Proving induction directly is not possible. Hence, we do proofs using pre-, post-conditions and recursion
//Each lemma is represented as a postcondition of a method.
//Immediately next method models and proves lemma using recursive calls.

//Before relation is transitive
procedure transitiveBefore(next:[Estamp][Estamp]bool);
ensures (forall a:Estamp, b:Estamp, c:Estamp :: before(a,b,next) && before(b,c,next) ==> before(a,c,next));

//a, b and c are unrestrained inputs. We assume before(a,b,next) and before(b,c,next).
//By applying structural induction on the recursive definition of before(b,c,next), we show before(a,c,next) holds.
procedure transitiveBeforeRec(a:Estamp, b:Estamp, c:Estamp, next:[Estamp][Estamp]bool)
requires before(a,b,next) && before(b,c,next);
ensures before(a,c,next);
{
    var cc:Estamp;
    if(*)
    {
        assume next[b][c];
        assert before(a,c,next);
    }
    else
    {
        assume before(b,cc,next) && next[cc][c];
        call transitiveBeforeRec(a,b,cc,next);
        assert before(a,c,next);
    }
}

//next2 is obtained by applying addBetweenImp(a,b,c) on next1.
//We claim that if x is before y in next1, so does it in next2.
procedure insertPreservesBefore(a:Estamp, b:Estamp, c:Estamp, next1:[Estamp][Estamp]bool, next2:[Estamp][Estamp]bool);
requires a != END && isElement(a,next1) && isElement(c,next1) && !isElement(b,next1);
requires correctLinearString(next1);
requires (forall x:Estamp, y:Estamp :: !((x == a && y == b) || (x == b && y == c) || (x == a && y == c)) ==> next1[x][y] == next2[x][y] );
requires next2[a][b] && next2[b][c] && !next2[a][c];
ensures (forall x:Estamp, y:Estamp :: before(x,y,next1) ==> before(x,y,next2)  );

//xx and yy are unstrained inputs. We assume xx comes before yy in next1.
//By applying structural induction on the recursive definition of before(xx, yy, next1), we show that before(xx,yy,next2)
procedure insertPreservesBeforeRec(xx:Estamp, yy:Estamp, a:Estamp, b:Estamp, c:Estamp, next1:[Estamp][Estamp]bool, next2:[Estamp][Estamp]bool)
requires a != END && isElement(a,next1) && isElement(c,next1) && !isElement(b,next1);
requires correctLinearString(next1);
requires (forall x:Estamp, y:Estamp :: !((x == a && y == b) || (x == b && y == c) || (x == a && y == c)) ==> next1[x][y] == next2[x][y] );
requires next2[a][b] && next2[b][c] && !next2[a][c];
ensures before(xx, yy, next2);
{
    var zz:Estamp;

    if(*)
    {
        assume next1[xx][yy];
        assert before(xx, yy, next2);
    }
    else
    {
        assume before(xx, zz, next1) && next1[zz][yy];    

        call insertPreservesBeforeRec(xx, zz, a, b, c, next1, next2);
        assert before(xx, yy, next2);
    }

    //assert false;
}

//next2 is obtained by applying addBetweenImp(a,b,c) on next1.
//We claim that if x is before y in next2, so either same is the case in next1 or
//x is b and y comes after a in next1 or y is b and x comes before c in next1.
procedure insertPreservesBefore2(a:Estamp, b:Estamp, c:Estamp, next1:[Estamp][Estamp]bool, next2:[Estamp][Estamp]bool);
requires a != END && isElement(a,next1) && isElement(c,next1) && !isElement(b,next1);
requires correctLinearString(next1);
requires next1[a][c];
requires (forall x:Estamp, y:Estamp :: !((x == a && y == b) || (x == b && y == c) || (x == a && y == c)) ==> next1[x][y] == next2[x][y] );
requires next2[a][b] && next2[b][c] && !next2[a][c];
ensures (forall x:Estamp, y:Estamp :: before(x,y,next2) ==> before(x,y,next1) || (x == b && before(a, y, next1)) || (y == b && before(x, c, next1))  );

//xx and yy are unstrained inputs. We assume xx comes before yy in next2.
//By applying structural induction on the recursive definition of before(xx, yy, next2), we show that the above claim holds
procedure insertPreservesBeforeRec2(xx:Estamp, yy:Estamp, a:Estamp, b:Estamp, c:Estamp, next1:[Estamp][Estamp]bool, next2:[Estamp][Estamp]bool)
requires a != END && isElement(a,next1) && isElement(c,next1) && !isElement(b,next1);
requires next1[a][c];
requires correctLinearString(next1);
requires (forall x:Estamp, y:Estamp :: !((x == a && y == b) || (x == b && y == c) || (x == a && y == c)) ==> next1[x][y] == next2[x][y] );
requires next2[a][b] && next2[b][c] && !next2[a][c];
requires before(xx, yy, next2);
ensures before(xx, yy, next1) || (xx == b && before(a, yy, next1)) || (yy == b && before(xx, c, next1));
{
    var zz:Estamp;

    if(*)
    {
        assume next2[xx][yy];
        assert before(xx, yy, next1) || (xx == b && before(a, yy, next1)) || (yy == b && before(xx, c, next1)) ;
    }
    else
    {
        assume before(xx, zz, next2) && next2[zz][yy];    

        call insertPreservesBeforeRec2(xx, zz, a, b, c, next1, next2);

        assert before(xx, yy, next1) || (xx == b && before(a, yy, next1)) || (yy == b && before(xx, c, next1));
    }
}

//METHODS

//addBetween(a,b,c) method of the implementation
procedure addBetweenImp(a:Estamp, b:Estamp, c:Estamp)
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires degree1[a] > degree1[c] ==> degree1[b] == degree1[a] + 1;
requires degree1[a] <= degree1[c] ==> degree1[b] == degree1[c] + 1;
requires correctLinearString(string1) && degreeCond(degree1);
modifies string1;
ensures correctLinearString(string1);                         
ensures (forall x:Estamp, y:Estamp :: before(x,y,old(string1)) ==> before(x,y,string1)  ); 
ensures before(a,b,string1) && before(b,c,string1);
ensures (forall x:Estamp, y:Estamp :: before(x,y,string1) ==> before(x,y,old(string1)) || (x == b && before(a, y, old(string1))) || (y == b && before(x, c, old(string1)))  );
{
    call IntegrateIns(a,b,c);
}

//IntegrateIns method of the implementation
procedure IntegrateIns(a:Estamp, b:Estamp, c:Estamp)
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires correctLinearString(string1) && degreeCond(degree1);
modifies string1;
ensures (forall x:Estamp, y:Estamp :: before(x,y,old(string1)) ==> before(x,y,string1)  ); 
ensures before(a,b,string1) && before(b,c,string1);
ensures (forall x:Estamp, y:Estamp :: before(x,y,string1) ==> before(x,y,old(string1)) || (x == b && before(a, y, old(string1))) || (y == b && before(x, c, old(string1)))  );
ensures correctLinearString(string1);
{
    var F:[Estamp]bool, dmin:int;
    var Fa:Estamp, Fc:Estamp;

    //If there is no other element between a and c 
    if(string1[a][c])
    {
        string1[a][c] := false;
        string1[a][b] := true;
        string1[b][c] := true;

        //This lemmas are needed for the postconditions
        call insertPreservesBefore(a, b, c, old(string1), string1);
        call insertPreservesBefore2(a, b, c, old(string1), string1);
        call transitiveBefore(string1);

        //This assertion is left for speeding up the verification
        assert endsOfTheString(string1);

    }
    else
    {
        //This is the case if there is an element between a and c
        assume (exists x:Estamp :: before(a,x,string1) && before(x,c,string1) );
        
        //Value of dmin and elements of F
        assume (forall x:Estamp :: before(a,x,string1) && before(x,c,string1) ==> degree1[x] >= dmin );
        assume (exists x:Estamp :: before(a,x,string1) && before(x,c,string1) && degree1[x] == dmin);
        assume (forall x:Estamp :: F[x] <==> before(a,x,string1) && before(x,c,string1) && degree1[x] == dmin );

        call transitiveBefore(string1);

        //Fa and Fc (a and c for the next iteration)
        assume (forall ff:Estamp ::  F[ff] ==> ff < b ) ==> Fc == c;
        assume (exists ff:Estamp :: F[ff] && ff >= b ) ==> F[Fc] && (forall fx:Estamp :: before(fx,Fc,string1) && F[fx] ==> fx < b) && Fc > b;

        assume (exists ff:Estamp ::  F[ff] && (forall x:Estamp :: before(a,x,string1) && before(x,ff,string1) ==> !F[x] ) && ff > b) ==> Fa == a ;
        assume !(exists ff:Estamp ::  F[ff] && (forall x:Estamp :: before(a,x,string1) && before(x,ff,string1) ==> !F[x] ) && ff > b) ==> 
                        F[Fa] && before(Fa,Fc,string1) && (forall x:Estamp :: before(Fa,x,string1) && before(x,Fc,string1) ==> !F[x]);

        
        call IntegrateIns(Fa,b,Fc);

        call transitiveBefore(string1);        
    }
}

//addBetween(a,b,c) method of the Specification
procedure addBetweenSpec(a:Estamp, b:Estamp, c:Estamp);
requires a != END && isElement(a,stringS) && isElement(c,stringS) && !isElement(b,stringS);
requires before(a,c,stringS);
requires correctLinearString(stringS);
modifies stringS;
ensures correctLinearString(stringS); 
ensures (forall x:Estamp, y:Estamp :: before(x,y,old(stringS)) ==> before(x,y,stringS)  ); 
ensures before(a,b,stringS) && before(b,c,stringS);
ensures  (forall x:Estamp, y:Estamp :: before(x,y,stringS) ==> x == b || y == b || before(x,y,old(stringS)) );


//remove(r) method of the implementation
procedure removeImp(r:Estamp);
modifies flag1;
ensures flag1[r] == false;
ensures (forall rr:Estamp :: r != rr ==> flag1[rr] == old(flag1)[rr]  );

//remove(r) method of the specification
procedure removeSpec(r:Estamp);
modifies tomb;
ensures tomb[r] == true;
ensures (forall rr:Estamp :: r != rr ==> tomb[rr] == old(tomb)[rr]  );

//read method of the implementation
procedure readImp() returns (l:[Estamp][Estamp]bool);
ensures (forall x:Estamp,  y:Estamp :: before(x,y,l) <==> before(x,y,string1) && flag1[x] && flag1[y] );

//read method of the specification
procedure readSpec() returns (l:[Estamp][Estamp]bool);
ensures (forall x:Estamp,  y:Estamp :: before(x,y,l) <==> before(x,y,stringS) && !tomb[x] && !tomb[y] );

//This method proves that refinement relation is preserved by the addBetween method of the implementation
//Assume (sigma, addBetween(a,b,c), sigma') is a step of the implementation
//We show that (RefMap(sigma), addBetween(a,b,c,), RefMap(sigma')) is a step of the specification
//Initially, We assume that refinement relation and program invariants hold.
//We show that they still hold after both programs execute addBetween(a,b,c)
procedure refAddBetween(a:Estamp, b:Estamp, c:Estamp)
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires degree1[a] > degree1[c] ==> degree1[b] == degree1[a] + 1;
requires degree1[a] <= degree1[c] ==> degree1[b] == degree1[c] + 1;
requires correctLinearString(string1) && degreeCond(degree1);
requires correctLinearString(stringS);
requires refinementMapping(string1,stringS,flag1,tomb);
modifies string1, stringS;
ensures correctLinearString(string1) && degreeCond(degree1);
ensures correctLinearString(stringS);
ensures refinementMapping(string1,stringS,flag1,tomb);
{
    call addBetweenImp(a,b,c);
    call addBetweenSpec(a,b,c);

    //Specification function is nondeterministic and can insert b in an arbitrary position between a and c.
    //We choose the step that it inserts exactly to the same place with the specification. 
    assume (forall x:Estamp :: before(a,x,string1) && before(x,c,string1) ==> (before(x,b,string1) <==> before(x,b,stringS)  )  );
    
    //This lemmas and assertions help verification of the postconditions (refienement relation and the invariants)
    call transitiveBefore(string1);
    call transitiveBefore(stringS);
    assert (forall x:Estamp, y:Estamp :: before(x,y,string1) <==> before(x,y,stringS));
}

//This method proves that refinement relation is preserved by the remove method of the implementation
//Assume (sigma, remove(), sigma') is a step of the implementation
//We show that (RefMap(sigma), remove(r), RefMap(sigma')) is a step of the specification
//Initially, We assume that refinement relation and program invariants hold.
//We show that they still hold after both programs execute remove(r)
procedure refRemove(r:Estamp)
requires correctLinearString(string1) && degreeCond(degree1);
requires correctLinearString(stringS);
requires refinementMapping(string1,stringS,flag1,tomb);
modifies flag1, tomb;
ensures correctLinearString(string1) && degreeCond(degree1);
ensures correctLinearString(stringS);
ensures refinementMapping(string1,stringS,flag1,tomb);
{
    call removeImp(r);
    call removeSpec(r);
}

//This method proves that refinement relation is preserved by the read method of the implementation
//Assume (sigma, read()=>l, sigma') is a step of the implementation
//We show that (RefMap(sigma), read()=>l, RefMap(sigma')) is a step of the specification
//Initially, We assume that refinement relation and program invariants hold.
//We show that they still hold after both programs execute read(r) and returned strings are the same
procedure refRead()
requires correctLinearString(string1) && degreeCond(degree1);
requires correctLinearString(stringS);
requires refinementMapping(string1,stringS,flag1,tomb);
ensures correctLinearString(string1) && degreeCond(degree1);
ensures correctLinearString(stringS);
ensures refinementMapping(string1,stringS,flag1,tomb);
{
    var l1:[Estamp][Estamp]bool, l2:[Estamp][Estamp]bool;

    call l1 := readImp();
    call l2 := readSpec();

    assert (forall x:Estamp, y:Estamp :: before(x,y,l1) <==> before(x,y,l2) );
}