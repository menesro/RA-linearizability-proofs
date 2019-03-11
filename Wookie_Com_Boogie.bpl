//Since every timestamp and element uniquely occurs in Wooki, we merge these two fields for simplifying the proofs and 
//impose less burden on the prover.
//Basically, we can think of it as the timestamp. But it can be used in place of the corresponding element as well.
type Estamp = int;

//CONSTANTS
const unique BEGIN:Estamp;          //First element marker of a string. We assume that it is included in the spec as the initial element as well to simplify proofs
const unique END:Estamp;            //Last element marker of a string. We assume that it is included in the spec as the last element as well to simplify proofs
axiom BEGIN < END;

//VARIABLES

//Various implementation state declarations for proving commutativity
//Each (stringi, degreei, pairi) tuple corresponds to to the state sigmai

var string1:[Estamp][Estamp]bool;   //String is a set of pairs. Each pair shows an element and its immediate successor
var degree1:[Estamp]int;            //Each element in the string has a degree.
var flag1:[Estamp]bool;             //Each element in the string has a flag field showing whether it is removed or not.

var string2:[Estamp][Estamp]bool;   //String is a set of pairs. Each pair shows an element and its immediate successor
var degree2:[Estamp]int;            //Each element in the string has a degree.
var flag2:[Estamp]bool;             //Each element in the string has a flag field showing whether it is removed or not.

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
//EFFECTORS

//addBetween method description for sigma1
procedure addBetween1(a:Estamp, b:Estamp, c:Estamp)
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
ensures  (forall x:Estamp :: string1[b][x] ==> x == c || x > b);
ensures (forall x:Estamp :: string1[x][b] ==> x == a || b > x);
{
    call IntegrateIns(a,b,c);
}

//IntegrateIns method description for sigma1
procedure IntegrateIns(a:Estamp, b:Estamp, c:Estamp)
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires correctLinearString(string1) && degreeCond(degree1);
modifies string1;
ensures correctLinearString(string1);
ensures (forall x:Estamp, y:Estamp :: before(x,y,old(string1)) ==> before(x,y,string1)  ); 
ensures before(a,b,string1) && before(b,c,string1);
ensures (forall x:Estamp, y:Estamp :: before(x,y,string1) ==> before(x,y,old(string1)) || (x == b && before(a, y, old(string1))) || (y == b && before(x, c, old(string1)))  );
ensures string1[a][b] || (exists x:Estamp :: string1[x][b] && x < b   );
ensures string1[b][c] || (exists x:Estamp :: string1[b][x] && x > b  );
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

        //This assertions are left for speeding up the verification
        assert string1[a][b];
        assert string1[b][c];
        assert totallyOrderedBefore(string1);
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

//addBetween method description for sigma2
procedure addBetween2(a:Estamp, b:Estamp, c:Estamp)
requires a != END && isElement(a,string2) && isElement(c,string2) && !isElement(b,string2);
requires before(a,c,string2);
requires degree2[a] > degree2[c] ==> degree2[b] == degree2[a] + 1;
requires degree2[a] <= degree2[c] ==> degree2[b] == degree2[c] + 1;
requires correctLinearString(string2) && degreeCond(degree2);
modifies string2;
ensures correctLinearString(string2);
ensures (forall x:Estamp, y:Estamp :: before(x,y,old(string2)) ==> before(x,y,string2)  ); 
ensures before(a,b,string2) && before(b,c,string2);
ensures (forall x:Estamp, y:Estamp :: before(x,y,string2) ==> before(x,y,old(string2)) || (x == b && before(a, y, old(string2))) || (y == b && before(x, c, old(string2)))  );
ensures  (forall x:Estamp :: string2[b][x] ==> x == c || x > b);
ensures (forall x:Estamp :: string2[x][b] ==> x == a || b > x);
{
    call IntegrateIns2(a,b,c);
}

//IntegrateIns method description for sigma2
procedure IntegrateIns2(a:Estamp, b:Estamp, c:Estamp)
requires a != END && isElement(a,string2) && isElement(c,string2) && !isElement(b,string2);
requires before(a,c,string2);
requires correctLinearString(string2) && degreeCond(degree2);
modifies string2;
ensures correctLinearString(string2);
ensures (forall x:Estamp, y:Estamp :: before(x,y,old(string2)) ==> before(x,y,string2)  ); 
ensures before(a,b,string2) && before(b,c,string2);
ensures (forall x:Estamp, y:Estamp :: before(x,y,string2) ==> before(x,y,old(string2)) || (x == b && before(a, y, old(string2))) || (y == b && before(x, c, old(string2)))  );
ensures string2[a][b] || (exists x:Estamp :: string2[x][b] && x < b   );
ensures string2[b][c] || (exists x:Estamp :: string2[b][x] && x > b  );
{
    var F:[Estamp]bool, dmin:int;
    var Fa:Estamp, Fc:Estamp;

    //If there is no other element between a and c 
    if(string2[a][c])
    {
        string2[a][c] := false;
        string2[a][b] := true;
        string2[b][c] := true;

        //This lemmas are needed for the postconditions
        call insertPreservesBefore(a, b, c, old(string2), string2);
        call insertPreservesBefore2(a, b, c, old(string2), string2);
        call transitiveBefore(string2);

         //This assertions are left for speeding up the verification
        assert string2[a][b];
        assert string2[b][c];
        assert totallyOrderedBefore(string2);
    }
    else
    {
        //This is the case if there is an element between a and c
        assume (exists x:Estamp :: before(a,x,string2) && before(x,c,string2) );

        //Value of dmin and elements of F
        assume (forall x:Estamp :: before(a,x,string2) && before(x,c,string2) ==> degree2[x] >= dmin );
        assume (exists x:Estamp :: before(a,x,string2) && before(x,c,string2) && degree2[x] == dmin);
        assume (forall x:Estamp :: F[x] <==> before(a,x,string2) && before(x,c,string2) && degree2[x] == dmin );

        call transitiveBefore(string2);

        //Fa and Fc (a and c for the next iteration)
        assume (forall ff:Estamp ::  F[ff] ==> ff < b ) ==> Fc == c;
        assume (exists ff:Estamp :: F[ff] && ff >= b ) ==> F[Fc] && (forall fx:Estamp :: before(fx,Fc,string2) && F[fx] ==> fx < b) && Fc > b;

        assume (exists ff:Estamp ::  F[ff] && (forall x:Estamp :: before(a,x,string2) && before(x,ff,string2) ==> !F[x] ) && ff > b) ==> Fa == a ;
        assume !(exists ff:Estamp ::  F[ff] && (forall x:Estamp :: before(a,x,string2) && before(x,ff,string2) ==> !F[x] ) && ff > b) ==> 
                        F[Fa] && before(Fa,Fc,string2) && (forall x:Estamp :: before(Fa,x,string2) && before(x,Fc,string2) ==> !F[x]);

        
        call IntegrateIns2(Fa,b,Fc);

        call transitiveBefore(string2);        
    }
}

//remove method description for sigma1
procedure remove1(r:Estamp);
modifies flag1;
ensures flag1[r] == false;
ensures (forall rr:Estamp :: r != rr ==> flag1[rr] == old(flag1)[rr]  );

//remove method description for sigma1
procedure remove2(r:Estamp);
modifies flag2;
ensures flag2[r] == false;
ensures (forall rr:Estamp :: r != rr ==> flag2[rr] == old(flag2)[rr]  );


//We aim to show that two concurrent addBetween operations commute.
//Assume sigma1 == sigma2 holds initially.
//We apply addBetween(a,b,c) and addBetween(d,e,f) (in that order) to sigma1 and obtain a new sigma1
//We apply addBetween(d,e,f) and addBetween(a,b,c) (in that order) to sigma2 and obtain a new sigma2
//We show that sigma1 == sigma2 still holds.
procedure comAddBetweenAddBetween(a:Estamp, b:Estamp, c:Estamp, d:Estamp, e:Estamp, f:Estamp)
requires b != e;
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires degree1[a] > degree1[c] ==> degree1[b] == degree1[a] + 1;
requires degree1[a] <= degree1[c] ==> degree1[b] == degree1[c] + 1;
requires d != END && isElement(d,string1) && isElement(f,string1) && !isElement(e,string1);
requires before(d,f,string1);
requires degree1[d] > degree1[f] ==> degree1[e] == degree1[d] + 1;
requires degree1[d] <= degree1[f] ==> degree1[e] == degree1[f] + 1;
requires correctLinearString(string1) && degreeCond(degree1);
requires string1 == string2 && degree1 == degree2 && flag1 == flag2;
modifies string1, string2;
ensures (forall x:Estamp, y:Estamp :: string1[x][y] <==> string2[x][y]  );
ensures degree1 == degree2 && flag1 == flag2;
ensures correctLinearString(string1) && degreeCond(degree1);
{
    var mid1:[Estamp][Estamp]bool, mid2:[Estamp][Estamp]bool;

    call addBetween1(a,b,c);
    mid1 := string1;                    //We keep the midstate to use Lemma 4
    call addBetween1(d,e,f);
   
    call addBetween2(d,e,f);
    mid2 := string2;                    //We keep the midstate to use Lemma 4
    call addBetween2(a,b,c);
    
    assume (forall x:Estamp, y:Estamp :: x != e && y != e ==> (before(x,y,mid1) <==> before(x,y,string2)  )  );     //Holds by Lemma 4 in the paper
    assume (forall x:Estamp, y:Estamp :: x != b && y != b ==> (before(x,y,mid2) <==> before(x,y,string1)  )  );     //Holds by Lemma 4 in the paper
   
    //We need following lemmas to prove postconditions.
    call transitiveBefore(string1);
    call transitiveBefore(string2);

    //We keep these assertions for faster reasoning 
    assert (exists x:Estamp :: before(b,x,string1) && before(x,e,string1) ) ==> before(b,e,string2);
    assert (exists x:Estamp :: before(e,x,string1) && before(x,b,string1) ) ==> before(e,b,string2);    

    assert (forall x:Estamp, y:Estamp :: before(x,y,string1) <==> before(x,y,string2)  );

}

//We aim to show that concurrent addBetween and remove operations commute.
//Assume sigma1 == sigma2 holds initially.
//We apply addBetween(a,b,c) and remove(r) (in that order) to sigma1 and obtain a new sigma1
//We apply remove(r) and addBetween(a,b,c) (in that order) to sigma2 and obtain a new sigma2
//We show that sigma1 == sigma2 still holds.
procedure comAddBetweenRemove(a:Estamp, b:Estamp, c:Estamp, r:Estamp)
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires degree1[a] > degree1[c] ==> degree1[b] == degree1[a] + 1;
requires degree1[a] <= degree1[c] ==> degree1[b] == degree1[c] + 1;
requires correctLinearString(string1) && degreeCond(degree1);
requires string1 == string2 && degree1 == degree2 && flag1 == flag2;
modifies string1, string2, flag1, flag2;
ensures (forall x:Estamp, y:Estamp :: string1[x][y] <==> string2[x][y]  );
ensures (forall rr:Estamp :: flag1[rr] == flag2[rr]);
ensures degree1 == degree2; 
ensures correctLinearString(string1) && degreeCond(degree1);
{
    call addBetween1(a,b,c);
    call remove1(r);

    call remove2(r);
    call addBetween2(a,b,c);

    assume (forall x:Estamp, y:Estamp :: before(x,y,string1) <==> before(x,y,string2)  );       //This assumption holds due to equivalencePreserved method below
}

//We aim to show that concurrent remove and addBetween operations commute.
//Assume sigma1 == sigma2 holds initially.
//We apply remove(r) and addBetween(a,b,c) (in that order) to sigma1 and obtain a new sigma1
//We apply addBetween(a,b,c) and remove(r) (in that order) to sigma2 and obtain a new sigma2
//We show that sigma1 == sigma2 still holds.
procedure comRemoveAddBetween(a:Estamp, b:Estamp, c:Estamp, r:Estamp)
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires degree1[a] > degree1[c] ==> degree1[b] == degree1[a] + 1;
requires degree1[a] <= degree1[c] ==> degree1[b] == degree1[c] + 1;
requires correctLinearString(string1) && degreeCond(degree1);
requires string1 == string2 && degree1 == degree2 && flag1 == flag2;
modifies string1, string2, flag1, flag2;
ensures (forall x:Estamp, y:Estamp :: string1[x][y] <==> string2[x][y]  );
ensures (forall rr:Estamp :: flag1[rr] == flag2[rr]);
ensures degree1 == degree2; 
ensures correctLinearString(string1) && degreeCond(degree1);
{
    call remove1(r);
    call addBetween1(a,b,c);

    call addBetween2(a,b,c);
    call remove2(r);

    assume (forall x:Estamp, y:Estamp :: before(x,y,string1) <==> before(x,y,string2)  );       //This assumption holds due to equivalencePreserved method below
}

//We aim to show that concurrent remove operations commute.
//Assume sigma1 == sigma2 holds initially.
//We apply remove(r1) and remove(r2) (in that order) to sigma1 and obtain a new sigma1
//We apply remove(r2) and remove(r1) (in that order) to sigma2 and obtain a new sigma2
//We show that sigma1 == sigma2 still holds.
procedure comRemoveRemove(r1:Estamp, r2:Estamp)
requires string1 == string2 && degree1 == degree2 && flag1 == flag2;
requires correctLinearString(string1) && degreeCond(degree1);
modifies flag1, flag2;
ensures string1 == string2 && degree1 == degree2;
ensures (forall rr:Estamp :: flag1[rr] == flag2[rr]);
ensures correctLinearString(string1) && degreeCond(degree1);
{
    call remove1(r1);
    call remove1(r2);

    call remove2(r2);
    call remove2(r1);
}

//Let sigma1 == sigma2. We aim to show it still holds if we apply addBetween(a,b,c) to both states.
//We do this by induction on the length of (a,c) in sigma1.
//We show that at each call IntegrateIns method is called with the same parameters 
//i.e., if sigma1 calls addBetween(a,b,c) and sigma2 calls addBetween(d,b,e) then a == d and c == e,
//and at the base case b is placed to the same place.
procedure equivalencePreserved(a:Estamp, b:Estamp, c:Estamp, d:Estamp, e:Estamp)
requires a == d && c == e;
requires string1 == string2 && degree1 == degree2;
requires a != END && isElement(a,string1) && isElement(c,string1) && !isElement(b,string1);
requires before(a,c,string1);
requires correctLinearString(string1) && degreeCond(degree1);
modifies string1, string2;
ensures (forall x:Estamp, y:Estamp :: before(x, y, string1) <==> before(x, y, string2) );
{
    var F1:[Estamp]bool, dmin1:int;     //F1, dmin fields for IntegrateIns call of sigma1
    var Fa1:Estamp, Fc1:Estamp;         //Fa1, Fc1 fields for IntegrateIns call of sigma1
    var F2:[Estamp]bool, dmin2:int;     //F1, dmin fields for IntegrateIns call of sigma2
    var Fa2:Estamp, Fc2:Estamp;         //Fa1, Fc1 fields for IntegrateIns call of sigma1

    assert isElement(a,string2) && isElement(c,string2) && !isElement(b,string2);
    assert correctLinearString(string2) && degreeCond(degree2);
    assert before(a,c,string2);

    assert (forall x:Estamp, y:Estamp :: before(x,y,string1) <==> before(x,y,string2));

    if(*)
    {
        //Base case: string1[a][c] and string2[d][e]
        assume string1[a][c];
        
        call IntegrateIns(a, b, c);
        call IntegrateIns2(d, b, e);

        call transitiveBefore(string1);
        call transitiveBefore(string2);
        assert (forall x:Estamp, y:Estamp :: before(x, y, string1) <==> before(x, y, string2) );
    }
    else
    {
        //F1, dmin1, Fa1 and Fc1 values
        assume (exists x:Estamp :: before(a,x,string1) && before(x,c,string1) );
        assume (forall x:Estamp :: before(a,x,string1) && before(x,c,string1) ==> degree1[x] >= dmin1 );
        assume (exists x:Estamp :: before(a,x,string1) && before(x,c,string1) && degree1[x] == dmin1);
        assume (forall x:Estamp :: F1[x] <==> before(a,x,string1) && before(x,c,string1) && degree1[x] == dmin1 );

        assume (forall ff:Estamp ::  F1[ff] ==> ff < b ) ==> Fc1 == c;
        assume (exists ff:Estamp :: F1[ff] && ff >= b ) ==> F1[Fc1] && (forall fx:Estamp :: before(fx,Fc1,string1) && F1[fx] ==> fx < b) && Fc1 > b;

        assume (exists ff:Estamp ::  F1[ff] && (forall x:Estamp :: before(a,x,string1) && before(x,ff,string1) ==> !F1[x] ) && ff > b) ==> Fa1 == a ;
        assume !(exists ff:Estamp ::  F1[ff] && (forall x:Estamp :: before(a,x,string1) && before(x,ff,string1) ==> !F1[x] ) && ff > b) ==> 
                        F1[Fa1] && before(Fa1,Fc1,string1) && (forall x:Estamp :: before(Fa1,x,string1) && before(x,Fc1,string1) ==> !F1[x]);

        //F2, dmin2, Fa2 and Fc2 values
        assume (exists x:Estamp :: before(a,x,string2) && before(x,c,string2) );
        assume (forall x:Estamp :: before(a,x,string2) && before(x,c,string2) ==> degree2[x] >= dmin2 );
        assume (exists x:Estamp :: before(a,x,string2) && before(x,c,string2) && degree2[x] == dmin2);
        assume (forall x:Estamp :: F2[x] <==> before(a,x,string2) && before(x,c,string2) && degree2[x] == dmin2 );

        assume (forall ff:Estamp ::  F2[ff] ==> ff < b ) ==> Fc2 == c;
        assume (exists ff:Estamp :: F2[ff] && ff >= b ) ==> F2[Fc2] && (forall fx:Estamp :: before(fx,Fc2,string2) && F2[fx] ==> fx < b) && Fc2 > b;

        assume (exists ff:Estamp ::  F2[ff] && (forall x:Estamp :: before(a,x,string2) && before(x,ff,string2) ==> !F2[x] ) && ff > b) ==> Fa2 == a ;
        assume !(exists ff:Estamp ::  F2[ff] && (forall x:Estamp :: before(a,x,string2) && before(x,ff,string2) ==> !F2[x] ) && ff > b) ==> 
                        F2[Fa2] && before(Fa2,Fc2,string2) && (forall x:Estamp :: before(Fa2,x,string2) && before(x,Fc2,string2) ==> !F2[x]);

        assert dmin1 == dmin2;
        assert (forall x:Estamp :: F1[x] <==> F2[x] );
        
        //Next intervals for the recursive calls are the same
        assert Fa1 == Fa2 && Fc1 == Fc2;

        //(Fa1, Fc) is a smaller interval than (a, c)
        assert Fa1 == a || before(a,Fa1, string1);
        assert Fc1 == c || before(Fc1, c, string1);
        assert Fa1 != a || Fc1 != c;
        
        //Since (Fa1, Fc) is a smaller interval than (a, c) We can assume the induction hypothesis
       call equivalencePreserved(Fa1, b, Fc1, Fa2, Fc2);
    }
}
