AJL_MoodyPatera := function(LIE_TYPE,n)
// Auxiliary function computing the number of classes of elements
// of a order n in a complex group of exceptional type LIE_TYPE

  LIE_TYPE := CartanName(RootDatum(LIE_TYPE));

  Q<x,y> := PolynomialRing(RationalField(),2);
  R<X,Y>,r := Q/ideal<Q|[1 - x^3,1 - y^2]>;
  P<t> := PowerSeriesRing(R : Precision := n+2);
  
  G2 := (P!((1-t)*(1-(t^2))*(1-(t^3))))^(-1);
  F4 := (P!((1-t)*((1-(t^2))^2)*(1-(t^3))*(1-t^4)))^(-1);
  E6 := (P!( (1-t)*(1-(X*t))*(1-(X^2)*t)
        * (1-(t^2))*(1-(X*(t^2)))*(1-((X^2)*(t^2)))
        * (1-(t^3)) ))^(-1);
  E7 := (P!( (1-t)*(1-(Y*t))
          * ((1-(t^2))^2)*(1-(Y*(t^2)))
          * (1-(t^3))*(1-(Y*(t^3)))
          * (1-(t^4)) ))^(-1);
  E8 := (P!( (1-t)
          * ((1-(t^2))^2)
          * ((1-(t^3))^2)
          * ((1-(t^4))^2)
          * (1-(t^5))
          * (1-(t^6)) ))^(-1);
  
  if LIE_TYPE in ["G2","G_2"] then G := G2;
  elif LIE_TYPE in ["F4", "F_4"] then G := F4;
  elif LIE_TYPE in ["E6", "E_6"] then G := E6;
  elif LIE_TYPE in ["E7", "E_7"] then G := E7;
  elif LIE_TYPE in ["E8", "E_8"] then G := E8;
  else
    printf "Invalid Lie type.\n";
    return 0;
  end if;

  COEFFS := [Coefficient(G,i) :  i in [1..n]];

  NUMBEROF := COEFFS;
  for ORDER in [2..n] do
    if IsPrime(ORDER) then
      NUMBEROF[ORDER] := COEFFS[ORDER] - 1;
    else
      NUMBEROF[ORDER] := NUMBEROF[ORDER] - &+[NUMBEROF[k] : k in Divisors(ORDER) | not k eq ORDER];
    end if;
  end for;

  if LIE_TYPE eq CartanName(RootDatum("E6")) then
    for ORDER in [1..n] do
      NUMBEROF[ORDER] := Coefficient(NUMBEROF[ORDER],X,0);
    end for;
  elif LIE_TYPE eq CartanName(RootDatum("E7")) then
    for ORDER in [1..n] do
      NUMBEROF[ORDER] := Coefficient(NUMBEROF[ORDER],Y,0);
    end for;
  end if;
  
  return NUMBEROF;

end function;



exelts_mp := function(LIE_TYPE, n : debug := false);
/*
Given a Lie type, a sequence of high weights and an integer n > 1, returns
the traces of all elements of G of order n on the modules of these high
weights, where G is the simple algebraic group of type LIE_TYPE over
an alg. closed field of characteristic not dividing n.
*/

// Based on an algorithm described in https://doi.org/10.1137/0605037

LIE_TYPE := CartanName(RootDatum(LIE_TYPE));

DATUM := RootDatum(LIE_TYPE: Isogeny := "SC");
RANK := Rank(DATUM);
limit := AJL_MoodyPatera(LIE_TYPE,n)[n];
FUND_INDEX := #FundamentalGroup(DATUM);
if debug then printf "Looking for %o classes.\n",limit; end if;
if LIE_TYPE eq "G2" then MARKS := [3,2,1];
elif LIE_TYPE eq "F4" then MARKS := [2,3,4,2,1];
elif LIE_TYPE eq "E6" then MARKS := [1,2,2,3,2,1,1];
elif LIE_TYPE eq "E7" then MARKS := [2,2,3,4,3,2,1,1];
elif LIE_TYPE eq "E8" then MARKS := [2,3,4,6,5,4,3,2,1];
end if;

if LIE_TYPE eq "G2" then
    W := [&join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[0,0],[1,0]]],
        &join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[0,0]^^2,[1,0],[0,1]]]];
elif LIE_TYPE eq "F4" then
    W :=  [&join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[0,0,0,0]^^2,[0,0,0,1]] ],
        &join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[0,0,0,0]^^4,[0,0,0,1],[1,0,0,0]] ] ];
elif LIE_TYPE eq "E6" then
    W :=  [SetToMultiset(WeightOrbit(DATUM,[1,0,0,0,0,0])),
        &join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[0,1,0,0,0,0],[0,0,0,0,0,0]^^6]] ];
elif LIE_TYPE eq "E7" then
    W :=  [SetToMultiset(WeightOrbit(DATUM,[0,0,0,0,0,0,1])),
        &join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[1,0,0,0,0,0,0],[0,0,0,0,0,0,0]^^7]] ];
elif LIE_TYPE eq "E8" then
    W :=  [&join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1]^^7,[0,0,0,0,0,0,0,0]^^35] ],
        &join[SetToMultiset(WeightOrbit(DATUM,x)) : x in [[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0]^^8]]];
else
    "Error: Please give an exceptional Lie type.";
    return -1;
end if;

INV_CARTAN := GL(RANK,RationalField())!CartanMatrix(LIE_TYPE)^(-1);
W := [{* w*INV_CARTAN : w in v *} : v in W];
EIGS := {};

if LIE_TYPE in {"G2","F4","E8"} then MULTIPLIERS := [1];
elif LIE_TYPE eq "E6" then MULTIPLIERS := [1,3];
elif LIE_TYPE eq "E7" then MULTIPLIERS := [1,2];
end if;

OrderMult := function(s)
  if LIE_TYPE in {"G2","F4","E8"} then return 1;
  elif LIE_TYPE eq "E6" then return IntegerRing()!(3/Gcd(3,s[1]+s[5]-(s[3]+s[6])));
  elif LIE_TYPE eq "E7" then return IntegerRing()!(2/Gcd(2,s[2]+s[5]+s[7]));
  end if;
end function;

if debug then "Generating first approximation to search space..."; end if;
COEFF_TUPLES := CartesianProduct([[0..(n div MARKS[j])] : j in [1..RANK] ]);
if debug then "Done. First approximation:", #COEFF_TUPLES; "Generating second approximation..."; end if;
COEFF_TUPLES := { [j : j in i] cat [r] : r in {(n div M) - &+[i[j]*MARKS[j] : j in [1..RANK]] : M in MULTIPLIERS | n mod M eq 0} meet {0..n}, i in COEFF_TUPLES };
if debug then "Done. Unfiltered search space:", #COEFF_TUPLES; "Filtering by GCD check..."; end if;
COEFF_TUPLES := { i : i in COEFF_TUPLES | (Gcd(SequenceToSet(i)) eq 1)};
if debug then "Done. Current approximation:", #COEFF_TUPLES; "Generating final search space..."; end if;
COEFF_TUPLES := { i : i in COEFF_TUPLES | &+[i[j]*MARKS[j] : j in [1..RANK+1]]*OrderMult(i) eq n };
if debug then "Done. Final search space:", #COEFF_TUPLES; end if;

EIGS := {
    [{* [IntegerRing()!((OrderMult([i : i in C])*FUND_INDEX)*C[x]*RationalField()!j[x]) : x in [1..RANK] ] : j in W[i] *} : i in [1,2]]
    : C in COEFF_TUPLES
};

num := #EIGS;

if num lt limit then printf "***WARNING: Not all classes found: %o of %o.\n",num,limit; end if;
if num gt limit then printf "***Too many classes found! This doesn't make sense! %o of %o.\n",num,limit; end if;

return EIGS;

end function;



F4_trace_table := function(n)
    VAR := RootOfUnity(n);
    X := exelts_mp("F4",n : debug := true);
    X_traces := { [ [&+{* &*[VAR^Q : Q in q]^IntegerRing()!e : q in i*} : e in [n div j : j in Divisors(n) | not (j eq 1)] ] : i in x] : x in X};
    return X_traces;
end function;



F4_ELTS2 := F4_trace_table(2);
F4_ELTS3 := F4_trace_table(3);
F4_ELTS6 := F4_trace_table(6);
F4_ELTS7 := F4_trace_table(7);
F4_ELTS13 := F4_trace_table(13);
F4_ELTS14 := F4_trace_table(14);

print "Built F4 trace tables for orders 2, 3, 6, 7, 13, 14.";
print "Sizes:";
print <#F4_ELTS2, #F4_ELTS3, #F4_ELTS6, #F4_ELTS7, #F4_ELTS13, #F4_ELTS14>;
FeasChar := procedure(G,LIE_TYPE,CHAR_K : debug := false, MODULES := [], ADJOINT_MODULES := [], MINIMAL_MODULES := [], LIMITING_ORDER := 17, ELEMENT_ORDERS := []);

ASSIGNED_LETTERS := [<"G2","G2_ELTS",7,14>,<"F4","F4_ELTS",26,52>,<"E6","E6_ELTS",27,78>,<"E7","E7_ELTS",56,133>,<"E8","E8_ELTS",0,248>];

LIE_TYPE := CartanName(RootDatum(LIE_TYPE));

if not LIE_TYPE in [i[1] : i in ASSIGNED_LETTERS] then
    "Invalid Lie type!";
    return;
end if;

if not ((IntegerRing()!CHAR_K eq IntegerRing()!0) or (IsPrime(IntegerRing()!CHAR_K))) then
    "Invalid characteristic! Must be zero or prime.";
    return;
end if;

DIM_MIN := [i[3] : i in ASSIGNED_LETTERS | LIE_TYPE eq i[1]][1];
DIM_AD := [i[4] : i in ASSIGNED_LETTERS | LIE_TYPE eq i[1]][1];

if CHAR_K eq 0 then
    CHAR_K := 2;
    repeat
        CHAR_K := NextPrime(CHAR_K);
    until not (CHAR_K in PrimeDivisors(#G));
end if;

if debug then printf "Calculating conjugacy classes and power map of G... "; end if;
Clss := Classes(G);
p := PowerMap(G);

if (IsEmpty(ADJOINT_MODULES) xor IsEmpty(MINIMAL_MODULES)) then
    "Error: Either specify MODULES, or both ADJOINT_MODULES and MINIMAL_MODULES.";
    return;
end if;

if IsEmpty(ADJOINT_MODULES) and IsEmpty(MINIMAL_MODULES) then
    if IsEmpty(MODULES) then
        if debug then printf "Done.\nCalculating absolutely irreducible G-modules... "; end if;
        MODULES := AbsolutelyIrreducibleModules(G,GF(CHAR_K));
    end if;
    ADJOINT_MODULES := MODULES;
    MINIMAL_MODULES := MODULES;
    if debug then printf " Done.\n"; end if;
end if;

DIMS_AD := [Dimension(i) : i in ADJOINT_MODULES | Dimension(i) le DIM_AD];
DIMS_MIN := [Dimension(i) : i in MINIMAL_MODULES | Dimension(i) le DIM_MIN];

FIELD_OF_DEFINITION := MinimalField([ C[i][j] : i,j in [1..#C] ] ) where C := CharacterTable(G);

if debug then FIELD_OF_DEFINITION; end if;

MODULI_AD := DIMS_AD;
for i in [1..#MODULI_AD] do
  MODULI_AD[i] := Gcd([MODULI_AD[j] : j in [i..#MODULI_AD]]);
end for;
MODULI_MIN := DIMS_MIN;
for i in [1..#MODULI_MIN] do
  MODULI_MIN[i] := Gcd([ IntegerRing() | MODULI_MIN[j] : j in [i..#MODULI_MIN]]);
end for;

B_AD := [BrauerCharacter(i) : i in ADJOINT_MODULES | Dimension(i) le DIM_AD];
B_MIN := [BrauerCharacter(i) : i in MINIMAL_MODULES | Dimension(i) le DIM_MIN];
if debug then printf "Done.\n"; end if;

if IsEmpty(ELEMENT_ORDERS) then
  ELEMENT_ORDERS := [c[1] : c in Clss | (c[1] gt 1) and (Gcd(c[1],CHAR_K) eq 1)];
end if;
EXCESS_ELEMENT_ORDERS := Sort(SetToSequence({x : x in ELEMENT_ORDERS | x gt LIMITING_ORDER}),func<x,y | x - y>);
if #EXCESS_ELEMENT_ORDERS gt 0 then
  printf "*** WARNING: Elements of order(s) %o not used.\n",EXCESS_ELEMENT_ORDERS;
  ELEMENT_ORDERS := [x : x in ELEMENT_ORDERS | x le LIMITING_ORDER];
end if;

T := [* 0 : i in [1..Max(ELEMENT_ORDERS)] *]; on := [];
for n in ELEMENT_ORDERS do
    on[n] := [[p(i,n div j) : j in Divisors(n) | j gt 1 ] : i in [1..#Clss] | Clss[i][1] eq n];
    T[n] := eval (LIE_TYPE cat "_ELTS" cat IntegerToString(n));
end for;

D_AD := [[FIELD_OF_DEFINITION | i[j] : i in B_AD] : j in [1..#B_AD[1]]];
if not (LIE_TYPE eq "E8") then
    D_MIN := [[FIELD_OF_DEFINITION | i[j] : i in B_MIN] : j in [1..#B_MIN[1]]];
end if;

ELT_CHAR_ARRAY_AD := [<Clss[i][1],D_AD[i]> : i in [1..#Clss]];
COEFFS_AD := [IntegerRing() | x : x in ELT_CHAR_ARRAY_AD[1][2]];
if not (LIE_TYPE eq "E8") then
  ELT_CHAR_ARRAY_MIN := [<Clss[i][1],D_MIN[i]> : i in [1..#Clss]];
  COEFFS_MIN := [IntegerRing() | x : x in ELT_CHAR_ARRAY_MIN[1][2]];
end if;

index_tick := function(integer_array,coefficients,maximum_sum,MODULI);
  max_index := #integer_array;

  repeat
    current_index := max_index;

    repeat
      DIFF := maximum_sum-&+[ IntegerRing() | integer_array[i]*coefficients[i] : i in [1..current_index-1] ];

      if
        (DIFF mod MODULI[current_index] eq 0)
      and
        (integer_array[current_index] lt DIFF div coefficients[current_index])
      then
        integer_array[current_index] +:= 1;
        break;
      else
        integer_array[current_index] := 0;
        current_index -:= 1;
      end if;

    until (current_index eq 0);

    if debug and current_index eq 1 then printf "."; end if;

    if current_index eq 0 then
      return integer_array,true;
    end if;

  until IntegerRing()!(&+[coefficients[index]*integer_array[index] : index in [1..max_index]]) eq maximum_sum;

  return integer_array,false;
end function;

if debug then printf "Beginning main loop.\n"; end if;

printf "\\begin{tabular}{r|*{%o}{c}", #DIMS_AD;
if not (LIE_TYPE eq "E8") then printf "|*{%o}{c}", #DIMS_MIN; end if;
printf "}\n";

printf "& \\multicolumn{%o}{c}{$V_{%o}$}", #DIMS_AD, DIM_AD;
if not (LIE_TYPE eq "E8") then printf "& \\multicolumn{%o}{|c}{$V_{%o}$}", #DIMS_MIN, DIM_MIN; end if;
printf " \\\\ \\hline\n\t";

for i in DIMS_AD do printf "&%2o ", i; end for;
if not (LIE_TYPE eq "E8") then printf " "; for i in DIMS_MIN do printf "&%2o ", i; end for; end if;
printf "\\\\ \\hline\n";
print "%";

if LIE_TYPE eq "E8" then
    thingAd := [0 : i in [1..#B_AD]];
    done := false;
    num := 0;

    while not done do
        charAd := &+[B_AD[i]*thingAd[i] : i in [1..#B_AD]]; 

        if (&and[&and{[FIELD_OF_DEFINITION!charAd[i[j]] : j in [1..#i]] in T[n] : i in on[n] } : n in ELEMENT_ORDERS]) then
            num +:= 1;
            if num gt 1 then
                printf "\\\\\n";
            end if;
            printf "%2o)\t",num;
            for item in thingAd do printf "&%2o ", item; end for;
        end if;

        thingAd,done := index_tick(thingAd,COEFFS_AD,DIM_AD,MODULI_AD);
    end while;

else
    thingAd := [0 : i in [1..#B_AD]];
    thingMin := [0 : i in [1..#B_MIN]];

    doneAd := false;
    num := 0;

    while not doneAd do
        charAd := &+[B_AD[i]*thingAd[i] : i in [1..#B_AD]];

        if (DIM_AD eq charAd[1])
        and
            (&and[&and{[FIELD_OF_DEFINITION!charAd[i[j]] : j in [1..#i]] in [z[2] : z in T[n]] : i in on[n] } : n in ELEMENT_ORDERS]) then

            if debug then printf "\nAdjoint module possibility found.\n"; end if;

            doneMin := false;

            while not doneMin do
                charMin := &+[B_MIN[i]*thingMin[i] : i in [1..#thingMin]];

                if (charMin[1] eq DIM_MIN)
                and
                    (&and[&and{[[FIELD_OF_DEFINITION!charMin[i[j]] : j in [1..#i]],[charAd[i[j]] : j in [1..#i]]] in T[n] : i in on[n] } : n in ELEMENT_ORDERS]) then

                    num +:= 1;
                    if num gt 1 then printf "\\\\\n"; end if;
                    printf "%2o)\t",num;
                    for item in thingAd do printf "&%2o ", item; end for;
                    printf " ";
                    for item in thingMin do printf "&%2o ", item; end for;
                end if;

                thingMin,doneMin := index_tick(thingMin,COEFFS_MIN,DIM_MIN,MODULI_MIN);
            end while;
        end if;

        thingAd,doneAd := index_tick(thingAd,COEFFS_AD,DIM_AD,MODULI_AD);
    end while;
end if;

if num gt 0 then printf " \\\\ \\hline\n\\end{tabular}"; end if;

end procedure;


H := PSL(2,13);

I := AbsolutelyIrreducibleModules(H, GF(5));
J := [ M : M in I | Dimension(M) gt 1 ];

FeasChar(H, "F4", 5 : MODULES := I);
