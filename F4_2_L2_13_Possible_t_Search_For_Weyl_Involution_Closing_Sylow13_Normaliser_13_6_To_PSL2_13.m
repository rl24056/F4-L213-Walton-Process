SetVerbose("GrpMat", 1);

TEST_ALL_F := true;
PRINT_EACH_T := false;
STOP_AFTER_FIRST_GOOD_T := false;

K := GF(2);
G := ChevalleyGroup("F", 4, K);

print "======================================================";
print "SETUP";
print "======================================================";

print "Order of G = F4(2) =", Order(G);

S := SylowSubgroup(G, 13);

print "Order of Sylow 13-subgroup S =", Order(S);

g := S.1;

if Order(g) ne 13 then
    repeat
        g := Random(S);
    until Order(g) eq 13;
end if;

print "Order of g =", Order(g);

Cg := Centralizer(G, g);
CgS := Centralizer(G, S);
NgS := Normalizer(G, S);

print "Order of C_G(g) =", Order(Cg);
print "Order of C_G(S) =", Order(CgS);
print "Order of N_G(S) =", Order(NgS);
print "Index [N_G(S):C_G(S)] =", Order(NgS) div Order(CgS);

MultOrderMod13 := function(a)

    R := Integers(13);
    aa := R!a;

    if aa eq R!0 then
        return 0;
    end if;

    for k in [1..12] do
        if aa^k eq R!1 then
            return k;
        end if;
    end for;

    return 0;

end function;


ActionExponent := function(x, g)

    for a in [1..12] do
        if x*g*x^-1 eq g^a then
            return a;
        end if;
    end for;

    return 0;

end function;


NormalisesGSubgroup := function(x, g)

    return ActionExponent(x,g) ne 0;

end function;


InvertsF := function(x, f)

    return x*f*x^-1 eq f^-1;

end function;


MovesGOutsideItsOwn13Subgroup := function(x, g)

    return ActionExponent(x,g) eq 0;

end function;

print "======================================================";
print "STEP 1: FIND SUITABLE ORDER-6 ELEMENTS f IN N_G(S)";
print "======================================================";

NgSElems := [ x : x in NgS ];

GoodFs := [];
GoodFData := [];

for x in NgSElems do

    if Order(x) eq 6 then

        a := ActionExponent(x,g);

        if a ne 0 and MultOrderMod13(a) eq 6 then

            B := sub< G | g, x >;

            if Order(B) eq 78 then
                Append(~GoodFs, x);
                Append(~GoodFData, <x, a, Order(B)>);
            end if;

        end if;

    end if;

end for;

print "Number of suitable order-6 elements f =", #GoodFs;

Exponents := { data[2] : data in GoodFData };

print "Action exponents found for f*g*f^-1 = g^a:";
print Exponents;

for a in Exponents do
    print "Exponent", a, "has multiplicative order", MultOrderMod13(a), "modulo 13";
end for;

GoodFSubgroups := [];
GoodFGenerators := [];

for f in GoodFs do

    F := sub< G | f >;

    already := false;

    for U in GoodFSubgroups do
        if F eq U then
            already := true;
            break;
        end if;
    end for;

    if not already then
        Append(~GoodFSubgroups, F);
        Append(~GoodFGenerators, f);
    end if;

end for;

print "Number of distinct cyclic order-6 subgroups <f> =", #GoodFSubgroups;

if #GoodFs eq 0 then
    error "No suitable f found. Cannot continue.";
end if;

FsToTest := [];

if TEST_ALL_F then
    FsToTest := GoodFs;
else
    FsToTest := [ GoodFs[1] ];
end if;

print "Number of f-elements selected for t-search =", #FsToTest;

Hstd := PSL(2,13);
OrderHstd := Order(Hstd);

print "Order of PSL(2,13) =", OrderHstd;

print "======================================================";
print "STEP 2: SEARCH FOR WEYL-TYPE INVOLUTIONS t";
print "======================================================";

AllGoodTriples := [];
AllOrdersFound := {};
AllCandidateCounts := [];
AllNormalisingCandidateCounts := [];

TotalCandidates := 0;
TotalNormalisingCandidates := 0;
TotalTested := 0;

for fi in [1..#FsToTest] do

    f := FsToTest[fi];
    a := ActionExponent(f,g);

    B := sub< G | g, f >;
    F := sub< G | f >;

    print "------------------------------------------------------";
    print "Testing f number", fi;
    print "Order of f =", Order(f);
    print "Action exponent of f on <g> =", a;
    print "Multiplicative order of exponent =", MultOrderMod13(a);
    print "Order of <g,f> =", Order(B);

    Nf := Normalizer(G, F);

    print "Order of <f> =", Order(F);
    print "Order of N_G(<f>) =", Order(Nf);

    CandidateTs := [];
    NormalisingTs := [];

    for x in Nf do

        if Order(x) eq 2 and InvertsF(x,f) then

            if MovesGOutsideItsOwn13Subgroup(x,g) then
                Append(~CandidateTs, x);
            else
                Append(~NormalisingTs, x);
            end if;

        end if;

    end for;

    Append(~AllCandidateCounts, #CandidateTs);
    Append(~AllNormalisingCandidateCounts, #NormalisingTs);

    TotalCandidates +:= #CandidateTs;
    TotalNormalisingCandidates +:= #NormalisingTs;

    print "Number of candidate t with t*f*t^-1 = f^-1 and t not normalising <g> =", #CandidateTs;
    print "Number of inverting involutions t which still normalise <g> =", #NormalisingTs;

    OrdersFoundForThisF := {};
    IntersectionsFoundForThisF := {};

    for ti in [1..#CandidateTs] do

        t := CandidateTs[ti];

        gImage := t*g*t^-1;
        SImage := sub< G | gImage >;

        H := sub< G | g, f, t >;
        ordH := Order(H);

        TotalTested +:= 1;

        Include(~OrdersFoundForThisF, ordH);
        Include(~AllOrdersFound, ordH);
        Include(~IntersectionsFoundForThisF, Order(S meet SImage));

        if PRINT_EACH_T then
            print "Candidate t number", ti;
            print "Order of t =", Order(t);
            print "t inverts f? ", InvertsF(t,f);
            print "t normalises <g>? ", NormalisesGSubgroup(t,g);
            print "Order of <t*g*t^-1> =", Order(SImage);
            print "<t*g*t^-1> equals <g>? ", SImage eq S;
            print "Order of <g> meet <t*g*t^-1> =", Order(S meet SImage);
            print "Order of <g,f,t> =", ordH;
        end if;

        if ordH eq OrderHstd then

            print "Possible good t found for f number", fi, "and t number", ti;
            print "Order of <g,f,t> =", ordH;

            iso := IsIsomorphic(H, Hstd);

            print "IsIsomorphic(<g,f,t>, PSL(2,13)) =", iso;

            if iso then
                Append(~AllGoodTriples, <fi, ti, f, t, H>);
                print "SUCCESS: This t gives a subgroup isomorphic to PSL(2,13).";

                if STOP_AFTER_FIRST_GOOD_T then
                    print "Stopping after first good t, as requested.";
                    break;
                end if;
            end if;

        end if;

    end for;

    print "Different orders of <g,f,t> found for this f:";
    print OrdersFoundForThisF;

    print "Different intersection sizes |<g> meet <t*g*t^-1>| for this f:";
    print IntersectionsFoundForThisF;

    if STOP_AFTER_FIRST_GOOD_T and #AllGoodTriples gt 0 then
        break;
    end if;

end for;

print "======================================================";
print "FINAL SUMMARY";
print "======================================================";

print "Order of G = F4(2) =", Order(G);
print "Order of g =", Order(g);
print "Order of C_G(g) =", Order(Cg);
print "Order of C_G(S) =", Order(CgS);
print "Order of N_G(S) =", Order(NgS);
print "Index [N_G(S):C_G(S)] =", Order(NgS) div Order(CgS);

print "Number of suitable f-elements found =", #GoodFs;
print "Number of distinct cyclic subgroups <f> found =", #GoodFSubgroups;
print "Action exponents for suitable f-elements:";
print Exponents;

print "Number of f-elements tested =", #FsToTest;

print "Candidate t counts for each f:";
print AllCandidateCounts;

print "Normalising inverting-t counts for each f:";
print AllNormalisingCandidateCounts;

print "Total candidate t tested =", TotalTested;
print "Total non-normalising candidate t found =", TotalCandidates;
print "Total normalising inverting t found =", TotalNormalisingCandidates;

print "Different orders of <g,f,t> found overall:";
print AllOrdersFound;

print "Number of good triples <g,f,t> giving PSL(2,13) =", #AllGoodTriples;

if #AllGoodTriples gt 0 then

    data := AllGoodTriples[1];

    good_f_index := data[1];
    good_t_index := data[2];
    good_f := data[3];
    good_t := data[4];
    good_H := data[5];

    print "------------------------------------------------------";
    print "FIRST GOOD TRIPLE";
    print "------------------------------------------------------";

    print "Good f index =", good_f_index;
    print "Good t index =", good_t_index;

    print "Order of good f =", Order(good_f);
    print "Action exponent of good f on <g> =", ActionExponent(good_f,g);
    print "Multiplicative order of exponent =", MultOrderMod13(ActionExponent(good_f,g));

    print "Order of good t =", Order(good_t);
    print "good t inverts good f? ", InvertsF(good_t, good_f);
    print "good t normalises <g>? ", NormalisesGSubgroup(good_t,g);

    gImage := good_t*g*good_t^-1;
    SImage := sub< G | gImage >;

    print "Order of <good_t*g*good_t^-1> =", Order(SImage);
    print "<good_t*g*good_t^-1> equals <g>? ", SImage eq S;
    print "Order of <g> meet <good_t*g*good_t^-1> =", Order(S meet SImage);

    print "Order of <g, good_f> =", Order(sub< G | g, good_f >);
    print "Order of <g, good_f, good_t> =", Order(good_H);
    print "IsIsomorphic(<g, good_f, good_t>, PSL(2,13)) =", IsIsomorphic(good_H, Hstd);

else

    print "No t satisfying the tested Weyl-type conditions gave PSL(2,13).";
    print "Further search may need additional relations, a different finite field model, or a more direct construction.";

end if;

print "======================================================";
print "END";
print "======================================================";
