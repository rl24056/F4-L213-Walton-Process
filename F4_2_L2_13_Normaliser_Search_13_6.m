////////////////////////////////////////////////////////////
// STEP 5: Search for the 13:6 step inside F4(2)
////////////////////////////////////////////////////////////

K := GF(2);

Gq := ChevalleyGroup("F", 4, K);

print "Order of Gq =", Order(Gq);

S := SylowSubgroup(Gq, 13);
print "Order of Sylow 13-subgroup S =", Order(S);

g := S.1;

if Order(g) ne 13 then
    repeat
        g := Random(S);
    until Order(g) eq 13;
end if;

print "Order of g =", Order(g);

Cg := Centralizer(Gq, g);
CgS := Centralizer(Gq, S);
NgS := Normalizer(Gq, S);

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


ActionExponent := function(x,g)

    for a in [1..12] do
        if x*g*x^-1 eq g^a then
            return a;
        end if;
    end for;

    return 0;

end function;


print "======================================================";
print "Random search for f of order 6 in N_G(S)";
print "======================================================";

RP := RandomProcess(NgS);

found := false;
f := Identity(Gq);
a := 0;

for i in [1..10000] do

    x := Random(RP);

    if Order(x) eq 6 then

        aa := ActionExponent(x,g);

        if aa ne 0 then

            if MultOrderMod13(aa) eq 6 then
                found := true;
                f := x;
                a := aa;
                break;
            end if;

        end if;

    end if;

end for;


if found then

    print "Found f directly in N_G(S).";
    print "Order of f =", Order(f);
    print "Action exponent a with f*g*f^-1 = g^a:";
    print a;
    print "Multiplicative order of a modulo 13:";
    print MultOrderMod13(a);

    B := sub< Gq | g, f >;
    print "Order of <g,f> =", Order(B);

else

    print "No suitable order 6 element found directly.";
    print "Trying order 12 elements and squaring them.";

    found12 := false;
    x12 := Identity(Gq);
    a12 := 0;

    for i in [1..10000] do

        x := Random(RP);

        if Order(x) eq 12 then

            aa := ActionExponent(x,g);

            if aa ne 0 then

                if MultOrderMod13(aa) eq 12 then
                    found12 := true;
                    x12 := x;
                    a12 := aa;
                    break;
                end if;

            end if;

        end if;

    end for;

    if found12 then

        print "Found x of order 12 in N_G(S).";
        print "Order of x =", Order(x12);
        print "Action exponent of x:";
        print a12;
        print "Multiplicative order of this exponent modulo 13:";
        print MultOrderMod13(a12);

        f := x12^2;
        a := ActionExponent(f,g);

        print "Set f = x^2.";
        print "Order of f =", Order(f);
        print "Action exponent a with f*g*f^-1 = g^a:";
        print a;
        print "Multiplicative order of a modulo 13:";
        print MultOrderMod13(a);

        B := sub< Gq | g, f >;
        print "Order of <g,f> =", Order(B);

        if Order(f) eq 6 and MultOrderMod13(a) eq 6 and Order(B) eq 78 then
            found := true;
        end if;

    else

        print "No suitable order 12 element found either.";

    end if;

end if;


print "======================================================";
print "Extra search inside N_G(C_G(g))";
print "======================================================";

NgC := Normalizer(Gq, Cg);

print "Order of N_G(C_G(g)) =", Order(NgC);

RPC := RandomProcess(NgC);

foundC := false;
f2 := Identity(Gq);
a2 := 0;

for i in [1..10000] do

    x := Random(RPC);

    if Order(x) eq 6 then

        aa := ActionExponent(x,g);

        if aa ne 0 then

            if MultOrderMod13(aa) eq 6 then
                foundC := true;
                f2 := x;
                a2 := aa;
                break;
            end if;

        end if;

    end if;

end for;


if foundC then

    print "Found f2 of order 6 in N_G(C_G(g)).";
    print "Order of f2 =", Order(f2);
    print "Action exponent a2 with f2*g*f2^-1 = g^a2:";
    print a2;
    print "Multiplicative order of a2 modulo 13:";
    print MultOrderMod13(a2);

    B2 := sub< Gq | g, f2 >;
    print "Order of <g,f2> =", Order(B2);

else

    print "No suitable order 6 element found in N_G(C_G(g)).";
    print "Trying order 12 elements in N_G(C_G(g)).";

    foundC12 := false;
    xC12 := Identity(Gq);
    aC12 := 0;

    for i in [1..10000] do

        x := Random(RPC);

        if Order(x) eq 12 then

            aa := ActionExponent(x,g);

            if aa ne 0 then

                if MultOrderMod13(aa) eq 12 then
                    foundC12 := true;
                    xC12 := x;
                    aC12 := aa;
                    break;
                end if;

            end if;

        end if;

    end for;

    if foundC12 then

        print "Found x of order 12 in N_G(C_G(g)).";
        print "Order of x =", Order(xC12);
        print "Action exponent of x:";
        print aC12;
        print "Multiplicative order of this exponent modulo 13:";
        print MultOrderMod13(aC12);

        f2 := xC12^2;
        a2 := ActionExponent(f2,g);

        print "Set f2 = x^2.";
        print "Order of f2 =", Order(f2);
        print "Action exponent a2 with f2*g*f2^-1 = g^a2:";
        print a2;
        print "Multiplicative order of a2 modulo 13:";
        print MultOrderMod13(a2);

        B2 := sub< Gq | g, f2 >;
        print "Order of <g,f2> =", Order(B2);

        if Order(f2) eq 6 and MultOrderMod13(a2) eq 6 and Order(B2) eq 78 then
            foundC := true;
        end if;

    else

        print "No suitable order 12 element found in N_G(C_G(g)).";

    end if;

end if;


print "======================================================";
print "Step 5 summary";
print "======================================================";

print "Order of Gq =", Order(Gq);
print "Order of S =", Order(S);
print "Order of g =", Order(g);
print "Order of C_G(g) =", Order(Cg);
print "Order of C_G(S) =", Order(CgS);
print "Order of N_G(S) =", Order(NgS);
print "Index [N_G(S):C_G(S)] =", Order(NgS) div Order(CgS);
print "Order of N_G(C_G(g)) =", Order(NgC);

if f ne Identity(Gq) then
    print "Candidate from N_G(S):";
    print "Order of f =", Order(f);
    print "Action exponent =", a;
    print "Multiplicative order of exponent modulo 13 =", MultOrderMod13(a);
    B := sub< Gq | g, f >;
    print "Order of <g,f> =", Order(B);
end if;

if f2 ne Identity(Gq) then
    print "Candidate from N_G(C_G(g)):";
    print "Order of f2 =", Order(f2);
    print "Action exponent =", a2;
    print "Multiplicative order of exponent modulo 13 =", MultOrderMod13(a2);
    B2 := sub< Gq | g, f2 >;
    print "Order of <g,f2> =", Order(B2);
end if;

if f ne Identity(Gq) or f2 ne Identity(Gq) then
    print "A candidate order-6 element acting on <g> was found.";
else
    print "No candidate order-6 element found yet by random search.";
end if;

print "======================================================";
