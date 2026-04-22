// Step 1: Constructing the local subgroup 13:6 inside L2(13)

H := PSL(2,13);
print "Order of H:", Order(H);

// Step 1: choose g of order 13
elts13 := [ x : x in H | Order(x) eq 13 ];
print "Number of elements of order 13:", #elts13;

g := elts13[1];
print "Order of g:", Order(g);

// Step 2: form P = <g>
P := sub< H | g >;
print "Order of P=<g>:", Order(P);

// Step 3: compute the normaliser of P in H
NH := Normalizer(H, P);
print "Order of N_H(P):", Order(NH);

// Step 4: find order 6 elements inside N_H(P)
elts6_in_NH := [ x : x in NH | Order(x) eq 6 ];
print "Number of order 6 elements in N_H(P):", #elts6_in_NH;

f := elts6_in_NH[1];
print "Order of f:", Order(f);

// Step 5: check that f normalises <g>
print "Does f send g into <g>?";
print f*g*f^-1 in P;

P2 := sub< H | f*g*f^-1 >;
print "Does f normalise <g>?";
print P2 eq P;

// Step 6: check that <g,f> gives the whole normaliser
B := sub< H | g, f >;
print "Order of <g,f>:", Order(B);
print "Is <g,f> equal to N_H(P)?", B eq NH;

// Step 7: find the power a such that f g f^-1 = g^a
for a in [1..12] do
    if f*g*f^-1 eq g^a then
        print "f g f^-1 = g^", a;
        print "Order of a in (Z/13Z)^*:", Order(Integers(13)!a);
    end if;
end for;

// Step 8: final summary
print "Summary:";
print "H = PSL(2,13)";
print "|H| =", Order(H);
print "|<g>| =", Order(P);
print "|N_H(<g>)| =", Order(NH);
print "|<g,f>| =", Order(B);
print "<g,f> = N_H(<g>)?", B eq NH;
