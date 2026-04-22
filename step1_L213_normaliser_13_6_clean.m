H := PSL(2,13);
print "Order of H:", Order(H);

print "Conjugacy class data:";
for c in Classes(H) do
    print "Order:", c[1], "Size:", c[2];
end for;

elts13 := [ x : x in H | Order(x) eq 13 ];
print "Number of elements of order 13:", #elts13;

g := elts13[1];
print "Order of g:", Order(g);

P := sub< H | g >;
print "Order of <g>:", Order(P);

NH := Normalizer(H,P);
print "Order of N_H(<g>):", Order(NH);

elts6 := [ x : x in NH | Order(x) eq 6 ];
print "Number of elements of order 6 in N_H(<g>):", #elts6;

f := elts6[1];
print "Order of f:", Order(f);

B := sub< H | g, f >;
print "Order of <g,f>:", Order(B);
print "<g,f> equals N_H(<g>):", B eq NH;

for a in [1..12] do
    if f*g*f^-1 eq g^a then
        print "f acts by power", a;
        print "Order of this power in (Z/13Z)^*:", Order(Integers(13)!a);
    end if;
end for;
