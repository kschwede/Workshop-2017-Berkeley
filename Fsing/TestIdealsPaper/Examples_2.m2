restart; 
uninstallPackage "TestIdeals"
installPackage "TestIdeals"
loadPackage "TestIdeals"
viewHelp "TestIdeals"

------------------------------------------------------------------------------------------
R = ZZ/5[x,y,z];
I = ideal(x^6*y*z + x^2*y^12*z^3 + x*y*z^18);
frobeniusPower(1/5, I)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals";

S = ZZ/5[x,y,z];
f = x^3 + y^3 + z^3;
u = f^(5-1);
frobeniusRoot(1, ideal u)
S = ZZ/7[x,y,z];
f = x^3 + y^3 + z^3;
u = f^(7-1);
frobeniusRoot(1, ideal u)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"
p = 3;
R = ZZ/p[x,y];
m = monomialIdeal(x, y);
I = m^5;
t = 3/5 - 1/(5*p^3);
frobeniusPower(t, I)
frobeniusPower(t - 1/p^5, I)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"
R = ZZ/2[a,b,c,d];
I = intersect(ideal(a, b),ideal(a, c),ideal(c, d),ideal(c + d, a^3 + b*d^2));
f = inducedMap(R^1/I, R^1/frobenius(I));
E2 = Ext^2(f, R^1)
target E2
source E2

U = matrix entries E2;
A = matrix entries relations source E2;
frobeniusRoot(1, U)

V = ascendModule(1, A, U)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"


S = ZZ/3[a..f,x,y];
G = a*x^5 + b*x^4*y + c*x^3*y^2 + d*x^2*y^3 + e*x*y^4 + f*y^5;
testIdeal(t, G)
testIdeal(t - 1/p^5, G)




R = ZZ/3[u,v];

u = u^2*v^2;

compatibleIdeals(u)



restart;

p=2;
m=5;
R=ZZ/pp[x_1..x_m]; 
E=matrix {{x_1,x_2,x_2,x_5},{x_4,x_4,x_3,x_1}};
I=minors(2,E);
I=gens I;
u=x_1^3*x_2*x_3 + x_1^3*x_2*x_4+x_1^2*x_3*x_4*x_5+ x_1*x_2*x_3*x_4*x_5+ x_1*x_2*x_4^2*x_5+ x_2^2*x_4^2*x_5+x_3*x_4^2*x_5^2+ x_4^3*x_5^2;


restart; 
loadPackage "TestIdeals"

R=ZZ/2[x_1..x_5]; 
E=matrix {{x_1,x_2,x_2,x_5},{x_4,x_4,x_3,x_1}};
I=minors(2,E);
J=parameterTestIdeal(R/I)
J=substitute(J,R);
mingens(J+I)

omega=canonicalIdeal(R/I)
omega=substitute(omega,R)+I
u1=(frobeniusPower(2,I)):I;
u2=(frobeniusPower(2,omega)):omega;
u=intersect(u1,u2)
u=first first entries mingens u




restart; 
loadPackage "TestIdeals"
p=2;
R=ZZ/p[a,b,c,d]
I=intersect( ideal(a,b), ideal(a,c), ideal(c,d), ideal(c+d, a^3+b*d^2))
J=parameterTestIdeal(R/I)
J=substitute(J,R);
mingens(I+J)



restart;

p=11;
m=5;
R=ZZ/p[x,y,z]; 
u=7*x^(3+11^2)



e=1
L1=apply(exponents(u),exponent->{coefficient(R_exponent,u)*R_(exponent //p^e),exponent%p^e})





restart; 
loadPackage "TestIdeals"

printWidth=80

R=ZZ/2[x_1..x_5]; 
E=matrix {{x_1,x_2,x_2,x_5},{x_4,x_4,x_3,x_1}};
I=minors(2,E);

isCohenMacaulay(R/I)

omega=canonicalIdeal(R/I)
omega=substitute(omega,R)+I;
u=intersect((frobeniusPower(2,I)):I,(frobeniusPower(2,omega)):omega);
u=compress((gens u)%(gens(frobeniusPower(2,I))));
u=first first entries  u
L=compatibleIdeals(u)
unique apply(L, J-> (J:omega))



restart; 
loadPackage "TestIdeals"

p=3
F = GF(p^2,Variable=>a)
R=F[x,y,z]
I=ideal(a^(2*p)*x^p+y*z^p+x^p*y^p)
frobeniusRoot(1,I)

frobeniusPower(1/p,I)



-----------------------------------------------------------------------------------------------

restart; 
loadPackage "TestIdeals"

printWidth=80
p=2;
R=ZZ/p[x_1..x_5]; 
E=matrix {{x_1,x_2,x_2,x_5},{x_4,x_4,x_3,x_1}};
I=minors(2,E);

dim coker gens I

codim I

f=inducedMap (coker gens I, coker gens frobeniusPower(p,I) );
resf=res f
G=Hom(resf, R^1)
E3=HH^3 G

U=matrix entries E3
A=matrix entries relations source E3
frobeniusRoot(1,U)














-----------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"
p=2;
R=ZZ/p[a,b,c,d];
I=intersect( ideal(a,b), ideal(a,c), ideal(c,d), ideal(c+d, a^3+b*d^2));


f=inducedMap (coker gens I, coker gens frobeniusPower(p,I) );
resf=res f
G=Hom(resf, R^1)
E2=HH^2 G

U=matrix entries E2
A=matrix entries relations source E2
frobeniusRoot(1,U)

V=ascendModule (1,A,U) 



----------------------------------------------------------------------------------