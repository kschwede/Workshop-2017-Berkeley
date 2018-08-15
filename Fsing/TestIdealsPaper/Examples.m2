restart; 
loadPackage "TestIdeals"

R=ZZ/5[x,y,z]
I=ideal(x^6*y*z+x^2*y^12*z^3+x*y*z^18)
frobeniusPower(1/5,I)

frobeniusPower(1/2, ideal(y^2-x^3))
frobeniusPower(5/6, ideal(y^2-x^3))

restart; 
loadPackage "TestIdeals";


R=ZZ/5[x,y,z]

g=x^3+y^3+z^3
u=g^(5-1)

frobeniusPower(1/5,ideal(u))


R=ZZ/7[x,y,z]

g=x^3+y^3+z^3
u=g^(7-1)

frobeniusPower(1/7,ideal(u))

restart; 
loadPackage "TestIdeals"

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