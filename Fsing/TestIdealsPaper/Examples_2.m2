------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

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

S = ZZ/3[a..f,x,y];
G = a*x^5 + b*x^4*y + c*x^3*y^2 + d*x^2*y^3 + e*x*y^4 + f*y^5;
testIdeal(t, G)
testIdeal(t - 1/p^5, G)

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
A = image matrix entries relations source E2;
frobeniusRoot(1, image U)

B = ascendModule(1, A, U)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/7[x,y,z]/(x^3 + y^3 + z^3);
isFInjective R
R = ZZ/5[x,y,z]/(x^3 + y^3 + z^3);
isFInjective R

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/7[x,y,z]/((x - 1)^5 + (y + 1)^5 + z^5);
isFInjective R -- R is not globally F-injective...
isFInjective(R, IsLocal => true) -- but is F-injective at the origin

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/5[x,y,z]/(x^2 + y*z);
isFRegular R
R = ZZ/7[x,y,z]/(x^3 + y^3 + z^3);
isFRegular R

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/5[x,y];
f = y^2 - x^3;
isFRegular(1/2, f)
isFRegular(5/6, f)
isFRegular(4/5, f)
isFRegular(4/5 - 1/100000, f)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/7[x,y,z]/((x - 1)^3 + (y + 1)^3 + z^3);
isFRegular R -- R is not globally F-regular...
isFRegular(R, IsLocal => true) -- but is F-regular at the origin
R = ZZ/13[x,y];
f = (y - 2)^2 - (x - 3)^3;
isFRegular(5/6, f) -- (R,f^(5/6)) is not F-regular...
isFRegular(5/6, f, IsLocal => true) -- but is F-regular at the origin

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/5[x,y,z]/(x^2 + y*z);
isFPure R
R = ZZ/7[x,y,z]/(x^3 + y^3 + z^3);
isFPure R
S = ZZ/2[x,y,z];
isFPure ideal(y^2 - x^3)
isFPure ideal(z^2 - x*y*z + x*y^2 + x^2*y)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

S = ZZ/3[a,b,c,d,t];
M = matrix{{ a^2 + t^4, b, d }, { c, a^2, b^3 - d }};
I = minors(2, M);
R = S/I;
isFRational R

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/5[x,y,z]/(x^4 + y^4 + z^4);
N = testModule R;
N#0
N#1

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/5[x,y,z]/(y*z, x*z, x*y);
N = testModule R;
N#0
N#1

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

R = ZZ/2[a..e];
E = matrix {{a, b, b, e}, {d, d, c, a}};
I = minors(2, E);
S = R/I;
J = parameterTestIdeal S
J = substitute(J, R);
mingens(J + I)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

T = ZZ/7[x,y];
S = ZZ/7[a,b,c,d];
f = map(T, S, {x^3, x^2*y, x*y^2, y^3});
I = ker f;
R = S/I;
testIdeal R

toString QGorensteinGenerator(1, R)

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

------------------------------------------------------------------------------------------
restart; 
loadPackage "TestIdeals"

