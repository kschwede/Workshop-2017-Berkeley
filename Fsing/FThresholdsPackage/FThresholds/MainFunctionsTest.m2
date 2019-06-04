-- tests for fpt computations that call special algorithms

--Below, we verify computations for a binomial from Example 4.3-4.5 in
--"F-pure thresholds of binomial hypersurfaces" by D. Hernandez.
--In each case, fpt is as computed in SpecialFThresholdTest.m2
--and nu's are read off from this.
--binomial test 1
TEST ///
ZZ/47[x,y];
f= x^7*y^2 + x^5*y^6;
assert(fpt(f)==3/16)
assert(nu(1,f)==8)
assert(nu(2,f)==414)
assert(nu(3,f)==19466)
assert(nu(3,f, UseSpecialAlgorithms => false)==19466)
assert(nu(3,f, UseSpecialAlgorithms => false, Search=>Linear)==19466)
///

--binomial test 2
TEST ///
ZZ/43[x,y];
f= x^7*y^2 + x^5*y^6;
assert(fpt(f)==8/43)
assert(nu(1,f)==7)
assert(nu(2,f)==343)
assert(nu(3,f)==14791)
assert(nu(3,f, UseSpecialAlgorithms => false)==14791)
assert(nu(3,f, UseSpecialAlgorithms => false, Search=>Linear)==14791)
///

--binomial test 3
TEST ///
ZZ/37[x,y];
f= x^7*y^2 + x^5*y^6;
assert(nu(1,f)==6)
assert(nu(2,f)==256)
assert(nu(3,f)==9494)
assert(nu(3,f, UseSpecialAlgorithms => false)==9494)
assert(nu(3,f, UseSpecialAlgorithms => false, Search=>Linear)==9494)
///

-- tests for fpt computations that call special algorithms

--diagonalFPT test 1
TEST ///
ZZ/5[x,y,z];
f = x^3+y^2;
g = x^3+y^4+z^5;
assert(fpt(f)==4/5)
assert(fpt(g)==3/5)
///

--diagonalFPT test 2
TEST ///
ZZ/11[x,y,z];
f = x^3+y^2;
g = x^3+y^4+z^5;
assert(fpt(f)==9/11)
assert(fpt(g)==8/11)
///

--diagonalFPT test 3
TEST ///
ZZ/13[x,y,z];
f = x^3+y^2;
g = x^3+y^4+z^5;
assert(fpt(f)==5/6)
assert(fpt(g)==10/13)
///

-- binaryFormFPT test 1
-- These values were tested with isFPT
TEST ///
R = ZZ/2[x,y]
assert( fpt( x ) == 1 )
assert( fpt( x^10*y^15 ) == 1/15 )
assert( fpt( x^10*y^3+x^9*y^4+x^6*y^7+x^4*y^9+x^3*y^10+x*y^12+y^13 ) == 315/2048 )
assert( fpt( x^10*y+x^9*y^2+x^8*y^3+x^7*y^4+x^4*y^7+x^3*y^8+x*y^10 ) == 93/512 )
assert( fpt( x^10+x^8*y^2+x^5*y^5+x^4*y^6+x^3*y^7 ) == 1/5 )
///

-- binaryFormFPT test 2
-- These values were tested with isFPT
TEST ///
R = ZZ/31[x,y]
L = { x, y, x+3*y, x+10*y }
assert( fpt( L, { 3, 6, 6, 10 } ) == 221645/2770563 )
assert( fpt( L, { 5, 17, 20, 11 } ) == 160922837253/4264455187205 )
assert( fpt( L, { 5, 12, 8, 11 } ) == 1/18 )
assert( fpt( L, { 19, 14, 17, 18 } ) == 14198854736226229/482761061031691789 )
assert( fpt( L, { 17, 10, 17, 20 } ) == 1/32 )
///

-- binaryFormFPT test 3
-- These values were tested by running the exact algorithm from "F-threshold
-- functions" semi-manually
TEST ///
kk = GF( ZZ/5[a]/ideal( a^3+a+1 ) )
R = kk[x,y]
L = { x, y, x+y, x-y, x+a*y, x+a^2*y }
assert( fpt( L, { 4, 19, 2, 11, 5, 20 } ) == 30535166380835361168/931322574615478515625 )
assert( fpt( L, { 22, 76, 46, 30, 92, 88 } ) == 18466082398285089576311704129149/3268496584496460855007171630859375 )
assert( fpt( L, {420, 419, 417, 390, 402, 438} ) == 46636216675556057485911762783799675605705641779512143/57968817327716179454988321140262996777892112731933593750 )
assert( fpt( L, { 3, 32, 2, 32, 73, 84 } ) == 18765116046319289672094923747611764472226361925425255193119555448/2120458113234079732946726383480129385361578897573053836822509765625 )
///

--------------------------------------------------------------
--Below, our computations are based on results in the paper
--"Frobenius Powers of some monomial ideals" by Hernandez, Teixeira, Witt
TEST ///
ZZ/5[x,y];
M=ideal(x,y);
D=ideal(x^3,y^3);
assert(nu(1,M^3,M, ContainmentTest => FrobeniusPower)== 2)
assert(nu(2,M^3,M, ContainmentTest => FrobeniusPower) == 14)
assert(nu(1,D,M, ContainmentTest => FrobeniusPower) == 2)
assert(nu(2,D,M, ContainmentTest => FrobeniusPower) == 14)
///

TEST ///
ZZ/7[x,y];
M=ideal(x,y);
D=ideal(x^4,y^4);
I=ideal(x^2,y);
f=x^4+y^4; -- generic element of D
g=x^4+x^3*y+x^2*y^2+x*y^3+y^4; -- generic element of M^4
assert(nu(1,M^4,I,ContainmentTest => FrobeniusPower)==4 )
assert(nu(2,M^4,I, ContainmentTest => FrobeniusPower)== 34)
assert(nu(1,D,I, ContainmentTest => FrobeniusPower)== 4)
assert(nu(2,D,I, ContainmentTest => FrobeniusPower)== 34)
assert(nu(1,f,I)==4)
assert(nu(2,f,I)==34)
assert(nu(1,g,I)==4)
assert(nu(2,g,I)==34)
///

--Here, we test F-pure threshold approximation computations for polynomials
TEST ///
ZZ/5[x,y,z];
f = 2*x^7*y^3*z^8+2*x^4*z^9+2*x*y^7*z^4;
assert( nu(6,f) == 2968 )
assert( nu(6,f,Search => Linear) == 2968 )
assert( nu(6,f,ReturnList => true) == {0, 0, 4, 23, 118, 593, 2968} )
///

TEST ///
ZZ/17[x,y,z,w];
F = -5*x*y^4*z^3-2*x^4*z^3*w+6*y*z^3*w^4+7*z*w^3-6*w^2;
assert( nu(2,F) == 220 )
///



TEST ///
ZZ/5[x,y,z];
I=ideal(x+y^2,y+z^2,z+x^2);
J=ideal(x^3,y^3,z^3);
time assert( nu(1,I,J,ContainmentTest => FrobeniusRoot) == 42 )
time assert( nu(1,I,J, ContainmentTest => FrobeniusPower) == 30 )
time assert( nu(1,I,J,ContainmentTest=> FrobeniusPower,ReturnList => true) == {6, 30} )
///

TEST ///
R = ZZ/11[x,y,z]/ideal(x*y-z^2);
f = sub(x, R);
assert(compareFPT(5/11, f) == -1)
assert(compareFPT(1/2, f) == 0)
assert(compareFPT(61/120, f) == 1)
///

TEST ///
p = 7;
T = ZZ/p[a,b];
S = ZZ/p[x,y,z,w];
f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
I = ker f;
R = S/I;
g = sub(x, R);
assert(compareFPT(113/342, g) == -1)
assert(compareFPT(1/3, g) == 0)
assert(compareFPT(17/49, g) == 1)
///

TEST ///--(p+1) lines through the origin
p = 13;
R = ZZ/p[x,y];
f = x^p*y + y^p*x;
assert(isFPT(1/p, f))
assert(not isFPT(2/p, f))
assert(not isFPT(1/(p+1), f))
///

TEST /// --an F-jumping number that is not the FPT, taken from a paper of Hernandez and Teixeira
p = 5;
R = ZZ/p[x,y];
f = x^7*y^10*(x+y)^13*(x+2*y)^16;
assert(isFJumpingExponent(1/16, f));
assert(not isFPT(1/16, f));
///

TEST ///--a set of jumping Numbers, taken from a paper of Kevin Tucker (for multiplier ideals)
p = 131;
R =ZZ/p[x,y];
f = x^13-y^5;
assert(isFJumpingExponent(36/65, f));
assert(not isFJumpingExponent(37/65, f));
///

TEST ///
R = ZZ/11[x,y,z]/ideal(x*y-z^2);
f = x^2;
assert(isFJumpingExponent(1/4, f));
assert(isFJumpingExponent(1/2, f));
assert(not isFJumpingExponent(1/3, f));
///

TEST /// --degenerate cases
R = ZZ/101[x,y];
f = sub(0, R);
assert(fpt(f) == 0);
g= sub(1, R);
assert(fpt(g) == infinity);
///

TEST /// -- a cusp by any other name
R = ZZ/5[x,y];
f = x^2 - y^3;
g = (x+3*y)^2 - (x+y)^3;
assert(fpt(f) == 4/5);
assert(fpt(g) == 4/5);
///

TEST /// --an example from Canton-Hernandez-Schwede-Witt
 n = 3; d = 5;
 p = 19;
 N = d*(n*(d-2)-d);
 R = ZZ/p[x,y,z];
 f = x^d+y^d+z^d+(x*y*z)^(d-2);
 assert(fpt(f) == (n*(p-d+1)+d)/(d*(p-1)))
///
