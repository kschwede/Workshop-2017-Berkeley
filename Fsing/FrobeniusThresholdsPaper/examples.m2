-- If you want the package to load automatically, so that the 
-- numbering starts at "1" after a restart, add 
-- loadPackage("FThresholds") to the file ~/.Macaulay2/init.m2

------------------------------------------------------------------
-- NUS
------------------------------------------------------------------

restart

R = ZZ/11[x,y];
I = ideal(x^2 + y^3, x*y);
J = ideal(x^2, y^3);
frobeniusNu(2, I, J)
f = x*y*(x^2 + y^2);
frobeniusNu(2, f, J)

------------------------------------------------------------------

R = ZZ/17[x,y,z];
f = x^3 + y^4 + z^5; -- a diagonal polynomial
time frobeniusNu(10, f)
time frobeniusNu(10, f, UseSpecialAlgorithms => false)

------------------------------------------------------------------

R = ZZ/5[x,y,z];
m = ideal(x, y, z);
time frobeniusNu(2, m, m^2) -- uses binary search (default)
time frobeniusNu(2, m, m^2, Search => Linear) -- but linear search gets luckier

------------------------------------------------------------------

frobeniusNu(5, x^2*y^4 + y^2*z^7 + z^2*x^8, ReturnList => true)

------------------------------------------------------------------

R = ZZ/11[x,y,z];
f = x^3 + y^3 + z^3 + x*y*z;
time frobeniusNu(3, f) -- ContainmentTest is set to FrobeniusRoot, by default
time frobeniusNu(3, f, ContainmentTest => StandardPower)

------------------------------------------------------------------

R = ZZ/3[x,y];
m = ideal(x, y);
frobeniusNu(4, m^5)
frobeniusNu(4, m^5, ContainmentTest => FrobeniusPower)

------------------------------------------------------------------

R = ZZ/7[x,y];
f = (x - 1)^3 - (y - 2)^2;
frobeniusNu(3, f)
frobeniusNu(3, f, AtOrigin => false)

------------------------------------------------------------------
-- COMPARISONS
------------------------------------------------------------------

restart

R = ZZ/11[x,y,z]/(x^2 - y*(z - 1));
compareFPT(5/11, z - 1)
isFPT(1/2, z - 1)
isFPT(1/2, z - 1, AtOrigin => true)

------------------------------------------------------------------

R = ZZ/13[x,y];
f = y*((y + 1) - (x - 1)^2)*(x - 2)*(x + y - 2);
isFJumpingExponent(3/4, f)
isFPT(3/4, f)

------------------------------------------------------------------
-- FPTS
------------------------------------------------------------------

restart

R = ZZ/5[x,y,z];
fpt(x^3 + y^3 + z^3 + x*y*z)
fpt(x^5 + y^6 + z^7 + (x*y*z)^3)

------------------------------------------------------------------

fpt(x^17 + y^20 + z^24) -- a diagonal polynomial
fpt(x^2*y^6*z^10 + x^10*y^5*z^3) -- a binomial
R = ZZ/5[x,y];
fpt(x^2*y^6*(x + y)^9*(x + 3*y)^10) -- a form in two variables

------------------------------------------------------------------

fpt({x, y, x + y, x + 3*y}, {2, 6, 9, 10}) == oo

------------------------------------------------------------------

f = x^2*(x + y)^3*(x + 3*y^2)^5;
fpt(f, Attempts => 0) -- a bad estimate
fpt(f, Attempts => 0, DepthOfSearch => 3) -- a better estimate
fpt(f, Attempts => 1, DepthOfSearch => 3) -- the right-hand endpoint (ν+1)/p^e is the F-pure threshold

------------------------------------------------------------------

f = x^6*y^4 + x^4*y^9 + (x^2 + y^3)^3;
fpt(f, Attempts => 1, DepthOfSearch => 3)
fpt(f, Attempts => 2, DepthOfSearch => 3) -- the left-hand endpoint ν/(p^e-1) is the F-pure threshold

------------------------------------------------------------------

f = x^3*y^11*(x + y)^8*(x^2 + y^3)^8;
fpt(f, DepthOfSearch => 3, Attempts => 4)
fpt(f, DepthOfSearch => 3, Attempts => 6)
fpt(f, DepthOfSearch => 3, Attempts => 8) 

------------------------------------------------------------------

f = x^7*y^5*(x + y)^5*(x^2 + y^3)^4;
fpt(f, DepthOfSearch => 3, Attempts => 5)
fpt(f, DepthOfSearch => 3, Attempts => 5, Bounds => oo)

------------------------------------------------------------------

f = 2*x^10*y^8 + x^4*y^7 - 2*x^3*y^8;
numeric fpt(f, DepthOfSearch => 3)
numeric fpt(f, DepthOfSearch => 3, FinalAttempt => true) -- FinalAttempt improves the estimate slightly

------------------------------------------------------------------

time numeric fpt(f, DepthOfSearch => 3, FinalAttempt => true)
time fpt(f, DepthOfSearch => 3, Attempts => 7) 
time fpt(f, DepthOfSearch => 4) 

------------------------------------------------------------------

fpt(f, DepthOfSearch => 3, FinalAttempt => true, Verbose => true)

------------------------------------------------------------------

R = ZZ/7[x,y];
f = x*(y - 1)^2 - y*(x - 1)^3;
fpt(f)
fpt(f, AtOrigin => false)

------------------------------------------------------------------

R = ZZ/7[x,y,z];
isSimpleNormalCrossing(x^2 - y^2)
isSimpleNormalCrossing(x^2 - y*z)

------------------------------------------------------------------

R = QQ[x,y,z];
f = (y - (x - 1)^2)*y^2; --SNC at the origin, but not globally
isSimpleNormalCrossing(f)
isSimpleNormalCrossing(f, AtOrigin => false)
