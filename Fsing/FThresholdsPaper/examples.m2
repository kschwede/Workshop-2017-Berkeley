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
nu(1, I, J)
f = x*y*(x^2 + y^2);
nu(1, f, J)

------------------------------------------------------------------

nu(1, 0_R, J)
nu(1, 1_R, J)

------------------------------------------------------------------

R = ZZ/17[x,y,z];
f = x^3 + y^4 + z^5;
m = ideal(x, y, z);
nu(2, f) == nu(2, f, m)

------------------------------------------------------------------

R = ZZ/17[x,y,z];
f = x^3 + y^4 + z^5; -- a diagonal polynomial
time nu(3, f)
time nu(3, f, UseSpecialAlgorithms => false)

------------------------------------------------------------------

R = ZZ/5[x,y,z];
f = x^2*y^4 + y^2*z^7 + z^2*x^8;
time nu(5, f) -- uses binary search (default)
time nu(5, f, Search => Linear)
m = ideal(x, y, z);
time nu(2, m, m^2) -- uses binary search (default)
time nu(2, m, m^2, Search => Linear) -- but linear seach gets luckier

------------------------------------------------------------------

nu(5, f, ReturnList => true)
nu(5, f, Verbose => true)

------------------------------------------------------------------

R = ZZ/11[x,y,z];
f = x^3 + y^3 + z^3 + x*y*z;
time nu(3, f) -- ContainmentTest is set to FrobeniusRoot, by default
time nu(3, f, ContainmentTest => StandardPower)

------------------------------------------------------------------

R = ZZ/3[x,y];
m = ideal(x, y);
nu(3, m^5)
nu(3, m^5, ContainmentTest => FrobeniusPower)

------------------------------------------------------------------

R = ZZ/7[x,y];
f = (x - 1)^3 - (y - 2)^2;
nu(1, f)
nu(1, f, IsLocal => false)

------------------------------------------------------------------
-- COMPARISONS
------------------------------------------------------------------

restart

R = ZZ/11[x, y, z]/(x^2 - y*(z - 1));
compareFPT(5/11, z - 1)
isFPT(1/2, z - 1)
isFPT(1/2, z - 1, IsLocal => true)

------------------------------------------------------------------

R = ZZ/13[x, y];
f = y*((y + 1) - (x - 1)^2)*(x - 2)*(x + y - 2);
isFJumpingExponent(3/4, f)

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
fpt(f, Attempts => 1, DepthOfSearch => 3) -- the right-hand endpoint (nu+1)/p^e is the F-pure threshold

------------------------------------------------------------------

f = x^6*y^4 + x^4*y^9 + (x^2 + y^3)^3;
fpt(f, Attempts => 1, DepthOfSearch => 3)
fpt(f, Attempts => 2, DepthOfSearch => 3) -- the left-hand endpoint nu/(p^e-1) is the F-pure threshold

------------------------------------------------------------------

f = x^3*y^11*(x + y)^8*(x^2 + y^3)^8;
fpt(f, DepthOfSearch => 3, Attempts => 2)
fpt(f, DepthOfSearch => 3, Attempts => 4) -- more attempts *always* improve the estimate
fpt(f, DepthOfSearch => 3, Attempts => 4, GuessStrategy => denominator) -- the exact answer, after a change of strategy

------------------------------------------------------------------

f = x^7*y^5*(x + y)^5*(x^2 + y^3)^4;
fpt(f, DepthOfSearch => 3, Attempts => 5)
fpt(f, DepthOfSearch => 3, Attempts => 5, Bounds => oo)

------------------------------------------------------------------

f = -2*x^10*y^5 - x^5*y^9 - 2*x^3*y^10 + 2*x^2*y^8 - 2*x*y^9;
numeric fpt(f, DepthOfSearch => 3)
numeric fpt(f, DepthOfSearch => 3, FinalAttempt => true) -- FinalAttempt improves the estimate slightly

------------------------------------------------------------------

f = -2*x^10*y^5 - x^5*y^9 - 2*x^3*y^10 + 2*x^2*y^8 - 2*x*y^9;
timing numeric fpt(f, DepthOfSearch => 3, FinalAttempt => true)
timing numeric fpt(f, DepthOfSearch => 3, Attempts => 4) -- a better answer in less time
timing fpt(f, DepthOfSearch => 4) -- the exact answer in even less time

------------------------------------------------------------------

f = x^7*y^5*(x + y)^5*(x^2 + y^3)^4;
fpt(f, DepthOfSearch => 3, FinalAttempt => true, Verbose => true)

------------------------------------------------------------------

R = ZZ/7[x,y];
f = (y - 1)^2-(x - 1)^3;
fpt(f, IsLocal => false)
fpt(f)

------------------------------------------------------------------

R = ZZ/7[x, y, z];
isSimpleNormalCrossing(x^2 - y^2)
isSimpleNormalCrossing(x^2 - y*z)

------------------------------------------------------------------

R = QQ[x, y, z];
f = (y - (x - 1)^2)*y^2; --SNC at the origin, but not globally
isSimpleNormalCrossing(f)
isSimpleNormalCrossing(f, IsLocal => false)
g = x*y^2*(x + 1)^3*(y - 1)^4; --SNC everywhere
isSimpleNormalCrossing(g)
isSimpleNormalCrossing(g, IsLocal => false)
