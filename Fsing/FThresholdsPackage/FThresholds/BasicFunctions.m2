--*******************************************************************************
--*******************************************************************************
-- This file is used for doing basic computations i.e. things using only lists, 
-- numbers, etc. that support other functions in the FThresholds  package.
--*******************************************************************************
--*******************************************************************************

--*******************************************************************************
--Manipulations with Lists
--*******************************************************************************

--===============================================================================

getNumAndDenom = method( TypicalValue => List )

-- Takes a rational vector u and returns a pair (a,q), where a
--is an integer vector and q an integer such that u=a/q.
getNumAndDenom List := List => u ->
(
    den := lcm apply( u, denominator );
    a := apply( u, n -> lift( n*den, ZZ ) );
    ( a, den )
)

--===============================================================================

--Selects or finds positions of nonzero, zero, positive entries in a list
selectNonzero = L -> select( L, x -> x != 0 )
selectPositive = L -> select( L, x -> x > 0 )
nonzeroPositions = L -> positions( L, x -> x != 0 )
zeroPositions = L -> positions( L, zero )
positivePositions = L -> positions( L, x -> x > 0 )

--===============================================================================

--*******************************************************************************
-- Tests for various types of polynomials and other objects
--*******************************************************************************

--===============================================================================

--isPolynomial(F) checks if F is a polynomial
isPolynomial = method( TypicalValue => Boolean )

isPolynomial RingElement := Boolean => F -> isPolynomialRing ring F

--===============================================================================

--isPolynomialOverPosCharField(F) checks if F is a polynomial over a field
--of positive characteristic
isPolynomialOverPosCharField = method( TypicalValue => Boolean )

isPolynomialOverPosCharField RingElement := Boolean => F ->
    isPolynomial F and isField( kk := coefficientRing ring F ) and char kk > 0

--===============================================================================

-- isDefinedOverFiniteField checks if somethethig is a polynomial ring over a
-- finite field, or an element or ideal in such ring
isDefinedOverFiniteField = method( TypicalValue => Boolean )

isDefinedOverFiniteField Ring := Boolean => R ->
    isPolynomialRing R and  (try (coefficientRing R)#order then true else false)

isDefinedOverFiniteField Ideal := Boolean => I ->
    isDefinedOverFiniteField ring I

isDefinedOverFiniteField RingElement := Boolean => f ->
    isDefinedOverFiniteField ring f

--===============================================================================

--Determines whether a polynomial f is a diagonal polynomial (i.e., of the form
--x_1^(a_1)+...+x_n^(a_n)) over a field of positive characteristic
isDiagonal = method( TypicalValue => Boolean )

isDiagonal RingElement := Boolean => f ->
    isPolynomialOverPosCharField f  and
    product( exponents f, v -> #(positions( v, x -> x != 0 )) ) == 1

--===============================================================================

--Returns true if the polynomial is a monomial
isMonomial = method( TypicalValue => Boolean )

isMonomial RingElement := Boolean => f ->
    isPolynomial f and #( terms f ) == 1

--===============================================================================

--Returns true if the polynomial is a binomial over a field of positive characteristic
isBinomial = method( TypicalValue => Boolean )

isBinomial (RingElement) := Boolean => f ->
    isPolynomialOverPosCharField f and #( terms f ) == 2

--===============================================================================

--isBinaryForm(F) checks if F is a (standard) homogeneous polynomial in two variables.
--WARNING: what we are really testing is if the *ring* of F is a polynomial ring
-- in two variables, and not whether F explicitly involves two variables.
-- (For example, if F=x+y is an element of QQ[x,y,z], this test will return "false";
-- if G=x is an element of QQ[x,y], this test will return "true".)
isBinaryForm = method( TypicalValue => Boolean )

isBinaryForm RingElement := Boolean => F ->
-- isHomogeneous is avoided below to account for non-standard gradings
    isPolynomial F and numgens ring F == 2 and same apply( exponents F, i -> sum i)

--===============================================================================

--isLinearBinaryForm(F) checks if F is a linearform in two variables. See warning
--under "isBinaryForm".
isLinearBinaryForm = method( TypicalValue => Boolean )

isLinearBinaryForm RingElement := Boolean => F ->
    isBinaryForm F and ( apply( exponents F, i -> sum i) )#0 == 1

--===============================================================================

--*******************************************************************************
--Handling of options
--*******************************************************************************

--===============================================================================

-- checkOptions checks whether the option values passed to a function are valid.
-- The arguments are:
-- 1. An option table.
-- 2. A list of the form { Option => check, ... } where check is an expected
--    Type or a list of valid values or a function that must return true for
--    valid values of Option.
-- If an option value is not appropriate, a user-friendly error message
-- is returned.

checkOptions = method()

checkOptions ( OptionTable, List ) := ( o, L ) ->
(
    opts := new HashTable from L;
    scanKeys( opts, k ->
	(
	    if instance( opts#k, VisibleList ) and not member( o#k, opts#k ) then
                error ( "checkOptions: value for option " | toString k | " must be an element of " | toString opts#k );
	    if instance( opts#k, Type ) and not instance( o#k, opts#k ) then
		error ( "checkOptions: value for option " | toString k | " must be of class " | toString opts#k );
	    if instance( opts#k, Function ) and not opts#k o#k  then
		error ( "checkOptions: value for option " | toString k | " is not valid" )
	)
    )
)

--===============================================================================

-- passOptions selects a subset of options from an OptionTable
passOptions = method()

passOptions ( OptionTable, List ) := (o, L) ->
    new OptionTable from apply( L, k -> k => o#k )

--===============================================================================

--*******************************************************************************
--Creating and testing ideals
--*******************************************************************************

--===============================================================================

-- maxIdeal returns the ideal generated by the variables of the ambient ring

maxIdeal = method( TypicalValue => MonomialIdeal )

maxIdeal PolynomialRing := MonomialIdeal => R ->
(
    if not isPolynomialRing R then 
        error "maxIdeal: expected a polynomial ring, or an ideal or element of a polynomial ring";
    monomialIdeal R_*
)

maxIdeal RingElement := MonomialIdeal => f -> maxIdeal ring f

maxIdeal Ideal := MonomialIdeal => I -> maxIdeal ring I

--===============================================================================

-- isProper and isUnitIdeal check if an ideal is proper or the unit ideal

isUnitIdeal = method( TypicalValue => Boolean )

isUnitIdeal Ideal := Boolean => I ->  dim I == -1

isProper = method( TypicalValue => Boolean )

isProper Ideal := Boolean => I -> not isUnitIdeal I

--===============================================================================

--*******************************************************************************
--Finding rational numbers in an interval
--*******************************************************************************

--===============================================================================

-- FINDING RATIONAL NUMBERS IN AN INTERVAL

-- This function is meant to estimate the computational cost
-- of comparing a rational number t with the fpt of a polynomial.
-- Right now, the standard way to compute this cost is as a
-- linear function of the numbers (a,b,c) returned by 
-- decomposeFraction(p,t). In the future, we may try using the 
-- base p expansion of a in this estimate.
 
cost = method()

-- These are the default weights, so the computatinal cost is 
-- assumed to be proportional to b + 1.5*c.
defaultWeights := { 0, 1, 1.5 }

-- This is for the case where the user passes his/her own weights.
-- The computational cost computed with the user's weights is
-- given priority, by being placed first in the list returned.
cost ( ZZ, QQ, List ) := ( p, t, userWeights ) ->
(
     decomp := decomposeFraction( p, t );
     uW := sum( decomp, userWeights, (i, j) -> i*j );
     dW := sum( decomp, defaultWeights, (i, j) -> i*j );
     { uW, dW }
)

-- This is for the case where the user passes his/her own cost function.
-- The computational cost computed with the user's function is given 
-- priority, by being placed first in the list returned.
cost ( ZZ, QQ, Function ) := ( p, t, userFunction ) ->
(
     decomp := decomposeFraction( p, t );
     uW := try userFunction t  else userFunction( p, t );
     dW := sum( decomp, defaultWeights, (i, j) -> i*j );
     { uW, dW }
)

-- This is for the case where the user does not pass anything.
cost ( ZZ, QQ, Nothing ) := ( p, t, userFunction ) ->
(
     decomp := decomposeFraction( p, t );
     { sum( decomp, defaultWeights, (i, j) -> i*j ) }
)

--===============================================================================

-- This finds rational numbers in an interval, and sorts them based on the value 
-- that has the smallest computational expense. 
-- This sorting is done by considering the user-specified cost weights/function, 
-- the cost computed with our default weights, and the distance from the midpoint
-- of the interval, and relies on the fact that the function "sort" sorts lists 
-- of lists lexicographically.  
fptWeightedGuessList = ( p, A, B, minGenSize, userCriterion ) ->
(
    if A >= B then 
        error "fptWeightedGuessList: Expected third argument to be greater than second";
    coreDenom := ceiling (1/(B - A))^(2/3);
    numList := findNumbersBetween( A, B, coreDenom );
    midpt := (B - A)/2;
    while #numList < minGenSize do
    ( 
        coreDenom = 2*coreDenom;
        numList = findNumbersBetween( A, B, coreDenom ) 
    );
    -- now that we have a list with enough rational numbers between a and b,
    -- compute their weights
    sort apply( numList, t ->
        join( cost( p, t, userCriterion ), { abs(t - midpt), t } )
    )
)

--This function finds rational numbers in the range of the interval (A,B)
--with the given denominator D; it is a helper function for fptWeightedGuessList
findNumberBetweenWithDenom = ( A, B, myDenom ) ->
(
    upperBound := ceiling( B*myDenom - 1 )/myDenom;
    --finds the number with denominator myDenom less than the upper
    --bound of myInterv
    lowerBound := floor( A*myDenom + 1 )/myDenom;
    --finds the number with denominator myDenom greater than the lower
     -- bound of myInterv
    if upperBound >= lowerBound then
    --first we check whether there is anything to search for
        apply( 1 + numerator( (upperBound - lowerBound)*myDenom ), i -> lowerBound + i/myDenom )
    else { }
)

--This function finds rational numbers in the range of
--the interval; the max denominator allowed is listed.
findNumbersBetween = ( A, B, maxDenom ) ->
(
    divisionChecks :=  new MutableList from maxDenom:true;
    -- creates a list with maxDenom elements all set to true.
    outList := {};
    i := 2;
    while i <= maxDenom do
    (
        outList = join( outList, findNumberBetweenWithDenom( A, B, i ) );
        i = i + 1
    );
    sort unique outList
)

-- numberWithMinimalDenominator(A,B,D) finds the number in the open interval
-- (A,B) with minimal denominator, starting the search with denominator D.
-- Returns sequence with the denominator and the number in (A,B) with that
-- denominator.
numberWithMinimalDenominator = (A, B, D) ->
(
    d := D;
    while ceiling( d*B - 1) < floor( d*A + 1 ) do d = d + 1;
    ( d, floor( d*A + 1 )/d )
)

--===============================================================================

--*******************************************************************************
--Miscelaneous
--*******************************************************************************

--===============================================================================

--Finds the x-intercept of a line passing through two points
xInt = ( x1, y1, x2, y2 ) ->
(
    if y1 == y2 then error "xInt: y1 == y2, so there is no intersection";
    x1 - y1 * ( x1 - x2 )/( y1 - y2 )
)

--===============================================================================

-- Factorization of polynomials and splitting fields --

-- factorsAndMultiplicities(F) factors the RingElement F and returns a list of pairs of
-- the form {factor,multiplicity}.
factorsAndMultiplicities = method( TypicalValue => List )

factorsAndMultiplicities RingElement := List => F ->
    apply( toList factor F, toList )

--splittingField returns the splittingField of a polynomial over a finite field
splittingField = method( TypicalValue => GaloisField )

splittingField RingElement := GaloisField => F ->
(
    if not isDefinedOverFiniteField F
        then error "splittingField: expected a polynomial over a finite field";
    p := char ring F;
    ord := ( coefficientRing ring F )#order;
    factors := first transpose factorsAndMultiplicities F;
    deg := lcm selectPositive flatten apply( factors, degree );
    GF( p, deg * floorLog( p, ord ) )
)

--===============================================================================

