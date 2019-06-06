--*************************************************
--*************************************************
-- This file is used for doing basic computations
-- i.e. things using only lists, numbers, etc.
-- that support other functions in the FThresholds
-- package.
--*************************************************
--*************************************************

--*************************************************
--Basic Manipulations with Numbers
--*************************************************
--===============================================================================

-- denominator ZZ := x -> 1
-- numerator ZZ := x -> x

--===============================================================================

--Finds the fractional part of a number.
-- fracPart = x -> x - floor x

--===============================================================================

--*************************************************
--Manipulations with Vectors
--*************************************************

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

-- Given a list L and a function f, minimalBy( L, f ) selects the elements 
-- of L with minimal value of f
minimalBy = ( L, f ) ->
(
    minValue := min( f \ L );
    select( L, i -> f(i) == minValue )
)

--===============================================================================

--*************************************************
--Tests for various types of polynomials
--*************************************************

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

-*
--===============================================================================

--isPolynomialOverFiniteField(F) checks if F is a polynomial over a finite field.
isPolynomialOverFiniteField = method( TypicalValue => Boolean )

-- isPolynomialOverFiniteField (RingElement) := Boolean => F ->
--     isPolynomialOverPosCharField( F ) and isFinitePrimeField coefficientRing ring F

isPolynomialOverFiniteField RingElement := Boolean => F ->
    isPolynomialOverPosCharField F and  ( try (coefficientRing ring F)#order then true else false )
*-

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

-*
--===============================================================================

--isNonconstantBinaryForm(F) checks if F is a nonconstant homogeneous polynomial
-- in two variables. See warning under "isBinaryForm".
isNonConstantBinaryForm = method( TypicalValue => Boolean )

isNonConstantBinaryForm RingElement := Boolean => F ->
    isBinaryForm F  and ( apply( exponents F, i -> sum i) )#0 > 0

--===============================================================================
*-

--isLinearBinaryForm(F) checks if F is a linearform in two variables. See warning
--under "isBinaryForm".
isLinearBinaryForm = method( TypicalValue => Boolean )

isLinearBinaryForm RingElement := Boolean => F ->
    isBinaryForm F and ( apply( exponents F, i -> sum i) )#0 == 1

--===============================================================================

--*************************************************
--Miscelaneous
--*************************************************

--===============================================================================

--Finds the x-intercept of a line passing through two points
xInt = ( x1, y1, x2, y2 ) ->
(
    if y1 == y2 then error "xInt: y1 == y2, so there is no intersection";
    x1 - y1 * ( x1 - x2 )/( y1 - y2 )
)

--===============================================================================

-- maxIdeal returns the ideal generated by the variables of a polynomial ring
maxIdeal = method( TypicalValue => MonomialIdeal )

maxIdeal PolynomialRing := MonomialIdeal => R ->
(
    if not isPolynomialRing R then error "maxIdeal: expected a polynomial ring, or an ideal or element of a polynomial ring";
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

-- HANDLING OF OPTIONS

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

-- passOptions selects a subset of options from an OptionTable
passOptions = method()

passOptions ( OptionTable, List ) := (o, L) ->
    new OptionTable from apply( L, k -> k => o#k )

--===============================================================================

-- FINDING RATIONAL NUMBERS IN AN INTERVAL

--this finds rational numbers in an interval, and ranks them based on the value that
--has the smallest computational expense
--we assume that each 1/(p^e-1) takes 1.5*e more computations than a 1/p value.
fptWeightedGuessList = ( pp, A, B, minGenSize ) ->
(
    coreDenom := ceiling (1/(B - A))^(2/3);
    numList := findNumbersBetween( A, B, coreDenom );
    while #numList < minGenSize do 
        ( coreDenom = 2*coreDenom; numList = findNumbersBetween( A, B, coreDenom ) );
    -- now that we have a list with enough rational numbers between a and b, 
    -- compute their weights
    local a;
    local b;
    local c;
    local wt;
    apply( numList, x -> 
        (
            ( a, b, c ) = decomposeFraction( pp, x );
            wt = b + 1.5*c;
            { wt, x }
        )
    )
)

--This function finds rational numbers in the range of the interval (A,B)
--with the given denominator, it is a helper function for fptWeightedGuessList
findNumberBetweenWithDenom = ( A, B, myDenom ) ->
(
    upperBound := floor( B*myDenom )/myDenom;
    --finds the number with denominator myDenom less than the upper
    --bound of myInterv
    lowerBound := ceiling( A*myDenom )/myDenom;
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
    sort toList set outList
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

