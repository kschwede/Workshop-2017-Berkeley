--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- CONTENTS
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

---------------------------------------------------------------------------------
-- Nu computations

-- Main function: nu

-- Auxiliary Functions: nu1, binarySearch, binarySearchRecursive, linearSearch,
--     testPower, testRoot, testFrobeniusPower, nuInternal

---------------------------------------------------------------------------------
-- FThreshold computations and estimates

-- Main function: fpt

-- Auxiliary functions: fSig, guessFPT

----------------------------------------------------------------------------------
-- FPT/F-Jumping exponent check

-- Main functions: compareFPT, isFPT, isFJumpingExponent

-- Auxiliary functions: getNonzeroGenerator, isLocallyPrincipalIdeal,
-- getDivisorIndex, compareFPTPoly, isFJumpingExponentPoly


--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for computing (nu_I)^J(p^e), (nu_f)^J(p^e)
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

---------------------------------------------------------------------------------
-- nu1(I,J) finds the maximal N such that I^N is not contained in J, i.e., nu_I^J(1)
nu1 = method( TypicalValue => ZZ )

nu1 ( Ideal, Ideal ) :=  ZZ => ( I, J ) ->
(
    d := 1;
    while not isSubset( I^d, J ) do d = d + 1;
    d - 1
)

nu1 ( RingElement, Ideal ) := ZZ => ( f, J ) -> nu1( ideal f, J )

---------------------------------------------------------------------------------
-- TESTS
---------------------------------------------------------------------------------

-- purpose is to verify containment in Frobenius powers

-- testRoot(J,a,I,e) checks whether J^a is a subset of I^[p^e] by checking whether (J^a)^[1/p^e] is a subset of I
testRoot = ( J, a, I, e ) -> isSubset( frobeniusRoot( e, a, J ), I )

testPower = ( J, a, I, e ) -> isSubset( if (isIdeal J) then J^a else ideal(J)^a, frobenius(e,I) )

-- testFrobeniusPower(J,a,I,e) checks whether J^[a] is a subset of I^[p^e]
testFrobeniusPower = method( TypicalValue => Boolean )

testFrobeniusPower ( Ideal, ZZ, Ideal, ZZ ) := Boolean => ( J, a, I, e ) ->
    isSubset( frobeniusPower( a, J ), frobenius( e, I ) )

testFrobeniusPower ( RingElement, ZZ, Ideal, ZZ ) := Boolean => ( f, a, I, e ) ->
    testRoot( f, a, I, e )

-- hash table to select test function from option keyword
test := new HashTable from
    {
	FrobeniusPower => testFrobeniusPower,
	FrobeniusRoot => testRoot,
        StandardPower => testPower
    }

---------------------------------------------------------------------------------
-- SEARCH FUNCTIONS
---------------------------------------------------------------------------------

-- Each *Search(I,J,e,a,b,testFunction) searches for the last n in [a,b) such that
-- testFunction(I,n,J,e) is false, assuming that test(I,a,J,e) is false and test(I,b,J,e)
-- is true.

-- Non-recursive binary search, based on our previous code
binarySearch = ( I, J, e, startPt, endPt, testFunction ) ->
(
    a := startPt;
    b := endPt;
    local c;
    while b > a + 1 do
    (
	c = floor( ( a + b )/2 );
	if testFunction( I, c, J, e ) then b = c else a = c
    );
    a
)

-- Linear search
linearSearch = ( I, J, e, a, b, testFunction ) ->
(
    c := a + 1;
    while not testFunction( I, c, J, e ) do c = c + 1;
    c - 1
)

-- hash table to select search function from option keyword
search := new HashTable from
    {
	Binary => binarySearch,
	Linear => linearSearch
    }

---------------------------------------------------------------------------------
-- OPTION PACKAGES
---------------------------------------------------------------------------------

optNu:=
{
    ContainmentTest => null,
    ReturnList => false,
    Search => Binary,
    UseSpecialAlgorithms => true,
    Verbose => false
}

---------------------------------------------------------------------------------
-- INTERNAL FUNCTION
---------------------------------------------------------------------------------

nuInternal = optNu >> o -> ( n, f, J ) ->
(
    -----------------
    -- SOME CHECKS --
    -----------------
    -- Verify if option values are valid
    checkOptions( o,
	{
	    ContainmentTest => { StandardPower, FrobeniusRoot, FrobeniusPower, null },
	    ReturnList => Boolean,
	    Search => { Binary, Linear },
	    UseSpecialAlgorithms => Boolean,
	    Verbose => Boolean
	}
    );
    -- Check if f is defined over a finite field
    if not isDefinedOverFiniteField f then
        error "nuInternal: expected polynomial or ideal in a polynomial ring over a finite field";

    -------------------
    -- TRIVIAL CASES --
    -------------------
    -- Return list with zeros if f is 0 (per Blickle-Mustata-Smith convention)
    if f == 0 then return if o.ReturnList then toList( (n + 1):0 ) else 0;
    -- Return list with infinities if f is not in the radical of J
    inRadical := if isIdeal f then isSubset( f, radical J ) else isSubset( ideal f, radical J );
    if not inRadical then return if o.ReturnList then toList( (n + 1):infinity ) else infinity;

    --------------------------------
    -- DEAL WITH PRINCIPAL IDEALS --
    --------------------------------
    -- Check if f is a principal ideal; if so, replace it with its generator,
    isPrincipal := false;
    g := f;
    if isIdeal g then
    (
        if numgens( g = trim g ) == 1 then
        (
	        isPrincipal = true;
	        g = g_*_0
        )
    )
    else isPrincipal = true;
    -----------------------------------------

    p := char ring g;

    -----------------------------------------
    -- WHEN SPECIAL ALGORITHMS CAN BE USED --
    -----------------------------------------
    -- Deal with some special cases for principal ideals
    if isPrincipal and J == maxIdeal g then
    (
	if not isSubset( ideal g, J ) then
	    error "nuInternal: the polynomial is not in the homogeneous maximal ideal";
        if not isSubset( ideal g^(p-1), frobenius J ) then -- fpt = 1
	    return if o.ReturnList then apply( n + 1, i -> p^i-1 ) else p^n-1;
        if o.UseSpecialAlgorithms then
        (
	    fpt := null;
	    if isDiagonal g then fpt = diagonalFPT g;
            if isBinomial g then fpt = binomialFPT g;
	    if fpt =!= null then
	        return
		(
		    if o.ReturnList then apply( n + 1, i -> p^i*adicTruncation( p, i, fpt ) )
		    else p^n*adicTruncation( p, n, fpt )
		)
        )
    );

    -----------
    -- SETUP --
    -----------
    searchFct := search#(o.Search);
    conTest := o.ContainmentTest;
    -- choose appropriate containment test, if not specified by user
    if conTest === null then conTest = (if isPrincipal then FrobeniusRoot else StandardPower);
    testFct := test#(conTest);
    local N;
    nu := nu1( g, J );
    theList := { nu };
    if o.Verbose then print( "nu(1) = " | toString nu );

    ----------------------
    -- EVERY OTHER CASE --
    ----------------------
    (
	N = if isPrincipal or conTest === FrobeniusPower
	   then p else (numgens trim J)*(p-1) + 1;
    scan( 1..n, e ->
        (
           nu = searchFct( g, J, e, p*nu, (nu + 1)*N, testFct );
           if o.Verbose then print( "nu(p^" | toString e | ") = " | toString nu );
           theList = append( theList, nu )
        )
    )
    );
    if o.ReturnList then theList else last theList
)

---------------------------------------------------------------------------------
-- EXPORTED METHODS
---------------------------------------------------------------------------------

nu = method( Options => optNu )

nu ( ZZ, Ideal, Ideal ) := o -> ( e, I, J ) -> nuInternal( e, I, J, o )

nu ( ZZ, RingElement, Ideal ) := o -> ( e, f, J ) -> nuInternal( e, f, J, o )

nu ( ZZ, Ideal ) := o -> ( e, I ) -> nu( e, I, maxIdeal I, o )

nu ( ZZ, RingElement ) := o -> ( e, f ) -> nu( e, f, maxIdeal f, o )

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for guessing and estimating F-Thresholds
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and FPT computations.   --
--************************************************************--
----------------------------------------------------------------

--- Computes the F-signature for a specific value a/p^e
--- Input:
---	f - some polynomial in two or three variables in a ring R of PRIME characteristic
---	a - some positive integer between 0 and p^e
---	e - some positive integer
--- Output:
---	returns value of the F-signature of the pair (R, f^{a/p^e})
--- Code is based on work of Eric Canton
fSig := ( f, a, e ) ->
(
     R := ring f;
     p := char R;
     1 - p^( -e * dim( R ) ) * degree( frobenius( e, maxIdeal R ) + ideal f^a )
)

-- some constants associated with guessFPT
numExtraCandidates := 20;
minNumCandidates := 6;
-- The default number of "random" checks to be performed
attemptsDefault := 3;

-- guessFPT takes a polynomial f, and endpoints a and b of a closed interval
--     that contains the F-pure threshold of f.
-- The option attempts specifies how many tests are to be done, starting with
--     the right- and left-hand endpoints b and a, respectively.
-- The option GuessStrategy specifies how to prioritize the numbers to be checked.
-- It returns either fpt(f), if found, or an interval containing it, if not.
guessFPT := { Attempts => attemptsDefault, GuessStrategy => null, Verbose => false } >> o -> ( f, a, b ) ->
(
    maxChecks := o.Attempts;
    if o.Verbose then print "\nStarting guessFPT ...";
    -- Check if fpt is the upper bound b
    if isFPT( b, f, IsLocal => true ) then
    (
        if o.Verbose then print( "\nfpt is the right-hand endpoint." );
        return b
    )
    else if o.Verbose then print "\nThe right-hand endpoint is not the fpt ...";
    -- Check if fpt is the lower bound a
    if maxChecks >= 2 then
        if not isFRegular( a, f, IsLocal => true ) then
	(
	    if o.Verbose then
	        print( "\nfpt is the left-hand endpoint." );
	    return a
	)
        else if o.Verbose then print "\nThe left-hand endpoint is not the fpt ...";
    -- Now proceed with more checks, selecting numbers in the current
    --   interval with minimal denominator
    counter := 3;
    local t;
    local comp;
    ( A, B ) := ( a, b );
    p := char ring f;
    candidateList := fptWeightedGuessList( p, A, B, maxChecks + numExtraCandidates, o.GuessStrategy );
    while counter <= maxChecks do
    (
        --  pick candidate with minimal weight
        t = last first candidateList; --the candidate list should already be sorted
        comp = compareFPT( t, f, IsLocal => true );
        if comp == 0 then  -- found exact FPT! YAY!
        (
	    if o.Verbose then
    	        print( "\nguessFPT found the exact value for fpt(f) in try number " | toString counter | "." );
    	    return t
    	);
        if comp == 1 then ( B = t; candidateList = select( candidateList, a -> last a < t ) ) -- fpt < t
    	else ( A = t; candidateList = select( candidateList, a -> last a > t ) ); -- fpt > t
        counter = counter + 1;
        -- if not done and running short on candidates, load up some more
        if counter < maxChecks and #candidateList <= minNumCandidates then
            candidateList = sort fptWeightedGuessList( p, A, B, maxChecks + numExtraCandidates, o.GuessStrategy )
    );
    if o.Verbose then
        print( "\nguessFPT narrowed the interval down to ( " | toString A | ", " | toString B | " ) ..." );
    { A, B }
)

-- F-pure threshold estimation, at the origin.
-- e is the max depth to search in.
-- FRegularityCheck is whether the last isFRegularPoly is run
--   (which can take a significant amount of time).
fpt = method(
    Options =>
        {
	    DepthOfSearch => 1,
	    FRegularityCheck => false,
	    Attempts => attemptsDefault,
	    UseSpecialAlgorithms => true,
	    UseFSignature => false,
	    Verbose => false,
            GuessStrategy => null
	}
)

fpt RingElement := o -> f ->
(
    ------------------------------
    -- DEAL WITH A TRIVIAL CASE --
    ------------------------------
    if f == 0 then return 0;
-- maybe check for monomials too

    ---------------------
    -- RUN SEVERAL CHECKS
    ---------------------
    -- Check if option values are valid
    checkOptions( o,
        {
	    DepthOfSearch => ( k -> instance( k, ZZ ) and k > 0 ),
	    FRegularityCheck => Boolean,
	    Attempts => ( k -> instance( k, ZZ ) and k >= 0 ),
	    UseSpecialAlgorithms => Boolean,
	    UseFSignature => Boolean,
	    Verbose => Boolean
	}
    );
    -- Check if polynomial has coefficients in a finite field
    if not isDefinedOverFiniteField f  then
        error "fpt: expected polynomial with coefficients in a finite field";
    -- Check if polynomial is in the homogeneous maximal ideal
    M := maxIdeal f;   -- The maximal ideal we are computing the fpt at
    p := char ring f;
    if not isSubset( ideal f, M ) then return infinity;

    ----------------------
    -- CHECK IF FPT = 1 --
    ----------------------
    if o.Verbose then print "\nStarting fpt ...";
    if not isSubset( ideal f^(p-1), frobenius M ) then
    (
        if o.Verbose then print "\nnu(1,f) = p-1, so fpt(f) = 1.";
        return 1
    );
    if o.Verbose then print "\nfpt is not 1 ...";

    ---------------------------------------------
    -- CHECK IF SPECIAL ALGORITHMS CAN BE USED --
    ---------------------------------------------
    if o.UseSpecialAlgorithms then
    (
	if o.Verbose then print "\nVerifying if special algorithms apply...";
	if isDiagonal f then
	(
	    if o.Verbose then
	        print "\nPolynomial is diagonal; calling diagonalFPT ...";
            return diagonalFPT f
        );
        if isBinomial f then
        (
            if o.Verbose then
	        print "\nPolynomial is a binomial; calling binomialFPT ...";
            return binomialFPT f
        );
        if isBinaryForm f then
        (
            if o.Verbose then
	        print "\nPolynomial is a binary form; calling binaryFormFPT ...";
            return binaryFormFPT( f, Verbose => o.Verbose )
        )
    );
    if o.Verbose then print "\nSpecial fpt algorithms were not used ...";

    -----------------------------------------------
    -- COMPUTE NU TO FIND UPPER AND LOWER BOUNDS --
    -----------------------------------------------
    e := o.DepthOfSearch;
    n := nu( e, f );
    LB := n/(p^e - 1); -- lower bound (because of forbidden intervals)
    UB := (n + 1)/p^e; -- upper bound
    strictLB := false; -- at this point, LB and UB *could* be the fpt
    strictUB := false;
    if o.Verbose then
    (
         print( "\nnu has been computed: nu = nu(" | toString e | ",f) = " | toString n | " ..." );
	 print( "\nfpt lies in the interval [ nu/(p^e-1), (nu+1)/p^e ] = [ " | toString LB | ", " | toString UB | " ] ..." )
    );

    --------------------
    -- CALL GUESS FPT --
    --------------------
    if o.Attempts > 0 then
    (
	guess := guessFPT( f, LB, UB, passOptions( o, { Attempts, Verbose, GuessStrategy } ) );
	if class guess =!= List then return guess; -- guessFPT was successful
	-- if not sucessful, adjust bounds and their strictness
	( LB, UB ) = toSequence guess;
	strictUB = true;
	if o.Attempts >= 2 then strictLB = true
    );

    ---------------------------------------
    -- F-SIGNATURE INTERCEPT COMPUTATION --
    ---------------------------------------
    if o.UseFSignature then
    (
        if o.Verbose then print "\nBeginning F-signature computation ...";
        s1 := fSig( f, n-1, e );
        if o.Verbose then
	    print( "\nFirst F-signature computed: s(f,(nu-1)/p^e) = " | toString s1 | " ..." );
        s2 := fSig( f, n, e );
        if o.Verbose then
            print( "\nSecond F-signature computed: s(f,nu/p^e) = " | toString s2 | " ..." );
        -- Compute intercept of line through ((nu-1)/p^2,s1) and (nu/p^e,s2)
        int := xInt( (n-1)/p^e, s1, n/p^e, s2 );
        if o.Verbose then
            print("\nComputed F-signature secant line intercept: " | toString int | " ...");
        -- Now check to see if F-signature line crosses at UB. If so, then that's the fpt
        if UB == int then
        (
	    if  o.Verbose then
	        print "\nF-signature secant line crosses at the upper bound, so that is the fpt.";
	    return int
        );
        -- Compare the intercept with the current lower bound
	if LB < int then
        (
	    if o.Verbose then
	        print "\nF-signature intercept is an improved lower bound ...";
	    LB = int;
	    strictLB = false;
        )
        else if o.Verbose then
            print "\nF-signature computation failed to find an improved lower bound ...";
    );

    ------------------------------
    -- FINAL F-REGULARITY CHECK --
    ------------------------------
    if o.FRegularityCheck and not strictLB then
    (
	if o.Verbose then print "\nStarting final check ...";
        if not isFRegular( LB, f, IsLocal => true ) then
        (
	   if o.Verbose then
	       print "\nFinal check successful; fpt is the lower bound.";
	   return LB
      	)
	else
	(
	    if o.Verbose then print "\nFRegularityCheck did not find the fpt ...";
	    strictLB = true
	)
    );
    if o.Verbose then
    (
	print "\nfpt failed to find the exact answer; try increasing the value of DepthOfSearch or Attempts.";
        print(
	    "\nfpt lies in the interval " |
	    ( if strictLB then "( " else "[ " ) |
	    toString LB |
	    ", " |
	    toString UB |
	    ( if strictUB then " )." else " ]." )
        )
    );
    { LB, UB }
)

-- Special template for products of linear forms in two variables
fpt ( List, List ) := o -> ( L, m ) ->
    binaryFormFPT( L, m, Verbose => o.Verbose )

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for checking if given numbers are F-jumping numbers
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--compareFPT see if a number is less than, equal to, or greater than the FPT.
--It returns -1 if less
--it returns 0 if equal
--it returns 1 if greater
compareFPT = method(
    Options =>
    {
	MaxCartierIndex => 10,
	FrobeniusRootStrategy => Substitution,
	AssumeDomain => true,
	QGorensteinIndex => 0,
    IsLocal => false,
    Verbose => false
    },
    TypicalValue => ZZ
)

--gets a nonzero generator of an ideal.
getNonzeroGenerator := I ->
(
    gen := select( 1, I_*, x -> x != 0 );
    if gen === { } then null else first gen
)

isLocallyPrincipalIdeal := I ->
(
    localGen := getNonzeroGenerator I;
    R := ring I;
    if localGen === null then return ( false, 0_R );
    inverseIdeal := ideal localGen : I;
    idealProduct := inverseIdeal * I;
    if reflexify idealProduct  == idealProduct then
        ( true, inverseIdeal )
    else ( false, 0_R )
)

--helper function for compareFPT
getDivisorIndex := ( maxIndex, divisorialIdeal ) ->
(
    cartIndex := 0;
    curIdeal := null;
    locallyPrincipal := false;
    while not locallyPrincipal and cartIndex < maxIndex do
    (
        cartIndex = cartIndex + 1;
        curIdeal = reflexivePower( cartIndex, divisorialIdeal );
        locallyPrincipal = first isLocallyPrincipalIdeal curIdeal
    );
    if cartIndex <= 0 or not locallyPrincipal then
        error "getDivisorIndex: Ring does not appear to be Q-Gorenstein; perhaps increase the option MaxCartierIndex. Also see the documentation for isFRegular";
    cartIndex
)

compareFPT ( Number, RingElement ) := ZZ => o -> ( t, f ) ->
(
    if o.Verbose or debugLevel > 1 then print "compareFPT: starting.";
    -- Check if option values are valid
    checkOptions( o,
        {
	    MaxCartierIndex => ZZ,
	    FrobeniusRootStrategy => { Substitution, MonomialBasis },
	    AssumeDomain => Boolean,
	    QGorensteinIndex => ZZ,
        IsLocal => Boolean,
        Verbose => Boolean
	}
    );
    --first we gather background info on the ring (QGorenstein generators, etc.)
    R1 := ring f;
    if isPolynomial f then return compareFPTPoly( t, f, passOptions( o, { IsLocal, FrobeniusRootStrategy, Verbose } ) );
    S1 := ambient R1;
    I1 := ideal R1;
    canIdeal := canonicalIdeal R1;
    pp := char R1;
    cartIndex := 0;
    fList := { f };
    tList := { t };
    local computedTau;
    local computedHSLGInitial;
    local computedHSLG;
    local baseTau;
    local runningIdeal;
    local a1quot;
    local a1rem;
    local locMax;
    if o.IsLocal then (locMax = sub(maxIdeal(S1), R1) ) else (locMax = ideal(0_R1));

    ( a1, b1, c1 ) := decomposeFraction( pp, t, NoZeroC => true );

    if o.QGorensteinIndex > 0 then cartIndex = o.QGorensteinIndex
    else cartIndex = getDivisorIndex( o.MaxCartierIndex, canIdeal );
    if o.Verbose or debugLevel > 1 then print "compareFPT: cartier index determined.";
    h1 := 0_S1;
    --first we do a quick check to see if the test ideal is easy to compute
    if ( pp - 1 ) % cartIndex == 0 then
    (
        if o.Verbose or debugLevel > 1 then print "compareFPT: cartier index divides p-1.";
        J1 := testElement R1;
        try h1 = QGorensteinGenerator( 1, R1 ) then
        (
            if o.Verbose or debugLevel > 1 then print "compareFPT: we found a single generating map.";
            computedTau = first testModule( tList, fList, CanonicalIdeal => ideal 1_R1, GeneratorList => { h1 }, passOptions( o, { AssumeDomain, FrobeniusRootStrategy } ) );
            if o.Verbose or debugLevel > 1 then print concatenate("compareFPT: testIdeal(f^t) = ", toString(computedTau));
            if isUnitIdeal ( computedTau + locMax ) then return -1;
            --at this point we know that this is not the FPT
            --now we have to run the sigma computation
            baseTau = first testModule( 0/1, 1_R1, CanonicalIdeal => ideal 1_R1, GeneratorList => { h1 }, passOptions( o, { AssumeDomain, FrobeniusRootStrategy } ) );
            if o.Verbose or debugLevel > 1 then print concatenate("compareFPT: testIdeal(R) = ", toString(baseTau));
            if isProper (baseTau + locMax) then
                error "compareFPT: The ambient ring must be F-regular";
            --the ambient isn't even F-regular
            if a1 > pp^c1 - 1 then
            (
                a1quot = floor( ( a1 - 1 )/( pp^c1 - 1 ) );
                a1rem = a1 - ( pp^c1 - 1 )*a1quot;
                computedHSLGInitial = first FPureModule( { a1rem/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => baseTau, GeneratorList => { h1 } );
                computedHSLG = frobeniusRoot( b1, { ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), a1quot }, { h1, sub( f, S1 ) }, sub( computedHSLGInitial, S1 ) );
            )
            else (
                computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => baseTau, GeneratorList => { h1 } );
                --the e is assumed to be 1 here since we are implicitly doing stuff
                computedHSLG = frobeniusRoot( b1, ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), h1, sub( computedHSLGInitial, S1 ) );
            );
            if o.Verbose or debugLevel > 1 then print concatenate("compareFPT: testIdeal(f^(t-epsilon)) = ", toString(computedHSLG));
            if o.IsLocal then (locMax = maxIdeal(S1)) else (locMax = ideal(0_S1));
            if isProper( computedHSLG + I1 + locMax ) then return 1;
            --the fpt we picked is too big
            return 0; --we found the FPT!
        )
        else h1 = 0_S1
    );
    --now compute the test ideal in the general way (if the index does not divide...)
    if (cartIndex % pp == 0) then error "compareFPT: This function requires that the Q-Gorenstein index is not divisible by p.";
    gg := first (trim canIdeal)_*;
    dualCanIdeal :=  ideal gg : canIdeal;
    nMinusKX := reflexivePower( cartIndex, dualCanIdeal );
    gensList := (trim nMinusKX)_*;
    gensList2 := apply(gensList, x -> sub(x, S1));

    omegaAmb := sub( canIdeal, S1 ) + ideal R1;
    u1 := frobeniusTraceOnCanonicalModule( I1, omegaAmb );
    if o.Verbose or debugLevel > 1 then
        print "compareFPT: frobenius trace on canonical module computed.";

    t2 := append( tList, 1/cartIndex );
    local f2;
    runningIdeal = ideal 0_S1;
    for x in gensList do
    (
        f2 = append( fList, x );
        runningIdeal = runningIdeal + first testModule( t2, f2, CanonicalIdeal => canIdeal, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain )
    );

    newDenom := reflexify( canIdeal * dualCanIdeal );
    computedTau = ( runningIdeal * R1 ) : newDenom;
    if o.Verbose or debugLevel > 1 then
        print concatenate("compareFPT: testIdeal(f^t) = ", toString(computedTau));
    if isUnitIdeal (computedTau + locMax) then return -1;
    --at this point we know that this is not the FPT

    --now we compute the base tau
    runningIdeal = ideal 0_S1;
    for x in gensList do
    (
        runningIdeal = runningIdeal + first testModule( {1/cartIndex}, {x}, CanonicalIdeal => canIdeal, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain )
    );
    baseTau = ( runningIdeal * R1 ) : newDenom;
    if o.Verbose or debugLevel > 1 then
        print concatenate("compareFPT: testIdeal(R) = ", toString(baseTau));
    if isProper baseTau then error "compareFPT: The ambient ring must be F-regular";

    ( a1x, b1x, c1x ) := decomposeFraction( pp, 1/cartIndex, NoZeroC => true );
    c2 := lcm(c1, c1x);
    b2 := ceiling(b1/c1x)*c1x; -- this is how many times to apply our version of trace
    scale := pp^(b2-b1);
    if a1 > pp^c1 - 1 then
    (
        a1quot = floor( ( a1 - 1 )/( pp^c1 - 1 ) );
        a1rem = a1 - ( pp^c1 - 1 )*a1quot;
        computedHSLGInitial = sum apply(gensList, x -> first FPureModule( { a1rem/( pp^c1 - 1 ), 1/cartIndex }, { f, x }, CanonicalIdeal => runningIdeal, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy ));
        computedHSLG = sum apply(gensList2, x -> sum( apply(u1, h1 -> frobeniusRoot( b2, { scale*ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), scale*a1quot, a1x*ceiling((pp^b2 - 1)/(pp^c1x - 1)) }, { h1, sub( f, S1 ), x }, sub( computedHSLGInitial, S1 ), FrobeniusRootStrategy => o.FrobeniusRootStrategy ) )));
    )
    else (
        computedHSLGInitial = sum apply(gensList, x -> first FPureModule( { a1/( pp^c1 - 1 ), 1/cartIndex }, { f, x }, CanonicalIdeal => baseTau, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy ));
        --the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = sum apply(gensList2, x-> sum( apply(u1, h1->frobeniusRoot( b2, {scale*ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), a1x*ceiling((pp^b2 - 1)/(pp^c1x - 1))}, {h1, x}, sub( computedHSLGInitial, S1 ) ) )));
    );
    if o.Verbose or debugLevel > 1 then
        print concatenate("compareFPT: testIdeal(f^(t-epsilon)) = ", toString( (computedHSLG* R1 ) : newDenom ));
    if isProper( ((computedHSLG * R1 ) : newDenom ) + locMax) then return 1;
    --the fpt we picked is too big
    return 0;
    --it is the FPT!
)

compareFPTPoly = method( Options => { IsLocal => false, FrobeniusRootStrategy => Substitution, Verbose => false } )

compareFPTPoly(Number, RingElement) := o -> ( t, f ) ->
(
    if o.Verbose or debugLevel > 1 then print "compareFPTPoly: starting";
    --first we gather background info on the ring (QGorenstein generators, etc.)
    S1 := ring f;
    pp := char S1;
    cartIndex := 0;
    fList := { f };
    tList := { t };
    local computedTau;
    local computedHSLG;
    local computedHSLGInitial;
    local locMax;
    if o.IsLocal then (locMax = maxIdeal(S1)) else (locMax = ideal(0_S1));

    h1 := 1_S1;
    --first we do a quick check to see if the test ideal is easy to compute
    computedTau = first testModule( tList, fList, CanonicalIdeal => ideal 1_S1, GeneratorList => { h1 }, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => true );
    if o.Verbose or debugLevel > 1 then
        print concatenate("compareFPTPoly: testIdeal(f^t) = ", toString(computedTau));
    if isUnitIdeal (computedTau + locMax) then return -1;
    --at this point we know that this is not the FPT

    --now we have to run the sigma computation
    ( a1, b1, c1 ) := decomposeFraction( pp, t, NoZeroC => true );
    if a1 > pp^c1 - 1 then
    (
        a1quot := floor( ( a1 - 1 )/( pp^c1 - 1 ) );
        a1rem := a1 - ( pp^c1 - 1 )*a1quot;
        computedHSLGInitial = first FPureModule( { a1rem/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => ideal 1_S1, GeneratorList => { h1 } );
        computedHSLG = frobeniusRoot( b1, { ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), a1quot }, { h1, f }, computedHSLGInitial );
    )
    else
    (
        computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => ideal 1_S1, GeneratorList => { h1 } );
	--the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = frobeniusRoot( b1, ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), h1, computedHSLGInitial );
    );
    if o.Verbose or debugLevel > 1 then
        print concatenate("compareFPTPoly: testIdeal(f^(t-epsilon)) = ", toString(computedHSLG ));
    if isProper (computedHSLG + locMax) then return 1;
    --the fpt we picked is too small
    0 --it is the FPT!
)

-- isInForbiddenInterval takes a prime number p and a rational number t
-- and checks whether t lies in an interval of the form (a/p^e,a/(p^e-1)),
-- for some e. If it does, it cannot be an FPT in characteristic p.
isInForbiddenInterval = method( TypicalValue => Boolean );

isInForbiddenInterval ( ZZ, QQ ) := Boolean => ( p, t ) ->
(
    if t < 0 or t > 1 then return true;
    ( a, b, c ) := decomposeFraction( p, t );
    valid := true; -- valid means "valid fpt" (not in forbidden interval)
    e := 1;
    while valid and e <= b + c do
    (
      --The following comes from Proposition 4.1 and Corollary 4.1(1) in
      --"F-purity of hypersurfaces" by Hernandez
        if floor( ( p^e - 1 )*t ) != p^e * adicTruncation( p, e, t ) then
	    valid = false;
	e = e + 1
    );
    not valid
)

isInForbiddenInterval ( ZZ, ZZ ) := Boolean => ( p, t ) ->
    isInForbiddenInterval( p, t/1 )

--isFPT, determines if a given rational number is the FPT of a pair in a
-- polynomial ring.

isFPT = method(
    Options =>
    {
	MaxCartierIndex => 10,
	FrobeniusRootStrategy => Substitution,
	AssumeDomain => true,
	QGorensteinIndex => 0,
    IsLocal => false,
    Verbose => false
    },
    TypicalValue => Boolean
)

-- Dan: We should use the "Origin" option somehow...
isFPT ( Number, RingElement ) := Boolean => o -> ( t, f ) ->
(
    if o.Verbose or debugLevel > 1 then print "isFPT: starting.";
    if isInForbiddenInterval( char ring f, t ) then false else
        0 == compareFPT( t/1, f, o )
)

-- isFJumpingExponent determines if a given rational number is an
-- F-jumping exponent
isFJumpingExponent = method(
    Options =>
    {
	MaxCartierIndex => 10,
	FrobeniusRootStrategy => Substitution,
	AssumeDomain => true,
	QGorensteinIndex => 0,
    IsLocal => false,
    Verbose => false
    },
    TypicalValue => Boolean
)

isFJumpingExponent ( Number, RingElement ) := ZZ => o -> ( t, f ) ->
(
    if o.Verbose or debugLevel > 1 then print "isFJumpingExponent: starting.";
    -- Check if option values are valid
    checkOptions( o,
        {
	    MaxCartierIndex => ZZ,
	    FrobeniusRootStrategy => { Substitution, MonomialBasis },
	    AssumeDomain => Boolean,
	    QGorensteinIndex => ZZ,
        IsLocal => Boolean,
        Verbose => Boolean
        }
    );

    --first we gather background info on the ring (QGorenstein generators, etc.)
    R1 := ring f;
    if isPolynomial f then return isFJumpingExponentPoly( t, f, passOptions( o, { IsLocal, FrobeniusRootStrategy, Verbose } ) );
    S1 := ambient R1;
    I1 := ideal R1;
    canIdeal := canonicalIdeal R1;
    pp := char R1;
    cartIndex := 0;
    fList := { f };
    tList := { t };
    local computedTau;
    local computedHSLGInitial;
    local computedHSLG;
    local baseTau;
    local runningIdeal;
    local a1quot;
    local a1rem;
    ( a1, b1, c1 ) := decomposeFraction( pp, t, NoZeroC => true );
    local locMax;
    if o.IsLocal then (locMax = sub(maxIdeal(S1), R1) ) else (locMax = ideal(0_R1));

    if o.QGorensteinIndex > 0 then cartIndex = o.QGorensteinIndex
    else cartIndex = getDivisorIndex( o.MaxCartierIndex, canIdeal );
    if o.Verbose or debugLevel > 1 then print "isFJumpingExponent: Cartier index determined.";
    h1 := 0_S1;
    --first we do a quick check to see if the test ideal is easy to compute
    if ( pp - 1 ) % cartIndex == 0 then
    (
        if o.Verbose or debugLevel > 1 then print "isFJumpingExponent: cartier index divides p-1.";
        J1 := testElement R1;
        try h1 = QGorensteinGenerator( 1, R1 ) then
        (
            if o.Verbose or debugLevel > 1 then print "isFJumpingExponent: we found a single generating map.";
            computedTau = first testModule( tList, fList, CanonicalIdeal => ideal 1_R1, GeneratorList => { h1 }, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain );
            if o.Verbose or debugLevel > 1 then print concatenate("isFJumpingExponent: testIdeal(f^t) = ", toString(computedTau));
            if isUnitIdeal(computedTau + locMax) then return false;
            --at this point we know that it can't be an F-jumping exponent
            --now we have to run the sigma computation
            baseTau = first testModule( 0/1, 1_R1, CanonicalIdeal => ideal 1_R1, GeneratorList => { h1 }, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain );
            if o.Verbose or debugLevel > 1 then print concatenate("isFJumpingExponent: testIdeal(R) = ", toString(baseTau));
            --the ambient isn't even F-regular
            if a1 > pp^c1 - 1 then
            (
                a1quot = floor( ( a1 - 1 )/( pp^c1 - 1 ) );
                a1rem = a1 - ( pp^c1 - 1 )*a1quot;
                computedHSLGInitial = first FPureModule( { a1rem/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => baseTau, GeneratorList => { h1 } );
                computedHSLG = frobeniusRoot( b1, { ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), a1quot }, { h1, sub( f, S1 ) }, sub( computedHSLGInitial, S1 ) );
            )
            else (
                computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => baseTau, GeneratorList => { h1 } );
                --the e is assumed to be 1 here since we are implicitly doing stuff
                computedHSLG = frobeniusRoot( b1, ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), h1, sub( computedHSLGInitial, S1 ) );
            );
            if o.Verbose or debugLevel > 1 then print concatenate("isFJumpingExponent: testIdeal(f^(t-epsilon)) = ", toString(sub(computedHSLG, R1)));
            if not o.IsLocal then (
                if (sub(computedHSLG, R1) == computedTau) then return false else return true;
                --we figured it out, return the value
            )
            else (
                if (saturate(sub(computedHSLG, R1)) == saturate(computedTau)) then return false else return true;
            )
        )
        else h1 = 0_S1
    );
    --now compute the test ideal in the general way (at least if the index does not divide...)
    if (cartIndex % pp == 0) then error "isFJumpingExponent: This function requires that the Q-Gorenstein index is not divisible by p.";
    gg := first (trim canIdeal)_*;
    dualCanIdeal :=  ideal gg : canIdeal;
    nMinusKX := reflexivePower( cartIndex, dualCanIdeal );
    gensList := (trim nMinusKX)_*;
    gensList2 := apply(gensList, x -> sub(x, S1));

    omegaAmb := sub( canIdeal, S1 ) + ideal R1;
    u1 := frobeniusTraceOnCanonicalModule( I1, omegaAmb );
    if o.Verbose or debugLevel > 1 then
        print "isFJumpingExponent: frobenius trace on canonical module computed.";

    t2 := append( tList, 1/cartIndex );
    local f2;
    runningIdeal = ideal 0_S1;
    for x in gensList do
    (
        f2 = append( fList, x );
        runningIdeal = runningIdeal + first testModule( t2, f2, CanonicalIdeal => canIdeal, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain )
    );

    newDenom := reflexify( canIdeal * dualCanIdeal );
    computedTau = ( runningIdeal * R1 ) : newDenom;
    if o.Verbose or debugLevel > 1 then
        print concatenate("isFJumpingExponent: testIdeal(f^t) = ", toString(computedTau));
    if isUnitIdeal(computedTau + locMax) then return false;
    --at this point we know that this is not a jumping number

    --now we compute the base tau
    runningIdeal = ideal 0_S1;
    for x in gensList do
    (
        runningIdeal = runningIdeal + first testModule( {1/cartIndex}, {x}, CanonicalIdeal => canIdeal, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain )
    );
    baseTau = ( runningIdeal * R1 ) : newDenom;
    if o.Verbose or debugLevel > 1 then
        print concatenate("isFJumpingExponent: testIdeal(R) = ", toString(baseTau));

    ( a1x, b1x, c1x ) := decomposeFraction( pp, 1/cartIndex, NoZeroC => true );
    c2 := lcm(c1, c1x);
    b2 := ceiling(b1/c1x)*c1x; -- this is how many times to apply our version of trace
    scale := pp^(b2-b1);
    if a1 > pp^c1 - 1 then
    (
        a1quot = floor( ( a1 - 1 )/( pp^c1 - 1 ) );
        a1rem = a1 - ( pp^c1 - 1 )*a1quot;
        computedHSLGInitial = sum apply(gensList, x -> first FPureModule( { a1rem/( pp^c1 - 1 ), 1/cartIndex }, { f, x }, CanonicalIdeal => runningIdeal, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy ));
        computedHSLG = sum apply(gensList2, x -> sum( apply(u1, h1 -> frobeniusRoot( b2, { scale*ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), scale*a1quot, a1x*ceiling((pp^b2 - 1)/(pp^c1x - 1)) }, { h1, sub( f, S1 ), x }, sub( computedHSLGInitial, S1 ), FrobeniusRootStrategy => o.FrobeniusRootStrategy ) )));
    )
    else (
        computedHSLGInitial = sum apply(gensList, x -> first FPureModule( { a1/( pp^c1 - 1 ), 1/cartIndex }, { f, x }, CanonicalIdeal => baseTau, GeneratorList => u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy ));
        --the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = sum apply(gensList2, x-> sum( apply(u1, h1->frobeniusRoot( b2, {scale*ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), a1x*ceiling((pp^b2 - 1)/(pp^c1x - 1))}, {h1, x}, sub( computedHSLGInitial, S1 ) ) )));
    );
    if o.Verbose or debugLevel > 1 then
        print concatenate("isFJumpingExponent: testIdeal(f^(t-epsilon)) = ", toString(((computedHSLG * R1 ) : newDenom)));

    if not o.IsLocal then (
        if ( ((computedHSLG * R1 ) : newDenom) == computedTau) then return false else return true;
        --we found the answer
    )
    else(
        if ( saturate(((computedHSLG * R1 ) : newDenom)) == saturate(computedTau)) then return false else return true;
    )
)

isFJumpingExponentPoly = method( Options => { FrobeniusRootStrategy => Substitution, IsLocal => false, Verbose => false } )

isFJumpingExponentPoly ( Number, RingElement ) := o -> ( t, f ) ->
(
    if o.Verbose or debugLevel > 1 then print "isFJumpingExponentPoly: starting.";
    S1 := ring f;
    pp := char S1;
    cartIndex := 1;
    fList := { f };
    tList := { t };
    computedTau := null;
    computedHSLG := null;
    computedHSLGInitial := null;
    local locMax;
    if o.IsLocal then (locMax = maxIdeal(S1)) else (locMax = ideal(0_S1));


    h1 := sub( 1, S1 );
    --first we do a quick check to see if the test ideal is easy to compute
    computedTau = first testModule( tList, fList, CanonicalIdeal => ideal 1_S1, GeneratorList => { h1 }, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => true );
    if o.Verbose or debugLevel > 1 then
        print concatenate("isFJumpingExponentPoly: testIdeal(f^t) = ", toString(computedTau));
    if isUnitIdeal(computedTau + locMax) then return false;

    --now we have to run the sigma computation
    ( a1, b1, c1 ) := decomposeFraction( pp, t, NoZeroC => true );
    if a1 > pp^c1 - 1 then
    (
        a1quot := floor( ( a1-1 )/( pp^c1 - 1 ) );
        a1rem := a1 - ( pp^c1-1 )*a1quot;
        computedHSLGInitial = first FPureModule( { a1rem/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => ideal 1_S1, GeneratorList => { h1 } );
        computedHSLG = frobeniusRoot( b1, { ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), a1quot }, { h1, f }, computedHSLGInitial );
    )
    else (
        computedHSLGInitial = first FPureModule( { a1/( pp^c1 - 1 ) }, { f }, CanonicalIdeal => ideal 1_S1, GeneratorList => { h1 } ); --the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = frobeniusRoot( b1, ceiling( ( pp^b1 - 1 )/( pp - 1 ) ), h1, computedHSLGInitial );
    );
    if o.Verbose or debugLevel > 1 then
        print concatenate("isFJumpingExponentPoly: testIdeal(f^(t-epsilon)) = ", toString(computedTau));
    if not o.IsLocal then (
        not isSubset( computedHSLG, computedTau )
    )
    else(
        not isSubset( saturate(computedHSLG), saturate(computedTau) )
    )
)
