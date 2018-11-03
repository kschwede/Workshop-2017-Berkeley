newPackage( "FThresholds",
Version => "1.0",
Date => "August 17th, 2018",
Authors => {
     {Name => "Erin Bela",
     Email => "ebela@nd.edu"
     },
     {Name => "Alberto F. Boix",
     Email => "alberto.fernandezb@upf.edu"
     },
     {Name => "Juliette Bruce",
     Email => "juliette.bruce@math.wisc.edu",
     HomePage => "https://juliettebruce.github.io/"
     },
     {Name => "Drew Ellingson",
     Email => "drewtell@umich.edu"
     },
     {Name => "Daniel Hernandez",
     Email => "hernandez@ku.edu",
     HomePage => "https://hernandez.faculty.ku.edu"
     },
     {Name => "Zhibek Kadyrsizova",
     Email => "zhibek.kadyrsizova@nu.edu.kz"
     },
     {Name => "Moty Katzman",
     Email => "m.katzman@sheffield.ac.uk",
     HomePage => "http://www.katzman.staff.shef.ac.uk/"
     },
     {Name => "Sara Malec",
     Email => "malec@hood.edu"
     },
     {Name => "Matthew Mastroeni",
     Email => "mmastro@okstate.edu",
     HomePage => "https://mnmastro.github.io/"
     },
     {Name => "Maral Mostafazadehfard",
     Email => "maralmostafazadehfard@gmail.com"
     },
     {Name => "Marcus Robinson",
     Email => "robinson@math.utah.edu"
     },
     {Name => "Karl Schwede",
      Email => "schwede@math.utah.edu",
     HomePage => "http://math.utah.edu/~schwede/"
     },
     {Name => "Dan Smolkin",
     Email => "smolkin@math.utah.edu",
     HomePage => "http://dan.smolk.in"
     },
     {Name => "Pedro Teixeira",
     Email => "pteixeir@knox.edu",
     HomePage => "http://www.knox.edu/academics/faculty/teixeira-pedro.html"
     },
     {Name => "Emily Witt",
     Email => "witt@ku.edu",
     HomePage => "https://witt.faculty.ku.edu"
     }
},
Headline => "A package for calculations of F-thresholds",
DebuggingMode => true,
Reload => true,
AuxiliaryFiles => true,
PackageExports => {"TestIdeals"}
)

export{
    "Attempts",
--F-thresholds computations (MainFunctions.m2)
    "BinaryRecursive",
    "compareFPT",
    "ComputePreviousNus",
    "ContainmentTest",
    "criticalExponentApproximation",
    "fpt",
    "fptApproximation",
    "FRegularityCheck",
    "FrobeniusPower",
    "FrobeniusRoot",
    "ftApproximation",
    "isFJumpingExponent",
    "isFPT",
    "MaxChecks",
    "mu",
    "muList",
    "nu",
    "nuList",
    "Search",
    "StandardPower",
    "UseColonIdeals",
    "UseFSignature",
    "UseSpecialAlgorithms"
}


--loadPackage("TestIdeals", LoadDocumentation => true, Reload=>true);


--*************************************************

--symbols

protect NoStrategy;
protect ReturnMap;
protect IdealStrategy;
protect Section;
protect KnownDomain;
protect IsGraded;
protect ModuleStrategy;

--the following code is take from Divisor.m2

reflexify = method(Options => {Strategy => NoStrategy, KnownDomain=>true, ReturnMap => false});

--the first variant simply reflexifies an ideal

reflexify(Ideal) := Ideal => o->(I1) -> (
    if (o.Strategy == ModuleStrategy) then (
        --the user specified we use the ModuleStrategy
        S1 := ring I1;
        inc := inducedMap(S1^1, I1*(S1^1));
        ddual := Hom(Hom(inc, S1^1), S1^1);
		annihilator(coker ddual)
    )
    else ( --otherwise we use the default ideal strategy
        reflexifyIdeal(I1, KnownDomain=>o.KnownDomain)
    )
);

--an internal function that reflexifies an ideal

reflexifyIdeal = method(Options => {KnownDomain=>true});

reflexifyIdeal(Ideal) := Ideal => o->(I1) -> (
	S1 := ring I1;
	assumeDomain := false;
	if (o.KnownDomain == true) then (assumeDomain = true;) else (assumeDomain = isDomain(S1););
	if (assumeDomain) then (
		if (I1 == ideal sub(0, S1)) then (
			I1
		)
		else(
			x := sub(0, S1);
			i := 0;
			genList := first entries gens I1;
			while ((i < #genList) and (x == sub(0, S1))) do(
				x = genList#i;
				i = i+1;
			);
			ideal(x) : (ideal(x) : I1)
		)

	)
	else (
		inc := inducedMap(S1^1, I1*(S1^1));
		ddual := Hom(Hom(inc, S1^1), S1^1);
		annihilator(coker ddual)
	)
);

--we also reflexify modules

reflexify(Module) := Module => o-> (M1) -> (
	S1 := ring M1;
	if (o.Strategy == IdealStrategy) then (
	    --the user specified we use the ideal strategy, this only works if the module can be embedded as an ideal
	    I1 := embedAsIdeal(M1);
	    I2 := reflexifyIdeal(I1, KnownDomain => o.KnownDomain);
	    if (o.ReturnMap == true) then (
	        inducedMap(I2*S1^1, I1*S1^1)
	    )
	    else (
	        I2*S1^1
	    )
	)
	else (
	    reflexifyModule(M1, ReturnMap => o.ReturnMap)
	)
);

reflexifyModule = method(Options=>{ReturnMap=>false});

reflexifyModule(Module) := Module => o-> (M1) -> (
	S1 := ring M1;
	if (o.ReturnMap == true) then (
	    gensMatrix := gens M1;
	    h := map(M1, source gensMatrix, id_(source gensMatrix));
	    ddh := Hom(Hom(h, S1^1), S1^1);
	    map(target ddh, M1, matrix ddh)
	)
	else (
	    (Hom(Hom(M1, S1^1), S1^1))
	)
);

idealPower = method(); -- it seems to be massively faster to reflexify ideals with few generators than ideals with many generators, at least some of the time...

idealPower(ZZ, Ideal) := Ideal => (n, J) -> (
	genList := first entries gens J;
	ideal( apply(genList, z->z^n))
);

reflexivePower = method(Options=>{Strategy=>IdealStrategy});

reflexivePower(ZZ, Ideal) := Ideal => o -> (n1, I1) -> (
	reflexify(idealPower(n1, I1), Strategy=>o.Strategy)
);

--this method embeds a rank 1 module as a divisorial ideal
--this method is based on and inspired by code originally written by Moty Katzman, earlier versions can be found in
-- http://katzman.staff.shef.ac.uk/FSplitting/ParameterTestIdeals.m2
--under canonicalIdeal

embedAsIdeal = method(Options => {Attempts =>10, IsGraded=>false, ReturnMap=>false, Section=>null});

embedAsIdeal(Module) := Ideal => o -> (M1) -> (
    S1 := ring M1;
	embedAsIdeal(S1, M1, Attempts=>o.Attempts, IsGraded=>o.IsGraded, ReturnMap=>o.ReturnMap, Section=>o.Section)
)

embedAsIdeal(Matrix) := Ideal => o -> (Mat1) -> (
    S1 := ring Mat1;
	embedAsIdeal(S1, Mat1, Attempts=>o.Attempts, IsGraded=>o.IsGraded, ReturnMap=>o.ReturnMap)
)

embedAsIdeal(Ring, Module) := Ideal => o ->(R1, M2) ->(
    if (instance(o.Section, Matrix)) then ( --if we are passing a section
        if (target o.Section == M2) then (
            embedAsIdeal(R1, o.Section, Attempts=>o.Attempts, IsGraded=>o.IsGraded, ReturnMap=>o.ReturnMap)
        )
        else (
            error "embedAsIdeal: the target of the section is not equal to the given module.";
        )
    )
    else(
        internalModuleToIdeal(R1, M2, Attempts=>o.Attempts, IsGraded=>o.IsGraded, ReturnMap=>o.ReturnMap)
    )
)

embedAsIdeal(Ring, Matrix) := Ideal => o->(R1, Mat2) -> (
    internalModuleWithSectionToIdeal(R1, Mat2, Attempts=>o.Attempts, IsGraded=>o.IsGraded, ReturnMap=>o.ReturnMap)
)

internalModuleToIdeal = method(Options => {Attempts=>10, IsGraded=>false, ReturnMap=>false});

internalModuleToIdeal(Ring, Module) := Ideal => o ->(R1, M2) ->
(--turns a module to an ideal of a ring
--	S1 := ambient R1;
	flag := false;
	answer:=0;
	if (M2 == 0) then ( --don't work for the zero module
	    answer = ideal(sub(0, R1));
	    if (o.IsGraded==true) then (
			answer = {answer, degree (sub(1,R1))};
		);
		if (o.ReturnMap==true) then (
		    if (#entries gens M2 == 0) then (
		        answer = flatten {answer, map(R1^1, M2, sub(matrix{{}}, R1))};
		    )
		    else (
			    answer = flatten {answer, map(R1^1, M2, {apply(#(first entries gens M2), st -> sub(0, R1))})};
			);
		);

	    return answer;
	);
--	M2 := prune M1;
--	myMatrix := substitute(relations M2, S1);
--	s1:=syz transpose substitute(myMatrix,R1);
--	s2:=entries transpose s1;
	s2 := entries transpose syz transpose presentation M2;
	h := null;
	--first try going down the list
	i := 0;
	t := 0;
	d1 := 0;
	while ((i < #s2) and (flag == false)) do (
		t = s2#i;
		h = map(R1^1, M2**R1, {t});
		if (isWellDefined(h) == false) then error "internalModuleToIdeal: Something went wrong, the map is not well defined.";
		if (isInjective(h) == true) then (
			flag = true;
			answer = trim ideal(t);
			if (o.IsGraded==true) then (
				--print {degree(t#0), (degrees M2)#0};
				d1 = degree(t#0) - (degrees M2)#0;
				answer = {answer, d1};
			);
			if (o.ReturnMap==true) then (
				answer = flatten {answer, h};
			)
		);
		i = i+1;
	);
	-- if that doesn't work, then try a random combination/embedding
     i = 0;
	while ((flag == false) and (i < o.Attempts) ) do (
		coeffRing := coefficientRing(R1);
		d := sum(#s2, z -> random(coeffRing, Height=>100000)*(s2#z));
       -- print d;
		h = map(R1^1, M2**R1, {d});
		if (isWellDefined(h) == false) then error "internalModuleToIdeal: Something went wrong, the map is not well defined.";
		if (isInjective(h) == true) then (
			flag = true;
			answer = trim ideal(d);
			if (o.IsGraded==true) then (
				d1 = degree(d#0) - (degrees M2)#0;
				answer = {answer, d1};
			);
			if (o.ReturnMap==true) then (
				answer = flatten {answer, h};
			)
		);
        i = i + 1;
	);
	if (flag == false) then error "internalModuleToIdeal: No way found to embed the module into the ring as an ideal, are you sure it can be embedded as an ideal?";
	answer
);


--this variant takes a map from a free module of rank 1 and maps to another rank 1 module.  The function returns the second module as an ideal combined with the element

internalModuleWithSectionToIdeal = method(Options => {Attempts=>10, ReturnMap=>false, IsGraded=>false});

internalModuleWithSectionToIdeal(Ring, Matrix) := Ideal => o->(R1, f1)->
(
	M1 := source f1;
	M2 := target f1;
	if ((isFreeModule M1 == false) or (not (rank M1 == 1))) then error ("internalModuleWithSectionToIdeal: Error, source is not a rank-1 free module";);
	flag := false;
	answer:=0;
	s2 := entries transpose syz transpose presentation M2;
	h := null;
	--first try going down the list
	i := 0;
	t := 0;
	d1 := 0;
	while ((i < #s2) and (flag == false)) do (
		t = s2#i;
		h = map(R1^1, M2**R1, {t});
		if (isWellDefined(h) == false) then error "internalModuleWithSectionToIdeal: Something went wrong, the map is not well defined.";
		if (isInjective(h) == true) then (
			flag = true;
			answer = trim ideal(t);
			if (o.IsGraded==true) then (
				--print {degree(t#0), (degrees M2)#0};
				d1 = degree(t#0) - (degrees M2)#0;
				answer = {answer, d1};
			);
			if (o.ReturnMap==true) then (
				answer = flatten {answer, h};
			);
		);
		i = i+1;
	);
	-- if that doesn't work, then try a random combination/embedding
	while ((flag == false) and (i < o.Attempts) ) do (
		coeffRing := coefficientRing(R1);
		d := sum(#s2, z -> random(coeffRing, Height=>100000)*(s2#z));
		h = map(R1^1, M2**R1, {d});
		if (isWellDefined(h) == false) then error "internalModuleWithSectionToIdeal: Something went wrong, the map is not well defined.";
		if (isInjective(h) == true) then (
			flag = true;
			answer = trim ideal(d);
			if (o.IsGraded==true) then (
				d1 = degree(d#0) - (degrees M2)#0;
				answer = {answer, d1};
			);
			if (o.ReturnMap==true) then (
				answer = flatten {answer, h};
			);
		);
	);

	if (flag == false) then error "internalModuleWithSectionToIdeal: No way found to embed the module into the ring as an ideal, are you sure it can be embedded as an ideal?";
	newMatrix := h*f1;
	flatten {first first entries newMatrix, answer}
);


isDomain = method();

isDomain(Ring) := Boolean => (R1) -> (
	isPrime( ideal(sub(0, R1)))
);

--gets a nonzero generator of an ideal.
getNonzeroGenerator := (I2) -> (
    i := 0;
    flag := false;
    genList := first entries gens I2;
    localZero := sub(0, ring I2);
    while ((i < #genList) and (flag == false)) do (
        if (genList#i != localZero) then (
            flag = true;
        );
        i = i + 1;
    );
    if (flag == true) then (
        genList#(i-1)
    )
    else (
        null
    )
);

isLocallyPrincipalIdeal = method();

--the following function should go elsewhere, it checks whether a given ideal is locally principal (really, invertible).  If it is locally principal, it returns the inverse ideal.
isLocallyPrincipalIdeal(Ideal) := (I2) -> (
    localGen := getNonzeroGenerator(I2);
    if (localGen === null) then (
        return {false, sub(0, ring I2)};
    );
    inverseIdeal := (ideal(localGen) : I2);
    idealProduct := inverseIdeal*I2;
    isLocPrinc := (reflexify(idealProduct) == idealProduct);
    if (isLocPrinc == true) then (
        return {true, inverseIdeal};
    )
    else (
        return {false, sub(0, ring I2)};
    );

);

--*************************************************
--*************************************************
--*************************************************
--*************************************************
--This file is used for doing basic computations
--i.e. things using only lists, numbers, etc.
-- that support other functions in the Fsing
--package.
--*************************************************
--*************************************************
--*************************************************
--*************************************************

--*************************************************
--Basic Manipulations with Numbers
--*************************************************
--===============================================================================

denominator ZZ := x -> 1
numerator ZZ := x -> x

--===============================================================================

--Finds the fractional part of a number.
fracPart = x -> x - floor x

--===============================================================================

--*************************************************
--Information Regarding Factors and Factorization
--*************************************************

--===============================================================================

--Returns a list of factors of a number with repeats.
numberToPrimeFactorList = n ->
(
    prod := factor n;
    flatten apply( toList prod, x -> toList( x#1:x#0 ) )
)

--===============================================================================

--Returns a list of all factors of number.
--Has funny order...
allFactors = n ->
(
     if n < 1 then error "properFactors: expected an integer greater than 1";
     powSet := subsets numberToPrimeFactorList n;
     toList set apply( powSet, x -> product x )
)

--===============================================================================

--*************************************************
--Finding Numbers in Given Range
--*************************************************

--===============================================================================

--This function finds rational numbers in the range of the interval
--with the given denominator
findNumberBetweenWithDenom = ( d, a, b ) ->
(
     A := ceiling( a*d );
     B := floor( b*d );
     toList( A..B )/d
)

--This function finds rational numbers in the range of
--the interval, with a given maximum denominator.
findNumberBetween = ( maxDenom, a, b ) ->
(
    denominators := toList( 1..maxDenom );
    outList := {};
    local d;
    while denominators != {} do
    (
	d = last denominators;
	factors := allFactors d;
	-- remove all factors of d
	denominators = select( denominators, x -> not member( x, factors) );
	outList = outList | findNumberBetweenWithDenom( d, a, b )
    );
    sort unique outList
)

--for backwards compatibility
--findNumberBetween( ZZ, List ) := ( maxDenom, myInterv )-> findNumberBetween( maxDenom, myInterv#0, myInterv#1);

--===============================================================================

--*************************************************
--Manipulations with Vectors
--*************************************************

--===============================================================================


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

--===============================================================================

--*************************************************
--Tests for various types of polynomials
--*************************************************

--===============================================================================

--isPolynomial(F) checks if F is a polynomial
isPolynomial = method( TypicalValue => Boolean )

isPolynomial RingElement := Boolean => F -> isPolynomialRing( ring F )

--===============================================================================

--isPolynomialOverPosCharField(F) checks if F is a polynomial over a field
--of positive characteristic
isPolynomialOverPosCharField = method( TypicalValue => Boolean )

isPolynomialOverPosCharField RingElement := Boolean => F ->
    isPolynomial F and isField( kk := coefficientRing ring F ) and ( char kk ) > 0

--===============================================================================

--isPolynomialOverFiniteField(F) checks if F is a polynomial over a finite field.
isPolynomialOverFiniteField = method( TypicalValue => Boolean )

-- This was reverted so that users with older M2 version could load

--isPolynomialOverFiniteField (RingElement) := Boolean => F ->
--    isPolynomialOverPosCharField( F ) and isFinitePrimeField(coefficientRing ring F)

isPolynomialOverFiniteField RingElement := Boolean => F ->
    isPolynomialOverPosCharField F and  ( try (coefficientRing ring F)#order then true else false )

--===============================================================================

--isPolynomialRingOverFiniteField(R) checks if R is a polynomial over a
-- finite field.
isPolynomialRingOverFiniteField = method( TypicalValue => Boolean )

isPolynomialRingOverFiniteField Ring := Boolean => R ->
    isPolynomialRing R and  (try (coefficientRing R)#order then true else false)

--===============================================================================

--Determines whether a polynomial f is a diagonal polynomial (i.e., of the form
--x_1^(a_1)+...+x_n^(a_n)) over a field of positive characteristic
isDiagonal = method( TypicalValue => Boolean )

isDiagonal RingElement := Boolean => f ->
    isPolynomialOverPosCharField( f ) and
    ( product( exponents( f ), v -> #(positions( v, x -> x != 0 )) ) == 1 )

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

--isBinaryForm(F) checks if F is a homogeneous polynomial in two variables.
--WARNING: what we are really testing is if the *ring* of F is a polynomial ring
-- in two variables, and not whether F explicitly involves two variables.
-- (For example, if F=x+y is an element of QQ[x,y,z], this test will return "false"; if G=x is an element of QQ[x,y], this test will return "true".)
isBinaryForm = method( TypicalValue => Boolean )

isBinaryForm RingElement := Boolean => F ->
    isPolynomial F and numgens ring F == 2 and isHomogeneous F

--===============================================================================

--isNonconstantBinaryForm(F) checks if F is a nonconstant homogeneous polynomial
-- in two variables. See warning under "isBinaryForm".
isNonConstantBinaryForm = method( TypicalValue => Boolean )

isNonConstantBinaryForm RingElement := Boolean => F ->
    isBinaryForm F  and ( degree F )#0 > 0

--===============================================================================

--isLinearBinaryForm(F) checks if F is a linearform in two variables. See warning
--under "isBinaryForm".
isLinearBinaryForm = method( TypicalValue => Boolean )

isLinearBinaryForm RingElement := Boolean => F ->
    isBinaryForm F and ( degree F )#0 == 1

--===============================================================================

--*************************************************
--Miscelaneous
--*************************************************

--===============================================================================

--Finds the x-intercept of a line passing through two points
xInt = ( x1, y1, x2, y2 ) ->
(
    if x1 == x2 then error "xInt: x1==x2 no intersection";
    x1-(y1/((y1-y2)/(x1-x2)))
)

--===============================================================================

-- maxIdeal returns the ideal generated by the variables of a polynomial ring
maxIdeal = method( TypicalValue => Ideal )

maxIdeal PolynomialRing := Ideal => R ->
(
    if not isPolynomialRing R then error "maxIdeal: expected a polynomial ring, or an ideal or element of a polynomial ring";
    monomialIdeal R_*
)

maxIdeal RingElement := Ideal => f -> maxIdeal ring f

maxIdeal Ideal := Ideal => I -> maxIdeal ring I

--===============================================================================

-- isProper and isUnitIdeal check if an ideal is proper or the unit ideal
isUnitIdeal = method( TypicalValue => Boolean )

isUnitIdeal Ideal := Boolean => I ->  isSubset( ideal 1_(ring I), I )

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
    if not isPolynomialOverFiniteField F
        then error "splittingField expects a polynomial over a finite field";
    p := char ring F;
    ord := ( coefficientRing ring F )#order;
    factors := first transpose factorsAndMultiplicities F;
    deg := lcm selectPositive( flatten apply( factors, degree ) );
    GF( p, deg * floorLog( p, ord ) )
)

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

checkOptions ( OptionTable, List ) := (o, L) ->
(
    opts := new HashTable from L;
    scanKeys( opts, k ->
	(
	    if instance( opts#k, VisibleList ) and not member( o#k, opts#k ) then
	        (
	            error ( "checkOptions: value for option " | toString( k ) | " must be an element of " | toString( opts#k ) )
		);
	    if instance( opts#k, Type ) and not instance( o#k, opts#k ) then
	        (
		    error ( "checkOptions: value for option " | toString( k ) | " must be of class " | toString( opts#k ) )
		);
	    if instance( opts#k, Function ) and not opts#k o#k  then
	        (
		    error ( "checkOptions: value for option " | toString( k ) | " is not valid" )
		)
	)
    )
)




--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- CONTENTS
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

---------------------------------------------------------------------------------
-- Nu computations

-- Main functions: nuList, nu, muList, mu

-- Auxiliary Functions: nu1, binarySearch, binarySearchRecursive, linearSearch,
--     testPower, testRoot, testFrobeniusPower, nuInternal

---------------------------------------------------------------------------------
-- FThreshold approximations

-- Main functions: fptApproximation, ftApproximation,
--     criticalExponentApproximation

---------------------------------------------------------------------------------
-- FThreshold computations and estimates

-- Main function: fpt

-- Auxiliary functions: fSig, guessFPT(?)

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
    if not isSubset( I, radical J ) then
        error "nu1: The first ideal is not contained in the radical of the second";
    d := 1;
    while not isSubset( I^d, J ) do d = d + 1;
    d - 1
)

-- for polynomials, we use fastExponentiation
nu1 ( RingElement, Ideal ) := ZZ => ( f, J ) ->
(
    if not isSubset( ideal f, radical J ) then
        error "nu1: The polynomial is not contained in the radical of the ideal";
    d := 1;
    while not isSubset( ideal fastExponentiation( d, f ), J ) do d = d + 1;
    d - 1
)

---------------------------------------------------------------------------------
-- TESTS
---------------------------------------------------------------------------------

-- purpose is to verify containment in Frobenius powers

-- testRoot(J,a,I,e) checks whether J^a is a subset of I^[p^e] by checking whether (J^a)^[1/p^e] is a subset of I
testRoot = ( J, a, I, e ) -> isSubset( frobeniusRoot( e, a, J ), I )

-- testPower(J,a,I,e) checks whether J^a is  a subset of I^[p^e], directly
testPower = method( TypicalValue => Boolean )

testPower ( Ideal, ZZ, Ideal, ZZ ) := Boolean => ( J, a, I, e ) ->
    isSubset( J^a, frobenius( e, I ) )

-- for polynomials, use fastExponentiation
testPower ( RingElement, ZZ, Ideal, ZZ ) := Boolean => ( f, a, I, e ) ->
    isSubset( ideal fastExponentiation( a, f ), frobenius( e, I ) )

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
    while b > a+1 do
    (
	c = floor( (a+b)/2 );
	if testFunction( I, c, J, e ) then b = c else a = c
    );
    a
)

-- Recursive binary search
binarySearchRecursive = ( I, J, e, a, b, testFunction ) ->
(
    if b <= a+1 then return a;
    c := floor( (a+b)/2 );
    if testFunction( I, c, J, e )
        then binarySearchRecursive( I, J, e, a, c, testFunction )
	else binarySearchRecursive( I, J, e, c, b, testFunction )
)

-- Linear search
linearSearch = ( I, J, e, a, b, testFunction ) ->
(
    c := a+1;
    while not testFunction( I, c, J, e ) do c = c+1;
    c-1
)

-- hash table to select search function from option keyword
search := new HashTable from
    {
	Binary => binarySearch,
	BinaryRecursive => binarySearchRecursive,
	Linear => linearSearch
    }

---------------------------------------------------------------------------------
-- OPTION PACKAGES
---------------------------------------------------------------------------------

optMuList :=
{
    UseColonIdeals => false,
    Search => Binary
}

optNuList := optMuList | {ContainmentTest => null, UseSpecialAlgorithms => true}

optMu := optMuList | { ComputePreviousNus => true }
optNu := optNuList | { ComputePreviousNus => true }

---------------------------------------------------------------------------------
-- INTERNAL FUNCTION
---------------------------------------------------------------------------------

nuInternal = optNu >> o -> ( n, f, J ) ->
(
    --------------------
    -- A TRIVIAL CASE --
    --------------------
    -- Return answer in a trivial case (per Blickle-Mustata-Smith convention)
    if f == 0 then return toList( (n+1):0 );

    -----------------
    -- SOME CHECKS --
    -----------------
    -- Verify if option values are valid
    checkOptions( o,
	{
	    ComputePreviousNus => Boolean,
	    ContainmentTest => { StandardPower, FrobeniusRoot, FrobeniusPower, null },
	    Search => { Binary, Linear, BinaryRecursive },
	    UseColonIdeals => Boolean,
	    UseSpecialAlgorithms => Boolean
	}
    );
    -- Check if f is in a polynomial ring over a finite field
    if not isPolynomialRingOverFiniteField ring f then
        error "nuInternal: expected polynomial or ideal in a polynomial ring over a finite field";
    -- Check if f is a principal ideal; if so, replace it with its generator,
    --   so that fastExponentiation can be used
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
	    return apply( n+1, i -> p^i-1 );
        if o.UseSpecialAlgorithms then
        (
	    fpt := null;
	    if isDiagonal g then fpt = diagonalFPT g;
            if isBinomial g then fpt = binomialFPT g;
	    if fpt =!= null then
	        return apply( n+1, i -> p^i*adicTruncation( p, i, fpt ) )
        )
    );

    -----------
    -- SETUP --
    -----------
    searchFct := search#(o.Search);
    conTest := o.ContainmentTest;
    -- choose appropriate containment test, if not specified by user
    if conTest === null then
	conTest = if isPrincipal then FrobeniusRoot else StandardPower;
    testFct := test#(conTest);
    local N;
    nu := nu1( g, J ); -- if f is not in rad(J), nu1 will return an error
    theList := { nu };

    --------------------------------------
    -- WHEN COMPUTE PREVIOUS NUS IS OFF --
    --------------------------------------
    if not o.ComputePreviousNus then
    (
	-- This computes nu in a non-recursive way
	if n == 0 then return theList;
 	N = if isPrincipal or conTest === FrobeniusPower
	     then p^n else (numgens trim J)*(p^n-1)+1;
     	return { searchFct( g, J, n, nu*p^n, (nu+1)*N, testFct ) }
    );
    ---------------------------------
    -- WHEN USE COLON IDEALS IS ON --
    ---------------------------------
    if o.UseColonIdeals and isPrincipal then
    -- colon ideals only work for polynomials
    (
	-- This computes nu recursively, using colon ideals.
	-- Only nu(p)'s are computed, but with respect to ideals other than J
	I := J;
	scan( 1..n, e ->
	    (
		I = I : ideal( fastExponentiation( nu, g ) );
		nu =  last nuInternal( 1, g, I, ContainmentTest => conTest );
	      	theList = append( theList, p*(last theList) + nu );
	      	I = frobenius I
	    )
	)
    )
    else
    ----------------------
    -- EVERY OTHER CASE --
    ----------------------
    (
	N = if isPrincipal or conTest === FrobeniusPower
	     then p else (numgens trim J)*(p-1)+1;
	scan( 1..n, e ->
	    (
		nu = searchFct( g, J, e, p*nu, (nu+1)*N, testFct );
    	       	theList = append( theList, nu )
    	    )
    	)
     );
     theList
)

---------------------------------------------------------------------------------
-- EXPORTED METHODS
---------------------------------------------------------------------------------

nuList = method( Options => optNuList, TypicalValue => List );

nuList ( ZZ, Ideal, Ideal ) := List => o -> ( e, I, J ) ->
    nuInternal( e, I, J, o )

nuList ( ZZ, RingElement, Ideal ) := List => o -> ( e, I, J ) ->
    nuInternal( e, I, J, o )

nuList ( ZZ, Ideal ) :=  List => o -> ( e, I ) ->
    nuList( e, I, maxIdeal I, o )

nuList ( ZZ, RingElement ) := List => o -> ( e, f ) ->
    nuList( e, f, maxIdeal f, o )

nu = method( Options => optNu, TypicalValue => ZZ );

nu ( ZZ, Ideal, Ideal ) := ZZ => o -> ( e, I, J ) ->
    last nuInternal( e, I, J, o )

nu ( ZZ, RingElement, Ideal ) := ZZ => o -> ( e, f, J ) ->
    last nuInternal( e, f, J, o )

nu ( ZZ, Ideal ) := ZZ => o -> ( e, I ) -> nu( e, I, maxIdeal I, o )

nu ( ZZ, RingElement ) := ZZ => o -> ( e, f ) -> nu( e, f, maxIdeal f, o )

-- Mus can be computed using nus, by using ContainmentTest => FrobeniusPower.
-- For convenience, here are some shortcuts:

muList = method( Options => optMuList, TypicalValue => List )

muList ( ZZ, Ideal, Ideal ) := List => o -> (e, I, J) ->
    nuList( e, I, J, o, ContainmentTest => FrobeniusPower )

muList ( ZZ, Ideal ) := List => o -> (e, I) ->
    nuList( e, I, o, ContainmentTest => FrobeniusPower )

muList ( ZZ, RingElement, Ideal ) := List => o -> (e, f, J) ->
    nuList( e, f, J, o, ContainmentTest => FrobeniusPower )

muList ( ZZ, RingElement ) := List => o -> (e, f) ->
    nuList( e, f, o, ContainmentTest => FrobeniusPower )

mu = method( Options => optMu, TypicalValue => ZZ )

mu ( ZZ, Ideal, Ideal ) := ZZ => o -> (e, I, J) ->
    nu( e, I, J, ContainmentTest => FrobeniusPower )

mu ( ZZ, Ideal ) := ZZ => o -> (e, I) ->
    nu( e, I, ContainmentTest => FrobeniusPower )

mu ( ZZ, RingElement, Ideal ) := ZZ => o -> (e, f, J) ->
    nu( e, f, J, ContainmentTest => FrobeniusPower )

mu ( ZZ, RingElement ) := ZZ => o -> (e, f) ->
    nu(e, f, ContainmentTest => FrobeniusPower )

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for approximating, guessing, estimating F-Thresholds and crit exps
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--Approximates the F-pure Threshold
--Gives a list of nu_I(p^d)/p^d for d=1,...,e
fptApproximation = method( TypicalValue => List )

fptApproximation ( ZZ, Ideal ) := List => ( e, I ) ->
(
     p := char ring I;
     nus := nuList( e, I );
     apply( nus, 0..e, (n,k) -> n/p^k )
)

fptApproximation ( ZZ, RingElement ) := List => ( e, f ) ->
    fptApproximation( e, ideal f )

--Approximates the F-Threshold with respect to an ideal J
--More specifically, this gives a list of nu_I^J(p^d)/p^d for d=1,...,e

ftApproximation = method( TypicalValue => List )

ftApproximation ( ZZ, Ideal, Ideal ) := List => ( e, I, J ) ->
(
    if not isSubset( I, radical J ) then
        error "ftApproximation: F-threshold undefined";
    p := char ring I;
    nus := nuList( e, I, J );
    apply( nus, 0..e, (n,k) -> n/p^k )
)

ftApproximation ( ZZ, RingElement, Ideal ) := List => ( e, f, J ) ->
   ftApproximation( e, ideal(f), J )

criticalExponentApproximation = method( TypicalValue => List )

criticalExponentApproximation ( ZZ, Ideal, Ideal ) := List => ( e, I, J ) ->
(
    if not isSubset( I, radical J ) then
        error "criticalExponentApproximation: critical exponent undefined";
    p := char ring I;
    mus := muList( e, I, J );
    apply( mus, 0..e, (n,k) -> n/p^k )
)

criticalExponentApproximation (ZZ, RingElement, Ideal) := List => ( e, f, J ) ->
    criticalExponentApproximation( e, ideal f, J )

--Gives a list of guesses for the F-pure threshold of f.  It returns a list of all numbers in
--the range suggested by nu(e,  ) with maxDenom as the maximum denominator
fptGuessList = ( f, e, maxDenom ) ->
(
    n := nu(e,f);
    p := char ring f;
    findNumberBetween( maxDenom, n/(p^e-1), (n+1)/p^e )
)

----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and Fpt computations.   --
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
     1 - p^( -e * dim( R ) ) * degree( frobenius( e, maxIdeal R ) + ideal( fastExponentiation( a, f ) ) )
)

-- isInteger checks if a rational number is an integer
isInteger := x -> x == floor x

-- guessFPT takes a polynomial f, endpoints a and b of an interval that contains
-- the F-pure threshold of f, and a positive integer that tells the max number
-- of checks the user wants to perform.
-- It returns either fpt(f), if found, or an interval containing it, if not.
-- It currently chooses numbers in the interval with minimal denominator.
-- In the future, different strategies should be implemented (e.g., use
-- only/first denominators that are multiple of the characteristic).
guessFPT := { Verbose => false } >> o -> ( f, a, b, maxChecks ) ->
(
    if o.Verbose then print "\nStarting guessFPT ...";
    -- Check if fpt is the upper bound b
    if isFPT( b, f ) then
    (
        if o.Verbose then print( "\nfpt is the right-hand endpoint." );
        return b
    )
    else if o.Verbose then print "\nThe right-hand endpoint is not the fpt ...";
    -- Check if fpt is the lower bound a
    if maxChecks >= 2 then
        if not isFRegular( a, f ) then
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
    d := 2;
    while counter <= maxChecks do
    (
	-- search for number with minimal denominator in the open interval (A,B)
	while floor(d*B) < ceiling(d*A) or isInteger(d*B) or isInteger(d*A) do
            d = d+1;
        t = ceiling(d*A)/d;
        comp = compareFPT(t,f);
	if comp == 0 then  -- found exact FPT!
	(
	    if o.Verbose then
	        print( "\nguessFPT found the exact value for fpt(f) in try number " | toString( counter ) | "." );
	    return t
	);
        if comp == 1 then B = t; -- fpt < t
	if comp == -1 then A = t; -- fpt > t
	counter = counter + 1
    );
    if o.Verbose then
        print( "\nguessFPT narrowed the interval down to ( " | toString( A ) | ", " | toString( B ) | " ) ..." );
    { A, B }
)

-- The default number of "random" checks to be performed
maxChecks := 3;

-- F-pure threshold estimation, at the origin.
-- e is the max depth to search in.
-- FRegularityCheck is whether the last isFRegularPoly is run
--   (which can take a significant amount of time).
fpt = method(
    Options =>
        {
	    DepthOfSearch => 1,
	    FRegularityCheck => false,
	    MaxChecks => maxChecks,
	    UseSpecialAlgorithms => true,
	    UseFSignature => false,
	    Verbose => false
	}
)

fpt RingElement := o -> f ->
(
    ------------------------------
    -- DEAL WITH A TRIVIAL CASE --
    ------------------------------
    if f == 0 then return 0;

    ---------------------
    -- RUN SEVERAL CHECKS
    ---------------------
    -- Check if option values are valid
    checkOptions( o,
        {
	    DepthOfSearch => ( k -> instance( k, ZZ ) and k > 0 ),
	    FRegularityCheck => Boolean,
	    MaxChecks => ( k -> instance( k, ZZ ) and k >= 0 ),
	    UseSpecialAlgorithms => Boolean,
	    UseFSignature => Boolean,
	    Verbose => Boolean
	}
    );
    -- Check if polynomial has coefficients in a finite field
    if not isPolynomialOverFiniteField f  then
        error "fpt: expected polynomial with coefficients in a finite field";
    -- Check if polynomial is in the homogeneous maximal ideal
    M := maxIdeal f;   -- The maximal ideal we are computing the fpt at
    p := char ring f;
    if not isSubset( ideal f, M ) then
        error "fpt: polynomial is not in the homogeneous maximal ideal";

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
    LB := n/(p^e-1); -- lower bound (because of forbidden intervals)
    UB := (n+1)/p^e; -- upper bound
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
    if o.MaxChecks > 0 then
    (
	guess := guessFPT( f, LB, UB, o.MaxChecks, Verbose => o.Verbose );
	if class guess =!= List then return guess; -- guessFPT was successful
	-- if not sucessful, adjust bounds and their strictness
	( LB, UB ) = toSequence guess;
	strictUB = true;
	if o.MaxChecks >= 2 then strictLB = true
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
    -- FINAL F_REGULARITY CHECK --
    ------------------------------
    if o.FRegularityCheck and not strictLB then
    (
	if o.Verbose then print "\nStarting final check ...";
        if not isFRegular( LB, f ) then
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
	print "\nfpt failed to find the exact answer; try increasing the value of DepthOfSearch or MaxChecks.";
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
	QGorensteinIndex => 0
    },
    TypicalValue => ZZ
)

--gets a nonzero generator of an ideal.
getNonzeroGenerator := I ->
(
    gen := select( 1, I_*, x -> x != 0 );
    if gen === {} then null else first gen
)

isLocallyPrincipalIdeal := I ->
(
    localGen := getNonzeroGenerator I;
    R := ring I;
    if localGen === null then return { false, 0_R };
    inverseIdeal := ideal( localGen ) : I;
    idealProduct := inverseIdeal * I;
    if reflexify idealProduct  == idealProduct then
        return { true, inverseIdeal }
    else return { false, 0_R }
)

--helper function for compareFPT
getDivisorIndex := ( maxIndex, divisorialIdeal ) ->
(
    fflag := false;
    cartIndex := 0;
    curIdeal := null;
    locPrincList := null;
    while not fflag and cartIndex < maxIndex do
    (
        cartIndex = cartIndex + 1;
        curIdeal = reflexivePower( cartIndex, divisorialIdeal );
        locPrincList = isLocallyPrincipalIdeal curIdeal;
        if locPrincList#0 then fflag = true
    );
    if cartIndex <= 0 or not fflag then
        error "getDivisorIndex: Ring does not appear to be Q-Gorenstein; perhaps increase the option MaxCartierIndex.  Also see the documentation for isFRegular.";
    return cartIndex
)

compareFPT(Number, RingElement) := ZZ => o -> (t, f) ->
(
    -- Check if option values are valid
    checkOptions( o,
        {
	    MaxCartierIndex => ZZ,
	    FrobeniusRootStrategy => { Substitution, MonomialBasis },
	    AssumeDomain => Boolean,
	    QGorensteinIndex => ZZ
	}
    );

    --first we gather background info on the ring (QGorenstein generators, etc.)
    R1 := ring f;
    if isPolynomial f then return compareFPTPoly( t, f );
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
    --computedTau := ideal(sub(0, R1));
    if o.QGorensteinIndex > 0 then cartIndex = o.QGorensteinIndex
    else cartIndex = getDivisorIndex(o.MaxCartierIndex, canIdeal);
    h1 := 0_S1;
    --first we do a quick check to see if the test ideal is easy to compute
    if (pp-1)%cartIndex == 0 then
    (
        J1 := testElement R1;
        try h1 = QGorensteinGenerator( 1, R1 ) then
	(
            computedTau = testModule( tList, fList, ideal 1_R1, { h1 }, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain );
            if isUnitIdeal computedTau#0 then return -1
	    --at this point we know that this is not the FPT
        )
        else h1 = 0_S1
    );
    --now compute the test ideal in the general way (if the index does not divide...)
    gg := first (trim canIdeal)_*;
    dualCanIdeal :=  ideal( gg ) : canIdeal;
    nMinusKX := reflexivePower( cartIndex, dualCanIdeal );
    gensList := (trim nMinusKX)_*;

    runningIdeal := ideal 0_R1;
    omegaAmb := sub( canIdeal, S1 ) + ideal R1;
    u1 := frobeniusTraceOnCanonicalModule( I1, omegaAmb );

    t2 := append( tList, 1/cartIndex );
    f2 := fList;

    for x in gensList do
    (
        f2 = append( fList, x );
        runningIdeal = runningIdeal + (testModule( t2, f2, canIdeal, u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain ) )#0;
    );

    newDenom := reflexify( canIdeal * dualCanIdeal );
    computedTau = ( runningIdeal * R1 ) : newDenom;
    if isUnitIdeal computedTau then return -1;
    --at this point we know that this is not the FPT

    --now we have to run the sigma computation
    if h1 != 0_S1 then
    (
        baseTau:= testModule( 0/1, 1_R1, ideal 1_R1, { h1 }, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain );
        if isProper baseTau#0 then
	    error "compareFPT: The ambient ring must be F-regular.";
	    --the ambient isn't even F-regular
        decomposedExponent := decomposeFraction( pp, t, NoZeroC => true );
        (a1,b1,c1) := toSequence decomposedExponent;
        if a1 > (pp^c1-1) then
	(
            a1quot := floor( (a1-1)/(pp^c1-1) );
            a1rem := a1 - (pp^c1-1)*a1quot;
            computedHSLGInitial = HSLGModule( { a1rem/(pp^c1-1) }, { f }, baseTau#0, { h1 } );
            computedHSLG = frobeniusRoot( b1, { ceiling( (pp^b1 - 1)/(pp-1) ), a1quot }, { h1, sub( f, S1 ) }, sub( computedHSLGInitial#0, S1 ) );
        )
        else (
            computedHSLGInitial = HSLGModule( { a1/(pp^c1-1) }, { f }, baseTau#0, { h1 } );
	    --the e is assumed to be 1 here since we are implicitly doing stuff
            computedHSLG = frobeniusRoot( b1, ceiling( (pp^b1-1)/(pp-1) ), h1, sub( computedHSLGInitial#0, S1 ) );
        );
        if isProper( computedHSLG+I1 ) then return 1;
	--the fpt we picked is too big
    )
    else
    --there should be an algorithm that works here
        error "compareFPT:  The current version requires that (p-1)K_R is Cartier (at least for the sigma part of the computation).  This error can also occur for non-graded rings that are Q-Gorenstein if there is a principal ideal that Macaulay2 cannot find the generator of.";
    return 0
    --it is the FPT!
)

compareFPTPoly = method(Options => {FrobeniusRootStrategy => Substitution})

compareFPTPoly(Number, RingElement) := o -> (t, f) -> (
    --first we gather background info on the ring (QGorenstein generators, etc.)
    S1 := ring f;
    pp := char S1;
    cartIndex := 0;
    fList := { f };
    tList := { t };
    local computedTau;
    local computedHSLG;
    local computedHSLGInitial;
    --computedTau := ideal(sub(0, R1));

    h1 := 1_S1;
    --first we do a quick check to see if the test ideal is easy to compute
    computedTau = testModule( tList, fList, ideal 1_S1, { h1 }, o, AssumeDomain => true );
    if isUnitIdeal computedTau#0 then return -1;
    --at this point we know that this is not the FPT

    --now we have to run the sigma computation
    decomposedExponent := decomposeFraction( pp, t, NoZeroC => true );
    (a1,b1,c1) := toSequence decomposedExponent;
    if a1 > (pp^c1-1) then
    (
        a1quot := floor( (a1-1)/(pp^c1-1) );
        a1rem := a1 - (pp^c1-1)*a1quot;
        computedHSLGInitial = HSLGModule( { a1rem/(pp^c1-1) }, { f }, ideal 1_S1, { h1 } );
        computedHSLG = frobeniusRoot( b1, { ceiling( (pp^b1-1)/(pp-1) ), a1quot }, { h1, f }, computedHSLGInitial#0 );
    )
    else
    (
        computedHSLGInitial = HSLGModule( { a1/(pp^c1-1) }, { f }, ideal 1_S1, { h1 } );
	--the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = frobeniusRoot( b1, ceiling( (pp^b1-1)/(pp-1) ), h1, computedHSLGInitial#0 );
    );
    if isProper computedHSLG then return 1;
    --the fpt we picked is too small

    return 0 --it is the FPT!
)

-- isInForbiddenInterval takes a prime number p and a rational number t
-- and checks whether t lies in an interval of the form (a/p^e,a/(p^e-1)),
-- for some e. If it does, it cannot be an FPT in characteristic p.
isInForbiddenInterval = method( TypicalValue => Boolean )

isInForbiddenInterval ( ZZ, QQ ) := Boolean => ( p, t ) ->
(
    if t < 0 or t > 1 then return true;
    (a,b,c) := toSequence decomposeFraction( p, t );
    valid := true;
    e := 1;
    while valid and e <= b+c do
    (
        if floor( (p^e-1)*t ) != p^e * adicTruncation( p, e, t ) then
	    valid = false;
	e = e+1
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
	QGorensteinIndex => 0
    },
    TypicalValue => Boolean
)

-- Dan: We should use the "Origin" option somehow...
isFPT ( Number, RingElement ) := Boolean => o -> ( t, f ) ->
(
    if isInForbiddenInterval( char ring f, t ) then false else
        0 == compareFPT(t/1, f, o )
)

-- isFJumpingExponent determines if a given rational number is an
-- F-jumping exponent
--***************************************************************************
--This needs to be speeded up, like the above function
--***************************************************************************

-- Dan: isn't is safer to have AssumeDomain default to "false" here?
isFJumpingExponent = method(
    Options =>
    {
	MaxCartierIndex => 10,
	FrobeniusRootStrategy => Substitution,
	AssumeDomain=>true,
	QGorensteinIndex => 0
    },
    TypicalValue => Boolean
)

isFJumpingExponent ( Number, RingElement ) := Boolean => o -> ( t, f ) ->
(
    -- Check if option values are valid
    checkOptions( o,
        {
	    MaxCartierIndex => ZZ,
	    FrobeniusRootStrategy => { Substitution, MonomialBasis },
	    AssumeDomain => Boolean,
	    QGorensteinIndex => ZZ
	}
    );

    --first we gather background info on the ring (QGorenstein generators, etc.)
    R1 := ring f;
    if class R1 === PolynomialRing then return isFJumpingExponentPoly(t, f);
    S1 := ambient R1;
    I1 := ideal R1;
    canIdeal := canonicalIdeal R1;
    pp := char R1;
    cartIndex := 0;
    fList := {f};
    tList := {t};
    computedTau := null;
    computedHSLG := null;
    computedHSLGInitial := null;
    --computedTau := ideal(sub(0, R1));

    if o.QGorensteinIndex > 0 then cartIndex = o.QGorensteinIndex
    else cartIndex = getDivisorIndex(o.MaxCartierIndex, canIdeal);
    h1 := 0_S1;
    --first we do a quick check to see if the test ideal is easy to compute
    if (pp-1) % cartIndex == 0 then
    (
        J1 := testElement R1;
        try h1 = QGorensteinGenerator( 1, R1 ) then
            computedTau = testModule(tList, fList, ideal 1_R1, {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain)
        else h1 = 0_S1
    )
    else--there should be an algorithm that works here
        error "isFJumpingExponent:  The current version requires that (p-1)K_R is Cartier (at least for the sigma part of the computation).  This error can also occur for non-graded rings that are Q-Gorenstein if there is a principal ideal that Macaulay2 cannot find the generator of.";

    --now compute the test ideal in the general way (if the index does not divide...)
    if computedTau =!= null then
    ( --this code will be enabled eventually
        gg := first first entries gens trim canIdeal;
        dualCanIdeal := (ideal(gg) : canIdeal);
        nMinusKX := reflexivePower(cartIndex, dualCanIdeal);
        gensList := first entries gens trim nMinusKX;

        runningIdeal := ideal 0_R1;
        omegaAmb := sub(canIdeal, S1) + ideal(R1);
        u1 := (frobeniusTraceOnCanonicalModule(I1, omegaAmb));

        t2 := append(tList, 1/cartIndex);
        f2 := fList;

        for x in gensList do (
            f2 = append(fList, x);
            runningIdeal = runningIdeal + (testModule(t2, f2, canIdeal, u1, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>o.AssumeDomain))#0;
        );

        newDenom := reflexify(canIdeal*dualCanIdeal);
        computedTau = (runningIdeal*R1) : newDenom;
    );
    --now we have to run the sigma computation
    if h1 != 0_S1 then
    (
        baseTau := testModule(0/1, 1_R1, ideal 1_R1, {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain => o.AssumeDomain );
        decomposedExponent := decomposeFraction( pp, t, NoZeroC => true );
        (a1,b1,c1) := toSequence decomposedExponent;
        if a1 > (pp^c1-1) then
	(
            a1quot := floor( (a1-1)/(pp^c1 - 1));
            a1rem := a1 - (pp^c1-1)*a1quot;
            computedHSLGInitial = HSLGModule({a1rem/(pp^c1-1)}, {f}, baseTau#0, {h1});
            computedHSLG = frobeniusRoot(b1, {ceiling( (pp^b1 - 1)/(pp-1) ), a1quot}, {h1, sub(f, S1)}, sub(computedHSLGInitial#0, S1))
        )
        else (
            computedHSLGInitial = HSLGModule({a1/(pp^c1 - 1)}, {f}, baseTau#0, {h1}); --the e is assumed to be 1 here since we are implicitly doing stuff
            computedHSLG = frobeniusRoot(b1, ceiling( (pp^b1 - 1)/(pp-1) ), h1, sub(computedHSLGInitial#0, S1))
        )
    )
    else--there should be an algorithm that works here
        error "isFJumpingExponent:  The current version requires that (p-1)K_R is Cartier (at least for the sigma part of the computation).  This error can also occur for non-graded rings that are Q-Gorenstein if there is a principal ideal that Macaulay2 cannot find the generator of.";
    return not isSubset( computedHSLG, I1 + sub(computedTau, S1) )
)

isFJumpingExponentPoly = method(
    Options => { FrobeniusRootStrategy => Substitution }
)

isFJumpingExponentPoly ( Number, RingElement ) := o -> ( t, f ) ->
(
    S1 := ring f;
    pp := char S1;
    cartIndex := 1;
    fList := {f};
    tList := {t};
    computedTau := null;
    computedHSLG := null;
    computedHSLGInitial := null;
    --computedTau := ideal(sub(0, R1));

    h1 := sub(1, S1);
    --first we do a quick check to see if the test ideal is easy to compute
    computedTau = (testModule(tList, fList, ideal(sub(1, S1)), {h1}, FrobeniusRootStrategy => o.FrobeniusRootStrategy, AssumeDomain=>true))#0;

    --now we have to run the sigma computation
    decomposedExponent := decomposeFraction(pp, t, NoZeroC => true);
    a1 := decomposedExponent#0;
    b1 := decomposedExponent#1;
    c1 := decomposedExponent#2;
    if (a1 > (pp^c1-1)) then(
        a1quot := floor( (a1-1)/(pp^c1 - 1));
        a1rem := a1 - (pp^c1-1)*a1quot;
        computedHSLGInitial = HSLGModule({a1rem/(pp^c1-1)}, {f}, ideal(sub(1, S1)), {h1});
        computedHSLG = frobeniusRoot(b1, {ceiling( (pp^b1 - 1)/(pp-1) ), a1quot}, {h1, f}, computedHSLGInitial#0);
    )
    else (
        computedHSLGInitial = HSLGModule({a1/(pp^c1 - 1)}, {f}, ideal(sub(1, S1)), {h1}); --the e is assumed to be 1 here since we are implicitly doing stuff
        computedHSLG = frobeniusRoot(b1, ceiling( (pp^b1 - 1)/(pp-1) ), h1, computedHSLGInitial#0);
    );

    return (not isSubset(computedHSLG, computedTau));
)


--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- CONTENTS - FPTs of special types of polynomials
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- Main functions: diagonalFPT, binomialFPT, binaryFormFPT

-- Auxiliary Functions: factorOutMonomial, monomialFactor, twoIntersection,
--    allIntersections, isInPolytope, isInInteriorPolytope,
--    polytopeDefiningPoints, maxCoordinateSum, dCalculation, calculateEpsilon
--    setFTData, isInUpperRegion, isInLowerRegion, neighborInUpperRegion, isCP,
--    findCPBelow, binaryFormFPTInternal

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for computing FPTs of diagonal polynomials
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--Given a vector w of rational integers in [0,1], returns a number of digits
-- such that it suffices to check to see if the components of w add without carrying in base p
carryTest = ( p, w ) ->
(
    if any( w, x -> x < 0 or x > 1 ) then
        error "carryTest: Expected the second argument to be a list of rational numbers in [0,1]";
     div := apply( w, x -> decomposeFraction(p, x) );
     c := max (transpose div)#1; --max of second components of div
     v := selectNonzero (transpose div)#2; -- nonzero third components of div
     d := if v === {} then 1 else lcm v;
     c+d+1
)

--===============================================================================

--Given a vector w of rational integers in [0,1], returns the first spot
--e where the the sum of the entries in w carry in base p
firstCarry = ( p, w ) ->
(
    if any( w, x -> x < 0 or x > 1 ) then
        error "firstCarry: Expected the second argument to be a list of rational numbers in [0,1]";
    if product( w ) == 0 then -1 else
    (
	i := 0;
	d := 0;
	while d < p and i < carryTest(p,w) do
	(
	    i = i + 1;
	    d = sum adicDigit( p, i, w )
	);
        if i == carryTest(p,w) then -1 else i
     )
)

--===============================================================================

-- Computes the F-pure threshold of a diagonal hypersurface
-- x_1^(a_1) + ... +x_n^(a_n) using Daniel Hernandez' algorithm

diagonalFPT = method( TypicalValue => QQ )

diagonalFPT RingElement := QQ => f ->
(
    if not isDiagonal f then
        error "diagonalFPT: expected a diagonal polynomial over a field of positive characteristic";
    p := char ring f;
    w := apply( terms f, g -> 1/( first degree g ) );
      -- w = list of reciprocals of the powers of the variables appearing in f
    fc := firstCarry( p, w );
    if fc == -1 then sum w
    else sum( adicTruncation( p, fc-1, w ) ) + 1/p^( fc-1 )
)

--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for computing FPTs of binomials
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

--Given input vectors v={a_1,...,a_n} and w={b_1,...,b_n}, gives the
--corresponding vectors that omit all a_i and b_i such that a_i=b_i
factorOutMonomial = ( v, w ) ->
(
    diffCoords := nonzeroPositions( v-w );
    ( v_diffCoords, w_diffCoords )
)

--Given input vectors v={a_1,...,a_n} and w={b_1,...,b_n}, gives the
--vector of the a_i for which a_i=b_i
monomialFactor = ( v, w ) -> v_( zeroPositions( v-w ) )

--Given two vectors v={v0,v1} and w={w0,w1} in the real plane, finds
--the intersection of the associated lines v0*x+w0*y=1 and v1*x+w1*y=1, if it exists
twoIntersection = ( v, w ) ->
    if ( d := det matrix { v, w } ) != 0 then { w#1 - w#0 , v#0 - v#1 } / d

--Given two vectors v={v0,...vn} and w={w0,...,wn}, list the nonnegative
--intersections of all lines vi*x+wi*y=1 and vj*x+wj*y=1,
--and the intersections of the lines vi*x=1 and wi*y=1 with the axes
allIntersections = ( v, w ) ->
(
    L1 := apply( subsets( #v, 2 ), k -> twoIntersection( v_k, w_k ) );
    L1 = select( L1, x -> x =!= null );
    L2 := apply( selectNonzero v, x -> { 1/x, 0 } );
    L3 := apply( selectNonzero w, x -> { 0, 1/x } );
    select( join( L1, L2, L3 ), x -> ( x#0 >= 0 and x#1 >= 0 ) )
)

--Given a point a=(x,y) in the real plane and two vectors v={v0,...,vn} and
-- w={w0,...,wn}, checks whether a is in the polytope defined by the equations vi*x+wi*y<=1
isInPolytope = ( a, v, w ) -> all( v, w, (i,j) -> i*a#0 + j*a#1 <= 1 )

--Given a point a=(x,y) in the real plane and two vectors
--v={v0,...,vn} and w={w0,...,wn}, checks whether a is in
--the interion of the polytope defined by the equations vi*x+wi*y<=1
isInInteriorPolytope = ( a, v, w ) -> all( v, w, (i,j) -> i*a#0 + j*a#1 < 1 )

--Given two vectors v and w of the same length, outputs
--a list of the defining vectors of the polytope as in isInPolytope
polytopeDefiningPoints = ( v, w ) ->
    select( allIntersections( v, w ), a -> isInPolytope( a, v, w ) )

--Given a list of coordinates in the real plane,
--outputs the one with the largest coordinate sum
maxCoordinateSum = L ->
(
     maxSum := max apply( L, sum );
     first select( L, v -> sum v == maxSum )
)

--Finds the "delta" in Daniel Hernandez's algorithm
--for F-pure thresholds of binomials
dCalculation = ( w, N, p ) ->
(
    i := N + 1;
    d := p;
    while d > p - 2 do
    (
	d = sum( w, x -> adicDigit( p, i, x ) );
	i = i - 1;
    );
    i + 1
)

--Given the "truncation" points  P1 and P2 and two vectors v and w defining the
-- binomial, outputs the "epsilon" in Daniel Hernandez's algorithm for
-- F-thresholds of binomials
calculateEpsilon = ( P1, P2, v, w ) ->
(
    X := 0;
    Y := 0;
    if isInInteriorPolytope( P1, v, w ) then
    	-- find how far we can move from P1 in the x direction
        X = min apply( nonzeroPositions v, i -> (1 - (v#i)*(P1#0) - (w#i)*(P1#1))/(v#i) );
    if isInInteriorPolytope( P2, v, w ) then
    	-- find how far we can move from P2 in the y direction
	Y = min apply( nonzeroPositions w, i -> (1 - (v#i)*(P2#0) - (w#i)*(P2#1))/(w#i) );
    max( X, Y )
)

-- Computes the FPT of a binomial
-- Based on the work of Daniel Hernandez, and implemented by Emily Witt
binomialFPT = method( TypicalValue => QQ )

binomialFPT RingElement := QQ => g ->
(
    if not isBinomial g then
        error "binomialFPT: expected a binomial over a field of positive characteristic";
    p := char ring g;
    ( v, w ) := toSequence exponents g;
    FPT := 0;
    mon := monomialFactor( v, w );
    ( v, w ) = factorOutMonomial( v, w );
    maxPt := maxCoordinateSum( polytopeDefiningPoints( v, w ) );
    if sum maxPt > 1 then FPT = 1 else
    (
	L := firstCarry( p, maxPt );
	if L == -1 then FPT = sum maxPt else
	(
	    d := dCalculation( maxPt, L-1, p );
	    P := adicTruncation( p, d, maxPt );
	    P1 := P + { 0, 1/p^d };
	    P2 := P + { 1/p^d, 0 };
	    FPT = adicTruncation(p, L-1, sum maxPt) + calculateEpsilon(P1,P2,v,w)
     	 )
     );
     monFPT := min apply( selectNonzero mon, x -> 1/x );
     	 -- monFPT = the FPT of the monomial factored out from g;
     	 -- if there are no nonzero terms in mon, min will return infinity
     min( FPT, monFPT )
)



--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
---------------------------------------------------------------------------------
-- Functions for computing FPTs of forms in two variables
---------------------------------------------------------------------------------
--%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

-- Based on the work of Hernandez and Teixeira, and implemented by Teixeira

-*
    Remark: At this point, only commands for computations of F-pure thresholds
    are implemented. Eventually computations of F-thresholds with respect to more
    general ideals will be implemented, and perhaps of more general polynomials.
    Some structures and functions below are already designed to handle such
    greater generality.
*-

-*
    Types and auxiliary commands
*-

-*
    FTData is a HashTable that stores the data necessary in F-threshold
    calculations, for conveniently passing those data from one function
    to another.
    It contains the following keys:
        "ring": the ring of the polynomial in question;
	"char": the characteristic of ring;
	"ideal": the ideal with respect to which we want to compute the F-threshold;
	"gens": the generators of the ideal;
	"polylist": a list of the (pairwise prime) factors of the
	    polynomial in question;
	"numpolys": the number of (pairwise prime) factors.
*-
FTData = new Type of HashTable

-- setFTData takes a list of generators of the ideal or the ideal itself and a
-- list of polynomials, and builds an FTData from them.
-- Currently, this ideal is always the homogeneous maximal ideal.
setFTData = method( TypicalValue => FTData )

setFTData ( List, List ) := FTData => ( gen, polylist ) ->
(
    A := ring gen_0;
    p:= char A;
    new FTData from
    {
	"char" => p,
	"ring" => A,
	"ideal" => ideal gen,
	"gens" => gen,
	"numpolys" => #polylist,
	"polylist" => polylist
    }
)

setFTData ( Ideal, List ) := FTData => ( I, polylist ) ->
    setFTData( I_*, polylist )

-*
    Tests and auxiliary functions
*-

-*
    isInUpperRegion(a,q,S)/isInUpperRegion(u,S) test if the point u=a/q is in
    the upper region attached to S. Suppose I is the ideal of the FTData S
    under consideration and L={L_1,...,L_n} is the "polylist". Then a point
    a/q (where a=(a_1,...,a_n) is a nonnegative integer vector and q a power
    of "char") is in the "upper region" if L_1^(a_1)...L_n^(a_n) is in I^[q];
    otherwise it is in the lower region.
*-
isInUpperRegion = method( TypicalValue => Boolean )

isInUpperRegion ( List, ZZ, FTData ) := Boolean => ( a, q, S ) ->
(
    frob := frobeniusPower( q, S#"ideal" );
    F := product( a, S#"polylist", (i,f) -> fastExponentiation(i,f) );
    (F % frob) == 0
)

isInUpperRegion ( List, FTData ) := Boolean => ( u, S ) ->
    isInUpperRegion append( getNumAndDenom u, S )

-*
    isInLoweRegion(a,q,S)/isInLoweRegion(u,S) test if the point u=a/q is in
    the lower region attached to S.
*-
isInLowerRegion = method( TypicalValue => Boolean )

isInLowerRegion ( List, ZZ, FTData ) := Boolean => ( a, q, S ) ->
    not isInUpperRegion( a, q, S )

isInLowerRegion ( List, FTData ) := Boolean => ( u, S ) ->
    not isInUpperRegion( u, S )

-*
   neighborInUpperRegion(a,q,S)/neighborInUpperRegion(u,S): auxiliary functions
   that, given a point u=a/q in the upper region, try to find a "neighbor" of
   the form (a-e_i)/q that also lies in the upper region. If the search is
   successful, they return the first such neighbor found; otherwise they
   return nothing.
*-
neighborInUpperRegion = method( TypicalValue => Sequence )

neighborInUpperRegion ( List, ZZ, FTData ) := Sequence => ( a, q, S ) ->
(
    if isInLowerRegion( a, q, S ) then
        error "neighborInUpperRegion: expected point in the upper region";
    n := S#"numpolys";
    posEntries := positions( a, k -> k > 0 );
    local candidate;
    for i in posEntries do
    (
	candidate = a - apply( n, j -> if i == j then 1 else 0 );
	-- candidate = a - e_i
       if isInUpperRegion( candidate, q, S ) then return candidate/q
    );
    null
)

neighborInUpperRegion ( List, FTData ) := List => ( u, S ) ->
    neighborInUpperRegion append( getNumAndDenom u, S )

-- findCPBelow(u,S) takes a point u in the upper region attached to S and
-- finds a critical point <= u with the same denominator. This critical point
-- always exist, but if q is large, it can take a long time to find it.
findCPBelow = method( TypicalValue => List )

-- trying a nonrecursive version, to avoid reaching recursion limit
findCPBelow ( List, FTData ) := List => ( pt, S ) ->
(
    if isInLowerRegion( pt, S ) then
        error "findCPBelow: the point must be in the upper region";
    candidate := pt;
    nbr := neighborInUpperRegion( pt, S );
    while nbr =!= null do
    (
        candidate = nbr;
	nbr = neighborInUpperRegion( candidate, S )
    );
    candidate
)

-*
    Computation of FPTs
*-

-*
    binaryFormFPTInternal({a1,...an},S): if S#"polylist={L1,...,Ln} is a list
    of linear forms, binaryFormFPTInternal({a1,...an},S) finds the FPT of the
    polynomial F=L1^(a1)...Ln^(an)
*-
binaryFormFPTInternal = method(
    TypicalValue => QQ,
    Options => { Verbose => false, "Nontrivial" => false }
)

binaryFormFPTInternal ( List, FTData ) := QQ => opt -> ( a, S ) ->
(
    -- Start by dealing with a simple degenerate case
    -- If some multiplicity a_i is "too big", return 1/a_i
    deg := sum a;
    pos := positions( a, k -> k >= deg/2 );
    if pos != {} then
    (
	if opt#Verbose then
	    print( "\nOne of the multiplicities, a_i = " | toString a_(pos_0) | ", is >= degree(F)/2, so fpt(F) = 1/a_i.");
	return  1/a_(pos_0)
    );

    p := S#"char";
    den := denominator( 2/deg );

    local mult;
    -- Nontrivial is set to true when its known that fpt != lct = 2/deg
    if opt#"Nontrivial" then mult = infinity
    else
    (
    	if gcd( S#"char", den) == 1 then mult = multiplicativeOrder( p, den )
	else
	(
	    F := product( S#"polylist", a, (f,i) -> f^i );
	    if isFPT( 2/deg, F ) then
	    (
		if opt#Verbose then print "\nThe fpt is the lct, 2/deg(F).";
		return 2/deg
	    )
	    else mult = infinity
	)
    );

    rng := S#"ring";
    polys := S#"polylist";
    I := S#"ideal";
    ideals := { I };
    e := 0;
    dgt := 0;
    u := 2*a/deg;
    while isProper I and e < mult do
    (
	e = e+1;
	dgt = adicDigit( p, e, u );
	I = frobenius( I ) : product( polys, dgt, (f,k) -> f^k );
	ideals = append( ideals, I )
    );
    if isProper I and e == mult then
    (
	if opt#Verbose then print "\nThe fpt is the lct, 2/deg(F).";
	return 2/deg
    )
    else
    (
	if opt#Verbose then print "\nThe fpt is NOT the lct, 2/deg(F).";
    );
    e0 := e-1;
    S1 := setFTData( ideals_e0, polys );
    cp := findCPBelow( dgt/p, S1 );
    	--if some coordinate of cp is 0, its magnification may not be a CP
    while product cp == 0 and e0 > 0 do
    (
	e0 = e0-1;
        -- zoom out one step and look for CP again
    	S1 = setFTData( ideals_e0, polys );
	cp = findCPBelow( cp/p + adicDigit( p, e0+1, u )/p, S1 )
    );
    cp = cp/p^e0 + adicTruncation( p, e0, u ); -- "zoom out"
    if opt#Verbose then
        print ( "\nThe fpt is determined by the critical point " | toString cp );
    max apply( cp, a, (c,k) -> c/k )
)

-----------------------
binaryFormFPT = method(
    TypicalValue => QQ,
    Options => { Verbose => false }
)

-*
    binaryFormFPT(RingElement)
    FPT(F) computes the F-pure threshold of a form F in two variables.
    KNOWN ISSUE: if the splitting field of F is too big, factor will not work.
*-
binaryFormFPT RingElement :=  QQ => opt ->  F ->
(
   if not isNonConstantBinaryForm F then
       error "binaryFormFPT: a nonconstant homogeneous polynomial in 2 variables is expected";
    -- because factoring is the weakness of this algorithm, we try to avoid it
    -- by first checking if fpt=lct
    deg := (degree F)_0;
    if isFPT( 2/deg, F ) then
    (
	if opt#Verbose then print "\nThe fpt is the lct, 2/deg(F).";
	return 2/deg
    );

    R := ring F;
    vv := R_*;
    kk := splittingField F;
    S := kk( monoid[getSymbol "a", getSymbol "b"] );
    G := sub( F, { vv#0 => (S_*)#0, vv#1 => (S_*)#1 } );
    ( L, m ) := toSequence transpose factorsAndMultiplicities G;
    binaryFormFPTInternal(
	m,
	setFTData(S_*,L),
	Verbose => opt#Verbose,
	"Nontrivial" => true
    )
)

-- binaryFormFPT(List,List)
-- Given a list L={L_1,...,L_n} of linear forms in 2 variables and a list
-- m={m_1,...,m_n} of multiplicities, binaryFormFPT(L,m) returns the F-pure
-- threshold of the polynomial L_1^(m_1)*...*L_n^(m_n).
binaryFormFPT ( List, List ) := QQ => opt -> ( L, m ) ->
(
    -- some checks to see if input makes sense
    if #L != #m then error "binaryFormFPT: expected lists of same length";
    if not uniform L then
        error  "binaryFormFPT: expected the entries of the first argument to be elements of the same ring";
    if not all( L, isLinearBinaryForm ) then
        error  "binaryFormFPT: expected the first argument to be a list of linear forms in two variables";
    if not all( m, x -> ( class x ) === ZZ ) then
        error  "binaryFormFPT: expected the second argument to be a list of positive integers";
    if not all( m, x -> x > 0 ) then
        error  "binaryFormFPT: expected the second argument to be a list of positive integers";

    -- now pass things to binaryFormFPTInternal
    binaryFormFPTInternal(
	m,
	setFTData( gens ring L_0, L ),
	Verbose => opt#Verbose
    )
)


beginDocumentation()



doc ///
    Key
        FThresholds
    Headline
        a package for computing numerical invariants in prime characteristic
    Description
        Text
            The Frobenius endomorphism on a ring of prime characteristic $p$, which sends a ring element to
            its $p$-th power, is a fundamental tool in prime characteristic commutative algebra.
            Kunz has shown that regularity is characterized
            by the behavior of this map, and since then, many other properties of Frobenius have been used to
            measure how {\em far} a ring is from being regular.

            Numerical invariants of rings, and of their elements and ideals, play an
            important role in this endeavor. Of particular focus are the $F$-pure threshold, and more generally,
            $F$-thresholds.

            However, the computation of these numerical invariants
            can be quite subtle, and at the same time computationally complex. In partnership with the package @TO TestIdeals@,
            which provides some important functionality for researchers in positive characteristic
            commutative algebra, the package @TO FThresholds@ implements known algorithms, as well as new methods,
            to estimate and compute numerical invariants in prime characteristic.
    SeeAlso
        TestIdeals
///



doc ///
    Key
        BinaryRecursive
    Headline
        an option value specifying a binary recursive search method
    Description
        Text
            a value for the option {\tt Search} to specify a binary recursive search method
    SeeAlso
        nu
        nuList
///

doc ///
    Key
        compareFPT
        (compareFPT, Number, RingElement)
        [compareFPT, MaxCartierIndex]
        [compareFPT, FrobeniusRootStrategy]
        [compareFPT, AssumeDomain]
        [compareFPT, QGorensteinIndex]
    Headline
        checks whether a given number is less than, greater than, or equal to the F-pure threshold
    Usage
        compareFPT(t, f)
    Inputs
        t:QQ
        f:RingElement
            an element of a $\mathbb{Q}$-Gorenstein ring
        FrobeniusRootStrategy => Symbol
            an option passed to computations in the TestIdeals package
        AssumeDomain => Boolean
        MaxCartierIndex => ZZ
        QGorensteinIndex => ZZ
    Description
        Text
            This function returns {\tt -1} if {\tt t} is less than the F-pure threshold of {\tt f}.
            It returns {\tt 1} if {\tt t} is greater than the F-pure threshold {\tt f}.
            Finally, it returns {\tt 0} if it is equal to the F-pure threshold.
        Example
            R = ZZ/7[x,y];
            f = y^2-x^3;
            compareFPT(1/2, f)
            compareFPT(5/6, f)
            compareFPT(6/7, f)
        Text
            This function can also check the FPT in singular (but still strongly $F$-regular) ring,
            so long as the ring is also Q-Gorenstein of index dividing $p-1$.  In the future we hope
            that this functionality will be extended to all Q-Gorenstein rings.  In the following exam,
            $x$ defines a Cartier divisor which is twice one of the rulings of the cone.
        Example
             R = ZZ/5[x,y,z]/ideal(x*y-z^2);
             f = x;
             compareFPT(1/3, f)
             compareFPT(1/2, f)
             compareFPT(13/25, f)
    SeeAlso
        fpt
        isFPT
///

doc ///
    Key
        ComputePreviousNus
    Headline
        an option to compute nu-values recursively
    Description
        Text
            An option for the function @TO nu@ (or @TO mu@) to compute its values recursively.

            If {\tt true}, then $\nu$-values (or $\mu$-values) are computed in succession.
            Otherwise, another method can be applied.

            Can take on only Boolean values. Default value is {\tt true}.
    SeeAlso
        mu
        nu
///

doc ///
    Key
        ContainmentTest
    Headline
        an option to specify the containment test used
    Description
        Text
            Specifies which test is used to check containment of powers of ideals.
            Valid values are {\tt FrobeniusPower}, {\tt FrobeniusRoot}, and {\tt StandardPower}.
            Default for @TO nu@ and @TO nuList@ applied to a polynomial is {\tt FrobeniusRoot},
            and applied to an ideal is {\tt StandardPower}.
    SeeAlso
        nu
        nuList
///

doc ///
    Key
        criticalExponentApproximation
        (criticalExponentApproximation,ZZ,Ideal,Ideal)
        (criticalExponentApproximation,ZZ,RingElement,Ideal)
    Headline
        gives a list of approximates of a critical exponent
    Usage
        criticalExponentApproximation(e,I,J)
        criticalExponentApproximation(e,f,J)
    Inputs
        e:ZZ
        I:Ideal
        J:Ideal
        f:RingElement
    Outputs
        :List
    Description
        Text
            This returns a list of $\mu_I^J(p^d)/p^d$, or $\mu_f^J(p^d)/p^d$, for $d = 0,\ldots,e$.

            As $d$ approaches $\infty$, the sequence of these terms converges to the critical exponent of $I$, or of $f$, with respect to $J$.
        Example
             R = ZZ/5[x,y];
             I = ideal(x^2,x*y,y^2);
             m = ideal(x,y);
             criticalExponentApproximation(2,I,m)
             f = x^2 + y^3;
             criticalExponentApproximation(2,f,m)
    SeeAlso
        ftApproximation
        fptApproximation
        mu
        muList
///

doc ///
     Key
         fpt
         (fpt, RingElement)
         [fpt, DepthOfSearch]
         [fpt, FRegularityCheck]
         [fpt, MaxChecks]
         [fpt, UseFSignature]
         [fpt, UseSpecialAlgorithms]
         [fpt, Verbose]
     Headline
         attempts to compute the F-pure threshold of a polynomial at the origin
     Usage
         fpt(f)
         fpt(L, m)
     Inputs
         f:RingElement
             a polynomial with coefficients in a finite field
         L:List
             containing forms in two variables
         m:List
             containing positive integers
         DepthOfSearch => ZZ
             specifies the power of the characteristic to be used in a search for the F-pure threshold
         FRegularityCheck => Boolean
             specifies whether to check if the final lower bound is the $F$-pure threshold of $f$
         MaxChecks => ZZ
             specifies the number of "guess and check" attempts to make
         UseFSignature => Boolean
             specifies whether to use the $F$-signature function and a secant line argument to attempt to improve the $F$-pure threshold estimate
         UseSpecialAlgorithms => Boolean
             specifies whether to check if $f$ is diagonal, binomial, or a binary form (i.e., a standard-graded homogeneous polynomial in 2 variables), and then apply appropriate algorithms
	 Verbose => Boolean
	     requests verbose feedback
     Outputs
        :List
            which contains the endpoints of an interval containing lower and upper bounds for the $F$-pure threshold of $f$
        Q:QQ
            the $F$-pure threshold of $f$
     Description
          Text
              The function fpt tries to find the exact value for the $F$-pure threshold of a polynomial $f$ at the origin, and returns that value, if possible.
              Otherwise, it returns lower and upper bounds for the $F$-pure threshold.
         Example
              ZZ/5[x,y,z];
              fpt( x^3+y^3+z^3+x*y*z )
              fpt( x^5+y^6+z^7+(x*y*z)^3 )
         Text
              If the option @TO UseSpecialAlgorithms@ is set to @TO true@ (the default value), then {\tt fpt} first checks whether $f$ is a diagonal polynomial, a binomial, or a form in two variables, respectively.
              If it is one of these, algorithms of D. Hernandez, or D. Hernandez and P. Teixeira, are executed to compute the $F$-pure threshold of $f$.
         Example
             fpt( x^17+y^20+z^24 ) -- a diagonal polynomial
             fpt( x^2*y^6*z^10+x^10*y^5*z^3 ) -- a binomial
             ZZ/5[x,y];
             fpt( x^2*y^6*(x+y)^9*(x+3*y)^10 ) -- a binary form
         Text
             When no special algorithm is available or @TO UseSpecialAlgorithms@ is set to @TO false@, {\tt fpt} computes $\nu = \nu_f(p^e)$ (see @ TO nu@), where $e$ is the value of the option @TO DepthOfSearch@, which conservatively defaults to 1.
              At this point, we know that the $F$-pure threshold of $f$ lies in the closed interval [$\nu/(p^e-1),(\nu+1)/p^e$], and the subroutine {\tt guessFPT} is called to make some "educated guesses" in an attempt to find the $F$-pure threshold, or at least narrow down the above interval.

	      The number of "guesses" is controlled by the option @TO MaxChecks@, which conservatively defaults to 3.
	      If @TO MaxChecks@ is set to 0, {\tt guessFPT} is bypassed.
	      If @TO MaxChecks@ is set to at least 1, then a first check is run to verify whether the right-hand endpoint $(\nu+1)/p^e$ of the above interval is the $F$-pure threshold.
         Example
             f = x^2*(x+y)^3*(x+3*y^2)^5;
             fpt( f, MaxChecks => 0 ) -- a bad estimate
             fpt( f, MaxChecks => 0, DepthOfSearch => 3 ) -- a better estimate
             fpt( f, MaxChecks => 1, DepthOfSearch => 3 ) -- the right-hand endpoint (nu+1)/p^e is the fpt
         Text
	      If @TO MaxChecks@ is set to at least 2 and the right-hand endpoint $(\nu+1)/p^e$ is not the $F$-pure threshold, a second check is run to verify whether the left-hand endpoint $\nu/(p^e-1)$ is the $F$-pure threshold.
	 Example
 	      f = x^6*y^4+x^4*y^9+(x^2+y^3)^3;
	      fpt( f, MaxChecks => 1, DepthOfSearch => 3 )
	      fpt( f, MaxChecks => 2, DepthOfSearch => 3 ) -- the left-hand endpoint is the fpt
	 Text
	      If neither endpoint is the $F$-pure threshold, and @TO MaxChecks@ is set to more than 2, additional checks are performed at numbers in the interval.
	      A number in the interval with minimal denominator is selected, and @TO compareFPT@ is used to test that number.
	      If that "guess" is correct, its value is returned; otherwise, the information returned by @TO compareFPT@ is used to narrow down the interval, and this process is repeated as many times as specified by @TO MaxChecks@.
	 Example
              f = x^3*y^11*(x+y)^8*(x^2+y^3)^8;
	      fpt( f, DepthOfSearch => 3, MaxChecks => 2 )
	      fpt( f, DepthOfSearch => 3, MaxChecks => 3 ) -- an additional check sharpens the estimate
	      fpt( f, DepthOfSearch => 3, MaxChecks => 4 ) -- and one more finds the exact answer
	 Text
              If guessFPT is unsuccessful and @TO UseFSignature@ is set to @TO true@, the fpt function proceeds to use the convexity of the $F$-signature function and a secant line argument to attempt to narrow down the interval bounding the $F$-pure threshold.
         Example
              f = x^5*y^6*(x+y)^9*(x^2+y^3)^4;
	      fpt( f, DepthOfSearch => 3 )
	      fpt( f, DepthOfSearch => 3, UseFSignature => true )
	      numeric ooo
	      numeric ooo -- UseFSignature sharpened the estimate a bit
	 Text
              When @TO FRegularityCheck@ is set to @TO true@ and no exact answer has been found, a final check is run (if necessary) to verify whether the final lower bound for the $F$-pure threshold is the exact answer.
         Example
	      f = (x+y)^4*(x^2+y^3)^6;
	      fpt( f, MaxChecks => 2, DepthOfSearch => 3 )
	      fpt( f, MaxChecks => 2, DepthOfSearch => 3, UseFSignature => true ) -- using FSignatures the answer improves a bit
 	      fpt( f, MaxChecks => 2, DepthOfSearch => 3, UseFSignature => true, FRegularityCheck => true ) -- FRegularityCheck finds the answer
         Text
	      The computations performed when @TO UseFSignature@ and @TO FRegularityCheck@ are set to @TO true@ are often slow, and often fail to improve the estimate, and for this reason, these options should be used sparingly.
	      It is often more effective to increase the values of @TO MaxChecks@ or @TO DepthOfSearch@, instead.
         Example
              f = x^7*y^5*(x+y)^5*(x^2+y^3)^4;
 	      timing numeric fpt( f, DepthOfSearch => 3, UseFSignature => true, FRegularityCheck => true )
	      timing numeric fpt( f, MaxChecks => 5, DepthOfSearch => 3 ) -- a better answer in less time
	      timing fpt( f, DepthOfSearch => 4 ) -- the exact answer in even less time
	 Text
              As seen in several examples above, when the exact answer is not found, a list containing the endpoints of an interval containing the $F$-pure threshold of $f$ is returned.
              Whether that interval is open, closed, or a mixed interval depends on the options passed; if the option @TO Verbose@ is set to @TO true@, the precise interval will be printed.
         Example
              f = x^7*y^5*(x+y)^5*(x^2+y^3)^4;
              fpt( f, DepthOfSearch => 3, UseFSignature => true, Verbose => true )
	 Text
              The computation of the $F$-pure threshold of a binary form $f$ requires factoring $f$ into linear forms, and can sometimes hang when attempting that factorization. For this reason, when a factorization is already known, the user can pass to fpt a list containing all the pairwise prime linear factors of $f$ and a list containing their respective multiplicities.
         Example
              L = {x, y, x+y, x+3*y};
              m = {2, 6, 9, 10};
              fpt(L, m)
	      fpt( x^2*y^6*(x+y)^9*(x+3*y)^10 )
    SeeAlso
              fptApproximation
              nu
              nuList
///

doc ///
     Key
         fptApproximation
         (fptApproximation,ZZ,Ideal)
         (fptApproximation,ZZ,RingElement)
     Headline
         gives a list of terms in the sequence whose limit defines the F-pure threshold
     Usage
          fptApproximation(e,I)
          fptApproximation(e,f)
     Inputs
         e:ZZ
         I:Ideal
         f:RingElement
     Outputs
         :List
     Description
        Text
            This returns a list consisting of terms whose limit defines the $F$-pure threshold of $I$, or of $f$.

            This list consists of $\nu_I(p^d)/p^d$, or $\nu_f(p^d)/p^d$, for $d = 0,\ldots,e$.
        Example
            R = ZZ/13[x,y];
            I = ideal(x^2, y);
            fptApproximation(2,I)
            f = x^5 + x^2*y^3;
            fptApproximation(2,f)
    SeeAlso
        fpt
        ftApproximation
        nu
        nuList
        criticalExponentApproximation
///

doc ///
    Key
        FRegularityCheck
    Headline
        an option to use an F-regularity check to find an F-pure threshold
    Description
        Text
            This option for the function @TO fpt@ specifies that, in a situation where the exact $F$-pure threshold was not found, a final check be run to determine whether the final lower bound for the $F$-pure threshold is actually its exact value.
            Only takes on Boolean values.
    SeeAlso
        fpt
///

doc ///
    Key
        FrobeniusPower
    Headline
        an option value to consider containment of Frobenius powers of ideals
    Description
        Text
            a value for the option {\tt ContainmentTest} to consider containment of Frobenius powers of ideals
    SeeAlso
        nu
        nuList
///

doc ///
    Key
        FrobeniusRoot
    Headline
        an option value to consider containment of Frobenius roots of ideals
    Description
        Text
            a value for the option {\tt ContainmentTest} to consider containment of Frobenius roots of ideals
    SeeAlso
        nu
        nuList
///

doc ///
     Key
         ftApproximation
         (ftApproximation,ZZ,Ideal,Ideal)
         (ftApproximation,ZZ,RingElement,Ideal)
     Headline
         gives a list of terms in the sequence whose limit defines an F-threshold
     Usage
         ftApproximation(e,I,J)
         ftApproximation(e,f,J)
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
         :List
     Description
         Text
            This returns a list of terms of the sequence whose limit defines the $F$-threshold of $I$, or of $f$, with respect to $J$.

            This list consists of $\nu_I^J(p^d)/p^d$, or $\nu_f^J(p^d)/p^d$, for $d = 0,\ldots,e$.
         Example
              R = ZZ/7[x,y];
              I = ideal(x^5, y^5);
              J = ideal(x^2, y^3);
              ftApproximation(2,I,J)
              f = x^3*y^2+x^5*y;
              ftApproximation(2,f,J)
///

doc ///
     Key
        isFJumpingExponent
        (isFJumpingExponent,Number,RingElement)
        [isFJumpingExponent, AssumeDomain]
        [isFJumpingExponent, FrobeniusRootStrategy]
        [isFJumpingExponent, MaxCartierIndex]
        [isFJumpingExponent, QGorensteinIndex]
     Headline
        Checks whether a given number is an F-jumping number
     Usage
         isFJumpingExponent(t,f,Verbose=>V)
     Inputs
         t:QQ
         f:RingElement
            an element of a $\mathbb{Q}$-Gorenstein ring
         V:Boolean
         AssumeDomain => Boolean
         FrobeniusRootStrategy => Symbol
            an option passed to computations in the TestIdeals package
         MaxCartierIndex => ZZ
         QGorensteinIndex => ZZ
     Outputs
        :Boolean
     Description
        Text
            Returns true if {\tt t} is an F-jumping number of {\tt f}, otherwise it returns false. This function only works if the ambient ring of $R$ is $\mathbb{Q}$-Gorenstein

            If the ambient ring of {\tt f} is a domain, the option {\tt AssumeDomain} can be set to {\tt true} in order
            to speed up the computation. Otherwise {\tt AssumeDomain} should be set to {\tt false}.

            Let $R$ be the ambient ring of $f$. If the Gorenstein index of $R$ is known, one should set the option {\tt QGorensteinIndex} to the Gorenstein index of $R$. Otherwise
            the function attempts find the Gorenstein index of $R$, assuming it is between 1 and {\tt MaxCartierIndex}. By default, {\tt MaxCartierIndex} is set to {\tt 10}.

            The option {\tt FrobeniusRootStrategy} is passed to an internal call of @TO frobeniusRoot@. The two valid values of {\tt FrobeniusRootStrategy} are {\tt Substitution} and {\tt MonomialBasis}.
        Example
            R = ZZ/5[x,y];
            f =  x^4 + y^3 + x^2*y^2;
            isFJumpingExponent(7/12,f)
            isFJumpingExponent(4/5,f)
            isFJumpingExponent(5/6,f)
            isFJumpingExponent(11/12,f)
    SeeAlso
        isFPT
///

doc ///
     Key
        isFPT
        (isFPT,Number,RingElement)
        [isFPT, FrobeniusRootStrategy]
        [isFPT, AssumeDomain]
        [isFPT, MaxCartierIndex]
        [isFPT, QGorensteinIndex]
     Headline
        Checks whether a given number is the F-pure threshold
     Usage
          isFPT(t,f,Verbose=>V,Origin=>W)
     Inputs
        t:QQ
        f:RingElement
        V:Boolean
        W:Boolean
        FrobeniusRootStrategy => Symbol
            an option passed to computations in the TestIdeals package
        AssumeDomain => Boolean
        MaxCartierIndex => ZZ
        QGorensteinIndex => ZZ
     Outputs
        :Boolean
     Description
        Text
            Returns true if t is the $F$-pure threshold, otherwise it returns false.  If {\tt Origin} is true, it only checks it at the homogeneous maximal ideal.

            The options are the same as in @TO compareFPT@.
        Example
            R = ZZ/11[x,y];
            f = x^3+y^2;
            isFPT(9/11,f)
     SeeAlso
        compareFPT
        fpt
        isFJumpingExponent
///

doc ///
     Key
          MaxChecks
     Headline
          specifies the number of "guess and check" attempts to make in an F-pure threshold computation
     Description
          Text
              an option for function @TO fpt@, which specifies the number of "guess and check" tries to be performed.
	      The first number checked is always the upper bound $(\nu+1)/p^e$, where $e$ is the value of the option @TO DepthOfSearch@ and $\nu=\nu_f(p^e)$.
	      The second number checked is always the lower bound $\nu/(p^e-1)$.
     SeeAlso
        fpt
        nu
///

doc ///
     Key
         mu
         (mu,ZZ,Ideal,Ideal)
         (mu,ZZ,Ideal)
         (mu,ZZ,RingElement,Ideal)
         (mu,ZZ,RingElement)
         [mu, ComputePreviousNus]
         [mu, Search]
         [mu, UseColonIdeals]
     Headline
        computes the largest Frobenius power of an ideal not contained in a specified Frobenius power
     Usage
          mu(e,I,J)
          mu(e,I)
          mu(e,f,J)
          mu(e,f)
          ComputePreviousNus => Boolean
          Search => Symbol
          UseColonIdeals => Boolean
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
         ComputePreviousNus => Boolean
             specifies whether to compute {\tt nu(d,I,J)} for $d = 0, \cdots, e-1$ to aid in the computation of {\tt mu(e,I,J)}
         Search => Symbol
            specifies the strategy in which to search for the largest integer $n$
            such that the $n$-th generalized Frobenius power of $I$ is not contained in some specified Frobenius power of $J$.
         UseColonIdeals => Boolean
             specifies whether to use colon ideals in a recursive manner when computing {\tt mu(e,I,J)}
     Outputs
        :ZZ
          the $e$-th value $\mu$ associated to the $F$-threshold or $F$-pure threshold
     Description
        Text
            Given an ideal $I$ in a polynomial ring $k[x_1, \ldots, x_n]$, {\tt mu(e, I, J)} or {\tt mu(e, f, J)} outputs the
            maximal integer $N$ such that the $N$-th generalized Frobenius power of $I$, or $f^N$,
            is not contained in the $p^e$-th Frobenius power of $J$.
        Example
            R = ZZ/3[x,y];
            I = ideal(x^2, x+y);
            J = ideal(x, y^2);
            mu(2,I,J)
            mu(3,I)
            mu(3,x^3+y^3,J)
     SeeAlso
        nu
        muList
///

doc ///
     Key
         muList
         (muList,ZZ,Ideal,Ideal)
         (muList,ZZ,Ideal)
         (muList,ZZ,RingElement,Ideal)
         (muList,ZZ,RingElement)
         [muList, Search]
         [muList, UseColonIdeals]
     Headline
          computes a list of mu-values associated to a given F-threshold or F-pure threshold
     Usage
          muList(e,I,J)
          muList(e,I)
          muList(e,f,J)
          muList(e,f)
          Search => Symbol
          UseColonIdeals => Boolean
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
         Search => Symbol
            specifies the strategy in which to search for the largest integer $n$
            such that the $n$-th generalized Frobenius power of $I$ is not contained in some specified Frobenius power of $J$.
         UseColonIdeals => Boolean
             specifies whether to use colon ideals in a recursive manner when computing {\tt mu(e,I,J)}
     Outputs
        :List
          a list of the $e$-th $\nu$-values for $e = 0,\ldots,d$
     Description
        Text
            Given an ideal $I$ in a polynomial ring $k[x_1,\ldots,x_n]$, this function computes {\tt mu(d, I, J)}
            or {\tt mu(d,f,J)} recursively for $d = 0,\ldots,e$.
            In other words, calling {\tt muList} is the same as calling @TO nuList@ with the option {\tt ComparisonTest}
            set to {\tt FrobeniusPower}.
        Example
            R = ZZ/3[x,y];
            I = ideal(x^2, x+y);
            J = ideal(x, y^2);
            muList(2,I,J)
            muList(3,I)
            muList(3,x^3+y^3,J)
     SeeAlso
        mu
        nuList
///

doc ///
     Key
         nu
         (nu,ZZ,Ideal,Ideal)
         (nu,ZZ,Ideal)
         (nu,ZZ,RingElement,Ideal)
         (nu,ZZ,RingElement)
         [nu, ComputePreviousNus]
         [nu, ContainmentTest]
         [nu, Search]
         [nu, UseColonIdeals]
     Headline
        computes the largest power of an ideal not contained in a specified Frobenius power
     Usage
          nu(e,I,J)
          nu(e,I)
          nu(e,f,J)
          nu(e,f)
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
         ComputePreviousNus => Boolean
             specifies whether to compute {\tt nu(d,I,J)} for $d = 0, \cdots, e-1$ to aid in the computation of {\tt nu(e,I,J)}
         ContainmentTest => Symbol
             specifies the manner in which to verify the containment of a power of $I$ in some specified Frobenius power of $J$
         Search => Symbol
            specifies the strategy in which to search for the largest integer $n$ such that $I^n$ is not contained in some specified Frobenius power of $J$.
         UseColonIdeals => Boolean
             specifies whether to use colon ideals in a recursive manner when computing {\tt nu(e,I,J)}
     Outputs
        :ZZ
          the $nu$-invarants whose normalized limits compute the $F$-pure threshold, and more generally, $F$-thresholds.
     Description
        Text
            Consider a field $k$ of characteristic $p>0$, and an ideal $J$ in the polynomial ring $S = k[x_1, \ldots, x_d]$.
            If $f$ is a polynomial contained in the radical of $J$, then the command {\tt nu(e, f, J)} outputs the maximal exponent
            $n$ such that $f^n$ is not contained in the $p^e$-th Frobenius power of $J$.  More generally, if $I$ is an ideal contained in the
            radical of $J$, then {\tt nu(e, I, J)} outputs the maximal integer exponent $n$ such that $I^n$ is not contained in the
            $p^e$-th Frobenius power of $J$.

            These numbers are denoted $\nu_f^J(p^e)$ and $\nu_I^J(p^e)$, respectively, in the literature, and were originally defined in the paper
            "F-thresholds and Bernstein-Sato Polynomials" by Mustata, Takagi, and Watanabe.
        Example
            S=ZZ/11[x,y];
            I=ideal(x^2+y^3, x*y);
            J=ideal(x^2,y^3);
            nu(1,I,J)
            f=x*y*(x^2+y^2);
            nu(1,f,J)
        Text
            When the ideal $J$ is omitted from the argument, it is assumed to be the homogeneous maximal ideal.
        Example
            S=ZZ/17[x,y,z];
            f=x^3+y^4+z^5;
            J=ideal(x,y,z);
            nu(2,f)
            nu(2,f,J)
        Text
            It is well-known that if $q=p^e$ for some nonnegative integer $e$, then $\nu_I^J(qp) = \nu_I^J(q) p + L$, where
            the error term $L$ is nonnegative, and can explicitly bounded from above in terms of $p$, and the number of
            generators of $I$ and $J$ (e.g., it is at most $p-1$ when $I$ is principal).  This relation implies that when searching
            for {\tt nu(e+1,I,J)}, it is always safe to start at $p$ times {\tt nu(e,I,J)}, and one needn't search too far past this number.

            The option {\tt ComputePreviousNus}, whose default value is {\tt true}, exploits this observation, and computes {\tt nu(d,I,J)}
            for $d = 0, \cdots, e-1$ to aid in the computation of {\tt nu(e,I,J)}.  It usually leads to faster computations.
        Example
            S=ZZ/79[x,y];
            f=x^5+x^4*y+x^3*y^2+x^2*y^3+x*y^4+y^5; -- a homogeneous polynomial of degree 5 in x,y
            time nu(10,f)
            time nu(10,f, ComputePreviousNus=>false)
        Text
            The valid values for the option {\tt ContainmentTest} are {\tt FrobeniusPower, FrobeniusRoot}, and {\tt StandardPower}.
            The default value of this option depends on what is passed to {\tt nu}.  Indeed, by default, {\tt ContainmentTest} is set to
            {\tt FrobeniusRoot} if {\tt nu} is passed a ring element $f$, and is set to {\tt StandardPower} if {\tt nu} is passed an ideal $I$.
            We describe the consequences of setting {\tt ContainmentTest} to each of these values below.

            First, if {\tt ContainmentTest} is set to {\tt StandardPower}, then the ideal containments that occur when computing
            {\tt nu(e,I,J)} are verified directly.  That is, the standard power $I^n$ is first computed, and a check is then run to see if
            it lies in the $p^e$-th Frobenius power of $J$.

            Alternately, if {\tt ContainmentTest} is set to {\tt FrobeniusRoot}, then the ideal containments that occur when computing
            {\tt nu(e,I,J)} are verified using Frobenius Roots.  That is, the $p^e$-th Frobenius root of $I^n$ is first computed, and
            a check is then run to see if it lies in $J$.  The output is unaffected, but this option often speeds up computations.
        Example
            ZZ/11[x,y,z];
            f=x^3+y^3+z^3+x*y*z;
            time nu(3,f) -- ContainmentTest is set to frobeniusRoot, by default
            time nu(3,f,ContainmentTest=>StandardPower)
        Text
            Finally, when {\tt ContainmentTest} is set to {\tt FrobeniusPower}, then instead of producing the invariant $\nu_I^J(p^e)$ as defined above,
            {\tt nu(e,I,J, ContainmentTest=>FrobeniusPower)} instead outputs the maximal integer $n$ such that the $n$-th Frobenius power of $I$ is not contained in the $p^e$-th Frobenius
            power of $J$.  Here, the $n$-th Frobenius power of $I$, when $n$ is a nonnegative integer, is as defined in the paper "Frobenius Powers" by
            Hernandez, Teixeira, and Witt.  In particular, {\tt nu(e,I,J)} and {\tt nu(e,I,J, ContainmentTest => FrobeniusPower)} need not agree!  However,
            they will when $I$ is a principal ideal.  We note that the output of {\tt nu(e,I,J, ContainmentTest => FrobeniusPower)} is the same as that of
            {\tt mu(e,I,J)}.
        Example
            ZZ/3[x,y];
            M=ideal(x,y);
            nu(3,M^5)
            nu(3,M^5,ContainmentTest=>FrobeniusPower)
            mu(3,M^5) -- should produce the same output as preceding command
        Text
            The function {\tt nu} works by searching through list of integers $n$ and checking containments of $I^n$ in a specified Frobenius power of $J$.
            The option {\tt Search} specifies the search algorithm used to do so search for the exponent $n$ among a list of possibilities.
            Valid values for {\tt Search} are {\tt Binary}, the default value, {\tt BinaryRecursive}, and {\tt Linear}.
        Example
            ZZ/17[x,y];
            M=ideal(x,y);
            time nu(2,M,M^2,Search=>Binary)
            time nu(2,M,M^2,Search=>BinaryRecursive)
            time nu(2,M,M^2,Search=>Linear)
        Text
            The option {\tt UseColonIdeals} specifies whether or not {\tt nu} uses colon ideals to compute $\nu$ in an iterative way.
--to do:  Add example that illustrates the difference.  If we can't find one, maybe remove this option.
        Example
            ZZ/5[x,y,z];
            f = 2*x^2*y^3*z^8+2*x^4*z^9+2*x*y^7*z^4;
            time nu( 5, f ) --Use ColonIdeals is set to false, by default
            time nu( 5, f, UseColonIdeals => true )
    SeeAlso
        mu
        nuList
///

doc ///
     Key
         nuList
         (nuList,ZZ,Ideal,Ideal)
         (nuList,ZZ,Ideal)
         (nuList,ZZ,RingElement,Ideal)
         (nuList,ZZ,RingElement)
         [nuList, ContainmentTest]
         [nuList, Search]
         [nuList, UseColonIdeals]
     Headline
          computes a list of nu-values associated to a given F-threshold or F-pure threshold
     Usage
          nuList(e,I,J)
          nuList(e,I)
          nuList(e,f,J)
          nuList(e,f)
          ContainmentTest => Symbol
              specifies the containment test used
          Search => Symbol
          UseColonIdeals => Boolean
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
        :List
          a list of the $e$-th $\nu$-values for $e = 0,\ldots,d$
     Description
        Text
            Given an ideal $I$ in a polynomial ring $k[x_1,\ldots,x_n]$, this function computes a list with indices
            $e = 0,\ldots,d$, and whose $e$-th entry is the function @TO nu@ applied to the input.
        Example
            S=ZZ/7[x,y];
            I=ideal(x^3+y, x^2*y);
            J=ideal(x^2,y);
            nuList(2,I,J)
            f=y + x^3;
            nuList(2,f,J)
     SeeAlso
        nu
///

doc ///
     Key
          Search
     Headline
          an option to specify the search method
     Description
          Text
              An option for functions @TO nu@ and @TO nuList@ (and @TO mu@ and @TO muList@) to specify
              the order in which ideal the containment of powers are computed.

              Valid values are
              {\tt Binary}, {\tt BinaryRecursive}, and {\tt Linear}.
     SeeAlso
          nu
          nuList
///

doc ///
    Key
        StandardPower
    Headline
        an option value to consider containment of standard power of an ideal in Frobenius power of another ideal
    Description
        Text
            a value for the option {\tt ContainmentTest} to consider containment of the standard power of an ideal in the
            Frobenius power of another ideal
    SeeAlso
        nu
        nuList
///

doc ///
     Key
          UseColonIdeals
     Headline
          an option to use colon ideals to compute nus in an iterative way
     Description
          Text
              An option for @TO nu@ and @TO nuList@ (and @TO mu@ and @TO muList@) to use colon ideals to compute nus in an iterative way.

              Valid values are {\tt true} and {\tt false}.
     SeeAlso
          nu
          nuList
///

doc ///
    Key
        UseFSignature
    Headline
        whether to use the F-signature function in the search for an F-pure threshold
    Description
        Text
            This option for the function @TO fpt@ specifies that the convexity of the $F$-signature function and a secant line argument be used, in an attempt to narrow down the interval bounding the $F$-pure threshold.
            Only takes on Boolean values.
    SeeAlso
        fpt
///

doc ///
     Key
          UseSpecialAlgorithms
     Headline
          an option to check whether the input is a diagonal polynomial, binomial, or binary form
     Description
          Text
              An option for the function @TO fpt@ to check whether the input is a diagonal polynomial, a binomial,
              or a binary form.
              If {\tt true}, the function @TO fpt@ first checks whether the input
              is a diagonal polynomial, a binomial, or a binary form (i.e., a homogeneous polynomial in two variables).
              If it is,
              the function @TO fpt@ applies specialized algorithms of D. Hernandez, or D. Hernandez and P. Teixeira.

              Can take on only Boolean values.
              Default value is {\tt true}.
     SeeAlso
          fpt
///


doc ///
     Key
     	binomialFPT
     Headline
        computes the F-pure threshold of a binomial polynomial
     Usage
     	 binomialFPT(f)
     Inputs
		f:RingElement
     Outputs
         :QQ
     Description
	Text
	    Returns the F-pure threshold of a binomial in a polynomial ring.  This is based on the work of Daniel Hernandez.
///

doc ///
     Key
     	diagonalFPT
     Headline
        computes the F-pure threshold of a diagonal polynomial
     Usage
     	 diagonalFPT(f)
     Inputs
		f:RingElement
     Outputs
         :QQ
     Description
	Text
	    Returns the F-pure threshold of a diagonal hypersurface in a polynomial ring.  This is based on the work of Daniel Hernandez.
///


doc ///
     Key
     	binaryFormFPT
         (binaryFormFPT,RingElement)
         (binaryFormFPT,List,List)
     Headline
         computes the F-pure threshold of a form in two variables
     Usage
     	  binaryFormFPT(G), binaryFormFPT(factors,multiplicities)
     Inputs
	factors:List
	    which contains the linear factors of a form G in two variables
	multiplicities:List
	    which contains the multiplicities of those linear factors in G
	G:RingElement
	    a form in two variables
     Outputs
        :QQ
     Description
	Text
	    binaryFormFPT computes the F-pure threshold of a homogeneous polynomial G
	    	in two variables.
	Example
	    R = ZZ/3[x,y];
	    G = x^5*y^2-x^3*y^4+x*y^6-y^7;
	Text
	    The method used requires factoring G into linear forms in some extension of the base field. If the user knows such a factorization beforehand, the alternate call binaryFormFPT(factors,multiplicities) can be used for improved performance.
	Example
	    R = ZZ/5[x,y];
	Text
	    This is based on the work of Daniel Hernandez and Pedro Teixeira.
///


doc ///
     Key
     	isBinomial
     Headline
        Checks whether a polynomial is binomial.
     Usage
     	 isBinomial(f)
     Inputs
		f:RingElement
     Outputs
         :Boolean
     Description
	Text
	    Returns true if f is a binomial, otherwise returns false.
///

doc ///
     Key
     	isDiagonal
     Headline
        Checks whether a polynomial is diagonal.
     Usage
     	 isDiagonal(f)
     Inputs
		f:RingElement
     Outputs
         :Boolean
     Description
	Text
	    Returns true if f is a diagonal, otherwise returns false.  Recall f is called diagonal if it is of the form x_1^(a_1)+...+x_n^(a_n) up to renumbering of the variables.
///
