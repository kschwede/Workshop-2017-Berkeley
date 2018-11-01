--*************************************************
--*************************************************
--This is the revised (and cleaned up) version
--of the TestIdeals.m2 package, which has been under
--continuous development since the Wake Forest
--Macaulay2 workshop of August 2012.
--TestIdeals.m2 and FThresholds.m2 broke off from
--the original package, called PosChar.m2
--*************************************************
--*************************************************

--version history
--0.2 first public version
--0.2a added AssumeDomain options to isFRegular and isFRational
--1.0 first complete version
--protect QGorensteinIndex;
--protect MaxCartierIndex;
--protect DepthOfSearch;
--protect FrobeniusPowerStrategy;

newPackage( "TestIdeals",
Version => "1.0",
Date => "8/17/2018, 2018",
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
     Email => "zhikadyr@umich.edu"
     },
     {Name => "Mordechai Katzman",
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
     HomePage => "http://cohenmacaulay.life"
     },
     {Name => "Pedro Teixeira",
     Email => "pteixeir@knox.edu",
     HomePage => "http://www.knox.edu/academics/faculty/teixeira-pedro.html"
     },
     {Name=> "Emily Witt",
     Email => "witt@ku.edu",
     HomePage => "https://witt.faculty.ku.edu"
     }
},
Headline => "A package for calculations of singularities in positive characteristic",
DebuggingMode => true,
Reload => true,
AuxiliaryFiles=>true,
PackageExports=>{"Depth"}
)

export{
--BasicFunctions (BasicFunctions.m2)
    "adicExpansion",
    "adicDigit",
    "adicTruncation",
    "decomposeFraction",
    "floorLog",
    "multiplicativeOrder",
    "NoZeroC", --option to force certain behavior from a function

--ethRootFunctions (EthRoots.m2)
    "ascendIdeal",
    "ascendModule",
    "AscentCount",
    "FrobeniusRootStrategy",
    "frobeniusRoot",
    "MonomialBasis",
    "Substitution",

--Frobenius Powers (frobeniusPowers.m2)
    "fastExponentiation",
    "frobenius",
    "frobeniusPower",
    "FrobeniusPowerStrategy",
    "Naive",
    "Safe",

-- parameterTestIdeal.m2
    "AssumeCM", --an option for function, if true, then the function will do less work.
    "AssumeReduced", --an option telling functions to assume a ring is reduced.
    "AssumeNormal", --an option telling functions to assume a ring is normal.
    "AssumeDomain", --an option telling functions to assume a ring is a domain.
    "canonicalIdeal", --Karl (still needs more tests / documentation), this is based on Moty's old code.
    "frobeniusTraceOnCanonicalModule", --Karl (this is Moty's find u function, but it returns a list if Macaulay2 doesn't identify 1 element).
    "isCohenMacaulay", --Karl (added recently, if anyone has ideas to improve this...)
    "isFRational", --Karl (added recently).
    "IsLocal", --an option for isCohenMacaulay, isFRational, etc.
    "testModule", --Karl (this subsumes a bunch of older functions)
    "parameterTestIdeal",

-- Finjective.m2
    "HSLGModule", --produces the non-F-injective module, ie the submodule of the canonical module
    "isFInjective",
    "CanonicalStrategy", --how to check F-injectivity on the canonical module (Ext or Katzman)
    "Katzman", --an option for CanonicalStrategy

-- testIdeals.m2
    "QGorensteinGenerator", --Karl (this finds y such that I^{[p^e]} : I = (y) + I^{[p^e]}, if it exists) **Documented**
    "testElement", --Karl (my students Marcus and Dan did some improvements on this recently, it doesn't compute the whole Jacobian, it just looks at random minors until it finds a good one, it can be much much faster) **Documented**
    "MaxCartierIndex", --the cartier index limfindAllCompatibleIdealsit in the test ideal method
    "testIdeal", --Karl (the new version)
    "QGorensteinIndex", --if you already know the Q-Gorenstein index, you can pass it
    "DepthOfSearch",
    "isFRegular",
    "isFPure",
    "compatibleIdeals" ---MK
}


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
--===================================================================================

denominator( ZZ ) := x -> 1

numerator( ZZ ) := x -> x

--===================================================================================

--Finds the fractional part of a number.
fracPart = x -> x - floor(x)

--===================================================================================

--Computes floor(log_b x), correcting problems due to rounding.
floorLog = method( TypicalValue => ZZ )

floorLog ( ZZ, ZZ ) := ZZ => ( b, x ) ->
(
    if b <= 1 then error "floorLog: expected the first argument to be greater than 1";
    if x <= 0 then error "floorLog: expected the second argument to be positive";
    if x < b then return 0;
    flog := floor( log_b x );
    while b^flog <= x do flog = flog + 1;
    flog - 1
)

--===================================================================================

multiplicativeOrder = method( TypicalValue => ZZ )

--eulerphi := n -> value(apply(factor n, i-> (i#0-1)*((i#0)^(i#1-1))))
--cyclicOrdPGroup := (pp, nn) -> ( return (factor(pp-1))*(new Power from {pp, (nn-1)}) );

--Finds the multiplicative order of a modulo b.
multiplicativeOrder( ZZ, ZZ ) := ZZ => ( a, b ) ->
(
    if gcd( a, b ) != 1 then error "multiplicativeOrder: Expected numbers to be relatively prime.";
    if b==1 then return 1;
    maxOrder := lcm(apply(toList apply(factor b, i-> factor ((i#0-1)*((i#0)^(i#1-1)))), tt -> value tt));
    primeFactorList := sort unique apply( subsets( flatten apply(toList factor maxOrder, myPower -> apply(myPower#1, tt->myPower#0))), tt -> product tt);
--    potentialOrderList := sort unique flatten  apply(flatten apply(toList apply(toList factor b, tt -> cyclicOrdPGroup(tt#0, tt#1)), tt -> toList tt), myPower -> subsets apply(myPower#1, tt->myPower#0));
    i := 0;
    while (i < #primeFactorList) do (
        if (powermod(a, primeFactorList#i, b) == 1) then return primeFactorList#i;
        i = i + 1;
    );
    error "Something went wrong, multiplicativeOrder failed to find the multiplicative order";
)

--===================================================================================

decomposeFraction = method( TypicalValue => List, Options => { NoZeroC => false } );

-- This function takes in a fraction t and a prime p and spits out a list
-- {a,b,c}, where t = a/(p^b*(p^c-1))
-- if c = 0, then this means that t = a/p^b
--alternately, if NoZeroC => true, then we will always write t = a/p^b(p^c - 1)
--even if it means increasing a.
decomposeFraction( ZZ, Number ) := List => o -> ( p, t ) ->
(
    t = t/1;
    if not isPrime( p ) then error "decomposeFraction: first argument must be a prime number.";
    a := numerator t; -- finding a is easy, for now
    den := denominator(t);
    b := 1;
    while den % p^b == 0 do b = b+1;
    b = b-1;
    temp := denominator( t*p^b );
    local c;
    if (temp == 1) then c = 0 else
    (
        c = multiplicativeOrder( p, temp );
        a = lift( a*(p^c-1)/temp, ZZ ); -- fix a
    );
    if o.NoZeroC and c == 0 then
    (
        a = a*(p-1);
        c = 1;
    );
    {a,b,c}
)

--decomposeFraction( ZZ, ZZ ) := List => o -> (p, t) -> decomposeFraction(p, t/1, o)


--===================================================================================

--*************************************************
--Base p-expansions
--*************************************************

--===================================================================================

adicDigit = method( )

--Gives the e-th digit of the non-terminating base p expansion of x in [0,1].
adicDigit ( ZZ, ZZ, QQ ) := ZZ => ( p, e, x ) ->
(
    if p <= 1 then error "adicDigit: Expected first argument to be greater than 1";
    if e <= 0 then error "adicDigit: Expected second argument to be positive";
    if x < 0 or x > 1 then error "adicDigit: Expected last argument in [0,1]";
    if x == 0 then return 0;
    lift( ( adicTruncation(p, e, x) - adicTruncation(p, e-1, x) ) * p^e, ZZ )
)

adicDigit ( ZZ, ZZ, ZZ ) := ZZ => ( p, e, x ) -> adicDigit( p, e, x/1 )

--Creates list containing e-th digits of non-terminating base p expansion of list of numbers.
adicDigit ( ZZ, ZZ, List ) := ZZ => ( p, e, u ) -> apply( u, x -> adicDigit( p, e, x ) )

--===================================================================================

adicExpansion = method( );

--Computes the terminating base p expansion of a positive integer.
--Gives expansion in reverse... so from left to right it gives
--the coefficient of 1, then of p, then of p^2, and so on

adicExpansion( ZZ, ZZ ) := List => ( p, N ) ->
(
    if p <= 1 then error "adicExpansion: Expected first argument to be greater than 1";
    if N < 0 then error "adicExpansion: Expected second argument to be nonnegative";
    if N < p then { N } else prepend( N % p, adicExpansion( p, N // p ) )
    -- would this be faster if it were tail-recursive? we could do this w/ a helper function.
)

--Special case for adic expansion of integers 0 or 1
adicExpansion( ZZ, ZZ, ZZ ) := List => ( p, e, x ) -> adicExpansion( p, e, x/1 )

--Creates a list of the first e digits of the non-terminating base p expansion of x in [0,1].
adicExpansion( ZZ, ZZ, QQ ) := List => ( p, e, x ) ->
(
    if p <= 1 then error "adicExpansion: Expected first argument to be greater than 1";
    if x < 0 or x > 1 then error "adicExpansion: Expected x in [0,1]";
    apply( e, i -> adicDigit( p, i+1, x ) )
)

--===================================================================================

adicTruncation = method( )

--Gives the e-th truncation of the non-terminating base p expansion of a rational
-- number, unless that number is zero.

adicTruncation ( ZZ, ZZ, QQ ) := QQ => ( p, e, x ) ->
(
    if p <= 1 then error "adicTruncation: Expected first argument to be greater than 1";
    if e < 0 then error "adicTruncation: Expected second argument to be nonnegative";
    if x < 0 then error "adicTruncation: Expected third argument to be nonnegative (or a list of nonegative numbers)";
    if x == 0 then 0 else ( ceiling( p^e*x ) - 1 ) / p^e
)

adicTruncation( ZZ, ZZ, ZZ ) := List => ( p, e, x ) -> adicTruncation( p, e, x/1 )

--truncation threads over lists.
adicTruncation ( ZZ, ZZ, List ) := List => ( p, e, u ) ->
    apply( u, x -> adicTruncation( p, e, x ) )

--===================================================================================

--- write n=a*p^e+a_{e-1} p^{e-1} + \dots + a_0 where 0\leq a_j <p
--- DS: so it's just like doing adicExpansion but giving up after p^e and just returning whatever number's left
--- DS: this could be merged with adicExpansion. Should it be?
--- note: I changed the calling order here should change to be consistent with adicExpansion
--- The change I made was switching the order of the first two arguments
baseP1 = ( p, n, e ) ->
(
    a:=n//(p^e);
    answer:=1:a; -- this generates the list (a)
    m:=n-a*(p^e);
    f:=e-1;
    while (f>=0) do
    (
        d:=m//(p^f);
        answer=append(answer,d);
        m=m-d*(p^f);
        f=f-1;
    );
    answer
)

--===================================================================================

--*************************************************
--Tests for various types of polynomials
--*************************************************
--===================================================================================

--isPolynomial(F) checks if F is a polynomial
isPolynomial = method( TypicalValue => Boolean )

isPolynomial (RingElement) := Boolean => F -> isPolynomialRing( ring F )

--===================================================================================

--isPolynomialOverPosCharField(F) checks if F is a polynomial over a field
--of positive characteristic
isPolynomialOverPosCharField = method( TypicalValue => Boolean )

isPolynomialOverPosCharField (RingElement) := Boolean => F ->
    isPolynomial F and isField( kk := coefficientRing ring F ) and ( char kk ) > 0

--===================================================================================

--isPolynomialOverFiniteField(F) checks if F is a polynomial over a finite field.
isPolynomialOverFiniteField = method( TypicalValue => Boolean )

isPolynomialOverFiniteField (RingElement) := Boolean => F ->
    isPolynomialOverPosCharField( F ) and  (coefficientRing ring F)#?order

--===================================================================================


--isPolynomialOverPrimeField(F) checks if F is a polynomial over ZZ/p.
isPolynomialOverPrimeField = method( TypicalValue => Boolean )

isPolynomialOverPrimeField (RingElement) := Boolean => F ->
    isPolynomial( F ) and  (coefficientRing ring F) === ZZ/(char ring F)

-- use isFinitePrimeField

--===================================================================================


--===================================================================================

--*************************************************
--Miscelaneous
--*************************************************

--===================================================================================

-- maxIdeal returns the ideal generated by the variables of a polynomial ring
maxIdeal = method( TypicalValue => MonomialIdeal )

maxIdeal ( PolynomialRing ) := MonomialIdeal => R -> monomialIdeal R_*

maxIdeal ( QuotientRing ) := MonomialIdeal => R -> ideal R_*

--Not used
--maxIdeal ( RingElement ) := Ideal => f -> maxIdeal (ring f)

maxIdeal ( Ideal ) := MonomialIdeal => I -> maxIdeal ring I

--===================================================================================

-- passOptions selects a subset of options from an OptionTable
passOptions = method()

passOptions ( OptionTable, List ) := (o, L) ->
    new OptionTable from apply( L, k -> k => o#k )

    --*************************************************
    --*************************************************
    --This file is used for doing the [1/p^e] operation
    --in the sense of Blickle-Mustata-Smith.
    --This operation is also called I_e in Katzman or
    --simply the image of
    --M \subseteq \Hom_R(R^{1/p^e}, R) -> R
    --under evaluation at 1.
    --*************************************************
    --*************************************************

    -------------------------------------------------------
    ---------- List of functions in this file -------------
    -----------------(as of 2017-05-17)--------------------
    -------------------------------------------------------
    -- frobeniusRoot
    -- getFieldGenRoot
    -- frobeniusRootMonStrat
    -- frobeniusRootSubStrat
    -- frobeniusRootRingElements
    -- frobeniusRootRingElements
    -- ascendIdeal
    -- getExponents
    -- mEthRootOfOneElement
    -- mEthRoot
    -- Mstar
    -------------------------------------------------------
    -------------------------------------------------------
    -------------------------------------------------------

    --if  ((not (class Fsing === Package)) and (not (class TestIdeals === Package))) then (
    --    needs "BasicFunctions.m2" -- maybe this should be removed
    --                          -- when we publish this package
    --)

    frobeniusRoot = method(Options => {FrobeniusRootStrategy => Substitution});
    --frobeniusRoot takes two strategy options: Substitution and MonomialBasis
    --The second strategy seems to generally be faster for computing I^[1/p^e] when e = 1, especially for polynomials of
    --high degree, but slower for larger e.
    -- Dan: I wonder if this is because getFieldGen is not optimized? It's called many times per
    -- generator of the ideal in the monomial strategy. Though I see it's also called for the
    -- substitution strategy...

    frobeniusRoot ( ZZ, Ideal ) := Ideal => opts -> (e,I) -> (
        if (not e >= 0) then (error "frobeniusRoot: Expected first argument to be a nonnegative integer.");
        R := ring I;
        if (class R =!= PolynomialRing) then (error "frobeniusRoot: Expected an ideal in a PolynomialRing.");
        p := char R;
        k := coefficientRing(R);
        if ((k =!= ZZ/p) and (class(k) =!= GaloisField)) then (error "frobeniusRoot: Expected the coefficient field to be ZZ/p or a GaloisField.");

        q := k#order;
        --Gets the cardinality of the base field.
        G := I_*;
        --Produces a list of the generators of I.
        if #G == 0 then ideal(0_R)
        else if opts.FrobeniusRootStrategy == MonomialBasis then (
    	    L := sum( apply( G, f -> frobeniusRootMonStrat(e,p,q,k,f,R) ) );
        	L = first entries mingens L;
    	    ideal(L)
    	)
        else frobeniusRootSubStrat(e,p,q,k,I,R)
    )

    -----------------------------------------------------------------------------

    frobeniusRoot ( ZZ, MonomialIdeal ) := Ideal => opts -> (e,I) -> (
         R := ring I;
         p := char R;
         G := I_*;
         if #G == 0 then ideal( 0_R ) else ideal( apply( G, f -> R_((exponents(f))#0//p^e )))
    )

    ------------------------------------------------------------------------------

    frobeniusRoot(ZZ, List, List) := opts -> (e, exponentList, idealList) -> (
        --idealList is a list of ideals and/or ring elements.
        --exponentList is a list of exponents we're taking these ideals/elemetns to

        --include the following line to set a break point:
        --error "break here";
    --    if (#idealList > 0) then (
    --        if (instance(idealList#0, RingElement)) then (
    --            return
    --        );
    --    );
        I := null;
        if e == 0 then (
            I = idealList#0^(exponentList#0);
            for j from 1 to length(idealList) - 1 do I = I*(idealList#j)^(exponentList#j);
            return I;
        );

        R := ring(idealList#0);
        p := char(R);
        minGensList := apply(idealList, jj -> (if (class jj === Ideal) then #(first entries mingens (jj)) else 1 ));

        -- find max n such that a - (n-1)p > m*p. This is the number of copies of $I$ we can
        -- move outside the pth root.

        nsList := apply(exponentList, minGensList, (aa, mm) -> (
           max(0, floor(aa/p - mm + 1))
        ));
        I = R;
        for j from 0 to length(idealList) - 1 do I = I*(idealList#j)^(exponentList#j - nsList#j * p);
        I = frobeniusRoot(1, I, opts );
        frobeniusRoot(e - 1, append(nsList, 1), append(idealList, I), opts )
    );


    -----------------------------------------------------------------------------

    frobeniusRoot ( ZZ, ZZ, RingElement, Ideal ) := opts -> ( e, a, f, I ) -> frobeniusRootRingElements ( e, a, f, I, opts ) ---MK
     -- in the future, frobeniusRootRingElements should be subsumed by frobeniusRoot(ZZ, List, List). When this happens,
     -- the above line should end with frobeniusRoot( e, {a, 1}, {f, I} )

    -----------------------------------------------------------------------------

    frobeniusRoot ( ZZ, ZZ, RingElement ) := opts -> ( e, a, f ) -> frobeniusRootRingElements ( e, a, f, opts ) ---MK
     -- in the future, frobeniusRootRingElements should be subsumed by frobeniusRoot(ZZ, List, List). When this happens,
     -- the above line should end with frobeniusRoot( e, {a}, {f} )

    -----------------------------------------------------------------------------

    frobeniusRoot ( ZZ, ZZ, Ideal ) := opts -> ( e, m, I ) -> frobeniusRoot( e, {m}, {I}, opts )

    -----------------------------------------------------------------------------

    frobeniusRoot( ZZ, List, List, Ideal) := opts -> (e, exponentList, idealList, J) ->
       frobeniusRoot(e, append(exponentList, 1), append(idealList, J), opts );
    -----------------------------------------------------------------------------

    frobeniusRoot ( ZZ, Matrix ) := opts -> (e, A) -> mEthRoot (e,A)  --- MK

    -----------------------------------------------------------------------------


    --frobeniusRoot = method( Options => { FrobeniusRootStrategy => Substitution } )

    --frobeniusRoot ( ZZ, Ideal ) := o -> ( n, I ) ->
    --(
    --    p := char ring I;
    --    e := floorLog( p, n );
    --    if n != p^e then error "frobeniusPower: first argument must be a number of the form p^e, where p is the characteristic of the ring.";
    --    frobeniusRoot( e, I, FrobeniusRootStrategy => o.FrobeniusRootStrategy )
    --)

    --frobeniusRoot ( ZZ, MonomialIdeal ) := o -> ( n, I ) ->
    --(
    --    p := char ring I;
    --    e := floorLog( p, n );
    --    if n != p^e then error "frobeniusPower: first argument must be a number of the form p^e, where p is the characteristic of the ring.";
    --    frobeniusRoot( e, I, FrobeniusRootStrategy => o.FrobeniusRootStrategy )
    --)


    -----------------------------------------------------------------------------
    -- MACHINERY
    -----------------------------------------------------------------------------

    getFieldGenRoot = (e,p,q,k) -> (
        s := floorLog(p,q);
        -- Gets the exponent s such that q = p^s.
        a := (gens k)#0;
        a^(p^(s-e%s))
        -- Gets the p^e-th root of the cyclic generator a for the field extension k
        -- over ZZ/p.  If 1,a,..,a^t is a basis for k over ZZ/p and
        -- c = c_0 + c_1a + .. + c_ta^t in k, then replacing a with its p^e-th root
        -- in the preceding expansion using substitute(c,a => getFieldGenRoot(e,p,q,k))
        -- yields the p^e-th root of c.
    )


    -----------------------------------------------------------------------------

    frobeniusRootMonStrat = (e,p,q,k,f,R) -> ( --print "MonStrat";
        -- e = exponent, p = prime, q = size of coeff field, k = coeff field,
    	-- f = a generator of the ideal in question, R = the ring
    	-- to use this strategy to find the p^eth root of an ideal, you need to apply this
    	-- function to each generator of the ideal and sum the results.
    	-- maybe this should just return the ideal though? I guess it's an internal
    	-- function, so it doesn't matter.
        expDecomp := apply(exponents(f),exponent->{coefficient(R_exponent,f)*R_(exponent //p^e),exponent%p^e});
        --Gets the exponent vectors of each monomial X^u of the polynomial f, and associates to u the two-element list whose
        --first entry is cX^v and second entry is w, where c is the coefficient of X^u in f and u = p^e*v + w.
        if q > p then (
    	substRule := ( (gens k)#0 => getFieldGenRoot(e,p,q,k) );
    	expDecomp = apply( expDecomp, pair -> { substitute( pair#0, substRule ), pair#1 } );
        );
        remainders := partition(x-> x#1, expDecomp);
        --Sorts the preceding list of two-element lists into a hash table with keys the remainder w of the exponent vector.
        --The value of each key is a list of two-element lists {cX^v,w} with the same remainder.
        remainders = applyValues(remainders,v->apply(v,w->(w#0)));
        --Forgets the second entry of each two-element list in the preceding hash table.
        remainders = applyValues(remainders,v->sum(v));
        --Adds together all the terms for each key w in the hash table to get the coefficient of the basis monomial X^w
        --for R over R^(p^e).
        return ideal(values(remainders))
    )

    -----------------------------------------------------------------------------

    frobeniusRootSubStrat = (e,p,q,k,I,R) -> ( --print "SubStrat";
        n := numgens R;
        Rvars := R_*;
        Y := local Y;
        S := k(monoid[(Rvars | toList(Y_1..Y_n)), MonomialOrder=>ProductOrder{n,n},MonomialSize=>64]);
        --Produces a polynomial ring with twice as many variables as R.  The peculiar notation in the previous two lines
        --is required to ensure that the variables of S are hidden from the user.  In particular, the variables in R_* are
        --still recognized as variables of R and not S, and the code will not break if the variables in R happen to be called
        --Y_i also.
        Svars := S_*;
        J := ideal(apply(n,i->Svars#(n+i) - Svars#i^(p^e)))*S;
        H := apply((substitute(I,S))_*, f -> f % J);
        --If we denote the variables in R as X_1 .. X_n, then this replaces each occurrence of X_i^(p^e) in the polynomial f
        --with a Y_i.
        L := sum(H, f -> ideal((coefficients(f,Variables => Rvars))#1));
        --Peals off the coefficients of the basis polynomials for R over R^(p^e) as polynomials in the Y_i, and produces the
        --ideal generated by these coefficient polynomials.
        L = first entries mingens L;
        subRelations := apply(n,i->Svars#(n+i) => Svars#i);
        if q > p then subRelations = subRelations|{(gens k)#0 => getFieldGenRoot(e,p,q,k)};
        L = apply(L, g ->substitute(g,subRelations));
        --Pushes the ideal of coefficient polynomials down to R by substituting Y_i => X_i.
        --q := k#order;
        --Gets the size of the base field.
        substitute(ideal L, R)
    )

    frobeniusRootRingElements = method(Options => {FrobeniusRootStrategy => Substitution});
    --This tries to compute (f1^a1*f2^a2*...fk^ak*I)^{[1/p^e]} in such a way that we don't blow exponent buffers.  It can be much faster as well.
    --We should probably just use it.  It relies on the fact that (f^(ap+b))^{[1/p^2]} = (f^a(f^b)^{[1/p]})^{[1/p]}.

    --It's a special case of frobeniusRoot(ZZ, List, List) that's optimized for lots of principal ideals

    frobeniusRootRingElements( ZZ, List, List, Ideal ) := o->( e, aList, elmtList, I ) -> (
        R := ring I;
        p := char R;

        aListRem := aList % p^e;
        aListQuot := aList // p^e;

        -- gives the basePexpansion of each element of aListRem
        -- expOfaList is thus a list of lists.
        expOfaList := apply(aListRem, z -> reverse toList baseP1( p, z, e ) );

        -- this computes { ... f_i^b_i ... } where b_i = a_i % p
        aPowerList := apply(elmtList, expOfaList, (f, z) -> f^(z#0));

        IN1 := I*ideal(product(aPowerList));
        if (e > 0) then (
            IN1 = frobeniusRoot( 1, IN1 );
            i := 1;
            while(i < e) do (
                aPowerList = apply(elmtList, expOfaList, (f, z) -> f^(z#i));
                IN1 = frobeniusRoot( 1, IN1*ideal(product(aPowerList)), o );
                i = i + 1;
            )
        );
        aPowerList = apply(elmtList, aListQuot, (f, z) -> f^z);
        IN1*ideal(product(aPowerList))
    )

    frobeniusRootRingElements( ZZ, Sequence, Sequence, Ideal ) := o->(a, b, c, d) -> frobeniusRootRingElements(a, toList b, toList c, d, o )

    frobeniusRootRingElements( ZZ, ZZ, RingElement, Ideal ) := o->( e, a, f, I ) ->
        frobeniusRootRingElements(e, {a}, {f}, I, o )

    frobeniusRootRingElements( ZZ, ZZ, RingElement ) := o->( e, a, f ) ->
        frobeniusRootRingElements( e, {a}, {f}, ideal( 1_(ring f) ), o )



    ----------------------------------------------------------------
    --************************************************************--
    --Functions for computing test ideals, and related objects.   --
    --************************************************************--
    ----------------------------------------------------------------


    --Finds the smallest phi-stable ideal containing the given ideal Jk
    --in a polynomial ring Sk
    --Jk is the given ideal, ek is the power of Frobenius to use, hk is the function to multiply
    --trace by to give phi:  phi(_) = Tr^(ek)(hk._)
    --This is based on ideas of Moty Katzman, and his star closure

    --this is a new ascendIdeal written by Karl.  It ascends but does it in a possibly non-polynomial ring.
    --the point is the ascending might be faster if we don't care about it mod a certain ideal.
    ascendIdeal = method(Options => {FrobeniusRootStrategy => Substitution, AscentCount=>false});

    ascendIdeal(ZZ, RingElement, Ideal) := o->(ek, hk, Jk) ->
        ascendIdeal(ek, {1}, {hk}, Jk, o)



    --Works like above ascendIdeal but tries to minimize the exponents elements are taken to
    -- what's ak?  Karl: ak is the numerator of the exponent t = ak/(p^ek - 1)

    ascendIdeal(ZZ, ZZ, RingElement, Ideal) := o->( ek, ak, hk, Jk) ->
        ascendIdeal(ek, {ak}, {hk}, Jk, o)



    --handles lists of hk to powers...
    ascendIdeal(ZZ, BasicList, BasicList, Ideal) := o->(ek, akList,  hkList, Jk) -> (
        Rk := ring Jk;
        Ik := ideal Rk;
        Sk := ambient Rk;

        pp := char Sk;
        IN := sub(Jk, Sk);
        IP := ideal(0_Sk);
        i1 := 0;
         --we want to make the largest ideal that is phi-stable, following Moty Katzman's idea
         --we do the following
        while (isSubset(IN+Ik, IP+Ik) == false) do(
            i1 = i1 + 1;
            --print "Step";
            IP = IN;
            IN = frobeniusRoot( ek, akList, hkList, IP, FrobeniusRootStrategy => o.FrobeniusRootStrategy) + IP
        );

        --trim the output
        if (o.AscentCount == false) then
    		trim (IP*Rk)
    	else {trim (IP*Rk), i1}
    )
    --


    --MKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMK
    -----------------------------------------------------------------------------
    --- Extend the Frobenius p^e th roots and star operations to submodules of
    --- free modules (over polynomial rings with *prime* coeeficient field)
    --- This implements the methods described in
    --- Moty Katzman and Wenliang Zhang's paper
    --- "Annihilators of Artinian modules compatible with a Frobenius map"
    --- Journal of Symbolic computation, 2014

    -----------------------------------------------------------------------------


    getExponents = method();
    getExponents(Matrix):= (f)-> (
        answer:={};
        t:=terms(first first entries f);
        apply(t, i->
        {
            exps:=first exponents(i);
            c:=(coefficients(i))#1;
            c=first first entries c;
            answer=append(answer,(c,exps));
        });
        answer
    )

    mEthRootOfOneElement= (e,v) ->(
    	local i; local j;
    	local d;
    	local w;
    	local m;
    	local answer;
    	R:=ring(v); p:=char R; q:=p^e;
    	F:=coefficientRing(R);
    	n:=rank source vars(R);
    	V:=ideal vars(R);
    	vv:=first entries vars(R);
    	T:=new MutableHashTable;
    	alpha:=rank target matrix(v);
    	B:={};
    	for i from 1 to alpha do
    	{
    		vi:=v^{i-1};
    ---print("i=",i);
    ---print("vi=",vi);
    		C:=getExponents(vi);
    ---print(C);
    		apply(C, c->
    		{
    			lambda:=c#0;
    			beta:=c#1;
    			gamma:=apply(beta, j-> (j%q));
    			B=append(B,gamma);
    			key:=(i,gamma);
    ---print(beta, #beta,vv);
    			data:=apply(1..(#beta), j-> vv_(j-1)^((beta#(j-1))//q));
    			data=lambda*product(toList data);
    ---print(beta, key, data);
    			if (T#?key) then
    			{
    				T#key=(T#key)+data;
    			}
    			else
    			{
    				T#key=data;
    			};
    		});
    	};
    	B=unique(B);
    	TT:=new MutableHashTable;
    	apply(B, b->
    	{
    		ww:={};
    		for i from 1 to alpha do if T#?(i,b) then ww=append(ww,T#(i,b)) else ww=append(ww,0_R);
    		ww=transpose matrix {ww};
    		TT#b=ww;
    	});
    	KEYS:=keys(TT);
    	answer=TT#(KEYS#0);
    	for i from 1 to (#KEYS)-1 do answer=answer | TT#(KEYS#i);
    	answer
    )

    mEthRoot = (e,A) ->(
    	local i;
    	local answer;
    	                                 --i->first entries mEthRootOfOneElement (e, A_{i-1}));
    	answer1:=apply(1..(rank source A), i-> mEthRootOfOneElement (e, A_{i-1}));
    	--the above subscript denotes taking the ith column of A
    	if (#answer1==0) then
    	{
    		answer=A;
    	}
    	else
    	{
    		answer=answer1#0;
    		apply(2..(#answer1), i->answer=answer | answer1#(i-1));
    		--this apply statement turns a list of columns into a matrix
    		--is there no better way?

    	    --answer = matrix toList answer1;
    	};
    	mingens( image answer )
    )



    --MKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMK
    -- given n by n matrix U and submodule A of a free module R^n,
    -- ascendModule finds the smallest submodule V of R^n containing A and which satisfies U^(1+p+...+p^(e-1)) V\subset V^{[p^e]}
    -- This is analogous to ascendIdeal, only for submodules of free modules.
    ascendModule = method();

    ascendModule(ZZ,Matrix,Matrix) := (e,A,U) -> (
    Mstar (e,A,U)
    )


    --MKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMKMK

    --- Mstar is the implementaion of the star closure operation desribed in
    --- M Katzman and W. Zhang's "Annihilators of Artinian modules compatible with a Frobenius map"
    --- Input:
    ---    a positive integer e
    ---    n by n matrix U and submodule A of a free module R^n OVER A PRIME FIELD.
    --- Output:
    ---    the smallest submodule V of R^n containing A and which satisfies U^(1+p+...+p^(e-1)) V\subset V^{[p^e]}
    Mstar = (e,A,U) ->(
    	local answer;
    	R:=ring(A); p:=char R;
    	if (A==0) then
    	{
    		answer=A;
    	}
    	else
    	{
    		flag:=true;
    		Ne:=sum toList(apply(0..(e-1), i->p^i));
    		lastA:= A;
    		while (flag) do
    		{
    			flag=false;
    			A1:=matrix entries mEthRoot(e, mingens image ((U^Ne)*lastA));
    			A1=A1 | lastA;
    			t1:=compress ((A1))%((lastA));
    			if (t1!=0) then
    			{
    				flag=true;
    				lastA=mingens image A1;
    			};
    		};
    		answer=mingens (image A1);
    	};
    	use(R);
    	answer
    )


    --*************************************************
    --*************************************************
    --This file is used for taking various types of
    --powers of ideals in characteristic p>0.
    --*************************************************
    --*************************************************



    --Computes powers of elements in char p>0, using that Frobenius is an endomorphism. If
    --N = N_0 + N_1 p + ... + N_e p^e, where 0 <= N_i < p, then this computes f^N as
    --f^(N_0) (f^(N_1))^p ... (f^(N_e))^(p^e).

    fastExponentiation = method( TypicalValue => RingElement )

    fastExponentiation ( ZZ, RingElement ) := RingElement => ( N, f ) ->
    (
        if N < 0 then error "fastExponentiation: first argument must a nonnegative integer.";
        p := char ring f;
        if p == 0 then return f^N;
        E:=adicExpansion(p,N);
        product(#E, e -> sum( terms f^(E#e), g -> g^(p^e) ) )
    )

    --------------------------------------------------------------------------------------------------------

    --Outputs the p^e-th Frobenius power of an ideal, or the p^e-th (entry-wise) Frobenius power of a matrix.

    frobeniusMethod =  method( Options => { FrobeniusRootStrategy => Substitution } );

    frobeniusMethod ( ZZ, Ideal ) := Ideal => o -> ( e, I ) ->
    (
        R := ring I;
        p := char R;
        if p == 0 then
            error "frobeniusMethod: expected an ideal in a ring of positive characteristic.";
        if e == 0 then return I;
        if e < 0 then return frobeniusRoot( -e, I, o );
        G := I_*;
        if #G == 0 then ideal( 0_R ) else ideal( apply( G, j -> fastExponentiation( p^e, j ) ) )
    )

    frobeniusMethod ( ZZ, Matrix ) := Matrix => o -> ( e, M ) ->
    (
        p := char ring M;
        if p == 0 then
            error "frobenius: expected an matrix with entries in a ring of positive characteristic.";
        if e == 0 then return M;
        if e < 0 then error "frobenius: first argument must be nonnegative.";
        matrix apply( entries M, u -> apply( u, j -> fastExponentiation( p^e, j ) ) )
    )

    frobeniusMethod ( Ideal ) := Ideal => o -> I -> frobeniusMethod( 1, I, o )

    frobeniusMethod ( Matrix ) := Matrix => o -> M -> frobeniusMethod( 1, M )

    FrobeniusOperator = new Type of MethodFunctionWithOptions

    frobenius = new FrobeniusOperator from frobeniusMethod

    FrobeniusOperator ^ ZZ := ( f, n ) -> ( x -> f( n, x ) )

    --------------------------------------------------------------------------------------------------------

    --This is an internal function. Given ideals I, J and a positive integer e, consider
    --the following chain of ideals:
    --K_1 = (I*J)^[1/p^e] and K_{s+1} = (I*K_s)^[1/p^e]
    --This chain is ascending, and has the property that once two consecutive terms
    --agree, the chain stabilizes.  This function outputs the stable ideal of this chain.

    stableIdeal = { FrobeniusRootStrategy => Substitution } >> o -> ( e, I, J ) ->
    (
        K := ideal( 0_( ring I ) );
        L := frobeniusRoot( e, I*J, o );
        while not isSubset( L, K ) do
        (
        	K = L;
        	L = frobeniusRoot( e, I*K, o );
        );
        trim K
    )

    --------------------------------------------------------------------------------------------------------

    --Outputs the generalized Frobenius power of an ideal; either the N-th Frobenius power of N/p^e-th one.

    frobeniusPower = method(
        Options => { FrobeniusPowerStrategy => Naive, FrobeniusRootStrategy => Substitution },
        TypicalValue => Ideal
    );

    --Computes the integral generalized Frobenius power I^[N]
    frobeniusPower ( ZZ, Ideal ) := Ideal => o -> ( N, I ) ->
    (
        R := ring I;
        p := char R;
        if p == 0 then
            error "frobeniusPower: expected an ideal in a ring of positive characteristic.";
        G := first entries mingens I;
        if #G == 0 then return ideal( 0_R );
        if #G == 1 then return ideal( fastExponentiation( N, G#0 ) );
        E := adicExpansion( p, N );
        product( #E, m -> frobenius( m, I^( E#m ) ) )
    )

    --Computes the generalized Frobenius power I^[N/p^e]
    frobeniusPowerHelper = { FrobeniusPowerStrategy => Naive, FrobeniusRootStrategy => Substitution } >>
        o -> ( e, N, I ) ->
    (
        R := ring I;
        p := char R;
        G := first entries mingens I;
        if #G == 0 then return ideal( 0_R );
        rem := N % p^e;
        M := N // p^e;
        J := frobeniusPower( M, I );  --component when applying Skoda's theorem
        if o.FrobeniusPowerStrategy == Safe then
        (
    	E := adicExpansion( p, rem );
    	J * product( #E, m -> frobeniusRoot( e-m, I^( E#m ), FrobeniusRootStrategy => o.FrobeniusRootStrategy ) );
            --step-by-step computation of generalized Frobenius power of I^[rem/p^e]
            --using the base p expansion of rem/p^e < 1
        )
        else J * frobeniusRoot( e, frobeniusPower( rem, I ), FrobeniusRootStrategy => o.FrobeniusRootStrategy )  --Skoda to compute I^[N/p^e] from I^[rem/p^e]
    )

    --Computes the generalized Frobenius power I^[t] for a rational number t
    frobeniusPower( QQ, Ideal ) := Ideal => o -> ( t, I ) ->
    (
        if t < 0 then error "frobeniusPower: expected a nonnegative exponent.";
        p := char ring I;
        if p == 0 then
            error "frobeniusPower: expected an ideal in a ring of positive characteristic.";
        ( a, b, c ) := toSequence decomposeFraction( p, t ); --write t = a/(p^b*(p^c-1))
        if c == 0 then frobeniusPowerHelper( b, a, I, o )  --if c = 0, call simpler function
            else
    	(
    	    rem := a % ( p^c - 1 );
    	    quot := a // ( p^c - 1 );
    	    J := stableIdeal( c, frobeniusPower( rem, I ), I, FrobeniusRootStrategy => o.FrobeniusRootStrategy );
    	    frobeniusRoot( b, frobeniusPower( quot, I ) * J, FrobeniusRootStrategy => o.FrobeniusRootStrategy )
            )
    )

    ----------------------------------------------------------------
    --************************************************************--
    --Functions for computing compatibly split ideals             --
    --************************************************************--
    ----------------------------------------------------------------

    -----------------------------------------------------------------------


    --- Start of MK ---------------------------------------------------------------------------------------------------

    -- FIND IDEALS COMPATIBLE WITH A GIVEN NEAR-SPLITTING
    -- This is an implementation of the algorithm described in
    -- Moty Katzman and Karl Schwede's paper
    -- "An algorithm for computing compatibly Frobenius split subvarieties"
    -- J. Symbolic Comput. 47 (2012), no. 8, 996\961008.

    ----------------------------------------------------------------------------------------


    --- Input:
    ---   	an element u of the polynomial ring R OVER A PRIME FIELD.
    --- Output:
    ---	A list of all prime ideals P such that
    ---	(a) u P \subseteq P^{[p]}, and
    ---	(b) the action of uT on the the annihilator of P on the injective hull of the residue field of R
    ---	is not the zero Frobenius map.

    compatibleIdeals = method(Options => {FrobeniusRootStrategy => Substitution});



    compatibleIdeals(RingElement) := o -> u ->
    (
        if not isPolynomialOverPrimeField( u ) then
            error "compatibleIdeals: expected an element of a polynomial ring over a prime field ZZ/p";
        L := { };
        R := ring u;
        P := ideal 0_R;
        J:=frobeniusRoot( 1, ideal u );
        t := 1_R % ( gens J );
        if t != 0_R then print "*** WARNING *** Frobenius action has nilpotent elements";
        compatibleIdealsInnards ( u, L, P )
    );

    compatibleIdealsInnards = method(Options => {FrobeniusRootStrategy => Substitution});

    compatibleIdealsInnards(RingElement, List, Ideal) := o->( u, L, P ) ->
    (
        local f;
        P1 := frobenius(P);
    --    C1 := ideal( ( singularLocus( P ) ).relations );
        C1 := ideal testElement((ring P)/P, AssumeDomain=>true);
        ---tau=ideal mingens star(C1,u,1) ; ---OLD VERSION
        tau := ideal mingens ascendIdeal( 1, u, C1, o );
        Plist := minimalPrimes tau;
        apply( Plist, Q ->
            (
        	    f = any( L, T -> T == Q );
    ---print(L,Q,f);
                if not f then
    	    (
    	        L = append( L, Q );
    	        L = unique( L | compatibleIdealsInnards( u, L, Q, o ) );
    	    );
            )
        );
    ---
        C2 := ( P1 + ideal( u ) ) : ( P1 : P );
    ---	JB:=C1*C2; ---MK
    ---print(mingens P, mingens JB);
    ---tau=ideal mingens star(C2,u,1) ;  --- OLD VERSION
        tau = ideal mingens ascendIdeal( 1, u, C2, o );
        Plist = minimalPrimes tau;
        apply( Plist, Q ->
    	(
    	    f = any( L, T -> T == Q );
    	---print(L,Q,f);
    	    if not f then
    	    (
    		L = append( L, Q );
    		L = unique( L | compatibleIdealsInnards( u, L, Q, o ) );
    	    );
    	)
        );
        ---
        L
    );

    ----------------------------------------------------------------
    --************************************************************--
    --Functions for computing parameter test modules and ideals   --
    --************************************************************--
    ----------------------------------------------------------------


    --This function computes the parameter test module of a ring, it returns it as a submodule of a canonical ideal.
    --this is a slightly modified function originally written by Moty Katzman for "Parameter test ideals of Cohen Macaulay rings"
    --it returns the lift of the canonical module to the ambient ring
    --needsPackage "Divisor";

    canonicalIdeal = method( Options => { Attempts => 10 } )

    canonicalIdeal(Ring) := o->(R1) -> (
        S1 := ambient R1;
    	I1 := ideal R1;
    	dR := dim R1;
    	dS := dim S1;
    	varList := first entries vars S1;
    	degList := {};
    	if (#varList > 0) then (
        	if (#(degree(varList#0)) == 1) then (
    	    	degList = apply(varList, q -> (degree(q))#0); )
        	else (
    	    	degList = apply(varList, q -> (degree(q))); );
        );
    	M1 := (Ext^(dS - dR)(S1^1/I1, S1^{-(sum degList)}))**R1;
    	embedAsIdeal(M1, Attempts => o.Attempts)
    );


    --the following function computes the u of a canonical ideal in a polynomial ring
    --it uses previous work of Katzman
    finduOfIdeal = method();

    finduOfIdeal(Ideal, Ideal) := (defIdeal, canIdeal) -> (
    	Ip := frobenius( defIdeal );
    	tempIdeal := intersect( (frobenius( canIdeal )) : canIdeal, Ip : defIdeal );

    	M1 := compress ((gens tempIdeal)%(gens Ip));
    	first first entries M1
    );

    --****************************************************
    --*****Karl rewrote this *****
    --****************************************************

    --this function finds the generators of the intersection of
    --J^{[p]} : J and I^{[p]} : I where I is the defining ideal and J is the canonical
    --ideal lifted to the ambient ring (in a maximal way).
    frobeniusTraceOnCanonicalModule = (defIdeal, canIdeal) -> (
    	Ip := frobenius( defIdeal );
    	tempIdeal := intersect( (frobenius( canIdeal )) : canIdeal, Ip : defIdeal );

    	M1 := compress ((gens tempIdeal)%(gens Ip));
    	first entries M1
    )

    testModule = method(Options => {FrobeniusRootStrategy => Substitution, AssumeDomain=>false}); --a rewritten function to construct the (parameter) test (sub)module of a given ring.
                           --it returns two ideals and an element.
                           --The first ideal is an ideal isomorphic to the test module and the
                           --and the second is an ideal isomorphic to the canonical module, in which the parameter
                           --resides.  The locus where these two ideals differ (plus the non-CM locus) is the
                           --locus where the ring does not have rational singularities.
                           --the final element is the element of the ambient polynomial ring which is used to
                           --induce the canonical trace map
                           --This function can also compute \tau(omega, f^t) (again as a submodule of omega).
                           --

    testModule(Ring) := o -> (R1) -> (
        J1 := canonicalIdeal(R1);
        testModule(R1, J1, o)
    );

    testModule(Ring, Ideal) := o->(R1, canIdeal) -> (
        S1 := ambient R1;
    	I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        C1 := testElement(R1, AssumeDomain => o.AssumeDomain);
        u1 := frobeniusTraceOnCanonicalModule(I1, J1+I1);
        tau := I1;
        if (#u1 > 1) then(
            print "testModule: Multiple trace map for omega generators (Macaulay2 failed to find the principal generator of a principal ideal).  Using them all.";
            j := 0;
            while (j < #u1) do (
                tau = tau + ascendIdeal(1, u1#j, C1*J1*R1, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
                j = j+1;
            );
        )
        else (
            u1 = u1#0;
            tau = ascendIdeal(1, u1, C1*J1*R1, FrobeniusRootStrategy => o.FrobeniusRootStrategy);
        );

        (sub(tau, R1), sub(J1, R1), u1)
    );



    testModule(Number, RingElement) := o-> (tt, ff) ->(
        tt = tt/1;
        R1 := ring ff;
        S1 := ambient R1;
        canIdeal := canonicalIdeal(R1);
        I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        u1 := frobeniusTraceOnCanonicalModule(I1, J1+I1);
        testModule(tt, ff, canIdeal, u1, o)
    );

    testModule(Number, RingElement, Ideal, List) := o -> (tt, ff, canIdeal, u1) -> (
        tt = tt/1;
        R1 := ring ff;
        pp := char R1;
        S1 := ambient R1;
        fff := sub(ff, S1);
        I1 := ideal R1;
        J1 := sub(canIdeal, S1);


        C1 := testElement(R1, AssumeDomain => o.AssumeDomain);
        fractionDivided := decomposeFraction(pp, tt);

        -- fraction divided writes tt = (a/(p^b(p^c-1))
        -- the point is that
        -- tau(\omega, f^t) = (tau( omega, f^{a/(p^c-1)}) * u1^{(p^b-1)/(p-1)} )^{[1/p^b]}
        aa := fractionDivided#0;
        bb := fractionDivided#1;
        cc := fractionDivided#2;
        --we need to managed the case when ttt = aa/(pp^cc - 1) is huge, we handle this as folows.
        -- tau(\omega, ff^ttt) = \tau(\omega, ff^{ttt - floor(ttt)} ) * ff^{floor(ttt)}
        -- we do this because we never want to actually compute ff^{floor(ttt)}
        ttt := 0;
        aaa := 0;
        ccc := 0;
        newIntegerPart := 0;
        newFractionalPart := 0;
        fractionDivided2 := {};
        if (cc > 0) then (
            ttt = aa/(pp^cc-1);
            newIntegerPart = floor(ttt);
            newFractionalPart = ttt - newIntegerPart;
            fractionDivided2 = decomposeFraction(pp, newFractionalPart);
            aaa = fractionDivided2#0;
            ccc = fractionDivided2#2;
        )
        else ( -- this is the case when t = a/p^b
            aaa = 0;
            ccc = 1;
            newIntegerPart = aa;
        );
        tau := I1;
        curTau := I1;
        if (#u1 > 1) then(
            if (debugLevel > 0) then (
                print "testModule: Multiple trace map for omega generators (Macaulay2 failed to find the principal generator of a principal ideal).  Using them all.";
            );
            j := 0;
            while (j < #u1) do (
                curTau = ascendIdeal(ccc, {floor((pp^ccc - 1)/(pp-1)),  aaa}, {u1#j, fff}, (ideal(fff))*C1*J1*R1, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
                    --note, we only have an ideal(ff) in the test element here since by construction,
                    --aaa/(pp^ccc-1) is less than 1.
                    --if we need to take more roots, do so...
                curTau = sub(curTau, S1);
                curTau = frobeniusRoot(bb, {floor((pp^bb - 1)/(pp-1)), newIntegerPart}, {u1#j, fff}, curTau, FrobeniusRootStrategy => o.FrobeniusRootStrategy);
                tau = tau + curTau;
                j = j+1;
            );
        )
        else (
            u1 = u1#0;
            curTau = ascendIdeal(ccc, {floor((pp^ccc - 1)/(pp-1)),  aaa}, {u1, fff}, (ideal(fff^(min(1, aaa))))*C1*J1*R1, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
                    --note, we only have an ideal(ff) in the test element here since by construction,
                    --aaa/(pp^ccc-1) is less than 1.
                    --if we need to take more roots, do so...
            curTau = sub(curTau, S1);
            tau = frobeniusRoot(bb, {floor((pp^bb - 1)/(pp-1)), newIntegerPart}, {u1, fff}, curTau, FrobeniusRootStrategy => o.FrobeniusRootStrategy);
        );

        (sub(tau, R1), sub(J1, R1), u1)
    );


    --Write a testModule function that computes \tau(omega, f^s g^t h^u) for example
    --this works similarly to testModule(QQ, RingElement, Ideal, List), but it takes lists of elements.
    --Note if you specify u1 and something a bit different that canIdeal (but that is u compatible), this can be used to still compute
    --a test module of a certain Cartier module.
    testModule(List, List, Ideal, List) := o -> (ttList, ffList, canIdeal, u1) -> (
        ff := ffList#0;
        R1 := ring ff;
        pp := char R1;
        S1 := ambient R1;
        fff := sub(ff, S1);
        I1 := ideal R1;
        J1 := sub(canIdeal, S1);

        ffList = apply(ffList, zz->sub(zz, S1));
        C1 := testElement(R1, AssumeDomain => o.AssumeDomain);
        fractionDividedList := apply(ttList, tt -> decomposeFraction(pp, tt));

        -- fraction divided writes tt = (a/(p^b(p^c-1))
        -- the point is that
        -- tau(\omega, f^t) = (tau( omega, f^{a/(p^c-1)}) * u1^{(p^b-1)/(p-1)} )^{[1/p^b]}
        bbList := apply(fractionDividedList, zz->zz#1);
        ccList := apply(fractionDividedList, zz->zz#2);
        --we need to write all of our fractions with the same denominator.
        lcmCs := lcm(apply(ccList, zz -> (if zz == 0 then 1 else zz))); --take the lcm of the cs,
                                                                       --but ignore those cs that
                                                                       --are equal to zero
        maxBs := max(bbList);
        --next we create the list of aa values for ascending the ideal
        aaListForCs := apply(fractionDividedList, zz -> (
                                                        if ((zz#2) == 0) then 0 else
                                                            (zz#0)*floor(pp^(maxBs - (zz#1)))*floor( (pp^lcmCs - 1)/(pp^(zz#2) - 1))
                                                     )
                            );
        --we need to managed the case when ttt = aa/(pp^cc - 1) is huge, we handle this as folows.
        -- tau(\omega, ff^ttt) = \tau(\omega, ff^{ttt - floor(ttt)} ) * ff^{floor(ttt)}
        -- we do this because we never want to actually compute ff^{floor(ttt)}
        aaListForCsReduced := apply(aaListForCs, aa -> (aa % (pp^lcmCs - 1)) );
        aaListForAfterAscension := apply(#fractionDividedList, nn -> (
                                                        if ( ((fractionDividedList#nn)#2) > 0 ) then floor((aaListForCs#nn)/(pp^lcmCs - 1)) else
                                                            ((fractionDividedList#nn)#0)*floor(pp^(maxBs - ((fractionDividedList#nn)#1)))
                                                     )
                            );

        tau := I1;
        curTau := I1;
        prodList := apply(#ffList, iii -> (ffList#iii)^(min(1, aaListForCsReduced#iii)) );
        if (#u1 > 1) then(
            print "testModule: Multiple trace map for omega generators (Macaulay2 failed to find the principal generator of a principal ideal).  Using them all.";
            j := 0;
            while (j < #u1) do (
                curTau = ascendIdeal(lcmCs, append(aaListForCsReduced, floor((pp^lcmCs - 1)/(pp-1))), append(ffList, u1), (product(prodList))*C1*J1*R1, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
                    --note, we only have an ideal(ff) in the test element here since by construction,
                    --aaa/(pp^ccc-1) is less than 1.
                    --if we need to take more roots, do so...
                curTau = sub(curTau, S1);

                curTau = frobeniusRoot(maxBs, append(aaListForAfterAscension, floor((pp^maxBs - 1)/(pp-1))), append(ffList, u1), curTau, FrobeniusRootStrategy => o.FrobeniusRootStrategy);

                tau = tau + curTau;
                j = j+1;
            );
        )
        else (
            u1 = u1#0;
            curTau = ascendIdeal(lcmCs, append(aaListForCsReduced, floor((pp^lcmCs - 1)/(pp-1))), append(ffList, u1), (product(prodList))*C1*J1*R1, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
                    --note, we only have an ideal(ff) in the test element here since by construction,
                    --aaa/(pp^ccc-1) is less than 1.
                    --if we need to take more roots, do so...
            curTau = sub(curTau, S1);
            tau = frobeniusRoot(maxBs, append(aaListForAfterAscension, floor((pp^maxBs - 1)/(pp-1))), append(ffList, u1), curTau, FrobeniusRootStrategy => o.FrobeniusRootStrategy);
        );

        (sub(tau, R1), sub(J1, R1), u1)
    );

    testModule(List, List) := o-> (ttList, ffList) ->(
        R1 := ring (ffList#0);
        S1 := ambient R1;
        canIdeal := canonicalIdeal(R1);
        I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        u1 := frobeniusTraceOnCanonicalModule(I1, J1+I1);
        testModule(ttList, ffList, canIdeal, u1, o)
    );


    --we also can compute the parameter test ideal (in a Cohen-Macaulay ring)

    parameterTestIdeal = method(Options => {FrobeniusRootStrategy => Substitution});

    parameterTestIdeal(Ring) := o-> (R1) -> (
        testMod := testModule(R1,o);
        (testMod#0) : (testMod#1)
    );


    --Below is an isCohenMacaulay function.  There are other implementations of this in the packages
    --Depth and LexIdeals.  This one has the advantage that it works even if the ring is not local/graded.
    --If you pass it the Local=>true option, then it calls the isCM function in Depth.


    --warning, this only works if R is equidimensional.  If Spec R has disjoint components of different dimensions
    --then this function will return false, even if R is Cohen-Macaulay.
    isCohenMacaulay = method(Options => {IsLocal => false});

    isCohenMacaulay(Ring) := o->(R1) ->(
        if (o.IsLocal == true) then (
            isCM(R1)
        )
        else (
            S1 := ambient R1;
            I1 := ideal R1;
            M1 := S1^1/I1;
            dimS := dim S1;
            dimR := dim R1;
            flag := true;
            P1 := res M1;

            if (length P1 == dimS - dimR) then (
                true
            )
            else if (isHomogeneous(I1) == true) then (
                false
            )
            else (
                RHom := Hom(P1, S1^1);
                i := dimS - dimR + 1;
                while ((flag == true) and (i <= dimS))do (
                    if (dim (HH^i(RHom)) > -1) then (
                        flag = false;
                    );
                    i = i+1;
                );
                flag
            )
        )
    );

    --next we write an isFRational function

    isFRational = method(Options => {AssumeDomain => false, IsLocal => false, AssumeCM => false, FrobeniusRootStrategy=>Substitution });

    isFRational(Ring) := o->(R1) ->(
        flag := true;
        --first verify if it is CM
        if (o.AssumeCM == false) then(
            if (not isCohenMacaulay(R1, IsLocal => o.IsLocal)) then (
                flag = false;
            );
        );
        --next verify if it is Frational
        if (flag == true) then (
            --note we don't compute the test module if we know that the ring is not CM.
            MList := testModule(R1, passOptions( o, { AssumeDomain, FrobeniusRootStrategy } ) );
            if (o.IsLocal == true) then (
                paraTestIdeal := (MList#0):(MList#1);
                myMaxIdeal := sub(maxIdeal(ambient R1), R1);
                flag = not isSubset(paraTestIdeal, myMaxIdeal);
            )
            else (
                if (isSubset(MList#1, MList#0) == false) then (
                    flag = false;
                )
            );
        );

        flag
    );

    ---------------------------------------------------------------------
    ---------------------------------------------------------------------
    --**************************************
    --*** HSLGModule computes the stable ***
    --*** image under trace of \omega    ***
    --*** This is dual to the stable     ***
    --*** kernel of Frobenius acting on  ***
    --*** local cohomology               ***
    --**************************************

    HSLGModule = method(Options => {FrobeniusRootStrategy => Substitution});
                           --it returns two ideals, an element and an integer
                           --The first ideal is an ideal isomorphic to the non-F-injective module and the
                           --and the second is an ideal isomorphic to the canonical module, in which the parameter
                           --resides.  The locus where these two ideals differ (plus the non-CM locus) is the
                           --locus where the ring does not have rational singularities.
                           --the final element is the element of the ambient polynomial ring which is used to
                           --induce the canonical trace map (or a list of elements)
                           --finally, it also outputs the associated HSL(G)-number.
                           --{HSLMod, CanMod, u, HSL#}


    HSLGModule(Ring) := o-> (R1) -> (
        J1 := trim canonicalIdeal(R1);
        HSLGModule(R1, J1, o)
    );

    HSLGModule(Ring, Ideal) := o-> (R1, canIdeal) -> (
        S1 := ambient R1;
    	I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        u1 := frobeniusTraceOnCanonicalModule(I1, J1+I1);
    --    powList := apply(u1, zz->1);
        --NEED TO CHANGE (and below), we should not have the full list of us there.
        HSLGModule(R1, canIdeal, u1)
    );

    HSLGModule(Ring, Ideal, List) := o-> (R1, canIdeal, u1) -> (
        S1 := ambient R1;
    	I1 := ideal R1;
        J1 := sub(canIdeal, S1);

        curIdeal := ideal(sub(0, R1));
        curHSL := 1;
        curHSLList := null;
        i := 0;
        while (i < #u1) do (
            curHSLList = HSLGModule(1, {1}, {u1#i}, canIdeal, o);
            curIdeal = curIdeal + curHSLList#0;
            curHSL = lcm(curHSL, curHSLList#3);
            i = i+1;
        );
        return {curIdeal, canIdeal, u1, curHSL};
    );

    HSLGModule(Ideal) := o -> (canIdeal) -> (
        R1 := ring canIdeal;
        HSLGModule(R1, canIdeal, o)
    );

    HSLGModule(Number, RingElement, Ideal, List) := o -> (tt, ff, canIdeal, u1) -> (
        R1 := ring ff;
        S1 := ambient R1;
        if (not (ring (u1#0) === S1)) then error "HSLGModule: Exptected u1 to be in the ambient polynomial ring.";
    	I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        pp := char S1;
        tt = tt*1/1;
        fractionDivided := decomposeFraction(pp, tt);
            -- fraction divided writes tt = (a/(p^b(p^c-1))
        aa := fractionDivided#0;
        bb := fractionDivided#1;
        cc := fractionDivided#2;
        if (bb > 0) then (
            error "HSLGModule: Cannot compute the HSLG module associated to something with p in denominator.";
        );
        if (cc == 0) then (
            cc = 1;
            aa = aa*(pp-1);
        );
        newExp := floor( (pp^cc-1)/(pp-1) );
    --    uList := append(u1, ff);
    --    powList = append(powList, aa);
        --now we have to do a sum again since Macaulay2 might not find one u in the nongraded case.
        curIdeal := ideal(sub(0, R1));
        curHSL := 1;
        curHSLList := null;
        i := 0;
        while (i < #u1) do (
            curHSLList = HSLGModule(cc, {newExp, aa}, {u1#i, ff}, canIdeal, o);
            curIdeal = curIdeal + curHSLList#0;
            curHSL = lcm(curHSL, curHSLList#3);
            i = i+1;
        );
        {curIdeal, canIdeal, u1, curHSL}
    );

    HSLGModule(Number, RingElement) := o -> (tt, ff) -> (
        R1 := ring ff;
        canIdeal := trim canonicalIdeal(R1);
        S1 := ambient R1;
    	I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        u1 := frobeniusTraceOnCanonicalModule(I1, J1+I1);
        return HSLGModule(tt, ff, canIdeal, u1);
    );

    HSLGModule(List, List, Ideal, List) := o -> (tList, fList, canIdeal, u1) -> (
        if ( not (#tList == #fList) ) then error "HSLGModule: expected the lists to have the same lengths.";
        if ( #fList == 0 ) then error "HSLGModule: expected a list of length > 0.";
        R1 := ring ((fList)#0);
        S1 := ambient R1;
    	I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        pp := char S1;
        tList = apply(tList, tt -> tt*1/1);
        fractionDividedList2 := apply(tList, tt -> decomposeFraction(pp, tt));
            -- fraction divided writes tt = (a/(p^b(p^c-1))
        fractionDividedList := apply(fractionDividedList2, myList -> ( if (myList#2 == 0) then {(pp-1)*(myList#0), myList#1, 1} else myList ) );
    --    aaList := apply(fractionDividedList, zz->zz#0);
        bbList := apply(fractionDividedList, zz->zz#1);
        ccList := apply(fractionDividedList, zz->zz#2);

        if (any(bbList, val -> (val > 0))) then (
            error "HSLGModule: Cannot compute the HSLG module associated to something with p in denominator.";
        );
        ccLCM := lcm(ccList);
        newExpList := apply(fractionDividedList, myList -> (myList#0)*floor( (pp^(ccLCM) - 1)/(pp^(myList#2)-1) ) );
    --    uList := u1 | fList;
    --    powList := (apply(u1, tt -> floor((pp^(ccLCM) - 1)/(pp - 1))) ) | newExpList;
    --    HSLGModule(ccLCM, powList, uList, canIdeal, FrobeniusRootStrategy=>o.FrobeniusRootStrategy)
        curIdeal := ideal(sub(0, R1));
        curHSL := 1;
        curHSLList := null;
        i := 0;

        while (i < #u1) do (
            curHSLList = HSLGModule(ccLCM, {floor((pp^(ccLCM) - 1)/(pp - 1))} | newExpList, {u1#i} | apply(fList, gg -> sub(gg, S1)), canIdeal, o);
            curIdeal = curIdeal + curHSLList#0;
            curHSL = lcm(curHSL, curHSLList#3);
            i = i+1;
        );
        {curIdeal, canIdeal, u1, curHSL}
    )

    HSLGModule(List, List) := o -> (tList, fList) -> (
        if ( not (#tList == #fList) ) then error "HSLGModule: expected the lists to have the same lengths.";
        if ( #fList == 0 ) then error "HSLGModule: expected a list of length > 0.";
        R1 := ring ((fList)#0);
        canIdeal := trim canonicalIdeal(R1);
        S1 := ambient R1;
    	I1 := ideal R1;
        J1 := sub(canIdeal, S1);
        u1 := frobeniusTraceOnCanonicalModule(I1, J1+I1);
        return HSLGModule(tList, fList, canIdeal, u1);
    );

    --the next one is the internal function that does the real work
    --you pass it the base frobeniusRoot to work with
    --the list of exponents of the u's (most frequently 1)
    --the list of u's
    --the canonical ideal (or whatever you want to run HSL on), this one is
    --it computes sigma(canIdeal, f^s g^t h^l ...)
    HSLGModule(ZZ, List, List, Ideal) :=  o-> (ee, expList, u1, canIdeal) -> (
        R1 := ring canIdeal;
        S1 := ambient R1;
        I1 := ideal R1;
        J1 := sub(canIdeal, S1) + I1;
        u2 := apply(u1, gg -> sub(gg, S1));
        --now we do the HSLG computation
        idealIn := J1;
        idealOut := frobeniusRoot(ee, expList, u1, idealIn, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
        HSLCount := 0;
        while (not (idealIn + I1 == idealOut + I1)) do (
            idealIn = idealOut;
            idealOut = frobeniusRoot(ee, expList, u2, idealIn + I1, o);
            HSLCount = HSLCount+1;
        );
        {sub(idealIn, R1), canIdeal, u1, HSLCount}
    );

    ---------------------------------------------------------------------
    ---------------------------------------------------------------------
    --****************************************************
    --*** isFInjective checks if a ring is F-injective ***
    --****************************************************


    isFInjective = method(
        Options =>
        {
    	FrobeniusRootStrategy => Substitution,
    	CanonicalStrategy => Katzman,
    	AssumeCM => false,
    	AssumeReduced => true,
    	AssumeNormal => false,
    	IsLocal => false
        }
    )
    --originally written by Drew Ellingson, with assistance from Karl Schwede

    isFInjective(Ring) := o-> (R1) ->
    (
        d := dim R1;
        S1 := ambient R1;
        I1 := ideal R1;
        FS := null; -- this is the pushFwd of (R-F_*R) to a map of (ambient R) modules. computationally expensive. Only computed if needed.
        F := map(R1,S1);
        d1 := dim S1;
        i := d1-d+1;
        myMap := null; -- maps between ext groups used to test F-injectivity. Computationally expensive and computed where needed.
        flag := true;
        flagPushComputed := false;

        -- F-Injectivity fast to compute on dim(S)-dim(R), so we check there seperately by default
        if (o.CanonicalStrategy === Katzman) then (
            if (isFInjectiveCanonicalStrategy(R1, passOptions( o, { IsLocal, FrobeniusRootStrategy } ) ) == false) then ( -- if F-injectivity fails in top dimension, no need to try any others
            	return false;
        	);
        )
        else (
            i = i - 1;
        );
        --if we assume Cohen-Macaulay, then we are already done
        if (o.AssumeCM == true) then return true;
        --otherwise we next construct G : R -> F_* R
        G := null;

        if (o.AssumeNormal == true) then (d1 = d1 - 2) else if (o.AssumeReduced == true) then (d1 = d1-1);

        while ((i <= d1) and (flag == true)) do (
        	--if ambient pushforward is faster in the next line, use it instead
    	    if (Ext^i(S1^1/I1, S1^1) != 0) then (
        	    if (G === null) then G = frobPFMap(1,R1);
    	        --note we only compute the Frobenius pushforward if the ring is not CM
                if (flagPushComputed == false) then (
                    FS = pushFwdToAmbient(R1,G);   --pushforward Frobenius
                    flagPushComputed == true;
                );

    	        myMap = Ext^i(FS,S1^1); --functorial Ext
    	        if ((dim coker myMap) != -1) then (flag = false;);
    	    );
    	    i = i + 1;
    	);
    	flag
    );

    --the following is an internal function, it checks if is F-injective at the top cohomology (quickly)
    isFInjectiveCanonicalStrategy = method(
        Options => {FrobeniusRootStrategy => Substitution, IsLocal => false}
    )

    isFInjectiveCanonicalStrategy(Ring) := o->(R1) -> (
        S1 := ambient R1;
    	I1 := ideal R1;
    	canIdeal := trim canonicalIdeal(R1);
        J1 := sub(canIdeal, S1) + I1;
        u1 := frobeniusTraceOnCanonicalModule(I1, J1+I1);
        curIdeal := ideal(sub(0, S1));
        i := 0;
        while (i < #u1) do (
            curIdeal = curIdeal + frobeniusRoot(1, {1}, {u1#i}, J1);
            i = i+1;
        );
        if (o.IsLocal == true) then (
            myMax := maxIdeal(S1);
            paramFideal := curIdeal : J1;
            return not isSubset(paramFideal, myMax);
        )
        else (
            if (curIdeal + I1 == J1 + I1) then return true else return false;
        );
    );


    --the following are internal functions
    --this creates the ring map A -> F^e_* A
    frob = method();
    frob(ZZ,Ring) := RingMap => (n,A)-> ( map(A,A,apply(gens A,i -> i^((char A)^n))));

    needsPackage "PushForward";
    --this one computes the Frobenius pushforward of a module F^e_* M
    frobPF = method();
    frobPF(ZZ,Ring):= Sequence => (n,A) -> (pushFwd(frob(n,A)));
    frobPF(Module, ZZ, Ring) := Module => (M,n,A) -> (
            pushFwd(frob(n,A),M);
    );

    --this one construct the map R -> F^e_* R
    frobPFMap = method();
    frobPFMap(ZZ, Ring) := Matrix => (n,A) -> (
    	frobList := frobPF(n,A);
    	map(frobList#0, A^1, (frobList#2)(sub(1, A)))
    );

    --give a map of modules represented by a matrix A over R = S/I, we'd like to represent the module over S.
    --This tries to do this faster than pushFwd.
    pushFwdToAmbient = method();
    pushFwdToAmbient(Ring, Matrix) := (R, A) ->(
        S := ambient(R);
        dimMax := (numRows A);
    --    SMatrix := matrix(apply(flatten entries A, i -> {sub(i,S)}));
        SMatrix := sub(matrix A, S);
    --    oldDefMatrix := matrix(apply( entries presentation target A, j -> apply(j,k -> sub(k, S))));
        oldDefMatrix := sub(presentation target A, S);
        modMatrix := presentation(S^(dimMax)/(ideal(R)));
        defMatrix := oldDefMatrix | modMatrix;
    --    matrixOfZeros := matrix{ apply(numRows modMatrix, z->0) }

        outputMap := map(coker defMatrix,S^1/(ideal(R)), SMatrix  );
        outputMap
    );

    --****************************************************
    --****************************************************
    --This file contains functions related to test ideals.
    --****************************************************
    --****************************************************

    --*********************
    --Preliminary functions
    --*********************

    -- This function computes the element f in the ambient ring S of R=S/I such that
    -- I^{[p^e]}:I = (f) + I^{[p^e]}.
    -- If there is no such unique element, the function returns an error.

    QGorensteinGenerator = method()

    QGorensteinGenerator ( ZZ, Ring ) := ( e, R ) ->
    (
        S := ambient R; -- the ambient ring
        I := ideal R; -- the defining ideal
        gensList := I_*;
        p := char R;
        --principal ideals shouldn't have colons computed
        if #gensList == 1 then return (gensList#0)^(p^e - 1);
        Ie := frobenius( e, I );
        J := trim ( Ie : I ); --compute the colon
        J = trim sub( J, S/Ie ); -- extend colon ideal to S/Ie
        L := J_*; -- grab generators
        if #L != 1 then
            error "QGorensteinGenerator: this ring does not appear to be (Q-)Gorenstein, or you might need to work on a smaller chart. Or the index may not divide p^e-1 for the e you have selected.  Alternately it is possible that Macaulay2 failed to trim a principal ideal.";
        lift( L#0, S )
    )

    QGorensteinGenerator Ring := R -> QGorensteinGenerator( 1, R )

    -- Finds a test element of a ring R = k[x, y, ...]/I (or at least an ideal
    -- containing a nonzero test element).  It views it as an element of the
    -- ambient ring of R. It returns an ideal with some of these elements in it.
    -- One could make this faster by not computing the entire Jacobian/singular
    -- locus. Instead, if we just find one element of the Jacobian not in I, then
    -- that would also work and perhaps be substantially faster.
    -- It assumes that R is a reduced ring.
    testElement = method( Options => { AssumeDomain => false } )

    testElement Ring := o -> R1 ->
    (
        -- Marcus I believe wrote this code to look at random minors instead of all
        -- minors. Note in the current version this will not terminate if the ring
        -- is not generically reduced.
        I1 := ideal R1;
        n1 := #(gens R1) - dim R1;
        M1 := jacobian I1;
        r1 := rank target M1;
        c1 := rank source M1;
        testEle := sub( 0, ambient R1 );
        primesList := {};
        primesList = if o.AssumeDomain then { I1 } else minimalPrimes I1;
        curMinor := ideal sub( 0, ambient R1 );
        while any( primesList, II -> isSubset( ideal testEle, II ) ) do
        (
    	curMinor = ( minors( n1, M1, First => {randomSubset(r1,n1),randomSubset(c1,n1)}, Limit => 1 ) )_*;
    	if #curMinor > 0 then
    	    testEle = if o.AssumeDomain then first curMinor else
    	        testEle + random( coefficientRing R1 )*( first curMinor );
        );
        testEle % I1
    )

    randomSubset = method()

    randomSubset ( ZZ, ZZ ) := ( m, n ) ->
    (
        L := toList( 0..m-1 );
        scan( m-n, i -> L = delete( L#(random(0,m-1-i)), L ) );
        L
    )

    --****************************
    --****************************
    --**New test ideal functions**
    --****************************
    --****************************

    --the following is the new function for computing test ideals written by Karl.

    testIdeal = method(
        Options =>
        {
    	MaxCartierIndex => 10,
    	FrobeniusRootStrategy => Substitution,
    	QGorensteinIndex => 0,
    	AssumeDomain => false
         }
    )

    testIdeal Ring := o -> R1 ->
    (
        canIdeal := canonicalIdeal R1;
        pp := char R1;
        cartIndex := 0;
        fflag := false;
        computedFlag := false;
        curIdeal := ideal 0_R1;
        locPrincList := null;
        computedTau := ideal 0_R1;
        if o.QGorensteinIndex > 0 then
        (
            cartIndex = o.QGorensteinIndex;
            fflag = true
        )
        else
            while not fflag and cartIndex < o.MaxCartierIndex do
    	(
                cartIndex = cartIndex + 1;
                curIdeal = reflexivePower( cartIndex, canIdeal );
                locPrincList = isLocallyPrincipalIdeal curIdeal;
                if locPrincList#0 then fflag = true
            );
        if cartIndex <= 0 or not fflag then error "testIdeal: Ring does not appear to be Q-Gorenstein, perhaps increase the option MaxCartierIndex.  Also see the documentation for isFRegular.";
        if (pp-1) % cartIndex == 0 then
        (
            J1 := testElement( R1, AssumeDomain => o.AssumeDomain );
            h1 := sub(0, ambient R1);
            try h1 = QGorensteinGenerator( 1, R1 ) then (
                computedTau = ascendIdeal( 1, h1, sub( ideal J1, R1 ), FrobeniusRootStrategy => o.FrobeniusRootStrategy );
                computedFlag = true
            )
            else computedFlag = false
        );
        if not computedFlag then --if we haven't already computed it
        (
            gg := first first entries gens trim canIdeal;
            dualCanIdeal := (ideal(gg) : canIdeal);
            nMinusKX := reflexivePower(cartIndex, dualCanIdeal);
            gensList := first entries gens trim nMinusKX;

            runningIdeal := ideal 0_R1;
            omegaAmb := sub( canIdeal, ambient R1 ) + ideal R1;
        	u1 := frobeniusTraceOnCanonicalModule( ideal R1, omegaAmb );
            for x in gensList do
                runningIdeal = runningIdeal + (testModule(1/cartIndex, sub(x, R1), canIdeal, u1, passOptions(o, { FrobeniusRootStrategy, AssumeDomain }) ))#0;
            newDenom := reflexify( canIdeal * dualCanIdeal );
            computedTau = ( runningIdeal*R1 ) : newDenom;
        );
        computedTau
    )

    --this computes \tau(R, f^t)
    testIdeal ( Number, RingElement, Ring ) := o -> ( t1, f1, R1 ) ->
        testIdeal( { t1/1 }, { f1 }, R1, o )

    testIdeal ( Number, RingElement ) := o -> ( t1, f1 ) ->
        testIdeal( { t1/1 }, { f1 }, ring f1, o )

    testIdeal ( List, List ) := o -> ( tList, fList ) ->
        testIdeal( tList, fList, ring fList#0, o )

    testIdeal ( List, List, Ring ) := o -> ( tList, fList, R1 ) ->
    (
        canIdeal := canonicalIdeal R1;
        pp := char R1;
        cartIndex := 0;
        fflag := false;
        computedFlag := false;
        curIdeal := ideal 0_R1;
        locPrincList := null;
        computedTau := ideal 0_R1;
        if o.QGorensteinIndex > 0 then cartIndex = o.QGorensteinIndex
        else
            while not fflag and cartIndex < o.MaxCartierIndex do
    	(
                cartIndex = cartIndex + 1;
                curIdeal = reflexivePower( cartIndex, canIdeal );
                locPrincList = isLocallyPrincipalIdeal curIdeal;
                if locPrincList#0 then fflag = true
            );
        if not fflag then error "testIdeal: Ring does not appear to be Q-Gorenstein, perhaps increase the option MaxCartierIndex.  Also see the documentation for isFRegular.";
        if (pp-1) % cartIndex == 0 then
        (
            J1 := testElement( R1, AssumeDomain => o.AssumeDomain );
            h1 := sub(0, ambient R1);
            try (h1 = QGorensteinGenerator( 1, R1)) then
    	    computedTau = testModule(tList, fList, ideal 1_R1, { h1 }, passOptions( o, { FrobeniusRootStrategy, AssumeDomain } ) )
            else computedFlag = false;
        );
        if not computedFlag then
        (
            gg := first first entries gens trim canIdeal;
            dualCanIdeal := ( ideal gg : canIdeal );
            nMinusKX := reflexivePower( cartIndex, dualCanIdeal );
            gensList := first entries gens trim nMinusKX;

            runningIdeal := ideal 0_R1;
            omegaAmb := sub( canIdeal, ambient R1 ) + ideal R1;
        	u1 := frobeniusTraceOnCanonicalModule( ideal R1, omegaAmb );
            t2 := append( tList, 1/cartIndex );
            f2 := fList;
            for x in gensList do
    	(
                f2 = append( fList, x );
                runningIdeal = runningIdeal + ( testModule( t2, f2, canIdeal, u1, passOptions( o, { FrobeniusRootStrategy, AssumeDomain } ) ) )#0;
            );
            newDenom := reflexify( canIdeal * dualCanIdeal );
            computedTau = ( runningIdeal*R1 ) : newDenom;
        );
        computedTau
    )

    --We can now check F-regularity

    isFRegular = method(
        Options =>
        {
    	AssumeDomain => false,
    	DepthOfSearch => 2,
    	MaxCartierIndex => 10,
    	IsLocal => false,
    	FrobeniusRootStrategy => Substitution,
    	QGorensteinIndex => 0
        }
    )

    isFRegular Ring := o -> R1 ->
    (
        if o.QGorensteinIndex == infinity then
            return nonQGorensteinIsFregular( o.DepthOfSearch, {0}, {1_R1}, R1, passOptions( o, { AssumeDomain, FrobeniusRootStrategy } ) );
      --      return nonQGorensteinIsFregular( o.DepthOfSearch, {0}, {1_R1}, R1, AssumeDomain => o.AssumeDomain, FrobeniusRootStrategy => o.FrobeniusRootStrategy );
        tau := testIdeal( R1, passOptions( o, { AssumeDomain, MaxCartierIndex, FrobeniusRootStrategy, QGorensteinIndex } ) );
    --    tau := testIdeal( R1, AssumeDomain => o.AssumeDomain, MaxCartierIndex => o.MaxCartierIndex, FrobeniusRootStrategy => o.FrobeniusRootStrategy, QGorensteinIndex => o.QGorensteinIndex);
        if o.IsLocal then isSubset( ideal 1_R1, tau + maxIdeal R1 )
        else isSubset( ideal 1_R1, tau )
    )

    isFRegular ( Number, RingElement ) := o -> ( tt, ff ) ->
    (
        tt = tt/1;
        if o.QGorensteinIndex == infinity then
            return nonQGorensteinIsFregular( o.DepthOfSearch, {tt}, {ff}, ring ff, passOptions( o, { AssumeDomain, FrobeniusRootStrategy } ) );
    --        return nonQGorensteinIsFregular( o.DepthOfSearch, {tt}, {ff}, ring ff, AssumeDomain => o.AssumeDomain,  FrobeniusRootStrategy => o.FrobeniusRootStrategy );
        R1 := ring ff;
        tau := testIdeal( tt, ff, passOptions( o, { AssumeDomain, MaxCartierIndex, FrobeniusRootStrategy, QGorensteinIndex } ) );
    --    tau := testIdeal( tt, ff, AssumeDomain => o.AssumeDomain, MaxCartierIndex => o.MaxCartierIndex, FrobeniusRootStrategy => o.FrobeniusRootStrategy, QGorensteinIndex => o.QGorensteinIndex );
        if o.IsLocal then isSubset( ideal 1_R1, tau + maxIdeal R1 )
        else isSubset( ideal 1_R1, tau )
    )

    isFRegular ( List, List ) := o -> ( ttList, ffList ) ->
    (
        if o.QGorensteinIndex == infinity then
            return nonQGorensteinIsFregular( o.DepthOfSearch, ttList, ffList, ring ffList#0, passOptions( o, { AssumeDomain, FrobeniusRootStrategy } ) );
    --        return nonQGorensteinIsFregular( o.DepthOfSearch, ttList, ffList, ring ffList#0, AssumeDomain => o.AssumeDomain,  FrobeniusRootStrategy => o.FrobeniusRootStrategy );
        R1 := ring ffList#0;
        tau := testIdeal( ttList, ffList, passOptions( o, { AssumeDomain,, MaxCartierIndex, FrobeniusRootStrategy, QGorensteinIndex } ) );
    --    tau := testIdeal( ttList, ffList, AssumeDomain => o.AssumeDomain, MaxCartierIndex => o.MaxCartierIndex, FrobeniusRootStrategy => o.FrobeniusRootStrategy, QGorensteinIndex => o.QGorensteinIndex);
        if o.IsLocal then isSubset( ideal 1_R1, tau + maxIdeal R1 )
        else isSubset( ideal 1_R1, tau )
    )

    --the following function is an internal function, it tries to prove a ring is F-regular (it can't prove it is not F-regular, it will warn the user if DebugLevel is elevated)
    nonQGorensteinIsFregular = method(
        Options => { AssumeDomain => false, FrobeniusRootStrategy => Substitution }
    )

    nonQGorensteinIsFregular ( ZZ, List, List, Ring ) := o -> ( n1, ttList, ffList, R1 ) ->
    (
        e := 1;
        cc := (sub(product(apply(#ffList, i -> (ffList#i)^(ceiling(ttList#i)) )), ambient(R1)))*testElement(R1, AssumeDomain => o.AssumeDomain);
        pp := char R1;
        I1 := ideal R1;
        ff1List := apply(ffList, ff->sub(ff, ambient(R1)));
        J1 := I1;
        testApproximate := I1;
        while e < n1 do
        (
            J1 = (frobenius(e, I1)) : I1;
            testApproximate = frobeniusRoot(e, apply(ttList, tt -> ceiling(tt*(pp^e - 1))), ff1List, cc*J1,  FrobeniusRootStrategy => o.FrobeniusRootStrategy);
            if (isSubset(ideal(sub(1, ambient(R1))), testApproximate)) then return true;
            e = e+1;
        );
        if debugLevel > 0 then print "isFRegular: This ring does not appear to be F-regular.  Increasing DepthOfSearch will let the function search more deeply.";
        false
    )

    ----------------------------------------------------------------
    --************************************************************--
    --Functions for checking whether a ring/pair is F-pure--
    --************************************************************--
    ----------------------------------------------------------------

    -- Given an ideal I of polynomial ring R
    -- this uses Fedder's Criterion to check if R/I is F-pure
    -- Recall that this involves checking if I^[p]:I is in m^[p]
    -- Note:  We first check if I is generated by a regular sequence.

    isFPure = method(
        Options => { FrobeniusRootStrategy => Substitution, IsLocal => false }
    )

    isFPure Ring := o -> R1 ->
        isFPure( ideal R1, o )

    isFPure Ideal := o -> I1 ->
    (
        p1 := char ring I1;
        if o.IsLocal then
        (
            maxideal := maxIdeal I1;
            if codim(I1) == numgens(I1) then
    	(
    	    L := flatten entries gens I1;
    	    not isSubset(
    		ideal( product( L, l -> fastExponentiation( p1-1, l ) ) ),
    		frobenius maxideal
    	    )
        	)
            else not isSubset( frobenius( I1 ) : I1, frobenius maxideal )
        )
        else (
            nonFPureLocus := frobeniusRoot( 1, frobenius( I1 ) : I1, FrobeniusRootStrategy => o.FrobeniusRootStrategy );
            nonFPureLocus == ideal( sub( 1, ring I1 ) )
        )
    )

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

beginDocumentation()

--***********************************************
--***********************************************
--Documentation for BasicFunctions.m2
--***********************************************
--***********************************************

doc ///
    Key
        adicDigit
        (adicDigit, ZZ, ZZ, ZZ)
        (adicDigit, ZZ, ZZ, QQ)
        (adicDigit, ZZ, ZZ, List)
    Headline
        digit of the non-terminating expansion of a number in [0,1] in a given base
    Usage
        d=adicDigit(p,e,x)
        D=adicDigit(p,e,L)
    Inputs
        p:ZZ
            greater than 1; the desired base
        e:ZZ
            positive, which specifies which digit is desired
        x:QQ
            in the interval [0,1]; the number whose digit is to be computed
        L:List
            a list of rational numbers in the interval [0,1]
    Outputs
        d:ZZ
            the $e$-th digit of the base $p$ expansion of $x$
        D:List
            consisting of the $e$-th digits of the base $p$ expansion of the elements of $L$
    Description
        Text
            The command {\tt adicDigit(p,e,0)} returns 0.  If $x\in (0,1]$,
            then {\tt adicDigit(p,e,x)} returns the coefficient of $p^{-e}$ in
            the non-terminating base $p$ expansion of $x$.
        Example
            adicDigit(5,4,1/3)
        Text
            If $L$ is a list
            of rational numbers in the unit interval,  {\tt adicDigit(p,e,L)}
            returns a list where this function is applied to each
            element of $L$.
        Example
            adicDigit(5,4,{1/3,1/7,2/3})
    SeeAlso
        adicExpansion
        adicTruncation
///

doc ///
    Key
        adicExpansion
        (adicExpansion, ZZ, ZZ)
        (adicExpansion, ZZ, ZZ, QQ)
        (adicExpansion, ZZ, ZZ, ZZ)
    Headline
        compute adic expansion
    Usage
        L1 = adicExpansion(p,N)
        L2 = adicExpansion(p,e,x)
    Inputs
        p:ZZ
	    greater than 1; the desired base
        N:ZZ
	    positive, whose base $p$ expansion is to be computed
        e:ZZ
	    positive, which specifies how many digits are to be computed
        x:QQ
	    in the interval [0,1], whose base $p$ expansion is to be computed
    Outputs
        L1:List
            consisting of all digits of the terminating base $p$ expansion of $N$
        L2:List
            consisting of the first $e$ digits of the {\em non}-terminating base
            $p$ expansion of $x$
    Description
        Text
            {\tt adicExpansion(p,0)} returns $\{ 0 \}$.
            If $N$ is nonzero, then {\tt adicExpansion(p,N)} returns a list in
            which the $i$th element is the coefficient of $p^i$ in the base $p$
            expansion of $N$.
        Example
            5==1*2^0+0*2^1+1*2^2
            adicExpansion(2,5)
        Text
            {\tt adicExpansion(p,e,0)} returns a list with $e$ elements, all of which
            are zero. If $x$ is nonzero, then {\tt adicExpansion(p,e,x)} returns a
            list of size $e$ in which the $i$th element is the coefficient of
            $p^{-i-1}$ in the unique nonterminating base $p$ expansion of $x$.
            For example, the non-terminating base $2$ expansion of $1/2$ is
            $1/2 = 0/2 + 1/4 + 1/8 + 1/16 + \cdots$, and so
        Example
            adicExpansion(2,4,1/2)
    SeeAlso
        adicDigit
        adicTruncation
///

doc ///
    Key
        adicTruncation
        (adicTruncation, ZZ, ZZ, ZZ)
        (adicTruncation, ZZ, ZZ, QQ)
        (adicTruncation, ZZ, ZZ, List)
    Headline
        truncation of a non-terminating adic expansion
    Usage
        t=adicTruncation(p, e, r)
        T=adicTruncation(p, e, L)
    Inputs
        p:ZZ
            greater than 1; the desired base
        e:ZZ
            nonnegative, which specifies where to truncate
        r:QQ
            nonnegative; the number whose truncation is to be computed
        L:List
            containing nonnegative rational numbers to compute the truncation of
    Outputs
        t:QQ
            the {\tt e}-th truncation of x (base {\tt p})
        T:List
            containing the {\tt e}-th truncations (base {\tt p})
            of the elements of {\tt L}
    Description
        Text
            This function computes the $e$-th truncation of the $p$-adic expansion of
            a rational number.
        Example
            adicTruncation(5, 2, 1/100)
            adicTruncation(5, 4, 1/100)
            adicTruncation(5, 5, 1/1000)
        Text
            If you pass it zero, it returns zero.
        Example
            adicTruncation(4,2,0)
        Text
            You can also pass it a list of numbers, in which case it returns the
            list of the truncations.
        Example
            adicTruncation(5, 5, {1/100, 1/1000})
    SeeAlso
        adicExpansion
        adicTruncation
///


doc ///
    Key
        floorLog
        (floorLog, ZZ, ZZ)
    Headline
        floor of a logarithm
    Usage
     	floorLog(b,x)
    Inputs
        b:ZZ
            greater than 1; the base of the logarithm
        x:ZZ
	    positive
    Outputs
        :ZZ
    Description
        Text
            {\tt floorLog(b,x)} computes {\tt floor(log_b(x))}, correcting occasional
            errors due to rounding.
        Example
            floor( log_3 3^5 )
            floorLog( 3, 3^5 )
///

doc ///
    Key
        multiplicativeOrder
        (multiplicativeOrder, ZZ, ZZ)
    Headline
        multiplicative order of an integer modulo another
    Usage
        multiplicativeOrder(a,b)
    Inputs
        a:ZZ
            the number whose multiplicative order is to be computed
        b:ZZ
            prime to $a$; the modulus
    Outputs
        :ZZ
            the multiplicative order of $a$ mod $b$.
    Description
        Text
            {\tt multiplicativeOrder(a,b)} computes the multiplicative order
            of $a$ modulo $b$.
        Example
            multiplicativeOrder(2, 11^2)
            multiplicativeOrder(3, 11^2)
            multiplicativeOrder(4, 11^2)
        Text
            If $a$ and $b$ are not relatively prime,  {\tt multiplicativeOrder(a,b)}
            returns an error.
///

doc ///
    Key
        decomposeFraction
        (decomposeFraction, ZZ, Number)
        [decomposeFraction, NoZeroC]
    Headline
        decompose a rational number into a/(p^b(p^c-1))
    Usage
        L = decomposeFraction(p,t)
    Inputs
        p:ZZ
            a prime
        t:QQ
            the fraction to be decomposed
        NoZeroC => Boolean
            forces the returned c to not be zero
    Outputs
        L:List
    Description
        Text
            Given a rational number $t$ and a prime $p$, {\tt decomposeFraction(p,t)}
            returns a list {\tt \{a,b,c\}} of integers, with $b$ and $c$ nonnegative,
            such that $t = a/(p^b(p^c-1))$.
        Example
            decomposeFraction( 3, 4/45 )
            4/45 == 64/( 3^2 * ( 3^4 -1 ) )
        Text
            If our number is of the form $a/p^b$ then there is no valid value of $c$ and the
            function returns $c = 0$. Setting the option {\tt NoZeroC => true}
            forces the third entry of the output list to be nonzero, even if
            that means increasing the first entry.
        Example
            decomposeFraction( 3, 4/27)
            decomposeFraction( 3, 4/27, NoZeroC => true )
            4/27 == 8/( 3^3 * ( 3 - 1 ) )
///


doc ///
    Key
        NoZeroC
    Headline
        an option for decomposeFraction
    Description
        Text
            Valid values are {\tt true} or {\tt false}.
    SeeAlso
        decomposeFraction
///

--***********************************************
--***********************************************
--Documentation for frobeniusPowers.m2
--***********************************************
--***********************************************

doc ///
    Key
        fastExponentiation
        (fastExponentiation, ZZ, RingElement)
    Headline
        computes powers of elements in rings of positive characteristic quickly
    Usage
        fastExponentiation(n,f)
    Inputs
        n:ZZ
            nonnegative
     	f:RingElement
            in positive characteristic
    Outputs
        :RingElement
            the $n$-th power of $f$
    Description
        Text
            In prime characteristic $p > 0$, raising a sum $a+b$ to the $p$-th power
            is more quickly done by simply computing $a^p$ and $b^p$ and adding them.
            The basic strategy is to break up the exponent into its base $p$
            expansion, and then use the exponent rules. For example,
            $(x+y)^{3p^2+5p+2} = ((x+y)^3)^{p^2}((x+y)^5)^p(x+y)^2$.
        Example
            R = ZZ/5[x];
            f = sum( 10, i -> x^i );
            time f^321;
            time fastExponentiation(321,f);
        Text
            If an element in a ring of characteristic 0 is passed,
            {\tt fastExponentiation(n,f)} simply computes $f^n$ in the usual way.
///

doc ///
    Key
        frobenius
        [frobenius, FrobeniusRootStrategy]
    Headline
        computes Frobenius powers of ideals and matrices
    Usage
        frobenius(e,I)
        frobenius^e(I)
        frobenius(e,M)
        frobenius^e(M)
        frobenius(I)
        frobenius(M)
    Inputs
        e:ZZ
            the power of Frobenius to take
        I:Ideal
            in a ring of positive characteristic $p > 0$
        M:Matrix
            with entries in a ring of positive characteristic $p > 0$
        FrobeniusRootStrategy => Boolean
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Ideal
	:Matrix
    Description
        Text
            Given an ideal $I$ in a ring of characteristic $p > 0$ and a nonnegative
            integer $e$, {\tt frobenius(e,I)} or {\tt frobenius^e(I)} returns the
            $p^e$-th Frobenius power $I^{[p^e]}$, that is, the ideal generated by
            all powers $f^{p^e}$, with $f \in I$ (see @TO frobeniusPower@).
        Example
            R = ZZ/3[x,y];
            I = ideal(x^2,x*y,y^2);
            frobenius(2,I)
            frobenius^2(I)
            frobeniusPower(3^2,I)
        Text
            If $e$ is negative, then {\tt frobenius(e,I)} or {\tt frobenius^e(I)}
            computes a Frobenius root, as defined by Blickle, Mustata, and Smith
            (see @TO frobeniusRoot@).
        Example
            R = ZZ/5[x,y,z,w];
            I = ideal(x^27*y^10+3*z^28-x^2*y^15*z^35,x^17*w^30+2*x^10*y^10*z^35,x*z^50);
            frobenius(-1,I)
            frobenius(-2,I)
            frobeniusRoot(2,I)
        Text
            If $M$ is a matrix with entries in a ring of positive characteristic
            $p > 0$ and $e$ is a nonnegative integer, then {\tt frobenius(e,M)} or
            {\tt frobenius^e(M)} outputs a matrix whose entries are
            the $p^e$-th powers of the entries of $M$.
        Example
            M = ZZ/3[x,y];
            M = matrix {{x,y},{x+y,x^2+y^2}};
            frobenius(2,M)
        Text
            {\tt frobenius(I)} and {\tt frobenius(M)} are abbreviations for
            {\tt frobenius(1,I)} and {\tt frobenius(1,M)}.
    SeeAlso
        frobeniusPower
        frobeniusRoot
///

doc ///
    Key
        frobeniusPower
        ( frobeniusPower, ZZ, Ideal )
        ( frobeniusPower, QQ, Ideal )
        [frobeniusPower, FrobeniusPowerStrategy]
        [frobeniusPower, FrobeniusRootStrategy]
    Headline
        computes the (generalized) Frobenius power of an ideal
    Usage
        frobeniusPower(n,I)
     	frobeniusPower(t,I)
    Inputs
        n:ZZ
            nonnegative
    	t:QQ
            nonnegative
        I:Ideal
            in a ring of characteristic $p > 0$
        FrobeniusPowerStrategy => Symbol
            control the strategy for frobeniusPower
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Ideal
    Description
        Text
	        {\tt frobeniusPower(t,I)} computes the generalized Frobenius power
            $I^{[t]}$, as introduced by Hernandez, Teixeira, and Witt.
            If the exponent is a power of the characteristic, this is just the
            usual Frobenius power:
        Example
            R = ZZ/5[x,y];
            I = ideal(x,y);
            frobeniusPower(125,I)
        Text
            If $n$ is an arbitrary nonnegative integer, then write the base $p$
            expansion of $n$ as follows: $n = a_0 + a_1 p + a_2 p^2 + ... + a_r p^r$.
            Then the $n$th Frobenius power of $I$ is defined as follows:
            $I^{[n]} = (I^{a_0})(I^{a_1})^{[p]}(I^{a_2})^{[p^2]}\cdots(I^{a_r})^{[p^r]}$.
        Example
            R = ZZ/3[x,y];
            I = ideal(x,y);
            adicExpansion(3,17)
            J1 = I^2*frobenius(1,I^2)*frobenius(2,I);
            J2 = frobeniusPower(17,I);
            J1 == J2
        Text
            If $t$ is a rational number of the form $t = a/p^e$, then
            $I^{[t]} = (I^{[a]})^{[1/p^e]}$.
        Example
            R = ZZ/5[x,y,z];
            I = ideal(x^50*z^95, y^100+z^27);
            frobeniusPower(4/5^2,I)
            frobeniusRoot(2,frobeniusPower(4,I))
        Text
            If $t$ is an arbitrary nonegative rational number, and
            $\{ t_n \} = \{ a_n/p^{e_n} \}$ is a sequence of rational numbers
            converging to $t$ from above, then $I^{[t]}$ is the largest ideal
            in the increasing chain of ideals $\{ I^{[t_n]} \}$.
        Example
            p = 7;
            R = ZZ/p[x,y];
            I = ideal(x^50,y^30);
            t = 6/19;
            expon = e -> ceiling( p^e*t )/p^e; -- a sequence converging to t from above
            scan( 5, i -> print frobeniusPower(expon(i),I) )
            frobeniusPower(t,I)
        Text
            The option {\tt FrobneiusPowerStrategy} controls the strategy for computing the generalized Frobenius power $I^{[t]}$. The two valid options are {\tt Safe} and {\tt Naive}, and the default strategy is {\tt Naive}.
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    SeeAlso
        frobenius
        frobeniusRoot
///

doc ///
    Key
        Naive
    Headline
        a valid value for the option FrobeniusPowerStrategy
    SeeAlso
        FrobeniusPowerStrategy
///

doc ///
    Key
        Safe
    Headline
        a valid value for the option FrobeniusPowerStrategy
    SeeAlso
        FrobeniusPowerStrategy
///

doc ///
    Key
        FrobeniusPowerStrategy
    Headline
        an option for frobeniusPower
    Description
        Text
            Valid options are {\tt Naive} and {\tt Safe}.
    SeeAlso
        frobeniusPower
///

--*************************************************
--*************************************************
--This file contains the documentation for the
--Fsing package.
--*************************************************
--*************************************************


document {
    Key => TestIdeals,
    Headline => "a package for calculations of singularities in positive characteristic ",
    EM "TestIdeals", " is a package for basic computations of F-singularities.
    It is focused on computing test ideals and related objects.
    It does this via ", TO "frobeniusRoot", ", which computes ", TEX ///$I^{[1/p^e]}$///,"
    as introduced by Blickle-Mustata-Smith (this is equivalent to the image of an ideal under the Cartier
        operator in a polynomial ring).",
    BR{},BR{},
    "We describe some notable functions below.",
    BR{},BR{},
    BOLD "Notable functions:",BR{},
    UL {
      {TO "testIdeal", " compute the test ideal of a normal Q-Gorenstein ring or pair."},
      {TO "testModule", " compute the parameter test module of a ring or pair."},
      {TO "parameterTestIdeal", " compute the parameter test ideal of a Cohen-Macaulay ring."},
      {TO "HSLGModule", " compute the stable image of the trace of Frobenius on the canonical module."},
	  {TO "isFRegular", " checks if a normal Q-Gorenstein ring or pair is F-regular."},
	  {TO "isFPure", " checks if a ring is F-pure."},
	  {TO "isFRational", " checks if a  ring is F-rational."},
	  {TO "isFInjective", " checks if a  ring is F-injective."},
	  {TO "compatibleIdeals", " finds the compatibly F-split ideals with a (near) F-splitting."},
	},
	BR{},"Consider for instance the test ideal of the cone over an elliptic curve",
    EXAMPLE{"R = ZZ/5[x,y,z]/ideal(z*y^2-x*(x-z)*(x+z));", "testIdeal(R)" },
    BR{}, "The following example was studied by Anurag Singh when showing that F-regularity does not deform",
    EXAMPLE{"S = ZZ/3[A,B,C,D,T];",
    "m = 4;", "n = 3;",
    "M = matrix{{A^2+T^m, B, D}, {C, A^2, B^n-D}};",
    "I = ideal(T) + minors(2, M);",
    "isFRegular(S/I)"},
    BR{},BR{},
	BOLD "Acknowledgements:",BR{},BR{},
	"The authors would like to thank David Eisenbud, Daniel Grayson, Anurag Singh, Greg Smith, and Mike Stillman for useful conversations and comments on the development of this package.",BR{}
}

-------------------------------------------------------
---------- List of functions to document---------------
-----------(as of 2016-07-18 --------------------------
-------------------------------------------------------
-- frobeniusRoot
-- minimalCompatible
-- Mstar
-------------------------------------------------------
-------------------------------------------------------
-------------------------------------------------------



doc ///
    Key
        ascendIdeal
        (ascendIdeal, ZZ, RingElement, Ideal)
        (ascendIdeal, ZZ, ZZ, RingElement, Ideal)
        (ascendIdeal, ZZ, BasicList, BasicList, Ideal)
        [ascendIdeal, AscentCount]
        [ascendIdeal, FrobeniusRootStrategy]
    Headline
        finds the smallest ideal containing a given ideal which is compatible with a given $p^{-e}$-linear map
    Usage
        ascendIdeal(e, h, J)
        ascendIdeal(e, a, h, J)
        ascendIdeal(e, expList, hList, J)
    Inputs
        J:Ideal
            the ideal to ascend
        h:RingElement
            the element to multiply by at each step of the ascent
        e:ZZ
            the Frobenius root to take at each step of the ascent
        a:ZZ
            the power to raise h to at each step of the ascent
        expList:BasicList
            a list of powers to raise the h's to at each step of the ascent
        hList:BasicList
            a list of elements to multiply by at each step of the ascent
        AscentCount => ZZ
            tell the function to return how many times it took before the ascent of the ideal stabilized
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Ideal
    Description
        Text
            Let $\phi$ be the $p^{-e}$ linear map obtained by multiplying $e$-th Frobenius trace on a polynomial ring by the polynomial $h$  (or $h^a$ if $a$ is given).
            This function finds the smallest $\phi$-stable ideal containing $J$ which is the stable value of ascending chain $J, J+\phi(J), J+\phi(J)+\phi^2(J), \ldots$.
            Note if the ideal $J$ is not an ideal in a polynomial ring, the function will do the computation with $e$-th Frobenius trace in the ambient polynomial ring, but will do the comparison inside the quotient ring (to see if we are done).
        Example
            S = ZZ/5[x,y,z];
            g = x^4+y^4+z^4;
            h = g^4;
            R = S/ideal(g);
            ascendIdeal(1, h, ideal(y^3))
            ascendIdeal(1, h, ideal((sub(y, S))^3))
        Text
            The alternate ways to call the function allow the function to behave in a more efficient way.  Indeed, frequently the polynomial passed is a power, $h^a$.  If $a$ is large, we don't want to compute $h^a$; instead we try to keep the exponent small by only raising it to the minimal power needed to do computation at that time.
        Example
            S = ZZ/5[x,y,z];
            g = x^4+y^4+z^4;
            R = S/ideal(g);
            ascendIdeal(1, 4, g, ideal(y^3))
            ascendIdeal(1, 4, g, ideal((sub(y, S))^3))
        Text
            More generally, if $h$ is a product of powers, $h = h_1^{a_1}\cdots h_n^{a_n}$, then you should pass {\tt ascendIdeal} the lists {\tt expList=\{a_1,\ldots,a_n\}} and {\tt \{h_1,\ldots,h_n\}} of exponents and bases.
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
        Text
            By default (when {\tt AscentCount => true}), {\tt ascendIdeal} just returns the stable (ascended) ideal.  If instead you set {\tt AscentCount=>true} then it returns a list.  The first value is the stable ideal.  The second is how many steps it took to reach that ideal.
        Example
            R = ZZ/5[x,y,z];
            J = ideal(x^12,y^15,z^21);
            f = y^2+x^3-z^5;
            ascendIdeal(1, f^4, J)
            ascendIdeal(1, f^4, J, AscentCount=>true)
        Text
            This method is described in M. Katzman's "Parameter-test-ideals of Cohen–Macaulay rings" (Compositio Mathematica 144 (4), 933-948) under the name "star-closure".
            It is a key tool in computing test ideals and test modules.
    SeeAlso
        testIdeal
        testModule
///


doc ///
    Key
        ascendModule
        (ascendModule,ZZ, Matrix, Matrix)
    Headline
        finds the smallest submodule of free module containing a given submodule which is compatible with a given $p^{-e}$-linear map
    Usage
        ascendModule(e, A, U)
    Inputs
        A:Matrix
        U:Matrix
        e:ZZ
    Outputs
        :Matrix
    Description
        Text
            Given n by n matrix U and submodule A of a free module R^n, ascendModule finds the smallest submodule V of R^n containing A
            and which satisfies U^(1+p+...+p^(e-1)) V\subset V^{[p^e]}
        Example
            R=ZZ/2[a,b,c,d];
            A= matrix {{b*c, a, 0}, {a^2* d, d^2 , c + d}}
            U= matrix {{a^4  + a*b*c^2  + a*b*c*d, a^2* b}, {a^2*c*d^3 , a^3* c*d + a^3 *d^2  + b*c*d^3 }}
            V=ascendModule (1,A,U)
        Text
            This method is described in M Katzman and W. Zhang's "Annihilators of Artinian modules compatible with a Frobenius map"
            under the name "star-closure".
///






doc ///
    Key
        AscentCount
    Headline
        an option for ascendIdeal
    SeeAlso
        [ascendIdeal, AscentCount]
///


doc ///
    Key
        frobeniusRoot
        (frobeniusRoot, ZZ, Ideal)
        (frobeniusRoot, ZZ, MonomialIdeal)
        (frobeniusRoot, ZZ, List, List)
        (frobeniusRoot, ZZ, ZZ, RingElement, Ideal)
        (frobeniusRoot, ZZ, ZZ, RingElement)
        (frobeniusRoot, ZZ, ZZ, Ideal)
        (frobeniusRoot, ZZ, List, List, Ideal)
        (frobeniusRoot, ZZ, Matrix)
        [frobeniusRoot, FrobeniusRootStrategy]
    Headline
        computes I^[1/p^e] in a polynomial ring over a finite field
    Usage
        frobeniusRoot(e, I)
        frobeniusRoot(e, exponentList, idealList)
        frobeniusRoot (e, a, f, I)
        frobeniusRoot (e, a, f)
        frobeniusRoot (e, m, I)
        frobeniusRoot(e, exponentList, idealList, I)
        frobeniusRoot(e, A)
    Inputs
        e:ZZ
            the order of the Frobenius root. E.g., to find the $p^2$-th root of an ideal, set {\tt e = 2}
        I:Ideal
            an ideal in a polynomial ring over a finite field
        idealList:List
            a list of ideals whose product you want to take the root of
        exponentList:List
            a list of exponents which you are raising idealList to. E.g., to find the root of {\tt I^2J^3}, set {\tt idealList = \{I, J\}} and {\tt exponentList = \{2, 3\}}
        a:ZZ
            the exponent you are raising {\tt f} to
        f:RingElement
            a polynomial
        m:ZZ
            the exponent you are raising {\tt I} to
        A:Matrix
        FrobeniusRootStrategy => Symbol
            control the strategy for this function
    Outputs
        :Ideal
    Description
        Text
            In a polynomial ring $R=k[x_1, \ldots, x_n]$ with cofficients in a field of positive characteristic $p$, the Frobenius root $I^{[1/p^e]}$ of an ideal $I$ is the smallest ideal $J$ such that $I\subseteq J^{[p^e]}$ ({\tt = frobeniusPower(J,e)} ).  This function computes it.  Alternately it can be viewed as the image under the trace Cartier map of the ideal $I$.
            Similarly, if the image of $A$ is in $R^k$, the Frobenius root is the smallest submodule $V$ of $R^k$ such that $A\subseteq V^{[p^e]}$.

            There are many ways to call {\tt frobeniusRoot}. The simplest way is to call {\tt frobeniusRoot(e,I)}. For instance,
        Example
            R = ZZ/5[x,y,z];
            I = ideal(x^50*z^95, y^100+z^27);
            frobeniusRoot(2, I)
        Text
            This computes $I^{[1/p^e]}$, i.e. the $p^e$-th root of $I$. Often, one wants to compute the frobeniusRoot of some product of ideals. This is best accomplished by calling the following version of frobeniusRoot:
        Example
            R =  ZZ/5[x,y,z];
            I1 = ideal(x^10, y^10, z^10);
            I2 = ideal(x^20*y^100, x + z^100);
            I3 = ideal(x^50*y^50*z^50);
            frobeniusRoot(1, {4,5,6}, {I1, I2, I3})
        Text
            The above example computes the ideal {\tt (I1^4 I2^5 I3^6)^{[1/p]}}. For legacy reasons, you can specify the last ideal in your list using {\tt frobeniusRoot(e,exponentList,idealList,I)}. This last ideal is just raised to the first power.
        Example
            p=3
            F = GF(p^2,Variable=>a)
            R=F[x,y,z]
            I=ideal(a^(2*p)*x^p+y*z^p+x^p*y^p)
            frobeniusRoot(1,I)
        Text
            frobeniusRoot works over finite fields.
        Example
            R=ZZ/2[a,b,c,d]
            U= matrix {{a^4  + a*b*c^2  + a*b*c*d, a^2* b}, {a^2*c*d^3 , a^3* c*d + a^3 *d^2  + b*c*d^3 }}
            V=frobeniusRoot(1,U)
        Text
            frobeniusRoot computes the smallest $V\subseteq R^2$ such that the image of $U$ is in $V^{[2]}$;
        Text
            You can also call {\tt frobeniusRoot(e,a,f)}. This computes the $e$th root of the principal ideal $(f^a)$. Calling {\tt frobeniusRoot(e,m,I)} computes the $e$th root of the ideal $I^m$, and calling {\tt frobeniusRoot(e,a,f,I)} computes the eth root of the product $f^a I$. Finally, you can also compute the $p^e$-th root of a matrix $A$ by calling {\tt frobeniusRoot(e,A)}.
        Text
            There are two valid inputs for the option {\tt FrobeniusRootStrategy}, namely {\tt Substitution} and {\tt MonomialBasis}.  In the end, for each generator $f$ of an ideal $I$, we are simply writing $f = \sum a_i^{p^e} m_i$ where $m$ is a monomial all of whose exponents are $< p^e$, then all the possible $a_i$ generate the {\tt frobeniusRoot}. {\tt Substitution} and {\tt MonomialBasis} use different methods for gathering these $a_i$, sometimes one method is faster than the other.
    SeeAlso
        frobenius
        frobeniusPower
///

---*
---- not exported
--doc ///
--    Key
--        minimalCompatible
--    Headline
--        computes minimal compatible ideals and submodules.
--    Usage
--        J = minimalCompatible(e, f, I)
--        J = minimalCompatible(a, e, f, I)
--        M = minimalCompatible(e, A, U)
--    Inputs
--        e:ZZ
--        f:RingElement
--        a:ZZ
--        I:Ideal
--        A:Matrix
--        U:Matrix
--    Outputs
--        J:Ideal
--        M:Matrix
--    Description
--        Text
--            minimalCompatible is a method for:
--            (1) finding the smallest ideal $J$ which satisfies $uJ\subset J^{[p^e]}$ and $I \subset J$ for a given ideal $I$ and a given ring element $u$, and
--            (2) finding the smallest submodule $V$ of a free module which satisfies $UV\subset V^{[p^e]}$ and image$(A)\subset V$ for given matrices $A$ and $U$.
--
--///
--*-

---*
-- not exported
--doc ///
--    Key
--        mEthRoot
--    Headline
--        computes p^eth roots of matrices
--    Usage
--        mEthRoot(e, A)
--    Inputs
--        e: ZZ
--        A: Matrix
--    Outputs
--        :Matrix
--///
--*-





doc ///
    Key
        FrobeniusRootStrategy
    Headline
        an option for various functions
    Description
        Text
            An option for various functions and in particular for frobeniusRoot.  The valid options are {\tt Substitution} and {\tt MonomialBasis}.
///

doc ///
    Key
        Substitution
    Headline
        a valid value for the FrobeniusRootStrategy option
///

doc ///
    Key
        MonomialBasis
    Headline
        a valid value for the FrobeniusRootStrategy option
///

doc ///
    Key
        compatibleIdeals
        (compatibleIdeals, RingElement)
        [compatibleIdeals, FrobeniusRootStrategy]
    Headline
        finds all ideals compatibly compatible with a Frobenius near-splitting ideals
    Usage
        compatibleIdeals (u)
    Inputs
        u:RingElement
            the element determining the Frobenius splitting
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :List
    Description
        Text
            The given an element $u$ in a polynomial ring $R$ over a prime field defines a
	    $p^{-e}$ linear map $\phi$: this is obtained by multiplying $e$-th Frobenius trace on a polynomial ring by the polynomial $u$.
	    An ideal $I$ is $\phi$-compatible if $\phi(I)\subseteq I$ or, equivalently, $u I \subseteq I^{[p]}$.
	    This function returns a list of all prime ideals $P$ such that:

            (a) $u P \subseteq P^{[p]}$, and

            (b) $u$ is not in $P^{[p]}$.

            Condition (b) is equivalent to the non-vanishing of the corresponding near-splitting of $R/P$. When $\phi$ is surjective, the set of all $\phi$-compatible ideals consists of all intersections of the
	    primes above.

	    This function is an implementation of the algorithm described in Moty Katzman and Karl Schwede's paper "An algorithm for computing compatibly Frobenius split subvarieties" J. Symbolic Comput. 47 (2012), no. 8, 996-1008.

	    These prime ideals have a "Matlis-dual" interpretation, too. Let $E$ be the injective hull of the residue field of the localization or $R$ at the irrelevant ideal,
	    and let $T: E \rightarrow E$ be the natural Frobenius map. Then $uT$ is a Frobenius map on $E$, and the primes $P$ computed by this function are precisely those for which
	    $uT$ restricts to a non-zero Frobenius map of the annihlator of $P$ on $E$.

            We begin with a simple example (what is split with the coordinate axes in A^2).
        Example
            R = ZZ/3[u,v];
            u = u^2*v^2;
            compatibleIdeals(u)
        Text
            Here is a more substantial example.
        Example
            R=ZZ/2[x_{21},x_{31},x_{32},x_{41},x_{42},x_{43}];
            u=x_{41}*(x_{31}*x_{42}-x_{41}*x_{32})*(x_{41}-x_{21}*x_{42}-x_{31}*x_{43}+x_{21}*x_{32}*x_{43});
            C=compatibleIdeals (u);
            apply(C, print);
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
///

doc ///
    Key
        QGorensteinGenerator
        (QGorensteinGenerator, ZZ, Ring)
        (QGorensteinGenerator, Ring)
    Headline
        finds an element representing the Frobenius trace map of a Q-Gorenstein ring
    Usage
        QGorensteinGenerator(e, R)
        QGorensteinGenerator(R)
    Inputs
        e: ZZ
            the degree in which to search
        R: Ring
            the Q-Gorenstein ring
    Outputs
        :RingElement
    Description
        Text
            Suppose that $R$ is a ring such that $(p^e-1)K_R$ is linearly equivalent to zero (for example, if $R$ is $Q$-Gorenstein with index not divisible by $p$).
            Then if we write $R = S/I$ where $S$ is a polynomial ring, we have that $I^{[p^e]} : I = u S + I^{[p^e]}$ for some $u \in S$.
            By Fedder's criterion, this element $u$ represents the generator of the $R^{1/p^e}$-module $Hom(R^{1/p^e}, R)$.
            For example if $I = (f)$ is principal, then $u = f^{p^e-1}$ works.
        Text
            This function produces the element $f$ described above.  If the user does not specify an integer e, it assumes e = 1.
        Example
            S = ZZ/3[x,y,z];
            f = x^2*y - z^2;
            I = ideal(f);
            R = S/I;
            u = QGorensteinGenerator(1, R)
            u%I^3 == f^2%I^3
        Text
            If Macaulay2 does not recognize that $I^{[p^e]} : I / I^{[p^e]}$ is principal, an error is thrown, which will also happen if R is not Q-Gorenstein of the appropriate index.  Note in the nongraded case, Macaulay2 is not guaranteed to find minimal generators of principally generated modules.
///

doc ///
    Key
        testElement
        (testElement, Ring)
        [testElement, AssumeDomain]
    Headline
        finds a test element of a ring
    Usage
        testElement(R)
    Inputs
        R: Ring
            the ring to find a test element in
        AssumeDomain => Boolean
            assume the ring is a domain
    Outputs
        :RingElement
    Description
        Text
            Given $R = S/I$ where $S$ is a polynomial ring, this finds an element of $S$ that restricts to a test element of $R$.  This does this by finding a minor of the Jacobian whose determinant is not in any minimal prime of the defining ideal of $R$.  This funtion considers random minors until one is found, instead of computing all minors.  Thus, repeated calls will not always produce the same answer.
        Example
            R = ZZ/5[x,y,z]/(x^3+y^3+z^3);
            testElement(R)
            testElement(R)
            testElement(R)
        Text
            If {\tt AssumeDomain => true} then testElement does not to compute the minimal primes of the ring.  This can result in a substantial speedup in some cases.  The default value is {\tt false}.
///

doc ///
    Key
        AssumeDomain
    Headline
        an option to assume a ring is a domain
///

doc ///
    Key
        MaxCartierIndex
    Headline
        an option to specify the maximum number to consider when computing the Cartier index of a divisor
    Description
        Text
                Some functions need to find the smallest value $N$ such that $N$ times a divisor (usually the canonical divisor) is Cartier. By specifying this value, the user controls what the maximal possible Cartier index to consider is.
///


doc ///
    Key
        QGorensteinIndex
    Headline
        an option to specify the index of the canonical divisor, if known
    Description
        Text
             When working in a $Q$-Gorenstein ring frequently we must find an $N$ such that $N * K_R$ is Cartier. This option lets the user skip this search if this integer $N$ is already known by setting {\tt QGorensteinIndex => N}.
///

doc ///
    Key
        DepthOfSearch
    Headline
        an option to specify how hard to search for something
    Description
        Text
             This option is used to tell certain functions how hard to look for an answer.  Increasing it too much can make functions take a lot of time and resources.  Making it too small may mean that an incorrect or incomplete answer is given.  See the documentation for each function.
///

doc ///
    Key
        testIdeal
        (testIdeal, Ring)
        (testIdeal, Number, RingElement)
        (testIdeal, Number, RingElement, Ring)
        (testIdeal, List, List)
        (testIdeal, List, List, Ring)
        [testIdeal, AssumeDomain]
        [testIdeal, FrobeniusRootStrategy]
        [testIdeal, MaxCartierIndex]
        [testIdeal, QGorensteinIndex]
    Headline
        computes the test ideal of f^t in a Q-Gorenstein ring
    Usage
        testIdeal(t, f)
        testIdeal(t, f, R)
        testIdeal(Lexp, Lelts)
        testIdeal(Lexp, Lelts, R)
    Inputs
        R: Ring
        t: QQ
            a formal exponent for f
        f: RingElement
            the element to compute the test ideal of
        Lexp: List
            a list of formal exponents
        Lelts: List
            a list of elements to compute the test ideal of
        AssumeDomain => Boolean
            assume the ring is an integral domain
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
        MaxCartierIndex => ZZ
            sets the maximum Gorenstein index to search for when working with a Q-Gorenstein ambient ring
        QGorensteinIndex => ZZ
            specifies the Q-Gorenstein index of the ring
    Outputs
        :Ideal
    Description
        Text
            Given a normal Q-Gorenstein ring $R$, passing the ring simply computes the test ideal $\tau(R)$.
        Example
            R = ZZ/5[x,y,z]/ideal(x^3+y^3+z^3);
            testIdeal(R)
        Example
            S = ZZ/5[x,y,z,w];
            T = ZZ/5[a,b];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            R = S/(ker f);
            testIdeal(R)
        Text
            Given a normal Q-Gorenstein ring $R$, a rational number $t \geq 0$ and a ring element $f \in R$, we can also compute the test ideal $\tau(R, f^t)$.
        Example
            R = ZZ/5[x,y,z];
            f = y^2 - x^3;
            testIdeal(1/2, f)
            testIdeal(5/6, f)
            testIdeal(4/5, f)
            testIdeal(1, f)
        Example
            R = ZZ/7[x,y,z];
            f = y^2 - x^3;
            testIdeal(1/2, f)
            testIdeal(5/6, f)
            testIdeal(4/5, f)
            testIdeal(1, f)
        Text
            It even works if the ambient ring is not a polynomial ring.
        Example
            R = ZZ/11[x,y,z]/ideal(x^2-y*z);
            f = y;
            testIdeal(1/2, f)
            testIdeal(1/3, f)
        Text
            Alternately, you can instead pass a list of rational numbers $\{t1, t2, ...\}$ and a list of ring elements $\{f1, f2, ...\}$.  In this case it will compute the test ideal $\tau(R, f1^{t1} f2^{t2} ...)$.
        Example
            R = ZZ/7[x,y];
            L = {x,y,(x+y)};
            f = x*y*(x+y);
            testIdeal({1/2,1/2,1/2}, L)
            testIdeal(1/2, f)
            testIdeal({2/3,2/3,2/3}, L)
            testIdeal(2/3, f)
            time testIdeal({3/4,2/3,3/5}, L)
            time testIdeal(1/60, x^45*y^40*(x+y)^36)
        Text
            As above, frequently passing a list will be faster (as opposed to finding a common denominator and passing a single element) since the {\tt testIdeal} can do things in a more intelligent way for such a list.
        Text
            The option {\tt AssumeDomain => true} is used when finding a test element.  The default value is {\tt false}.  The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
        Text
            When working in a Q-Gorenstein ring this function finds an $N$ such that $N * K_R$ is Cartier.  This option controls the maximum value of $N$ to consider.  The default value is $100$.  If you pass this function a ring such that the smallest such $N$ is less that MaxCartierIndex, then the function will throw an error.  This value is ignored if the user specifies the option {\tt QGorensteinIndex}.  In particular, specifying the {\tt QGorensteinIndex} will let the user skip the search for the value $N$.
    SeeAlso
        testModule
        isFRegular
///



doc ///
    Key
        isFRegular
        (isFRegular, Ring)
        (isFRegular, Number, RingElement)
        (isFRegular, List, List)
        [isFRegular, AssumeDomain]
        [isFRegular, FrobeniusRootStrategy]
        [isFRegular, MaxCartierIndex]
        [isFRegular, QGorensteinIndex]
        [isFRegular, IsLocal]
        [isFRegular, DepthOfSearch]
    Headline
        whether a ring or pair is strongly F-regular
    Usage
        isFRegular(R)
        isFRegular(t, f)
        isFRegular(Lexp, Lelts)
    Inputs
        R: Ring
        t: QQ
            a formal exponent for f
        f: RingElement
            the element for the pair, to compute F-regularity
        Lexp: List
            a list of formal exponents
        Lelts: List
            a list of elements for the tuple, to compute F-regularity
        AssumeDomain => Boolean
            assume the ring is an integral domain
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
        MaxCartierIndex => ZZ
            sets the maximum Gorenstein index to search for when working with a Q-Gorenstein ambient ring
        QGorensteinIndex => ZZ
            specifies the Q-Gorenstein index of the ring
        IsLocal => Boolean
            specifies whether to check F-regularity just at the origin
        DepthOfSearch => ZZ
            specifies how hard to try to prove a non-Q-Gorenstein ring is F-regular
    Outputs
        :Boolean
    Description
        Text
            Given a normal Q-Gorenstein ring $R$, this computes whether the ring is strongly F-regular.  It can also prove that a non-Q-Gorenstein ring is F-regular (but cannot show it is not).  See below for how to access this functionality.
        Example
            R = ZZ/5[x,y,z]/ideal(x^2+y*z);
            isFRegular(R)
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            isFRegular(R)
        Text
            It can also do the same computation for a pair.
        Example
            R = ZZ/5[x,y];
            f = y^2-x^3;
            isFRegular(1/2, f)
            isFRegular(5/6, f)
            isFRegular(4/5, f)
            isFRegular(4/5-1/100000, f)
        Text
            When checking whether a ring or pair is strongly F-regular, the option IsLocal determines if this is checked at the origin or everywhere (default is {\tt false}, which corresponds to everywhere).  If you set {\tt IsLocal=>true}, it will only check this at the origin.
        Example
            R = ZZ/7[x,y,z]/ideal((x-1)^3+(y+1)^3+z^3);
            isFRegular(R)
            isFRegular(R, IsLocal=>true)
            S = ZZ/13[x,y,z]/ideal(x^3+y^3+z^3);
            isFRegular(S)
            isFRegular(S, IsLocal=>true)
        Text
            Here is an example of {\tt IsLocal} behavior with a pair.
        Example
            R = ZZ/13[x,y];
            f = (y-2)^2 - (x-3)^3;
            isFRegular(5/6, f)
            isFRegular(5/6, f, IsLocal=>true)
            g = y^2 - x^3;
            isFRegular(5/6, g)
            isFRegular(5/6, g, IsLocal=>true)
        Text
            The option {\tt AssumeDomain => true} is used when finding a test element.  The default value is {\tt false}.  The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
        Text
            When working in a Q-Gorenstein ring this function finds an $N$ such that $N * K_R$ is Cartier.  This option controls the maximum value of $N$ to consider.  The default value is $100$.  If you pass this function a ring such that the smallest such $N$ is less that MaxCartierIndex, then the function will throw an error.  This value is ignored if the user specifies the option {\tt QGorensteinIndex}.  In particular, specifying the {\tt QGorensteinIndex} will let the user skip the search for the value $N$.
        Text
            You can also show that rings that are {\bf NOT} Q-Gorenstein are F-regular (it cannot show that such a ring is {\bf not} F-regular).  To do this, set the option {\tt QGorensteinIndex=>infinity}.  One may change the option {\tt DepthOfSearch} to increase the depth of search.
        Example
            S = ZZ/7[x,y,z,u,v,w];
            I = minors(2, matrix{{x,y,z},{u,v,w}});
            debugLevel = 1;
            time isFRegular(S/I, QGorensteinIndex=>infinity, DepthOfSearch=>1)
            time isFRegular(S/I, QGorensteinIndex=>infinity, DepthOfSearch=>2)
            debugLevel = 0;
    SeeAlso
        testIdeal
        isFRational
///

doc ///
    Key
        isFPure
        (isFPure, Ring)
        (isFPure, Ideal)
        [isFPure, IsLocal]
        [isFPure, FrobeniusRootStrategy]
    Headline
        whether a ring is F-pure
    Usage
        isFPure(R)
        isFPure(I)
    Inputs
        R: Ring
            the ring to check F-purity of
        I: Ideal
            the defining ideal of the ring to check F-purity of
        IsLocal => Boolean
            whether the F-purity is checked at the origin or everwhere
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Boolean
    Description
        Text
            Given a ring $R$, this computes whether the ring is F-pure using Fedder's criterion (by applying @TO frobeniusRoot@ to $I^{[p]} : I$).
        Example
            R = ZZ/5[x,y,z]/ideal(x^2+y*z);
            isFPure(R)
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            isFPure(R)
        Example
            R = ZZ/5[x,y,z]/ideal(x^3+y^3+z^3);
            isFPure(R)
        Text
            Alternately, one may pass it the defining ideal of a ring.
        Example
            S = ZZ/2[x,y,z];
            isFPure(ideal(y^2-x^3))
            isFPure(ideal(z^2-x*y*z+x*y^2+x^2*y))
        Text
            The option {\tt IsLocal} controls whether F-purity is checked at the origin or everywhere.  If you set {\tt IsLocal=>true} (default is {\tt false}), it will only check this at the origin.
        Example
            R = ZZ/5[x,y,z]/ideal((x-1)^3+(y-2)^3+z^3);
            isFPure(R)
            isFPure(R, IsLocal=>true)
            S = ZZ/13[x,y,z]/ideal(x^3+y^3+z^3);
            isFPure(S)
            isFPure(S, IsLocal=>true)
        Text
            Note there is a difference in the strategy for the local or non-local computations.  In fact, checking it everywhere can sometimes be faster than checking the origin.  If {\tt IsLocal=>false} then the function computes @TO frobeniusRoot@ applied to $I^{[p]} : I$, if {\tt IsLocal=>true} then the function checks wheter or not $I^{[p^e]} : I$ is contained in $m^{[p^e]}$ where $m$ is the maximal ideal generated by the variables.
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    SeeAlso
        isFRegular
        isFInjective
///

doc ///
    Key
        canonicalIdeal
        (canonicalIdeal, Ring)
        [canonicalIdeal, Attempts]
    Headline
        given a ring, produces an ideal isomorphic to the canonical module
    Usage
        canonicalIdeal(R)
    Inputs
        R:Ring
        Attempts => ZZ
            how many times the function should try to embed the canonical module as an ideal before giving up
    Outputs
        :Ideal
    Description
        Text
            Given a ring $R$, typically a domain, this produces an ideal isomorphic to the canonical module of $R$.  This will not always produce the same ideal, especially in a non-domain.  It uses the function {\tt embedAsIdeal} from {\tt Divisor.m2}.
        Example
            S = QQ[x,y,u,v];
            T = QQ[a,b];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            R = S/(ker f);
            canonicalIdeal(R)
        Text
            Here's an example in a non-domain.
        Example
            R = ZZ/13[x,y,z]/ideal(x*y, x*z, y*z);
            canonicalIdeal(R)
        Text
            The option {\tt Attempts} is passed to an internal function which embeds the canonical module as an ideal.  This tells it how many times to try before giving up.
///

doc ///
    Key
        frobeniusTraceOnCanonicalModule
    Headline
        finds the u, which in a polynomial ring, determines the Frobenius trace on the canonical module of a quotient of that ring
    Usage
        frobeniusTraceOnCanonicalModule(canIdeal, defIdeal)
    Inputs
        canIdeal:Ideal
            a ring representing the canonical ideal
        defIdeal:Ideal
            the defining ideal of the ring
    Outputs
        :RingElement
    Description
        Text
            Given $R = S/I$, where $S$ is a polynomial ring, there is a map from the canonical module of $R$ back to itself, dual to the Frobenius: $\omega_R^{1/p^e} \to \omega_R$.
            By embedding $\omega_R$ as an ideal $J$ of $R$, one can interpret this map as a $p^e$-inverse linear map on $S$.  But every $p$ inverse linear map on $S$ is a premultiple of the dual to Frobenius on $S$, by some element $u$.  This function finds the $u$.
        Text
            However, because Macaulay2 does not always properly identify an ideal as principal (even though it is), sometimes we cannot find this single $u$ and instead find a list of $u$s, a linear combination of which is the desired $u$.
        Text
            Specifically, you pass this function two ideals.  First, an ideal that restricts to the canonical ideal $J \subseteq R$, and an ideal $I$ that defines the $R$ as a quotient of $S$.  The canonical ideal should be chosen so that it contains the defining ideal (if you do not do this, there may be unexpected behavior).
        Example
            S = ZZ/5[x,y,z,w];
            T = ZZ/5[a,b];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            defIdeal = ker f;
            R = S/defIdeal;
            J = canonicalIdeal(R);
            canIdeal = sub(J, S) + defIdeal;
            frobeniusTraceOnCanonicalModule(canIdeal, defIdeal)
///

doc ///
    Key
        testModule
        (testModule, Ring)
        (testModule, Ring, Ideal)
        (testModule, Number, RingElement)
        (testModule, Number, RingElement, Ideal, List)
        (testModule, List, List)
        (testModule, List, List, Ideal, List)
        [testModule, AssumeDomain]
        [testModule, FrobeniusRootStrategy]
    Headline
        finds the parameter test module of a reduced ring
    Usage
        testModule(R)
        testModule(R, canIdeal)
        testModule(tt, ff)
        testModule(tt, ff, canIdeal, u1)
    Inputs
        R:Ring
        canIdeal:Ideal
            an ideal isomorphic to the canonical module
        tt:QQ
            the formal exponent that ff is raised to
        u1:List
            a list of elements describing the map on hte canonical module
        AssumeDomain => Boolean
            assume whether the ring passed is an integral domain
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Sequence
    Description
        Text
            Computes the parameter test module (as a submodule of the canonical module).  The function returns three values, the parameter test submodule, the canonical module of which it is a subset, and the element $u$ (or $u$s) used to compute this ideal via the method @TO frobeniusTraceOnCanonicalModule@.
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            testModule(R)
        Text
            The canonical module returned is always embedded as an ideal of $R$ (not of the ambient polynomial ring).  Likewise the parameter test submodule is then viewed as a subideal of that.
            With this in mind, because the example above is a Gorenstein ring, the ambient canonical module is the unit ideal.  The next example is not Gorenstein.
        Example
            S = ZZ/3[x,y,u,v];
            T = ZZ/3[a,b];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            R = S/(ker f);
            testModule(R)
        Text
            Note that the output in this case has the parameter test module equal to the canonical module, as it should be.  Let's consider a non-Gorenstein example which is not F-rational.
        Example
            R = ZZ/5[x,y,z]/ideal(y*z, x*z, x*y);
            paraTestMod = testModule(R)
            (paraTestMod#0) : (paraTestMod#1)
        Text
            This function can be used to compute parameter test ideals in Cohen-Macaulay rings
        Example
            S=ZZ/2[X_1..X_5];
            E=matrix {{X_1,X_2,X_2,X_5},{X_4,X_4,X_3,X_1}};
            I=minors(2,E);
            tau=testModule(S/I);
            (tau#0):(tau#1)
        Text
            This function can also be used to compute the parameter test module of a pair $(R, f^t)$.
        Example
            R = ZZ/7[x,y];
            f = y^2 - x^3;
            testModule(5/6, f)
            testModule(5/7, f)
        Text
            This can also be used to compute $(R, f^s g^t)$.
        Example
            R = ZZ/7[x,y];
            f = y^2 - x^3;
            g = x^2 - y^3;
            testModule({1/2, 1/2}, {f, g})
        Text
            Sometimes you would like to specify the ambient canonical module (and choice of u) across multiple calls of testModule.  Those are what the $canIdeal$ or $u1$ can be used to specify.  Finally, the option {\tt FrobeniusRootStrategy} is passed to any calls of @TO frobeniusRoot@ and the option {\tt AssumeDomain} is used when computing a test element.
    SeeAlso
        testIdeal
///

doc ///
    Key
        parameterTestIdeal
        (parameterTestIdeal, Ring)
        [parameterTestIdeal, FrobeniusRootStrategy]
    Headline
        computes the parameter test ideal of a Cohen-Macaulay ring
    Usage
        parameterTestIdeal(R)
    Inputs
        R:Ring
        FrobeniusRootStrategy=>Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Ideal
    Description
        Text
            This computes the parameter test ideal of a Cohen-Macaulay ring.  Technically, it computes $\tau(\omega) : \omega$ where $\omega$ is a canonical module and $\tau(\omega)$ it the (parameter) testModule as computed by @TO testModule@.  For example, the following example is F-rational and so has trivial parameter test ideal.
        Example
            T = ZZ/5[x,y];
            S = ZZ/5[a,b,c,d];
            g = map(T, S, {x^3, x^2*y, x*y^2, y^3});
            R = S/(ker g);
            parameterTestIdeal(R)
        Text
            Consider now a non-F-rational Gorenstein ring where the @TO testIdeal@ and parameterTestIdeal coincide.
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            parameterTestIdeal(R)
            testIdeal(R)
    SeeAlso
        testModule
        testIdeal
///


doc ///
    Key
        isCohenMacaulay
        (isCohenMacaulay, Ring)
        [isCohenMacaulay, IsLocal]
    Headline
        determines if a ring is Cohen-Macaulay
    Usage
        isCohenMacaulay(R)
    Inputs
        R:Ring
        IsLocal => Boolean
            instead call the isCM function from the Depth package which checks if the ring is Cohen-Macaulay only at the origin.
    Outputs
        :Boolean
    Description
        Text
            Determines if a ring is Cohen-Macaulay.  If you pass the {\tt IsLocal parameter}, this will simply call the @TO isCM@ function in the {\tt Depth} package, which checks whether the ring is Cohen-Macaulay at the origin.  This function checks the Cohen-Macaulay property globally and sometimes is much faster than the local computation.
        Example
            T = ZZ/5[x,y];
            S = ZZ/5[a,b,c,d];
            g = map(T, S, {x^3, x^2*y, x*y^2, y^3});
            R = S/(ker g);
            isCohenMacaulay(R)
        Example
            R = QQ[x,y,u,v]/(ideal(x*u, x*v, y*u, y*v));
            isCohenMacaulay(R)
        Text
            The function works as follows.  It considers $R$ as a quotient of an ambient polynomial ring, $R = S/I$.  It takes a resolution of $I$.  If the resolution has length equal to dim $R$ - dim $S$, then it is Cohen-Macaulay.  If the resolution has a different length, and $I$ is homogeneous, then it is not Cohen-Macaulay.  Finally, if the resolution has a different length and I is not homogeneous, the function looks at the $Ext$ groups which compute the depth.
    Caveat
        Warning, this function assumes that Spec $R$ is connected.  In particular, if you pass it a non-equidimensional Cohen-Macaulay ring (for example, if Spec $R$ has two connected components of different dimensions), this function will return false.
///

doc ///
    Key
        IsLocal
    Headline
        an option used to specify whether to only work locally
    Description
        Text
            If true, then the function will only try to work at the origin (the ideal generated by the variables).
///

doc ///
    Key
        isFRational
        (isFRational, Ring)
        [isFRational, IsLocal]
        [isFRational, AssumeCM]
        [isFRational, AssumeDomain]
        [isFRational, FrobeniusRootStrategy]
    Headline
        whether a ring is F-rational
    Usage
        isFRational(R)
    Inputs
        R:Ring
        IsLocal => Boolean
            check F-rationality only at the origin and call the isCM command from the depth package
        AssumeCM => Boolean
            assume whether the ring is Cohen-Macaulay
        AssumeDomain => Boolean
            assume whether the ring is an integral domain
        FrobeniusRootStrategy=>Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Boolean
    Description
        Text
            Determines if a ring is F-rational.  If you pass it {\tt IsLocal=>true}, it will only check if the ring is F-rational at the origin (this can be slower).  If you pass it {\tt AssumeCM=>true}, it will not verify that the ring is Cohen-Macaulay.
        Example
            T = ZZ/5[x,y];
            S = ZZ/5[a,b,c,d];
            g = map(T, S, {x^3, x^2*y, x*y^2, y^3});
            R = S/(ker g);
            isFRational(R)
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            isFRational(R)
        Text
            We conclude with a more interesting example of a ring that is F-rational but not F-regular.  This example first appeared in A. K. Singh's work on deformation of F-regularity.
        Example
             S = ZZ/3[a,b,c,d,t];
             m = 4;
             n = 3;
             M = matrix{ {a^2 + t^m, b, d}, {c, a^2, b^n-d} };
             I = minors(2, M);
             R = S/I;
             isFRational(R)
        Text
            The option {\tt AssumeDomain} is used when computing a test element.  The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    Caveat
        Warning, this function assumes that Spec R is connected.  Like {\tt isCohenMacaulay}, if you pass it a non-equidimensional F-rational ring (for example, if Spec R has two connected components of different dimensions), this function will return false.
///

doc ///
    Key
        HSLGModule
        (HSLGModule, Ring)
        (HSLGModule, Ring, Ideal)
        (HSLGModule, Ideal)
        (HSLGModule, Ring, Ideal, List)
        (HSLGModule, Number, RingElement)
        (HSLGModule, Number, RingElement, Ideal, List)
        (HSLGModule, List, List)
        (HSLGModule, List, List, Ideal, List)
        (HSLGModule, ZZ, List, List, Ideal)
        [HSLGModule, FrobeniusRootStrategy]
    Headline
        computes the submodule of the canonical module stable under the image of the trace of Frobenius
    Usage
        HSLGModule(R)
        HSLGModule(R, canonicalIdeal)
        HSLGModule(canonicalIdeal)
        HSLGModule(R, canonicalIdeal, uList)
        HSLGModule(t, f)
        HSLGModule(t, f, canonicalIdeal, uList)
        HSLGModule(expList, eltList)
        HSLGModule(expList, eltList, canonicalIdeal, uList)
        HSLGModule(e, expList, eltList, canIdeal) --this last command is largely an internal function
    Inputs
        R:Ring
        canonicalIdeal:Ideal
            an ideal isomorphic to the canonical ideal
        f:RingElement
            a ring element, to make a pair
        expList:List
            a list of formal exponents for ring elements, for pairs
        eltList:List
            a list of ring elements, for pairs
        t:Number
            a formal exponent
        expList:List
            a list of formal exponents
        e:ZZ
            an integer, what root of Frobenius to take
        uList:List
            the trace generator in the ambient polynomial ring (a list of elements that generate the trace map)
        FrobeniusRootStrategy=>Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :List
    Description
        Text
            Given a ring $R$ with canonical module $\omega$, this computes the image of $F^e_* \omega \to \omega$ for $e >> 0$.  This image is sometimes called the HSLG-module (named for Hartshorne-Speiser, Lyubeznik and Gabber).  It roughly tells you where a ring is non-F-injective.
        Text
            Specifically, this function returns a list of the following entries.  {\tt HSLGmodule, canonicalModule, u, HSLCount} where {\tt canonicalModule} is the canonical module of the ring (expressed as an ideal), {\tt HSLGmodule} is a submodule of that canonical module, {\tt u} is an element of the ambient polynomial ring representing the trace of Frobenius on the canonical module and {\tt HSLCount} is how many times the trace of Frobenius was computed before the image stabilized.
        Example
            R = ZZ/7[x,y,z]/ideal(x^5+y^5+z^5);
            HSLList = HSLGModule(R);
            HSLList#1 --the ambient canonical module
            HSLList#0 --the HSLGsubmodule
            HSLList#2 --the element representing trace of Frobenius
            HSLList#3 --how many times it took until the image stabilized
        Text
            If you do not want the function to compute the canonical module, you can also pass the canonical module as an ideal.
            You can also pass it something other than the canonical module as well (for example, a submodule of the canonical module).
            In the following example, we compute the non-F-pure ideal of a Q-Gorenstein ring by hijacking this functionality.
        Example
            T = ZZ/7[a,b];
            S = ZZ/7[x,y,z,w];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            I = ker f;
            R = S/I;
            J = ideal(sub(1, R));
            u = QGorensteinGenerator(1, R);
            HSLGModule(R, J, {u})
        Text
            Additionally, you can specify a pair $(R, f^t)$ as long as $t$ is a rational number without $p$ in its denominator.
        Example
            R = ZZ/7[x,y];
            HSLList = HSLGModule(5/6, y^2-x^3);
            HSLList#1 --the canonical module
            HSLList#0
            HSLList = HSLGModule(9/10, y^2-x^3);
            HSLList#0
        Text
            Additionally, we can compute HSLG-modules of things like $(R, f^s g^t)$ even when $R$ is not regular (although we do require that R is Q-Gorenstein with index not divisible by the characteristic).
        Example
            R = ZZ/3[x,y,z]/ideal(x^2-y*z);
            f = y;
            g = z;
            HSLGModule({1/2, 1/2, 1/2}, {y,z,y+z})
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    SeeAlso
        testModule
        isFInjective
///

doc ///
    Key
        isFInjective
        (isFInjective, Ring)
        [isFInjective, FrobeniusRootStrategy]
        [isFInjective, IsLocal]
        [isFInjective, AssumeCM]
        [isFInjective, AssumeNormal]
        [isFInjective, AssumeReduced]
        [isFInjective, CanonicalStrategy]
    Headline
        whether a ring is F-injective
    Usage
        isFInjective(R)
    Inputs
        R:Ring
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
        IsLocal => Boolean
            specify whether to check F-injectivity only at the origin
        AssumeCM => Boolean
            assume the ring is Cohen-Macaulay
        AssumeNormal => Boolean
            assume the ring is normal
        AssumeReduced => Boolean
            assume the ring is reduced
        CanonicalStrategy => Boolean
            specify what strategy to use when computing the Frobenius action on top local cohomology
    Outputs
        :Boolean
    Description
        Text
            This determines whether a ring of finite type over a prime field is F-injective or not.  Over a more general field this checks the F-injectivity of the relative Frobenius.
            We begin with an example of an F-injective ring that is not F-pure (taken from the work of Anurag Singh).
        Example
             S = ZZ/3[a,b,c,d,t];
             m = 4;
             n = 3;
             M = matrix{ {a^2 + t^m, b, d}, {c, a^2, b^n-d} };
             I = minors(2, M);
             R = S/I;
             isFInjective(R)
             isFPure(R)
        Text
            Next let's form the cone over $P^1 \times E$ where $E$ is an elliptic curve.  We begin with a supersingular elliptic curve.  This should be F-injective and only if it is F-pure.
        Example
            S = ZZ/3[xs, ys, zs, xt, yt, zt];
            EP1 = ZZ/3[x,y,z,s,t]/ideal(x^3+y^2*z-x*z^2); --supersingular elliptic curve
            f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
            R = S/(ker f);
            isFInjective(R)
            isFPure(R)
        Text
            Now we do a similar computation this time with an ordinary elliptic curve.
        Example
            S = ZZ/3[xs, ys, zs, xt, yt, zt];
            EP1 = ZZ/3[x,y,z,s,t]/ideal(y^2*z-x^3+x*y*z); --ordinary elliptic curve
            f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
            R = S/(ker f);
            isFInjective(R)
            isFPure(R)
        Text
            If {\tt CanonicalStrategy=>Katzman} which is the default behavior, then the Frobenius action on the top local cohomology (bottom $Ext$) is computed via the method of Katzman.  If it is set to anything else, it is simply brute forced in Macaulay2 using the fuctoriality of Ext.  {\tt CanonicalStrategy=>Katzman} typically is much faster.
        Example
            R = ZZ/5[x,y,z]/ideal(y^2*z + x*y*z-x^3)
            time isFInjective(R)
            time isFInjective(R, CanonicalStrategy=>null)
        Text
            If you set the option {\tt IsLocal => true} (default {\tt false}) it will only check F-injectivity at the origin.  Otherwise it will check it everywhere.  Note checking at the origin can be slower than checking it everywhere.  Consider the example of the following non-F-injective ring.
        Example
            R = ZZ/7[x,y,z]/ideal( (x-1)^5 + (y+1)^5 + z^5 );
            isFInjective(R)
            isFInjective(R, IsLocal=>true)
        Text
            If {\tt AssumeCM=>true} then the function only checks the Frobenius action on top cohomology (which is typically much faster).  The default value is {\tt false}.  Note, that it can give an incorrect answer if the non-injective Frobenius occurs in a lower degree.  Consider the example of the cone over a supersingular elliptic curve times $P^1$.
        Example
            S = ZZ/3[xs, ys, zs, xt, yt, zt];
            EP1 = ZZ/3[x,y,z,s,t]/ideal(x^3+y^2*z-x*z^2);
            f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
            R = S/(ker f);
            time isFInjective(R)
            time isFInjective(R, AssumeCM=>true)
        Text
            If {\tt AssumedReduced=>true} (default {\tt true}) then the bottom local cohomology is avoided (this means the Frobenius action on the top potentially nonzero Ext is not computed).
        Text
            If {\tt AssumeNormal=>true} (default {\tt false}) then we need not compute the bottom two local cohomology modules (or rather their duals).
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    SeeAlso
        isFPure
        testModule
///



doc ///
    Key
        AssumeCM
        AssumeNormal
        AssumeReduced
    Headline
        make assumptions about your ring
    Description
        Text
            These are options used in various functions to make assumptions about your ring.
///


doc ///
    Key
        CanonicalStrategy
    Headline
        an option for isFInjective
    SeeAlso
        isFInjective
///

doc ///
    Key
        Katzman
    Headline
        a valid value for the option CanonicalStrategy
    SeeAlso
        isFInjective
///

-- TESTS

-- floorLog test#1
TEST ///
time J = floorLog(2,3);
assert(J == 1)
///

TEST ///
time J = floorLog(5,26);
assert(J==2)
///

TEST ///
time J = floorLog(5,2);
assert(J==0)
///


-- multiplicativeOrder test#1
TEST ///
time J = multiplicativeOrder(10, 7);
assert(J == 6)
///

TEST ///
time J = multiplicativeOrder(1, 1);
assert(J == 1)
///

TEST ///
time J = multiplicativeOrder(408, 409);
assert(J == 2)
///

-- divideFraction test#1 - (denominator a power of p)
TEST ///
time J = decomposeFraction(7, 19/49);
assert(J == {19, 2, 0} )
///

-- divideFraction test#2 - (denominator not power of p)
TEST ///
time J = decomposeFraction(2, 5/56);
assert(J == {5, 3, 3} )
///

-- divideFraction test#3 - (denominator not power of p)
TEST ///
time J = decomposeFraction(2, 5/24);
assert(J == {5, 3, 2} )
///

-- divideFraction test#4 - (negative)
TEST ///
time J = decomposeFraction(7, -19/49);
assert(J == { -19, 2, 0} )
///

-- adicDigit tests
TEST ///
time J = adicDigit(7, 2, 0);
assert(J == 0)
///

TEST ///
time J = adicDigit(13, 100, 1);
assert(J == 12)
///

TEST ///
time J = adicDigit(3, 2, 3/4);
assert(J == 0)
///

TEST ///
time J = adicDigit(3, 1, 3/4);
assert(J == 2)
///

TEST ///
time J = adicDigit(5, 3, 1/13);
assert(J == 4)
///

TEST ///
L = {3/4, 1/13};
time J = adicDigit(5, 3, L);
assert(J == {3,4})
///

-- adicExpansion tests
TEST ///
time J = adicExpansion(2, 22);
assert(J == {0, 1, 1, 0, 1})
///

TEST ///
time J = adicExpansion(5, 399);
assert(J == {4, 4, 0, 3})
///

TEST ///
time J = adicExpansion(2, 4, 1/5);
assert(J == {0, 0, 1, 1})
///

TEST ///
time J = adicExpansion(7, 7, 1/19);
assert(J == {0, 2, 4, 0, 2, 4,0})
///

-- adicTruncation
TEST ///
time J = adicTruncation(7, 4, 1/19);
assert(J == 18/343)
///

TEST ///
time J = adicTruncation(7, 4, 1/29);
assert(J == 82/2401)
///

TEST ///
time J = adicTruncation(7, 4, {1/19, 1/29});
assert(J == {18/343, 82/2401})
///








TEST /// -- test 0
R = ZZ/5[x,y,z,w]
I = ideal(x^27*y^10+3*z^28+4*x^2*y^15*z^35,x^17*w^30+2*x^10*y^10*z^35,x*z^50)
assert(frobeniusRoot(1,I) == ideal(x^5*y^2+4*y^3*z^7,z^5,x^3*w^6,x^2*y^2*z^7,z^10))
assert(frobeniusRoot(1,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x^5*y^2+4*y^3*z^7,z^5,x^3*w^6,x^2*y^2*z^7,z^10))
assert(frobeniusRoot(2,I) == ideal(x,z,w))
assert(frobeniusRoot(2,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x,z,w))
assert(frobeniusRoot(3,I) == ideal(1_R))
assert(frobeniusRoot(3,I,FrobeniusRootStrategy => MonomialBasis) == ideal(1_R))
///

TEST /// -- test 1
R = GF(27)[x,y,z]
--The ambient ring of GF(27) is ZZ[a]/(a^3-a+1).
I = ideal(a^2*x^18+(a-1)*x^14*y^7*z^4 +x^2*y^10*z^10,(a^2-a)*x^5*y^9*z^8-y^21)
--a^(1/3) = a + 1
--a^(1/9) = a - 1
assert(frobeniusRoot(1,I) == ideal(x^6,a*x^4*y^2*z+y^3*z^3,x*y^3*z^2,y^7))
assert(frobeniusRoot(1,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x^6,a*x^4*y^2*z+y^3*z^3,x*y^3*z^2,y^7))
assert(frobeniusRoot(2,I) == ideal(x,y))
assert(frobeniusRoot(2,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x,y))
assert(frobeniusRoot(3,I) == ideal(1_R))
assert(frobeniusRoot(3,I,FrobeniusRootStrategy => MonomialBasis) == ideal(1_R))
///

--TEST ///  -- test 2
--    kk = GF(5^4);
--    fg = (gens kk)#0;
--    assert( (getFieldGenRoot(6,5,5^4, kk))^(5^6) == fg)
--///

TEST /// -- test 3 (ascend ideal test)
    pp = 5;
    R = ZZ/pp[x,y,z];
    ff = x^3 + y^3 + z^3;
    cc = x;
    testIdeal1 = ascendIdeal(1, ff^(pp-1), ideal(cc)); --this should be the test ideal
    testIdeal2 = ascendIdeal(1, pp-1, ff, ideal(cc));
    testIdeal3 = ascendIdeal(1, {2, 2}, {ff, ff}, ideal(cc));
    mm = ideal(x,y,z);
    assert( (testIdeal1 == mm) and (testIdeal2 == mm) and (testIdeal3 == mm) )
///

TEST ///  --test 4 (ascend ideal test 2)
    pp = 13;
    R = ZZ/pp[x,y,z];
    ff = x^4 + y^4 + z^4;
    cc = x^3;
    testIdeal1 = ascendIdeal(1, ff^(pp-1), ideal(cc)); --this should be the test ideal
    testIdeal2 = ascendIdeal(1, pp-1, ff, ideal(cc)); --this should be the test ideal
    testIdeal3 = ascendIdeal(1, {5, 7}, {ff, ff}, ideal(cc));
    m2 = (ideal(x,y,z))^2;
    assert( (testIdeal1 == m2) and (testIdeal2 == m2) and (testIdeal3 == m2) )
///

TEST /// --test 5 (frobeniusRoots lists test 1)
    pp = 5;
    R = ZZ/pp[x,y,z];
    ff = x^5 + x*y^6 + y^3*z^4 + z^7;
    II = ideal(x^(2*pp)*x*y + y^(3*pp)*x^2*z, (x*y)^pp*x^3*y*z + (x*z)^pp*x^4*z);
    out1 = frobeniusRoot(1, ideal(ff^12)*II);
    out2 = frobeniusRoot(1, {12}, {ff}, II);
    out3 = frobeniusRoot(1, {12, 1}, {ff, II});
    assert( (out1 == out2) and (out1 == out3) )
///

TEST /// --test6 (compare frobeniusRoot vs frobeniusRootRingElements)
    pp = 5;
    R = ZZ/pp[x,y,z];
    ff = random(3, R) + random(5, R) + random(6, R);
    ak = 55+random(10);
    out1 = time frobeniusRoot(2, {ak}, {ff});
    out2 = time frobeniusRoot(2, ak, ff, FrobeniusRootStrategy=>MonomialBasis);
    assert( out1 == out2 )
///




TEST /// -- fastExponentiation
R = ZZ/5[x,y];
-- some extreme cases
assert( fastExponentiation(0,0_R) == 1_R )
assert( fastExponentiation(409,0_R) == 0_R )
f = -2*x^5+x^3*y^2+x^2*y^3-2*x*y^4-2*y^5;
assert( fastExponentiation(0,f) == 1_R )
assert( fastExponentiation(1,f) == f )
-- less trivial case, in polynomial ring over prime field
time out1 = f^409;
time out2 = fastExponentiation(409,f);
assert( out1 == out2 )
-- quotient ring over prime field
R = R/ideal( f );
g = -x^10+x^9*y-x^8*y^2+2*x^7*y^3-x^6*y^4+x^4*y^6+2*x^3*y^7+2*x*y^9-2*y^10;
assert( fastExponentiation(0,g) == 1_R )
assert( fastExponentiation(1,g) == g )
time out1 = g^409;
time out2 = fastExponentiation(409,g);
assert( out1 == out2 )
-- quotient ring over a GaloisField
R = GF(25)[x,y]/ideal( x^10 + y^7 )
f = (-a+1)*x^4+(-2*a-2)*x^3*y-a*x^2*y^2+x*y^3+(2*a-2)*y^4-2*x^3+(a-2)*x^2*y+(-2*a+2)*x*y^2+(2*a+2)*y^3
assert( fastExponentiation(123,f) == f^123 )
-- polynomial ring over an infinite field
kk = frac( ZZ/3[t] )
R = kk[x,y,z]
f = -t^2*x^3*z+1/(t^2+1)*x*y+t^(-2)*y^2*z^3+x*z*y^2+1/(t-1)*y*z-t^3*x*z^2-y*t^(-1)+6*z*t-y+z*x^7-t^(-4)
assert( fastExponentiation(16,f) == f^16 )
-- quotient ring over an infinite field
R = R/ideal(f)
g = t^3*x^3*y*z+1/(t^2-1)*x*y*z^3+t^(-2)*x^5*y^2*z^3
assert( fastExponentiation(7,g) == g^7 )
///

TEST /// -- eth roots via frobenius and frobeniusPower
R = ZZ/5[x,y,z,w]
I = ideal(x^27*y^10+3*z^28+4*x^2*y^15*z^35,x^17*w^30+2*x^10*y^10*z^35,x*z^50)
assert(frobenius^(-1)(I) == ideal(x^5*y^2+4*y^3*z^7,z^5,x^3*w^6,x^2*y^2*z^7,z^10))
assert(frobenius(-1,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x^5*y^2+4*y^3*z^7,z^5,x^3*w^6,x^2*y^2*z^7,z^10))
assert(frobeniusPower(1/5^2,I) == ideal(x,z,w))
assert(frobenius(-2,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x,z,w))
assert(frobenius^(-3) I == ideal(1_R))
assert(frobeniusPower(1/5^3,I,FrobeniusRootStrategy => MonomialBasis) == ideal(1_R))
///

TEST ///  -- eth roots via frobenius and frobeniusPower
R = GF(27)[x,y,z]
--The ambient ring of GF(27) is ZZ[a]/(a^3-a+1).
I = ideal(a^2*x^18+(a-1)*x^14*y^7*z^4 +x^2*y^10*z^10,(a^2-a)*x^5*y^9*z^8-y^21)
--a^(1/3) = a + 1
--a^(1/9) = a - 1
assert(frobenius^(-1) I == ideal(x^6,a*x^4*y^2*z+y^3*z^3,x*y^3*z^2,y^7))
assert(frobenius(-1,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x^6,a*x^4*y^2*z+y^3*z^3,x*y^3*z^2,y^7))
assert(frobeniusPower(1/3^2,I) == ideal(x,y))
assert(frobeniusPower(1/3^2,I,FrobeniusRootStrategy => MonomialBasis) == ideal(x,y))
assert(frobenius^(-3) I == ideal(1_R))
assert(frobenius(-3,I,FrobeniusRootStrategy => MonomialBasis) == ideal(1_R))
///




-- load "c:/Berkeley-2017/Workshop-2017-Berkeley/Fsing/TestIdeals.m2"
TEST ///

p=2;
R=ZZ/p[x_1..x_5];
E=matrix {{x_1,x_2,x_2,x_5},{x_4,x_4,x_3,x_1}};
I=minors(2,E);

time assert(isCohenMacaulay(R/I) == true);

Omega=canonicalIdeal(R/I);
time assert(substitute(Omega,R)==ideal(x_1, x_4, x_5));
--u=finduOfIdeal(I,Omega);
time tau=testModule(R/I);
assert((tau#1)==Omega);
assert((tau#2)== x_1^3*x_2*x_3+x_1^3*x_2*x_4+x_1^2*x_3*x_4*x_5+x_1*x_2*x_3*x_4*x_5+x_1*x_2*x_4^2*x_5+x_2^2*x_4^2*x_5+x_3*x_4^2*x_5^2+x_4^3*x_5^2);
assert(substitute( (tau#0):(tau#1),R)==ideal(x_1, x_2, x_3+x_4));
time assert(isFRational(R/I)==false);



S=ZZ/101[a,b,x,y,u,v, MonomialOrder=>ProductOrder{2,4}];
time assert(isCohenMacaulay(S) == true);
J=ideal(x-a^4, y-a^3*b, u-a*b^3, v-b^4);
G=gens gb J;
K=selectInSubring(1,G);
time assert(isCohenMacaulay(S/ideal(K)) == false);

pp=11;
R=ZZ/pp[X_1..X_3];
I=ideal(X_1^3+X_2^3+X_3^3);
tau=testModule(R/I);
time assert(substitute( tau#0,R)==ideal(X_1, X_2, X_3));
time assert(isFRational(R/I)==false);


///

TEST /// --an easy veronese
    T = ZZ/5[x,y];
    S = ZZ/5[a,b,c,d];
    g = map(T, S, {x^3, x^2*y, x*y^2, y^3});
    R = S/(ker g);
    assert( isCohenMacaulay(R) );
    assert( isFRational(R) );
///

TEST /// --test for weird user inputs
    R = ZZ/11[];
    assert(isFRational(R));
///

TEST /// --an old F-rational but not F-regular Hochster-Huneke example "Tight closure of parameter ideals and splitting in module-Finite extensions"
    T = ZZ/7[x,y,z]/ideal(x^3-y*z*(y+z));
    S = ZZ/7[a,b,c,d,e];
    g = map(T, S, {x, y^3, y^2*z, y*z^2, z^3});
    R = S/(ker g);
    assert(isFRational(R));
    assert(not isFRegular(R));
///

TEST /// --a simple monomial test
R = ZZ/5[x,y,z];
compatIdeals = compatibleIdeals(x^4*y^4*z^4);
answerList =  {ideal(x,y,z), ideal(x,y), ideal(x,z), ideal(y,z), ideal(x), ideal(y), ideal(z)};
assert( all(compatIdeals, tt->any(answerList, ss -> tt==ss)));
assert(  all(answerList, tt->any(compatIdeals, ss -> tt==ss)) );
///

TEST ///
R=ZZ/2[x_{21},x_{31},x_{32},x_{41},x_{42},x_{43}];
u=x_{41}*(x_{31}*x_{42}-x_{41}*x_{32})*(x_{41}-x_{21}*x_{42}-x_{31}*x_{43}+x_{21}*x_{32}*x_{43});
time CompatibleIdeals=compatibleIdeals(u);
answer=  {
    ideal(x_{21}*x_{32}*x_{43}+x_{21}*x_{42}+x_{31}*x_{43}+x_{41}),
    ideal(x_{32}*x_{41}+x_{31}*x_{42},x_{31}*x_{43}+x_{41},x_{32}*x_{43}+x_{42}),
    ideal(x_{32}*x_{41}+x_{31}*x_{42},x_{31}*x_{43}+x_{41},x_{32}*x_{43}+x_{42},x_{21}*x_{42}+x_{41},x_{21}*x_{32}+x_{31}),
    ideal(x_{31},x_{21},x_{41},x_{32}*x_{43}+x_{42}),
    ideal(x_{42},x_{41},x_{31},x_{21},x_{43}),
    ideal(x_{43},x_{42},x_{41},x_{32},x_{31},x_{21}),
    ideal(x_{42},x_{41},x_{32},x_{31},x_{21}),
    ideal(x_{42},x_{43},x_{41},x_{21}*x_{32}+x_{31}),
    ideal(x_{43},x_{42},x_{41},x_{31},x_{32}),
    ideal(x_{42},x_{31},x_{32},x_{41}),
    ideal(x_{31},x_{41},x_{32}*x_{43}+x_{42}),
    ideal(x_{41},x_{31},x_{42},x_{43}),
    ideal(x_{42},x_{41},x_{43}),
    ideal(x_{41},x_{21}*x_{32}*x_{43}+x_{21}*x_{42}+x_{31}*x_{43}),
    ideal(x_{41},x_{42},x_{21}*x_{32}+x_{31}),
    ideal(x_{42},x_{41},x_{31},x_{21}),
    ideal(x_{41},x_{31},x_{21}),
    ideal(x_{21}*x_{32}+x_{31},x_{32}*x_{41}+x_{31}*x_{42},x_{21}*x_{42}+x_{41}),
    ideal x_{41},
    ideal(x_{41},x_{42}),
    ideal(x_{42},x_{41},x_{31}),
    ideal(x_{41},x_{31}),
    ideal(x_{32}*x_{41}+x_{31}*x_{42})
}
assert( all(CompatibleIdeals, tt->any(answer, ss -> tt==ss)));
assert( all(answer, tt->any(CompatibleIdeals, ss -> tt==ss)));
///


--tests of test ideals of ambient rings
TEST ///
    R1 = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3); --elliptic curve
    assert(testIdeal(R1, FrobeniusRootStrategy=>Substitution) == ideal(x,y,z));
    assert(testIdeal(R1, FrobeniusRootStrategy=>MonomialBasis) == ideal(x,y,z));
///

TEST ///
    R2 = ZZ/3[x,y,z]/ideal(x*y^2-z^2); --pinch point
    assert(testIdeal(R2, FrobeniusRootStrategy=>Substitution) == ideal(y, z));
    assert(testIdeal(R2, FrobeniusRootStrategy=>MonomialBasis) == ideal(y, z));
///

TEST ///
    R3 = ZZ/5[x,y,z]/ideal(x*y-z^2); --quadric cone
    assert(testIdeal(R3, FrobeniusRootStrategy=>Substitution) == ideal(sub(1, R3)));
    assert(testIdeal(R3, FrobeniusRootStrategy=>MonomialBasis) == ideal(sub(1, R3)));
///

TEST ///
    T4 = ZZ/7[x,y]; --veronese in 2 variables
    S4 = ZZ/7[a,b,c,d,e];
    g = map(T4, S4, {x^4, x^3*y, x^2*y^2, x*y^3, y^4});
    R4 = S4/(ker g);
    assert(testIdeal(R4, FrobeniusRootStrategy=>Substitution) == ideal(sub(1, R4)) );
    assert(testIdeal(R4, FrobeniusRootStrategy=>MonomialBasis) == ideal(sub(1, R4)) );
///

TEST ///
    T5 = ZZ/11[x,y,z]; --veronese in 3 variables
    S5 = ZZ/11[a,b,c,d,e,f];
    g = map(T5, S5, {x^2, x*y, x*z, y^2, y*z, z^2});
    R5 = S5/(ker g);
    assert(testIdeal(R5, FrobeniusRootStrategy=>Substitution) == ideal(sub(1, R5)));
    assert(testIdeal(R5, FrobeniusRootStrategy=>MonomialBasis) == ideal(sub(1, R5)));
///

TEST ///
    R6 = ZZ/2[x,y,z]/ideal(z^2-x*y*z-x^2*y-x*y^2); --nonstandard D4-singularity in char 2 (Z/2 quotient)
    assert(testIdeal(R6, FrobeniusRootStrategy=>Substitution) == ideal(x,y,z));
    assert(testIdeal(R6, FrobeniusRootStrategy=>MonomialBasis) == ideal(x,y,z));
///

TEST ///
    S7 = ZZ/2[xu, yu, zu, xv, yv, zv, xw, yw, zw];
    EP7 = ZZ/2[x,y,z,u,v,w]/ideal(y^2*z+z^2*y+x^3, v^2*w+w^2*v+u^3); --cone over product of supersingular elliptic curves in char 2
    g = map(EP7, S7, {x*u, y*u, z*u, x*v, y*v, z*v, x*w, y*w, z*w});
    R7 = S7/(ker g);
    assert(testIdeal(R7, AssumeDomain=>true) == ideal(xu, yu, zu, xv, yv, zv, xw, yw, zw));
///

TEST /// --test for weird input
    R = ZZ/7[];
    assert(testIdeal(R, FrobeniusRootStrategy=>Substitution) == ideal(sub(1, R)));
    assert(testIdeal(R, FrobeniusRootStrategy=>MonomialBasis) == ideal(sub(1, R)));
///


 --tests of test ideals of polynomials in polynomial rings
TEST ///
    R = ZZ/101[x,y];
    assert(testIdeal(5/6-1/(6*101), y^2-x^3, FrobeniusRootStrategy=>Substitution) == ideal(x,y));
    assert(testIdeal(5/6-1/(6*101), y^2-x^3, FrobeniusRootStrategy=>MonomialBasis) == ideal(x,y));
    assert(testIdeal(5/6-2/(6*101), y^2-x^3, FrobeniusRootStrategy=>Substitution) == ideal(sub(1, R)));
    assert(testIdeal(5/6-2/(6*101), y^2-x^3, FrobeniusRootStrategy=>MonomialBasis) == ideal(sub(1, R)));
///

TEST ///
    R = ZZ/13[x,y];
    assert(testIdeal(2/3, y*x*(x+y), FrobeniusRootStrategy=>Substitution) == ideal(x,y));
    assert(testIdeal(2/3, y*x*(x+y), FrobeniusRootStrategy=>MonomialBasis) == ideal(x,y));
    assert(testIdeal(2/3-1/100, y*x*(x+y), FrobeniusRootStrategy=>Substitution) == ideal(sub(1, R)));
    assert(testIdeal(2/3-1/100, y*x*(x+y), FrobeniusRootStrategy=>MonomialBasis) == ideal(sub(1, R)));
///

TEST /// --test for weird input
    R = ZZ/7[x];
    assert(testIdeal(1/2, sub(0, R), FrobeniusRootStrategy=>Substitution) == ideal(sub(0, R)));
    assert(testIdeal(1/2, sub(0, R), FrobeniusRootStrategy=>MonomialBasis) == ideal(sub(0, R)));
///

TEST /// --test the isFRegular function, including in the non-Q-Gorenstein case
    R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
    assert( isFRegular(R) == false);
    assert( isFRegular(R, QGorensteinIndex => infinity) == false);
    assert( isFRegular(R, QGorensteinIndex => infinity, MaxCartierIndex=>20) == false);
    S = ZZ/7[x,y,z, u,v,w];
    I = minors(2, matrix{{x,y,z},{u,v,w}});
    T = S/I;
    assert( isFRegular(T, QGorensteinIndex => infinity, MaxCartierIndex=>30) == true);
    A = ZZ/11[x,y,z]/ideal(x^2-y^3+z^5);
    assert(isFRegular(A) == true);
///

TEST /// --test the isFRegular function for non-Q-Gorenstein pairs (or at least when we forget the Gorenstein property)
    R = ZZ/7[x,y];
    f = y^2-x^3;
    assert(isFRegular(5/6, f) == false);
    assert(isFRegular(5/6, f, QGorensteinIndex=>infinity) == false);
    assert(isFRegular(5/6, f, QGorensteinIndex=>infinity, DepthOfSearch=> 10) == false);
    assert(isFRegular(5/6-1/100, f, QGorensteinIndex=>infinity, DepthOfSearch=> 10) == true);
///

TEST /// --Fedder's original F-injective not F-pure, deformation examples
    S = ZZ/2[x,y,z,u,v];
    I =  minors(2, matrix {{x^2, z, v}, {u, z, y^2}});
    J = I + ideal(x,y);
    assert(isFInjective(S/I));
    assert(isFInjective(S/J));
    assert(isFPure(S/J));
    assert(not isFPure(S/I));
///

TEST /// --cone over P1 times supersingular elliptic curve (non CM)
    S = ZZ/3[xs, ys, zs, xt, yt, zt];
    EP1 = ZZ/3[x,y,z,s,t]/ideal(x^3+y^2*z-x*z^2); --supersingular elliptic curve
    f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
    R = S/(ker f);
    assert(not isFInjective(R));
///

TEST /// --cone over P1 times ordinary elliptic curve (non CM)
    S = ZZ/3[xs, ys, zs, xt, yt, zt];
    EP1 = ZZ/3[x,y,z,s,t]/ideal(y^2*z-x^3+x*y*z); --ordinary elliptic curve
    f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
    R = S/(ker f);
    assert( isFInjective(R) );
///

TEST /// --HSLGModule cone over ordinary elliptic curve
    R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
    HSLmod = HSLGModule(R);
    assert(HSLmod#0 == HSLmod#1);
///

TEST /// --the isLocal option
    R = ZZ/5[x,y,z]/ideal((x-2)^3 + y^3 + z^3); --supersingular
    assert( isFInjective(R, IsLocal=>true) );
    assert( not isFInjective(R) );
///

TEST /// --HSLGModule cone over supersingular elliptic curve
    R = ZZ/5[x,y,z]/ideal(x^3+y^3+z^3);
    HSLmod = HSLGModule(R);
    assert(not (HSLmod#0 == HSLmod#1));
///

TEST /// --HSLGModule cone over supersingular elliptic curve
    R = ZZ/7[x,y]
    HSLmod = HSLGModule(5/6, y^2-x^3);
    assert((HSLmod#0 == HSLmod#1));
///

TEST /// --isFInjective of a ring with no variables
    R = ZZ/17[];
    assert(isFInjective(R));
///

TEST /// --checking brute force F-injective vs canonicalStrategy
    R = ZZ/3[x,y,z]/ideal(y^2*z-x^3+x*y*z); --ordinary
    assert(isFInjective(R));
    assert(isFInjective(R, CanonicalStrategy=>null));
    S = ZZ/3[x,y,z]/ideal(x^3+y^2*z-x*z^2); --supersingular
    assert(not isFInjective(S));
    assert(not isFInjective(S, CanonicalStrategy=>null));
///

end
