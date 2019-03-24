---------------------------------------------------------------------
---------------------------------------------------------------------
--**************************************
--*** HSLGModule computes the stable ***
--*** image under trace of \omega    ***
--*** This is dual to the stable     ***
--*** kernel of Frobenius acting on  ***
--*** local cohomology               ***
--**************************************

HSLGModule = method(
    TypicalValue => Sequence,
    Options => { FrobeniusRootStrategy => Substitution, CanonicalIdeal=>null, CurrentRing=>null, GeneratorList=>null }
)
--it returns two ideals, a ring element, and an integer.
--The first ideal is an ideal isomorphic to the non-F-injective module
--and the second is an ideal isomorphic to the canonical module, in which the parameter
--resides. The locus where these two ideals differ (plus the non-CM locus) is the
--locus where the ring does not have rational singularities.
--The third element is the element of the ambient polynomial ring which is used to
--induce the canonical trace map (or a list of elements).
--Finally, it also outputs the associated HSL(G)-number.
-- (HSLMod, CanMod, u, HSL#)


--we install the method for for no arguments
installMethod(HSLGModule,
    o->() -> (
        curRing := o.CurrentRing;
        canIdeal := o.CanonicalIdeal;
        uList := o.GeneratorList;
        if ( (not (curRing === null)) and (canIdeal === null) ) then (--if no canonicalIdeal is chosen
            canIdeal = canonicalIdeal curRing;
        );
        if (canIdeal===null) then (error "HSGLModule: cannot compute the HSLGModule with no arguments or optional arguments";)
        else (--if we have a canonical ideal (or built one)
            if (curRing === null) then curRing = ring canIdeal;
            if (uList === null) then ( --build the uList if needed
                S1 := ambient curRing;
                I1 := ideal curRing;
                J1 := sub(canIdeal, S1);
                uList = frobeniusTraceOnCanonicalModule(I1, J1);
            )
        );
        return internalHSLGModule(curRing, canIdeal, uList, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
    )
)

HSLGModule ( Number, RingElement ) := Sequence => opts -> ( tt, ff ) ->
(
    R1 := opts.CurrentRing;
    canIdeal := opts.CanonicalIdeal;
    uList := opts.GeneratorList;

    if (R1 === null ) then R1 = ring ff;
    if (canIdeal === null) then canIdeal = trim canonicalIdeal R1;
    S1 := ambient R1;
    I1 := ideal R1;
    J1 := sub( canIdeal, S1 );
    if (uList === null) then uList = frobeniusTraceOnCanonicalModule( I1, J1 );

    internalHSLGModule( tt, ff, canIdeal, uList,FrobeniusRootStrategy=>opts.FrobeniusRootStrategy )
)

HSLGModule ( List, List ) := Sequence => opts -> ( tList, fList ) ->
(
    if #tList != #fList then error "HSLGModule: expected the lists to have the same lengths";
    if #fList == 0 then error "HSLGModule: expected a nonempty list";

    R1 := opts.CurrentRing;
    canIdeal := opts.CanonicalIdeal;
    uList := opts.GeneratorList;

    if (R1 === null ) then R1 = ring( fList#0 );
    if (canIdeal === null) then canIdeal = trim canonicalIdeal R1;
    S1 := ambient R1;
    I1 := ideal R1;
    J1 := sub( canIdeal, S1 );
    if (uList === null) then uList = frobeniusTraceOnCanonicalModule( I1, J1 );

    internalHSLGModule( tList, fList, canIdeal, uList,FrobeniusRootStrategy=>opts.FrobeniusRootStrategy )
)

--this version is only to be called by real experts as to what is going on.
HSLGModule (ZZ, List, List ) := Sequence => opts -> (e1, expList, fList ) ->
(
    if #expList != #fList then error "HSLGModule: expected the lists to have the same lengths";
    if #fList == 0 then error "HSLGModule: expected a nonempty list";

    R1 := opts.CurrentRing;
    canIdeal := opts.CanonicalIdeal;
    --uList := opts.GeneratorList; (ulist is ignored for this construction)

    if (R1 === null ) then R1 = ring( fList#0 );
    if (canIdeal === null) then canIdeal = trim canonicalIdeal R1;
    S1 := ambient R1;
    J1 := sub( canIdeal, S1 );

    internalHSLGModule( e1, expList, fList, canIdeal,FrobeniusRootStrategy=>opts.FrobeniusRootStrategy )
)

internalHSLGModule = method(
    TypicalValue => Sequence,
    Options => { FrobeniusRootStrategy => Substitution }
)

--internalHSLGModule Ring := Sequence => o -> R1 -> HSLGModule( R1, canonicalIdeal R1, o )

--HSLGModule ( Ring, Ideal ) := Sequence => o -> ( R1, canIdeal ) ->
--(
 --   S1 := ambient R1;
--    I1 := ideal R1;
--    J1 := sub( canIdeal, S1 );
--    u1 := frobeniusTraceOnCanonicalModule( I1, J1 );
--    HSLGModule( R1, canIdeal, u1 )
--)

internalHSLGModule ( Ring, Ideal, List ) := Sequence => o -> ( R1, canIdeal, u1 ) ->
(
    S1 := ambient R1;
    I1 := ideal R1;
    J1 := sub( canIdeal, S1 );

    curIdeal := ideal 0_R1;
    curHSL := 1;
    local curHSLList;
    scan( u1, u->
	(
            curHSLList = internalHSLGModule( 1, {1}, {u}, canIdeal, o );
            curIdeal = curIdeal + curHSLList#0;
            curHSL = lcm( curHSL, curHSLList#3 )
	)
    );
    ( trim curIdeal, canIdeal, u1, curHSL )
)

--HSLGModule Ideal := Sequence => o -> canIdeal -> HSLGModule( ring canIdeal, canIdeal, o )

internalHSLGModule ( Number, RingElement, Ideal, List ) := Sequence => o -> ( tt, ff, canIdeal, u1 ) ->
(
    R1 := ring ff;
    S1 := ambient R1;
    if ring( u1#0 ) =!= S1 then error "internalHSLGModule: Exptected u1 to be in the ambient polynomial ring";
    I1 := ideal R1;
    J1 := sub( canIdeal, S1 );
    pp := char S1;
    tt = tt / 1;
    (aa, bb, cc) := decomposeFraction( pp, tt, NoZeroC => true );
        -- fraction divided writes tt = (a/(p^b(p^c-1))
    if bb > 0 then error "internalHSLGModule: Cannot compute the HSLG module associated to something with p in denominator";
    newExp := floor( ( pp^cc - 1 )/( pp - 1 ) );
--    uList := append(u1, ff);
--    powList = append(powList, aa);
    --now we have to do a sum again since Macaulay2 might not find one u in the nongraded case.
    curIdeal := ideal 0_R1;
    curHSL := 1;
    local curHSLList;
    scan( u1, u ->
	(
            curHSLList = internalHSLGModule( cc, {newExp, aa}, {u, ff}, canIdeal, o );
            curIdeal = curIdeal + curHSLList#0;
            curHSL = lcm(curHSL, curHSLList#3)
        )
    );
    ( trim curIdeal, canIdeal, u1, curHSL )
)


internalHSLGModule ( List, List, Ideal, List ) := Sequence => o -> ( tList, fList, canIdeal, u1 ) ->
(
    if #tList != #fList then error "internalHSLGModule: expected the lists to have the same lengths";
    if #fList == 0 then error "internalHSLGModule: expected a nonempty list";
    R1 := ring ( fList#0 );
    S1 := ambient R1;
    I1 := ideal R1;
    J1 := sub( canIdeal, S1 );
    pp := char S1;
    tList = tList / 1;
    fractionDividedList := apply( tList, tt -> decomposeFraction( pp, tt, NoZeroC => true ) );
        -- fraction divided writes tt = (a/(p^b(p^c-1))
    bbList := apply( fractionDividedList, zz -> zz#1 );
    ccList := last \ fractionDividedList;

    if any( bbList, val -> val > 0 ) then
        error "internalHSLGModule: Cannot compute the HSLG module associated to something with p in denominator";
    ccLCM := lcm ccList;
    newExpList := apply( fractionDividedList, myList -> (myList#0) * floor( (pp^ccLCM - 1) / (pp ^(myList#2) - 1) ) );
--    uList := u1 | fList;
--    powList := (apply(u1, tt -> floor((pp^(ccLCM) - 1)/(pp - 1))) ) | newExpList;
--    HSLGModule(ccLCM, powList, uList, canIdeal, FrobeniusRootStrategy=>o.FrobeniusRootStrategy)
    curIdeal := ideal 0_R1;
    curHSL := 1;
    local curHSLList;
    scan( u1, u ->
	(
            curHSLList = internalHSLGModule(ccLCM, {floor((pp^(ccLCM) - 1)/(pp - 1))} | newExpList, {u} | apply(fList, gg -> sub(gg, S1)), canIdeal, o);
            curIdeal = curIdeal + curHSLList#0;
            curHSL = lcm(curHSL, curHSLList#3)
        )
    );
    ( trim curIdeal, canIdeal, u1, curHSL )
)



--the next one is the internal function that does the real work
--you pass it the base frobeniusRoot to work with
--the list of exponents of the u's (most frequently 1)
--the list of u's
--the canonical ideal (or whatever you want to run HSL on), this one is
--it computes sigma(canIdeal, f^s g^t h^l ...)
internalHSLGModule ( ZZ, List, List, Ideal ) :=  Sequence => o -> ( ee, expList, u1, canIdeal ) ->
(
    R1 := ring canIdeal;
    S1 := ambient R1;
    I1 := ideal R1;
    J1 := sub( canIdeal, S1 ) + I1;
    u2 := apply( u1, gg -> sub( gg, S1 ) );
    --now we do the HSLG computation
    idealIn := J1;
    idealOut := frobeniusRoot( ee, expList, u1, idealIn, FrobeniusRootStrategy => o.FrobeniusRootStrategy );
    HSLCount := 0;
    while idealIn + I1 != idealOut + I1 do
    (
        idealIn = idealOut;
        idealOut = frobeniusRoot( ee, expList, u2, idealIn + I1, o );
        HSLCount = HSLCount + 1;
    );
    ( trim sub( idealIn, R1 ), canIdeal, u1, HSLCount )
)

---------------------------------------------------------------------
---------------------------------------------------------------------
--****************************************************
--*** isFInjective checks if a ring is F-injective ***
--****************************************************

isFInjective = method(
    TypicalValue => Boolean,
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

isFInjective Ring := Boolean => o-> R1 ->
(
    d := dim R1;
    S1 := ambient R1;
    I1 := ideal R1;
    FS := null; -- this is the pushFwd of (R-F_*R) to a map of (ambient R) modules. computationally expensive. Only computed if needed.
    F := map( R1, S1 );
    d1 := dim S1;
    i := d1 - d + 1;
    myMap := null; -- maps between ext groups used to test F-injectivity. Computationally expensive and computed where needed.
    flag := true;
    flagPushComputed := false;

    -- F-Injectivity fast to compute on dim(S)-dim(R), so we check there seperately by default
    if o.CanonicalStrategy === Katzman then
    (
	-- if F-injectivity fails in top dimension, no need to try any others
         if not isFInjectiveCanonicalStrategy(R1, passOptions( o, { IsLocal, FrobeniusRootStrategy } ) )  then return false
    )
    else i = i - 1;

    --if we assume Cohen-Macaulay, then we are already done
    if o.AssumeCM then return true;
    --otherwise we next construct G : R -> F_* R
    G := null;

    if o.AssumeNormal then d1 = d1 - 2 else if o.AssumeReduced then d1 = d1 - 1;

    while i <= d1 and flag do
    (
    	--if ambient pushforward is faster in the next line, use it instead
	    if Ext^i( S1^1/I1, S1^1 ) != 0 then
	    (
    	        if G === null then G = frobPFMap( 1, R1 );
	        --note we only compute the Frobenius pushforward if the ring is not CM
                if not flagPushComputed then
		(
		    FS = pushFwdToAmbient( R1, G );   --pushforward Frobenius
                    flagPushComputed = true
                );
	        myMap = Ext^i( FS, S1^1 ); --functorial Ext
	        if (dim coker myMap) != -1 then flag = false;
	    );
	    i = i + 1;
	);
	flag
)

--the following is an internal function, it checks if is F-injective at the top cohomology (quickly)
isFInjectiveCanonicalStrategy = method(
    TypicalValue => Boolean,
    Options => { FrobeniusRootStrategy => Substitution, IsLocal => false }
)

isFInjectiveCanonicalStrategy Ring := Boolean => o -> R1 ->
(
    S1 := ambient R1;
    I1 := ideal R1;
    canIdeal := trim canonicalIdeal R1;
    J1 := sub( canIdeal, S1 ) + I1;
    u1 := frobeniusTraceOnCanonicalModule( I1, J1 );
    curIdeal := ideal 0_S1;
    scan( u1, u -> curIdeal = curIdeal + frobeniusRoot( 1, {1}, {u}, J1 ) );
    if o.IsLocal then
    (
        myMax := maxIdeal S1;
        paramFideal := curIdeal : J1;
        not isSubset( paramFideal, myMax )
    )
    else curIdeal + I1 == J1 + I1
)

--the following are internal functions
--this creates the ring map A -> F^e_* A
frob = method( TypicalValue => RingMap );
frob ( ZZ, Ring ) := RingMap => ( n, A )-> map( A, A, apply( gens A, i -> i^((char A)^n)) )

needsPackage "PushForward";

--this one computes the Frobenius pushforward of a module F^e_* M
frobPF = method( TypicalValue => Sequence )

frobPF ( ZZ, Ring ) := Sequence => ( n, A ) -> pushFwd frob( n, A )

frobPF ( Module, ZZ, Ring ) := Module => ( M, n, A ) -> pushFwd( frob( n, A ), M )

--this one construct the map R -> F^e_* R
frobPFMap = method( TypicalValue => Matrix )

frobPFMap ( ZZ, Ring ) := Matrix => ( n, A ) ->
(
    frobList := frobPF( n, A );
    map( frobList#0, A^1, (frobList#2)(sub(1, A)) )
)

--give a map of modules represented by a matrix A over R = S/I, we'd like to represent the module over S.
--This tries to do this faster than pushFwd.
pushFwdToAmbient = method( TypicalValue => Matrix )

pushFwdToAmbient ( Ring, Matrix ) := Matrix => ( R, A ) ->
(
    S := ambient R;
    dimMax := numRows A;
--    SMatrix := matrix(apply(flatten entries A, i -> {sub(i,S)}));
    SMatrix := sub( matrix A, S );
--    oldDefMatrix := matrix(apply( entries presentation target A, j -> apply(j,k -> sub(k, S))));
    oldDefMatrix := sub( presentation target A, S );
    modMatrix := presentation( S^dimMax / ideal(R) );
    defMatrix := oldDefMatrix | modMatrix;
--    matrixOfZeros := matrix{ apply(numRows modMatrix, z->0) }

    map(coker defMatrix, S^1 / ideal(R), SMatrix )
)
