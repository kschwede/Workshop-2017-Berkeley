--this file has modifications of functions in TestIdeals.

randomSubset = method()

randomSubset ( ZZ, ZZ ) := ( m, n ) ->
(
    L := toList( 0..m-1 );
    scan( m-n, i -> L = delete( L#(random(0,m-1-i)), L ) );
    L
)

testElementNotIn = method( Options => {FrobeniusRootStrategy=>Substitution} )

testElementNotIn(Ideal) := o -> Q1 ->
(
    R1 := ring Q1;
    I1 := ideal R1;
    Q2 := sub(Q1, ambient R1) + I1;
    n1 := #(gens R1) - dim R1;
    M1 := jacobian I1;
    r1 := rank target M1;
    c1 := rank source M1;
    testEle := sub( 0, ambient R1 );
    primesList := {};
    primesList = minimalPrimes Q2;
    curMinor := ideal sub( 0, ambient R1 );
    while any( primesList, II -> isSubset( ideal testEle, II ) ) do
    (
        curMinor = ( minors( n1, M1, First => {randomSubset(r1,n1),randomSubset(c1,n1)}, Limit => 1 ) )_*;
        if #curMinor > 0 then
        testEle = testEle + random( coefficientRing R1 )*( first curMinor );
    );
    testEle % I1
);

--this is a slight modification of the internalTestModule command.
--it differs from the one in TestIdeals because we specify a test element
internalTestModule = method(Options =>{});

internalTestModule ( List, List, Ideal, List ) := o -> ( ttList, ffList, canIdeal, u1 ) ->
(
    ff := ffList#0;
    R1 := ring ff;
    pp := char R1;
    S1 := ambient R1;
    fff := sub(ff, S1);
    I1 := ideal R1;
    J1 := sub(canIdeal, S1);

    C1 := testElementNotIn(canIdeal);

    ffList = apply(ffList, zz->sub(zz, S1));
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
    if #u1 > 1 then
    (
        print "internalTestModule: Multiple trace map for omega generators (Macaulay2 failed to find the principal generator of a principal ideal).  Using them all.";
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
    else
    (
        u1 = u1#0;
        curTau = ascendIdeal(lcmCs, append(aaListForCsReduced, floor((pp^lcmCs - 1)/(pp-1))), append(ffList, u1), (product(prodList))*C1*J1*R1, FrobeniusRootStrategy=>o.FrobeniusRootStrategy);
                --note, we only have an ideal(ff) in the test element here since by construction,
                --aaa/(pp^ccc-1) is less than 1.
                --if we need to take more roots, do so...
        curTau = sub(curTau, S1);
        tau = frobeniusRoot(maxBs, append(aaListForAfterAscension, floor((pp^maxBs - 1)/(pp-1))), append(ffList, u1), curTau, FrobeniusRootStrategy => o.FrobeniusRootStrategy);
    );

    (sub(tau, R1), sub(J1, R1), u1)
)
