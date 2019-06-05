numberWithMinimalDenominator = (A,B,D) ->
(
    d := D;
    while ceiling( d*B - 1) < floor( d*A + 1 ) do d = d + 1;
    ( d, floor( d*A + 1 )/d )
)

--this is some alternate guessFPT code, it tries to do it based on the value that
--has the smallest computational expense
--we assume that each 1/(p^e-1) takes 1.5*e more computations than a 1/p value.
guessFPTWeighted = { Verbose => false } >> o -> ( pp, a, b, minGenSize ) ->(
    --startDenom := (numberWithMinimalDenominator(a,b,2))#0;
    --coreDenom := ceiling(startDenom*log_2(startDenom)) + 1; -- this is the max denominator we will look for
    coreDenom := ceiling((1/(b-a))^(2/3));
    numList := findNumbersBetween((a, b), coreDenom);
    while (#numList < minGenSize) do (coreDenom = 2*coreDenom; numList = findNumberBetween((a, b), coreDenom));
    --pp := char ring f;
    local u;
    local v;
    local w;
    local wt;
    weightList := apply(numList, i -> (
        (u,v,w) = decomposeFraction(pp, i);
        wt = v + 1*w;
        --if (wt == 0) then 1/0;
        --d = (timing(isFJumpingExponent(i, f)))#0;
        return(wt, i)));
        --return (i, wt, d, 1.0*(d)/wt)));

    return weightList;
)

  --This function finds rational numbers in the range of the interval
--with the given denominator, it is a helper function for guessFPTAlt
findNumberBetweenWithDenom = (myInterv, myDenom)->(
     upperBound := floor((myInterv#1)*myDenom)/myDenom;
          --finds the number with denominator myDenom less than the upper
	  --bound of myInterv
     lowerBound := ceiling((myInterv#0)*myDenom)/myDenom;
          --finds the number with denominator myDenom greater than the lower
	  -- bound of myInterv
     if (upperBound >= lowerBound) then (
	  --first we check whether there is anything to search for
	  apply( 1+numerator((upperBound-lowerBound)*myDenom), i-> lowerBound+(i/myDenom) )
     )
     else(
	  {}
     )
)


--This function finds rational numbers in the range of
--the interval; the max denominator allowed is maxDenom.
findNumbersBetweenV2 = (myInterv, maxDenom)->(
    divisionChecks :=  new MutableList from maxDenom:true;
         -- creates a list with maxDenom elements all set to true.
    outList := {};
    i := 2;
    while (i <= maxDenom) do (
        outList = join(outList, findNumberBetweenWithDenom(myInterv, i));
        i = i+1;
    );
    sort(toList set outList)
)

--This function finds rational numbers in the range of
--the interval; the max denominator allowed is maxDenom.
findNumbersBetween = (myInterv, maxDenom)->(
    divisionChecks :=  new MutableList from maxDenom:true;
         -- creates a list with maxDenom elements all set to true.
    outList := {};
    i := maxDenom;
    while (i > 0) do (
        if ((divisionChecks#(i-1)) == true) then --if we need to do a computation..
            outList = join(outList,findNumberBetweenWithDenom(myInterv, i));
        factorList := getFactorList(i);
     	apply(#factorList, j-> (divisionChecks#( (factorList#j)-1) = false) );
	    i = i - 1;
    );
    sort(toList set outList)
)

--Returns the power set of a given list, except it leaves out
--the emptyset.
--For example {2,3,4} becomes { (2),(3),(4),(2,3),(2,4),(3,4),(2,3,4) }
nontrivialPowerSet = (myList) ->(
     apply(2^(#myList)-1, i-> getSublistOfList(myList, getNonzeroBinaryDigits(i+1,0) ) )
)

--This turns a number into a list of factors with repeats
--For example, 12 becomes (2,2,3)
numberToPrimeFactorList = (nn)->(
     prod := factor nn;
     flatten (apply(#prod, i -> toList(((prod#(i))#1):((prod#(i))#0)) ))
)

--Returns a list of all proper factors of nn, for use with sieving...
getFactorList = (nn) ->(
     if (nn < 1) then error "getFactorList: expected an integer greater than 1.";
     powSet := nontrivialPowerSet(numberToPrimeFactorList(nn));
     toList ( set apply(#powSet, i->product(powSet#i)) )
)


--Returns the digits in nn which are nonzero in binary
--for example, 5 in binary is 101, so this would return {0,2}
--the second term tells me where to start the count, so passing
--5,0 gives {0,2} but 5,1 is sent to {1,3}.  i should be
--used only for recursive purposes
getNonzeroBinaryDigits = (nn, i) -> (
--    error "breakme";
    halfsies := nn//2;
    val1 := nn%2;
    val2 := false;
    if (halfsies > 0) then val2 = (getNonzeroBinaryDigits(nn//2,i+1));
    if ( (val1 != 0) and (not (val2 === false))) then (
	 flatten {i, val2}
    )
    else if (val1 != 0) then (
	 {i}
    )
    else if ( not (val2 === false)) then (
	 flatten {val2}
    )
    else(
	 false
    )
)

--Returns the entries of myList specified by entryList
--For example, ( {1,2,3}, {0,2}) is sent to {1,3}
getSublistOfList = (myList, entryList) -> (
     --error "help";
     apply( #entryList, i->myList#(entryList#i) )
)
