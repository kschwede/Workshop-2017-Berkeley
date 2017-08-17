----------------------------------------------------------------
--************************************************************--
--Functions for computing sigma                               --
--************************************************************--
----------------------------------------------------------------


--Computes Non-Sharply-F-Pure ideals over polynomial rings for (R, fm^{a/(p^{e1}-1)}), 
--at least defined as in Fujino-Schwede-Takagi.
sigmaAOverPEMinus1Poly ={HSL=> false}>> o -> (fm, a1, e1) -> ( 
     Rm := ring fm;
     pp := char Rm;
     m1 := 0;
	e2 := e1;
	a2 := a1;
	--if e1 = 0, we treat (p^e-1) as 1.  
     if (e2 == 0) then (e2 = 1; a2 = a1*(pp-1));
     if (a2 > pp^e2-1) then (m1 = floor((a2-1)/(pp^e2-1)); a2=((a2-1)%(pp^e2-1)) + 1 );
     --fpow := fm^a2;
     IN := ethRoot(e2,ideal(1_Rm)); -- this is going to be the new value.
     -- the previous commands should use the fast power raising when Emily finishes it
     IP := ideal(0_Rm); -- this is going to be the old value.
     count := 0;
     
     --our initial value is something containing sigma.  This stops after finitely many steps.  
     while (IN != IP) do(
		IP = IN;
	  	IN = ethRootRingElements(e2,a2,fm,IP); -- ethRoot(e2,ideal(fpow)*IP);
	  	count = count + 1
     );

     --return the final ideal and the HSL number of this function
     if (o.HSL == true) then {IP*ideal(fm^m1),count} else IP*ideal(fm^m1)
)

--Computes Non-Sharply-F-pure ideals for non-polynomial rings with respect to no pair.
sigmaQGor ={HSL=> false}>> o -> (Rm, gg) -> (
     Sm := ambient Rm; --the polynomial ring that Rm is a quotient of
     hk := findQGorGen(Rm, gg);
     
     IN := ideal(1_Sm);
     count := 0;
     IP := ideal(0_Sm);
     
     while (IN != IP) do(
     	IP = IN;
     	IN = ethRoot(gg,ideal(hk)*IP);
     	count = count + 1
     );
     
     --return the ideal and HSL
     if (o.HSL == true) then {sub(IP,Rm), count} else sub(IP, Rm)
)

--Computes Non-Sharply-F-Pure ideals for non-polynomial rings
--gg is the Gorenstein index
sigmaAOverPEMinus1QGor  ={HSL=> false}>> o -> (fk, a1, e1, gg) -> (
     Rm := ring fk;
     Sm := ambient Rm; --the polynomial ring that Rm is a quotient of
     pp := char Rm;
     ek := lcm(e1,gg); --we need to raise things to common powers
     hk := findQGorGen(Rm, gg); --it will be faster to find the Q-Gorenstein generator
     hl := hk^(sub((pp^ek - 1)/(pp^gg - 1), ZZ) ); --
	fm := lift(fk, Sm); --lift fk to the ambient ring
	fpow := fm^(a1*sub( (pp^ek - 1)/(pp^e1-1), ZZ) );


	IN := sigmaAOverPEMinus1Poly(hk,1,gg);
	count := 0;
	IP := ideal(0_Sm);

	while (IN != IP) do(
		IP = IN;
		IN = ethRoot(e1, ideal(fpow*hl)*IP);
		count = count + 1
	);
	
     --return the final ideal
     if (o.HSL == true) then {sub(IP,Rm), count} else sub(IP,Rm)
	
)



----------------------------------------------------------------
--************************************************************--
--Functions for checking whether a ring/pair is F-pure/regular--
--************************************************************--
----------------------------------------------------------------

-- Given an ideal I of polynomial ring R
-- this uses Fedder's Criterion to check if R/I is F-pure
-- Recall that this involves checking if I^[p]:I is in m^[p]
-- Note:  We first check if I is generated by a regular sequence.

isFPure = I1->(
    maxIdeal:= monomialIdeal(first entries vars ring I1);  
    local answer;
    local cond;
    p1:=char ring I1;
    if codim(I1)==numgens(I1) then(
	L:=flatten entries gens I1;
	cond = isSubset(ideal(product(#L, l-> fastExp(p1-1,L#l))),frobenius( maxIdeal ));
	if(cond==false) then answer=true else answer=false;
	)
    else(
	cond = isSubset((frobenius( I1 )):I1,frobenius( maxIdeal ));
	if(cond==false) then answer=true else answer=false;
	);
    answer
)

isFRegularPoly = method();

--Determines if a pair (R, f^t) is F-regular at a prime
--ideal Q in R, R is a polynomial ring  
isFRegularPoly (RingElement, QQ, Ideal) := (f1, t1, Q1) -> (
     not isSubset(tauPoly(f1,t1), Q1)
)

--Determines if a pair (R, f^t) is F-regular, R a polynomial ring
isFRegularPoly (RingElement, QQ) := (f1, t1) -> (
     isSubset(ideal(1_(ring f1)), tauPoly(f1,t1))
)

--Checks whether (R, f1^(a1/(p^e1-1)) is sharply F-pure at the prime ideal m1
isSharplyFPurePoly = (f1, a1, e1,m1) -> (
     if (isPrime m1 == false) then error "isSharplyFPurePoly: expected a prime ideal.";
     not (isSubset(ideal(f1^a1), frobenius(e1,m1)))
)

--Checks whether a Q-Gorenstein pair is strongly F-regular 
isFRegularQGor = method();

--Computes whether (R, f1^t1) is F-regular, assuming the index of R divides p^e1-1
isFRegularQGor (ZZ, RingElement, QQ) := (e1,f1, t1) ->(
     R := ring f1;
     isSubset(ideal(1_R), tauQGor((ring f1),e1,f1,t1))
)

--Computes whether (R, f1^t1) is F-regular at Q1, assuming the index of R divides p^e1-1
isFRegularQGor (ZZ, RingElement, QQ, Ideal) := (e1,f1, t1, Q1) ->(
     not isSubset(tauQGor((ring f1),e1,f1,t1), Q1)
)

--Assuming no pair
isFRegularQGor (Ring,ZZ) := (R,e1) ->(
     isSubset(ideal(1_R), tauQGor(R,e1,1_R,1/1 ) )
)

--Assuming no pair checking at Q1
isFRegularQGor (Ring,ZZ,Ideal) := (R,e1,Q1) ->(
     not isSubset(tauQGor(R,e1,1_R,1/1 ),Q1 )
)


----------------------------------------------------------------
--************************************************************--
--Auxiliary functions for F-signature and Fpt computations.   --
--************************************************************--
----------------------------------------------------------------
 
--- Computes the F-signature for a specific value a1/p^e1
--- Input:
---	e - some positive integer
---	a - some positive integer between 0 and p^e
---	f - some polynomial in two or three variables in a ring R of PRIME characteristic
--- Output:
---	returns value of the F-signature of the pair (R, f^{a/p^e})
--- Code is based on work of Eric Canton
fSig = (f, a, e) -> (
     R := ring f;
     p := char ring f;     
     1 - p^(-e*dim(R))*degree( frobenius( e, maxIdeal R) + ideal( fastExp( a, f ) )) 
)  

--Calculates the x-int of the secant line between two guesses for the fpt
--Input:
--     t - some positive rational number
--     b - the f-signature of (R,f^{t/p^e})
--     e - some positive integer
--     t1- another rational number > t
--     f - some polynomial in two or three variables in a ring of PRIME characteristic
--
-- Output:
--	fSig applied to (f,t1,e)
--	x-intercept of the line passing through (t,b) and (t1,fSig(f,t1,e))
threshInt = (f,e,t,b,t1)-> (
     b1:=fSig(f,t1,e);
{b1,xInt(t,b,t1/(char ring f)^e,b1)}
)


--********************************************
--Some functions for the purpose of checking whether a map of rings is a splitting.  It also computes images of (field) trace.
--********************************************

needsPackage "PushForward"; 

--checks whether f1 : R1 -> S1 splits as a map of R1-modules
isMapSplit = (f1) -> (
	J1 := imageOfRelativeCanonical(f1);
	val := false;
	if (1 % J1 == 0) then val = true;
	
	val
)

--computes the image of Hom_R1(S1, R1) -> R1.
imageOfRelativeCanonical = (f1) -> (
	outList := pushFwd(f1);
--	myGenerators := first entries (outList#1);	
	target1 := (outList#2)(sub(1, target f1));
	
	h1 := map(outList#0, (source f1)^1, target1);
	
	d1 := Hom(h1, (source f1)^1);
	
	trim ideal( first entries gens image d1)
)

--computes the image of trace : S \to R if S is a finite R-module.
imageOfTrace = (f1) -> (
	print "Warning, this only works right now if S is a free module.  We should try to fix it...";
	outList := pushFwd(f1);
	myGenerators := first entries (outList#1);	
	i := 0;
	traceList := {};
	newMap := null;
	newMatrix := null;
	S1 := target f1;
	
	while (i < #myGenerators) do (
		newMap = map(S1^1, S1^1, {{myGenerators#i}});
		newMatrix = pushFwd(newMap, f1);
		traceList = append(traceList, trace newMatrix);
		i = i+1;
	);
	
	trim ideal traceList
)

