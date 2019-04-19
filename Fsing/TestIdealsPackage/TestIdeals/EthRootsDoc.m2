--***********************************************
--***********************************************
--Documentation for EthRoots.m2
--***********************************************
--***********************************************

doc ///
    Key
        ascendIdeal
        (ascendIdeal, ZZ, RingElement, Ideal)
        (ascendIdeal, ZZ, ZZ, RingElement, Ideal)
        (ascendIdeal, ZZ, List, List, Ideal)
        [ascendIdeal, AscentCount]
        [ascendIdeal, FrobeniusRootStrategy]
    Headline
        find the smallest ideal containing a given ideal which is compatible with a given Cartier linear map
    Usage
        ascendIdeal(e,h,J)
        ascendIdeal(e,a,h,J)
        ascendIdeal(e,expList,hList,J)
    Inputs
        J:Ideal
            the ideal to ascend
        h:RingElement
            the element to multiply by at each step of the ascent
        e:ZZ
            the Frobenius root to take at each step of the ascent
        a:ZZ
            the power to raise {\tt h} to at each step of the ascent
        expList:List
            consisting of the powers to raise the elements of {\tt hList} to, at each step of the ascent
        hList:List
            consisting of the elements to multiply by, at each step of the ascent
        AscentCount => Boolean
            tells the function to return the number of steps it took before the ascent of the ideal stabilized
        FrobeniusRootStrategy => Symbol
            selects the strategy for internal {\tt frobeniusRoot} calls
    Outputs
        :Ideal
	    the stable ideal in the ascending chain $J\subseteq J + \phi(J)\subseteq J + \phi(J) + \phi^2(J)\subseteq \cdots$, where $\phi$ is the $p^{-e}$ linear map obtained by multiplying the $e$th Frobenius trace on a polynomial ring by $h$, or $h^a$, or {\tt product(hList,expList,(h,a)->h^a)}
    Description
        Text
            Let $\phi$ be the $p^{-e}$ linear map obtained by multiplying the $e$th Frobenius trace on a polynomial ring by the polynomial $h$  (or $h^a$, if $a$ is given).
            This function finds the smallest $\phi$-stable ideal containing $J$, which is the stable value of the ascending chain $J\subseteq J + \phi(J)\subseteq J + \phi(J) + \phi^2(J)\subseteq \cdots$.
            Note that if the ideal $J$ is not an ideal in a polynomial ring, but in a quotient of a polynomial ring, the function will do the computation with the $e$th Frobenius trace in the ambient polynomial ring, but will do the comparison, to see if stabilization has occured, inside the quotient ring.
        Example
            S = ZZ/5[x,y,z];
            g = x^4 + y^4 + z^4;
            h = g^4;
            R = S/ideal(g);
            ascendIdeal(1, h, ideal(y^3))
            ascendIdeal(1, h, ideal((sub(y, S))^3))
        Text
            The alternate ways to call the function allow the function to behave in a more efficient way. Indeed, frequently the polynomial passed is a power, $h^a$.  If $a$ is large, it is more efficient not to compute $h^a$, but instead, to keep the exponent small by only raising $h$ to the minimal power needed to do the computation at that time.
        Example
            S = ZZ/5[x,y,z];
            g = x^4 + y^4 + z^4;
            R = S/ideal(g);
            ascendIdeal(1, 4, g, ideal(y^3))
            ascendIdeal(1, 4, g, ideal((sub(y, S))^3))
        Text
            More generally, if $h$ is a product of powers, $h = h_1^{a_1}\cdots h_n^{a_n}$, then it is more efficient to pass {\tt ascendIdeal} the lists {\tt expList = \{a_1,\ldots,a_n\}} and {\tt hList = \{h_1,\ldots,h_n\}} of exponents and bases.
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
        Text
            By default (when {\tt AscentCount => false}), {\tt ascendIdeal} just returns the stable (ascended) ideal.  If, instead, {\tt AscentCount} is set to {\tt true}, then {\tt ascendIdeal} returns a list, where the first value is the stable ideal, and the second is the number of steps it took for the ascending chain to stabilize and reach that ideal.
        Example
            R = ZZ/5[x,y,z];
            J = ideal(x^12, y^15, z^21);
            f = y^2 + x^3 - z^5;
            ascendIdeal(1, f^4, J)
            ascendIdeal(1, f^4, J, AscentCount => true)
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
        find the smallest submodule of free module containing a given submodule which is compatible with a given Cartier linear map
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
            Given an $n \times n$ matrix $U$ and a submodule $A$ of a free module $R^n$, {\tt ascendModule} finds the smallest submodule $V$ of $R^n$ containing $A$ and which satisfies $U^{1 + p + \cdots + p^{e-1}} V\subset V^{[p^e]}$.
        Example
            R = ZZ/2[a,b,c,d];
            A = matrix {{b*c, a, 0}, {a^2* d, d^2 , c + d}}
            U = matrix {{a^4  + a*b*c^2  + a*b*c*d, a^2* b}, {a^2*c*d^3 , a^3* c*d + a^3 *d^2  + b*c*d^3 }}
            V = ascendModule( 1, A, U )
        Text
            This method is described in M Katzman and W. Zhang's "Annihilators of Artinian modules compatible with a Frobenius map"
            under the name "star-closure".
///

doc ///
    Key
        AscentCount
    Headline
        an option for ascendIdeal
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
        compute a Frobenius root
    Usage
        frobeniusRoot(e, I)
        frobeniusRoot(e, A)
        frobeniusRoot(e, expList, idealList)
        frobeniusRoot(e, expList, idealList, I)
        frobeniusRoot(e, m, I)
        frobeniusRoot(e, a, f)
        frobeniusRoot(e, a, f, I)
    Inputs
        e:ZZ
            the order of the Frobenius root
        I:Ideal
            an ideal in a polynomial ring over a finite field of characteristic {\tt p}
        A:Matrix
	    with entries in a polynomial ring over a finite field of characteristic {\tt p}
        idealList:List
            containing ideals {\tt I_1,\ldots,I_n}
        expList:List
            containing exponents {\tt a_1,\ldots,a_n} to which the ideals in {\tt idealList} will be raised 
        m:ZZ
            the exponent to which {\tt I} will be raised, before taking the Frobenius root
        f:RingElement
            a polynomial over a finite field of characteristic {\tt p}
        a:ZZ
            the exponent to which {\tt f} will be raised, before taking the Frobenius root
        FrobeniusRootStrategy => Symbol
            controls the strategy for this function
    Outputs
        :Ideal
	    the {\tt p^e}-th Frobenius root of {\tt I} (or {\tt I_1^{a_1}\cdots I_n^{a_n}}, {\tt I_1^{a_1}\cdots I_n^{a_n}I}, {\tt I^m}, {\tt (f^a)}, {\tt f^aI}, depending on the arguments passed)
        :Matrix
	    whose image is the {\tt p^e}-th Frobenius root of the image of the matrix {\tt A} 
    Description
        Text
            In a polynomial ring $R = k[x_1, \ldots, x_n]$ with cofficients in a field of positive characteristic $p$, the $p^e$-th Frobenius root $I^{[1/p^e]}$ of an ideal $I$ is the smallest ideal $J$ such that $I\subseteq J^{[p^e]}$ ({\tt = frobeniusPower(p^e,J)}).   
            Similarly, if $M$ is a submodule of $R^k$, the $p^e$-th Frobenius root of $M$, denoted $M^{[1/p^e]}$, is the smallest submodule $V$ of $R^k$ such that $M\subseteq V^{[p^e]}$.
	    The function {\tt frobeniusRoot} computes such ideals and submodules.

            There are many ways to call {\tt frobeniusRoot}. The simplest way is to call {\tt frobeniusRoot(e,I)}, which computes $I^{[1/p^e]}$.
        Example
            R = ZZ/5[x,y,z];
            I = ideal(x^50*z^95, y^100 + z^27);
            frobeniusRoot(2, I)
        Text
            The function {\tt frobeniusRoot} works over arbitrary finite fields.
        Example
            p = 3;
            R = GF( p^2 )[x,y,z];
            I = ideal(a^(2*p)*x^p + y*z^p + x^p*y^p);
            frobeniusRoot(1,I)
        Text
            For the matrix $A$ below, {\tt frobeniusRoot(1,A)} computes a matrix whose image is the smallest submodule $V$ of $R^2$ such that the image of $A$ is in $V^{[2]}$.
        Example
            R = ZZ/2[a,b,c,d];
            A = matrix {{a^4  + a*b*c^2  + a*b*c*d, a^2* b}, {a^2*c*d^3 , a^3* c*d + a^3 *d^2  + b*c*d^3 }}
            frobeniusRoot(1,A)
        Text
            Often, one wants to compute a Frobenius root of some product of powers of ideals, $I_1^{a_1}\cdots I_n^{a_n}$. This is best accomplished by calling {\tt frobeniusRoot(e,\{a_1,\ldots,a_n\},\{I_1,\ldots,I_n\})}.
        Example
            R =  ZZ/5[x,y,z];
            I1 = ideal(x^10, y^10, z^10);
            I2 = ideal(x^20*y^100, x + z^100);
            I3 = ideal(x^50*y^50*z^50);
            time J1 = frobeniusRoot( 1, {8,10,12}, {I1,I2,I3} );
            time J2 = frobeniusRoot( 1, I1^8 * I2^10 * I3^12 );
	    J1 == J2  
        Text
            For legacy reasons, the last ideal in the list can be specified separately, using {\tt frobeniusRoot(e,\{a_1,\ldots,a_n\},\{I_1,\ldots,I_n\},I)}. The last ideal, {\tt I}, is just raised to the first power.
        Text
            The following are additional ways of calling {\tt frobeniusRoot}:

	    $\bullet$ {\tt frobeniusRoot(e,m,I)} computes the $p^e$-th Frobenius root of the ideal $I^m$.
	    
	    $\bullet$ {\tt frobeniusRoot(e,a,f)} computes the $p^e$-th Frobenius root of the principal ideal ($f^a$). 
	    	    
	    $\bullet$ {\tt frobeniusRoot(e,a,f,I)} computes the $p^e$-th Frobenius root of the product $f^aI$. 
        Text
            There are two valid inputs for the option {\tt FrobeniusRootStrategy}, namely {\tt Substitution} and {\tt MonomialBasis}.  In the computation of the $p^e$-th Frobenius root of an ideal $I$, each generator $f$ of $I$ is written in the form $f = \sum a_i^{p^e} m_i$, where each $m_i$ is a monomial whose exponents are less than $p^e$; then the collection of all the $a_i$, obtained for all generators of $I$, generates the Frobenius root $I^{[1/p^e]}$. {\tt Substitution} and {\tt MonomialBasis} use different methods for gathering these $a_i$, and sometimes one method is faster than the other.
    SeeAlso
        frobenius
        frobeniusPower
///

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
        a valid value for the option FrobeniusRootStrategy
    SeeAlso
	FrobeniusRootStrategy
///

doc ///
    Key
        MonomialBasis
    Headline
        a valid value for the option FrobeniusRootStrategy
    SeeAlso
	FrobeniusRootStrategy
///
