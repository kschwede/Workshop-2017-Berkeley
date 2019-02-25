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
        expList:List
            a list of powers to raise the h's to at each step of the ascent
        hList:List
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
            Given an $n \times n$ matrix $U$ and a submodule $A$ of a free module $R^n$, {\tt ascendModule} finds the smallest submodule $V$ of $R^n$ containing $A$ and which satisfies $U^{1+p+\cdots+p^{e-1}} V\subset V^{[p^e]}$.
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
        compute a Frobenius root of an ideal in a polynomial ring over a finite field
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
            In a polynomial ring $R=k[x_1, \ldots, x_n]$ with cofficients in a field of positive characteristic $p$, the Frobenius root $I^{[1/p^e]}$ of an ideal $I$ is the smallest ideal $J$ such that $I\subseteq J^{[p^e]}$ ({\tt = frobeniusPower(p^e,J)} ).  This function computes it.  Alternately it can be viewed as the image under the trace Cartier map of the ideal $I$.
            Similarly, if the image of $A$ is in $R^k$, the Frobenius root is the smallest submodule $V$ of $R^k$ such that $A\subseteq V^{[p^e]}$.

            There are many ways to call {\tt frobeniusRoot}. The simplest way is to call {\tt frobeniusRoot(e,I)}. 
        Example
            R = ZZ/5[x,y,z];
            I = ideal(x^50*z^95, y^100+z^27);
            frobeniusRoot(2, I)
        Text
            This computes $I^{[1/p^e]}$, i.e., the $p^e$-th root of $I$. Often, one wants to compute the frobeniusRoot of some product of ideals. This is best accomplished by calling the following version of frobeniusRoot.
        Example
            R =  ZZ/5[x,y,z];
            I1 = ideal( x^10, y^10, z^10 );
            I2 = ideal( x^20*y^100, x + z^100 );
            I3 = ideal( x^50*y^50*z^50 );
            frobeniusRoot( 1, {4,5,6}, {I1, I2, I3} )
        Text
            The above example computes the ideal {\tt (I1^4 I2^5 I3^6)^{[1/p]}}. For legacy reasons, the last ideal in the list can be specified separately, using {\tt frobeniusRoot(e,exponentList,idealList,I)}. The last ideal $I$ is just raised to the first power.
        Text
            The function {\tt frobeniusRoot} works over arbitrary finite fields.
        Example
            p = 3
            F = GF( p^2, Variable => a )
            R = F[x,y,z]
            I = ideal( a^(2*p)*x^p+y*z^p+x^p*y^p )
            frobeniusRoot(1,I)
        Text
            For the matrix $A$ below, {\tt frobeniusRoot(1,A)} computes the smallest $V\subseteq R^2$ such that the image of $A$ is in $V^{[2]}$.
        Example
            R = ZZ/2[a,b,c,d]
            A = matrix {{a^4  + a*b*c^2  + a*b*c*d, a^2* b}, {a^2*c*d^3 , a^3* c*d + a^3 *d^2  + b*c*d^3 }}
            V = frobeniusRoot(1,A)
        Text
            You can also call {\tt frobeniusRoot(e,a,f)}. This computes the $e$th root of the principal ideal $(f^a)$. Calling {\tt frobeniusRoot(e,m,I)} computes the $e$th root of the ideal $I^m$, and calling {\tt frobeniusRoot(e,a,f,I)} computes the eth root of the product $f^a I$. Finally, you can also compute the $p^e$-th root of a matrix $A$ by calling {\tt frobeniusRoot(e,A)}.
        Text
            There are two valid inputs for the option {\tt FrobeniusRootStrategy}, namely {\tt Substitution} and {\tt MonomialBasis}.  In the end, for each generator $f$ of an ideal $I$, we are simply writing $f = \sum a_i^{p^e} m_i$ where $m$ is a monomial all of whose exponents are $< p^e$, then all the possible $a_i$ generate the {\tt frobeniusRoot}. {\tt Substitution} and {\tt MonomialBasis} use different methods for gathering these $a_i$, sometimes one method is faster than the other.
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
        a valid value for the FrobeniusRootStrategy option
///

doc ///
    Key
        MonomialBasis
    Headline
        a valid value for the FrobeniusRootStrategy option
///
