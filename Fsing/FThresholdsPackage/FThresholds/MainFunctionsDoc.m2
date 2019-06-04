doc ///
    Key
        compareFPT
        (compareFPT, Number, RingElement)
        [compareFPT, MaxCartierIndex]
        [compareFPT, FrobeniusRootStrategy]
        [compareFPT, AssumeDomain]
        [compareFPT, QGorensteinIndex]
    Headline
        determine whether a given number is less than, greater than, or equal to the F-pure threshold
    Usage
        compareFPT(t, f)
    Inputs
        t:QQ
            a rational number to compare to the $F$-pure threshold
        f:RingElement
            an element of a $\mathbb{Q}$-Gorenstein ring
        FrobeniusRootStrategy => Symbol
            an option passed to computations in the TestIdeals package
        AssumeDomain => Boolean
            assumes the ring passed is an integral domain
        MaxCartierIndex => ZZ
            sets the maximum $\mathbb{Q}$-Gorenstein index to search for 
        QGorensteinIndex => ZZ
            specifies the $\mathbb{Q}$-Gorenstein index of the ring
    Outputs
        :ZZ
            namely {\tt -1}, {\tt 1}, or {\tt 0}, according as {\tt t} is less than, greater than, or equal to the $F$-pure threshold or {\tt f}.
    Description
        Text
            Let $f$ be a ring element, and $t$ a rational number.  
	    The function {\tt compareFPT} returns $-1$ if $t$ is less than the $F$-pure threshold of $f$, $1$ if $t$ is greater than the $F$-pure threshold $f$, or $0$ if $t$ equals the $F$-pure threshold.
        Example
            R = ZZ/7[x,y];
            f = y^2-x^3;
            compareFPT(1/2, f)
            compareFPT(5/6, f)
            compareFPT(6/7, f)
        Text
            This function can be used in a singular ring that is strongly $F$-regular, as long as the ring is $\mathbb{Q}$-Gorenstein of index dividing $p-1$, where $p>0$ is the characteristic of the ring. 
            For instance, in the following example, $x$ defines a Cartier divisor that is twice one of the rulings of the cone.
        Example
             R = ZZ/5[x,y,z]/(x*y - z^2);
             f = x;
             compareFPT(1/3, f)
             compareFPT(1/2, f)
             compareFPT(13/25, f)
    SeeAlso
        fpt
        isFPT
        isFJumpingExponent
///

doc ///
    Key
        ContainmentTest
    Headline
        an option for nu 
    Description
        Text
            The option {\tt ContainmentTest} tells the function @TO nu@ which type of containment test to use.  
            The valid values are {\tt FrobeniusPower}, {\tt FrobeniusRoot}, and {\tt StandardPower}.
///

doc ///
    Key
        fpt
        (fpt, RingElement)
        [fpt, DepthOfSearch]
        [fpt, FRegularityCheck]
        [fpt, Attempts]
        [fpt, UseFSignature]
        [fpt, UseSpecialAlgorithms]
        [fpt, Verbose]
    Headline
        attempt to compute the F-pure threshold of a polynomial at the origin
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
            specifies the power of the characteristic to be used in a search for the $F$-pure threshold
        FRegularityCheck => Boolean
            specifies whether to check if the final lower bound is the $F$-pure threshold of {\tt f}
        Attempts => ZZ
            specifies the number of "guess and check" attempts to make
        UseFSignature => Boolean
            specifies whether to use the $F$-signature function and a secant line argument to attempt to improve the $F$-pure threshold estimate
        UseSpecialAlgorithms => Boolean
            specifies whether to check if {\tt f} is a diagonal polynomial, binomial, or a binary form (i.e., a standard-graded homogeneous polynomial in 2 variables), and then apply appropriate algorithms
        Verbose => Boolean
            requests verbose feedback
    Outputs
       :List
           containing lower and upper bounds for the $F$-pure threshold of {\tt f}
       :QQ
           the $F$-pure threshold of {\tt f}
       :InfiniteNumber
           the $F$-pure threshold of {\tt f}, if {\tt f} does not vanish at the origin
    Description
         Text
             Given a polynomial $f$ with coefficients in a finite field, the function {\tt fpt} attempts to find the exact value for the $F$-pure threshold of $f$ at the origin, and returns that value, if possible.
             Otherwise, it returns lower and upper bounds for the $F$-pure threshold.
        Example
             ZZ/5[x,y,z];
             fpt( x^3 + y^3 + z^3 + x*y*z )
             fpt( x^5 + y^6 + z^7 + (x*y*z)^3 )
        Text
             If the option @TO UseSpecialAlgorithms@ is set to {\tt true} (the default value), then {\tt fpt} first checks whether $f$ is diagonal polynomial, a binomial, or a form in two variables, respectively.
             If it is one of these, algorithms of Hernandez, or Hernandez and Teixeira, are executed to compute the $F$-pure threshold of $f$.
        Example
            fpt( x^17 + y^20 + z^24 ) -- a diagonal polynomial
            fpt( x^2*y^6*z^10 + x^10*y^5*z^3 ) -- a binomial
            ZZ/5[x,y];
            fpt( x^2*y^6*(x + y)^9*(x + 3*y)^10 ) -- a binary form
        Text
            The computation of the $F$-pure threshold of a binary form $f$ requires factoring $f$ into linear forms, and can sometimes hang when attempting that factorization. 
            For this reason, when a factorization is already known, the user can pass to {\tt fpt} a list containing all the pairwise prime linear factors of $f$ and a list containing their respective multiplicities.
        Example
            L = {x, y, x + y, x + 3*y};
            m = {2, 6, 9, 10};
            fpt(L, m)
            fpt( x^2*y^6*(x + y)^9*(x + 3*y)^10 )
        Text
            When no special algorithm is available or @TO UseSpecialAlgorithms@ is set to {\tt false}, {\tt fpt} computes {\tt u}$(e,f)$ (see @TO nu@), where $e$ is the value of the option @TO DepthOfSearch@, which conservatively defaults to 1.
            At this point, we know that the $F$-pure threshold of $f$ lies in the closed interval [$\nu/(p^e-1),(\nu+1)/p^e$], and the subroutine {\tt guessFPT} is called to make some "educated guesses" in an attempt to find the $F$-pure threshold, or at least narrow down the above interval.
	    The number of "guesses" is controlled by the option @TO Attempts@, which conservatively defaults to 3.
            If @TO Attempts@ is set to 0, {\tt guessFPT} is bypassed.
            If @TO Attempts@ is set to at least 1, then a first check is run to verify whether the right-hand endpoint $(\nu+1)/p^e$ of the above interval is the $F$-pure threshold.
        Example
            f = x^2*(x + y)^3*(x + 3*y^2)^5;
            fpt( f, Attempts => 0 ) -- a bad estimate
            fpt( f, Attempts => 0, DepthOfSearch => 3 ) -- a better estimate
            fpt( f, Attempts => 1, DepthOfSearch => 3 ) -- the right-hand endpoint (nu+1)/p^e is the fpt
        Text
            If @TO Attempts@ is set to at least 2 and the right-hand endpoint $(\nu+1)/p^e$ is not the $F$-pure threshold, a second check is run to verify whether the left-hand endpoint $\nu/(p^e-1)$ is the $F$-pure threshold.
        Example
	    f = x^6*y^4 + x^4*y^9 + (x^2 + y^3)^3;
            fpt( f, Attempts => 1, DepthOfSearch => 3 )
            fpt( f, Attempts => 2, DepthOfSearch => 3 ) -- the left-hand endpoint nu/(p^e-1) is the fpt
        Text
            If neither endpoint is the $F$-pure threshold, and @TO Attempts@ is set to more than 2, additional checks are performed at numbers in the interval.
            A number in the interval with minimal denominator is selected, and @TO compareFPT@ is used to test that number.
            If that "guess" is correct, its value is returned; otherwise, the information returned by @TO compareFPT@ is used to narrow down the interval, and this process is repeated as many times as specified by @TO Attempts@.
        Example
            f = x^3*y^11*(x + y)^8*(x^2 + y^3)^8;
            fpt( f, DepthOfSearch => 3, Attempts => 2 )
            fpt( f, DepthOfSearch => 3, Attempts => 3 ) -- an additional check sharpens the estimate
            fpt( f, DepthOfSearch => 3, Attempts => 4 ) -- and one more finds the exact answer
        Text
            If guessFPT is unsuccessful and @TO UseFSignature@ is set to {\tt true}, the fpt function proceeds to use the convexity of the $F$-signature function and a secant line argument to attempt to narrow down the interval bounding the $F$-pure threshold.
        Example
            f = x^5*y^6*(x + y)^9*(x^2 + y^3)^4;
            fpt( f, DepthOfSearch => 3 )
            fpt( f, DepthOfSearch => 3, UseFSignature => true )
            numeric ooo
            numeric ooo -- UseFSignature sharpened the estimate a bit
        Text
            When @TO FRegularityCheck@ is set to {\tt true} and no exact answer has been found, a final check is run (if necessary) to verify whether the final lower bound for the $F$-pure threshold is the exact answer.
        Example
            f = (x + y)^4*(x^2 + y^3)^6;
            fpt( f, Attempts => 2, DepthOfSearch => 3 )
            fpt( f, Attempts => 2, DepthOfSearch => 3, UseFSignature => true ) -- using FSignatures the answer improves a bit
	    fpt( f, Attempts => 2, DepthOfSearch => 3, UseFSignature => true, FRegularityCheck => true ) -- FRegularityCheck finds the answer
        Text
            The computations performed when @TO UseFSignature@ and @TO FRegularityCheck@ are set to {\tt true} are often slow, and often fail to improve the estimate, and for this reason, these options should be used sparingly.
            It is often more effective to increase the values of @TO Attempts@ or @TO DepthOfSearch@, instead.
        Example
            f = x^7*y^5*(x + y)^5*(x^2 + y^3)^4;
	    timing numeric fpt( f, DepthOfSearch => 3, UseFSignature => true, FRegularityCheck => true )
            timing numeric fpt( f, Attempts => 5, DepthOfSearch => 3 ) -- a better answer in less time
            timing fpt( f, DepthOfSearch => 4 ) -- the exact answer in even less time
        Text
            As seen in several examples above, when the exact answer is not found, a list containing the endpoints of an interval containing the $F$-pure threshold of $f$ is returned.
            Whether that interval is open, closed, or a mixed interval depends on the options passed; if the option @TO Verbose@ is set to {\tt true}, the precise interval will be printed.
        Example
            f = x^7*y^5*(x + y)^5*(x^2 + y^3)^4;
            fpt( f, DepthOfSearch => 3, UseFSignature => true, Verbose => true )
    SeeAlso
        compareFPT
        isFPT
        nu
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
        whether a given number is an F-jumping number
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
            Returns true if {\tt t} is an $F$-jumping number of {\tt f}, otherwise it returns false. This function only works if the ambient ring of $R$ is $\mathbb{Q}$-Gorenstein

            If the ambient ring of {\tt f} is a domain, the option {\tt AssumeDomain} can be set to {\tt true} in order
            to speed up the computation. Otherwise {\tt AssumeDomain} should be set to {\tt false}.

            Let $R$ be the ambient ring of $f$.
	    If the Gorenstein index of $R$ is known, one should set the option {\tt QGorensteinIndex} to the Gorenstein index of $R$.
	    Otherwise the function attempts find the Gorenstein index of $R$, assuming it is between 1 and {\tt MaxCartierIndex}. By default, {\tt MaxCartierIndex} is set to {\tt 10}.

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
            Returns true if t is the $F$-pure threshold, otherwise it returns false.
	    If {\tt Origin} is true, it only checks it at the homogeneous maximal ideal.

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
        nu
        (nu, ZZ, Ideal, Ideal)
        (nu, ZZ, Ideal)
        (nu, ZZ, RingElement, Ideal)
        (nu, ZZ, RingElement)
        [nu, ContainmentTest]
	[nu, ReturnList]
        [nu, Search]
	[nu, Verbose]
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
        ContainmentTest => Symbol
            specifies the manner in which to verify the containment of a power of $I$ in some specified Frobenius power of $J$
	ReturnList => Boolean
	    specifies whether the list of presceding {\tt \nu}s should be returned
        Search => Symbol
            specifies the strategy in which to search for the largest integer $n$ such that $I^n$ is not contained in some specified Frobenius power of $J$
        Verbose => Boolean
	    requests verbose feedback
    Outputs
        :ZZ
            $nu$ invariants whose normalized limits compute the $F$-pure threshold, and more generally, $F$-thresholds
        :InfiniteNumber
            the $nu$ invariant, if {\tt I} or {\tt f} is not contained in the radical of $J$
	:List
            a list of the $i$-th $\nu$-values for $i = 0,\ldots,e$
    Description
        Text
            Consider a field $k$ of characteristic $p>0$, and an ideal $J$ in the polynomial ring $S = k[x_1, \ldots, x_d]$.
            If $f$ is a polynomial contained in the radical of $J$, then the command {\tt nu(e, f, J)} outputs the maximal exponent
            $n$ such that $f^n$ is not contained in the $p^e$-th Frobenius power of $J$.
	    More generally, if $I$ is an ideal contained in the radical of $J$, then {\tt nu(e, I, J)} outputs the maximal integer exponent $n$ such that $I^n$ is not contained in the $p^e$-th Frobenius power of $J$.

            These numbers are denoted $\nu_f^J(p^e)$ and $\nu_I^J(p^e)$, respectively, in the literature, and were originally defined in the paper
            "$F$-thresholds and Bernstein-Sato Polynomials" by Mustata, Takagi, and Watanabe.
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
            generators of $I$ and $J$ (e.g., it is at most $p-1$ when $I$ is principal).
	    This relation implies that when searching
            for {\tt nu(e+1,I,J)}, it is always safe to start at $p$ times {\tt nu(e,I,J)}, and one needn't search too far past this number.

            The valid values for the option {\tt ContainmentTest} are {\tt FrobeniusPower, FrobeniusRoot}, and {\tt StandardPower}.
            The default value of this option depends on what is passed to {\tt nu}.
	    Indeed, by default, {\tt ContainmentTest} is set to {\tt FrobeniusRoot} if {\tt nu} is passed a ring element $f$, and is set to {\tt StandardPower} if {\tt nu} is passed an ideal $I$.
            We describe the consequences of setting {\tt ContainmentTest} to each of these values below.

            First, if {\tt ContainmentTest} is set to {\tt StandardPower}, then the ideal containments that occur when computing
            {\tt nu(e,I,J)} are verified directly.
	    That is, the standard power $I^n$ is first computed, and a check is then run to see if
            it lies in the $p^e$-th Frobenius power of $J$.

            Alternately, if {\tt ContainmentTest} is set to {\tt FrobeniusRoot}, then the ideal containments that occur when computing
            {\tt nu(e,I,J)} are verified using Frobenius Roots.  That is, the $p^e$-th Frobenius root of $I^n$ is first computed, and
            a check is then run to see if it lies in $J$.
	    The output is unaffected, but this option often speeds up computations.
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
            they will when $I$ is a principal ideal.
        Example
            ZZ/3[x,y];
            M=ideal(x,y);
            nu(3,M^5)
            nu(3,M^5,ContainmentTest=>FrobeniusPower)
        Text
            The function {\tt nu} works by searching through list of integers $n$ and checking containments of $I^n$ in a specified Frobenius power of $J$.
            
            There are two valid values for the option {\tt Search}, either the default value, {\tt Binary}, or the value {\tt Linear}.
            The value {\tt Binary} checks containments in a binary search order, and {\tt Linear} in a linear order. 

        Example
            ZZ/17[x,y];
            M=ideal(x,y);
            time nu(2,M,M^2,Search=>Binary)
            time nu(2,M,M^2,Search=>Linear)
///

doc ///
     Key
          Search
     Headline
          an option to specify the search method
     Description
          Text
              An option for function @TO nu@ to specify the order in which ideal the containment of powers are computed.

              Valid values are {\tt Binary} and {\tt Linear}.
     SeeAlso
          nu
///

doc ///
    Key
        StandardPower
    Headline
        an option value to consider containment of standard power of an ideal in Frobenius power of another ideal
    Description
        Text
            A value for the option {\tt ContainmentTest} to consider containment of the standard power of an ideal in the
            Frobenius power of another ideal
    SeeAlso
        nu
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
              If it is, the function @TO fpt@ applies specialized algorithms of D. Hernandez, or D. Hernandez and P. Teixeira.

              Can take on only Boolean values.
              The default value is {\tt true}.
     SeeAlso
          fpt
///
