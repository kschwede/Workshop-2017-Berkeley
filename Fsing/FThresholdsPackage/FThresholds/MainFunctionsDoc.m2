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
        t:Number
            a rational number to compare to the $F$-pure threshold
        f:RingElement
            in a $\mathbb{Q}$-Gorenstein ring of positive characteristic
        AssumeDomain => Boolean
            assumes the ring passed is an integral domain
        FrobeniusRootStrategy => Symbol
            passed to computations in the {\it TestIdeals} package
        MaxCartierIndex => ZZ
            sets the maximum $\mathbb{Q}$-Gorenstein index to search for 
        QGorensteinIndex => ZZ
            specifies the $\mathbb{Q}$-Gorenstein index of the ring
    Outputs
        :ZZ
            namely {\tt -1}, {\tt 1}, or {\tt 0}, according as {\tt t} is less than, greater than, or equal to the $F$-pure threshold of {\tt f}.
    Description
        Text
            Let $f$ be an element of a ring of positive characteristic, and $t$ a rational number.  
            The function {\tt compareFPT} returns $-1$ if $t$ is less than the $F$-pure threshold of $f$, $1$ if $t$ is greater than the $F$-pure threshold $f$, or $0$ if $t$ equals the $F$-pure threshold.
        Example
            R = ZZ/7[x,y];
            f = y^2 - x^3;
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
        an option for the function nu specifying the type of containment of powers of ideals to test
    Description
        Text
            An option for the function @TO nu@ specifying which type of containment test to apply.  
            The valid values are {\tt FrobeniusPower}, {\tt FrobeniusRoot}, and {\tt StandardPower}.
            The default value, {\tt null}, is replaced with {\tt FrobeniusRoot} when the second argument passed to @TO nu@ is a ring element, and {\tt StandardPower} when that argument is an ideal.
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
        an option for the function fpt specifying whether to use an F-regularity check as a final attempt to find an F-pure threshold
    Description
        Text
            An option for the function @TO fpt@ specifying that, in a situation where the exact value of the $F$-pure threshold has not been not found, a final check be run to determine whether the final lower bound for the $F$-pure threshold equals the $F$-pure threshold.
            This option takes on {\tt Boolean} values, and its default value is {\tt false}. 
///

doc ///
    Key
        FrobeniusPower
    Headline
        a valid value for the option ContainmentTest
    Description
        Text
            A valid value for the option {\tt ContainmentTest} specifying that Frobenius powers be used when verifying containments of powers of ideals. 
    SeeAlso
        ContainmentTest
        nu
///

doc ///
    Key
        FrobeniusRoot
    Headline
        a valid value for the option ContainmentTest
    Description
        Text
            A valid value for the option {\tt ContainmentTest} specifying that Frobenius roots be used when verifying containments of powers of ideals.
    SeeAlso
        ContainmentTest
        nu
///

doc ///
    Key
        isFJumpingExponent
        (isFJumpingExponent, Number, RingElement)
        [isFJumpingExponent, AssumeDomain]
        [isFJumpingExponent, FrobeniusRootStrategy]
        [isFJumpingExponent, MaxCartierIndex]
        [isFJumpingExponent, QGorensteinIndex]
    Headline
        whether a given number is an F-jumping exponent
    Usage
        isFJumpingExponent(t, f)
    Inputs
        t:Number
            a rational number
        f:RingElement
            in a $\mathbb{Q}$-Gorenstein ring of positive characteristic
        AssumeDomain => Boolean
            assumes the ring passed is an integral domain
        FrobeniusRootStrategy => Symbol
            passed to computations in the {\it TestIdeals} package
        MaxCartierIndex => ZZ
            sets the maximum $\mathbb{Q}$-Gorenstein index to search for 
        QGorensteinIndex => ZZ
            specifies the $\mathbb{Q}$-Gorenstein index of the ring
    Outputs
        :Boolean
            reporting whether {\tt t} is an $F$-jumping exponent of {\tt f}
    Description
        Text
            Given an element $f$ of a $\mathbb{Q}$-Gorenstein ring $R$ of positive characteristic and a rational number $t$, {\tt isFJumpingExponent(t,f)} returns true if $t$ is an $F$-jumping exponent of $f$, and otherwise it returns false. 
        Example
            R = ZZ/5[x,y];
            f =  x^4 + y^3 + x^2*y^2;
            isFJumpingExponent(7/12, f)
            isFJumpingExponent(4/5, f)
            isFJumpingExponent(5/6, f)
            isFJumpingExponent(11/12, f)
        Text
            If the ambient ring $R$ is a domain, the option {\tt AssumeDomain} can be set to {\tt true} in order to speed up the computation. 
            Otherwise {\tt AssumeDomain} should be set to {\tt false} (its default value).
        Example
            R = ZZ/5[x,y];
            f =  x^4 + y^3 + x^2*y^2;
            time isFJumpingExponent(11/12, f)
            time isFJumpingExponent(11/12, f, AssumeDomain => true)
        Text        
            If the Gorenstein index of $R$ is known, the user should set the option {\tt QGorensteinIndex} to the Gorenstein index of $R$.
            Otherwise the function attempts to find the Gorenstein index of $R$, assuming it is between 1 and the value passed to the option {\tt MaxCartierIndex} (default value 10).

            The option {\tt FrobeniusRootStrategy} is passed to an internal call of @TO frobeniusRoot@. The two valid values of {\tt FrobeniusRootStrategy} are {\tt Substitution} and {\tt MonomialBasis}.
    SeeAlso
        compareFPT
        isFPT
///

doc ///
    Key
        isFPT
        (isFPT, Number, RingElement)
        [isFPT, AssumeDomain]
        [isFPT, FrobeniusRootStrategy]
        [isFPT, MaxCartierIndex]
        [isFPT, QGorensteinIndex]
    Headline
        checks whether a given rational number is the F-pure threshold
    Usage
        isFPT(t, f)
    Inputs
        t:Number
            a number that is a candidate for the $F$-pure threshold of {\tt f}
        f:RingElement
            an element of a $\mathbb{Q}$-Gorenstein ring of characteristic $p>0$
        FrobeniusRootStrategy => Symbol
            an option passed to computations in the TestIdeals package
        AssumeDomain => Boolean
            assumes the ring passed is an integral domain
        MaxCartierIndex => ZZ
            sets the maximum $\mathbb{Q}$-Gorenstein index to search for 
        QGorensteinIndex => ZZ
            specifies the $\mathbb{Q}$-Gorenstein index of the ring
    Outputs
        :Boolean
            the value {\tt true} if {\tt t} is the $F$-pure threshold of $f$, and {\tt false} otherwise 
    Description
        Text
            Consider an element {\tt f} of a $\mathbb{Q}$-Gorenstein ring of characteristic $p>0$, and a number {\tt t}. 
            If {\tt t} is the $F$-pure threshold of {\tt f}, then the command {\tt isFPT(t, f)} outputs {\true}, and otherwise, outputs {\tt false}.         
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
        nu(e, I, J)
        nu(e, I)
        nu(e, f, J)
        nu(e, f)
    Inputs
        e:ZZ
            the order of the Frobenius power to consider
        I:Ideal
            in a polynomial ring {\tt R} with coefficients in a field of characteristic {\tt p > 0}        
        f:RingElement
            in a polynomial ring {\tt R} with coefficients in a field of characteristic {\tt p > 0}        
        J:Ideal
            in the same ring {\tt R}; if omitted, {\tt J} is assumed to be the ideal generated by the variables of the ring {\tt R}
        ContainmentTest => Symbol
            specifies the manner in which to verify the containment of powers of {\tt I} or {\tt f} in {\tt J^{[p^e]}}
        ReturnList => Boolean
            specifies whether to return the list {\tt \{\nu(1),\ldots,\nu(p^e)\}}, as opposed to just {\tt \nu(p^e)}
        Search => Symbol
            specifies the strategy to be used in the search for the largest power of {\tt I} not contained in {\tt J^{[p^e]}}
        UseSpecialAlgorithms => Boolean
            specifies whether to use special algorithms to compute the $F$-pure threshold of {\tt f}, for certain special types of polynomials 
        Verbose => Boolean
            requests verbose feedback, where {\tt \nu(1)}, {\tt \nu(p)}, {\tt \nu(p^2)}, etc., are printed as they are computed 
    Outputs
        :ZZ
            the largest integer {\tt \nu\ = \nu(p^e)} such that {\tt I^{\nu}} (or {\tt f^n}, or {\tt I^{[\nu]}}, depending on the arguments and options passed) is not contained in {\tt J^{[p^e]}}
        :InfiniteNumber
            if {\tt I} or {\tt f} is not contained in the radical of $J$
        :List
            containing {\tt \nu(p^i)}, for {\tt i = 0,\ldots,e}
    Description
        Text
            Consider a finite field $k$ of characteristic $p>0$, and an ideal $J$ in the polynomial ring $S = k[x_1, \ldots, x_d]$.
            If $f$ is a polynomial contained in the radical of $J$, then the command {\tt nu(e,f,J)} outputs the maximal exponent $n$ such that $f^n$ is not contained in the $p^e$-th Frobenius power of $J$.
            More generally, if $I$ is an ideal contained in the radical of $J$, then {\tt nu(e,I,J)} outputs the maximal integer exponent $n$ such that $I^n$ is not contained in the $p^e$-th Frobenius power of $J$.

            These numbers are denoted $\nu_f^J(p^e)$ and $\nu_I^J(p^e)$, respectively, in the literature, and were originally defined in the paper {\it $F$-thresholds and Bernstein-Sato Polynomials} by Mustata, Takagi, and Watanabe.
        Example
            R = ZZ/11[x,y];
            I = ideal(x^2 + y^3, x*y);
            J = ideal(x^2, y^3);
            nu(1, I, J)
            f = x*y*(x^2 + y^2);
            nu(1, f, J)
        Text
            If $f$ or $I$ is zero, then {\tt nu} returns {\tt 0}; if $f$ or $I$ is not contained in the radical of $J$, {\tt nu} returns infinity.
        Example
           nu(1, 0_R, J)
           nu(1, 1_R, J)
        Text
            When the third argument is ommited, the ideal $J$ is assumed to be the homogeneous maximal ideal of $R$.
        Example
            R = ZZ/17[x,y,z];
            f = x^3 + y^4 + z^5;
            M = ideal(x, y, z);
            nu(2, f)
            nu(2, f, M)
        Text
            It is well known that if $q=p^e$ for some nonnegative integer $e$, then $\nu_I^J(qp) = \nu_I^J(q) p + L$, where the error term $L$ is nonnegative, and can explicitly bounded from above in terms of $p$ and the number of generators of $I$ and $J$ (e.g., it is at most $p-1$ when $I$ is principal).
            This relation implies that when searching for {\tt nu(e+1,I,J)}, it is always safe to start at $p$ times {\tt nu(e,I,J)}, and one needn't search too far past this number.
            
            If $M$ is the homogeneous maximal ideal of $R$ and $f$ is an element of $R$, the numbers $\nu_f^M(p^e)$ determine and are determined by the $F$-pure threshold of $F$ at the origin. 
            Indeed, $\nu_f^M(p^e)$ is $p^e$ times the truncation of the non-terminating base $p$ expansion of fpt($f$) at its $e$^{th} spot.
            This fact is used to speed up the computations for certain polynomials whose $F$-pure thresholds can be quickly computed via special algorithms, namely diagonal polynomials and binomials.
            This feature can be disabled by setting the option {\tt UseSpecialAlgorithms} (default value {\tt true}) to {\tt false}.
        Example
            R = ZZ/17[x,y,z];
            f = x^3 + y^4 + z^5; -- a diagonal polynomial
            time nu(3, f)
            time nu(3, f, UseSpecialAlgorithms => false)
        Text
            The valid values for the option {\tt ContainmentTest} are {\tt FrobeniusPower}, {\tt FrobeniusRoot}, and {\tt StandardPower}.
            The default value of this option depends on what is passed to {\tt nu}.
            Indeed, by default, {\tt ContainmentTest} is set to {\tt FrobeniusRoot} if {\tt nu} is passed a ring element $f$, and is set to {\tt StandardPower} if {\tt nu} is passed an ideal $I$.
            We describe the consequences of setting {\tt ContainmentTest} to each of these values below.

            First, if {\tt ContainmentTest} is set to {\tt StandardPower}, then the ideal containments checked when computing {\tt nu(e,I,J)} are verified directly.
            That is, the standard power $I^n$ is first computed, and a check is then run to see if it lies in the $p^e$-th Frobenius power of $J$.

            Alternately, if {\tt ContainmentTest} is set to {\tt FrobeniusRoot}, then the ideal containments are verified using Frobenius Roots.  
            That is, the $p^e$-th Frobenius root of $I^n$ is first computed, and a check is then run to see if it lies in $J$.
            The output is unaffected, but this option often speeds up computations, specially when a polynomial or principal ideal is passed as the second argument.
        Example
            R = ZZ/11[x,y,z];
            f = x^3 + y^3 + z^3 + x*y*z;
            time nu(3, f) -- ContainmentTest is set to FrobeniusRoot, by default
            time nu(3, f, ContainmentTest => StandardPower)
        Text
            Finally, when {\tt ContainmentTest} is set to {\tt FrobeniusPower}, then instead of producing the invariant $\nu_I^J(p^e)$ as defined above, {\tt nu(e,I,J,ContainmentTest=>FrobeniusPower)} instead outputs the maximal integer $n$ such that the $n$^{th} (generalized) Frobenius power of $I$ is not contained in the $p^e$-th Frobenius power of $J$.  
            Here, the $n$^{th} Frobenius power of $I$, when $n$ is a nonnegative integer, is as defined in the paper {\it Frobenius Powers} by Hernandez, Teixeira, and Witt.  
            In particular, {\tt nu(e,I,J)} and {\tt nu(e,I,J,ContainmentTest=>FrobeniusPower)} need not agree.  
            However, they will agree when $I$ is a principal ideal.
        Example
            R = ZZ/3[x,y];
            M = ideal(x, y);
            nu(3, M^5)
            nu(3, M^5, ContainmentTest => FrobeniusPower)
        Text
            The function {\tt nu} works by searching through the list of potential integers $n$ and checking containments of $I^n$ in a specified Frobenius power of $J$.
            The way this search is approached is specified by the option {\tt Search}, which can be set to {\tt Binary} (the default value) or {\tt Linear}.
        Example
            R = ZZ/5[x,y,z];
            f = x^2*y^4 + y^2*z^7 + z^2*x^8;
            time nu(5, f) -- uses binary search (default)
            time nu(5, f, Search => Linear)
            M = ideal(x, y, z);
            time nu(2, M, M^2) -- uses binary search (default)
            time nu(2, M, M^2, Search => Linear)
        Text
            The option {\tt ReturnList} (default value {\tt false}) can be used to request that the output be not only $\nu_I^J(p^e)$, but a list contaning $\nu_I^J(p^i)$, for $i=0,\ldots,e$.
        Example
            nu(5, f, ReturnList => true)
        Text
            Alternatively, the option {\tt Verbose} (default value {\tt false}) can be used to request that the values $\nu_I^J(p^i)$ ($i=0,\ldots,e$) be printed as they are computed, to monitor the progress of the computation. 
        Example
            nu(5, f, Verbose => true)
    SeeAlso
            fpt    
///

doc ///
    Key
        Search
    Headline
        an option to specify the search method for testing containments of powers of ideals
    Description
        Text
            An option for function @TO nu@ specifies the order in which to compute containment of powers of ideals.         
            Valid values are {\tt Binary} and {\tt Linear}.  Default value is {\tt Binary}. 
    SeeAlso
        nu
///

doc ///
    Key
        StandardPower
    Headline
        an option value to consider containment of the standard power of an ideal in the Frobenius power of another ideal
    Description
        Text
            A value for the option {\tt ContainmentTest} specifying that when verifying containments of powers of ideals, to check whether the standard power of an ideal is contained in the Frobenius power of another ideal. 
    SeeAlso
        ContainmentTest
        nu
///

doc ///
    Key
        UseFSignature
    Headline
        an option to specify whether to use the F-signature function in the search for an F-pure threshold
    Description
        Text
            An option for the function @TO fpt@ specifying whether the convexity of the $F$-signature function, and a secant line argument, are used to attempt to refine the interval containing the $F$-pure threshold.  
            Takes on Boolean values.
    SeeAlso
        fpt
///

doc ///
    Key
        UseSpecialAlgorithms
    Headline
        an option to check whether the input is a diagonal polynomial, a binomial, or a binary form, in which case appropriate algorithms can be applied toward computing an F-pure threshold
    Description
        Text
            An option for the function @TO fpt@ to check whether the input is a diagonal polynomial, a binomial (i.e., a homogeneous polynomial in two variables), or a binary form, in which case, a specialized algorithm of Hernandez, or Hernandez and Teixeira, is applied. 
            Takes on Boolean values.
            Default value is {\tt true}.
    SeeAlso
        fpt
///
