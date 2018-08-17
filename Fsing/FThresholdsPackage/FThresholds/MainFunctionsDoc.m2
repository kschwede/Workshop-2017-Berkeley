
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
         [fpt, NuCheck]
         [fpt, UseFSignature]
         [fpt, UseSpecialAlgorithms]
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
         UseSpecialAlgorithms => Boolean
             specifies whether to check if $f$ is diagonal, binomial, or a binary form (i.e., a standard-graded homogeneous polynomial in 2 variables), and then apply appropriate algorithms
         FRegularityCheck => Boolean
             specifies whether to check if the lower bound derived from the $F$-signature function is the $F$-pure threshold of $f$
         NuCheck => Boolean
             specifies whether to check if $\nu_f(p^e)/(p^e-1)$ or $(\nu_f(p^e)+1)/p^e$ is the $F$-pure threshold of $f$, where $e$ is the value of the option  @TO DepthOfSearch@
         DepthOfSearch => ZZ
             specifies the power of the characteristic to be used in a search for the F-pure threshold
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
              If the option @TO UseSpecialAlgorithms@ is set to @TO true@ (the default value), then the function first checks whether $f$ is a diagonal polynomial, a binomial, or a form in two variables, respectively.
              If it is one of these, algorithms of D. Hernandez, or D. Hernandez and P. Teixeira, are executed to compute the $F$-pure threshold of $f$.
         Example
             fpt( x^17+y^20+z^24 ) -- a diagonal polynomial
             fpt( x^2*y^6*z^10+x^10*y^5*z^3 ) -- a binomial
             ZZ/5[x,y];
             fpt( x^2*y^6*(x+y)^9*(x+3*y)^10 ) -- a binary form
         Text
             When no special algorithm is available or @TO UseSpecialAlgorithms@ is set to @TO false@, @TO fpt@ computes $\nu = \nu_f(p^e)$ (see @ TO nu @), where $e$ is the value of the option @TO DepthOfSearch@, which conservatively defaults to 1.
              The $F$-pure threshold of $f$ lies in the closed interval [$\nu/(p^e-1),(\nu+1)/p^e$], and if @TO NuCheck@ is set to @TO true@ (its default value), then checks are run to verify whether either endpoint of this interval is the $F$-pure threshold.
         Example
             f = x^2*(x+y)^3*(x+3*y^2)^5;
             fpt f
             fpt( f, NuCheck => false, DepthOfSearch => 3 )
             fpt( f, DepthOfSearch => 3 )
             oo == (nu(3,f)+1)/5^3
         Text
              If @TO NuCheck@ is unsuccessful and @TO UseFSignature@ is set to @TO true@ (its default value), the fpt function proceeds to use the convexity of the $F$-signature function and a secant line argument to attempt to narrow down the interval bounding the $F$-pure threshold.
         Example
	      f = x^3*(x^2+y^3)^6;
	      numeric fpt( f, DepthOfSearch => 3, UseFSignature => false )
	      numeric fpt( f, DepthOfSearch => 3 ) -- UseFSignature improves the answer              
	 Text     
              When @TO FRegularityCheck@ is set to @TO true@ (its default value), a check is run to verify whether the left-hand endpoint of the interval containing the $F$-pure threshold is the exact answer.
         Example
	      f = (x+y)^4*(x^2+y^3)^6;
	      fpt( f, DepthOfSearch => 3, UseFSignature => false, FRegularityCheck => false )
	      fpt( f, DepthOfSearch => 3, FRegularityCheck => false ) -- using FSignatures the answer is improved
	      fpt( f, DepthOfSearch => 3 ) -- FRegularityCheck verifies that FSignature actually found the answer              
         Text
	      The computations performed by @TO NuCheck@, @TO UseFSignature@, and @TO FRegularityCheck@ often take a long time, and for this reason the user is given the option to disable them.
	 
              As seen above, when the exact answer is not found, a list containing the endpoints of an interval containing the $F$-pure threshold of $f$ is returned.
              Whether that interval is open, closed, or a mixed interval depends on the options passed; if the option @TO Verbose@ is set to @TO true@, the precise interval will be printed.
         Example
	      f = x^2*(x^2+y^3)^4;
	      fpt( f, DepthOfSearch => 3, NuCheck => false, Verbose => true )
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
        fptGuessList
     Headline
        Tries to guess the FPT in a really naive way (this should be improved).
     Usage
         fptGuessList(f,e,d)
     Inputs
         f:RingElement
         e:ZZ
         d:ZZ
     Outputs
        :List
     Description
        Text
             This function tries to guess the F-pure threshold of $f$.  In particular, it computes the number $\nu$ such that $\nu/(p^e - 1) \leq$ fpt(f) $< (\nu+1)/p^e$.  It then outputs a list of all rational numbers with denominators less than or equal to d, which lie in that range.  WARNING:  There are several improvements which should be made to this function to rule out many of the possibilies.
///

doc ///
    Key
        FRegularityCheck
    Headline
        an option to use an F-regularity check to find an F-pure threshold
    Description
        Text
            This option for the function @TO fpt@ enables the user to check whether the given pair is $F$-regular
            at the given maximal ideal (so that if not, the $F$-pure threshold can be determined from the $F$-signature function).
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
            f=2*x^2*y^3*z^8+2*x^4*z^9+2*x*y^7*z^4
            time nu(5,f) --Use ColonIdeals is set to false, by default
            time nu(5,f, UseColonIdeals=>true)
    SeeAlso
        mu
        nuList
///

doc ///
     Key
          NuCheck
     Headline
          an option to check whether certain guesses, in term of nu, are the F-pure threshold
     Description
          Text
              an option for function @TO fpt@ to check whether $\nu/(p^e-1)$ or $(\nu+1)/p^e$ is the $F$-pure threshold of $f$,
              where $e$ is the value of the option @TO DepthOfSearch@ and $\nu=\nu_f(p^e)$.

              Valid values are {\tt true} and {\tt false}.  Default value is {\tt true}.
     SeeAlso
        fpt
        nu
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
