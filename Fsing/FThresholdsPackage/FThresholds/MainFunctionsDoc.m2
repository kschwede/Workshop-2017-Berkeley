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

            If the ambient ring of {\tt f} is a domain, the option {\tt AssumeDomain} can be set to {\tt true} in order
            to speed up the computation. Otherwise {\tt AssumeDomain} should be set to {\tt false}.

            Let $R$ be the ambient ring of $f$.  If the Gorenstein index of $R$ is known, one should set the option {\tt QGorensteinIndex} to the Gorenstein index of $R$. Otherwise
            the function uses @TO getDivisorIndex@ to find the Gorenstein index of $R$, assuming it is between 1 and {\tt MaxCartierIndex}. By default, {\tt MaxCartierIndex} is set to {\tt 10}.

            The option {\tt FrobeniusRootStrategy} is passed to an internal call of @TO frobeniusRoot@. The two valid values of {\tt FrobeniusRootStrategy} are {\tt Substitution} and {\tt MonomialBasis}.
    SeeAlso
        fpt
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
        nu
        mu
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
            Default for @TO nu@ and @TO nuList@
            (and @TO mu@ and @TO muList@, respectively) applied to a polynomial is {\tt FrobeniusRoot},
            and applied to an ideal is {\tt StandardPower} (or {\tt Frobenius Power}, respectively).
///

doc ///
    Key
        criticalExponentApproximation
        (criticalExponentApproximation,ZZ,Ideal,Ideal)
        (criticalExponentApproximation,ZZ,RingElement,Ideal)
    Headline
        gives a list of approximates of the critical exponent of an ideal or polynomial with respect to an ideal
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
         [fpt, FRegularityCheck]
         [fpt, NuCheck]
         [fpt, UseSpecialAlgorithms]
         [fpt, DepthOfSearch]
     Headline
         attempts to compute the F-pure threshold of a polynomial at the origin
     Usage
         fpt(f)
         fpt(L, m)
     Inputs
         f:RingElement
             a polynomial with coefficients in a finite field
         L:List
             A list of linear forms in two variables
         m:List
             A list of positive integers
         UseSpecialAlgorithms => Boolean
             specifies whether to check if $f$ is diagonal, binomial, or a binary form (i.e., a standard-graded homogeneous polynomial in 2 variables), and then apply appropriate algorithms
         FRegularityCheck => Boolean
             specifies whether to check if the lower bound derived from the $F$-signature function is the $F$-pure threshold of $f$
         NuCheck => Boolean
             specifies whether to check if $\nu/(p^e-1)$ or $(\nu+1)/p^e$ is the $F$-pure threshold of $f$, where $e$ is the value of the option {\tt DepthOfSearch} and $\nu=\nu_f(p^e)$
         DepthOfSearch => ZZ
             specifies the power of the characteristic to be used in a search for the F-pure threshold
     Outputs
        :List
            which contains the endpoints of an interval containing the $F$-pure threshold of $f$
        Q:QQ
            the $F$-pure threshold of $f$
     Description
          Text
              The function {\tt fpt(f)} tries to find the exact value for the $F$-pure threshold of $f$ at the origin, and returns that value, if possible.
              Otherwise, it returns an interval containing the $F$-pure threshold.
         Example
              ZZ/5[x,y,z];
              fpt( x^3+y^3+z^3+x*y*z )
              fpt( x^5+y^6+z^7+(x*y*z)^3 )
         Text
              If the option {\tt UseSpecialAlgorithms} is set to {\tt true} (the default value), then the function first checks whether $f$ is a diagonal polynomial, a binomial, or a form in two variables, respectively.
              If it is one of these, algorithms of D. Hernandez, or D. Hernandez and P. Teixeira, are executed to compute the $F$-pure threshold of $f$.
         Example
             fpt( x^17+y^20+z^24 ) -- a diagonal polynomial
             fpt( x^2*y^6*z^10+x^10*y^5*z^3 ) -- a binomial
             ZZ/5[x,y];
             fpt( x^2*y^6*(x+y)^9*(x+3*y)^10 ) -- a binary form
         Text
             When no special algorithm is available or {\tt UseSpecialAlgorithms} is set to {\tt false}, {\tt fpt} computes $\nu = \nu_f(p^e)$, where $e$ is the value of the option {\tt DepthOfSearch}, which conservatively defaults to 1.
              The $F$-pure threshold of $f$ lies in the closed interval [$\nu/(p^e-1),(\nu+1)/p^e$], and if {\tt NuCheck} is set to {\tt true} (its default value), then checks are run to verify whether either endpoint of this interval is the $F$-pure threshold.
         Example
             f = x^2*(x+y)^3*(x+3*y^2)^5;
             fpt f
             fpt( f, NuCheck => false, DepthOfSearch => 3 )
             fpt( f, DepthOfSearch => 3 )
             oo == (nu(3,f)+1)/5^3
         Text
              If {\tt Nucheck} is unsuccessful, the {\tt fpt} function proceeds to use the convexity of the $F$-signature function and a secant line argument to narrow down the interval bounding the $F$-pure threshold.

              When {\tt FRegularityCheck} is set to {\tt true} (its default value), a check (which can take significant time) is run to verify whether the left-hand endpoint of the interval containing the $F$-pure threshold is the exact answer.

              If no exact answer was found, then a list containing the endpoints of an interval containing the $F$-pure threshold of $f$ is returned.
              Whether that interval is open, closed, or a mixed interval depends on the options passed; if the option {\tt Verbose} is set to {\tt true}, the precise interval will be printed.

              Now suppose we have a polynomial ring in two variables over a finite field. Given a list of linear forms in this ring, $L = \{ L_1, \ldots, L_n \}$, and a list of multiplicities $m = \{ m_1, \ldots, m_n \}$, the function {\tt fpt(L, m)}  computes the $F$-pure threshold of the polynomial $L_1^{m_1} \cdots L_n^{m_n}$.

         Example
              S = ZZ/5[x,y]
              L = {x+y, x+2*y}
              m = {2, 3}
              fpt(L, m)
              oo == fpt( (x+y)^2*(x+2*y)^3)
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
        FRegularityCheck
    Headline
        an option to use an F-regularity check to find an F-pure threshold
    Description
        Text
            This option for the function @TO fpt@ enables the user to check whether the given pair is $F$-regular
            at the given maximal ideal (so that if not, the $F$-pure threshold can be determined from the $F$-signature function).
            Only takes on Boolean values.

            Enables the user to check whether the given pair is F-regular at the given maximal ideal
            (so that if not, the F-pure threshold can be determined from the F-signature function).
            Only takes on Boolean values.
    SeeAlso
        fpt
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
            This returns a list of terms of the sequence whose terms limit to the $F$-threshold of $I$, or of $f$, with respect to $J$.

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
            the function uses @TO getDivisorIndex@ to find the Gorenstein index of $R$, assuming it is between 1 and {\tt MaxCartierIndex}. By default, {\tt MaxCartierIndex} is set to {\tt 10}.

            The option {\tt FrobeniusRootStrategy} is passed to an internal call of @TO frobeniusRoot@. The two valid values of {\tt FrobeniusRootStrategy} are {\tt Substitution} and {\tt MonomialBasis}.
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
        Checks whether a given number is the $F$-pure threshold
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

     SeeAlso
        compareFPT
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
        computes nu-values associated to a given F-threshold or F-pure threshold
        --$\nu_I^J(p^e)$ or $\nu_f^J(p^e)$
     Usage
          nu(e,I,J)
          nu(e,I)
          nu(e,f,J)
          nu(e,f)
          ComputePreviousNus => Boolean
          ContainmentTest => Symbol
          Search => Symbol
          UseColonIdeals => Boolean
     Inputs
         e:ZZ
         I:Ideal
         J:Ideal
         f:RingElement
     Outputs
        :ZZ
          the $e$-th value $\nu$ associated to the $F$-threshold or $F$-pure threshold
     Description
        Text
            Given an ideal $I$ in a polynomial ring $k[x_1, \ldots, x_n]$, {\tt nu(e, I, J)} or {\tt nu(e, f, J)} outputs the
            maximal integer $N$ such that $I^N$ or $f^N$ is not contained in the ideal $J^{[p^e]}$. This number is denoted
            $\nu_I^J(p^e)$ or $\nu_f^J(p^e)$ in "F-thresholds and Bernstein-Sato Polynomials" by Mustata-Takagi-Watanabe.

            The commands {\nu(e,I)} or {\nu(e,f)} do the same for $J = (x_1,\ldots,x_n)$.

            If the option {\tt ComputePreviousNus} is set to {\tt true}, {\tt nu} will recursively compute nu(d, I) for $d = 0,\ldots, e$.

            The option {\tt ContainmentTest} specifies the algorithm used to test the containment of $I^n$ in $J^{[p^e]}$.
            Valid values for {\tt ContainmentTest} are {\tt FrobeniusPower, FrobeniusRoot}, and {\tt StandardPower}.
            By default, {\tt ContainmentTest} is set to {\tt FrobeniusPower} if {\tt nu} is passed a ring element $f$,
            and {\tt ContainmentTest} is set to {\tt StandardPower} if {\tt nu} is passed an ideal $I$.

            The function {\tt nu} works by searching a list of integers for the above number $\nu$.
            The option {\tt Search} specifies the search algorithm used to do so.
            Valid values for {\tt Search} are {\tt Binary}, {\tt BinaryRecursive}, and {\tt Linear}.

            The option {\tt UseColonIdeals} specifies whether or not {\tt nu} uses colon ideals to compute $\nu$ in an iterative way.

     SeeAlso
        nuList
///

doc ///
     Key
          NuCheck
     Headline
          an option to check whether certain values equal the F-pure threshold.
     Description
          Text
              An option for the function @TO fpt@ to specify whether to check whether $\nu/(p^e-1)$ or $(\nu+1)/p^e$
              is the $F$-pure threshold.  Takes on only Boolean values.  Default value is {\tt true}.
     SeeAlso
          fpt
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
            Given an ideal $I$ in a polynomial ring $k[x_1,\ldots,x_n]$, this function computes {\tt nu(d, I, J)}
            or {\tt nu(d,f,J)} recursively for $d = 0,\ldots,e$.  If {\tt nu(d, I, J)}
            or {\tt nu(d,f,J)}
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
              An option for functions @TO nu@ and @TO nuList@ to specify
              the order in which ideal the containment of powers are computed. Valid values are
              {\tt Binary}, {\tt BinaryRecursive}, and {\tt Linear}.
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
              An option for @TO nu@ and @TO nuList@ to use colon ideals to compute nus in an iterative way.
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
              An option for the function @TO fpt@ to check whether the input is a diagonal polynomial, a binomial, or a binary form.
              If {\tt true}, the function @TO fpt@ first checks whether the input
              is a diagonal polynomial, binomial, or binary form (i.e., a homogeneous polynomial in 2 variables).  If it is,
              the function @TO fpt@ applies specialized algorithms.  Can take on only Boolean values.   Default value is {\tt true}.
     SeeAlso
          fpt
///
