--***********************************************
--***********************************************
--Documentation for parameterTestIdeal.m2
--***********************************************
--***********************************************

doc ///
    Key
        canonicalIdeal
        (canonicalIdeal, Ring)
        [canonicalIdeal, Attempts]
    Headline
        produce an ideal isomorphic to the canonical module of a ring
    Usage
        canonicalIdeal(R)
    Inputs
        R:Ring
        Attempts => ZZ
            specify how many times the function should try to embed the canonical module as an ideal before giving up
    Outputs
        :Ideal
	    isomorphic to the canonical module of {\tt R}
    Description
        Text
            Given a ring $R$, typically a domain, this produces an ideal isomorphic to the canonical module of $R$.  This will not always produce the same ideal, especially in a non-domain.  It uses the function {\tt embedAsIdeal} from {\tt Divisor.m2}.
        Example
            S = QQ[x,y,u,v];
            T = QQ[a,b];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            R = S/(ker f);
            canonicalIdeal(R)
        Text
            Here is an example in a non-domain.
        Example
            R = ZZ/13[x,y,z]/ideal(x*y, x*z, y*z);
            canonicalIdeal(R)
        Text
            The option {\tt Attempts} is passed to {\tt embedAsIdeal}, and tells it how many times to try before giving up.
///

doc ///
    Key
        frobeniusTraceOnCanonicalModule
        (frobeniusTraceOnCanonicalModule, Ideal, Ideal)
    Headline
        find an element of a polynomial ring that determines the Frobenius trace on the canonical module of a quotient of that ring
    Usage
        frobeniusTraceOnCanonicalModule( defIdeal, canIdeal )
    Inputs
        defIdeal:Ideal
            the defining ideal of the ring
        canIdeal:Ideal
            an ideal representing the canonical ideal
    Outputs
        :List
    Description
        Text
            Given $R = S/I$, where $S$ is a polynomial ring, there is a map $\omega_R^{1/p^e} \to \omega_R$ dual to the Frobenius map on $R$.
            By embedding $\omega_R$ as an ideal of $R$, one can interpret this map as a $p^{-e}$-linear map on $S$.  But every $p^{-e}$-linear map on $S$ is a premultiple of the dual to Frobenius on $S$, by some element of $S$. This function finds such an element.

            However, because {\it Macaulay2} does not always properly identify an ideal as principal (even though it is), sometimes we cannot find this single element, but instead find a list of elements of $S$, a linear combination of which is the desired one.
	    
            The function {\tt frobeniusTraceOnCanonicalModule} takes as inputs the defining ideal $I$ of $R$, and an ideal $J$ of $S$ whose image in $R$ is a canonical module of $R$.  
        Example
            S = ZZ/5[x,y,z,w];
            I = ker map( ZZ/5[a,b], S, {a^3, a^2*b, a*b^2, b^3} );
	    R = S/I;
            canIdeal = canonicalIdeal R;
            J = sub( canIdeal, S );
            frobeniusTraceOnCanonicalModule( I, J )
///

doc ///
    Key
        testModule
        (testModule, Ring)
        (testModule, Ring, Ideal)
        (testModule, Number, RingElement)
        (testModule, Number, RingElement, Ideal, List)
        (testModule, List, List)
        (testModule, List, List, Ideal, List)
        [testModule, AssumeDomain]
        [testModule, FrobeniusRootStrategy]
    Headline
        find the parameter test module of a reduced ring
    Usage
        testModule(R)
        testModule(R, canIdeal)
        testModule(tt, ff)
        testModule(tt, ff, canIdeal, u1)
    Inputs
        R:Ring
        canIdeal:Ideal
            an ideal isomorphic to the canonical module
        tt:QQ
            the formal exponent that ff is raised to
        u1:List
            a list of elements describing the map on hte canonical module
        AssumeDomain => Boolean
            assume whether the ring passed is an integral domain
        FrobeniusRootStrategy => Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Sequence
    Description
        Text
            Computes the parameter test module (as a submodule of the canonical module).  The function returns three values, the parameter test submodule, the canonical module of which it is a subset, and the element $u$ (or $u$s) used to compute this ideal via the method @TO frobeniusTraceOnCanonicalModule@.
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            testModule(R)
        Text
            The canonical module returned is always embedded as an ideal of $R$ (not of the ambient polynomial ring).  Likewise the parameter test submodule is then viewed as a subideal of that.
            With this in mind, because the example above is a Gorenstein ring, the ambient canonical module is the unit ideal.  The next example is not Gorenstein.
        Example
            S = ZZ/3[x,y,u,v];
            T = ZZ/3[a,b];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            R = S/(ker f);
            testModule(R)
        Text
            Note that the output in this case has the parameter test module equal to the canonical module, as it should be.  Let's consider a non-Gorenstein example which is not F-rational.
        Example
            R = ZZ/5[x,y,z]/ideal(y*z, x*z, x*y);
            paraTestMod = testModule(R)
            (paraTestMod#0) : (paraTestMod#1)
        Text
            This function can be used to compute parameter test ideals in Cohen-Macaulay rings.
        Example
            S=ZZ/2[X_1..X_5];
            E=matrix {{X_1,X_2,X_2,X_5},{X_4,X_4,X_3,X_1}};
            I=minors(2,E);
            tau=testModule(S/I);
            (tau#0):(tau#1)
        Text
            This function can also be used to compute the parameter test module of a pair $(R, f^t)$.
        Example
            R = ZZ/7[x,y];
            f = y^2 - x^3;
            testModule(5/6, f)
            testModule(5/7, f)
        Text
            This can also be used to compute $(R, f^s g^t)$.
        Example
            R = ZZ/7[x,y];
            f = y^2 - x^3;
            g = x^2 - y^3;
            testModule({1/2, 1/2}, {f, g})
        Text
            Sometimes you would like to specify the ambient canonical module (and choice of u) across multiple calls of testModule.  Those are what the $canIdeal$ or $u1$ can be used to specify.  Finally, the option {\tt FrobeniusRootStrategy} is passed to any calls of @TO frobeniusRoot@ and the option {\tt AssumeDomain} is used when computing a test element.
    SeeAlso
        testIdeal
///

doc ///
    Key
        parameterTestIdeal
        (parameterTestIdeal, Ring)
        [parameterTestIdeal, FrobeniusRootStrategy]
    Headline
        compute the parameter test ideal of a Cohen-Macaulay ring
    Usage
        parameterTestIdeal(R)
    Inputs
        R:Ring
	    a Cohen-Macaulay ring
        FrobeniusRootStrategy => Symbol
            specifies the strategy for internal {\tt frobeniusRoot} calls
    Outputs
        :Ideal
	    the parameter test ideal of {\tt R}
    Description
        Text
            This function computes the parameter test ideal of a Cohen-Macaulay ring $R$. Technically, it computes $\tau(\omega) : \omega$ where $\omega$ is a canonical module of $R$, and $\tau(\omega)$ is the (parameter) test module, as computed by @TO testModule@. For example, the ring $R$ in the following example is $F$-rational, and so its parameter test ideal is the unit ideal.
        Example
            T = ZZ/5[x,y];
            S = ZZ/5[a,b,c,d];
            g = map(T, S, {x^3, x^2*y, x*y^2, y^3});
            R = S/(ker g);
            parameterTestIdeal(R)
        Text
            Consider now a non-$F$-rational Gorenstein ring, whose test ideal and parameter test ideal coincide.
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            parameterTestIdeal(R)
            testIdeal(R)
    SeeAlso
        testModule
        testIdeal
///


doc ///
    Key
        isCohenMacaulay
        (isCohenMacaulay, Ring)
        [isCohenMacaulay, IsLocal]
    Headline
        whether a ring is Cohen-Macaulay
    Usage
        isCohenMacaulay(R)
    Inputs
        R:Ring
        IsLocal => Boolean
	    stipulates whether to check if the ring is Cohen-Macaulay only at the origin 
    Outputs
        :Boolean
    Description
        Text
            The function {\tt isCohenMacaulay} determines if a ring is Cohen-Macaulay.  If the option {\tt IsLocal} (which defaults to {\tt false}) is set to {\tt true}, {\tt isCohenMacaulay} will simply call the @TO isCM@ function in the {\tt Depth} package, which checks whether the ring is Cohen-Macaulay at the origin; otherwise, {\tt isCohenMacaulay} checks the Cohen-Macaulay property globally, which sometimes is much faster than the local computation.
        Example
            T = ZZ/5[x,y];
            S = ZZ/5[a,b,c,d];
            g = map(T, S, {x^3, x^2*y, x*y^2, y^3});
            R = S/(ker g);
            isCohenMacaulay(R)
        Example
            R = QQ[x,y,u,v]/(ideal(x*u, x*v, y*u, y*v));
            isCohenMacaulay(R)
        Text
            The function works as follows.  It considers $R$ as a quotient of an ambient polynomial ring, $R = S/I$.  It takes a resolution of $I$.  If the resolution has length equal to dim $R$ - dim $S$, then $R$ is Cohen-Macaulay.  If the resolution has a different length, and $I$ is homogeneous, then $R$ is not Cohen-Macaulay.  Finally, if the resolution has a different length and $I$ is not homogeneous, the function looks at the $Ext$ groups which compute the depth.
    Caveat
        This function assumes that Spec $R$ is connected.  In particular, if you pass it a non-equidimensional Cohen-Macaulay ring (for example, if Spec $R$ has two connected components of different dimensions), this function will return {\tt false}.
///

doc ///
    Key
        IsLocal
    Headline
        an option used to specify whether to only work locally
    Description
        Text
            If true, then the function will only try to work at the origin (the ideal generated by the variables).
///

doc ///
    Key
        isFRational
        (isFRational, Ring)
        [isFRational, IsLocal]
        [isFRational, AssumeCM]
        [isFRational, AssumeDomain]
        [isFRational, FrobeniusRootStrategy]
    Headline
        whether a ring is F-rational
    Usage
        isFRational(R)
    Inputs
        R:Ring
        IsLocal => Boolean
            check F-rationality only at the origin and call the isCM command from the depth package
        AssumeCM => Boolean
            assume whether the ring is Cohen-Macaulay
        AssumeDomain => Boolean
            assume whether the ring is an integral domain
        FrobeniusRootStrategy=>Symbol
            choose the strategy for internal frobeniusRoot calls
    Outputs
        :Boolean
    Description
        Text
            Determines if a ring is F-rational.  If you pass it {\tt IsLocal => true}, it will only check if the ring is F-rational at the origin (this can be slower).  If you pass it {\tt AssumeCM => true}, it will not verify that the ring is Cohen-Macaulay.
        Example
            T = ZZ/5[x,y];
            S = ZZ/5[a,b,c,d];
            g = map(T, S, {x^3, x^2*y, x*y^2, y^3});
            R = S/(ker g);
            isFRational(R)
        Example
            R = ZZ/7[x,y,z]/ideal(x^3+y^3+z^3);
            isFRational(R)
        Text
            We conclude with a more interesting example of a ring that is F-rational but not F-regular.  This example first appeared in A. K. Singh's work on deformation of F-regularity.
        Example
             S = ZZ/3[a,b,c,d,t];
             m = 4;
             n = 3;
             M = matrix{ {a^2 + t^m, b, d}, {c, a^2, b^n-d} };
             I = minors(2, M);
             R = S/I;
             isFRational(R)
        Text
            The option {\tt AssumeDomain} is used when computing a test element.  The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    Caveat
        Warning, this function assumes that Spec R is connected.  Like {\tt isCohenMacaulay}, if you pass it a non-equidimensional F-rational ring (for example, if Spec R has two connected components of different dimensions), this function will return false.
///
