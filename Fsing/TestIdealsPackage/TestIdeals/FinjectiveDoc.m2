--***********************************************
--***********************************************
--Documentation for Finjective.m2
--***********************************************
--***********************************************

doc ///
    Key
        HSLGModule
--        (HSLGModule, null)
        (HSLGModule, Number, RingElement)
        (HSLGModule, List, List)
        (HSLGModule, ZZ, List, List)
        [HSLGModule, FrobeniusRootStrategy]
        [HSLGModule, CanonicalIdeal]
        [HSLGModule, CurrentRing]
        [HSLGModule, GeneratorList]
    Headline
        compute the submodule of the canonical module stable under the image of the trace of Frobenius
    Usage
        HSLGModule()
        HSLGModule(t, f)
        HSLGModule(tList, fList)
        HSLGModule(e, expList, fList) --this last command is largely an internal function
    Inputs
        f:RingElement
            a ring element, to make a pair
        t:Number
            a formal exponent
        tList:List
            a list of formal exponents for ring elements, for pairs
        fList:List
            a list of ring elements, for pairs
        expList:List
            a list of formal exponents
        e:ZZ
            an integer, what root of Frobenius to take
        FrobeniusRootStrategy=>Symbol
            choose the strategy for internal frobeniusRoot calls
        CanonicalIdeal=>Ideal
            specify the canonical ideal (so the function doesn't recompute it)
        CurrentRing=>Ring
            specify the current ring to work with
        GeneratorList=>List
            specify the action on the canonical module
    Outputs
        :Sequence
    Description
        Text
            Given a ring $R$ with canonical module $\omega$, this computes the image of $F^e_* \omega \to \omega$ for $e >> 0$.  This image is sometimes called the HSLG-module (named for Hartshorne-Speiser, Lyubeznik and Gabber).
            It roughly tells you where a ring is non-F-injective.
            It can also be used to compute the maximal F-pure sub-Cartier module of a given rank-1 Cartier module (represented as an ideal).
        Text
            Specifically, this function returns a list of the following entries.  {\tt HSLGmodule, canonicalModule, u, HSLCount} where {\tt canonicalModule} is the canonical module of the ring (expressed as an ideal), {\tt HSLGmodule} is a submodule of that canonical module, {\tt u} is a list of elements of the ambient polynomial ring representing the trace of Frobenius on the canonical module and {\tt HSLCount} is how many times the trace of Frobenius was computed before the image stabilized.
        Example
            R = ZZ/7[x,y,z]/ideal( x^5+y^5+z^5 );
            ( HSLGMod, canMod, frobTrace, count ) = HSLGModule(CurrentRing => R);
            canMod --the ambient canonical module
            HSLGMod --the HSLG submodule
            frobTrace --the element representing trace of Frobenius
            count --how many times it took until the image stabilized
        Text
            If you do not want the function to compute the canonical module, you can also pass the canonical module as an ideal via the {\tt CanonicalModule} option.
            You could also pass it something other than the canonical module as well (for example, a submodule of the canonical module).
            Likewise you can use the {\tt GeneratorList} option to specify the dual Frobenius action on the canonical module (or ideal playing the role of the canonical module).
            In the following example, the non-F-pure ideal of a Q-Gorenstein ring is computed by hijacking this functionality.
        Example
            T = ZZ/7[a,b];
            S = ZZ/7[x,y,z,w];
            f = map(T, S, {a^3, a^2*b, a*b^2, b^3});
            I = ker f;
            R = S/I;
            J = ideal(sub(1, R));
            u = QGorensteinGenerator(1, R);
            HSLGModule(CanonicalIdeal=>J, GeneratorList=>{u})
        Text
            Additionally, you can specify a pair $(R, f^t)$ as long as $t$ is a rational number without $p$ in its denominator.
        Example
            R = ZZ/7[x,y];
            M = HSLGModule(5/6, y^2-x^3);
            M#1 --the canonical module
            M#0
            N = HSLGModule(9/10, y^2-x^3);
            N#0
        Text
            Additionally, we can compute HSLG-modules of things like $(R, f^s g^t)$ even when $R$ is not regular (although we do require that R is Q-Gorenstein with index not divisible by the characteristic).
        Example
            R = ZZ/3[x,y,z]/ideal(x^2-y*z);
            f = y;
            g = z;
            HSLGModule({1/2, 1/2, 1/2}, {y,z,y+z})
        Text
            The other way to call HSLGModule is to by passing it and integer $e$, a list of integers $L$ and a list of ring elements $G$.  It will the compute the maximal $F$-pure Cartier submodule (ie, the HSLG-submodule)
            of the the ideal passed with the {\tt CanonicalIdeal} option with respect to the Cartier action defined by the $e$-iterated Frobenius Trace pre-composed with the elements of $G$ raised to the $L$.
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    SeeAlso
        testModule
        isFInjective
///

doc ///
    Key
        isFInjective
        (isFInjective, Ring)
        [isFInjective, FrobeniusRootStrategy]
        [isFInjective, IsLocal]
        [isFInjective, AssumeCM]
        [isFInjective, AssumeNormal]
        [isFInjective, AssumeReduced]
        [isFInjective, CanonicalStrategy]
    Headline
        whether a ring is F-injective
    Usage
        isFInjective(R)
    Inputs
        R:Ring
        FrobeniusRootStrategy => Symbol
            selects the strategy for internal {\tt frobeniusRoot} calls
        IsLocal => Boolean
            stipulates whether to check F-injectivity only at the origin
        AssumeCM => Boolean
            assumes the ring is Cohen-Macaulay
        AssumeNormal => Boolean
            assumes the ring is normal
        AssumeReduced => Boolean
            assumes the ring is reduced
        CanonicalStrategy => Boolean
            specifies what strategy to use when computing the Frobenius action on top local cohomology
    Outputs
        :Boolean
    Description
        Text
            This function determines whether a ring of finite type over a prime field is F-injective.  Over a more general field, it checks the F-injectivity of the relative Frobenius.
            We begin with an example of an F-injective ring that is not F-pure (taken from the work of Anurag Singh).
        Example
             S = ZZ/3[a,b,c,d,t];
             m = 4;
             n = 3;
             M = matrix{ {a^2 + t^m, b, d}, {c, a^2, b^n-d} };
             I = minors(2, M);
             R = S/I;
             isFInjective(R)
             isFPure(R)
        Text
            Next, let us form the cone over $P^1 \times E$ where $E$ is an elliptic curve.  We begin with a supersingular elliptic curve.  This should be F-injective if and only if it is F-pure.
        Example
            S = ZZ/3[xs, ys, zs, xt, yt, zt];
            EP1 = ZZ/3[x,y,z,s,t]/ideal(x^3+y^2*z-x*z^2); --supersingular elliptic curve
            f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
            R = S/(ker f);
            isFInjective(R)
            isFPure(R)
        Text
            Now we do a similar computation, this time with an ordinary elliptic curve.
        Example
            S = ZZ/3[xs, ys, zs, xt, yt, zt];
            EP1 = ZZ/3[x,y,z,s,t]/ideal(y^2*z-x^3+x*y*z); --ordinary elliptic curve
            f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
            R = S/(ker f);
            isFInjective(R)
            isFPure(R)
        Text
            If {\tt CanonicalStrategy} is set to {\tt Katzman}, which is the default behavior, then the Frobenius action on the top local cohomology (bottom Ext) is computed via the method of Katzman.  If it is set to anything else, it is simply brute forced in Macaulay2 using the fuctoriality of Ext.  {\tt CanonicalStrategy => Katzman} typically is much faster.
        Example
            R = ZZ/5[x,y,z]/ideal(y^2*z + x*y*z-x^3)
            time isFInjective(R)
            time isFInjective(R, CanonicalStrategy => null)
        Text
            If the option {\tt IsLocal} (default value {\tt false}) is set to {\tt true}, {\tt isFInjective} will only check F-injectivity at the origin.  Otherwise it will check F-injectivity globally.  Note that checking F-injectivity at the origin can be slower than checking it globally.  Consider the following example of a non-F-injective ring.
        Example
            R = ZZ/7[x,y,z]/ideal( (x-1)^5 + (y+1)^5 + z^5 );
            isFInjective(R)
            isFInjective(R, IsLocal => true)
        Text
            If the option {\tt AssumeCM} (default value {\tt false}) is set to {\tt true}, then the function only checks the Frobenius action on top cohomology (which is typically much faster). Note that it can give an incorrect answer if the non-injective Frobenius occurs in a lower degree.  Consider the example of the cone over a supersingular elliptic curve times $P^1$.
        Example
            S = ZZ/3[xs, ys, zs, xt, yt, zt];
            EP1 = ZZ/3[x,y,z,s,t]/ideal(x^3+y^2*z-x*z^2);
            f = map(EP1, S, {x*s, y*s, z*s, x*t, y*t, z*t});
            R = S/(ker f);
            time isFInjective(R)
            time isFInjective(R, AssumeCM => true)
        Text
            If the option {\tt AssumedReduced} is set to {\tt true} (its default behavior), then the bottom local cohomology is avoided (this means the Frobenius action on the top potentially nonzero Ext is not computed).
        Text
            If the option {\tt AssumeNormal} (default value {\tt false}) is set to {\tt true}, then we need not compute the bottom two local cohomology modules (or rather their duals).
        Text
            The value of the option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    SeeAlso
        isFPure
        testModule
///

doc ///
    Key
        CurrentRing
    Headline
        an option to specify that a certain ring is used
    Description
        Text
            {\tt CurrentRing} is an option used in various functions specify a ring to work with.
///

doc ///
    Key
        CanonicalIdeal
    Headline
        an option to specify that a certain ideal should be used as the canonical ideal
    Description
        Text
            {\tt CanonicalIdeal} is an option used in various functions specify an ideal to use as the canonical ideal.  In this way, the canonical ideal does not have to be recomputed and one can use a single fixed choice.
///

doc ///
    Key
        GeneratorList
    Headline
        an option to specify that a certain list of elements are used to describe a Cartier action
    Description
        Text
            {\tt GeneratorList} is an option used in various functions to specify a Cartier action, particularly on the canonical module.  In particular, if it is not specified, typically the Cartier action on the canonical module will need to be recomputed.
///


doc ///
    Key
        AssumeCM
    Headline
        an option to assume a ring is Cohen-Macaulay
    Description
        Text
            {\tt AssumeCM} is an option used in various functions, to assume that a ring is Cohen-Macaulay.
///

doc ///
    Key
        AssumeNormal
    Headline
        an option to assume a ring is normal
    Description
        Text
            {\tt AssumeNormal} is an option used in various functions, to assume that a ring is normal.
///

doc ///
    Key
        AssumeReduced
    Headline
        an option to assume a ring is reduced
    Description
        Text
            {\tt AssumeReduced} is an option used in various functions, to assume that a ring is reduced.
///


doc ///
    Key
        CanonicalStrategy
    Headline
        an option for isFInjective
///

doc ///
    Key
        Katzman
    Headline
        a valid value for the option CanonicalStrategy
    SeeAlso
        isFInjective
	CanonicalStrategy
///
