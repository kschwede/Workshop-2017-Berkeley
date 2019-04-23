--***********************************************
--***********************************************
--Documentation for frobeniusPowers.m2
--***********************************************
--***********************************************

doc ///
    Key
        fastExponentiation
        (fastExponentiation, ZZ, RingElement)
    Headline
        compute a power of an element in a ring of positive characteristic quickly
    Usage
        fastExponentiation(n, f)
    Inputs
        n:ZZ
            nonnegative
     	f:RingElement
            in positive characteristic
    Outputs
        :RingElement
            the {\tt n^{th}} power of {\tt f}
    Description
        Text
            In prime characteristic $p > 0$, raising a sum $a + b$ to the $p$th power
            is more quickly done by simply computing $a^p$ and $b^p$ and adding them.
            The basic strategy behind {\tt fastExponentiation} is to break up the exponent into its base $p$
            expansion, and then use the exponent rules. For example,
            $(x + y)^{3p^2 + 5p + 2} = ((x + y)^3)^{p^2}((x + y)^5)^p(x + y)^2$.
        Example
            R = ZZ/5[x];
            f = sum(10, i -> x^i);
            time f^321;
            time fastExponentiation(321, f);
        Text
            If an element in a ring of characteristic 0 is passed,
            {\tt fastExponentiation(n,f)} simply computes $f^n$ in the usual way.
///

doc ///
    Key
        frobenius
        [frobenius, FrobeniusRootStrategy]
    Headline
        compute a Frobenius power of an ideal or a matrix
    Usage
        frobenius(e, I)
        frobenius^e(I)
        frobenius(e, M)
        frobenius^e(M)
        frobenius(I)
        frobenius(M)
    Inputs
        e:ZZ
            the power of Frobenius to take
        I:Ideal
            in a ring of positive characteristic $p > 0$
        M:Matrix
            with entries in a ring of positive characteristic $p > 0$
        FrobeniusRootStrategy => Symbol
            chooses the strategy for internal {\tt frobeniusRoot} calls
    Outputs
        :Ideal
	    the {\tt p^e}-th Frobenius power of {\tt I} (with {\tt e = 1}, if {\tt e} is not specified)
	:Matrix
	    the {\tt p^e}-th Frobenius power of {\tt M} (with {\tt e = 1}, if {\tt e} is not specified)
    Description
        Text
            Given an ideal $I$ in a ring of characteristic $p > 0$ and a nonnegative
            integer $e$, {\tt frobenius(e,I)} or {\tt frobenius^e(I)} returns the
            $p^e$-th Frobenius power $I^{[p^e]}$, that is, the ideal generated by
            all powers $f^{p^e}$, with $f \in I$ (see @TO frobeniusPower@).
        Example
            R = ZZ/3[x,y];
            I = ideal(x^2, x*y, y^2);
            frobenius(2, I)
            frobenius^2(I)
            frobeniusPower(3^2, I)
        Text
            If $e$ is negative, then {\tt frobenius(e, I)} or {\tt frobenius^e(I)}
            computes a Frobenius root, as defined by Blickle, Mustata, and Smith
            (see @TO frobeniusRoot@).
        Example
            R = ZZ/5[x,y,z,w];
            I = ideal(x^27*y^10 + 3*z^28 - x^2*y^15*z^35, x^17*w^30 + 2*x^10*y^10*z^35, x*z^50);
            frobenius(-1, I)
            frobenius(-2, I)
            frobeniusRoot(2, I)
        Text
            If $M$ is a matrix with entries in a ring of characteristic
            $p > 0$ and $e$ is a nonnegative integer, then {\tt frobenius(e, M)} or
            {\tt frobenius^e(M)} outputs a matrix whose entries are
            the $p^e$-th powers of the entries of $M$.
        Example
            M = ZZ/3[x,y];
            M = matrix {{x, y},{x + y, x^2 + y^2}};
            frobenius(2, M)
        Text
            {\tt frobenius(I)} and {\tt frobenius(M)} are abbreviations for
            {\tt frobenius(1,I)} and {\tt frobenius(1,M)}.
    SeeAlso
        frobeniusPower
        frobeniusRoot
///

doc ///
    Key
        frobeniusPower
        ( frobeniusPower, ZZ, Ideal )
        ( frobeniusPower, QQ, Ideal )
        [frobeniusPower, FrobeniusPowerStrategy]
        [frobeniusPower, FrobeniusRootStrategy]
    Headline
        compute a (generalized) Frobenius power of an ideal
    Usage
        frobeniusPower(n, I)
     	frobeniusPower(t, I)
    Inputs
        n:ZZ
            nonnegative
    	t:QQ
            nonnegative
        I:Ideal
            in a ring of characteristic $p > 0$
        FrobeniusPowerStrategy => Symbol
            selects the strategy for {\tt frobeniusPower}
        FrobeniusRootStrategy => Symbol
            chooses the strategy for internal {\tt frobeniusRoot} calls
    Outputs
        :Ideal
	    the {\tt n^{th}} or {\tt t^{th}} Frobenius power of {\tt I}
    Description
        Text
	        {\tt frobeniusPower(t,I)} computes the generalized Frobenius power
            $I^{[t]}$, as introduced by Hernandez, Teixeira, and Witt.
            If the exponent is a power of the characteristic, this is just the
            usual Frobenius power.
        Example
            R = ZZ/5[x,y];
            I = ideal(x, y);
            frobeniusPower(125, I)
        Text
            If $n$ is an arbitrary nonnegative integer, then write the base $p$
            expansion of $n$ as follows: $n = a_0 + a_1 p + a_2 p^2 + ... + a_r p^r$.
            Then the $n$th Frobenius power of $I$ is defined as follows:
            $I^{[n]} = (I^{a_0})(I^{a_1})^{[p]}(I^{a_2})^{[p^2]}\cdots(I^{a_r})^{[p^r]}$.
        Example
            R = ZZ/3[x,y];
            I = ideal(x, y);
            adicExpansion(3, 17)
            J1 = I^2*frobenius(1, I^2)*frobenius(2, I);
            J2 = frobeniusPower(17, I);
            J1 == J2
        Text
            If $t$ is a rational number of the form $t = a/p^e$, then
            $I^{[t]} = (I^{[a]})^{[1/p^e]}$.
        Example
            R = ZZ/5[x,y,z];
            I = ideal(x^50*z^95, y^100 + z^27);
            frobeniusPower(4/5^2, I)
            frobeniusRoot(2, frobeniusPower(4, I))
        Text
            If $t$ is an arbitrary nonegative rational number, and
            $\{ t_n \} = \{ a_n/p^{e_n} \}$ is a sequence of rational numbers
            converging to $t$ from above, then $I^{[t]}$ is the largest ideal
            in the increasing chain of ideals $\{ I^{[t_n]} \}$.
        Example
            p = 7;
            R = ZZ/p[x,y];
            I = ideal(x^50, y^30);
            t = 6/19;
            expon = e -> ceiling(p^e*t)/p^e; -- a sequence converging to t from above
            print \ apply(6, i -> frobeniusPower(expon i, I));
            frobeniusPower(t, I)
        Text
            The option {\tt FrobeniusPowerStrategy} controls the strategy for computing the generalized Frobenius power $I^{[t]}$. The two valid options are {\tt Safe} and {\tt Naive}, and the default strategy is {\tt Naive}.
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
    SeeAlso
        frobenius
        frobeniusRoot
///

doc ///
    Key
        Naive
    Headline
        a valid value for the option FrobeniusPowerStrategy
    SeeAlso
        FrobeniusPowerStrategy
///

doc ///
    Key
        Safe
    Headline
        a valid value for the option FrobeniusPowerStrategy
    SeeAlso
        FrobeniusPowerStrategy
///

doc ///
    Key
        FrobeniusPowerStrategy
    Headline
        an option for frobeniusPower
    Description
        Text
            Valid options are {\tt Naive} and {\tt Safe}.
///
