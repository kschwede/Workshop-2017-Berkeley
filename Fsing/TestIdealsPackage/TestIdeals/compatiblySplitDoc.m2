--***********************************************
--***********************************************
--Documentation for compatiblySplit.m2
--***********************************************
--***********************************************

doc ///
    Key
        compatibleIdeals
        (compatibleIdeals, RingElement)
        [compatibleIdeals, FrobeniusRootStrategy]
    Headline
        find all prime ideals compatible with a Frobenius near-splitting 
    Usage
        compatibleIdeals(u)
    Inputs
        u:RingElement
            in a polynomial ring over the prime field $\mathbb{Z}/p$; the element determining the Frobenius splitting
        FrobeniusRootStrategy => Symbol
            stipulates the strategy for internal {\tt frobeniusRoot} calls
    Outputs
        :List
	    containing all prime ideals $P$ of the ring of $u$ such that $u P \subseteq P^{[p]}$ and $u$ is not in $P^{[p]}$

    Description
        Text
            The given element $u$ in a polynomial ring $R$ over the prime field $\mathbb{Z}/p$ defines a
	    $p^{-e}$-linear map $\phi$; this map is obtained by multiplying the $e$th Frobenius trace on the polynomial ring by the polynomial $u$.
	    An ideal $I$ is $\phi$-compatible if $\phi(I)\subseteq I$ or, equivalently, $u I \subseteq I^{[p]}$.
	    The function {\tt compatibleIdeals} returns a list of all prime ideals $P$ such that:

            (a) $u P \subseteq P^{[p]}$, and

            (b) $u$ is not in $P^{[p]}$.

            Condition (b) is equivalent to the non-vanishing of the corresponding near-splitting of $R/P$. When $\phi$ is surjective, the set of all $\phi$-compatible ideals consists of all intersections of the above prime ideals.

	    This function is an implementation of the algorithm described in Moty Katzman and Karl Schwede's paper "An algorithm for computing compatibly Frobenius split subvarieties", J. Symbolic Comput. 47 (2012), no. 8, pp. 996-1008.

	    These prime ideals have a "Matlis-dual" interpretation, too. Let $E$ be the injective hull of the residue field of the localization of $R$ at the irrelevant ideal,
	    and let $T: E \rightarrow E$ be the natural Frobenius map. Then $uT$ is a Frobenius map on $E$, and the primes $P$ computed by this function are precisely those for which
	    $uT$ restricts to a nonzero Frobenius map of the annihlator of $P$ on $E$.

            The following is a simple example, which is split with the coordinate axes in $\mathbb{A}^2$.
        Example
            R = ZZ/3[s,t];
            u = s^2*t^2;
            compatibleIdeals u
        Text
            Here is a more substantial example.
        Example
            R = ZZ/2[x_21,x_31,x_32,x_41,x_42,x_43];
            u = x_41*(x_31*x_42-x_41*x_32)*(x_41-x_21*x_42-x_31*x_43+x_21*x_32*x_43);
            print \ compatibleIdeals u;
        Text
            The option {\tt FrobeniusRootStrategy} is passed to internal @TO frobeniusRoot@ calls.
///
