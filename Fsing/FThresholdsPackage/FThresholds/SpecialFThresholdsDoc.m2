doc ///
    Key
        isSimpleNormalCrossing
        (isSimpleNormalCrossing, RingElement)
        (isSimpleNormalCrossing, Product)
        [isSimpleNormalCrossing, IsLocal]
        [isSimpleNormalCrossing, Verbose]
    Headline
       determines whether a polynomial is a product of factors that are in simple normal crossing
    Usage
        isSimpleNormalCrossing(f)
        isSimpleNormalCrossing(P)
    Inputs
        f:RingElement
            in a ring
        P:Product
            a product {\tt P} of ring elements 
        IsLocal => Boolean
            tells the function whether to only consider the behavior at the origin
        Verbose => Boolean
            toggles verbose output
    Outputs
        :Boolean
            true if it is simple normal crossing, false if not
    Description
        Text
            Let $f$ be an element of a {\tt PolynomialRing} (or an object of
            class {\tt Product} representing a factoring of ring element $f$).
            The function {\tt isSimpleNormalCrossing} returns true if the distinct factors of $f$
            are in simple normal crossing.  In other words, if at each point,
            the distinct factors in the factorization of $f$,
            locally analytically, form part of a regular system of parameters.
        Example
            R = ZZ/7[x,y,z];
            isSimpleNormalCrossing(x^3*y^2)
            isSimpleNormalCrossing(x^2-y^2)
            isSimpleNormalCrossing(x*y*(x-y))
            isSimpleNormalCrossing(x^2-y*z)
        Text
            The option {\tt IsLocal} (default value {\tt true}) is used to specify
            whether we should work at the origin (when {\tt true}) or globally (when {\tt false}).
        Example
            R = QQ[x,y,z];
            f = (y - (x-1)^2)*y^2; --SNC at the origin, but not globally
            isSimpleNormalCrossing(f)
            isSimpleNormalCrossing(f, IsLocal=>false)
            g = (y-1)^2+(x-7)^2 --doesn't even pass through the origin
            isSimpleNormalCrossing(g)
            isSimpleNormalCrossing(g, IsLocal=>false)
            h = x*y^2*(x+1)^3*(y-1)^4; --SNC everywhere
            isSimpleNormalCrossing(h)
            isSimpleNormalCrossing(h, IsLocal=>false)
        Text
            Setting the option {\tt Verbose} (default value {\tt false}) to {\tt true} produces verbose output.
///
