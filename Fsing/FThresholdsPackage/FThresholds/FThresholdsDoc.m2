

document {
    Key => FThresholds,
    Headline => "a package for computing F-pure thresholds and related invariants",
    EM "FThresholds", " is a package for computing ", TEX ///$F$///, "-pure thresholds,
    ", TEX ///$F$///, "-jumping exponents, and related numerical measures of singularities in positive characteristic.",
    BR{},BR{},"The Frobenius endomorphism on a ring of prime characteristic ", TEX ///$p > 0$///," which sends a ring element to
    its ", TEX ///$p > 0$///,"-th power, is a fundamental tool in prime characteristic commutative algebra.
    Kunz showed that regularity is characterize
    by the behavior of this map, and since then, many other properties of Frobenius have been used to
    measure how singular a ring or function is.  The ", TEX ///$F$///, "-pure threshold is a very prominent
    example of this philosopy.", BR{},BR{},"
    This package relies heavily on the ", TO "TestIdeals", " package. Many special cases (binomials, diagonal elements, etc) are", EM " seemlessly ",
    "handled by using special formulas found in ", HREF{"https://doi.org/10.1090/S0002-9939-2014-12260-X", "Hernández"}, ", ",HREF{"https://doi.org/10.1090/S0002-9939-2014-11941-1", "Hernández"}, ", and ", HREF{"https://doi.org/10.1090/S0002-9939-2014-11941-1","Hernández-Teixeira"},
    ".  This package even can compute ", TEX ///$F$///, "-pure thresholds in ", EM "singular ambient rings.",
    BR{},BR{},
    BOLD "Notable functions:",BR{},
    UL {
      {TO "fpt", ":  This computes (or estimates) the ", TEX ///$F$///, "-pure threshold."},
      {TO "isFJumpingExponent", ":  This function checks whether a given number is a ", TEX ///$F$///, "-jumping exponent."},
      {TO "compareFPT", ":  This determines whether the given is number is bigger, smaller, or equal to the ", TEX ///$F$///, "-pure threshold."},
      {TO "nu", ":  This is the function whose normalized value provides a way to estimate the ", TEX ///$F$///, "-pure threshold, ", TEX ///$F$///, "-threshold and more."}
	},
	BR{},"The following example demonstrates some of the functionality of this package.",
    EXAMPLE{"p = 131;","R =ZZ/p[x,y];","f = x^13-y^5;","c = fpt(f)","compareFPT(c-1/131^2, f)","compareFPT(c, f)","compareFPT(c+1/131^2, f)","isFJumpingExponent(36/65, f)"},
    BR{},BR{},
    BOLD "Acknowledgements:",BR{},BR{},
    "The authors would like to thank David Eisenbud, Daniel Grayson, Anurag Singh, Greg Smith, and Mike Stillman for useful conversations and comments on the development of this package.",BR{}
}
