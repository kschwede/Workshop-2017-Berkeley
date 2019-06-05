

document {
    Key => FThresholds,
    Headline => "a package for computing F-pure thresholds and related invariants",
    EM "FThresholds", " is a package for computing ", TEX ///$F$///, "-pure thresholds,
    ", TEX ///$F$///, "-jumping exponents, and related numerical measures of singularities in positive characteristic.",
    BR{},BR{},"The Frobenius endomorphism on a ring of prime characteristic ", TEX ///$p > 0$///,", which sends a ring element to
    its ", TEX ///$p$///,"-th power, is a fundamental tool in positive characteristic commutative algebra.
    Kunz showed that regularity is characterized by the behavior of this map, and since then many other properties of Frobenius have been used to measure how singular a ring or function is. The ", TEX ///$F$///, "-pure threshold is a very prominent
    example of this philosophy.", BR{},BR{},"
    This package relies heavily on the ", TO "TestIdeals", " package. Many special cases (binomials, diagonal polynomials, etc.) are", EM " seemlessly ",
    "handled by using special formulas found in ", HREF{"https://doi.org/10.1090/S0002-9939-2014-12260-X", "Hernández"}, ", ",HREF{"https://doi.org/10.1090/S0002-9939-2014-11941-1", "Hernández"}, ", and ", HREF{"https://arxiv.org/abs/1404.5871","Hernández-Teixeira"},
    ".  This package can even compute ", TEX ///$F$///, "-pure thresholds in ", EM "singular ambient rings.",
    BR{},BR{},
    BOLD "Notable functions:",BR{},
    UL {
      {TO "fpt", " computes (or estimates) the ", TEX ///$F$///, "-pure threshold."},
      {TO "isFJumpingExponent", " checks whether a given number is an ", TEX ///$F$///, "-jumping exponent."},
      {TO "compareFPT", " determines whether the given number is greater than, less than, or equal to the ", TEX ///$F$///, "-pure threshold."},
      {TO "nu", " is the function whose normalized value provides a way to estimate the ", TEX ///$F$///, "-pure threshold, ", TEX ///$F$///, "-thresholds and more."}
	},
	BR{},"The following example demonstrates some of the functionality of this package.",
    EXAMPLE{"p = 131;","R =ZZ/p[x,y];","f = x^13 - y^5;","c = fpt(f)","compareFPT(c - 1/p^2, f)","compareFPT(c,  f)","compareFPT(c + 1/p^2, f)","isFJumpingExponent(36/65, f)"},
    BR{},BR{},
    BOLD "Acknowledgements:",BR{},BR{},
    "The authors would like to thank David Eisenbud, Daniel Grayson, Anurag Singh, Greg Smith, and Mike Stillman for useful conversations and comments on the development of this package.",BR{},BR{},
    BOLD "Contributors", BR{}, BR{},
    EM "(the following non-authors contributed to this package)",
        UL {
        {"Alice"},
        {"Bob"},
        {"Eve"}
    }, BR{},BR{}
}
