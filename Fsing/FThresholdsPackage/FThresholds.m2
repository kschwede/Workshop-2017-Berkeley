newPackage( "FThresholds",
Version => "2.0",
Date => "June 5th, 2019",
Authors => {
     {Name => "Juliette Bruce",
     Email => "juliette.bruce@math.wisc.edu",
     HomePage => "https://juliettebruce.github.io/"
     },
     {Name => "Daniel Hernandez",
     Email => "hernandez@ku.edu",
     HomePage => "https://hernandez.faculty.ku.edu"
     },
     {Name => "Zhibek Kadyrsizova",
     Email => "zhibek.kadyrsizova@nu.edu.kz"
     },
     {Name => "Sara Malec",
     Email => "malec@hood.edu"
     },
     {Name => "Matthew Mastroeni",
     Email => "mmastro@okstate.edu",
     HomePage => "https://mnmastro.github.io/"
     },
     {Name => "Maral Mostafazadehfard",
     Email => "maralmostafazadehfard@gmail.com"
     },
     {Name => "Marcus Robinson",
     Email => "robinson@math.utah.edu"
     },
     {Name => "Karl Schwede",
      Email => "schwede@math.utah.edu",
     HomePage => "http://math.utah.edu/~schwede/"
     },
     {Name => "Dan Smolkin",
     Email => "smolkin@math.utah.edu",
     HomePage => "http://dan.smolk.in"
     },
     {Name => "Pedro Teixeira",
     Email => "pteixeir@knox.edu",
     HomePage => "https://www.knox.edu/academics/majors-and-minors/mathematics/faculty/teixeira-pedro"
     },
     {Name => "Emily Witt",
     Email => "witt@ku.edu",
     HomePage => "https://witt.faculty.ku.edu"
     }
},
Headline => "A package for calculations of F-thresholds",
DebuggingMode => true,
Reload => true,
AuxiliaryFiles => true,
PackageExports => {"TestIdeals"}
)

export{
    "compareFPT",
    "ContainmentTest",
    "fpt",
    "FRegularityCheck",
    "FrobeniusPower",
    "FrobeniusRoot",
    "isFJumpingExponent",
    "isFPT",
    "nu",
    "ReturnList",
    "Search",
    "StandardPower",
    "UseFSignature",
    "UseSpecialAlgorithms"
}

--*************************************************

load "./FThresholds/DivisorPatch.m2" --some helper functions

load "./FThresholds/TestIdealsPatch.m2"

load "./FThresholds/BasicFunctions.m2"

load "./FThresholds/MainFunctions.m2"

load "./FThresholds/SpecialFThresholds.m2"

-- DOCUMENTATION

beginDocumentation()

load "./FThresholds/FThresholdsDoc.m2"

load "./FThresholds/MainFunctionsDoc.m2"

-- TESTS

load "./FThresholds/MainFunctionsTest.m2"
