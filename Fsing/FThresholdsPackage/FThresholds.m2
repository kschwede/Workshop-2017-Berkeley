
newPackage( "FThresholds",
Version => "0.1",
Date => "August 13th, 2018",
Authors => {
     {Name => "Erin Bela",
     Email => "ebela@nd.edu"
     },
     {Name => "Alberto F. Boix",
     Email => "alberto.fernandezb@upf.edu"
     },
     {Name => "Juliette Bruce",
     Email => "juliette.bruce@math.wisc.edu",
     HomePage => "https://juliettebruce.github.io/"
     },
     {Name => "Drew Ellingson",
     Email => "drewtell@umich.edu"
     },
     {Name => "Daniel Hernandez",
     Email => "hernandez@ku.edu",
     HomePage => "https://hernandez.faculty.ku.edu"
     },
     {Name => "Zhibek Kadyrsizova",
     Email => "zhibek.kadyrsizova@nu.edu.kz"
     },
     {Name => "Moty Katzman",
     Email => "m.katzman@sheffield.ac.uk",
     HomePage => "http://www.katzman.staff.shef.ac.uk/"
     },
     {Name => "Sara Malec",
     Email => "malec@hood.edu"
     },
     {Name => "Matthew Mastroeni",
     Email => "mastroe2@illinois.edu"
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
     HomePage => "http://www.knox.edu/academics/faculty/teixeira-pedro.html"
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
--F-thresholds computations (MainFunctions.m2)
    "BinaryRecursive",
    "ComputePreviousNus",
    "criticalExponentApproximation",
    "fpt",
    "fptApproximation",
    "fptGuessList", --Karl (probably should be incorporated into fpt
    "FRegularityCheck",
    "FrobeniusPower",
    "FrobeniusRoot",
    "ftApproximation",
    "isFJumpingExponent",
    "isFPT", --Karl (should be redone, so as not to assume a polynomial ring)
    "compareFPT",
    "mu",
    "muList",
    "nu",
    "NuCheck",
    "nuList",
    "Search",
    "StandardPower",
    "ContainmentTest",
    "UseColonIdeals",
    "UseSpecialAlgorithms"
}

--loadPackage("TestIdeals", LoadDocumentation => true, Reload=>true);


--*************************************************

load "./FThresholds/DivisorPatch.m2" --some helper functions

load "./FThresholds/BasicFunctions.m2"

load "./FThresholds/MainFunctions.m2"

load "./FThresholds/SpecialFThresholds.m2"

beginDocumentation()

load "./FThresholds/MainFunctionsDoc.m2"

load "./FThresholds/SpecialFThresholdsDoc.m2"

-- TESTS

load "./FThresholds/SpecialFThresholdsTest.m2"
