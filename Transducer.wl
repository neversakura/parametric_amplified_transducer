(* ::Package:: *)

BeginPackage["Transducer`"];


SolveODEConst::usage="SolveODEConst[\[CapitalDelta], \[Kappa], \[CapitalOmega], t] solves the intra-cavity \[Alpha] for constant drive with amplitude \[CapitalOmega].";


SolveSteadyConst::usage="SolveSteadyConst[\[CapitalDelta], \[Kappa], \[CapitalOmega]] solves the steady state of the intra-cavity \[Alpha] for constant drive with amplitude \[CapitalOmega].";


SolveODEOsc::usage="SolveODEOsc[\[CapitalDelta], \[Kappa], \[CapitalOmega], \[Omega], t] solves the intra-cavity \[Alpha] for oscillating drive with amplitude \[CapitalOmega] and frequency \[Omega].";


SolveSteadyOsc::usage="SolveSteadyOsc[\[CapitalDelta], \[Kappa], \[CapitalOmega], \[Omega]] solves the amplitude of the steady state \[Alpha] for oscillating drvie with amplitude \[CapitalOmega] and frequency \[Omega].";


AmatDecompose::usage="AmatDecompose[Am] decomposes the matrix Am into dc, positive-frequency and negative-frequency parts.";


Iterative\[CapitalXi]::usage="Iterative\[CapitalXi][Ad, Ap, Am, N, \[Omega], \[Omega]m] calculate the \[CapitalXi](\[Omega]) matrix to Nth order given the driving frequency \[Omega]m for the pump laser.";


Logspace::usage="Logspace[a, b, n] gives a sequence starting at 10^a and ending at 10^b, with n points logarithmically spaced.";


TransFConst::usage="TransFConst[A, B, \[Omega], opts] solves the transfer function for the case of constant driving." 


TransFOsc::usage="TransFOsc[Ad, Ap, Am, B, N, \[Omega]] solves the transfer matrix T(\[Omega]) for the case of PD with 2N sidebands."


IterativeX


TMech


TForth


Begin["`Private`"];


SolveODEConst[\[CapitalDelta]_, \[Kappa]_, \[CapitalOmega]_, t_] :=
    Module[{y, sol},
        sol = DSolve[{y'[t] == -I * \[CapitalDelta] * y[t] - \[Kappa] * y[t] / 2 - I * \[CapitalOmega], 
            y[0] == 0}, y[t], t];
        y[t] /. sol[[1]] // FullSimplify
    ];


SolveSteadyConst[\[CapitalDelta]_, \[Kappa]_, \[CapitalOmega]_] := Module[{y, t, sol},
    sol = SolveODEConst[\[CapitalDelta], \[Kappa], \[CapitalOmega], t];
    Limit[
        sol
        ,
        t -> Infinity
        ,
        Assumptions -> {
            If[NumericQ[\[CapitalDelta]],
                Null
                ,
                \[CapitalDelta] > 0
            ]
            ,
            If[NumericQ[\[Kappa]],
                Null
                ,
                \[Kappa] > 0
            ]
        }
    ]
];


SolveODEOsc[\[CapitalDelta]_, \[Kappa]_, \[CapitalOmega]_, \[Omega]_, t_] :=
    Module[{y, sol},
        sol = DSolve[{y'[t] == -I * \[CapitalDelta] * y[t] - \[Kappa] * y[t] / 2 - I * \[CapitalOmega] * 
            Exp[-I * 2 * \[Omega] * t], y[0] == 0}, y[t], t];
        y[t] /. sol[[1]] // FullSimplify
    ];


SolveSteadyOsc[\[CapitalDelta]_, \[Kappa]_, \[CapitalOmega]_, \[Omega]_] :=
    Module[{y, t, sol},
        sol = SolveODEOsc[\[CapitalDelta], \[Kappa], \[CapitalOmega], \[Omega], t];
        Coefficient[sol, Exp[-2 * I * t * \[Omega]]]
    ];


AmatDecompose[Am_] :=
    Module[{Ad, Aoff, Ao, Aoc, tidx},
        Ad = DiagonalMatrix @ Diagonal @ Am;
        Aoff = Am - Ad;
        tidx = Position[Aoff, Conjugate[_]];
        Ao = ConstantArray[0, Dimensions @ Am];
        For[i = 1, i <= Length[tidx], i++,
            Ao[[tidx[[i, 1]], tidx[[i, 2]]]] = Am[[tidx[[i, 1]], tidx
                [[i, 2]]]]
        ];
        Aoc = Aoff - Ao;
        {"diag" -> Ad, "\!\(\*SuperscriptBox[\(G\), \(*\)]\)" -> Ao, "G" -> Aoc
            }
    ];


Iterative\[CapitalXi][Ad_, Ap_, Am_, N_, \[Omega]_, opts : OptionsPattern[]] :=
    Module[{\[CapitalXi]p, \[CapitalXi]m, iden},
        iden = IdentityMatrix[Dimensions[Ad, 1][[1]]]; 
        \[CapitalXi]p = Ap . Simplify[Inverse[
            I * (-\[Omega] - 2 * N * \[Omega]) * iden - Ad],FilterRules[{opts}, Options[
            Simplify]]] . Am; 
        \[CapitalXi]m = Am . Simplify[Inverse[I * (-\[Omega] + 
            2 * N * \[Omega]) * iden - Ad], FilterRules[{opts}, Options[
            Simplify]]] . Ap; 
        Do[\[CapitalXi]p = Ap . Simplify[Inverse[I * (-\[Omega] - 2 * i *
             \[Omega]) * iden - Ad - \[CapitalXi]p], FilterRules[{opts}, Options[
            Simplify]]] . Am; \[CapitalXi]m = Am . Simplify[Inverse[I * (-\[Omega] + 2 * i * \[Omega]) 
            * iden - Ad - \[CapitalXi]m],FilterRules[{opts}, Options[
            Simplify]]] . Ap, {i, N - 1, 1, -1}]; 
       {Simplify[\[CapitalXi]p, FilterRules[{opts}, Options[
            Simplify]]], Simplify[\[CapitalXi]m, FilterRules[{opts}, Options[
            Simplify]]]}
    ];


Logspace[a_, b_, n_] := 10.0^Range[a, b, (b - a)/(n - 1)];


TransFConst[A_, B_, \[Omega]_, opts : OptionsPattern[]] :=
    Module[{dimIn = Dimensions[B, 2][[2]], dimS = Dimensions[A, 1][[1
        ]], idenIn, idenS},
        idenIn = IdentityMatrix[dimIn]; idenS = IdentityMatrix[dimS];
             FullSimplify[Transpose[B] . Inverse[-idenS * I * \[Omega] - A] . B - idenIn,
             FilterRules[{opts}, Options[FullSimplify]]]
    ]


TransFOsc[Ad_, Ap_, Am_, B_, N_, \[Omega]_] :=
    Module[{\[CapitalXi], dimIn = Dimensions[B, 2][[2]], dimS = Dimensions[B, 1][[1
        ]], idenIn, idenS},
        idenIn = IdentityMatrix[dimIn]; idenS = IdentityMatrix[dimS];
        \[CapitalXi] = Iterative\[CapitalXi][Ad, Ap, Am, N, \[Omega]]; Transpose[B] . Inverse[-I *
             \[Omega] * idenS - Ad - \[CapitalXi][[1]] - \[CapitalXi][[2]]] . B - idenIn // Simplify
    ]


IterativeX[Ad_, Ap_, Am_, N_, \[Omega]_, opts : OptionsPattern[]] := 
	Module[{iden, rules, Xp={}, Xm={}, \[CapitalXi]p={}, \[CapitalXi]m={}},
	iden = IdentityMatrix[Dimensions[Ad,1][[1]]];
	rules = FilterRules[{opts}, Options[
            Simplify]];
	Xp=Prepend[Xp, Simplify[Inverse[
            I * (-\[Omega] - 2 * N * \[Omega]) * iden - Ad], rules]];
    Xm=Prepend[Xm, Simplify[Inverse[I * (-\[Omega] + 
            2 * N * \[Omega]) * iden - Ad], rules]];
    \[CapitalXi]p=Prepend[\[CapitalXi]p, Ap . Xp[[1]] . Am];
    \[CapitalXi]m=Prepend[\[CapitalXi]m, Am . Xm[[1]] . Ap];
    Do[Xp=Prepend[Xp, Simplify[Inverse[I * (-\[Omega] - 2 * i *
             \[Omega]) * iden - Ad - \[CapitalXi]p[[1]]], rules]];
       Xm=Prepend[Xm, Simplify[Inverse[I * (-\[Omega] + 2 * i * \[Omega]) 
            * iden - Ad - \[CapitalXi]m[[1]]], rules]];
       \[CapitalXi]p=Prepend[\[CapitalXi]p,Ap . Xp[[1]] . Am]; 
       \[CapitalXi]m=Prepend[\[CapitalXi]m,Am . Xm[[1]] . Ap], {i, N - 1, 1, -1}];
    {Xp, \[CapitalXi]p, Xm, \[CapitalXi]m}
	]


TMech[Ad_, Ap_, Am_, B_, N_, \[Omega]_, opts : OptionsPattern[]] :=
    Module[{iden, Xp, Kp, Xm, Km, X, K = Transpose[B], rules},
        iden = IdentityMatrix[Dimensions[Ad, 1][[1]]]; rules = FilterRules[
            {opts}, Options[Simplify]]; {Xp, Kp, Xm, Km} = IterativeX[Ad, Ap, Am,
             N, \[Omega]]; X = Simplify[Inverse[-I * \[Omega] * iden - Ad - Kp[[1]] - Km[[1]]],
             rules]; {Simplify[K . X . Ap . Xp[[1]] . B, rules], Simplify[K . X .
             Am . Xm[[1]] . B, rules]}
    ]


TForth[Ad_, Ap_, Am_, B_, N_,\[Omega]_, opts : OptionsPattern[]] :=
    Module[{iden, Xp, Kp, Xm, Km, X, K = Transpose[B], rules},
        iden = IdentityMatrix[Dimensions[Ad, 1][[1]]]; rules = FilterRules[
            {opts}, Options[Simplify]]; {Xp, Kp, Xm, Km} = IterativeX[Ad, Ap, Am,
             N, \[Omega]]; X = Simplify[Inverse[-I * \[Omega] * iden - Ad - Kp[[1]] - Km[[1]]],
             rules]; {Simplify[K . X . Ap . Xp[[1]] . Ap . Xp[[2]] . B, rules], Simplify[
            K . X . Am . Xm[[1]] . Am . Xm[[2]] . B, rules]}
    ]


End[];


EndPackage[];
