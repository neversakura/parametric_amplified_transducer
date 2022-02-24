(* ::Package:: *)

BeginPackage["Transducer`"];


SolveODEConst::usage="SolveODEConst[\[CapitalDelta], \[Kappa], \[CapitalOmega], t] solves the intra-cavity \[Alpha] for constant drive with amplitude \[CapitalOmega].";


SolveSteadyConst::usage="SolveSteadyConst[\[CapitalDelta], \[Kappa], \[CapitalOmega]] solves the steady state of the intra-cavity \[Alpha] for constant drive with amplitude \[CapitalOmega].";


SolveODEOsc::usage="SolveODEOsc[\[CapitalDelta], \[Kappa], \[CapitalOmega], \[Omega], t] solves the intra-cavity \[Alpha] for oscillating drive with amplitude \[CapitalOmega] and frequency \[Omega].";


SolveSteadyOsc::usage="SolveSteadyOsc[\[CapitalDelta], \[Kappa], \[CapitalOmega], \[Omega]] solves the amplitude of the steady state \[Alpha] for oscillating drvie with amplitude \[CapitalOmega] and frequency \[Omega].";


AmatDecompose::usage="AmatDecompose[Am] decomposes the matrix Am into dc, positive-frequency and negative-frequency parts.";


FFTFreq::usage="FFTFreq[n, d] generates the sample frequencies of the n-point FFT with sample spacing d.";


FFTSample::usage="FFTSample[func, n, dt, tf] sample function with n-point DFT from tf-(n-1)dt to tf.";


InputSigFFT::usage="InputSigFFT[\[Omega], n, dt] calculate the n-point spectrum density of the input signal at frequenc \[Omega] with sample spacing d.";


InputSigAmp::usage="InputSigAmp[\[Omega], n, dt] calculates the input signal amplitude using a n-point squre window function.";


OutputPiecewisePlot::usage="OutputPiecewisePlot[func, ts, te, tf, points] plots piecewise output signals where the Fourier transformed region is highlighted in red.";


OutputFreqPlot::usage="OutputFreqPlot[func, n, dt, tf, \[Omega]] plot the spectrum of the `func` sampled from tf-(n-1)dt to tf, together with a single frequency input function centered at \[Omega].";


Iterative\[CapitalXi]::usage="Iterative\[CapitalXi][Ad, Ap, Am, N, \[Omega], \[Omega]m] calculate the \[CapitalXi](\[Omega]) matrix to Nth order given the driving frequency \[Omega]m for the pump laser.";


GetEfficiency::usage="GetEfficiency[func, n, dt, \[Omega], t] calculate the transduction efficieny \[Eta](\[Omega]) for `func` sampled from t-(n-1)dt to t.";


Logspace::usage="Logspace[a, b, n] gives a sequence starting at 10^a and ending at 10^b, with n points logarithmically spaced.";


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
            Exp[-I * \[Omega] * t], y[0] == 0}, y[t], t];
        y[t] /. sol[[1]] // FullSimplify
    ];


SolveSteadyOsc[\[CapitalDelta]_, \[Kappa]_, \[CapitalOmega]_, \[Omega]_] :=
    Module[{y, t, sol},
        sol = SolveODEOsc[\[CapitalDelta], \[Kappa], \[CapitalOmega], \[Omega], t];
        Coefficient[sol, Exp[-I * t * \[Omega]]]
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


FFTFreq[n_, d_] :=
    Module[{xf},
        xf =
            If[EvenQ[n],
                Join[Table[i, {i, 0, n / 2 - 1}], Table[i, {i, -n / 2,
                     -1}]] / (d * n)
                ,
                Join[Table[i, {i, 0, (n - 1) / 2}], Table[i, {i, -(n 
                    - 1) / 2, -1}]] / (d * n)
            ];
        FFTShift[xf]
    ];


FFTShift[dat_?ArrayQ] :=
    Module[{dims = Dimensions[dat]},
        RotateRight[dat, Quotient[dims, 2]]
    ];


FFTSample[func_, n_, dt_, tf_] :=
    Module[{ysample},
        FFTShift[Fourier[Table[func[t][[1]], {t, tf - (n - 1) * dt, tf, dt}]]]/Sqrt[n]
    ];


InputSigFFT[\[Omega]_, n_, dt_]:=Module[{},
	FFTShift[Fourier[Table[-1/Sqrt[2*\[Pi]]*Exp[-I*\[Omega]*t],{t,0,(n-1)*dt,dt}]]]/Sqrt[n]
];


InputSigAmp[\[Omega]_, n_, dt_]:=Module[{yf},
	yf=FFTShift[Fourier[Table[-1/Sqrt[2*\[Pi]]*Exp[-I*\[Omega]*t],{t,0,(n-1)*dt,dt}]]];
	(Max@Abs@yf)/Sqrt[n]
];


OutputPiecewisePlot[func_, ts_, te_, tf_, points_] :=
    Module[{p},
        p = Show[{Plot[Evaluate[func[t]], {t, 0, ts}, PlotPoints
             -> points[[1]]], Plot[Evaluate[func[t]], {t, ts, te}, PlotPoints
             -> points[[2]], PlotStyle -> Red], Plot[Evaluate[func[t]], {t,
             te, tf}, PlotPoints -> points[[3]]]}, PlotRange -> All, BaseStyle ->
             {FontFamily -> "Times New Roman", 15}, LabelStyle -> {FontFamily -> 
            "Times New Roman"}];
        Legended[p, Placed[LineLegend[{Red}, {Style["Fourier sampled region",
             FontFamily -> "Times New Roman", 15]}], Top]]
    ];


OutputFreqPlot[func_, n_, dt_, tf_, \[Omega]_] :=
    Module[{xf, yf, yfIn},
        xf = FFTFreq[n, dt];
        yf = FFTSample[func, n, dt, tf];
        yfIn = InputSigFFT[\[Omega], n, dt];
        p = Show[ListLinePlot[Transpose[{xf, Abs[yfIn]}], PlotRange ->
             All, PlotStyle -> {Blue, Thickness[0.01]}], ListLinePlot[Transpose[{xf,
             Abs[yf]}], PlotRange -> All, PlotStyle -> {Red, Thickness[0.01]}], BaseStyle
             -> {FontFamily -> "Times New Roman", 15}, LabelStyle -> {FontFamily 
            -> "Times New Roman"}];
        Legended[p, Placed[LineLegend[{Blue, Red}, {Style["Input Signal",
             FontFamily -> "Times New Roman", 15], Style["Output Signal", FontFamily
             -> "Times New Roman", 15]}], {0.2, 0.8}]]
    ];


GetEfficiency[func_, n_, dt_, \[Omega]_, t_] :=
    Module[{inputAmp = InputSigAmp[\[Omega], n, dt]},
        Table[Max[Abs[FFTSample[func, n, dt, tau]]]/inputAmp, {tau, t}]
    ];


Iterative\[CapitalXi][Ad_, Ap_, Am_, N_, \[Omega]_, \[Omega]m_] :=
    Module[{\[CapitalXi]p, \[CapitalXi]m, iden},
        iden = IdentityMatrix[Dimensions[Ad, 1][[1]]]; \[CapitalXi]p = Ap . Inverse[
            I * (-\[Omega] - 2 * N * \[Omega]m) * iden - Ad] . Am; \[CapitalXi]m = Am . Inverse[I * (-\[Omega] + 
            2 * N * \[Omega]m) * iden - Ad] . Ap; Do[\[CapitalXi]p = Ap . Inverse[I * (-\[Omega] - 2 * N *
             \[Omega]m) * iden - Ad - \[CapitalXi]p] . Am; \[CapitalXi]m = Am . Inverse[I * (-\[Omega] + 2 * N * \[Omega]m) 
            * iden - Ad - \[CapitalXi]m] . Ap, {i, N - 1, 1, -1}]; {Simplify[\[CapitalXi]p], Simplify[\[CapitalXi]m
            ]}
    ];


Logspace[a_, b_, n_] := 10.0^Range[a, b, (b - a)/(n - 1)];


End[];


EndPackage[];
