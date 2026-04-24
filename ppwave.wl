(* ::Package:: *)

Needs["StringCode`"];

InitStringCode[<|"theory" -> "TypeII", "CFT" -> "Lightcone", "conventions" -> "TypeII-Lightcone", "bracket" -> "Flat"|>];


canonicalizeDummies[expr_] := Module[{terms, canonicalize},
  canonicalize[term_] := Module[{indices, rules},
    (* Find all module-generated indices *)
    indices = DeleteDuplicates[
      Cases[term, s_Symbol /; StringMatchQ[SymbolName[s], __ ~~ "$" ~~ DigitCharacter..], Infinity]
    ];
    (* Replace with canonical names in order of appearance *)
    rules = Thread[indices -> Take[{\[Mu], \[Nu], \[Rho], \[Sigma], \[Tau], \[Lambda]}, Length[indices]]];
    term /. rules
  ];
  
  (* Apply to each term in the sum *)
  If[Head[expr] === Plus,
    Total[canonicalize /@ (List @@ expr)],
    canonicalize[expr]
  ]
]


ppSol2[z_,zbar_] := R[ProfileX[h[p,p], {}, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][p,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[p,0,zbar]];

ppH0[z_,zbar_] := R[c[0,z],ct[0,zbar],exp\[Phi]f[-1,z],\[Psi][m,0,z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]]+R[c[0,z],ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],exp\[Phi]tf[-1,zbar],\[Psi]t[m,0,zbar]];

(* Full vacuum state: phi^(0) = c ct e^{ip_- X^-} (alpha_{--} e^{-phi} psi^- e^{-phi~} psi~^- + alpha_{ij} e^{-phi} psi^i e^{-phi~} psi~^j + alpha_{-i} e^{-phi} psi^- e^{-phi~} psi~^i + alpha_{-i} e^{-phi} psi^i e^{-phi~} psi~^-) *)
trZJ[z_, zbar_] := \[Alpha]mm R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][m,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[m,0,zbar]] + \[Alpha]ij R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][i,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[j,0,zbar]] + \[Alpha]mi R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][m,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[i,0,zbar]] + \[Alpha]mi R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][i,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[m,0,zbar]];

(*Splitting trZJ into components to track down contributions*)

trZJmm[z_ ,zbar_ ] := \[Alpha]mm R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][m,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[m,0,zbar]];

trZJij[z_, zbar_] := \[Alpha]ij R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][i,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[j,0,zbar]];

trZJmi[z_, zbar_] := \[Alpha]mi R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][m,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[i,0,zbar]] + \[Alpha]mi R[expX[pM, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][i,0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[m,0,zbar]];

twoBracketReplRule = {Private`z[2,1][{}] :> z, Private`z[2,2][{}] :> -z, Private`q[2,1][{}]:> Private`r0,Private`q[2,2][{}] :> Private`r0, Private`zbar[2,1][{}] :> z, Private`zbar[2,2][{}] :> -z, Private`qbar[2,1][{}]:> Private`r0, Private`qbar[2,2][{}] :> Private`r0};



(*State is annihilated by zeroth-order Hamiltonian. This is a feature of the only non-zero momentum component being in the minus direction.*)

ZeroH = (BracketProjected[ppH0[z,zbar], trZJ[-z,-zbar],0,0]//Private`CollapseB0m//Expand//ContractTransverseDelta//Expand)//.{pM[idx_]:>0 /; idx=!=p}//Simplify



(*Hamiltonian does get corrected at second order. Consistent with non-truncated expansion of supersymmetry generators.*)

sourceHam2 = (BracketProjected[ppSol2[z,zbar], ppH0[-z, -zbar], 0, 0]//Private`CollapseB0m//Expand//ContractTransverseDelta//FullSimplify)//canonicalizeDummies;
sourceHam2Simp = sourceHam2 //. {\[Rho] :> \[Mu], \[Sigma] :> \[Nu]}//FullSimplify;
sourceHam2Simp//.twoBracketReplRule//Simplify


(*Second order correction to tr(Z^J)ij*)

source2ijC = BracketProjected[ppSol2[z,zbar], trZJij[-z,-zbar],0,0]//Expand//ContractTransverseDelta//Private`CollapseB0m;

source2ijF = (source2ijC)//.{dot[pM, der[h[p,p]]] :> 0}//FullSimplify



(*Second order correction to tr(Z^J)mm*)

source2mmC = BracketProjected[ppSol2[z,zbar], trZJmm[-z,-zbar],0,0]//Expand//ContractTransverseDelta//Private`CollapseB0m;

source2mmSimplified = (source2mmC // Expand // canonicalizeDummies) // FullSimplify;

source2mmF = (source2mmSimplified)//.{dot[pM, der[h[p,p]]] :> 0}//.twoBracketReplRule//Simplify


(*Second order correction to tr(Z^J)mi*)

source2miC = BracketProjected[ppSol2[z,zbar], trZJmi[-z,-zbar],0,0]//Expand//ContractTransverseDelta//Private`CollapseB0m;

source2miSimplified = source2miC // Expand // canonicalizeDummies // FullSimplify;

source2miF = (source2miSimplified)//.{dot[pM, der[h[p,p]]] :> 0}//.twoBracketReplRule//FullSimplify



(*Sum of 2nd order sources*)

totalSource = (source2ijF + source2mmF +source2miF)//FullSimplify



(* Supersymmetry generator eq 2.4 with + sign:
   \[Lambda]^(0)+ = \[CurlyEpsilon]_\[Alpha] c c\:0303 (e^{-1/2 \[CurlyPhi]} S^\[Alpha] e^{-2\[CurlyPhi]\:0303} \[PartialD]\:0303\[Xi]\:0303 + e^{-2\[CurlyPhi]} \[PartialD]\[Xi] e^{-1/2 \[CurlyPhi]\:0303} S\:0303^\[Alpha])
   where \[CurlyEpsilon]_\[Alpha] is a constant spinor (coefficient) *)
\[Lambda][\[Alpha]_, z_, zbar_]:=R[c[0, z], ct[0, zbar], exp\[Phi]f[-1/2, z], S[{\[Alpha], "chiral"}, -1/2, {}, 0, z], exp\[Phi]tb[-2, zbar], \[Xi]t[1, zbar]];




(*Tests*)
OPEProjectedHolo[0][R[ProfileX[F,{},z,zbar],c[0,z],exp\[Phi]f[-1,z],\[Psi][\[Mu],0,z]],R[c[0,-z],exp\[Phi]f[-1,-z],\[Psi][\[Nu],0,-z]]]//Simplify
