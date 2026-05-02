Needs["StringCode`"];

InitStringCode[<| "theory" -> "TypeII", "CFT" -> "FlatSpace", "conventions" -> "TypeII-Ashoke", "bracket" -> "Flat"|>];

(*Setup*)

twoBracketReplRule = {Private`z[2,1][{}] :> z, Private`z[2,2][{}] :> -z, Private`q[2,1][{}]:> Private`r0,Private`q[2,2][{}] :> Private`r0, Private`zbar[2,1][{}] :> z, Private`zbar[2,2][{}] :> -z, Private`qbar[2,1][{}]:> Private`r0, Private`qbar[2,2][{}] :> Private`r0};


(*Defining general string fields*)

stringFieldRR[F_,\[Alpha]_,\[Beta]_, z_, zbar_] := R[ProfileX[F, {}, z, zbar],c[0,z], ct[0,zbar], S[{\[Alpha], "chiral"}, -1/2, {}, 0, z], St[{\[Beta], "chiral"}, -1/2, {}, 0, zbar]];

stringFieldGrav[h_,\[Mu]_, \[Nu]_, z_, zbar_] := R[ProfileX[h[\[Mu],\[Nu]], {}, z, zbar], c[0,z], ct[0,zbar], exp\[Phi]f[-1,z], \[Psi][\[Mu],0,z], exp\[Phi]tf[-1,zbar], \[Psi]t[\[Nu],0,zbar]];

stringFieldGD[Dil_ , z_, zbar_] := R[ProfileX[Dil,{},z,zbar],c[0,z], ct[0,zbar], \[Eta][0,z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]] - R[ProfileX[D,{},z,zbar],c[0,z], ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],\[Eta]t[0,zbar]];

symRNS[\[Lambda]_ ,\[Alpha]_, z_, zbar_] := R[ProfileX[\[Lambda][\[Alpha]],{},z,zbar],c[0,z],ct[0,zbar],S[{\[Alpha], "chiral"}, -1/2, {}, 0, z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]];

symNSR[\[Lambda]_,\[Alpha]_,z_,zbar_] := R[ProfileX[\[Lambda][\[Alpha]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],St[{\[Alpha], "chiral"}, -1/2, {}, 0, zbar]];

symNSNS[V_,\[Mu]_, z_, zbar_] := R[ProfileX[V[\[Mu]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]f[-1,z],\[Psi][\[Mu],0,z],exp\[Phi]tb[-2,zbar],\[Xi]t[1,zbar]]+R[ProfileX[V[\[Mu]],{},z,zbar],c[0,z],ct[0,zbar],exp\[Phi]b[-2,z],\[Xi][1,z],exp\[Phi]tf[-1,zbar],\[Psi]t[\[Mu],0,zbar]];



(*Brackets*)
(BracketProjected[stringFieldRR[F1,\[Alpha]1,\[Beta]1,z1,z1bar],stringFieldRR[F2,\[Alpha]2,\[Beta]2,z2,z2bar],0,0]//Private`CollapseB0m)//.{_der:>0, dot[0,0]:>0}//.twoBracketReplRule//Simplify

(BracketProjected[stringFieldRR[F1,\[Alpha]1,\[Beta]1,z1,z1bar],stringFieldRR[F2,\[Alpha]2,\[Beta]2,z2,z2bar],stringFieldRR[F3,\[Alpha]3,\[Beta]3,z3,z3bar],0,0])//Simplify

result = (BracketProjected[stringFieldRR[F1,\[Alpha]1,\[Beta]1,z1,z1bar],stringFieldRR[F2,\[Alpha]2,\[Beta]2,z2,z2bar],stringFieldGrav[Vac,\[Mu],\[Nu],z3,z3bar],0,0])//Private`CollapseB0m//.{der[F1]:>0, der[F2]:>0, dot[0,_]:>0}//Simplify

(* Option 1: Export as InputForm (can be re-imported with Get) *)
Put[result, "~/Desktop/OPEresult.m"]

(BracketProjected[stringFieldRR[F1,\[Alpha]1,\[Beta]1,z1,z1bar],stringFieldRR[F2,\[Alpha]2,\[Beta]2,z2,z2bar],symNSNS[V,\[Mu],z3,z3bar],0,0])

OPEProjected[0,0][stringFieldRR[F1,\[Alpha]1,\[Beta]1,z1,z1bar],stringFieldRR[F2,\[Alpha]2,\[Beta]2,z2,z2bar],symNSNS[V,\[Mu],z3,z3bar]]

test = OPEProjected[0,0][stringFieldRR[F1,\[Alpha]1,\[Beta]1,z1,z1bar],stringFieldRR[F2,\[Alpha]2,\[Beta]2,z2,z2bar]]//.{der[F1]:>0, der[F2]:>0, dot[0,_]:>0}//Simplify

OPEProjected[0,0][test, stringFieldGrav[Vac,\[Mu],\[Nu],z3,z3bar]]//.{der[F1]:>0, der[F2]:>0, dot[0,_]:>0}//Simplify