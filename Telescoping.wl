(* ::Package:: *)

(* ::Section:: *)
(*Load HarmonicSums*)


SetDirectory[NotebookDirectory[]];
<<HarmonicSums.m


(* ::Section:: *)
(*Misc*)


(* ::Subsubsection:: *)
(*Homemade sum*)


Clear[sum]

sum[0, index_] := 0

sum[Power[0,_] * (expr_:1), index_] := 0


Clear[denomShift]

(* Shift denominators from \[Mu]+\[Alpha] to \[Mu] *)

denomShift = sum[(x_:1) Power[\[Mu]_ + \[Alpha]_, p_], {\[Mu]_,min_,max_}] /; NumericQ[\[Alpha]] \[And] p<0 :> 

		sum[(x /. \[Mu] -> \[Mu] - \[Alpha]) Power[\[Mu],p], {\[Mu], min + \[Alpha], max + \[Alpha]}];


(* ::Subsubsection:: *)
(*Simplifications*)


Clear[expSimplify]

(* Simplify exponents *)

expSimplify = {

	x_^((A_:1) * \[Mu][i_] + (a_:0)) * y_^((B_:1) * \[Mu][i_] + (b_:0)) :> 
		(x^A * y^B)^\[Mu][i] * x^a * y^b,
		
	x_^((A_:1) * \[Mu][i_] - (a_:0)) * y_^((B_:1) * \[Mu][i_] - (b_:0)) :> 
		(x^A * y^B)^\[Mu][i] * (1/x)^a * (1/y)^b,
		
	x_^(k + (a_:0)) y_^(k + (b_:0)) :> 
		(x y)^k x^a y^b,
		
	sum[x_^(y_ + z_) * (w_:1), list_] /; FreeQ[{y}, First@list] \[Or] NumericQ[y] :> 
		x^y * sum[x^z * w, list],
	
	sum[x_^(y_ - z_) * (w_:1), list_] /; FreeQ[{y}, First@list] \[Or] NumericQ[y] :> 
		x^y * sum[x^-z * w, list]
};


Clear[ratSimplify]

(* Simplify rational terms *)

ratSimplify = expr_ :> Module[{rat,ratNew},
	rat = Select[expr, FreeQ[#,S|Z]&];
	ratNew = rat // Simplify // Expand;
	expr /. rat -> ratNew
];


Clear[sumSimplify]

(* Linear sum + put constants outside of summation + simplify exponents *)

sumSimplify = sum[expr_,index_] :> Module[{temp},
	temp = ExpandAll[sum[expr,index], \!\(\*
TagBox[
StyleBox[
RowBox[{"Power", "[", 
RowBox[{
RowBox[{"Plus", "[", 
RowBox[{"__", ",", 
RowBox[{"\\[Mu]", "[", "_", "]"}]}], "]"}], ",", "_"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\) ]; 
	temp = temp //. sum[x_ + y_, list_] :> sum[x, list] + sum[y, list];
	temp = temp //. sum[x_ * y_, list_] /; FreeQ[{x}, First@list] \[Or] NumericQ[x] :> x * sum[y, list];
	temp /. expSimplify
];


Clear[Sync]

(* Synchronize denominator of x^n/(n+c) with upper bound of Z-sum *)

Sync = sum[expr_,index_] :> Module[{temp},
	temp = sum[expr,index] //. sumSimplify;
	temp = temp /. pf;
	temp = temp /. denomShift // LinearExpand
];


(* ::Subsubsection:: *)
(*Transforms*)


Clear[ZToLi]

(* Convert Z-sums to MPLs. Note that Li cannot be numerically calculated. *)

ZToLi = {

	Z[1, {x_}, \[Infinity]] :>
		-Log[1-x],

	Z[m__, {x__}, \[Infinity]] /; (Length @ {m} != 1) \[Or] (First @ {m} != 1) :> 
		If[Length @ {m} == 1, PolyLog[m,x], Li[Sequence @@ (Reverse @ {m}), Reverse @ {x}]]
		
};


Clear[ToCS]

(* Convert nested S-sums with denominator shifts to cyclotomic S-sums *)

ToCS[1] = S[m__,{x__},\[Mu][i_] + N_] :> 
	S[m,{x},N] + First[{x}]^N sum[First[{x}]^\[Mu][i+1]/(\[Mu][i+1]+N)^First[{m}] S[Sequence @@ Drop[{m},1], Drop[{x},1], \[Mu][i+1] + N] /. S[{},n_] :> 1, {\[Mu][i+1],1,\[Mu][i]}];
	
ToCS[2] = {

	sum[x_^\[Mu]_ Power[\[Mu]_+k_,p_], {\[Mu]_,1,N_}] :> 
		cs[{{1,k,-p}},{x},N],
	
	sum[x_^\[Mu]_ Power[\[Mu]_+(k_:0),p_] cs[m__, y_?ListQ, \[Mu]_], {\[Mu]_,1,N_}] :>
		cs[Join[{{1,k,-p}},m], Join[{x},y], N]
};


(* ::Subsubsection:: *)
(*Partial fraction*)


Clear[pf]

(* Partial fraction w.r.t summation index *)

pf = sum[x_, y_] :> sum[Apart[x, First@y], y];


Clear[pfC]

(* Partial fraction coefficients for 1/n^p * 1/(n+alpha)^q *)

pfC[ii_,p_,index_] := Binomial[p+ii-1,p-1]/\[Mu][index]^(p+ii)


Clear[pfSum1,pfSum2]

(* Partial fraction terms for 1/n^p * 1/(n+alpha)^q *)

pfSum1[p_,q_] [index_?NumberQ] [expr_] := Sum[pfC[ii,q,index] (-1)^ii * expr, {ii,0,p-1}]

pfSum2[p_,q_] [index_?NumberQ] [expr_] := Sum[pfC[ii,p,index] (-1)^p * expr, {ii,0,q-1}] 


(* ::Section:: *)
(*Telescoping.*)


(* ::Subsubsection:: *)
(*Misc*)


Clear[yList,zList]

(* Continuous variables for Z_m(n-1|y) * Z_r(n+\[Alpha]-1|z) *)

yList[m_] := Table[y[i], {i,1,Length@m}]
zList[r_] := Table[z[i], {i,1,Length@r}]


Clear[first,drop]

(* These functions deal with m' and r' (see paper for primed notation) when Length[m] and Length[r] are already zero. *)

first[list_] := Which[
	Length[list] == 0, 
		0,
	Length[list] > 0,
		First[list]
]

drop[list_] := Which[
	Length[list] == 0, 
		0,
	Length[list] > 0,
		Drop[list,1]
]


Clear[s]

(* Set {\cal S} to zero when m',r' come from zero-length weight vectors m,r. The 0's in {m,r} will appear due to 'first' & 'drop' defined above. *)

s[m_,r_] [x_,y_,z_] [p_,q_] [N_] [\[Mu][index_]] := 0 /; !FreeQ[{m,r},0]


Clear[xMinus]

(* Operator with the property that xMinus[n^p x^n] = n^{p+1} x^n. See eq. (2.23). *)

xMinus[Ssum_] := x * DifferentiateSSum[Ssum, x] // Expand


(* ::Subsubsection:: *)
(*Special case sums*)


Clear[s1]

(* s[\[Alpha]=1] *)

s1[m_, r_] [x_, y_, z_] [p_?NumberQ, q_?NumberQ] [N_] := Module[{temp},

	temp = sum[x^n/(n^p (n+1)^q) ZZ[Sequence@@m, y, n-1] * ZZ[Sequence@@r, z, n] /. ZZ[{},_] :> 1, {n,1,N}] /. ZZ -> Z // LinearExpand;
	
	(temp //. Sync // ZToS) /. sum -> HarmonicSumsSum // TransformToSSums // SToZ // Expand
	
]


Clear[V]

(* Boundary terms from eq. (3.9). This is not used in the algorithm but just for testing how these terms look for various input data. *)

V[m_?ListQ, r_?ListQ] [p_?NumberQ, q_?NumberQ] [N_] /; q>=0 \[And] p>=0 := Module[{y,z},
	
	y = yList[m];
	z = zList[r];
	
	pfSum1[p,q][0][ s1[m,r][x,y,z][p-ii,0][N] ] +
	
	pfSum2[p,q][0][ 
	
		x * s1[m,r][x,y,z][0,q-ii][N] -
		 
		KroneckerDelta[Length@m,0] * (Z[q-ii,Sequence@@r, Join[{x},z], \[Alpha]] - KroneckerDelta[Length@r,0] * x) + 
		
		If[N === Infinity, 0, (Z[Sequence@@m, y, N] /. Z[{},_] :> 1) * (Z[q-ii,Sequence@@r, Join[{x},z], N+\[Alpha]] - Z[q-ii,Sequence@@r, Join[{x},z], N+1])]
		
	] * (1/x)^\[Alpha]  /. \[Mu][0] -> \[Alpha] //. expSimplify // Expand

]


(* ::Subsubsection:: *)
(*Recursive algorithm*)


Clear[BaseCase]

(* When m,r have zero length. See eq. (3.13). *)

BaseCase = s[{},{}] [x_,{},{}] [p_,q_] [N_] [\[Mu][index_]] :>

	pfSum1[p,q][index][S[p-ii,{x},N]] + 
	
	pfSum2[p,q][index][S[q-ii,{x},N+\[Mu]@index] - S[q-ii,{x},\[Mu]@index]] * (1/x)^\[Mu][index]; 


Clear[Recursion]

(* S = S^(p,0) + S^(0,q). See eq. (A.1). *)

Recursion = s[m_?ListQ, r_?ListQ] [x_,y_?ListQ, z_?ListQ] [p_?NumberQ, q_?NumberQ] [N_] [\[Mu][index_?NumberQ]] /; TrueQ[Length[m]>0 \[Or] Length[r]>0] :> 

	pfSum1[p,q][index][sp0[m,r] [x,y,z] [p-ii] [N] [\[Mu]@index]] + 
	
	pfSum2[p,q][index][s0q[m,r] [x,y,z] [q-ii] [N] [\[Mu]@index]];


Clear[sp0]

(* S^(p,0). See eq. (A.3). *)

sp0[m_,r_] [x_,y_,z_] [p_] [N_] [\[Mu]@index_] := sp0[m,r] [x,y,z] [p] [N] [\[Mu]@index] =
	If[Length@r == 0,
		ZZ[p,Sequence@@m, Join[{x},y], N], 
		
		sum[(first@z)^\[Mu][index+1] * s[m, drop@r] [x*first@z, y, drop@z] [p, first@r] [N] [\[Mu][index+1]], {\[Mu][index+1], 1, \[Mu]@index}] -
		
		(first@z)^\[Mu]@index * s[m, drop@r] [x*first@z, y, drop@z] [p, first@r] [N] [\[Mu]@index] +
		
		s1[m,r] [x,y,z] [p,0] [N]
]


Clear[s0q]

(* S^(0,q). See eq. (A.8). *)

s0q[m_,r_] [x_,y_,z_] [q_] [N_] [\[Mu]@index_] := s0q[m,r] [x,y,z] [q] [N] [\[Mu][index]] =
	If[Length@m == 0,
		(1/x)^\[Mu]@index * (ZZ[q,Sequence@@r, Join[{x},z], N+\[Mu]@index] - ZZ[q,Sequence@@r, Join[{x},z], \[Mu]@index]),
		
		- (1/x)^\[Mu]@index * sum[x^\[Mu][index+1] s[drop@m, r] [x*first@y, drop@y, z] [first@m, q] [N] [\[Mu][index+1]], {\[Mu][index+1], 1, \[Mu]@index}]
		
		+ (1/x)^(\[Mu]@index-1) s1[drop@m, r] [x*first@y, drop@y, z] [first@m, q] [N]
		
		+ (1/x)^(\[Mu]@index-1) * s1[m,r] [x,y,z] [0,q] [N]
		
		+ (1/x)^\[Mu]@index * If[N === \[Infinity], 0, ZZ[Sequence@@m, y, N] * (ZZ[q,Sequence@@r, Join[{x},z], N+\[Mu]@index] - ZZ[q,Sequence@@r, Join[{x},z], N+1])]
]


Clear[Resum]

(* For N=\[Infinity] where cyclotomic sums do not appear. *)

Resum[s_] := Module[{temp},	
	temp = s //. Recursion /. BaseCase /. ZZ -> Z // ZToS;
	temp /. sum -> HarmonicSumsSum // TransformToSSums // Expand	
]


Clear[ResumCS]

(* For symbolic N (we use N=k) where cyclotomic sums do appear *)

ResumCS[s_] := Module[{temp},
	temp = s //. Recursion /. BaseCase /. ZZ -> Z // ZToS;
	temp = temp //. ToCS[1] //. Flatten@{sumSimplify, pf} // Expand;
	temp = temp //. ToCS[2] /. sum -> HarmonicSumsSum // TransformToSSums // Expand;
	temp /. cs -> CS // SToZ // Expand
]


Clear[ResumMaster]

(* Combining resum functions for special cases and include error messages. *)

ResumMaster[s[m_,r_] [x_,y_,z_] [p_,q_] [N_] [\[Mu]@index_]] := Module[{expr},
	
	expr = s[m,r] [x,y,z] [p,q] [N] [\[Mu]@index];
	
	Which[
	
		N === Infinity,
			If[p<0 \[Or] (p == 0 \[And] q == 0), 
				NestTemp[xMinusTemp, s[m,r] [x,y,z] [1,q] [N] [\[Mu]@index] // Resum, Abs@p+1] /. {NestTemp -> Nest, xMinusTemp -> xMinus} /. ratSimplify, 
				expr // Resum
			] // SToZ // Expand,
		
		True,
			If[p<0 \[Or] (p == 0 \[And] q == 0), 
				"We have not implemented the x^+ operator for cyclotomic sums which is required for p<1.", 
				expr // ResumCS
			]
			
		] //. expSimplify
]


Clear[CalS]

(* Resummed CalS. See eq. (3.7). *)

CalS[m_?ListQ,r_?ListQ] [p_?NumberQ,q_?NumberQ] [N_] /; q>=0 && AllTrue[Flatten[{m,r}], Positive] := 

	ResumMaster[s[m,r] [x, yList[m], zList[r]] [p,q] [N] [\[Mu]@0]] /. \[Mu][0] -> \[Alpha]
