(* ::Package:: *)

(*Version 06/30/2024*)

(*run this to change everything to default format*)
SetOptions[EvaluationNotebook[], StyleDefinitions -> "Default.nb"]


BeginPackage["YoungFunctions`"];


Needs["Combinatorica`"]


(* ::Title:: *)
(*Young.nb\:5705\:6570*)


(*\:8f14\:52a9\:5705\:6570*)

Sgn[perm_]:=Apply[Times,(-1)^(Length/@First[perm]-1)]
Trans[x_]:=Module[{
l=Max[Length/@x]},
Transpose[#~Join~Table[0,l-Length[#]]&/@x]/. 0->Nothing]

(*cut: remove the biggest element
	input: list*)
cut[x_]:=x/.{Max[x]->Nothing}//.{{}->Nothing};
series[x_]:=NestList[cut,x,Max[x]];

(*\:5e7c\:5705\:6570*)
FindPerForList[list_](*generate all elems of a permuattion group*):=Module[{rules=Thread[Rule[Range@Length@list,list]]},FindPermutation[list,#]&/@Permutations[list]/.rules]
(*Generate all permutations for rows/columns of a young tableaux, entered as a list of listes (rows)*)
AllPer[YT_]:=Flatten[Outer[PermutationProduct,Sequence@@Map[FindPerForList,YT]]]
P[YT_]:=Plus@@AllPer[YT]
Q[YT_]:=Plus@@(Sgn[#]#&/@AllPer[Trans@YT])
(*corresponding to Unormalized Young Projector E on notes since E is built-in defined*)
e[YT_]:=P[YT]\[Diamond]Q[YT]

(*toYT[]
	input form of Young Diagram {lrow,lrow,lrow...}
	 output all possibly Young Diagrams
	*)
toYT[YD_]:=GroupBy[Tableaux[Total[YD]],Length/@#&][YD]
(*toD[]
	get young diagram from a specific tableau
	*)
toYD[YT_]:=Length/@YT
\[Theta][YD_]:=Total[YD]!/Length[toYT[YD]]
y[YT_](*normalized idempotent*):=e[YT]/\[Theta][toYD[YT]]

(*Is Indemp \:9a8c\:8bc1\:672c\:5e42*)
IsIdemp[ele_]:=Simplify[ele\[Diamond]ele==ele]


(* ::Chapter:: *)
(*\:534a\:6b63\:5219\:6bcd\:5355\:4f4d (\:96a0)*)


(*BasisE[YT:List[List], n: Int] n take 1 to Total[YD], note this goes backwards
	gerate the list of basis by diminution of YT, i.e. e^(1), e^(2), e^(3), etc*)
BasisE[YT_,n_:1]:=Block[{i=0,S=series[YT],e0=System`Cycles[{{}}],nexte},nexte[laste_]:=(++i;1/\[Theta][toYD[S[[-i-1]]]]laste\[Diamond] e[S[[-i-1]]]\[Diamond]laste);Nest[nexte,e0,Length[S]-n]]

(*Find the permutation Subscript[\[Sigma], rs] that links two YT*)Relate[YT1_,YT2_]:=FindPermutation[Flatten[YT2],Flatten[YT1]]/.Thread[Rule[Range[Total[toYD[YT2]]],Flatten[YT2]]]
MixedBasis[YT1_,YT2_]:=1/\[Theta][toYD[YT1]] BasisE[YT1]\[Diamond]P[YT1]\[Diamond]Relate[YT1,YT2]\[Diamond]Q[YT2]\[Diamond]BasisE[YT2]

(*Get all Subscript[e, rs] basis at once*)
basisEAs[YD_]:=AssociationThread[toYT[YD],BasisE[#]&/@toYT[YD]];

(*\:751f\:6210\:57fa\:77e9\:9635*)
GetBasis[YD_]:=Module[{basisEAs=AssociationThread[toYT[YD],BasisE/@toYT[YD]]},Outer[MixedBasis[#1,#2,basisEAs]&,toYT[YD],toYT[YD],1]]
(*\:751f\:6210\:8868\:793a\:77e9\:9635*)
GetMatrices[YD_]:=With[{basis=GetBasis[YD]},\[Theta][YD]BraKet[System`InversePermutation[#],Transpose@basis]&/@GroupElements[System`SymmetricGroup[Total[YD]]]]
GetMatrices[YD_]:=With[{basis=GetBasis[YD]},\[Theta][YD]BraKet[#\[Diamond]Transpose@basis,System`Cycles[{}]]&/@GroupElements[System`SymmetricGroup[Total[YD]]]]

(*\:5176\:4ed6\:529f\:80fd*)
GetAssociation[1][YD_]:=AssociationThread[GroupElements[System`SymmetricGroup[Total[YD]]],GetMatrices[YD]]
TraditionalFormn[form_]:=form/.{{}}->"()"//TraditionalForm


(* ::Chapter:: *)
(*Matrix Representation*)


matrix[g_](*representation matrix with left multiplication*):=Outer[BraKet,mybasis,g\[Diamond]mybasis]
matrixr[g_](*representation matrix with right multplication*):=Outer[BraKet,mybasis,mybasis\[Diamond]g]


(* ::Title:: *)
(*Weyl.nb\:5705\:6570*)


(* ::Subchapter:: *)
(*Weyl\:56fe \:5705\:6570*)


(*Weyl\:56fe \:5705\:6570
	Input: <YD> \:661c\:555a, <int> \:5b50\:7a7a\:95f4\:7ef4\:5ea6 N
   Output: \:8fd4\:56de\:6240\:6709\:53ef\:43fb\:37a2\:96fe(Weyl)\:76d8\:ff081 indexing\:ff09
*)
ExtendRow[row_,max_,lastrow_](*grow row by 1 slot*):=Module[{min=Piecewise[
{{Last@row,Length@row!=0&&Length[lastrow]<=Length[row]},
{Max[Last@row,lastrow[[Length[row]+1]]+1],Length@row!=0&&Length[lastrow]>Length[row]},
{lastrow[[Length[row]+1]]+1,Length@row==0&&Length[lastrow]>Length[row]},
{1,Length@row==0&&Length[lastrow]<=Length[row]}
}]},Table[Append[row,i],{i,min,max}]]
NextLevel[rows_,max_,lastrow_:{0}]:=Flatten[Map[ExtendRow[#,max,lastrow]&,rows],1]


NewRows[length_,max_,lastrow_](*generate possibility of new rows based on the last row*):=Nest[NextLevel[#,max,lastrow]&,{{}},length]


AddRow[length_,max_,lastrow_](*deprecated:*):=Module[{row=NewRows[length,max,lastrow]},Piecewise[{{{lastrow,#}&/@row,Length[lastrow]!=0},{row,True}}]]

AddRows[length_,max_,lastrows_(*deprecated: list of rows*)]:=Flatten[Map[AddRow[length,max,#]&,lastrows],1]

LastRow[YT_]:=Piecewise[{{YT[[-1]],Length[YT]>0},{{0},True}}](*get last row of YT, otherwise use {0}*)

Grow[length_,max_,YT_](*Start from a YT, grow bigger by one tow*):=
(Append[YT,#])&/@NewRows[length,max,LastRow[YT](*last row*)]

Grows[length_,max_,YTs_(*list of YTs*)]:=Flatten[Map[Grow[length,max,#]&,YTs],1]

WT[YD_,N_]:=Fold[Grows[#2,N,#]&,{{}},YD]


(* ::Subchapter:: *)
(*\:5f35\:91cf \:5705\:6570*)


(*\:751f\:6210\:4ee3\:6570\:7684\:5f20\:91cf\:7a4d*)TensorBases[N_,P_]:=Apply[e,Tuples[Range[N],P],1]
(*S\:37a2\:5143\:7d20\:37a2\:4f5c\:7528*)
InversePermute[x___]:=System`Permute[First[{x}],System`InversePermutation@Last[{x}]]
Acti[unit_,basis_](*inverse permute*):=TensorExpand[basis\[TensorProduct]unit]/.TensorProduct->InversePermute
Act[unit_,basis_]:=TensorExpand[basis\[TensorProduct]unit]/.TensorProduct->System`Permute
(*get basis from tableau*)
Tensor[Weyl_]:=Apply[e,Flatten[Flatten[Weyl,{{2},{1}}](*ragged transpose!!*)]]


repMatrix[unit_]:=Outer[BraKet,TensorBases[2,3],Act[unit,#]&/@TensorBases[2,3]]


repComp[vec_](*components*):= BraKet[vec , #] & /@ TensorBases[2, 3]


(*Generate representation matrix in computational basis*)TensorRepMatrix[n_,Matrix_]:=Nest[TPM[Matrix,#]&,Matrix,n-1]


(* ::Subsection:: *)
(*\:4f8b\:5b50\:ff1a\:597d\:57fa*)


normalize[vector_]:=vector/Sqrt[BraKet[vector,vector]]


fullbasisN2M2(*U,S \:5206\:584a\:57fa*)=(*[2]*)((Act[BasisE[{{1, 2}}], #] & /@ (Tensor[{{1, 2}}, #] & /@ WT[{2}, 2])))~Join~
  (*[1,1]*)( (Act[BasisE[{{1}, {2}}], #] & /@ (Tensor[{{1}, {2}}, #] & /@ WT[{1, 1}, 2])))


(BN2M2(*change of coordinate matrix*)=Outer[BraKet,TensorBases[2,2],normalize/@fullbasisN2M2])


fullbasisN2M3(*U,S \:5206\:584a\:57fa*)=(*[2]*)((Act[BasisE[{{1,2}}],#]&/@(Tensor[{{1, 2}}, #] & /@ WT[{2},3])))~Join~
(*[1,1]*)(Act[BasisE[{{1},{2}}],#]&/@(Tensor[{{1},{2}}, #] & /@ WT[{1,1},3]))


(BN2M3(*change of coordinate matrix*)=Outer[BraKet,TensorBases[3,2],normalize/@fullbasisN2M3])


fullbasisN3M2(*U,S \:5206\:584a\:57fa*)=(*[2,1] 1*)((Act[BasisE[t1],#]&/@(Tensor[t1, #] & /@WT[{2,1},2])))~Join~
(*[2,1] 2*)( (Act[BasisE[t2],#]&/@(Tensor[t2, #] & /@WT[{2,1},2])))~Join~
(*[3]*)(Act[BasisE[{{1,2,3}}],#]&/@(Tensor[{{1,2,3}}, #] & /@WT[{3},2]))~Join~
(*[1,1,1] 1*)(Act[BasisE[{{1},{2},{3}}],#]&/@(Tensor[{{1}, {2},{3}}, #] & /@WT[{1,1,1},2]));


(BN3M2(*change of coordinate matrix*)=Outer[BraKet,TensorBases[2,3],normalize/@fullbasisN3M2])


fullbasisN3M3(*U,S \:5206\:584a\:57fa*)=(*[1,1,1] 1*)(Acti[BasisE[{{1},{2},{3}}],#]&/@(Tensor[{{1},{2},{3}}, #] & /@WT[{1,1,1},3]))~Join~
(*[2,1] 1*)(BlockDiagonalMatrix[{IdentityMatrix[2],{{0,0,1},{0,1,0},{2/3,0,1/3}}(*diagonalization*),IdentityMatrix[3]}] . (Acti[BasisE[t1],#]&/@(Tensor[t1, #] & /@WT[{2,1},3])))~Join~
(*[2,1] 2*)( BlockDiagonalMatrix[{IdentityMatrix[2],{{-1/3,0,2/3}(*double check w GT!*),{0,1,0},{1,0,0}},IdentityMatrix[3]}] . (Acti[BasisE[t2],#]&/@(Tensor[t2, #] & /@WT[{2,1},3])))~Join~
(*[3]*)(Acti[BasisE[{{1,2,3}}],#]&/@(Tensor[{{1,2,3}}, #] & /@WT[{3},3]));(*note that the matrix generated this way is not unitary, since the bases are not orthogonal for the e[1,2,3] components]*)


(BN3M3(*change of coordinate matrix*)=Outer[BraKet,TensorBases[3,3],normalize/@fullbasisN3M3])


(*Generate representation matrix in computational basis*)TensorRepMatrix[n_,Matrix_]:=Nest[TPM[Matrix,#]&,Matrix,n-1]


Begin["`Private`"];


End[];


EndPackage[];
