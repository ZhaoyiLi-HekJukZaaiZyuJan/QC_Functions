(* ::Package:: *)

(*Version 06/20/2024*)


BeginPackage["QCFunctions`"];


TPM::usage="Input:
	sequence of matrices, e.g. TPM[X,Y,Z,i,H,S,CZ]"
T2M::usage="Input:
	2dim'l tensor"
TP::usage="Same as TensorProduct"
M2T::usage="Input:
	even dim matrix"
M::usage="Input:
	nn_ number of regs
	I_ ops to apply"
Stab::usage="generate stabilizer op from recipe
	Input:
	recipe (lists)"
M2TArbitrary::usage="Input: 1.matrix\[IndentingNewLine]	                        2. list of tensor shape, say for a matrix of dim 8 and list={2,4}, will output tensor of rank 6 with d/8, d/8, 2, 2, 4, 4 dim resp."
Mtranspose::usage="Input: matrix, tensor index i, tensor indexj"
TensorRepMatrix::usage="Input:
	n matrix"
Mtr::usage="Input:
	qubit Matrix, # which is to be contracted"
tr::usage="Input:
	tensor 1. list of indices # which is to be contracted, the list is automatically ordered reversely
	eg: tr[tensor,{1,4,3}]
			2. single number"
tensorTrace::usage="Input:
	qubit Tensor, # which is to be contracted"
Exchange::usage="Input:
	tensor, perm list {\!\(\*SubscriptBox[\(n\), \(1\)]\),...,\!\(\*SubscriptBox[\(n\), \(N\)]\)} s.t. k-th becomes \!\(\*SubscriptBox[\(n\), \(k\)]\)-th level in the result"


(* ::Subsection:: *)
(*Common Gate Definitions*)


X=PauliMatrix[1];
Y=PauliMatrix[2];
Z=PauliMatrix[3];
(*Hamahard*) H=1/Sqrt[2]{{1,1},{1,-1}};
(*Arbitrary U*) U={{U11,U12},{U21,U22}};
(*Arbitrary U*) V={{V11,V12},{V21,V22}};
S={{1,0},{0,I}};
T={{1,0},{0,Sqrt[I]}};
id = IdentityMatrix[2];
(*Controlled-Z*) CZ=DiagonalMatrix[{1,1,1,-1}];
(*Controlled-U*)CU =TPM[{{1,0},{0,0}},id]+TPM[{{0,0},{0,1}},U];
(*Controlled-X*) CX=TPM[IdentityMatrix[2],H] . CZ . TPM[IdentityMatrix[2],H];
(*SWAP*) SWAP=CX . Mtranspose[CX,1,2] . CX;
(*Troffoli*)(CCX=TPM[{{1,0},{0,0}},id,id]+TPM[{{0,0},{0,1}},CX])//MatrixForm;


(*Controlled-SWAP*)CSWAP =TPM[{{1,0},{0,0}},id,id]+TPM[{{0,0},{0,1}},SWAP];


(*Rotation*)
Rx[t_]:=MatrixExp[I X t/2];
Ry[t_]:=MatrixExp[I Y t/2];
Rz[t_]:=MatrixExp[I Z t/2];


getVec[c_,n_]:=ReplacePart[Table[0,2^n],ToExpression[ToExpression["2^^"<>ToString[c]]]+1->1]


(*Random D.M. Generation*)


random\[Rho][d_]:=Module[{uframe=RandomVariate[GaussianUnitaryMatrixDistribution[d]],mtest},(mtest=uframe . RandomVariate[WishartMatrixDistribution[5,IdentityMatrix[d]]] . uframe);mtest/Tr[mtest]]


(* ::Subsection:: *)
(*Density Matrix Operations for Qubits*)


(*Gate on qubit n:
	[Input] matrix:matrix, bi-unitary operation, pos:int, where to act, n:int, # of physical qubits*)
applytwo[matrix_,pos_,n_]:=TPM@@(ReplacePart[Table[0,n],{pos->matrix,j_/;j!=pos->TPM[imat,imat]}])


(*Pure state*)

pure[vec_]:=Outer[Times,vec,Conjugate[vec]]


Begin["`Private`"];


Mtranspose[matrix_,i_,j_]:=T2M@Transpose[Transpose[M2T[matrix],2i-1<->2j-1],2i<->2j](*acting on matricies, exchanging i with j*)


(* ::Subsection:: *)
(*Density  Matrix  Operations  for  Qutriits*)


(*Tensor To Matrix*)
(*Input:
	two matrices
	*)
SetAttributes[TM, {Flat, OneIdentity}];(*has to come first somehow than the next line*)
TM[a_, b_] := Flatten[TensorProduct[a, b], {{1, 3}, {2, 4}}]

(*Input:
	sequence of matrices, e.g. TPM[X,Y,Z,i,H,S,CZ]*)
TPM[a__] := TM[a] /.(*Correction*)TM[x_] :> x (*input qubit operators*)
T2M[tensor_] := Block[{n = ArrayDepth[tensor]/2}, Flatten[tensor, {2 Range[n] - 1, 2 Range[n]}]](*functions the same as TM, input tensor; Note, use Arraydepth instead of Depth*)
(*Generate representation matrix in computational basis*)TensorRepMatrix[n_,Matrix_]:=Nest[TPM[Matrix,#]&,Matrix,n-1]
TP[a___]:=TensorProduct[a]


(*Transversal gates*)
(*[Input]
	gate: matrix, number: int, # of physical qubits*)
transversal[gate_,number_]:=TPM@@Table[gate,number]


(*Matrix To Tensor*)
M2T[matrix_]:=Nest[Partition[#,{2,2}]&,matrix,Log[2,Length[matrix]]-1]


(*Partition  matrix into Tensors of rank given by a list
Input, 1.matrix
	    2. list of tensor shape, say for a matrix of dim 8 and list={2,4}, will output tensor of rank 6 with d/8, d/8, 2, 2, 4, 4 dim resp. 
*)
M2TArbitrary[matrix_,list_]:=Fold[Partition[#1,{#2,#2}]&,matrix,Reverse[list]]


(*Pauli Group Recipe*)
M[nn_,I_]:=Normal@SparseArray[{i_,j_}/;(i==j||Mod[i,nn]+1==j)->I,{nn,nn}]
(*Pauli Group Element*)
(*nn: length of group, I: pauli number*)
Stab[recipe_]:=Plus@@TPM@@@PauliMatrix/@recipe
Stab[nn_,pos_,I_]:=1/2TPM@@PauliMatrix/@ReplacePart[Table[0,nn],pos->I]


(* ::Input:: *)
(*(*Matrix Transposition and Exchange*)*)


(*new version*)
vectorize[tensor_]:=Flatten[tensor,Table[{i,i+1},{i,1,ArrayDepth[tensor],2}]]
devectorize[vec_(*1xd^2 vector*)]:=Module[{dlist=Sqrt[Dimensions[vec]]},ArrayReshape[vec,Flatten@Transpose[{dlist,dlist}]]]
Exchange[tensor_,permlist_]:=devectorize[TensorTranspose[vectorize[tensor],permlist]]
Mtr[M_,n_]:=T2M[TensorContract[M2T[M],{{2n-1,2n}}]]
tr1[tensor_,n_]:=TensorContract[tensor,{2n-1,2n}];
tr[tensor_,n_]:=If[Head[n]===List,Fold[tr1,tensor,Sort[n,Greater]],tr1[tensor,n]]


End[];


EndPackage[];
