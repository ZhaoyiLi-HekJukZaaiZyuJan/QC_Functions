(* ::Package:: *)

(*Styledata is defined in "Package.nb"*)


SetOptions[EvaluationNotebook[], StyleDefinitions -> "Default.nb"]


BeginPackage["QCFunctions`"];


(* ::Subsection:: *)
(*Common Qubit Gate Definitions*)


(* ::Subsection:: *)
(*Density Matrix Operations For Qubits*)


TPM::usage="Input:
	sequence of matrices, e.g. TPM[X,Y,Z,i,H,S,CZ]"
T2M::usage="Input:
	2dim'l tensor"
M2T::usage="Input:
	even dim matrix"
Mtranspose::usage="Input: matrix, tensor index i, tensor indexj"


(* ::Subsection:: *)
(*Common Qubit Gate Definitions*)


Xmat=PauliMatrix[1];
Ymat=PauliMatrix[2];
Zmat=PauliMatrix[3];
(*Hamahard*) Hmat=1/Sqrt[2]{{1,1},{1,-1}};
(*Arbitrary U*) Umat={{U11,U12},{U21,U22}};
(*Arbitrary U*) Vmat={{V11,V12},{V21,V22}};
Smat={{1,0},{0,I}};
Tmat={{1,0},{0,Sqrt[I]}};
imat = IdentityMatrix[2];
(*Controlled-Z*) CZmat=DiagonalMatrix[{1,1,1,-1}];
(*Controlled-U*)CUmat =TPM[{{1,0},{0,0}},imat]+TPM[{{0,0},{0,1}},Umat];
(*Controlled-X*) CXmat=TPM[IdentityMatrix[2],H] . CZmat . TPM[IdentityMatrix[2],Hmat];
(*SWAP*) SWAPmat=CXmat . Mtranspose[CX,1,2] . CXmat;
(*Troffoli*)(CCXmat=TPM[{{1,0},{0,0}},imat,imat]+TPM[{{0,0},{0,1}},CXmat])//MatrixForm;


(*Controlled-SWAP*)CSWAP =TPM[{{1,0},{0,0}},i,i]+TPM[{{0,0},{0,1}},SWAP];


(*Rotation*)
Rx[t_]=MatrixExp[I Xmat t/2];
Ry[t_]=MatrixExp[I Ymat t/2];
Rz[t_]=MatrixExp[I Zmat t/2];


getVec[c_,n_]:=ReplacePart[Table[0,2^n],ToExpression[ToExpression["2^^"<>ToString[c]]]+1->1]


Begin["`Private`"];


(* ::Subsection:: *)
(*Density Matrix Operations For Qubits*)


(*Gate on qubit n:
	[Input] matrix:matrix, bi-unitary operation, pos:int, where to act, n:int, # of physical qubits*)
applytwo[matrix_,pos_,n_]:=TPM@@(ReplacePart[Table[0,n],{pos->matrix,j_/;j!=pos->TPM[imat,imat]}])


(*Pure state*)

pure[vec_]:=Outer[Times,Conjugate[vec],vec]


(*Tensor To Matrix*)
(*Input:
	two matrices
	*)
TM[a_, b_] := Flatten[TensorProduct[a, b], {{1, 3}, {2, 4}}]
SetAttributes[TM, {Flat, OneIdentity}];
(*Input:
	sequence of matrices, e.g. TPM[X,Y,Z,i,H,S,CZ]*)
TPM[a__] := TM[a] /.(*Correction*)TM[x_] :> x (*input 1qubit operators*)
T2M[tensor_] := Block[{n = ArrayDepth[tensor]/2}, Flatten[tensor, {2 Range[n] - 1, 2 Range[n]}]](*functions the same as TM, input tensor; Note, use Arraydepth instead of Depth*)


(*Transversal gates*)
(*[Input]
	gate: matrix, number: int, # of physical qubits*)
	transversal[gate_,number_]:=TPM@@Table[gate,number]


(*Matrix To Tensor*)
M2T[matrix_]:=Nest[Partition[#,{2,2}]&,matrix,Log[2,Length[matrix]]-1]


(*Pauli Group Recipe*)
M[nn_,I_]:=Normal@SparseArray[{i_,j_}/;(i==j||Mod[i,nn]+1==j)->I,{nn,nn}]
(*Pauli Group Element*)
(*nn: length of group, I: pauli number*)
Stab[recipe_]:=Plus@@TPM@@@PauliMatrix/@recipe
Stab[nn_,pos_,I_]:=1/2TPM@@PauliMatrix/@ReplacePart[Table[0,nn],pos->I]


(* ::Input:: *)
(*(*Matrix Transposition*)*)


Mtranspose[matrix_,i_,j_]:=T2M@Transpose[Transpose[M2T[matrix],2i-1<->2j-1],2i<->2j](*acting on matricies, exchanging i with j*)


End[];


EndPackage[];
