

(*gary anderson  implementation of terdik multivariate hermite polynomials*)


BeginPackage["terdik`",{

"Statistics`ContinuousDistributions`",
"Statistics`MultinormalDistribution`",
"LinearAlgebra`MatrixManipulation`",
"DiscreteMath`Combinatorica`"

}]


herm::usage="herm[nn_Integer,xVars_List,xCov__?MatrixQ]"

expCovHerm::usage="expCovHerm[nn_Integer,xCov_?MatrixQ]"


expMultiHerm::usage=
"expMultiHerm[partn:{_?integersListQ...},dimsList:{dim_Integer...},xCov_?MatrixQ]"


symUnVec::usage=
"symUnVec[aMat_?MatrixQ]"

integersListQ::usage="integersListQ[xx_List]"
numbersListQ::usage="integersListQ[xx_List]"

kron::usage="kron[a_?MatrixQ,b_?MatrixQ]"
commutationMatrix::usage="commutationMatrix[mm_Integer,nn_Integer],commutationMatrix[mm_Integer]"

(*usage information*)



Begin["Private`"]


(*asVec[xVars_,nn_Integer]:=Transpose[{Through[xVars[nn]]}]*)
asVec[xVars_,nn_Integer]:=Transpose[{xVars}]

(*trying all x's same*)
(*herm[0,xVars_List,_]:=Transpose[{Table[1,{Length[xVars]}]}];*)
herm[0,xVars_List,_]:={{1}}
herm[1,xVars_List,_]:=asVec[xVars,1]


herm[nn_Integer,xVars_List,xCov__?MatrixQ]:=
kron[herm[nn-1,xVars,xCov],asVec[xVars,nn]] -
hermSecondTerm[nn,xVars,xCov]




hermSecondTerm[nn_Integer,xVars_List,xCov_?MatrixQ]:=
Sum[hermTerm[nn,jj,xVars,xCov],{jj,1,nn-1}]

hermTerm[nn_Integer,jj_Integer,xVars_List,xCov_?MatrixQ]:=
With[{dims=Table[Length[xVars],{nn}]},
With[{kPermInv=kInvNJ[jj,dims]},
kPermInv . kron[vec[xCov],herm[nn-2,xVars,xCov]]
]]


expCovHerm[nn_Integer,xCov_?MatrixQ]:=
With[{dims=Table[Length[xCov],{nn}],vXCov=vec[xCov]},
forSum02[dims,dims] . powerKron[Table[vXCov,{nn}]]]





semiFactorial[kk_Integer]:=
Apply[Times,Range[1,kk-1,2]]/;And[EvenQ[kk],kk>0]
(*
makePII[nn_Integer]:=
With[{theList=Range[nn]},
Map[chooseOne[#,
*)


chooseOne[thisOne_Integer,aList_?integersListQ]:=
{Take[aList,{thisOne}],Drop[aList,{thisOne}]}/;
And[0<thisOne<=Length[aList]]

choosePair[thisOne_Integer,thatOne_Integer,aList_?integersListQ]:=
With[{theRest=Complement[Range[Length[aList]],{thisOne,thatOne}]},
{{Take[aList,{thisOne}],Take[aList,{thatOne}]},aList[[theRest]]}]/;
And[thisOne!=thatOne,0<thisOne<=Length[aList],0<thatOne<=Length[aList]]



makePairsUT[remaining_?integersListQ]:=
If[Length[remaining]==2,{Partition[remaining,1]},
With[{choiceNow=Map[choosePair[1,#,remaining]&,Range[2,Length[remaining]]]},
Flatten[Map[Apply[preGlom,#]&,choiceNow],1]]]/;
And[EvenQ[Length[remaining]]]



preGlom[{fir_?integersListQ,sec_?integersListQ},aList_?integersListQ]:=
glom[{fir,sec},makePairsUT[aList]]

makePairs[nn_Integer]:=
With[{theList=Range[nn]},
Map[Transpose,makePairsUT[theList]]]/;
And[EvenQ[nn]]


glom[{fir_?integersListQ,sec_?integersListQ},listOfPairs_List]:=
Map[{Join[fir,#[[1]]],Join[sec,#[[2]]]}&,listOfPairs]
(*should transpose*)



notNoLoops[partitionList_List,aPairList:{{{_Integer,_Integer}...}...}]:=
With[{allOfEm=Flatten[partitionList]},
Print["allOfEm=",allOfEm,"aPairList=",aPairList];
With[{allRight=Select[aPairList,Complement[Flatten[#],allOfEm]=={}&]},
Print["allRight=",allRight];
Select[allRight,noneThesePairingsInAnySet[#,partitionList]&]]]


noLoops[partitionList_List,aPairList:{{{_Integer,_Integer}...}...}]:=
Select[aPairList,noneThesePairingsInAnySet[#,partitionList]&]

notBothInThisSet[pair:{_Integer,_Integer},aSet_?integersListQ]:=
Length[Intersection[aSet,pair]]!=2
notBothInAnySet[pair:{_Integer,_Integer},theSets:{_?integersListQ...}]:=
Apply[And,Map[notBothInThisSet[pair, #1] & , theSets]]
noneThesePairingsInAnySet[pairs:{{_Integer,_Integer}...},
theSets:{_?integersListQ...}]:=
Apply[And,Map[notBothInAnySet[#1, theSets] & , pairs]]



(*expects all dimensions the same*)
forSumMulti[partn:{_?integersListQ...},dim_Integer]:=
With[{dimsList=Table[dim,{Length[Flatten[partn]]}]},
With[{unPart=Flatten[partn]},
With[{nn=Length[unPart]},
With[{nLoops=noLoops[partn,makePairs[nn]]},
With[{perms=Map[Flatten,nLoops]},
With[{kInvs=Map[Transpose[commutationPerm[#,dimsList][[1]]]&,perms]},
If[kInvs=={},With[{matDim=Apply[Times,dimsList]},ZeroMatrix[matDim]],
Apply[Plus,kInvs]]]]]]]]

collapseMat[partn:{_?integersListQ...},dim_Integer]:=
With[{layout=Flatten[partn]},
With[{clp=collapseRow[layout]},
With[{bigClp=kron[clp,IdentityMatrix[dim]]},
With[{allMats=Map[kron[{#},{#}]&,bigClp]},allMats]]]]

collapseRow[fPattern_?integersListQ]:=
With[{onceOnly=Union[fPattern]},
With[{zip=Table[0,{Length[fPattern]}],
places=Map[matchPlaces[fPattern,#]&,onceOnly]},
Map[ReplacePart[zip,1,#]&,places]]]

matchPlaces[vec_?integersListQ,num_Integer]:=Position[vec,num]

notForSumMulti[partn:{_?integersListQ...},dim_Integer]:=
With[{dimsList=Table[dim,{Length[Union[Flatten[partn]]]}]},
With[{unPart=Union[Flatten[partn]]},
With[{nn=Length[unPart]},
With[{nLoops=notNoLoops[partn,makePairs[nn]]},Print["nLoops=",nLoops];
With[{perms=Map[Flatten,nLoops]},Print["perms=",perms];
With[{kInvs=Map[Transpose[commutationPerm[#,dimsList][[1]]]&,perms]},
Print["prekInvs=",Map[Identity[commutationPerm[#,dimsList][[1]]]&,perms]];
If[kInvs=={},With[{matDim=Apply[Times,dimsList]},ZeroMatrix[matDim]],
Apply[Plus,kInvs]]]]]]]]


(*expects all dimensions the same*)
expMultiHerm[partn:{_?integersListQ...},xCov_?MatrixQ]:=
With[{dim=Length[xCov]},
forSumMulti[partn,dim] . 
rightKron[xCov,partn]]
(*
powerKron[
Join[Map[vec[kron[IdentityMatrix[#],xCov]]&,dimsList]]]]
forSumMulti[partn,dimsList] . powerKron[Table[vXCov,{nn/2}]]]
*)
rightKron[xCov_?MatrixQ,prtn:{_?integersListQ...}]:=
powerKron[Join[
Map[rightForAPart[xCov,#]&,prtn]]]

rightForAPart[xCov_?MatrixQ,aPart_?integersListQ]:=
powerKron[Table[xCov,{Length[aPart]}]]
(*
not diagonal
expCovHerm[3,IdentityMatrix[3]]
expCovHerm[2,IdentityMatrix[2]]
expMultiHerm[{{1, 3}, {2, 4}},IdentityMatrix[2]]//symUnVec
*)

(*
expCovHerm[2,{{2,1},{1,2}}]//symUnVec
*)



(*pg 159 for moments of gaussian system*)
(*second order*)
forSum02[dimsListA_?integersListQ,dimsListB_?integersListQ]:=
With[{nn=Length[dimsListA]},
With[{perms=Permutations[Range[nn]]},
Apply[Plus,Map[kInvQ[#,dimsListA,dimsListB]&,perms]]]]/;
And[Length[dimsListA]==Length[dimsListB]]


(*
expCovHerm[2,IdentityMatrix[2]]


not diagonal
expCovHerm[3,IdentityMatrix[3]]
*)
(*
expCovHerm[2,{{2,1},{1,2}}]//symUnVec
*)


commutationMatrix[mm_Integer,nn_Integer]:=
Module[{retMat=ZeroMatrix[mm*nn,mm*nn],ii,jj},
For[ii=1,ii<=mm,ii++,
For[jj=1,jj<=nn,jj++,
retMat[[(ii-1)*nn+jj,(jj-1)*mm+ii]]=1]];
retMat]
commutationMatrix[mm_Integer]:=commutationMatrix[mm,mm]


commutationSwitch[dimsList_List,jj_Integer]:=
With[{nn=Length[dimsList]},
With[{preJ=If[jj==1,{},Take[dimsList,jj-1]],
postJ=If[jj>nn-2,{},Take[dimsList,-(nn-(jj+1))]]},
With[{jDim=dimsList[[jj]],
jP1Dim=dimsList[[jj+1]]},
With[{theCommMat=commutationMatrix[jP1Dim,jDim]},
With[{switchMat=powerKron[Join[dimsToIDims[preJ],
{theCommMat},dimsToIDims[postJ]]]},
{switchMat,switchDims[dimsList,jj]}
]]]]]/;jj<Length[dimsList]


switchDims[dims_?integersListQ,thePos_Integer]:=
With[{jth=dims[[thePos]],jP1th=dims[[thePos+1]]},
ReplacePart[ReplacePart[dims,jP1th,thePos],jth,thePos+1]]/;
And[thePos>0,thePos<Length[dims]]


pairSeq[{fromPerm_?integersListQ,toPerm_?integersListQ,
matched_List,xForms_List}]:=
If[fromPerm==toPerm,xForms,
pairSeq[matchFirst[{fromPerm,toPerm,matched,xForms}]]]/;
And[Length[fromPerm]==Length[toPerm],
Complement[fromPerm,toPerm]=={}]


matchFirst[{fromPerm_?integersListQ,toPerm_?integersListQ,
matched_List,xForms_List}]:=
With[{begTo=First[toPerm],begFrom=First[fromPerm]},
If[begTo==begFrom,
{Rest[fromPerm],Rest[toPerm],Append[matched,begTo],xForms},
With[{thePos=Flatten[Position[fromPerm,begTo]][[1]]},
With[{tToF=thereToFront[thePos,fromPerm]},
{tToF[[2]],Rest[toPerm],Append[matched,begTo],
Join[xForms,Length[matched]+tToF[[1]]]}]]]]


thereToFront[therePos_Integer,fromVec_?integersListQ]:=
{Range[therePos-1,1,-1],Drop[fromVec,{therePos}]}


commutationPerm[thePerm_?integersListQ,dimsList_?integersListQ]:=
With[{theSeq=pairSeq[{thePerm,Range[Length[thePerm]],{},{}}]},
With[{permRes=
syncSwitch[{IdentityMatrix[Apply[Times,dimsList]],dimsList,theSeq}]},
permRes]]/;And[PermutationQ[thePerm],Length[dimsList]==Length[thePerm]]

notCommutationPerm[thePerm_?integersListQ,dimsList_?integersListQ]:=
With[{theSeq=pairSeq[{thePerm,Range[Length[thePerm]],{},{}}]},
With[{permRes=
syncSwitch[{IdentityMatrix[Apply[Times,dimsList]],dimsList,theSeq}]},
permRes]]/;And[PermutationQ[thePerm],Length[dimsList]==Length[thePerm]]

commutationTranspose[dimsList_?integersListQ,jj_Integer,kk_Integer]:=
With[{thePerm=
ReplacePart[ReplacePart[Range[Length[dimsList]],kk,jj],jj,kk]},
commutationPerm[thePerm,dimsList]]/;With[{len=Length[dimsList]},And[0<jj<=len,0<kk<=len]]

syncSwitch[{xMat_?MatrixQ,theDims_?integersListQ,switchCols_?integersListQ}]:=
If[switchCols=={},{xMat,theDims,switchCols},
With[{switchPair=commutationSwitch[theDims,First[switchCols]]},
syncSwitch[{switchPair[[1]] . xMat,switchPair[[2]],Rest[switchCols]}]]]



orderPartPerm[partList_List]:=
Flatten[orderPartition[partList]]/;
With[{allOfEm=Apply[Join,partList]},
Union[allOfEm]==Range[Length[allOfEm]]]



kInvNJ[jj_Integer,dimsList_?integersListQ]:=
With[{nn=Length[dimsList]},
With[{
kNTo1=commutationTranspose[dimsList,nn,1][[1]],
kJP1To2=commutationTranspose[
Prepend[Drop[dimsList,-1],dimsList[[nn]]],jj+1,2][[1]]
},
Transpose[kJP1To2 . kNTo1]]]


kInvQ[thePerm_?integersListQ,
dimsListA_?integersListQ,dimsListB_?integersListQ]:=
With[{qPerm=makeQ[thePerm],longDims=Join[dimsListA,dimsListB]},
Transpose[commutationPerm[qPerm,longDims][[1]]]]/;
And[Length[thePerm]==Length[dimsListA]==Length[dimsListB]]

(*
*)


makeQ[pp_?numbersListQ]:=
With[{nn=Length[pp]},
Table[
If[OddQ[ii],(ii+1)/2,
nn+pp[[ii/2]]],{ii,2*nn}]]



(*should be list of lists of symbols*)


dOpStep[theFuncs_,aLamVal_List]:=Flatten[theJac[theFuncs,aLamVal]]

(*a list of lam lists of symbols*)
dOp[theFuncs_,lamVals_List]:=Flatten[
Fold[dOpStep,theFuncs,lamVals]]

(*lamVec should be list of symbols*)
theJac[theFuncs_List,theLamVec_List]:=
Map[doAFuncALambda[#,theLamVec]&,theFuncs]

doAFuncALambda[theFunc_,theLamVec_List]:=
Map[D[theFunc,#]&,theLamVec]


(*

Needs["LinearAlgebra`MatrixManipulation`"]

(*terdik nonlinear analysis ofmultidimensional time series*)

(*lamVec should be list of symbols*)
theJac[theFuncs_List,theLamVec_List]:=
Map[doAFuncALambda[#,theLamVec]&,theFuncs]

doAFuncALambda[theFunc_,theLamVec_List]:=
Map[D[theFunc,#]&,theLamVec]

(*should be list of lists of symbols*)


dOpStep[theFuncs_,aLamVal_List]:=Flatten[theJac[theFuncs,aLamVal]]

(*a list of lam lists of symbols*)
dOp[theFuncs_,lamVals_List]:=Flatten[
Fold[dOpStep,theFuncs,lamVals]]



kron[a_,b_]:=BlockMatrix[Outer[Times,a,b]]



*)



symUnVec[aMat_?MatrixQ]:=
With[{len=Sqrt[Length[aMat]]},
Partition[Flatten[aMat],len]]

randomVecs[]:=Transpose[{Table[Random[],{Random[Integer,{2,4}]}]}]


dimsToIDims[theDims_List]:=Map[IdentityMatrix[#]&,theDims]
dimsToIDims[{}]:={{{1}}}

powerKron[theMats_List]:=Fold[kron,{{1}},theMats]


vec[aMat_?MatrixQ]:=Transpose[{Flatten[Transpose[aMat]]}]




kron[a_?MatrixQ,b_?MatrixQ]:=BlockMatrix[Outer[Times,a,b]]

numbersListQ[___]:=False
numbersListQ[xx_List]:=And[VectorQ[xx,NumberQ],Min[xx]>0]
integersListQ[___]:=False
integersListQ[xx_List]:=And[VectorQ[xx,IntegerQ],Min[xx]>0]



quasiNorm[bVec_?integersListQ]:=Apply[Times,2^(-bVec)]
orderPartition[partList_List]:=
With[{eachSorted=Map[Sort,partList]},
Sort[eachSorted,quasiNorm[#1] <quasiNorm[#2]&]]/;
With[{allOfEm=Apply[Join,partList]},
Union[allOfEm]==Range[Length[allOfEm]]]




Needs["LinearAlgebra`MatrixManipulation`"]

(*terdik nonlinear analysis ofmultidimensional time series*)




End[]




Begin["Tests`"]


(*
herm[3,{xx},IdentityMatrix[1]]/.xx[_]->daX//Expand
HermiteH[3,xx]
symetries
unfolded index
000
001
010 
...

folded
000
001
011
111
elimnates symetries
boo=herm[4,{xx,yy},IdentityMatrix[2]]/.{xx[_]->daX,yy[_]->daY}//Expand
boo[[{2,3,5}]]
boo[[{4,6,7}]]
ExpectedValue[goo=herm[3,{xx,yy,zz},IdentityMatrix[3]]/.{xx[_]->daX,yy[_]->daY,zz[_]->daZ}//Expand,MultinormalDistribution[{0,0,0},IdentityMatrix[3]],{daX,daY,daZ}]


(*
Apply[Plus,Map[kInvQ[#,dimsListA,dimsListB]&,perms]]]]/;
And[Length[dimsListA]==Length[dimsListB]]
With[{perms=Permutations[Range[nn]]},
Apply[Plus,Map[kInvQ[#,dimsListA,dimsListB]&,perms]]]]/;
And[Length[dimsListA]==Length[dimsListB]]


*)


ExpectedValue[goo=herm[3,{xx,yy,zz},IdentityMatrix[3]]/.{xx[_]->daX,yy[_]->daY,zz[_]->daZ}//Expand,MultinormalDistribution[{0,0,0},IdentityMatrix[3]],{daX,daY,daZ}]
folded=Union[goo]
ExpectedValue[kron[folded,folded],MultinormalDistribution[{0,0,0},IdentityMatrix[3]],{daX,daY,daZ}]
*)


(*
not diagonal
expCovHerm[1,IdentityMatrix[1]]//symUnVec
expMultiHerm[{{1}, {2}},IdentityMatrix[1]]//symUnVec

expCovHerm[2,IdentityMatrix[2]]//symUnVec
expMultiHerm[{{1,2}, {3,4}},IdentityMatrix[2]]//symUnVec

expCovHerm[3,IdentityMatrix[3]]//symUnVec
expMultiHerm[{{1,2,3}, {4,5,6}},IdentityMatrix[3]]//symUnVec



Partitions[4,3] ->{{3, 1}, {2, 2}, {2, 1, 1}, {1, 1, 1, 1}}
expMultiHerm[{{1}, {2,3,4}},IdentityMatrix[2]]//symUnVec
expMultiHerm[{{1,2},{3,4}},IdentityMatrix[1]]//symUnVec
expMultiHerm[{{1},{2},{3,4}},IdentityMatrix[1]]//symUnVec
expMultiHerm[{{1},{2},{3},{4}},IdentityMatrix[1]]//symUnVec
expMultiHerm[{{1}, {2,3,4}},IdentityMatrix[2]]//symUnVec
expMultiHerm[{{1,2},{3,4}},IdentityMatrix[2]]//symUnVec
expMultiHerm[{{1},{2},{3,4}},IdentityMatrix[2]]//symUnVec
expMultiHerm[{{1},{2},{3},{4}},IdentityMatrix[2]]//symUnVec

no factorial term
expMultiHerm[{{1}, {2}},IdentityMatrix[2]]//symUnVec->
{{1, 0}, {0, 1}}
expMultiHerm[{{1},{2},{3},{4}},IdentityMatrix[1]]//symUnVec->3
expMultiHerm[{{1},{2},{3},{4}},IdentityMatrix[2]]//symUnVec->3
expMultiHerm[{{1},{2},{3},{4}},IdentityMatrix[2]]//symUnVec
{{3, 0, 0, 1}, {0, 2, 0, 0}, {0, 0, 2, 0}, {1, 0, 0, 3}}
(expMultiHerm[{{1},{2},{3},{4},{5},{6}},IdentityMatrix[2]]//symUnVec)==
{{15, 0, 0, 5, 0, 6, 4, 0}, {0, 0, 2, 0, 1, 0, 0, 3}, 
 {0, 4, 4, 0, 4, 0, 0, 12}, {0, 0, 0, 0, 0, 0, 0, 0}, 
 {0, 0, 0, 0, 0, 0, 0, 0}, {12, 0, 0, 4, 0, 4, 4, 0}, 
 {3, 0, 0, 1, 0, 2, 0, 0}, {0, 4, 6, 0, 5, 0, 0, 15}}

*)


trySyncSwitch[theDims_?integersListQ,switches_?integersListQ]:=
With[{iMat=IdentityMatrix[Apply[Times,theDims]]},
syncSwitch[{iMat,theDims,switches}]]



(*
pairSeq[{{1,2,3},{1,2,3},{},{}}]
pairSeq[{{4,2,3,1},{1,3,2,4},{},{}}]
commutationPerm[{2,1},{2,3}][[1]] == commutationSwitch[{2,3},1][[1]]
commutationPerm[{1,2,4,3},{2,3,4,5}][[1]] == commutationSwitch[{2,3,4,5},3][[1]]boo=commutationPerm[{1,2,4,3},{2,3,4,5}][[1]] ;
Max[Abs[boo . Transpose[boo] - IdentityMatrix[Length[boo]]]]
*)


tryCommutation[mm_Integer,nn_Integer]:=
With[{aMat=Table[Random[],{mm},{nn}],
cMat=commutationMatrix[mm,nn]},
Max[Abs[Flatten[(cMat . vec[aMat]) - vec[Transpose[aMat]]]]]
]/;And[mm>0,nn>0]



tryCommutationSwitch[kk_Integer,jj_Integer]:=
With[{theVecs=Table[randomVecs[],{kk}]},
With[{theDims=Map[Length,theVecs]},
With[{cSwitch=commutationSwitch[theDims,jj][[1]]},
With[{preSwitchProd=powerKron[theVecs]},
With[{preJ=If[jj==1,{},Take[theVecs,jj-1]],
postJ=If[jj>kk-2,{},Take[theVecs,-(kk-(jj+1))]]},
With[{jVec=theVecs[[jj]],
jP1Vec=theVecs[[jj+1]]},
Max[Abs[Flatten[cSwitch . preSwitchProd-
powerKron[Join[preJ,{jP1Vec,jVec},postJ]]]]]]]]]]]/;
And[kk>0,jj<kk]



hVec[qq_Integer]:=
Table[herm[ii][xx],{ii,0,qq}]
aVec[qq_Integer]:=
Table[aa[ii],{ii,0,qq}]


theInts[qq_Integer]:=
With[{theHs=hVec[qq],theAs=aVec[qq]},
With[{theInnerSq=(theHs . theAs)^2},
Map[Integrate[#*theInnerSq,phi[xx],{xx,lower,upper}]&,
theHs]]]


boo=theInts[1]



End[]



EndPackage[]
