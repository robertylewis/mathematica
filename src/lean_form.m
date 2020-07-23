(* ::Package:: *)

LeanName[s_String] := LeanNameMkString[s, LeanNameAnonymous];
LeanName[s_String, t_String] := LeanNameMkString[t, LeanName[s]];
LeanName[i_Int] := LeanNameMkNum[i, LeanNameAnonymous];

UnderscoreName[LeanNameMkString[s_String, t_]] :=
  LeanNameMkString[s <> "_1", t];
UnderscoreName[LeanNameMkNum[i_Int, t_]] :=
  LeanNameMkNum[1, LeanNameMkNum[i, t]];

StringOfName[LeanNameAnonymous] := "";
StringOfName[LeanNameMkString[s_String, LeanNameAnonymous]] := s;
StringOfName[LeanNameMkString[s_String, t_]] :=
  s <> "." <> StringOfName[t];
StringOfName[LeanNameMkNum[i_Int, LeanNameAnonymous]] := ToString[i];
StringOfName[LeanNameMkNum[i_Int, t_]] :=
  ToString[i] <> "." <> StringOfName[t];


LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_add", "add"], _], _], _], x_],
   y_], v_] := Inactive[Plus][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_mul", "mul"], _], _], _], x_],
   y_], v_] := Inactive[Times][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_div", "div"], _], _], _], x_],
   y_], v_] := Inactive[Divide][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_sub", "sub"], _], _], _], x_],
   y_], v_] := Inactive[Subtract][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["has_neg", "neg"], _], _], _],
   x_], v_] := Inactive[Times][-1, LeanForm[x, v]]
LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["add"], _], _], _], x_],
    y_], v_] := Inactive[Plus][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["mul"], _], _], _], x_],
    y_], v_] := Inactive[Times][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["div"], _], _], _], x_],
    y_], v_] := Inactive[Divide][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["sub"], _], _], _], x_],
    y_], v_] := Inactive[Subtract][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["neg"], _], _], _], x_], v_] :=
  Inactive[Times][-1, LeanForm[x, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanApp[LeanConst[LeanName["npow"], _], _], _], _],
    x_], y_], v_] := Inactive[Power][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["nat", "pow"], _],
    x_], y_], v_] := Inactive[Power][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanApp[LeanApp[LeanApp[LeanConst[LeanName["has_pow", "pow"], _],
    _], _], _], x_], y_], v_] := Inactive[Power][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["and"], _], x_], y_],
  v_] := Inactive[And][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["or"], _], x_], y_], v_] :=
  Inactive[Or][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["implies"], _], x_], y_],
  v_] := Inactive[Implies][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanConst[LeanName["not"], _], x_], v_] :=
 Inactive[Not][LeanForm[x, v]]

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["one"], _], _], _],
  v_] := 1

LeanForm[LeanApp[LeanApp[LeanConst[LeanName["zero"], _], _], _],
  v_] := 0

LeanForm[LeanApp[
   LeanApp[LeanConst[LeanName["has_one", "one"], _], _], _], v_] := 1

LeanForm[LeanApp[
   LeanApp[LeanConst[LeanName["has_zero", "zero"], _], _], _], v_] := 0

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["bit0"], _], _], _], t_], v_] :=
  2*LeanForm[t, v]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["bit1"], _], _], _], _],
    t_], v_] := 2*LeanForm[t, v] + 1

LeanForm[LeanApp[LeanConst[LeanName["list", "nil"], _], _], v_] := {}

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["list", "cons"], _], _], h_],
   t_], v_] := Prepend[LeanForm[t, v], LeanForm[h, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["lt"], _], _], _], x_],
   y_], v_] := Inactive[Less][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["le"], _], _], _], x_],
   y_], v_] := Inactive[LessEqual][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["gt"], _], _], _], x_],
   y_], v_] := Inactive[Greater][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanApp[LeanConst[LeanName["ge"], _], _], _], x_],
   y_], v_] := Inactive[GreaterEqual][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_lt", "lt"], _], _], _], x_], y_],
   v_] := Inactive[Less][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_le", "le"], _], _], _], x_], y_],
   v_] := Inactive[LessEqual][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_gt", "gt"], _], _], _], x_], y_],
   v_] := Inactive[Greater][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[
     LeanApp[LeanConst[LeanName["has_ge", "ge"], _], _], _], x_], y_],
   v_] := Inactive[GreaterEqual][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[
   LeanApp[LeanApp[LeanConst[LeanName["eq"], _], _], x_], y_],
   v_] := Inactive[Equal][LeanForm[x, v], LeanForm[y, v]]

LeanForm[LeanApp[LeanConst[LeanName["sin"],_],x_], v_] := Inactive[Sin][LeanForm[x, v]]
LeanForm[LeanApp[LeanConst[LeanName["cos"],_],x_], v_] := Inactive[Cos][LeanForm[x, v]]
LeanForm[LeanApp[LeanConst[LeanName["tan"],_],x_], v_] := Inactive[Tan][LeanForm[x, v]]
LeanForm[LeanConst[LeanName["pi"], _], v_] := Pi

LeanForm[LeanConst[LeanName["true"], _], v_] := True

LeanForm[LeanSort[l_], v_] := LeanSort[l]

LeanForm[LeanConst[a_, b_], v_] := LeanConst[a, b]

LeanForm[LeanMetaVar[a_, b_], v_] := LeanMetaVar[a, b]

(*LeanForm[LeanApp[f_, e_],v__] := LeanForm[f, v][LeanForm[e, v]]*)

LeanForm[LeanLocal[n_, pn_, b_, t_], v_] := LeanLocal[n, pn, b, t]

LeanForm[LeanPi[nm_, bi_, tp_, bod_], v_] := LeanPi[nm, bi, tp, bod]

LeanForm[LeanLambda[nm_, bi_, tp_, bd_], v_] :=
 If[MemberQ[v, Symbol[StringOfName[nm]]],
  LeanForm[LeanLambda[UnderscoreName[nm], bi, tp, bd], v],
  Apply[Function,
   List[Symbol[StringOfName[nm]],
    LeanForm[bd, Prepend[v, Symbol[StringOfName[nm]]]]]]]

LeanForm[LeanVar[i_], v_] := If[Length[v]>i,v[[i+1]],LeanVar[i]]

  (*LeanForm[LeanApp[LeanLambda[nm_, bi_, tp_, bd_], e_], v_] :=
   LeanForm[LeanLambda[nm, bi, tp, bd], v][LeanForm[e,v]]*)




LeanForm[e_] := LeanForm[e, {}]

OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]"
OutputFormat[s_String] := "T[\"" <> s <> "\"]"
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]"
OutputFormat[h_[args___]] :=
 "A" <> OutputFormat[h] <> "[" <>
  StringRiffle[Map[OutputFormat, List[args]], ","] <> "]"


MakeDataUrlFromImage[img_] := "data:image/png;base64," <> ExportString[ExportString[Graphics[img], "PNG"], "Base64"]


PlotOverX[f_, {X_, lb_, ub_}] := Module[{nv, re},
  re = f /. X -> nv; Plot[re, {nv, lb, ub}]]