(* ::Package:: *)


$ContextPath = Append[$ContextPath,"MyGlobalContext`"];
$Context = "MyGlobalContext`";
cctr = 0;
mgc = "MyGlobalContext`";
ClearAll["Global`*"];

<< "lean_form.m"

WindowsDirQ[s_String] := StringTake[s, 1] != "/";
ToWindowsDir[s_String] :=
 If[WindowsDirQ[s], s,
  With[{t = StringTake[s, {2}]},
       FileNameJoin[{t <> ":" <> StringDrop[s, 2]}]]];
DirectoryFormat[s_String] :=
 If[WindowsDirQ[Directory[]], ToWindowsDir[s], s]

s = SocketOpen[10000]

OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]"
OutputFormat[s_String] := "T[\"" <> s <> "\"]"
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]"
OutputFormat[h_[args___]] :=
 "A" <> OutputFormat[h] <> "[" <>
  StringRiffle[Map[OutputFormat, List[args]], ","] <> "]"

resp := ""

AccumulateResponse[query_] :=
  resp = resp <> ToString[query]; Print[resp]

ResponseCompleteQ[] := StringTake[resp,{-3,-2}] == "&!"

CreateResponse[] :=
  Module[{o, g=ToExpression[StringTake[resp,-1]], xct},
    xct = If[g==0,"LeanLinkCtx`",mgc];
    $Context = xct;
    o = ToExpression[StringDrop[StringReplace[resp,"&&"->"&"],-3]] // OutputFormat;
    $Context = mgc;
    ClearAll["Global`*"];
    ClearAll["LeanLinkCtx`*"];
    resp = "";
    StringToByteArray[o]]

SocketListen[s,
  (AccumulateResponse[#["Data"]];
  If[ResponseCompleteQ[],
    Print[resp]; With[{out=CreateResponse[]}, Print[out]; 
      WriteString[#["SourceSocket"], ToString[Length[out]] <> " "]; BinaryWrite[#["SourceSocket"], out]], True])&];

