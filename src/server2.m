(* ::Package:: *)


$ContextPath = Append[$ContextPath,"MyGlobalContext`"];
$Context = "MyGlobalContext`";
cctr = 0;
mgc = "MyGlobalContext`";
ClearAll["Global`*"];


(* << "SocketLink`" *)
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

CreateResponse[query_] :=
  Module[{o, g=ToExpression[StringTake[query,-1]], xct},
    xct = If[g==0,"LeanLinkCtx`",mgc];
    $Context = xct;
    o = ToExpression[StringDrop[query,-1]] // OutputFormat;
    $Context = mgc;
    ClearAll["Global`*"];
    ClearAll["LeanLinkCtx`*"];
    ToString[StringLength[o]] <> " " <> o] (* ByteCount instead?*)

SocketListen[s, With[{resp=CreateResponse[#["Data"]]}, Print[#["Data"]]; Print[resp]; WriteString[#["SourceSocket"], resp]]&];

