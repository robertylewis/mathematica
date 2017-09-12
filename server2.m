(* ::Package:: *)

<< "SocketLink`"
<< "lean_form.m"

WindowsDirQ[s_String] := StringTake[s, 1] != "/";
ToWindowsDir[s_String] := 
 If[WindowsDirQ[s], s, 
  With[{t = StringTake[s, {2}]}, 
       FileNameJoin[{t <> ":" <> StringDrop[s, 2]}]]];
DirectoryFormat[s_String] := 
 If[WindowsDirQ[Directory[]], ToWindowsDir[s], s]


$ContextPath = Append[$ContextPath,"MyGlobalContext`"];
$Context = "MyGlobalContext`";
cctr = 0;
mgc = "MyGlobalContext`";
ClearAll["Global`*"];

CreateAsynchronousServer[CreateServerSocket[10000], Handler]

TestNextChar[in_] := BinaryRead[in, "Character8"] != "&"
WriteLine["stdout",""];


Handler[{in_InputStream, out_OutputStream}] :=
  Module[{o = "", r = "", c = "", g = 0, xct},
         While[True, c = BinaryRead[in, "Character8"];
         If[c == "&" && TestNextChar[in],
            (g = BinaryRead[in, "Character8"] // ToExpression; Close[in]; Break[]), 
             r = r <> c]];
         WriteLine["stdout", "Received:"];
         WriteLine["stdout",  r <> "\n"];
         WriteLine["stdout", "Global: " <> ToString[g]];
         WriteLine["stdout", "Output:"];
         xct = If[g==0,"LeanLinkCtx`",mgc];
         (*{begin, end} = If[g==0,{"LeanLinkCtx`", "$Context=mgc;cctr=cctr+1;"},{mgc, "Null;"}];*)
         $Context = xct;
         o = ToExpression[r] // OutputFormat;
         WriteString[out, ToString[StringLength[o]] <> " "];
         WriteString[out, o];
         $Context = mgc;
         ClearAll["Global`*"];
         ClearAll["LeanLinkCtx`*"];
         WriteString["stdout", o <>"\n\n"];
         Close[out];
  ]

OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]"
OutputFormat[s_String] := "T[\"" <> s <> "\"]"
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]"
OutputFormat[h_[args___]] := 
 "A" <> OutputFormat[h] <> "[" <> 
  StringRiffle[Map[OutputFormat, List[args]], ","] <> "]"
