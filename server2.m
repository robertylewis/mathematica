<< "SocketLink`"
<< "E:\\Dropbox\\lean\\mathematica\\lean_form.m"
CreateAsynchronousServer[CreateServerSocket[10000], Handler]

TestNextChar[in_] := BinaryRead[in, "Character8"] != "&"

Handler[{in_InputStream, out_OutputStream}] := 
  Module[{o = "", r = "", c = ""},(*While[True,TimeConstrained[r=r<>
   BinaryRead[in,"Character8"],0.05,(Close[in];Break[])]];*)
   While[True, c = BinaryRead[in, "Character8"]; 
    If[c == "&" && TestNextChar[in], (Close[in]; Break[]), 
     r = r <> c]];
   WriteString["stdout", "Received:\n" <> r <> "\n\nOutput:"];
   o = ToExpression[r] // OutputFormat;
   WriteString[out, ToString[StringLength[o]] <> " "];
   WriteString[out, o];
   WriteString["stdout", o <>"\n\n"];
   Close[out];];

OutputFormat[i_Integer] := "I[" <> ToString[i] <> "]"
OutputFormat[s_String] := "T[\"" <> s <> "\"]"
OutputFormat[s_Symbol] := "Y[" <> ToString[s] <> "]"
OutputFormat[h_[args___]] := 
 "A" <> OutputFormat[h] <> "[" <> 
  StringRiffle[Map[OutputFormat, List[args]], ","] <> "]"
