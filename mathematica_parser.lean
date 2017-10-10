import data.buffer.parser system.io
open parser
--namespace mathematica

meta def htfi : has_to_format ℤ := ⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-"++↑(k+1))⟩
local attribute [instance] htfi


structure mfloat :=
(sign     : nat)
(mantisa  : nat)
(exponent : nat)

local notation `float` := mfloat

meta instance : has_to_format float :=
⟨λ f, to_fmt "(" ++ to_fmt f.sign ++ to_fmt ", " ++ 
      to_fmt f.mantisa ++ ", " ++ to_fmt f.exponent ++ to_fmt ")"⟩

meta instance : has_reflect float | ⟨s, m, e⟩ :=
((`(λ s' m' e', mfloat.mk s' m' e').subst (nat.reflect s)).subst (nat.reflect m)).subst (nat.reflect e)

/--
The type mmexpr reflects Mathematica expression syntax.
-/
inductive mmexpr : Type
| sym   : string → mmexpr
| mstr  : string → mmexpr
| mint  : int → mmexpr 
| app   : mmexpr → list mmexpr → mmexpr
| mreal : float → mmexpr 


meta def mmexpr_list_to_format (f : mmexpr → format) : list mmexpr → format
| []       := to_fmt ""
| [h]      := f h
| (h :: t) := f h ++ ", " ++ mmexpr_list_to_format t

open mmexpr
meta def mmexpr_to_format : mmexpr → format
| (sym s)     := to_fmt s
| (mstr s)     := to_fmt "\"" ++ to_fmt s ++ "\""
| (mint i)    := to_fmt i
| (app e1 ls) := mmexpr_to_format e1 ++ to_fmt "[" ++ mmexpr_list_to_format mmexpr_to_format ls ++ to_fmt "]"
| (mreal r)   := to_fmt r 


meta instance : has_to_format mmexpr := ⟨mmexpr_to_format⟩

def nat_of_char : char → nat
| '0' := 0
| '1' := 1
| '2' := 2
| '3' := 3
| '4' := 4
| '5' := 5
| '6' := 6
| '7' := 7
| '8' := 8
| '9' := 9
|  _  := 0

def nat_of_string_aux : nat → nat → list char → nat
| weight acc [] := acc
| weight acc (h::t) := nat_of_string_aux (weight*10) (weight * (nat_of_char h) + acc) t 

def nat_of_string (s : string) : nat :=
nat_of_string_aux 1 0 s.to_list.reverse

def parse_is_neg : parser bool :=
(ch '-' >> return tt) <|> return ff

def parse_int : parser mmexpr := 
do str "I[",
   is_neg ← parse_is_neg,
   n ← (nat_of_string ∘ list.as_string) <$> many (sat char.is_alphanum),
   ch ']',
   return $ mmexpr.mint (if is_neg then -n else n)

def parse_string : parser mmexpr :=
do str "T[\"",
   s ←  list.as_string <$> many (sat ((≠) '\"')), 
   ch '\"', ch ']',
   return $ mmexpr.mstr s

def parse_symbol : parser mmexpr :=
do str "Y[",
   s ←  list.as_string <$> many (sat ((≠) ']')), 
   ch ']',
   return $ mmexpr.sym s

def parse_app_aux (parse_expr : parser mmexpr) : parser mmexpr :=
do str "A",
   hd ← parse_expr,
   ch '[',
   args ← sep_by (ch ',') parse_expr,
   ch ']',
   return $ mmexpr.app hd args

meta def parse_mmexpr_aux (p : parser mmexpr) : parser mmexpr :=
parse_int <|> parse_string <|> parse_symbol <|> (parse_app_aux p)

meta def parse_mmexpr : parser mmexpr := fix parse_mmexpr_aux

private def make_monospaced : char → char
| '\n' := ' '
| '\t' := ' '
| '\x0d' := ' '
| c := c

def mk_mono_cb (s : char_buffer) : char_buffer :=
s.map make_monospaced

def buffer.back {α} [inhabited α] (b : buffer α) : α :=
b.read' (b.size-1)

meta def strip_trailing_whitespace_cb : char_buffer → char_buffer := λ s,
if s.back = '\n' ∨ s.back = ' ' then strip_trailing_whitespace_cb s.pop_back else s

meta def escape_quotes_cb (s : char_buffer) : char_buffer :=
s.foldl buffer.nil (λ c s', if c = '\"' then s' ++ "\\\"".to_char_buffer else s'.push_back c)

meta def escape_term_buffer_cb (s : char_buffer) : char_buffer :=
s.foldl buffer.nil (λ c s', if c = '&' then s' ++ "&&".to_char_buffer else s'.push_back c)

meta def quote_string_cb (s : char_buffer) : char_buffer :=
"\'".to_char_buffer ++ s ++ "\'".to_char_buffer


def mk_mono (s : string) : string :=
(s.to_list.map make_monospaced).as_string

meta def strip_trailing_whitespace : string → string := λ s,
if s.back = '\n' ∨ s.back = ' ' then strip_trailing_whitespace s.pop_back else s

meta def escape_quotes (s : string) : string :=
s.fold "" (λ s' c, if c = '\"' then s' ++ "\\\"" else s'.str c)

meta def escape_term (s : string) : string :=
s.fold "" (λ s' c, if c = '&' then s' ++ "&&" else s'.str c)

meta def escape_slash (s : string) : string :=
s.fold "" (λ s' c, if c = '\\' then s' ++ "\\\\" else s'.str c)

meta def quote_string (s : string) : string :=
"\'" ++ s ++ "\'"


meta def parse_mmexpr_tac (s : char_buffer) : tactic mmexpr :=
match parser.run parse_mmexpr ((strip_trailing_whitespace_cb ∘ mk_mono_cb) s) with
| sum.inr mme := return mme
| sum.inl error := tactic.fail error
end

def parse_name : parser (list string) := 
do l ← sep_by (ch '.') (many $ sat ((≠) '.')),
   return $ (l.map list.as_string).reverse

def mk_name_using : list string → name
| []       := name.anonymous
| (s :: l) := mk_str_name (mk_name_using l) s

meta def parse_name_tac (s : string) : tactic name :=
match parser.run_string parse_name s with
| sum.inr ls := return $ mk_name_using ls
| sum.inl error := tactic.fail error
end

/-meta def parse_mmexpr_tac (s : char_buffer) : tactic mmexpr :=
(do sum.inr mme ← return $ parser.run parse_mmexpr ((strip_trailing_whitespace_cb ∘ mk_mono_cb) s),
   return mme)
-/
namespace mathematica

section
variable [io.interface]
def write_file (fn : string) (cnts : string) (mode := io.mode.write) : io unit := do
h ← io.mk_file_handle fn io.mode.write,
io.fs.write h cnts.to_char_buffer,
io.fs.close h


def exists_file (f : string) : io bool := do
ch ← io.proc.spawn { cmd := "test", args := ["-f", f] },
ev ← io.proc.wait ch,
return $ ev = 0

meta def new_text_file : string → nat → io nat | base n :=
do b ← exists_file (base ++ to_string n ++ ".txt"),
   if b then new_text_file base (n+1)
   else return n

end

meta def temp_file_name (base : string) : tactic string :=
do n ← tactic.run_io (λ i, @new_text_file i base 0),
   return $ base ++ to_string n ++ ".txt"
end mathematica

variable [io.interface]
def io.buffer_cmd (args : io.process.spawn_args) : io char_buffer :=
do child ← io.proc.spawn { args with stdout := io.process.stdio.piped },
  buf ← io.fs.read_to_end child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ to_string exitv,
  return buf
