import data.buffer.parser
open parser
--namespace mathematica

meta def htfi : has_to_format ℤ := ⟨λ z, int.rec_on z (λ k, ↑k) (λ k, "-"++↑(k+1))⟩
local attribute [instance] htfi


structure float :=
(sign     : nat)
(mantisa  : nat)
(exponent : nat)

meta instance : has_to_format float :=
⟨λ f, to_fmt "(" ++ to_fmt f.sign ++ to_fmt ", " ++ 
      to_fmt f.mantisa ++ ", " ++ to_fmt f.exponent ++ to_fmt ")"⟩

meta instance : has_reflect float | ⟨s, m, e⟩ :=
((`(λ s' m' e', float.mk s' m' e').subst (nat.reflect s)).subst (nat.reflect m)).subst (nat.reflect e)

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
do str "@INTEGER@[",
   is_neg ← parse_is_neg,
   n ← (nat_of_string ∘ list.as_string) <$> many (sat char.is_alphanum),
   ch ']',
   return $ mmexpr.mint (if is_neg then -n else n)

def parse_string : parser mmexpr :=
do str "@STRING@[\"",
   s ←  list.as_string <$> many (sat ((≠) '\"')), 
   ch '\"', ch ']',
   return $ mmexpr.mstr s

def parse_symbol : parser mmexpr :=
do str "@SYMBOL@[",
   s ←  list.as_string <$> many (sat ((≠) ']')), 
   ch ']',
   return $ mmexpr.sym s

def parse_app_aux (parse_expr : parser mmexpr) : parser mmexpr :=
do str "@SYMAPP@",
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

def mk_mono (s : string) : string :=
(s.to_list.map make_monospaced).as_string

meta def strip_trailing_whitespace : string → string := λ s,
if s.back = '\n' ∨ s.back = ' ' then strip_trailing_whitespace s.pop_back else s

meta def escape_quotes (s : string) : string :=
s.fold "" (λ s' c, if c = '\"' then s' ++ "\\\"" else s'.str c)

meta def escape_term (s : string) : string :=
s.fold "" (λ s' c, if c = '&' then s' ++ "&&" else s'.str c)

meta def quote_string (s : string) : string :=
"\'" ++ s ++ "\'"

#eval "\'"

meta def parse_mmexpr_tac (s : string) : tactic mmexpr :=
do sum.inr mme ← return $ parser.run_string parse_mmexpr ((strip_trailing_whitespace ∘ mk_mono) s),
   return mme

--def singleparse : parser mmexpr :=
--do m ← parse_app_aux parse_int,
 --  m2 ← 

/-run_cmd tactic.trace $ run_string (parse_app_aux parse_int) "@SYMAPP@[@INTEGER@[2]][@INTEGER@[3],@INTEGER@[4]]"
run_cmd tactic.trace $ run_string parse_mmexpr "@SYMAPP@@INTEGER@[2][@INTEGER@[2],@SYMBOL@[xyz],@SYMAPP@@SYMBOL@[Add][@STRING@[\"five\"]]]"
run_cmd tactic.trace $ run_string parse_int "@INTEGER@[-10]"-/

--end mathematica
