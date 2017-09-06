/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/


import .mathematica_parser system.io
open expr string level name binder_info

namespace list
variables {α β : Type} 
universes u v w

def for : list α → (α → β) → list β := flip map

def mfor {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (l : list α) (f : α → m β) : m (list β) :=
mmap f l

end list

meta def rb_lmap.of_list {key : Type} {data : Type} [has_ordering key] : list (key × data) → rb_lmap key data
| []           := rb_lmap.mk key data
| ((k, v)::ls) := rb_lmap.insert (rb_lmap.of_list ls) k v

meta def rb_map.insert_list {key : Type} {data : Type} : rb_map key data → list (key × data) → rb_map key data
| m [] := m
| m ((k, d) :: t) := rb_map.insert_list (rb_map.insert m k d) t

local attribute [instance] htfi

-- this has the expected behavior only if i is under the max size of unsigned
def unsigned_of_int (i : int) : unsigned := 
int.rec_on i (λ k, unsigned.of_nat k) (λ k, unsigned.of_nat k)

meta def expand_let : expr → expr
| (elet nm tp val bod) := expr.replace bod (λ e n, match e with |var n := some val | _ := none end)
| e := e

/-
  The following definitions are used to reflect Lean syntax into Mathematica. We reflect the types
   - name
   - level
   - list level
   - binder_info
   - expr
-/
namespace mathematica
meta def form_of_name : name → string
| anonymous         := "LeanNameAnonymous"
| (mk_string s nm)  := "LeanNameMkString[\"" ++ s ++ "\", " ++ form_of_name nm ++ "]"
| (mk_numeral i nm) := "LeanNameMkNum[" ++ to_string i ++ ", " ++ form_of_name nm ++ "]"

meta def form_of_lvl : level → string
| zero              := "LeanZeroLevel"
| (succ l)          := "LeanLevelSucc[" ++ form_of_lvl l ++ "]"
| (level.max l1 l2) := "LeanLevelMax[" ++ form_of_lvl l1 ++ ", " ++ form_of_lvl l2 ++ "]"
| (imax l1 l2)      := "LeanLevelIMax[" ++ form_of_lvl l1 ++ ", " ++ form_of_lvl l2 ++ "]"
| (param nm)        := "LeanLevelParam[" ++ form_of_name nm ++ "]"
| (mvar nm)         := "LeanLevelMeta[" ++ form_of_name nm ++ "]"

meta def form_of_lvl_list : list level → string
| []       := "LeanLevelListNil"
| (h :: t) := "LeanLevelListCons[" ++ form_of_lvl h ++ ", " ++ form_of_lvl_list t ++ "]"

meta def form_of_binder_info : binder_info → string
| binder_info.default := "BinderInfoDefault"
| implicit            := "BinderInfoImplicit"
| strict_implicit     := "BinderInfoStrictImplicit"
| inst_implicit       := "BinderInfoInstImplicit"
| other               := "BinderInfoOther"

/-
  let expressions get unfolded before translation.
  translating macro expressions is not supported.
-/
meta def form_of_expr : expr → string
| (var i)                     := "LeanVar[" ++ (format.to_string (to_fmt i) options.mk) ++ "]"
| (sort lvl)                  := "LeanSort[" ++ form_of_lvl lvl ++ "]"
| (const nm lvls)             := "LeanConst[" ++ form_of_name nm ++ ", " ++ form_of_lvl_list lvls ++ "]"
| (mvar nm nm' tp)                := "LeanMetaVar[" ++ form_of_name nm ++ ", " ++ form_of_expr tp ++ "]"
| (local_const nm ppnm bi tp) := "LeanLocal[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_name ppnm ++ ", " ++ form_of_binder_info bi ++ 
                                     ", " ++ form_of_expr tp ++ "]"
| (app f e)                   := "LeanApp[" ++ form_of_expr f ++ ", " ++ form_of_expr e ++ "]"
| (lam nm bi tp bod)          := "LeanLambda[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_binder_info bi ++ ", " ++ 
                                     form_of_expr tp ++ ", " ++ form_of_expr bod ++ "]"
| (pi nm bi tp bod)           := "LeanPi[" ++ form_of_name nm ++ ", " ++ 
                                     form_of_binder_info bi ++ ", " ++ form_of_expr tp ++
                                     ", " ++ form_of_expr bod ++ "]"
| (elet nm tp val bod)        := form_of_expr $ expand_let $ elet nm tp val bod
| (macro mdf mlst)           := "LeanMacro"

/-
These functions are difficult to implement without a monad map over expr. 
The problem: macros can be definitionally equal but have different meanings.
So we need to replace them in an expr as soon as we encounter them, which involves
generating a fresh name.

section
open tactic

meta def is_macro : expr → bool
| (macro _ _ _) := tt
| _             := ff

meta def find_macros (e : expr) : rb_set expr :=
e^.fold (rb_map.mk _ _) (λ ex _ map, if is_macro ex then map^.insert ex else map)

meta def {u} flip_pair_list {α : Type u} (l : list (α × α)) : list (α × α) :=
l^.map (λ ⟨p1, p2⟩, ⟨p2, p1⟩)

meta def remove_macros (e : expr) : tactic (expr × rb_map expr expr) :=
do ls ← (find_macros e)^.mfold [] (λ ex l, do mv ← infer_type ex >>= mk_meta_var, return ((ex, mv)::l)),
   replmap ← return $ rb_map.of_list ls,
   e' ← return $ e^.replace (λ ex _, replmap^.find ex),
   return (e', rb_map.of_list $ flip_pair_list ls)

meta def reinsert_macros (e : expr) (map : rb_map expr expr) : expr :=
e^.replace (λ ex _, map^.find ex)

--meta def reinsert_macros_in_mmexpr (m : mmexpr) (map : rb_map expr expr) : expr := sorry
-/

/-
  The following definitions are used to make pexprs out of various types.
-/
end mathematica

meta def pexpr_of_nat : ℕ → pexpr
| 0 := ```(0)
| 1 := ```(1)
| k := if k%2=0 then ```(bit0 %%(pexpr_of_nat (k/2))) else ```(bit1 %%(pexpr_of_nat (k/2)))

meta def pexpr_of_int : int → pexpr
| (int.of_nat n) := pexpr_of_nat n
| (int.neg_succ_of_nat n) := ```(-%%(pexpr_of_nat (n+1)))

/-
The type mmexpr reflects Mathematica expression syntax.
-/
/-inductive mmexpr : Type
| sym   : string → mmexpr
| mstr  : string → mmexpr
| mint  : int → mmexpr 
| app   : mmexpr → list mmexpr → mmexpr
| mreal : float → mmexpr -/

namespace tactic
namespace mathematica

section
variable [io.interface]
def write_file (fn : string) (cnts : string) (mode := io.mode.write) : io unit := do
h ← io.mk_file_handle fn io.mode.write,
io.fs.write h cnts.to_char_buffer,
io.fs.close h
end

/--
execute str evaluates str in Mathematica.
The evaluation happens in a unique context; declarations that are made during
evaluation will not be available in future evaluations.
-/
meta def execute (cmd : string) : tactic char_buffer :=
let cmd' := escape_term cmd ++ "&!",
    args := ["_target/deps/mathematica/client2.py"] in
if cmd'.length < 2040 then
  tactic.run_io  (λ i, @io.buffer_cmd i { cmd := "python2", args := args.append [escape_quotes cmd'] })
else do 
   path ← mathematica.temp_file_name "exch",
   tactic.run_io (λ i, @write_file i path cmd' io.mode.write),
   tactic.run_io (λ i, @io.buffer_cmd i { cmd := "python2", args := args.append ["-f", path] })

   
meta def execute_and_eval (cmd : string) : tactic mmexpr :=
execute cmd >>= parse_mmexpr_tac


-- run_cmd execute_and_eval "Directory[]" >>= trace
-- run_cmd trace $  mathematica.form_of_expr ↑`(5)
-- run_cmd trace $ (quote_string) (mathematica.form_of_expr ↑`(2) ++ "// LeanForm // Activate")

/-run_cmd execute (mathematica.form_of_expr ↑`(2) ++ "// LeanForm // Activate") >>= trace
variable x : ℤ
include x
example : true := by do
e ← to_expr ```(x*x - 2*x + 1),
--trace e.to_raw_fmt,
 execute_and_eval (mathematica.form_of_expr e ++ "// LeanForm // Activate // Factor") >>= trace,
triv-/


/-run_cmd execute "$ProcessID" >>= trace
run_cmd execute "Solve[x^2-2x+1==0]" >>= trace
run_cmd execute "Solve[x^2-2x+1==0]" >>= trace
run_cmd execute "Solve[x^2-2x+1==0]" >>= trace
run_cmd execute "Solve[x^2-2x+1==0]" >>= trace
run_cmd execute "Solve[x^2-2x+1==0]" >>= trace
run_cmd execute "$ProcessID" >>= trace-/

/--
execute_global str evaluates str in Mathematica.
The evaluation happens in the global context; declarations that are made during
evaluation will persist.
-/
meta constant execute_global : string → tactic expr

/--
Returns the path to {LEAN_ROOT}/extras/mathematica (TODO: FIX COMMENT)
-/
meta def extras_path : tactic string :=
do s ← run_io $ λ i, @io.cmd i {cmd := "pwd"},
   return $ strip_trailing_whitespace s ++ "/extras/"

end mathematica
end tactic


namespace mathematica
open mmexpr tactic


private meta def pexpr_mk_app : pexpr → list pexpr → pexpr
| fn [] := fn
| fn (h::t) := pexpr_mk_app (app fn h) t

section translation
open rb_lmap


@[reducible] meta def trans_env := rb_map string expr
meta def trans_env.empty := rb_map.mk string expr

meta def sym_trans_pexpr_rule := string × pexpr
meta def sym_trans_expr_rule := string × expr
meta def app_trans_pexpr_keyed_rule := string × (trans_env → list mmexpr → tactic pexpr)
meta def app_trans_expr_keyed_rule := string × (trans_env → list mmexpr → tactic expr)
meta def app_trans_pexpr_unkeyed_rule := trans_env → mmexpr → list mmexpr → tactic pexpr
meta def app_trans_expr_unkeyed_rule := trans_env → mmexpr → list mmexpr → tactic expr

-- databases

private meta def mk_sym_trans_pexpr_db (l : list name) : tactic (rb_lmap string pexpr) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr sym_trans_pexpr_rule) l,
   return $ of_list dcls

private meta def mk_sym_trans_expr_db (l : list name) : tactic (rb_lmap string expr) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr sym_trans_expr_rule) l,
   return $ of_list dcls

private meta def mk_app_trans_pexpr_keyed_db (l : list name) : 
     tactic (rb_lmap string (trans_env → list mmexpr → tactic pexpr)) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr app_trans_pexpr_keyed_rule) l,
   return $ of_list dcls

private meta def mk_app_trans_expr_keyed_db (l : list name) : 
     tactic (rb_lmap string (trans_env → list mmexpr → tactic expr)) := 
do dcls ← monad.mapm (λ n, mk_const n >>= eval_expr app_trans_expr_keyed_rule) l,
   return $ of_list dcls

private meta def mk_app_trans_pexpr_unkeyed_db (l : list name) : 
     tactic (list (trans_env → mmexpr → list mmexpr → tactic pexpr)) :=
monad.mapm (λ n, mk_const n >>= eval_expr app_trans_pexpr_unkeyed_rule) l

private meta def mk_app_trans_expr_unkeyed_db (l : list name) : 
     tactic (list (trans_env → mmexpr → list mmexpr → tactic expr)) :=
monad.mapm (λ n, mk_const n >>= eval_expr app_trans_expr_unkeyed_rule) l

@[user_attribute]
private meta def sym_to_pexpr_rule : user_attribute (rb_lmap string pexpr) unit :=
{ name := `sym_to_pexpr, 
  descr := "rule for translating a mmexpr.sym to a pexpr",
  cache_cfg := ⟨mk_sym_trans_pexpr_db, []⟩ }

@[user_attribute]
private meta def sym_to_expr_rule : user_attribute (rb_lmap string expr) unit :=
{ name := `sym_to_expr, 
  descr := "rule for translating a mmexpr.sym to a expr", 
  cache_cfg := ⟨mk_sym_trans_expr_db, []⟩ }

@[user_attribute]
private meta def app_to_pexpr_keyed_rule : 
        user_attribute (rb_lmap string (trans_env → list mmexpr → tactic pexpr)) :=
{ name := `app_to_pexpr_keyed, 
  descr := "rule for translating a mmexpr.app to a pexpr",
  cache_cfg := ⟨mk_app_trans_pexpr_keyed_db, []⟩ } 

@[user_attribute]
private meta def app_to_expr_keyed_rule : 
        user_attribute (rb_lmap string (trans_env → list mmexpr → tactic expr)) :=
{ name := `app_to_expr_keyed, 
  descr := "rule for translating a mmexpr.app to a expr",
  cache_cfg := ⟨mk_app_trans_expr_keyed_db, []⟩ }

@[user_attribute]
private meta def app_to_pexpr_unkeyed_rule : 
        user_attribute (list (trans_env → mmexpr → list mmexpr → tactic pexpr)) :=
{ name := `app_to_pexpr_unkeyed, 
  descr := "rule for translating a mmexpr.app to a pexpr",
  cache_cfg := ⟨mk_app_trans_pexpr_unkeyed_db, []⟩ }

@[user_attribute]
private meta def app_to_expr_unkeyed_rule : 
        user_attribute (list (trans_env → mmexpr → list mmexpr → tactic expr)) :=
{ name := `app_to_expr_unkeyed, 
  descr := "rule for translating a mmexpr.app to a expr",
  cache_cfg := ⟨mk_app_trans_expr_unkeyed_db, []⟩ }


private meta def expr_of_mmexpr_app_keyed (env : trans_env) : mmexpr → list mmexpr → tactic expr
| (sym hd) args :=
  do expr_db ← app_to_expr_keyed_rule.get_cache,
     tactic.first $ (find expr_db hd).for $ λ f, f env args
| _ _ := failed

private meta def expr_of_mmexpr_app_unkeyed (env : trans_env) (hd : mmexpr) (args : list mmexpr) : tactic expr :=
do expr_db ← app_to_expr_unkeyed_rule.get_cache,
   tactic.first (list.map (λ f : trans_env → mmexpr → list mmexpr → tactic expr, f env hd args) expr_db)

private meta def expr_of_mmexpr_app_decomp (env : trans_env) (expr_of_mmexpr : trans_env → mmexpr → tactic expr)
         (hd : mmexpr) (args : list mmexpr) : tactic expr := 
do hs ← expr_of_mmexpr env hd,
   args' ← monad.mapm (expr_of_mmexpr env) args,
   return $ expr.mk_app hs args'

private meta def expr_of_mmexpr_app (env : trans_env) (expr_of_mmexpr : trans_env → mmexpr → tactic expr)
         (m : mmexpr) (l : list mmexpr) : tactic expr :=
expr_of_mmexpr_app_keyed env m l <|> 
expr_of_mmexpr_app_unkeyed env m l <|> 
expr_of_mmexpr_app_decomp env expr_of_mmexpr m l

private meta def pexpr_of_mmexpr_app_keyed (env : trans_env) : mmexpr → list mmexpr → tactic pexpr
| (sym hd) args := 
  do expr_db ← app_to_pexpr_keyed_rule.get_cache,
     tactic.first $ (find expr_db hd).for $ λ f, f env args
| _ _ := failed


private meta def pexpr_of_mmexpr_app_unkeyed (env : trans_env) (hd : mmexpr) (args : list mmexpr) : tactic pexpr := 
do expr_db ← app_to_pexpr_unkeyed_rule.get_cache,
   tactic.first (list.map (λ f : trans_env → mmexpr → list mmexpr → tactic pexpr, f env hd args) expr_db)

private meta def pexpr_of_mmexpr_app_decomp (env : trans_env) (pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr)
         (hd : mmexpr) (args : list mmexpr) : tactic pexpr := 
do hs ← pexpr_of_mmexpr env hd,
   args' ← monad.mapm (pexpr_of_mmexpr env) args,
   return $ pexpr_mk_app hs args'

private meta def pexpr_of_mmexpr_app (env : trans_env) (pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr)
         (m : mmexpr) (l : list mmexpr) : tactic pexpr :=
pexpr_of_mmexpr_app_keyed env m l <|> 
pexpr_of_mmexpr_app_unkeyed env m l <|> 
pexpr_of_mmexpr_app_decomp env pexpr_of_mmexpr m l

private meta def find_in_env (env : trans_env) (sym : string) : tactic expr :=
match rb_map.find env sym with
| some e := return e
| none   := failed
end

/--
expr_of_mmexpr env m will attempt to translate m to an expr, using translation rules found by
the attribute manager. env maps symbols (representing bound variables) to placeholder exprs.
-/
meta def expr_of_mmexpr : trans_env → mmexpr → tactic expr
| env (sym s)       := find_in_env env s <|> 
  do expr_db ← sym_to_expr_rule.get_cache,
     match find expr_db s with
     | (h :: t) := return h
     | []       := fail ("Couldn't find translation for sym \"" ++ s ++ "\"")
     end
| env (mstr s)      := return (string.reflect s)--to_expr (_root_.quote s)
| env (mreal r)     := return (reflect r)
| env (app hd args) := expr_of_mmexpr_app env expr_of_mmexpr hd args 
| env (mint i)      := failed

private meta def pexpr_of_mmexpr_aux (env : trans_env) 
         (pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr) :  mmexpr → tactic pexpr
| (sym s)   := 
  do expr_db ← sym_to_pexpr_rule.get_cache,
     match find expr_db s with
     | (h :: t) := return h
     | []       := fail ("Couldn't find translation for sym \"" ++ s ++ "\"")
     end
| (mint i ) := return $ pexpr_of_int i
| (app hd args) := pexpr_of_mmexpr_app env pexpr_of_mmexpr hd args 
| (mstr s)   := fail "unreachable, str case shouldn't reach pexpr_of_mmexpr_aux"
| (mreal r) := fail "unreachable, real case shouldn't reach pexpr_of_mmexpr_aux"

/--
pexpr_of_mmexpr env m will attempt to translate m to a pexpr, using translation rules found by
the attribute manager. env maps symbols (representing bound variables) to placeholder exprs.
-/
meta def pexpr_of_mmexpr : trans_env → mmexpr → tactic pexpr := 
λ env m, (do e ← expr_of_mmexpr env m, return ```(%%e)) <|>
         (pexpr_of_mmexpr_aux env pexpr_of_mmexpr m)

end translation

section unreflect

meta def level_of_mmexpr : mmexpr → tactic level 
| (sym "LeanZeroLevel") := return $ level.zero
| (app (sym "LeanLevelSucc") [m])      := do m' ← level_of_mmexpr m, return $ level.succ m'
| (app (sym "LeanLevelMax") [m1, m2])  := 
  do m1' ← level_of_mmexpr m1, 
     m2' ← level_of_mmexpr m2, 
     return $ level.max m1' m2'
| (app (sym "LeanLevelIMax") [m1, m2]) := 
  do m1' ← level_of_mmexpr m1, 
     m2' ← level_of_mmexpr m2, 
     return $ level.imax m1' m2'
| (app (sym "LeanLevelParam") [mstr s]) := return $ level.param s
| (app (sym "LeanLevelMeta") [mstr s])  := return $ level.mvar s
| _ := failed

meta def level_list_of_mmexpr : mmexpr → tactic (list level) 
| (sym "LeanLevelListNil")               := return []
| (app (sym "LeanLevelListCons") [h, t]) := 
  do h' ← level_of_mmexpr h, 
     t' ← level_list_of_mmexpr t,
     return $ h' :: t'
| _ := failed

meta def name_of_mmexpr : mmexpr → tactic name 
| (sym "LeanNameAnonymous")                 := return $ name.anonymous
| (app (sym "LeanNameMkString") [mstr s, m]) := 
  do n ← name_of_mmexpr m, return $ name.mk_string s n
| (app (sym "LeanNameMkNum") [mint i, m])   := 
  do n ← name_of_mmexpr m, return $ name.mk_numeral (unsigned_of_int i) n
| _ := failed

meta def binder_info_of_mmexpr : mmexpr → tactic binder_info 
| (sym "BinderInfoDefault")        := return $ binder_info.default 
| (sym "BinderInfoImplicit")       := return $ binder_info.implicit 
| (sym "BinderInfoStrictImplicit") := return $ binder_info.strict_implicit
| (sym "BinderInfoInstImplicit")   := return $ binder_info.inst_implicit
| (sym "BinderInfoOther")          := return $ binder_info.aux_decl
| _ := failed
end unreflect

section transl_expr_instances

@[app_to_expr_keyed]
meta def mmexpr_var_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanVar", 
λ _ args, match args with
| [mint i] := return $ var (i.nat_abs)
| _        := failed
end⟩ 

@[app_to_expr_keyed]
meta def mmexpr_sort_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanSort",
λ _ args, match args with
| [m] := do lvl ← level_of_mmexpr m, return $ sort lvl
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_const_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanConst",
λ _ args, match args with
| [nm, lvls] := do nm' ← name_of_mmexpr nm, lvls' ← level_list_of_mmexpr lvls, return $ const nm' lvls'
| _          := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_mvar_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanMetaVar",
λ env args, match args with
| [nm, tp] := do nm' ← name_of_mmexpr nm, tp' ← expr_of_mmexpr env tp, return $ mvar nm' `workaround tp'
| _        := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_local_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanLocal",
λ env args, match args with
| [nm, ppnm, bi, tp] := 
  do nm' ← name_of_mmexpr nm, 
     ppnm' ← name_of_mmexpr ppnm, 
     bi' ← binder_info_of_mmexpr bi, 
     tp' ← expr_of_mmexpr env tp, 
     return $ expr.local_const nm' ppnm' bi' tp'
| _ := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_app_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanApp",
λ env args, match args with
| [hd, bd] := do hd' ← expr_of_mmexpr env hd, bd' ← expr_of_mmexpr env bd, return $ expr.app hd' bd'
| _        := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_lam_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanLambda",
λ env args, match args with
| [nm, bi, tp, bd] :=
  do nm' ← name_of_mmexpr nm, 
     bi' ← binder_info_of_mmexpr bi, 
     tp' ← expr_of_mmexpr env tp,
     bd' ← expr_of_mmexpr env bd,
     return $ lam nm' bi' tp' bd'
| _   := failed
end⟩

@[app_to_expr_keyed]
meta def mmexpr_pi_to_expr : app_trans_expr_keyed_rule :=
⟨"LeanPi",
λ env args, match args with
| [nm, bi, tp, bd] := 
  do nm' ← name_of_mmexpr nm, 
     bi' ← binder_info_of_mmexpr bi, 
     tp' ← expr_of_mmexpr env tp,
     bd' ← expr_of_mmexpr env bd,
     return $ lam nm' bi' tp' bd'
| _ := failed
end⟩

meta def pexpr_fold_op_aux (op : pexpr) : pexpr → list pexpr → pexpr
| e [] := e
| e (h::t) := pexpr_fold_op_aux ```(%%op %%e %%h) t

meta def pexpr_fold_op (dflt op : pexpr) : list pexpr → pexpr
| [] := dflt
| [h] := h
| (h::t) := pexpr_fold_op_aux op h t

-- pexpr instances

@[app_to_pexpr_keyed]
meta def add_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Plus", 
λ env args, do args' ← list.mfor args (pexpr_of_mmexpr env), return $ pexpr_fold_op ```(0) ```(has_add.add) args'⟩

@[app_to_pexpr_keyed]
meta def mul_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Times", 
λ env args, do args' ← list.mfor args (pexpr_of_mmexpr env), return $ pexpr_fold_op ```(1) ```(has_mul.mul) args'⟩

@[app_to_pexpr_keyed]
meta def list_to_pexpr : app_trans_pexpr_keyed_rule := 
⟨"List", λ env args, 
         do args' ← list.mfor args (pexpr_of_mmexpr env), 
            return $ list.foldr (λ h t, ```(%%h :: %%t)) ```([]) args'⟩

@[app_to_pexpr_keyed]
meta def and_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"And", 
λ env args, do args' ← list.mfor args (pexpr_of_mmexpr env), return $ pexpr_fold_op ```(true) ```(and) args'⟩

@[app_to_pexpr_keyed]
meta def or_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Or", 
λ env args, do args' ← list.mfor args (pexpr_of_mmexpr env), return $ pexpr_fold_op ```(false) ```(or) args'⟩

@[app_to_pexpr_keyed]
meta def not_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Not",
λ env args, match args with
 | [t] := do t' ← pexpr_of_mmexpr env t, return ```(¬ %%t')
 | _   := failed
 end⟩

@[app_to_pexpr_keyed]
meta def implies_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Implies",
λ env args, match args with
 | [h,c] := do h' ← pexpr_of_mmexpr env h, c' ← pexpr_of_mmexpr env c, return $ ```(%%h' → %%c')
 | _   := failed
 end⟩

meta def pexpr.to_raw_expr : pexpr → expr
| (var n)                     := var n
| (sort l)                    := sort l
| (const nm ls)               := const nm ls
| (mvar n n' e)                  := mvar n n' (pexpr.to_raw_expr e)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (pexpr.to_raw_expr tp)
| (app f a)                   := app (pexpr.to_raw_expr f) (pexpr.to_raw_expr a)
| (lam nm bi tp bd)           := lam nm bi (pexpr.to_raw_expr tp) (pexpr.to_raw_expr bd)
| (pi nm bi tp bd)            := pi nm bi (pexpr.to_raw_expr tp) (pexpr.to_raw_expr bd)
| (elet nm tp df bd)          := elet nm (pexpr.to_raw_expr tp) (pexpr.to_raw_expr df) (pexpr.to_raw_expr bd)
| (macro md l)                := macro md (l.map pexpr.to_raw_expr)

meta def pexpr.of_raw_expr : expr → pexpr
| (var n)                     := var n
| (sort l)                    := sort l
| (const nm ls)               := const nm ls
| (mvar n n' e)                  := mvar n n' (pexpr.of_raw_expr e)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (pexpr.of_raw_expr tp)
| (app f a)                   := app (pexpr.of_raw_expr f) (pexpr.of_raw_expr a)
| (lam nm bi tp bd)           := lam nm bi (pexpr.of_raw_expr tp) (pexpr.of_raw_expr bd)
| (pi nm bi tp bd)            := pi nm bi (pexpr.of_raw_expr tp) (pexpr.of_raw_expr bd)
| (elet nm tp df bd)          := elet nm (pexpr.of_raw_expr tp) (pexpr.of_raw_expr df) (pexpr.of_raw_expr bd)
| (macro md l)                := macro md (l.map pexpr.of_raw_expr)


meta def mk_local_const_placeholder (n : name) : expr :=
let t := pexpr.mk_placeholder in
local_const n n binder_info.default (pexpr.to_raw_expr t)


private meta def sym_to_lcp : mmexpr → tactic (string × expr)
| (sym s) := return $ (s, mk_local_const_placeholder s)
| _ := failed

meta def mk_lambdas (l : list expr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (lambdas l (pexpr.to_raw_expr b))

meta def mk_lambda' (x : expr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (lambdas [x] (pexpr.to_raw_expr b))

meta def mk_pis (l : list expr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (pis l (pexpr.to_raw_expr b))

meta def mk_pi' (x : expr) (b : pexpr) : pexpr :=
pexpr.of_raw_expr (pis [x] (pexpr.to_raw_expr b))

@[app_to_pexpr_keyed]
meta def function_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"Function",
λ env args, match args with
| [sym x, bd] := 
  do v ← return $ mk_local_const_placeholder x, 
     bd' ← pexpr_of_mmexpr (env.insert x v) bd,
     return $ mk_lambda' v bd' 
| [app (sym "List") l, bd] :=
  do vs ← list.mfor l sym_to_lcp,
     bd' ← pexpr_of_mmexpr (env.insert_list vs) bd,
     return $ mk_lambdas (list.map prod.snd vs) bd'
| _ := failed
end⟩

@[app_to_pexpr_keyed]
meta def forall_to_pexpr : app_trans_pexpr_keyed_rule :=
⟨"ForAll",
λ env args, match args with
| [sym x, bd] := 
  do v ← return $ mk_local_const_placeholder x, 
     bd' ← pexpr_of_mmexpr (env.insert x v) bd,
     return $ mk_pi' v bd' 
| [app (sym "List") l, bd] :=
  do vs ← list.mfor l sym_to_lcp,
     bd' ← pexpr_of_mmexpr (env.insert_list vs) bd,
     return $ mk_pis (list.map prod.snd vs) bd'
| [sym x, t, bd] := 
  do v ← return $ mk_local_const_placeholder x,
     bd' ← pexpr_of_mmexpr (env.insert x v) (app (sym "Implies") [t,bd]),
     return $ mk_pi' v bd'
| _ := failed
end⟩

@[sym_to_pexpr]
meta def rat_to_pexpr : sym_trans_pexpr_rule :=
⟨"Rational", ```(has_div.div)⟩ 


end transl_expr_instances
end mathematica

-- user-facing tactics
namespace tactic
namespace mathematica
open mathematica

meta def mk_get_cmd (path : string) : tactic string :=
do s ← extras_path,
   return $ "Get[\"" ++ path ++ "\",Path->{DirectoryFormat[\""++ s ++"\"]}];"

/--
load_file path will load the file found at path into Mathematica.
The declarations will persist until the kernel is restarted.
-/
meta def load_file (path : string) : tactic unit :=
do s ← mk_get_cmd path,
   execute_global s >> return ()

/--
run_command_on cmd e reflects e into Mathematica syntax, applies cmd to this reflection,
evaluates this in Mathematica, and attempts to translate the result to a pexpr.
-/
meta def run_command_on (cmd : string → string) (e : expr) : tactic pexpr := 
do rval ← execute_and_eval $ cmd $ form_of_expr e,
   --rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval

/--
run_command_on_using cmd e path reflects e into Mathematica syntax, applies cmd to this reflection,
evaluates this in Mathematica after importing the file at path, and attempts to translate the result to a pexpr.
-/
meta def run_command_on_using (cmd : string → string) (e : expr) (path : string) : tactic pexpr := 
do p ← escape_slash <$> mk_get_cmd path,
   run_command_on (λ s, p ++ cmd s) e

meta def run_command_on_2 (cmd : string → string → string) (e1 e2 : expr) : tactic pexpr :=
do rval ← execute_and_eval $ cmd (form_of_expr e1) (form_of_expr e2),
   --rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval

/--
run_command_on_2_using cmd e1 e2 reflects e1 and e2 into Mathematica syntax, 
applies cmd to these reflections, evaluates this in Mathematica after importing the file at path, 
and attempts to translate the result to a pexpr.
-/
meta def run_command_on_2_using (cmd : string → string → string) (e1 e2 : expr) (path : string) :
     tactic pexpr :=
do p ← escape_slash <$> mk_get_cmd path,
  run_command_on_2 (λ s1 s2, p ++ cmd s1 s2) e1 e2

private def sep_string : list string → string
| [] := ""
| [s] := s
| (h::t) := h ++ ", " ++ sep_string t

/--
run_command_on_list cmd l reflects each element of l into Mathematica syntax, 
applies cmd to a Mathematica list of these reflections,
evaluates this in Mathematica, and attempts to translate the result to a pexpr.
-/
meta def run_command_on_list (cmd : string → string) (l : list expr) : tactic pexpr :=
let lvs := "{" ++ (sep_string $ l.map form_of_expr) ++ "}" in
do rval ← execute_and_eval $ cmd lvs,
   --rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval


meta def run_command_on_list_using (cmd : string → string) (l : list expr) (path : string) : tactic pexpr :=
let lvs := "{" ++ (sep_string $ l.map form_of_expr) ++ "}" in
do p ← mk_get_cmd path,
   rval ← execute_and_eval $ p ++ cmd lvs,
   --rval' ← eval_expr mmexpr rval,
   pexpr_of_mmexpr trans_env.empty rval

end mathematica
end tactic
