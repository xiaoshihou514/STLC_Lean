import STLCLean.inference

/-- Type assignment checker
    Returns `some ty` if `t` can be assigned type `ty` in context `ctx`, or `none` if the term
    is ill-typed.
    * `.var c`: look up `c` in the context.
    * `.abs x m`: check `m`, look up `x`'s type, and form the arrow type `x.ty → m.ty`.
    * `.app m n`: check both `m` and `n`; require `m : domain → ty` and `n : domain`. -/
@[grind]
def check (ctx : TypeCtx) (t : Term) : Option CurryType :=
  match t with
  | .var c => ctx.lookup c
  | .abs x m =>
    match check ctx m with
    | none => none
    | some ty => match ctx.lookup x with
      | none => none
      | some ty' => some <| CurryType.arrow ty' ty
  | .app m n =>
    match check ctx m, check ctx n with
    | some ty_m, some ty_n =>
      match ty_m with
      | .arrow a b => if a == ty_n then some b else none
      | _ => none
    | _, _ => none

/-- Predicate asserting that term `t` has type `ty` in context `ctx`.
    Defined as the decidable proposition `check ctx t = some ty`. -/
@[grind]
def WellTyped (ctx : TypeCtx) (t : Term) (ty : CurryType) : Prop :=
  check ctx t = some ty

def runTest' (name : String) (t : Term) : String :=
  match pp t with
  | some pair => match check pair.ctx t with
    | some ty => if ty == pair.ty then
        s!"✅ [{name}] {t}: {pair}"
        else
          s!"❌ [{name}] {t}: {pair}, expects {ty}"
    | none => "Check failed"
  | _ => "Inference failed"

#eval runTest' "type of single variable x" (Term.var 'x')
#eval runTest' "type of another variable y" (Term.var 'y')

#eval runTest' "type of identity function" (Term.abs 'x' (Term.var 'x'))
#eval runTest' "type of constant function" 
  (Term.abs 'x' (Term.abs 'y' (Term.var 'x')))

#eval runTest' "type of simple application" (Term.app (Term.var 'f') (Term.var 'x'))
#eval runTest' "type of left-associative application" 
  (Term.app (Term.app (Term.var 'f') (Term.var 'x')) (Term.var 'y'))
#eval runTest' "type of application with abstraction" 
  (Term.app (Term.abs 'x' (Term.var 'x')) (Term.var 'y'))

-- S: λx.λy.λz.(x z)(y z)
#eval runTest' "type of S combinator" 
  (Term.abs 'x' 
    (Term.abs 'y' 
      (Term.abs 'z' 
        (Term.app 
          (Term.app (Term.var 'x') (Term.var 'z')) 
          (Term.app (Term.var 'y') (Term.var 'z'))))))

-- K: λx.λy.x
#eval runTest' "type of K combinator" 
  (Term.abs 'x' (Term.abs 'y' (Term.var 'x')))

-- comp: λf.λg.λx.f (g x)
#eval runTest' "type of function composition" 
  (Term.abs 'f' 
    (Term.abs 'g' 
      (Term.abs 'x' 
        (Term.app (Term.var 'f') (Term.app (Term.var 'g') (Term.var 'x'))))))
