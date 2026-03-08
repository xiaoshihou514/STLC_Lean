import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.RelClasses
import Mathlib.Data.Set.Card

inductive CurryType : Type
| phi : Char → CurryType
| arrow : CurryType → CurryType → CurryType
deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

inductive Term : Type
| var : Char → Term
| abs : Char → Term → Term
| app : Term → Term → Term
deriving Repr

structure TypeCtx where
  env : List (Char × CurryType)
  label : Char
deriving Repr

def emptyEnv : TypeCtx := ⟨[], 'A'⟩

@[grind]
def union (ctx1 ctx2 : TypeCtx) : TypeCtx :=
  ⟨ctx1.env ++ ctx2.env, if ctx1.label > ctx2.label then ctx1.label else ctx2.label⟩

@[grind]
def next (ctx : TypeCtx) : (CurryType × TypeCtx) :=
  (CurryType.phi (Char.ofNat (ctx.label.toNat + 1)), ⟨ctx.env, Char.ofNat (ctx.label.toNat + 1)⟩)

@[grind]
def add (c : Char) (ty : CurryType) (ctx : TypeCtx) : TypeCtx :=
  ⟨(c, ty) :: ctx.env, ctx.label⟩

@[grind]
def applySubst (f : CurryType → CurryType) (ctx : TypeCtx) : TypeCtx :=
  ⟨ctx.env.map (fun (c, ty) => (c, f ty)), ctx.label⟩

structure PrincipalPair where
  ctx : TypeCtx
  ty : CurryType
deriving Repr

partial def curryTypeToString : CurryType → String
  | .phi p => s!"{p}"
  | .arrow a b => s!"({curryTypeToString a} -> {curryTypeToString b})"

instance : ToString CurryType := ⟨curryTypeToString⟩

partial def termToString : Term → String
  | .var c => s!"{c}"
  | .abs x m => s!"(λ{x}. {termToString m})"
  | .app m n => s!"({termToString m} {termToString n})"

instance : ToString Term := ⟨termToString⟩

instance : ToString PrincipalPair where
  toString res := 
    let env := res.ctx.env.map (fun (c, ty) => s!"{c}: {ty}")
    s!"[{", ".intercalate env}] ⊢ {res.ty}"

instance [ToString α] : ToString (Option α) where
  toString 
    | some x => toString x
    | none   => "Type Error"

/-- Check whether type variable `p` occurs (free) in type `τ`.
    Used in the occurs-check of `unify` to prevent circular substitutions. -/
@[grind]
def occursIn (p : Char) : CurryType → Bool
| .phi q => p == q
| .arrow a b => occursIn p a || occursIn p b

/-- Substitute type variable `x` with type `ty` throughout the given type.
    The caller must ensure the occurs-check holds (i.e., `¬occursIn x ty`) to
    prevent introducing a cyclic type. -/
@[grind]
def replaceVar (x : Char) (ty : CurryType) : CurryType → CurryType
| .phi y => if y == x then ty else .phi y
| .arrow a b => CurryType.arrow (replaceVar x ty a) (replaceVar x ty b)

/-- Compute the set of free type variables in a `CurryType`.
    Used as the primary component of the lexicographic termination measure for `unify`:
    cardinality of `vars left ∪ vars right` must decrease (or stay equal with size decreasing)
    across recursive calls. -/
@[grind]
def vars : CurryType → Finset Char
  | .phi p => {p}
  | .arrow a b => vars a ∪ vars b

/-- Compute the structural size (number of syntax-tree nodes) of a `CurryType`.
    Used as the secondary component of the termination measure for `unify`:
    when the variable-cardinality component stays equal, size must strictly decrease. -/
@[grind]
def size : CurryType → ℕ
  | .phi _ => 1
  | .arrow a b => 1 + size a + size b

/-- Every `CurryType` has strictly positive size. Used as a termination witness for `unify`. -/
@[grind .]
theorem SizeGtZ : ∀ ty, size ty > 0 := by
  intro ty
  induction ty with
  | phi p => grind
  | arrow p q indp indq => grind

/-- The free type variables of any type are a subset of the free variables of any arrow type
    built from it. Used as a termination witness for `unify`. -/
@[grind .]
theorem VarsArrow : ∀ ty ty', vars ty ⊆ vars (ty.arrow ty') := by
  intro ty ty'
  nth_rw 2 [vars.eq_def]
  simp

/-- A type substitution witnessing that `left` and `right` can be unified.
    Carries `apply : CurryType → CurryType` together with three invariants used to
    prove termination of `unify`:
    * `vars_decreased`: the free variables of any image are bounded by those of `left`, `right`,
      and the input type's own variables.
    * `vars_eq_then_id`: if the variable-cardinality does not decrease, `apply` is the identity.
    * `subst_rec`: `apply` distributes over arrow types. -/
structure Subst (left right : CurryType) where
  apply : CurryType → CurryType
  vars_decreased: 
    ∀ ty, vars (apply ty) ⊆ (vars left) ∪ (vars right) ∪ (vars ty)
  vars_eq_then_id:
    ∀ ty, (vars (apply ty)).card = ((vars left) ∪ (vars right) ∪ (vars ty)).card → apply = id
  subst_rec: ∀ a b, apply (.arrow a b) = .arrow (apply a) (apply b)
  uleft: CurryType
  uright: CurryType

/-- The identity substitution. `apply` is `id`, so all invariants hold trivially. -/
@[grind]
def Subst.id (left right : CurryType) : Subst left right where
  apply := _root_.id
  uleft := left
  uright := right
  vars_decreased := by grind
  vars_eq_then_id := by grind
  subst_rec := by grind

/-- Substituting `ty` for `a` in any type `ty1` can only introduce variables already present
    in `ty` (where `a` was replaced). All free variables of the result lie within
    `vars (.phi a) ∪ vars ty ∪ vars ty1`. -/
theorem ReplaceVarScope (a : Char) (ty : CurryType)
    : ∀ (ty1 : CurryType), vars (replaceVar a ty ty1) ⊆ vars (.phi a) ∪ vars ty ∪ vars ty1 := by
  intro ty1
  induction ty1 with
  | phi b =>
    simp only [replaceVar, beq_iff_eq, vars, Finset.singleton_union, Finset.union_singleton]
    by_cases h : b = a
    · -- b = a: replaceVar substitutes ty; vars ty ⊆ RHS by construction
      simp [h]
    · -- b ≠ a: replaceVar leaves .phi b unchanged; {b} ⊆ RHS trivially
      grind
  -- By ind. hyp.
  | arrow t1 t2 ih1 ih2 => grind

/-- Membership in `vars` implies `occursIn`: if `c ∈ vars τ` then `occursIn c τ = true`.
    Connects the `Finset`-based and `Bool`-based representations of free-variable occurrence. -/
theorem OccursInIffInVars {c : Char} {τ : CurryType} : c ∈ vars τ → occursIn c τ = true := by
  induction τ with
  | phi d => grind
  | arrow τ1 τ2 ih1 ih2 => grind

/-- After substituting `ty` for `a`, the variable `a` no longer appears in the result.
    The occurs-check condition `¬occursIn a ty` prevents `a` from being reintroduced via `ty`. -/
theorem ReplaceElim (a : Char) (ty : CurryType) (ho : ¬occursIn a ty) (t : CurryType) :
    a ∉ vars (replaceVar a ty t) := by
  induction t with
  | phi b =>
    simp only [replaceVar, beq_iff_eq]
    by_cases hb : b = a
    · -- b = a: replaceVar substitutes ty, and a ∉ vars ty by ho + OccursInIffInVars
      simp only [hb, ↓reduceIte]
      by_contra hmem
      have := OccursInIffInVars hmem
      contradiction
    · -- b ≠ a: replaceVar leaves .phi b unchanged, so a ∉ {b}
      grind
  -- By ind. hyp.
  | arrow t1 t2 ih1 ih2 => grind

/-- The variable count can never stay equal after a `replaceVar` substitution.
    Formally, `(vars (replaceVar a ty ty')).card ≠ (vars (.phi a) ∪ vars ty ∪ vars ty').card`.
    This is used to show that `Subst.replace` satisfies `vars_eq_then_id` by contradiction:
    if cardinalities were equal, subset equality would follow (by `ReplaceVarScope`), but
    `a` is in the RHS (`vars (.phi a)`) and absent from the LHS (`ReplaceElim`). -/
theorem ReplaceAddsNewVars (a : Char) (ty : CurryType) (ho : ¬occursIn a ty) (ty' : CurryType) :
    ¬ ((vars (replaceVar a ty ty')).card = (vars (.phi a) ∪ vars ty ∪ vars ty').card) := by
  intro h
  have sub := ReplaceVarScope a ty ty'          -- LHS ⊆ RHS as sets
  have ain : a ∈ vars (.phi a) ∪ vars ty ∪ vars ty' := by simp [vars]  -- a ∈ RHS
  have aout : a ∉ vars (replaceVar a ty ty') := by  -- a ∉ LHS
    induction ty' with
    | phi b =>
      simp only [replaceVar, beq_iff_eq]
      by_cases hb : b = a
      · simp only [hb, ↓reduceIte]
        -- result is ty; use ho to show a ∉ vars ty via OccursInIffInVars
        have : a ∉ vars ty := by
          intro hmem
          have := OccursInIffInVars hmem
          grind
        exact this
      · grind  -- b ≠ a: result is .phi b, and a ≠ b
    -- By ind. hyp.
    | arrow t1 t2 ih1 ih2 =>
      simp only [replaceVar, vars, Finset.mem_union, not_or]
      constructor
      · exact ReplaceElim a ty ho t1  -- a ∉ vars (replaceVar a ty t1)
      · exact ReplaceElim a ty ho t2  -- a ∉ vars (replaceVar a ty t2)
  -- Equal cardinality + subset implies set equality, but a ∈ RHS and a ∉ LHS — contradiction
  have := Finset.eq_of_subset_of_card_le sub (le_of_eq h.symm)
  grind

/-- Substitution that replaces type variable `a` with `ty` everywhere, given the occurs-check
    `¬occursIn a ty`. -/
@[grind]
def Subst.replace (a : Char) (ty : CurryType) (ho : ¬occursIn a ty) : Subst (.phi a) ty where
  apply := replaceVar a ty
  uleft := .phi a
  uright := ty
  vars_decreased := by
    intro ty1
    induction ty1 with
    | phi b =>
      simp only [replaceVar, beq_iff_eq, vars, Finset.singleton_union, Finset.union_singleton]
      by_cases h : b = a
      · simp [h]   -- b = a: result is ty; vars ty ⊆ vars (.phi a) ∪ vars ty ∪ _ by construction
      · grind       -- b ≠ a: result is .phi b; {b} ⊆ vars (.phi a) ∪ vars ty ∪ {b}
    | arrow t1 t2 ih1 ih2 => grind
  vars_eq_then_id := by
    intro ty' h
    -- If cardinalities are equal, ReplaceAddsNewVars gives a contradiction
    exfalso
    exact ReplaceAddsNewVars a ty ho ty' h
  subst_rec := by grind

/-- Like `Subst.replace` but with the `Subst` type indices swapped (`Subst ty (.phi a)` instead
    of `Subst (.phi a) ty`). The underlying function is the same (`replaceVar a ty`);
    invariants delegate to `ReplaceVarScope` and `ReplaceAddsNewVars`. -/
@[grind]
def Subst.replacer (a : Char) (ty : CurryType) (ho : ¬occursIn a ty) : Subst ty (.phi a) where
  apply := replaceVar a ty
  uleft := .phi a
  uright := ty
  vars_decreased := by
    intro t
    have h := ReplaceVarScope a ty t
    grind  -- ReplaceVarScope gives the required subset; grind reorders the union to match the goal
  vars_eq_then_id := by
    intro ty' h
    exfalso
    -- Reorder the union to match the shape expected by ReplaceAddsNewVars, then apply it
    have h' : (vars (replaceVar a ty ty')).card = (vars (.phi a) ∪ vars ty ∪ vars ty').card := by
      grind
    exact ReplaceAddsNewVars a ty ho ty' h'
  subst_rec := by grind

/-- Composition of two substitutions. Given `s1 : Subst a c` and
    `s2 : Subst (s1.apply b) (s1.apply d)`, their composition `s2 ∘ s1` is a
    `Subst (.arrow a b) (.arrow c d)`.
    * `vars_decreased`: chain the two subset inclusions via `calc`.
    * `vars_eq_then_id`: if the composition is variable-count-preserving, derive that `s2 = id`
      (by cardinality squeeze on s2's image), then that `s1 = id` similarly.
    * `subst_rec`: each factor distributes over arrows; compose the two equations. -/
def Subst.comp
  (s1 : Subst a c)
  (s2 : Subst (s1.apply b) (s1.apply d))
: Subst (.arrow a b) (.arrow c d) where
  apply := s2.apply ∘ s1.apply
  uleft := .arrow a b
  uright := .arrow c d
  vars_decreased := by
    intro ty
    -- Chain the two subset inclusions: s2 maps into s1's image; s1 maps into a,c,ty
    calc
      vars ((s2.apply ∘ s1.apply) ty)
        ⊆ vars (s1.apply b) ∪ vars (s1.apply d) ∪ vars (s1.apply ty)
      := s2.vars_decreased (s1.apply ty)
      _ ⊆ ((vars a ∪ vars c ∪ vars b) ∪ (vars a ∪ vars c ∪ vars d)) ∪ (vars a ∪ vars c ∪ vars ty)
      := by
        -- Apply s1.vars_decreased to b, d, and ty separately, then take unions
        apply Finset.union_subset_union
        · apply Finset.union_subset_union
          · exact s1.vars_decreased b
          · exact s1.vars_decreased d
        · exact s1.vars_decreased ty
      _ = vars a ∪ vars b ∪ vars c ∪ vars d ∪ vars ty := by grind
      _ = vars (.arrow a b) ∪ vars (.arrow c d) ∪ vars ty := by simp [vars]
  vars_eq_then_id := by
    intro ty h
    -- Unfold the composition so h involves (s2.apply (s1.apply ty))
    simp only [Function.comp, Finset.union_assoc] at h
    -- Let U be the combined variable set of all four types
    let U := vars a ∪ vars b ∪ vars c ∪ vars d
    have hU : U = vars (.arrow a b) ∪ vars (.arrow c d) := by grind
    rw [← Finset.union_assoc] at h
    rw [← hU] at h  -- h : (vars (s2.apply (s1.apply ty))).card = (U ∪ vars ty).card
    have h1 := s1.vars_decreased ty  -- vars (s1.apply ty) ⊆ vars a ∪ vars c ∪ vars ty
    have hb := s1.vars_decreased b
    have hd := s1.vars_decreased d
    have h2 := s2.vars_decreased (s1.apply ty)
    -- Squeeze: U ∪ vars ty ≤ card(s1 images) ≤ U ∪ vars ty, so they are equal in cardinality
    have le1' :
      (U ∪ vars ty).card ≤
      (vars (s1.apply b) ∪ vars (s1.apply d) ∪ vars (s1.apply ty)).card
    := by
      rw [← h]
      exact Finset.card_le_card h2
    have le2 :
      (vars (s1.apply b) ∪ vars (s1.apply d) ∪ vars (s1.apply ty)).card ≤
      (U ∪ vars ty).card
    := by
      apply Finset.card_le_card
      grind
    have eq_card :
      (vars (s1.apply b) ∪ vars (s1.apply d) ∪ vars (s1.apply ty)).card =
      (U ∪ vars ty).card
    := by grind
    -- Cardinality equality + subset → set equality
    have eq_set : vars (s1.apply b) ∪ vars (s1.apply d) ∪ vars (s1.apply ty) = U ∪ vars ty :=
      Finset.eq_of_subset_of_card_le
        (Finset.Subset.trans (Finset.union_subset_union
          (Finset.union_subset_union hb hd) h1) (by grind))
        (le_of_eq eq_card.symm)
    -- Rewrite h so its RHS is the s1-image union, then apply vars_eq_then_id to s2
    rw [← eq_set] at h
    -- h : (vars (s2.apply (s1.apply ty))).card =
    --     (vars (s1.apply b) ∪ vars (s1.apply d) ∪ vars (s1.apply ty)).card
    have s2_id : s2.apply = _root_.id := s2.vars_eq_then_id (s1.apply ty) h
    rw [s2_id] at h
    simp only [id_eq, Finset.union_assoc] at h
    -- h : (vars (s1.apply ty)).card = (U ∪ vars ty).card
    -- Show vars (s1.apply ty) ⊆ U ∪ vars ty via the chain through vars a ∪ vars c ∪ vars ty
    have sub1 : vars (s1.apply ty) ⊆ vars a ∪ vars c ∪ vars ty := h1
    have sub2 : vars a ∪ vars c ∪ vars ty ⊆ U ∪ vars ty := by grind
    have sub := Finset.Subset.trans sub1 sub2
    -- Cardinality equality + subset → vars (s1.apply ty) = U ∪ vars ty as sets
    have eq1 : vars (s1.apply ty) = U ∪ vars ty := by
      rw [← Finset.union_assoc] at h
      rw [eq_set] at h
      exact Finset.eq_of_subset_of_card_le sub (le_of_eq h.symm)
    rw [eq1] at sub1
    -- Derive U ∪ vars ty = vars a ∪ vars c ∪ vars ty by antisymmetry
    have eq_union : U ∪ vars ty = vars a ∪ vars c ∪ vars ty := by
      apply Finset.Subset.antisymm
      · grind  -- uses h1: vars (s1.apply ty) ⊆ vars a ∪ vars c ∪ vars ty
      · assumption
    rw [eq_union] at eq1  -- eq1 : vars (s1.apply ty) = vars a ∪ vars c ∪ vars ty
    -- Apply vars_eq_then_id to s1 to conclude s1 = id
    have s1_id : s1.apply = _root_.id := s1.vars_eq_then_id ty (by rw [eq1])
    -- Both factors are identity, so their composition is identity
    rw [← s1_id, s2_id]
    rfl
  -- By ind. hyp.
  subst_rec := by
    intro a1 b1
    simp only [Function.comp_apply, s1.subst_rec, s2.subst_rec]

/-- Unification of two `CurryType`s. Returns a `Subst left right` whose `apply` unifies the two
    types, or `none` if no unifier exists (fails occurs check).
    Termination measure: `((vars left ∪ vars right).card, size left + size right)` lexicographically
    * φp = φq: identity if equal, otherwise `replace p (φq)`.
    * φp, non-variable: occurs check; if clear, `replace p ty`.
    * arrow cases: unify heads with `s1`, then unify `s1`-images of tails with `s2`; compose.
    * non-variable, φp: symmetric to the φp case. -/
def unify (left right : CurryType) : Option (Subst left right) :=
  match left, right with
  | .phi p, .phi q => 
    if ho: p = q then 
      some <| Subst.id (.phi p) (.phi q)
    else
      some <| Subst.replace p (.phi q) (by grind)
  | .phi p, ty =>
    if ho: occursIn p ty then 
      none
    else 
      some <| Subst.replace p ty (by grind)
  | .arrow a b, .arrow c d =>
    match unify a c with
    | none => none
    | some s1 =>
      match unify (s1.apply b) (s1.apply d) with
      | none => none
      | some s2 => some <| Subst.comp s1 s2
  | ty, .phi p =>
    if ho: occursIn p ty then 
      none
    else 
      some <| Subst.replacer p ty (by grind)
  termination_by ((vars left ∪ vars right).card, size left + size right)
  decreasing_by
  -- First recursive call: unify a c from the arrow a b, arrow c d case.
  -- The measure for (a, c) is ≤ that of (a.arrow b, c.arrow d); show it is strictly smaller.
  · simp only [Prod.lex_def]
    by_cases hl: (vars a ∪ vars c).card < (vars (a.arrow b) ∪ vars (c.arrow d)).card
    · left  -- cardinality strictly decreased
      assumption
    · right
      constructor
      · -- cardinality did not decrease: VarsArrow gives a ⊆ a.arrow b and c ⊆ c.arrow d,
        -- so card(a ∪ c) ≤ card(a.arrow b ∪ c.arrow d); combined with ¬< gives equality
        have :=
            Finset.card_le_card (Finset.union_subset_union (VarsArrow a b) (VarsArrow c d))
        grind
      · grind  -- size a + size c < size (a.arrow b) + size (c.arrow d) by definition of `size`
  -- Second recursive call: unify (s1.apply b) (s1.apply d).
  -- The measure for (s1 b, s1 d) must be strictly smaller than for (a.arrow b, c.arrow d).
  · simp only [Prod.lex_def]
    by_cases hl: (vars (s1.apply b) ∪ vars (s1.apply d)).card <
                 (vars (a.arrow b) ∪ vars (c.arrow d)).card
    · left  -- cardinality strictly decreased
      assumption
    · right
      have hb := s1.vars_decreased b
      have hd := s1.vars_decreased d
      -- s1's images stay within the union of all four types' variables
      have h:
        vars (s1.apply b) ∪ vars (s1.apply d) ⊆ vars a ∪ vars c ∪ vars b ∪ vars d := by
        grind
      -- Unwrap vars (.arrow _ _)
      nth_rw 3 [vars.eq_def]
      dsimp only
      nth_rw 5 [vars.eq_def]
      dsimp only
      have hreord:
        vars a ∪ vars c ∪ vars b ∪ vars d = vars a ∪ vars b ∪ vars c ∪ vars d := by grind
      -- Cardinality of s1's image union equals that of the full arrow union
      -- Since ! _ < _ but _ ≤ _ by invariance of s1
      have hveq:
        (vars (s1.apply b) ∪ vars (s1.apply d)).card =
        (vars (a.arrow b) ∪ vars (c.arrow d)).card
      := by
        have :
          (vars (s1.apply b) ∪ vars (s1.apply d)).card ≤
          (vars a ∪ vars b ∪ vars c ∪ vars d).card
        := by
          rw [← hreord]
          exact Finset.card_le_card h
        grind
      constructor
      · assumption
      · -- Cardinalities equal + vars_eq_then_id → s1 = id, so sizes are literally unchanged
        have hid : s1.apply = id := by
            apply s1.vars_eq_then_id (CurryType.arrow b d)
            have h_arrow : s1.apply (.arrow b d) = .arrow (s1.apply b) (s1.apply d) :=
              s1.subst_rec b d
            grind
        simp only [hid, id_eq, gt_iff_lt]
        grind  -- size b + size d < size (a.arrow b) + size (c.arrow d) by definition of `size`

/-- A substitution that simultaneously unifies all common variable bindings of two typing
    contexts. Unlike `Subst`, it does not carry termination invariants; it stores
    the `apply` function, the list of unified type pairs, and a `subst_rec` distribution proof. -/
structure CtxSubst (ctx1 ctx2 : TypeCtx) where
  apply : CurryType → CurryType
  vars: List (CurryType × CurryType)
  subst_rec: ∀ a b, apply (.arrow a b) = .arrow (apply a) (apply b)
  uctx1: TypeCtx
  uctx2: TypeCtx

/-- Construct a `CtxSubst ctx1 ctx2` from a list of `(variable, type1, type2)` triples,
    a substitution function `f`, a proof that `f` distributes over arrows, and the two contexts. -/
def CtxSubst.from
  (cvars : List (Char × CurryType × CurryType))
  (f : CurryType → CurryType)
  (subst_rec : ∀ a b, f (.arrow a b) = .arrow (f a) (f b))
  (ctx1 ctx2 : TypeCtx)
: CtxSubst ctx1 ctx2 where
  apply := f
  vars := cvars.map (fun (_, a, b) => (a, b))
  subst_rec := subst_rec
  uctx1 := ctx1
  uctx2 := ctx2

/-- Wrapper that erases the dependent type params of a `Subst`, allowing substitutions for
    different type pairs to be stored in a homogeneous list. -/
inductive ExSubst : Type
| from {a b : CurryType} : Subst a b → ExSubst

/-- Extract the underlying substitution function from an `ExSubst`. -/
def ExSubst.cast (ex : ExSubst) : CurryType → CurryType :=
  match ex with
  | ExSubst.from s => s.apply

/-- Helper function to recursively unify a list of common variables.
    Crucially, it applies the substitution from unifying the first pair 
    to the rest of the list before continuing the recursion. -/
def unifyCtx' (commonVars : List (Char × CurryType × CurryType)) : Option (List ExSubst) :=
  match commonVars with
  | [] => some []
  | (_, a, b) :: rest =>
    match unify a b with
    | none => none
    | some s1 =>
      -- Apply the substitution s1 to all remaining type pairs!
      let rest' := rest.map (fun (y, ty1, ty2) => (y, s1.apply ty1, s1.apply ty2))
      match unifyCtx' rest' with
      | none => none
      | some substs => some (ExSubst.from s1 :: substs)
  termination_by commonVars.length
  decreasing_by simp


/-- Unify two typing contexts by unifying the types assigned to their common variables.
    Collects all variables present in both environments, runs `unifyCtx'` to recursively
    unify and accumulate substitutions, and composes the resulting substitutions 
    left-to-right via `foldl`.
    Returns `none` if any individual unification fails. -/
@[grind]
def unifyCtx (ctx1 ctx2 : TypeCtx) : Option (CtxSubst ctx1 ctx2) :=
  let env1 := ctx1.env
  let env2 := ctx2.env
  -- Collect all variables common to both environments, paired with their respective types
  let commonVars : List (Char × CurryType × CurryType) :=
    env1.filterMap (fun (x, a) =>
      match env2.lookup x with
      | some b => some (x, a, b)
      | none => none)
  -- Use the recursive helper to get the accumulated unifications
  match unifyCtx' commonVars with
  | none => none
  | some exList =>
    -- The composed substitution applies each per-variable unifier in left-to-right order
    let apply : CurryType → CurryType :=
      fun t => exList.foldl (fun acc ex => ex.cast acc) t
    -- The composed function distributes over arrows because each factor does
    have h_subst_rec : ∀ a b, apply (.arrow a b) = .arrow (apply a) (apply b) := by
      intro a b
      induction exList generalizing a b with
      | nil =>
        -- empty composition is identity; identity distributes trivially
        simp only [List.foldl, apply]
      | cons ex exs ih =>
        simp only [List.foldl, apply]
        -- Extract lemma from underlying subst
        have h_ex : ∀ a b, ex.cast (.arrow a b) = .arrow (ex.cast a) (ex.cast b) := by
          cases ex with
          | «from» s => exact s.subst_rec
        rw [h_ex]
        grind
    some <| CtxSubst.from
      commonVars
      apply
      h_subst_rec
      ctx1
      ctx2

/-- Look up the type assigned to variable `c` in the typing context. -/
@[grind]
def TypeCtx.lookup (ctx : TypeCtx) (c : Char) : Option CurryType :=
  ctx.env.lookup c

/-- Principal-type algorithm helper. Infers a `PrincipalPair` for term `t` given initial context
    `ctx`. Fresh type variables are allocated with `next`; type and context unification use
    `unify` / `unifyCtx`. Returns `none` only if unification fails (term is untypeable).
    * `.var c`: return the existing type if `c` is in `ctx`, else allocate a fresh variable.
    * `.abs x m`: recursively infer for `m`; if `x` was assigned a type, wrap as `x.ty → m.ty`;
      otherwise allocate a fresh type for `x`.
    * `.app m n`: infer for `m` and `n` sequentially; unify `p1` with `p2 → a` (fresh `a`);
      then unify the two resulting contexts and apply the composed substitution. -/
@[grind]
def pp' (ctx : TypeCtx) : Term → Option PrincipalPair
| .var c =>
    match ctx.lookup c with
    | some ty => some ⟨ctx, ty⟩
    | none =>
      let (a, ctx') := next ctx
      some ⟨add c a ctx', a⟩
| .abs x m =>
    match pp' ctx m with
    | none => none
    | some ⟨ctx', p⟩ =>
      match ctx'.lookup x with
      | some ty => some ⟨ctx', .arrow ty p⟩
      | none =>
        let (a, ctx'') := next ctx'
        some ⟨add x a ctx'', .arrow a p⟩
| .app m n => 
    match pp' ctx m with
    | none => none
    | some ⟨ctx1, p1⟩ =>
      match pp' ctx1 n with
      | none => none
      | some ⟨ctx2, p2⟩ =>
        let (a, ctx3) := next ctx2
        match unify p1 (.arrow p2 a) with
        | none => none
        | some s1 =>
          -- Apply substitution to both contexts
          let ctx1' := applySubst s1.apply ctx1
          let ctx3' := applySubst s1.apply ctx3
          -- Try to unify the contexts
          match unifyCtx ctx1' ctx3' with
          | none => none
          | some s2 =>
            let finalCtx := applySubst s2.apply ctx3'
            let finalTy := s2.apply (s1.apply a)
            some ⟨finalCtx, finalTy⟩

/-- Principal-type algorithm. Infers the principal type of `t` starting from an empty context.
    Returns `some pair` where `pair.ctx` is the minimal typing context and `pair.ty` the
    principal type, or `none` if `t` is not typeable in the simply-typed lambda calculus. -/
def pp (t : Term) : Option PrincipalPair :=
  pp' emptyEnv t

def runTest (name : String) (t : Term) : String :=
  s!"[{name}] {t}: {pp t}"

#eval runTest "type of single variable x" (Term.var 'x')
#eval runTest "type of another variable y" (Term.var 'y')

#eval runTest "type of identity function" (Term.abs 'x' (Term.var 'x'))
#eval runTest "type of constant function" 
  (Term.abs 'x' (Term.abs 'y' (Term.var 'x')))

#eval runTest "type of simple application" (Term.app (Term.var 'f') (Term.var 'x'))
#eval runTest "type of left-associative application" 
  (Term.app (Term.app (Term.var 'f') (Term.var 'x')) (Term.var 'y'))
#eval runTest "type of application with abstraction" 
  (Term.app (Term.abs 'x' (Term.var 'x')) (Term.var 'y'))

-- S: λx.λy.λz.(x z)(y z)
#eval runTest "type of S combinator" 
  (Term.abs 'x' 
    (Term.abs 'y' 
      (Term.abs 'z' 
        (Term.app 
          (Term.app (Term.var 'x') (Term.var 'z')) 
          (Term.app (Term.var 'y') (Term.var 'z'))))))

-- K: λx.λy.x
#eval runTest "type of K combinator" 
  (Term.abs 'x' (Term.abs 'y' (Term.var 'x')))

-- comp: λf.λg.λx.f (g x)
#eval runTest "type of function composition" 
  (Term.abs 'f' 
    (Term.abs 'g' 
      (Term.abs 'x' 
        (Term.app (Term.var 'f') (Term.app (Term.var 'g') (Term.var 'x'))))))
