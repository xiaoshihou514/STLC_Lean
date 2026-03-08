import STLCLean.inference
import STLCLean.check
import Mathlib.Data.List.Basic

set_option relaxedAutoImplicit true

/-- If a variable `x` is absent from `pair'.ctx` and `pair.ctx` extends `pair'.ctx` with a
    binding for `x`, then type-checking any term `m` (where `Term.var x ≠ m`) in `pair.ctx`
    yields the same result as in `pair'.ctx`. In other words, adding an unused variable to the
    context does not affect checking. -/
theorem CheckInvUnderAdd
  (pair pair' : PrincipalPair)
  (hxm : Term.var x ≠ m)
  (hl : pair'.ctx.lookup x = none)
  (hn : nc = next pair'.ctx)
  (hp : pair.ctx = add x nc.fst nc.snd)
  (hp' : check pair'.ctx m = some pair'.ty)
: check pair.ctx m = some pair'.ty := by
  induction m generalizing pair pair' with
  -- base case: x
  | var c =>
    rw [hp]
    unfold check TypeCtx.lookup at hp' ⊢
    unfold add
    dsimp only
    rw [List.lookup_cons]
    by_cases hc: c = x
    · rw [hc]
      -- exact?
      exact False.elim (hxm (congrArg Term.var (id (Eq.symm hc))))
    · have : (c == x) = false := by exact beq_false_of_ne hc
      simpa [this, hn, next]
  -- Inductive case: λx.m
  | abs y m indm =>
    unfold check at hp' ⊢
    match hm : check pair'.ctx m with
    | none =>
      rw [hm] at hp'
      dsimp only at hp'
      contradiction
    | some tym =>
      rw [hm] at hp'
      dsimp only at hp'
      match hl' : pair'.ctx.lookup y with
      | none =>
        rw [hl'] at hp'
        dsimp only at hp'
        contradiction
      | some tyy =>
        rw [hl'] at hp'
        dsimp only at hp'
        let pair'' : PrincipalPair := { ctx := pair'.ctx, ty := tym }
        have hxm' : Term.var x ≠ m := by
          -- suppose contradiction, if m = x, pair'.ctx would contain x
          -- That contradicts with hl
          intro h
          rw [← h] at hm
          simp [check, hl] at hm
        -- Apply induction hypothesis
        specialize indm pair pair'' hxm' hl hn hp hm
        -- unfold
        rw [indm] at ⊢
        have hxy : x ≠ y := by grind
        have lookup_y : pair.ctx.lookup y = some tyy := by grind
        grind
  -- Inductive case: m n
  | app m n indm indn =>
    unfold check at hp' ⊢
    have hnc := hn
    match hm: check pair.ctx m with
    -- all cases give contradiction since then it contradicts ind. hyp.
    -- all cases would imply that check pair m is none via ind. hyp. with appropriate pair
    -- the contradictions all have form none = some _
    | none =>
      match hn: check pair.ctx n with
      | none =>
        match hpm : check pair'.ctx m with
        | none => simp [hpm] at hp'
        | some tym =>
          match hpn : check pair'.ctx n with
          | none => simp [hpm, hpn] at hp'
          | some tyn =>
            simp only [hpm, hpn] at hp'
            cases tym with
            | phi _ => simp at hp'
            | arrow a b =>
              dsimp only at hp'
              let pair_m : PrincipalPair := { ctx := pair'.ctx, ty := a.arrow b }
              specialize indm pair pair_m (by grind) hl hnc hp hpm
              rw [indm] at hm
              contradiction
      | some tyn =>
        match hpm : check pair'.ctx m with
        | none => simp [hpm] at hp'
        | some tym =>
          match hpn : check pair'.ctx n with
          | none => simp [hpm, hpn] at hp'
          | some tyn =>
          let pair_m : PrincipalPair := { ctx := pair'.ctx, ty := tym }
          specialize indm pair pair_m (by grind) hl hnc hp hpm
          rw [indm] at hm
          contradiction
    | some tym => 
      match hn: check pair.ctx n with
        -- more contradictions...
      | none =>
        match hpm : check pair'.ctx m with
        | none => simp [hpm] at hp'
        | some tym' =>
          match hpn : check pair'.ctx n with
          | none => simp [hpm, hpn] at hp'
          | some tyn' =>
            simp only [hpm, hpn] at hp'
            cases tym' with
            | phi _ => simp at hp'
            | arrow a b =>
              dsimp only at hp'
              by_cases heq : a == tyn'
              · simp at hp'
                let pair_n : PrincipalPair := { ctx := pair'.ctx, ty := tyn' }
                specialize indn pair pair_n (by grind) hl hnc hp hpn
                rw [indn] at hn
                contradiction
              · grind
      | some tyn =>
        match hpm : check pair'.ctx m with
        | none => simp [hpm] at hp'
        | some tym' =>
          match hpn : check pair'.ctx n with
          | none => simp [hpm, hpn] at hp'
          | some tyn' =>
            simp only [hpm, hpn] at hp'
            cases tym' with
            | phi _ => simp at hp'
            -- The real thing
            | arrow a b =>
              dsimp only at hp'
              by_cases heq : a == tyn'
              · simp at hp'
                cases tym with
                | phi _ =>
                  let pair_m : PrincipalPair := { ctx := pair'.ctx, ty := a.arrow b }
                  specialize indm pair pair_m (by grind) hl hnc hp hpm
                  rw [indm] at hm
                  grind
                | arrow a' b' =>
                  -- Apply ind. hyp.
                  -- This is the only case that's "normal"
                  let pair_m : PrincipalPair := { ctx := pair'.ctx, ty := a.arrow b }
                  specialize indm pair pair_m (by grind) hl hnc hp hpm
                  rw [indm] at hm
                  let pair_n : PrincipalPair := { ctx := pair'.ctx, ty := tyn' }
                  specialize indn pair pair_n (by grind) hl hnc hp hpn
                  -- Now this gives us the results we wanted
                  grind
              · grind

/-- `List.lookup` commutes with mapping a function over the values: looking up `x` in a
    mapped list returns the mapped value. -/
theorem LookupMap {x : Char} {y : CurryType} {xys : List (Char × CurryType)}
  (s : CurryType → CurryType)
  (hc : List.lookup x xys = some y)
: List.lookup x (List.map (fun xy => (xy.fst, s xy.snd)) xys) = some (s y) := by
  induction xys with
  | nil => grind
  | cons xy xys ind => grind

/-- Applying a type substitution `s` to every type in a context maps a successful `check` result
    covariantly: if `check ctx t = some ty` then `check (applySubst s ctx) t = some (s ty)`. -/
theorem CheckSubst
  (t : Term)
  (ty : CurryType)
  (s : CurryType → CurryType)
  (ctx : TypeCtx)
  (hc : check ctx t = some ty)
  {h_arrow : ∀ a b, s (CurryType.arrow a b) = CurryType.arrow (s a) (s b)}
: check (applySubst s ctx) t = some (s ty) := by
  induction t generalizing ty with
  | var c => 
    unfold check TypeCtx.lookup at hc ⊢
    unfold applySubst
    dsimp only at hc ⊢
    apply LookupMap
    assumption
  | abs x m ind =>
    unfold check TypeCtx.lookup at hc ⊢
    match hc_m : check ctx m with
    | none => simp [hc_m] at hc
    | some tym =>
      simp only [hc_m] at hc
      match hc_x : List.lookup x ctx.env with
      | none => simp [hc_x] at hc
      | some ty' =>
        simp [hc_x] at hc
        have h_ty_eq : ty = CurryType.arrow ty' tym := by grind
        subst h_ty_eq
        specialize ind tym hc_m
        simp [ind]
        have hl' := LookupMap s hc_x
        grind
  | app m n indm indn =>
    unfold check at hc ⊢
    match hc_m : check ctx m with
    | none => simp [hc_m] at hc
    | some ty_m =>
      simp only [hc_m] at hc
      match hc_n : check ctx n with
      | none => simp [hc_n] at hc
      | some ty_n =>
        simp only [hc_n] at hc
        cases ty_m with
        | phi _ => simp at hc
        | arrow a b =>
          -- Extract from hc: the boolean condition a == ty_n and the result ty = b
          have h_eq : a == ty_n := by
            by_cases h : a == ty_n
            · assumption
            · grind
          simp at hc
          have h_ty_eq : ty = b := by grind
          subst h_ty_eq
          -- Apply induction hypotheses to m and n
          specialize indm (a.arrow ty) hc_m
          specialize indn ty_n hc_n
          simp only [indm, indn]
          rw [h_arrow a ty]
          -- Convert boolean equality a == ty_n to propositional equality a = ty_n
          have h_a_eq_ty_n : a = ty_n := beq_iff_eq.mp h_eq
          rw [h_a_eq_ty_n]
          -- The if-condition s a == s ty_n now holds (substitutions preserve BEq)
          -- so the result is some (s ty)
          simp

/-- Composing two substitution applications is the same as applying their functional composition.
    That is, `applySubst f (applySubst g ctx) = applySubst (f ∘ g) ctx`. -/
theorem SubstComp
  (f g : CurryType → CurryType)
  (ctx : TypeCtx)
: applySubst f (applySubst g ctx) = applySubst (f ∘ g) ctx := by
  simp [applySubst]

/-- `check` depends only on the `env` field of `TypeCtx` and ignores the `label` (fresh-variable
    counter). Two contexts with equal environments yield identical check results for any term. -/
theorem CheckInvUnderLabel
  (t : Term)
  (ctx ctx' : TypeCtx)
  (henv : ctx.env = ctx'.env)
: check ctx t = check ctx' t := by
  induction t with
  | var c => grind
  | abs x m ind => grind
  | app m n indm indn => grind

/-- Applying a substitution to a context and then advancing to the next fresh variable yields the
    same check result as applying the substitution to the already-advanced context. In other words,
    `applySubst` and `next` commute as far as `check` is concerned.
    This is a corollary of `CheckInvUnderLabel`.
-/
theorem CheckInvUnderNextSubst
  (ctx : TypeCtx)
  (f : CurryType → CurryType)
  (m : Term)
: check (applySubst f ctx) m = check (applySubst f (next ctx).snd) m :=
  CheckInvUnderLabel m (applySubst f ctx) (applySubst f (next ctx).snd) (by simp [applySubst, next])

/-- `applySubst` preserves the `env` field of a context (up to value substitution), so two
    contexts with equal environments produce equal environments after the same substitution. -/
theorem EnvInvUnderSubst
  (ctx ctx' : TypeCtx)
  (fce : ctx.env = ctx'.env)
  (f : CurryType → CurryType)
: (applySubst f ctx).env = (applySubst f ctx').env := by
  grind

/-- Soundness of `unify`: if `unify t1 t2` returns a substitution `s`, then `s` is indeed a
    unifier, i.e. `s.apply t1 = s.apply t2`. -/
theorem UnifySound
  (t1 t2 : CurryType)
  (s : Subst t1 t2)
: unify t1 t2 = some s → s.apply t1 = s.apply t2 := by
  intro h
  -- t1, t2 all cases: phi - phi, phi - arrow etc.
  induction t1, t2 using unify.induct
  with
  | case1 p =>
    simp only [unify] at h
    cases h
    simp [Subst.id]
  | case2 p q h_neq =>
    simp only [unify, dif_neg h_neq] at h
    cases h
    have : ¬occursIn p (.phi q) := by simp [occursIn, h_neq]
    simp [Subst.replace, replaceVar]
  | case3 p ty h_occ =>
    simp only [unify] at h
    grind
  | case4 p ty h_occ h_not_occ =>
    simp only [unify] at h
    rw [dif_neg h_not_occ] at h
    cases h
    simp only [Subst.replace]
    have h_not_occ_prop : ¬occursIn p ty := by
      grind
    have replaceVar_self :
      ∀ (p : Char) (σ τ : CurryType), ¬occursIn p τ → replaceVar p σ τ = τ
    := by
      intros p σ τ h
      induction τ with
      | phi q =>
        simp [replaceVar]
        by_cases hpq : q = p
        · grind
        · simp [hpq]
      | arrow a b iha ihb =>
        simp only [replaceVar]
        have ha : ¬occursIn p a := by grind
        have hb : ¬occursIn p b := by grind
        rw [iha ha, ihb hb]
    have h_eq : replaceVar p ty ty = ty := replaceVar_self p ty ty h_not_occ_prop
    rw [h_eq]
    simp [replaceVar.eq_def]
  | case5 a b c d h_rec =>
    simp only [unify, h_rec] at h
    contradiction
  | case6 a b c d s1 h_rec1 h_rec2 =>
    simp only [unify, h_rec1] at h
    rw [h_rec2] at h
    contradiction
  | case7 a b c d s1 h1 s2 h2 ih1 ih2 =>
    -- Arrow-arrow case: s = Subst.comp s1 s2.
    -- ih1 gives s1.apply a = s1.apply c; ih2 gives s2.apply (s1.apply b) = s2.apply (s1.apply d).
    -- Use subst_rec to distribute both substitutions over the arrow constructors,
    -- then rewrite with ih1 and ih2 to close the goal.
    simp only [unify, h1, h2] at h
    cases h
    simp only [Subst.comp]
    have eq1 := ih1 s1 h1
    have eq2 := ih2 s2 h2
    simp only [Function.comp_apply, s1.subst_rec, s2.subst_rec, CurryType.arrow.injEq]
    rw [eq1, eq2]
    trivial
  | case8 ty p h_occ =>
    simp only [unify] at h
    grind
  | case9 ty p h_occ h_not_occ =>
    simp only [unify, dif_neg h_not_occ] at h
    cases h
    simp only [Subst.replacer]
    -- Lemma: if p does not occur in a, replacing p with any type σ leaves a unchanged
    have replace_no_occ : ∀ (σ a : CurryType), ¬occursIn p a → replaceVar p σ a = a := by
      intro σ a
      induction a with
      | phi q => grind
      | arrow a1 a2 iha1 iha2 =>
        simp only [Bool.not_eq_true, replaceVar, CurryType.arrow.injEq]
        intro h
        have h1 : ¬occursIn p a1 := by grind
        have h2 : ¬occursIn p a2 := by grind
        rw [iha1 h1, iha2 h2]
        trivial
    -- First equation: replaceVar p ty ty = ty (since p does not occur in ty, by h_not_occ)
    have eq1 : replaceVar p ty ty = ty := replace_no_occ ty ty h_not_occ
    -- Second equation: replaceVar p ty (.phi p) = ty (direct substitution of p)
    have eq2 : replaceVar p ty (.phi p) = ty := by simp [replaceVar]
    rw [eq1, eq2]

/-- If a `Subst` `s1` distributes over arrows
    (i.e. `s1.apply ab = (s1.apply a).arrow (s1.apply b)`),
    then composing with a `CtxSubst` `s2` preserves this arrow structure. -/
theorem SubstMap
  (s1 : Subst α β)
  (s2 : CtxSubst ctx1 ctx2)
  (hs : s1.apply ab = (s1.apply a).arrow (s1.apply b))
: (s2.apply ∘ s1.apply) ab = ((s2.apply ∘ s1.apply) a).arrow ((s2.apply ∘ s1.apply) b) := by
  simp only [Function.comp_apply, hs]
  rw [s2.subst_rec]

/-- If `pp' ctx m = some ⟨ctx', ty⟩`, then there exists a substitution `f` such that
    `(applySubst f ctx).env ⊆ ctx'.env`. In other words, the inference output context
    contains the input context (up to substitution). -/
theorem InferenceSubsetMap
  (ctx ctx' : TypeCtx)
  (m : Term)
  (ty : CurryType)
  (hpp : pp' ctx m = some ⟨ctx', ty⟩)
: ∃ f, (applySubst f ctx).env ⊆ ctx'.env := by
  induction m generalizing ctx ctx' ty with
  | var x =>
    unfold pp' at hpp
    match hl: ctx.lookup x with
    | none =>
      use id
      grind
    | some ty =>
      use id
      grind
  | abs x m indm =>
    unfold pp' at hpp
    match hm: pp' ctx m with
    | none => grind
    | some p =>
      simp only [hm] at hpp
      match hp: p.ctx.lookup x with
      | none =>
        specialize indm ctx p.ctx p.ty hm
        grind
      | some ty' =>
        specialize indm ctx p.ctx p.ty hm
        grind
  | app m n indm indn =>
    unfold pp' at hpp
    match hm: pp' ctx m with
    | none => grind
    | some pm =>
      match hn: pp' pm.ctx n with
      | none => grind
      | some pn =>
        match hu: unify pm.ty (pn.ty.arrow (next pn.ctx).1) with
        | none => grind
        | some s1 =>
          match huc:
            unifyCtx (applySubst s1.apply pm.ctx) (applySubst s1.apply (next pn.ctx).2)
          with
          | none => grind
          | some s2 =>
            simp only [hm, hn, hu, huc] at hpp
            specialize indm ctx pm.ctx pm.ty hm
            specialize indn pm.ctx pn.ctx pn.ty hn
            have ⟨f, indm'⟩ := indm
            have ⟨g, indn'⟩ := indn
            use (s2.apply ∘ s1.apply ∘ g ∘ f)
            have : (applySubst g (applySubst f ctx)).env ⊆ pn.ctx.env := by grind
            have :
              (applySubst s2.apply (applySubst s1.apply (applySubst g (applySubst f ctx)))).env ⊆
              ctx'.env := by grind
            rw [
              SubstComp g f ctx,
              SubstComp s1.apply (g ∘ f) ctx,
              SubstComp s2.apply (s1.apply ∘ g ∘ f)
            ] at this
            assumption

-- Assumption: next always produces a fresh type variable
-- This is guaranteed by next's definition and existence of inj Nat -> Char
-- In particular, if I add new info (y, <fresh>) to ctx
-- it will not affect any existing lookups
@[grind .]
theorem NextFresh
  (x y : Char)
  (ty : CurryType)
  (ctx : TypeCtx)
  {hxy : x ≠ y}
: ctx.lookup x = some ty ↔ (add y (next ctx).1 (next ctx).2).lookup x = some ty := by
  sorry

/-- `SubstLookup`: applying a substitution to a context preserves lookup results up to `f`.
    This is a convenience wrapper around `LookupMap`. -/
theorem SubstLookup (f : CurryType → CurryType) (ctx : TypeCtx) (x : Char) (ty : CurryType) :
    ctx.lookup x = some ty → (applySubst f ctx).lookup x = some (f ty) :=
  fun h => LookupMap f h

/-- `distributes f`: predicate asserting that `f` distributes over arrow types,
    i.e. `f (a → b) = f(a) → f(b)`. Required by `CheckSubst`. -/
@[grind .]
def distributes (f : CurryType → CurryType) :=
  ∀ a b, f (a.arrow b) = (f a).arrow (f b)

/-- `lookup_inv f ctx ctx'`:
    predicate asserting that `f` is a lookup invariant from `ctx` to `ctx'`,
    i.e. for every variable `x` with type `ty` in `ctx`, `ctx'` assigns `f ty` to `x`. -/
@[grind .]
def lookup_inv (f : CurryType → CurryType) (ctx ctx' : TypeCtx) :=
  ∀ x ty, ctx.lookup x = some ty → ctx'.lookup x = some (f ty)

/-- `check_inv f ctx ctx'`: predicate asserting that `f` is a check invariant from `ctx` to `ctx'`,
    i.e. for every term `t` with type `ty` under `ctx`, `ctx'` assigns `f ty` to `t`. -/
@[grind .]
def check_inv (f : CurryType → CurryType) (ctx ctx' : TypeCtx) :=
  ∀ t ty, check ctx t = some ty → check ctx' t = some (f ty)

/-- `equiv_lookup_on f g ctx`: `f` and `g` agree on types of variables actually occurring in `ctx`,
    i.e. for all `x` with `ctx.lookup x = some ty`, `g ty = f ty`. -/
@[grind .]
def equiv_lookup_on (f g : CurryType → CurryType) (ctx : TypeCtx) :=
  ∀ x ty, ctx.lookup x = some ty → g ty = f ty

/-- `equiv_check_on f g ctx`: `f` and `g` agree on types of terms that type-check under `ctx`,
    i.e. for all `t` with `check ctx t = some ty`, `g ty = f ty`. -/
@[grind .]
def equiv_check_on (f g : CurryType → CurryType) (ctx : TypeCtx) :=
  ∀ x ty, check ctx x = some ty → g ty = f ty

/-- `InferenceLookupInv`: if `pp' ctx m = some ⟨ctx', _⟩`, then there exists a canonical
    substitution `f` (distributing over arrows) that is a lookup invariant from `ctx` to `ctx'`,
    and it is unique in the sense that any other lookup invariant `g` agrees with `f` on
    types occurring in `ctx`. -/
theorem InferenceLookupInv
  (ctx ctx' : TypeCtx)
  (m : Term)
  (hpp : pp' ctx m = some ⟨ctx', _ty⟩)
  : ∃ f,
    lookup_inv f ctx ctx' ∧
    distributes f ∧
    ∀ g, lookup_inv g ctx ctx' → equiv_lookup_on f g ctx
:= by
  induction m generalizing ctx ctx' _ty with
  | var x =>
    use id
    constructor <;> grind
  | abs x m indm =>
    unfold pp' at hpp
    simp only at hpp
    match hm: pp' ctx m with
    | none => grind
    | some { ctx := ctxm, ty := tym } =>
      simp only [hm] at hpp
      match hl: ctxm.lookup x with
      | none =>
        simp only [hl] at hpp
        have : ctx' = add x (next ctxm).1 (next ctxm).2 := by grind
        rw [this]
        specialize indm ctx ctxm hm
        have ⟨f, ⟨hinvf, ⟨hdistf, hequiv⟩⟩⟩ := indm
        use f
        constructor <;> grind
      | some tyx =>
        simp only [hl] at hpp
        specialize indm ctx ctxm hm
        have ⟨f, ⟨hinvf, ⟨hdistf, hequiv⟩⟩⟩ := indm
        use f
        constructor <;> grind
  | app m n indm indn =>
    unfold pp' at hpp
    simp only at hpp
    match hm: pp' ctx m with
    | none => grind
    | some { ctx := ctxm, ty := tym } =>
      match hn: pp' ctxm n with
      | none => grind
      | some { ctx := ctxn, ty := tyn } =>
        match hu: unify tym (tyn.arrow (next ctxn).1) with
        | none => grind
        | some s1 =>
          match hum: unifyCtx (applySubst s1.apply ctxm) (applySubst s1.apply (next ctxn).2) with
          | none => grind
          | some s2 =>
            simp only [hm, hn, hu, hum] at hpp
            have : ctx' = applySubst s2.apply (applySubst s1.apply (next ctxn).2) := by grind
            subst this
            specialize indm ctx ctxm hm
            have ⟨f, ⟨hinvf, ⟨hdistf, hequivf⟩⟩⟩ := indm
            specialize indn ctxm ctxn hn
            have ⟨g, ⟨hinvg, ⟨hdistg, hequivg⟩⟩⟩ := indn
            use (s2.apply ∘ s1.apply ∘ g ∘ f)
            constructor
            · intro x ty hlx
              have : (next ctxn).2.lookup x = g (f ty) := by grind
              rw [SubstComp s2.apply s1.apply]
              exact
                SubstLookup (s2.apply ∘ s1.apply) (next ctxn).2 x ((g ∘ f) ty)
                  (hinvg x (f ty) (hinvf x ty hlx))
            · constructor
              · have s1_dist := s1.subst_rec
                have s2_dist := s2.subst_rec
                grind
              · intro h hinvh x ty hlx
                have h3 : (next ctxn).2.lookup x = some (g (f ty)) := by grind
                have h4 := LookupMap s1.apply h3
                have h5 := LookupMap s2.apply h4
                grind

/-- `InferenceCheckInv`: if `pp' ctx m = some ⟨ctx', _⟩`, then there exists a canonical
    substitution `f` (distributing over arrows) that is a check invariant from `ctx` to `ctx'`,
    and it is unique among check invariants in that any other `g` agrees with `f` on types
    of terms typeable under `ctx`. -/
theorem InferenceCheckInv
  (ctx ctx' : TypeCtx)
  (m : Term)
  (hpp : pp' ctx m = some ⟨ctx', _ty⟩)
  : ∃ f,
    check_inv f ctx ctx' ∧
    distributes f ∧
    ∀ g, check_inv g ctx ctx' → equiv_check_on f g ctx
:= by
  induction m generalizing ctx ctx' _ty with
  | var x0 =>
    use id
    constructor
    · unfold check_inv
      intro t ty hc
      unfold check at hc ⊢
      match t with
      | .var x => grind
      | .abs x n =>
        match hcn: check ctx n with
        | none => grind
        | some tyn =>
          match hlx: ctx.lookup x with
          | none => grind
          | some tyx =>
            simp only [hcn, hlx] at hc ⊢
            have hty : ty = tyx.arrow tyn := by grind
            subst hty
            simp [pp'] at hpp
            cases hx0: ctx.lookup x0 with
            | none =>
              have hneq : Term.var x0 ≠ n := by grind
              let nc := next ctx
              have hctx' : ctx' = add x0 nc.fst nc.snd := by grind
              let pair' : PrincipalPair := { ctx := ctx, ty := tyn }
              let pair : PrincipalPair := { ctx := add x0 nc.fst nc.snd, ty := tyn }
              have hcn' := @CheckInvUnderAdd x0 n _ pair pair' hneq hx0 rfl rfl hcn
              have hlx' : ctx'.lookup x = some tyx := by grind
              grind
            | some _ => grind
      | .app p q =>
        simp [pp'] at hpp
        cases hx0: ctx.lookup x0 with
        | none =>
          -- ctx' = add x0 (next ctx).fst (next ctx).snd
          let nc := next ctx
          have hctx' : ctx' = add x0 nc.fst nc.snd := by grind
          rw [hctx']
          simp only at hc
          cases hc_p : check ctx p with
          | none => grind
          | some ty_p =>
            cases hc_q : check ctx q with
            | none => grind
            | some ty_q =>
              simp only [hc_p, hc_q, beq_iff_eq] at hc
              cases ty_p with
              | phi _ => grind
              | arrow a b =>
                simp at hc
                have h_eq : a == ty_q := by grind
                have h_ty : ty = b := by grind
                let pair'_p : PrincipalPair := { ctx := ctx, ty := a.arrow b }
                let pair_p : PrincipalPair := { ctx := add x0 nc.fst nc.snd, ty := a.arrow b }
                subst h_ty
                have hcn_p := @CheckInvUnderAdd x0 p _ pair_p pair'_p (by grind) hx0 rfl rfl hc_p
                let pair'_q : PrincipalPair := { ctx := ctx, ty := a }
                let pair_q : PrincipalPair := { ctx := add x0 nc.fst nc.snd, ty := a }
                have hcn_q :=
                  @CheckInvUnderAdd
                    x0 q _ pair_q pair'_q (by grind) hx0 rfl rfl (by grind)
                grind
        | some ty0 => grind
    · constructor
      · grind
      · intro g hg m tym hcm
        specialize hg m tym hcm
        cases hx0: ctx.lookup x0 with
        | none =>
          let pair' : PrincipalPair := { ctx := ctx, ty := tym }
          let pair : PrincipalPair := { ctx := ctx', ty := tym }
          let nc := next ctx
          have h_eq := @CheckInvUnderAdd x0 m _ pair pair' (by grind) hx0 rfl (by grind) hcm
          grind
        | some _ => grind
  | abs x n indn =>
    unfold pp' at hpp
    match hpn: pp' ctx n with
    | none => grind
    | some ⟨ctxn, tyn⟩  =>
      match hlnx: ctxn.lookup x with
      | none =>
        simp only [hpn, hlnx] at hpp
        specialize indn ctx ctxn hpn
        have ⟨f, ⟨hci, ⟨hdistf, hequiv⟩⟩⟩ := indn
        use f
        have : ctx' = add x (next ctxn).1 (next ctxn).2 := by grind
        rw [this]
        constructor
        · intro t ty hct
          have hctxn := hci t ty hct
          let pair' : PrincipalPair := { ctx := ctxn, ty := f ty }
          let pair : PrincipalPair := { ctx := add x (next ctxn).1 (next ctxn).2, ty := f ty }
          exact @CheckInvUnderAdd x t _ pair pair' (by grind) hlnx rfl rfl hctxn
        · constructor
          · assumption
          · intro g hg t tyx hcx
            have hctxn := hci t tyx hcx
            have h_ne : Term.var x ≠ t := by grind
            let pair' : PrincipalPair := { ctx := ctxn, ty := f tyx }
            let pair : PrincipalPair := { ctx := add x (next ctxn).1 (next ctxn).2, ty := f tyx }
            have h_add := @CheckInvUnderAdd x t _ pair pair' h_ne hlnx (by rfl) (by rfl) hctxn
            specialize hg t tyx hcx
            grind
      | some hlx =>
        simp only [hpn, hlnx] at hpp
        specialize indn ctx ctxn hpn
        have ⟨f, ⟨hci, ⟨hdistf, hequiv⟩⟩⟩ := indn
        use f
        constructor <;> grind
  | app m n indm indn =>
    unfold pp' at hpp
    match hpm: pp' ctx m with
    | none => grind
    | some ⟨ctxm, tym⟩ =>
      match hpn: pp' ctxm n with
      | none => grind
      | some ⟨ctxn, tyn⟩ => 
        match hu: unify tym (tyn.arrow (next ctxn).1) with
        | none => grind
        | some s1 =>
          match huctx: unifyCtx (applySubst s1.apply ctxm) (applySubst s1.apply (next ctxn).2) with
          | none => grind
          | some s2 =>
            simp only [hpm, hpn, hu, huctx] at hpp
            have : ctx' = applySubst s2.apply (applySubst s1.apply (next ctxn).2) := by grind
            rw [this]
            specialize indm ctx ctxm hpm
            have ⟨f, ⟨hcm, ⟨hdistf, hequiv⟩⟩⟩ := indm
            specialize indn ctxm ctxn hpn
            have ⟨g, ⟨hcn, ⟨hdistg, gequiv⟩⟩⟩ := indn
            use (s2.apply ∘ s1.apply ∘ g ∘ f)
            constructor
            · intro t ty hct
              have hcnt := hcn t (f ty) (hcm t ty hct)
              have hnext := CheckInvUnderLabel t ctxn (next ctxn).snd (by grind)
              rw [hnext] at hcnt
              have := @CheckSubst t (g (f ty)) s1.apply (next ctxn).snd hcnt s1.subst_rec
              have :=
                @CheckSubst
                  t
                  (s1.apply (g (f ty)))
                  s2.apply
                  (applySubst s1.apply (next ctxn).snd)
                  this
                  s2.subst_rec
              grind
            · constructor
              · have s1_dist := s1.subst_rec
                have s2_dist := s2.subst_rec
                grind
              · intro h hch t tyt hct
                have hcnt := hcn t (f tyt) (hcm t tyt hct)
                have hnext := CheckInvUnderLabel t ctxn (next ctxn).snd (by grind)
                rw [hnext] at hcnt
                have := @CheckSubst t (g (f tyt)) s1.apply (next ctxn).snd hcnt s1.subst_rec
                have :=
                  @CheckSubst
                    t
                    (s1.apply (g (f tyt)))
                    s2.apply
                    (applySubst s1.apply (next ctxn).snd)
                    this
                    s2.subst_rec
                grind

/-- `occursInTerm x t`:
    proposition that variable `x` occurs (free or bound as a name) in term `t`. -/
def occursInTerm (x : Char) : Term → Prop
| .var y => x = y
| .abs y m => x = y ∨ occursInTerm x m
| .app m n => occursInTerm x m ∨ occursInTerm x n

/-- `CheckEqIfOccursInv`: if two contexts agree on the types of all variables occurring in `t`,
    then `check ctx1 t = check ctx2 t`. -/
theorem CheckEqIfOccursInv (t : Term) (ctx1 ctx2 : TypeCtx) :
    (∀ x, occursInTerm x t → ctx1.lookup x = ctx2.lookup x) → check ctx1 t = check ctx2 t := by
  induction t with
  | var x =>
    intro h
    simp only [check]
    exact h x (by simp only [occursInTerm])
  | abs x m ih =>
    intro h
    simp only [check]
    -- By the induction hypothesis, the result holds for m
    have h_m : ∀ y, occursInTerm y m → ctx1.lookup y = ctx2.lookup y :=
      fun y hy => h y (Or.inr hy)
    have eq_m := ih h_m
    rw [eq_m]
    -- Compare the lookup result for x
    have hx : ctx1.lookup x = ctx2.lookup x := h x (Or.inl rfl)
    cases h1 : check ctx1 m with
    | none => grind
    | some ty1 => grind
  | app m n ih_m ih_n =>
    intro h
    simp [check]
    have h_m : ∀ y, occursInTerm y m → ctx1.lookup y = ctx2.lookup y :=
      fun y hy => h y (Or.inl hy)
    have h_n : ∀ y, occursInTerm y n → ctx1.lookup y = ctx2.lookup y :=
      fun y hy => h y (Or.inr hy)
    grind

/-- `CheckSuccessLookupSome`: if `check ctx t = some ty`, then every variable occurring in `t`
    has a type in `ctx`. -/
theorem CheckSuccessLookupSome (t : Term) (ctx : TypeCtx) (ty : CurryType) :
    check ctx t = some ty → ∀ x, occursInTerm x t → ∃ ty', ctx.lookup x = some ty' := by
  induction t generalizing ty with
  | var x =>
    unfold occursInTerm
    grind
  | abs x m ih =>
    intro h hx
    simp only [check] at h
    cases hcm : check ctx m with
    | none => grind
    | some tym =>
      cases hlx : ctx.lookup x with
      | none => grind
      | some tyx =>
        simp [hcm, hlx] at h
        intro h_occ
        cases h_occ with
        | inl h_eq => grind
        | inr h_occ_m => grind
  | app m n ih_m ih_n =>
    intro h hx
    simp only [check] at h
    cases h1 : check ctx m with
    | none => grind
    | some tym =>
      cases h2 : check ctx n with
      | none => grind
      | some tyn =>
        simp only [h1, h2] at h
        cases tym with
        | phi _ => grind
        | arrow a b =>
          by_cases heq : a == tyn
          · simp only [
              Option.ite_none_right_eq_some,
              Option.some.injEq
            ] at h
            intro hox
            cases hox with
            | inl h_occ_m => exact ih_m (a.arrow b) h1 hx h_occ_m
            | inr h_occ_n => exact ih_n tyn h2 hx h_occ_n
          · grind


-- Auxiliary lemma: if a list lookup succeeds, the key-value pair is in the list
theorem LookupThenIn {α β : Type} [BEq α] [LawfulBEq α] {x : α} {y : β} {l : List (α × β)}
    (h : List.lookup x l = some y) : (x, y) ∈ l := by
  induction l with
  | nil => grind
  | cons hd tl ih => grind

-- Auxiliary lemma: if f a = f b, then for any substitution list es,
-- left-folding each substitution in es after f preserves the equality of a and b
theorem FoldlInv (es : List ExSubst) (f : CurryType → CurryType) (a b : CurryType)
    (h : f a = f b) :
    (es.foldl (fun acc ex => ex.cast ∘ acc) f) a =
      (es.foldl (fun acc ex => ex.cast ∘ acc) f) b
:= by
  induction es generalizing f with
  | nil => simp [h]
  | cons ex es' ih =>
    simp only [List.foldl_cons]
    apply ih
    exact congrArg ex.cast h

-- Core inductive lemma: for any variable-pair list l and substitution list exs,
-- if unifyCtx' l = some exs, then
-- the left-folded composition of substitutions unifies each pair in l
theorem UnifyCtxSound :
  ∀ (l : List (Char × CurryType × CurryType)) (exs : List ExSubst),
    unifyCtx' l = some exs →
    ∀ (x : Char) (a b : CurryType),
      (x, a, b) ∈ l →
      let F := exs.foldl (fun acc ex => ex.cast ∘ acc) id
      F a = F b := by
  intro l exs h x a b hmem
  -- Induct on the length of the list using strong induction
  have main : ∀ (n : Nat) (l : List (Char × CurryType × CurryType)) (exs : List ExSubst),
      l.length = n →
      unifyCtx' l = some exs →
      ∀ x a b, (x, a, b) ∈ l
      → (exs.foldl (fun acc ex => ex.cast ∘ acc) id) a =
        (exs.foldl (fun acc ex => ex.cast ∘ acc) id) b
  := by
    intro n
    refine Nat.strongRecOn n (fun n IH => ?_)
    intro l exs hlen h x a b hmem
    cases l with
    | nil => contradiction
    | cons hd tl =>
      have ⟨y, a0, b0⟩ := hd
      simp only [unifyCtx'] at h
      cases h0 : unify a0 b0 with
      | none => simp [h0] at h
      | some s1 =>
        simp only [h0] at h
        let rest' := tl.map (fun (z, c, d) => (z, s1.apply c, s1.apply d))
        cases h_rest : unifyCtx' rest' with
        | none => grind
        | some exs' =>
          rw [h_rest] at h
          injection h with heq
          rw [← heq]
          simp only [List.foldl_cons, Function.comp_id]
          have : (ExSubst.from s1).cast = s1.apply := rfl
          simp only [this]
          rw [List.mem_cons] at hmem
          cases hmem with
          | inl heq' =>
            cases heq'
            have eq := UnifySound a b s1 h0
            exact FoldlInv exs' s1.apply a b eq
          | inr hmem_tl =>
            specialize IH rest'.length (by grind) rest' exs' (by grind)
                          h_rest x (s1.apply a) (s1.apply b) (by grind)
            let F := (ExSubst.from s1 :: exs').foldl (fun acc ex => ex.cast ∘ acc) id
            let G := exs'.foldl (fun acc ex => ex.cast ∘ acc) id
            have F_eq : ∀ t, F t = G (s1.apply t) := by
              intro t
              induction exs' with
              | nil =>
                simp only [F, G, List.foldl_nil, List.foldl_cons, Function.comp_apply, id_eq, this]
              | cons ex exs' ih =>
                simp only [F, G, List.foldl_cons, this]
                -- Goal: foldl (fun acc ex => ex.cast ∘ acc) (ex.cast ∘ s1.apply) exs' t =
                --       foldl (fun acc ex => ex.cast ∘ acc) ex.cast exs' (s1.apply t)
                -- Prove an auxiliary lemma:
                -- for any list l and functions h, s, foldl (h ∘ s) l t = foldl h l (s t)
                have h_comp : ∀ {l : List ExSubst} {h s : CurryType → CurryType} {t},
                    List.foldl (fun acc ex => ex.cast ∘ acc) (h ∘ s) l t =
                    List.foldl (fun acc ex => ex.cast ∘ acc) h l (s t)
                := by
                  intro l h s t
                  induction l generalizing h with
                  | nil => simp
                  | cons ex l' IH =>
                    simp only [List.foldl_cons]
                    rw [← Function.comp_assoc, @IH (ex.cast ∘ h)]
                rw [h_comp]
                rfl
            have F_eq_fold :
              ∀ t, List.foldl (fun acc ex => ex.cast ∘ acc) s1.apply exs' t = F t
            := by
              intro t
              -- because F = foldl f id (s1::exs') = foldl f s1.apply exs'
              simp only [F, List.foldl_cons]
              rfl
            rw [F_eq_fold a, F_eq_fold b]
            rw [F_eq a, F_eq b]
            exact IH
  exact main l.length l exs rfl h x a b hmem

/-- `UnifyCtxMapCommon`: if `unifyCtx ctx1 ctx2 = some s`, then for any variable `x` whose
    type is `ty1` in `ctx1` and `ty2` in `ctx2`, the substitution `s` unifies them:
    `s.apply ty1 = s.apply ty2`. This is the soundness property of `unifyCtx`. -/
theorem UnifyCtxMapCommon {ctx1 ctx2 : TypeCtx} {s : CtxSubst ctx1 ctx2}
    (h : unifyCtx ctx1 ctx2 = some s) (x : Char) (ty1 ty2 : CurryType)
    (h1 : ctx1.lookup x = some ty1) (h2 : ctx2.lookup x = some ty2) :
    s.apply ty1 = s.apply ty2 := by
  let commonVarsExpr := List.filterMap (fun (x, a) =>
    match ctx2.env.lookup x with
    | some b => some (x, a, b)
    | none => none) ctx1.env
  have hx_in : (x, ty1, ty2) ∈ commonVarsExpr := by
    apply List.mem_filterMap.2
    use (x, ty1)
    constructor
    · exact LookupThenIn h1
    · grind
  unfold unifyCtx at h
  simp only at h
  match hc:
    unifyCtx'
      (List.filterMap
        (fun x =>
          match List.lookup x.1 ctx2.env with
          | some b => some (x.1, x.2, b)
          | none => none)
        ctx1.env) with
  | none => grind
  | some exs =>
    erw [hc] at h
    simp only [Option.some.injEq] at h
    rw [← h]  -- Replace s with the concrete CtxSubst.from construction
    dsimp [CtxSubst.from]  -- Unfold the structure so .apply becomes a lambda

    -- Prove equivalence between the two fold forms
    have fold_comp : ∀ (exs : List ExSubst) (f : CurryType → CurryType),
        List.foldl (fun acc ex => ex.cast ∘ acc) f exs =
        (List.foldl (fun acc ex => ex.cast ∘ acc) id exs) ∘ f := by
      intro exs
      induction exs with
      | nil => intro f; ext t; simp
      | cons ex exs ih =>
        intro f
        ext t
        simp only [List.foldl_cons, Function.comp_id, Function.comp_apply]
        rw [ih (ex.cast ∘ f)]
        rw [ih ex.cast]
        rfl
    have fold_eq : ∀ (exs : List ExSubst) (t : CurryType),
        List.foldl (fun acc ex => ex.cast acc) t exs =
        (List.foldl (fun acc ex => ex.cast ∘ acc) id exs) t := by
      intro exs
      induction exs with
      | nil => simp
      | cons ex exs ih =>
        intro t
        simp only [List.foldl_cons, Function.comp_id]
        rw [ih (ex.cast t)]
        rw [fold_comp exs ex.cast]
        rfl
    rw [fold_eq exs ty1, fold_eq exs ty2]
    exact UnifyCtxSound commonVarsExpr exs hc x ty1 ty2 hx_in

/-- Soundness of the principal-type algorithm helper `pp'`: if `pp' ctx t = some pair`, then
    `t` is well-typed in `pair.ctx` with type `pair.ty`, i.e. `check pair.ctx t = some pair.ty`. -/
theorem InferenceSound' (t : Term) (ctx : TypeCtx) (pair : PrincipalPair) :
  pp' ctx t = some pair → WellTyped pair.ctx t pair.ty := by
  intro h
  unfold WellTyped
  induction t generalizing ctx pair with
  | var c =>
      -- Don't change this line or else you can't expand pp'
      dsimp only [pp', check] at h ⊢
      match hc: ctx.lookup c with
      | none =>
        simp [hc] at h
        rw [← h]
        dsimp only
        unfold add TypeCtx.lookup
        simp
      | some ty0 =>
        rw [hc] at h
        simp at h
        rw [← h]
        dsimp only
        unfold TypeCtx.lookup
        unfold TypeCtx.lookup at hc
        rw [hc]
  | abs x m ind =>
      -- Don't change this line or else you can't expand pp'
      dsimp only [pp', check] at h ⊢

      match hm: pp' ctx m with
      | none =>
        simp [hm] at h
      | some pair' =>
        simp [hm] at h
        match hl: pair'.ctx.lookup x with
        | none =>
          -- Here pair'.ctx ⊆ pair.ctx, pair'.ctx :: (x, a) = pair.ctx
          simp [hl] at h
          specialize ind ctx pair'
          have ind' := ind hm
          have hm' : check pair.ctx m = some pair'.ty := by
            if hxm: Term.var x = m then
              -- contradiction: ind' now claims x is found in pair' instead
              rw [← hxm] at ind'
              unfold check at ind'
              rw [hl] at ind'
              grind
            else
              -- Now we know (x: a) found in pair'.ctx, since pair.ctx is bigger
              -- check should stay invariant
              let nc := next pair'.ctx
              have hp: pair.ctx = add x nc.fst nc.snd := by rw [← h]
              exact @CheckInvUnderAdd
                x m (by assumption)
                pair pair'
                (by assumption)
                (by assumption)
                (by trivial)
                (by assumption)
                (by assumption)
          simp [← h]
          -- Now we've arrived at lookup, since we just added (x: a) into pair
          -- This should also give us some
          unfold TypeCtx.lookup add
          -- By simplification we arrive at the conclusion
          grind
        | some ty =>
          simp [hl] at h
          simp [← h]
          specialize ind ctx pair'
          simp [ind hm, hl]
  | app m n indm indn =>
      -- Don't change this line or else you can't expand pp'
      simp [pp', check] at h ⊢
      -- Again, we unfold until we've eliminated all the contridictary cases
      match hm: pp' ctx m with
      | none => simp [hm] at h
      | some ⟨ctx_m, p1⟩ =>
        match hn: pp' ctx_m n with
        | none => simp [hm, hn] at h
        | some ⟨ctx_mn, p2⟩ =>
          match hum : unify p1 (p2.arrow (next ctx_mn).fst) with
          | none => grind
          | some s1 =>
            match hsubctx: 
              unifyCtx (applySubst s1.apply ctx_m) (applySubst s1.apply (next ctx_mn).snd) with
            | none => grind
            | some s2 =>
              simp [hm, hn, hum, hsubctx] at h ⊢
              -- Prove common property using lemmas from CtxSubst and Subst
              have h_arrow : ∀ a b, (s2.apply ∘ s1.apply) (CurryType.arrow a b) =
                                    CurryType.arrow ((s2.apply ∘ s1.apply) a) ((s2.apply ∘ s1.apply) b) := by
                intro a b
                simp only [Function.comp_apply]
                rw [s1.subst_rec a b]
                rw [s2.subst_rec (s1.apply a) (s1.apply b)]

              -- unfold away the checks
              match hcm: check pair.ctx m with
              | none =>
                specialize indm ctx { ctx := ctx_m, ty := p1 } hm
                dsimp only at indm
                simp [← h] at hcm
                have hms := @CheckSubst m p1 (s2.apply ∘ s1.apply) ctx_m indm h_arrow
                rw [SubstComp s2.apply s1.apply (next ctx_mn).snd] at hcm
                rw [← CheckInvUnderNextSubst ctx_mn (s2.apply ∘ s1.apply) m] at hcm
                have hcmn : (check (applySubst (s2.apply ∘ s1.apply) ctx_mn) m).isSome := by
                  exfalso
                  -- Obtain g from InferenceLookupInv applied to hn
                  have ⟨g, ⟨hlookup, ⟨hdist, _⟩⟩⟩ := InferenceLookupInv ctx_m ctx_mn _ hn
                  -- Apply CheckSubst to indm using g
                  have h1 := @CheckSubst m p1 g ctx_m indm hdist
                  -- Show check agrees on ctx_mn and applySubst g ctx_m for variables occurring in m
                  have h_eq : check ctx_mn m = check (applySubst g ctx_m) m := by
                    apply CheckEqIfOccursInv
                    intro x hx
                    -- By indm, x has a type in ctx_m
                    have ⟨ty, hty⟩ := CheckSuccessLookupSome m ctx_m p1 indm x hx
                    -- Use hlookup to get ctx_mn.lookup x = some (g ty)
                    have h_mn_lookup := hlookup x ty hty
                    -- Use LookupMap to get (applySubst g ctx_m).lookup x = some (g ty)
                    have h_apply_lookup := LookupMap g hty
                    rw [h_mn_lookup, ← h_apply_lookup]
                    rfl
                  rw [← h_eq] at h1
                  -- Now apply the final substitution f = s2 ∘ s1
                  let f := s2.apply ∘ s1.apply
                  have hf_dist : ∀ a b, f (a.arrow b) = (f a).arrow (f b) := by grind
                  have h2 := @CheckSubst m (g p1) f ctx_mn h1 hf_dist
                  -- h2 gives some (f (g p1)), contradicting hcm = none
                  rw [hcm] at h2
                  contradiction
                grind
              | some tym =>
                match hcn: check pair.ctx n with
                | none =>
                  -- Similar to check hcm = none
                  specialize indn ctx_m { ctx := ctx_mn, ty := p2 } hn
                  dsimp only at indn
                  simp [← h] at hcn
                  have hns := @CheckSubst n p2 (s2.apply ∘ s1.apply) ctx_mn indn h_arrow
                  rw [SubstComp s2.apply s1.apply (next ctx_mn).snd] at hcn
                  rw [← CheckInvUnderNextSubst ctx_mn (s2.apply ∘ s1.apply) n] at hcn
                  have hnenv: ctx_mn.env = (next ctx_mn).snd.env := by grind
                  have : check (applySubst (s2.apply ∘ s1.apply) ctx_mn) m = check (applySubst (s2.apply ∘ s1.apply) (next ctx_mn).snd) m := by
                    apply CheckInvUnderNextSubst
                  grind
                | some tyn =>
                  simp
                  match tym with
                  | CurryType.arrow a b =>
                    by_cases ha: a == tyn
                    -- All good case
                    · simp
                      constructor
                      · grind
                      · specialize indm ctx { ctx := ctx_m, ty := p1 } hm
                        specialize indn ctx_m { ctx := ctx_mn, ty := p2 } hn
                        dsimp only at indm
                        dsimp only at indn
                        have : a = tyn := by grind
                        subst this
                        clear ha
                        -- (s2 ∘ s1) p1 = a.arrow b
                        have hnenv: ctx_mn.env = (next ctx_mn).snd.env := by grind
                        have hsubctx': check (applySubst (s2.apply ∘ s1.apply) ctx_mn) m = check (applySubst (s2.apply ∘ s1.apply) (next ctx_mn).snd) m := by
                          apply CheckInvUnderNextSubst
                        have hsubm := @CheckSubst m p1 (s2.apply ∘ s1.apply) ctx_m indm h_arrow
                        -- From UnifySound, s1 unifies p1 and p2.arrow (next ctx_mn).1
                        have eq1 : s1.apply p1 = s1.apply (p2.arrow (next ctx_mn).1) := UnifySound _ _ _ hum
                        rw [s1.subst_rec] at eq1
                        -- Apply s2 to both sides
                        have eq2 : s2.apply (s1.apply p1) = s2.apply ((s1.apply p2).arrow (s1.apply (next ctx_mn).1)) := congrArg s2.apply eq1
                        rw [s2.subst_rec] at eq2

                        -- Connect s2.apply (s1.apply p1) with a.arrow b via the output context
                        have h_eq_m : check pair.ctx m = check (applySubst (s2.apply ∘ s1.apply) ctx_m) m := by
                          apply CheckEqIfOccursInv
                          intro x hx
                          -- By indm, x has a type in ctx_m
                          have ⟨ty_x, hlx⟩ := CheckSuccessLookupSome m ctx_m p1 indm x hx
                          -- Obtain the lookup-invariant substitution g from ctx_m to ctx_mn via hn
                          have ⟨g, ⟨hlookup_g, _, _⟩⟩ := InferenceLookupInv ctx_m ctx_mn n hn
                          have hlx_mn : ctx_mn.lookup x = some (g ty_x) := hlookup_g x ty_x hlx
                          -- (next ctx_mn).2 has the same environment as ctx_mn
                          have hlx_next : (next ctx_mn).2.lookup x = some (g ty_x) := by grind
                          -- Lookup in pair.ctx
                          have hlx_pair : pair.ctx.lookup x = some (s2.apply (s1.apply (g ty_x))) := by
                            rw [← h]  -- pair.ctx = applySubst s2.apply (applySubst s1.apply (next ctx_mn).2)
                            simp only
                            apply LookupMap s2.apply
                            apply LookupMap s1.apply
                            exact hlx_next
                          -- Lookup in the other context
                          have hlx' : (applySubst (s2.apply ∘ s1.apply) ctx_m).lookup x = some ((s2.apply ∘ s1.apply) ty_x) :=
                            LookupMap (s2.apply ∘ s1.apply) hlx
                          -- By unifyCtx, s2 unifies applySubst s1.apply ctx_m and applySubst s1.apply (next ctx_mn).2
                          -- So for common variable x: s2.apply (s1.apply (g ty_x)) = s2.apply (s1.apply ty_x)
                          have h_unif : s2.apply (s1.apply (g ty_x)) = s2.apply (s1.apply ty_x) :=
                            Eq.symm (UnifyCtxMapCommon hsubctx x (s1.apply ty_x) (s1.apply (g ty_x))
                              (LookupMap s1.apply hlx)
                              (LookupMap s1.apply hlx_next))
                          rw [hlx_pair, hlx', h_unif]
                          rfl
                        rw [h_eq_m] at hcm
                        have h_sub_m := hsubm
                        rw [hcm] at h_sub_m
                        injection h_sub_m with h_arrow_eq
                        -- Now h_arrow_eq : (s2.apply ∘ s1.apply) p1 = a.arrow b
                        rw [
                          ← s2.subst_rec (s1.apply p2) (s1.apply (next ctx_mn).1),
                          ← s1.subst_rec p2 (next ctx_mn).1,
                        ] at eq2
                        change (s2.apply ∘ s1.apply) p1 = s2.apply (s1.apply (p2.arrow (next ctx_mn).1)) at eq2
                        rw [← h_arrow_eq] at eq2

                        -- Handle n: show check pair.ctx n = some ((s2 ∘ s1) p2)
                        have h_n_check : check (applySubst (s2.apply ∘ s1.apply) ctx_mn) n = some ((s2.apply ∘ s1.apply) p2) :=
                          @CheckSubst n p2 (s2.apply ∘ s1.apply) ctx_mn indn h_arrow
                        have h_env_eq_n : pair.ctx.env = (applySubst (s2.apply ∘ s1.apply) ctx_mn).env := by
                          rw [← h]
                          simp [applySubst, next]
                        have h_eq_n : check pair.ctx n = check (applySubst (s2.apply ∘ s1.apply) ctx_mn) n :=
                          CheckInvUnderLabel n pair.ctx (applySubst (s2.apply ∘ s1.apply) ctx_mn) h_env_eq_n
                        grind
                    · specialize indm ctx { ctx := ctx_m, ty := p1 } hm
                      specialize indn ctx_m { ctx := ctx_mn, ty := p2 } hn
                      dsimp only at indm indn
                      exfalso

                      -- Step 1: show check pair.ctx m = check (applySubst (s2.apply ∘ s1.apply) ctx_m) m
                      have h_eq_m : check pair.ctx m = check (applySubst (s2.apply ∘ s1.apply) ctx_m) m := by
                        apply CheckEqIfOccursInv
                        intro x hx
                        obtain ⟨ty, hlx⟩ := CheckSuccessLookupSome m ctx_m p1 indm x hx
                        obtain ⟨g, hg, _, _⟩ := InferenceLookupInv ctx_m ctx_mn n hn
                        have h_mn_lookup : ctx_mn.lookup x = some (g ty) := hg x ty hlx
                        have h_next_lookup : (next ctx_mn).2.lookup x = some (g ty) := by grind
                        -- Lookup in the left context applySubst (s2∘s1) ctx_m
                        have h_left : (applySubst (s2.apply ∘ s1.apply) ctx_m).lookup x = some ((s2.apply ∘ s1.apply) ty) :=
                          LookupMap (s2.apply ∘ s1.apply) hlx
                        -- Lookup in the right context pair.ctx
                        have h_right : pair.ctx.lookup x = some (s2.apply (s1.apply (g ty))) := by
                          rw [← h]
                          apply LookupMap s2.apply
                          apply LookupMap s1.apply
                          exact h_next_lookup
                        -- By unifyCtx, s2 unifies the two corresponding types
                        have h_unif := UnifyCtxMapCommon hsubctx x (s1.apply ty) (s1.apply (g ty))
                          (LookupMap s1.apply hlx) (LookupMap s1.apply h_next_lookup)
                        grind

                      -- Step 2: apply CheckSubst to indm to get the result after applySubst
                      have h_subst_m := @CheckSubst m p1 (s2.apply ∘ s1.apply) ctx_m indm h_arrow

                      -- Combine to get the concrete value of check pair.ctx m
                      have hm_val : check pair.ctx m = some ((s2.apply ∘ s1.apply) p1) := by
                        rw [h_eq_m, h_subst_m]

                      -- Substitute into the known hcm
                      rw [hm_val] at hcm
                      injection hcm with hm_arrow

                      -- Similarly handle n
                      have h_eq_n : check pair.ctx n = check (applySubst (s2.apply ∘ s1.apply) ctx_mn) n := by
                        apply CheckEqIfOccursInv
                        intro x hx
                        obtain ⟨ty, hlx⟩ := CheckSuccessLookupSome n ctx_mn p2 indn x hx
                        have h_next_lookup : (next ctx_mn).2.lookup x = some ty := by grind
                        have h_left : (applySubst (s2.apply ∘ s1.apply) ctx_mn).lookup x = some ((s2.apply ∘ s1.apply) ty) :=
                          LookupMap (s2.apply ∘ s1.apply) hlx
                        have h_right : pair.ctx.lookup x = some (s2.apply (s1.apply ty)) := by
                          rw [← h]
                          apply LookupMap s2.apply
                          apply LookupMap s1.apply
                          assumption
                        grind

                      have h_subst_n := @CheckSubst n p2 (s2.apply ∘ s1.apply) ctx_mn indn h_arrow
                      have h_unif1 := UnifySound p1 (p2.arrow (next ctx_mn).1) s1 hum
                      grind
                  | CurryType.phi _ =>
                    specialize indm ctx { ctx := ctx_m, ty := p1 } hm
                    dsimp only at indm
                    have hsubm := @CheckSubst m p1 (s2.apply ∘ s1.apply) ctx_m indm h_arrow
                    exfalso
                    -- Obtain substitution g from ctx_m to ctx_mn via InferenceLookupInv applied to hn
                    obtain ⟨g, hg, hg_dist, _⟩ := InferenceLookupInv ctx_m ctx_mn n hn
                    -- Show check agrees on pair.ctx m and applySubst (s2∘s1) ctx_m for variables in m
                    have h_eq_check : check pair.ctx m = check (applySubst (s2.apply ∘ s1.apply) ctx_m) m := by
                      apply CheckEqIfOccursInv
                      intro x hx
                      obtain ⟨ty, hlx⟩ := CheckSuccessLookupSome m ctx_m p1 indm x hx
                      -- Lookup in the left context
                      have h_left : (applySubst (s2.apply ∘ s1.apply) ctx_m).lookup x = some ((s2.apply ∘ s1.apply) ty) :=
                        LookupMap (s2.apply ∘ s1.apply) hlx
                      -- Lookup in the right context pair.ctx
                      have h_lookup_mn : ctx_mn.lookup x = some (g ty) := hg x ty hlx
                      have h_lookup_next : (next ctx_mn).2.lookup x = some (g ty) := by grind
                      have h_right1 : (applySubst s1.apply (next ctx_mn).2).lookup x = some (s1.apply (g ty)) :=
                        LookupMap s1.apply h_lookup_next
                      have h_right2 : pair.ctx.lookup x = some (s2.apply (s1.apply (g ty))) := by
                        rw [← h]
                        exact LookupMap s2.apply h_right1
                      -- By unifyCtx, s2 unifies the two corresponding types
                      have h_unif := UnifyCtxMapCommon hsubctx x (s1.apply ty) (s1.apply (g ty))
                        (LookupMap s1.apply hlx) (LookupMap s1.apply h_lookup_next)
                      grind
                    have h_arrow_eq : (s2.apply ∘ s1.apply) p1 =
                        (s2.apply (s1.apply p2)).arrow (s2.apply (s1.apply (next ctx_mn).1)) := by
                      rw [← s2.subst_rec, ← s1.subst_rec]
                      have := UnifySound p1 (p2.arrow (next ctx_mn).1) s1 hum
                      grind
                    grind

/-- Soundness of the principal-type algorithm `pp`: if `pp t = some pair`, then `t` is
    well-typed in `pair.ctx` with type `pair.ty`. This is the top-level soundness statement. -/
theorem InferenceSound (t : Term) (pair : PrincipalPair) : 
  pp t = some pair → WellTyped pair.ctx t pair.ty := by
  unfold pp
  intro h
  exact InferenceSound' t emptyEnv pair h
