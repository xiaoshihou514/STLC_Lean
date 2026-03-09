#import "@preview/charged-ieee:0.1.4": ieee
#import "@preview/ctheorems:1.1.3": *

// This fix prevents the "expected string or function" error in charged-ieee
#show figure.where(kind: "theorem"): set figure(numbering: "1.1")

#set page(numbering: "1 / 1")

#let theorem = thmbox(
  "theorem",
  "Theorem",
  inset: 0em,
)

#let lemma = thmbox(
  "theorem",
  "Lemma",
  inset: 0em,
)

#let remark = thmbox(
  "theorem",
  "Remark",
  inset: 0em,
)

#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  inset: 0em,
)

#let definition = thmbox(
  "definition",
  "Definition",
  inset: 0em,
)

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")

#show: ieee.with(
  title: [Principal Type Inference for the STLC: Addendum — Soundness Completion],
  authors: (
    (
      name: "xiaoshihou514",
      email: "xiaoshihou@tutamail.com",
    ),
  ),
  abstract: [
    This addendum extends the Lean 4 formalisation of principal type inference for the Simply Typed Lambda Calculus described in the companion report. The primary achievement is the resolution of the application case of `InferenceSound'`, which was left as an open item in the original development. A suite of new supporting lemmas was developed, `unifyCtx` was refactored for correctness.
  ],
  index-terms: (
    "type inference",
    "Lean 4",
    "soundness",
    "unification",
  ),
  bibliography: bibliography("refs.bib"),
)
#show: thmrules

= Overview

This document is an addendum to the companion report _Principal Type Inference for the Simply Typed Lambda Calculus: A Lean Formalisation_. The additions fall into three categories:

+ *Correctness fix to `unifyCtx`* (#ref(<para_2>, form: "page")): the prior implementation unified each common-variable pair independently, without threading substitutions through subsequent pairs. A new recursive helper `unifyCtx'` fixes this.
+ *New supporting lemmas and definitions* (#ref(<para_3>, form: "page")): a collection of lemmas about variable occurrence, lookup, and substitution invariants, needed to discharge the application case.
+ *Resolution of the open item in `InferenceSound'`* (#ref(<para_4>, form: "page")): the application case of the main soundness lemma is now fully proved, closing the primary open item from the companion report. `NextFresh`, previously left as a sorry'd assumption, is also now proved.

= Correctness Fix: Refactoring `unifyCtx` <para_2>

The prior `unifyCtx` unified each common-variable pair _independently_: it mapped over the
common variable list calling `unify` on each pair in isolation, then composed the resulting
substitutions left-to-right. This is incorrect: the substitution from unifying the first pair
should be applied to the remaining pairs before those are unified, just as Robinson's algorithm
proceeds sequentially.

The new implementation introduces a recursive helper:

#definition[
  $
    "unifyCtx'"([]) = "some"([]) \
    "unifyCtx'"((x, a, b) :: "rest") =\
    cases(
      "none, unify"(a, b) = "none",
      "some"([s_1] ++ "exs'")", unify"(a, b) = "some"(s_1) "and",
      quad quad quad quad "unifyCtx'"("rest"."map"(s_1)) = "some"("exs'")
    )
  $

  where $"rest"."map"(s_1)$ applies $s_1$ to all remaining type pairs before recursing.
]

`unifyCtx` is now defined in terms of `unifyCtx'`: it collects all common variables into a list,
calls `unifyCtx'`, then composes the resulting substitutions left-to-right via `foldl`.

= New Supporting Lemmas and Definitions <para_3>

All entries in this section are new results residing in `proof.lean` unless otherwise noted.

== Definitions

#definition([`distributes`])[
  $"distributes"(f) := forall a, b, quad f(a arrow.r b) = f(a) arrow.r f(b).$
  A predicate asserting that a type function distributes over arrow types.
  Required by `CheckSubst` to push a substitution through function types.
]

#definition([`lookup_inv`])[
  $"lookup_inv"(f, Gamma, Gamma') := forall x, tau, quad Gamma(x) = "some"(tau) => Gamma'(x) = "some"(f(tau)).$
  A predicate asserting that $f$ is a _lookup invariant_ from $Gamma$ to $Gamma'$:
  if $Gamma$ assigns $tau$ to $x$, then $Gamma'$ assigns $f(tau)$ to $x$.
]

#definition([`check_inv`])[

  $"check_inv"(f, Gamma, Gamma') := forall t, tau, quad "check"(Gamma, t) = "some"(tau) => "check"(Gamma', t) = "some"(f(tau)).$ A predicate asserting that $f$ is a _check invariant_ from $Gamma$ to $Gamma'$.
]

#definition([`equiv_lookup_on`])[$"equiv_lookup_on"(f, g, Gamma) := forall x, tau, quad Gamma(x) = "some"(tau) => g(tau) = f(tau).$ Two substitutions $f$ and $g$ agree on all types assigned by $Gamma$.]

#definition([`equiv_check_on`])[
  $"equiv_check_on"(f, g, Gamma) := forall t, tau, quad "check"(Gamma, t) = "some"(tau) => g(tau) = f(tau).$
  Two substitutions $f$ and $g$ agree on all types derivable under $Gamma$.
]

#definition([`occursInTerm`])[
  The predicate $"occurs"(x, t)$ holds when variable $x$ appears in term $t$:
  $
    &"occurs"(x, "var" y) := (x = y) \
    &"occurs"(x, lambda y. m) := (x = y) or "occurs"(x, m) \
    &"occurs"(x, m " " n) := "occurs"(x, m) or "occurs"(x, n).
  $
]

== Auxiliary Lemmas

#theorem([`LookupThenIn`])[
  If $"lookup"(x, l) = "some"(y)$ then $(x, y) in l$.
]

#theorem([`FoldlInv`])[
  If $f(a) = f(b)$, then for any list of substitutions $"es"$,
  $
    ("es"."foldl"(lambda "acc", "ex". "ex" compose "acc", f))(a) =\
    ("es"."foldl"(lambda "acc", "ex". "ex" compose "acc", f))(b).
  $
  Left-folding further substitutions after $f$ preserves the equality $f(a) = f(b)$. This is a corollary of `congrArg`.
]

#theorem([`SubstLookup`])[
  If $Gamma(x) = "some"(tau)$ then $("applySubst"(f, Gamma))(x) = "some"(f(tau))$.
]

#theorem([`CheckEqIfOccursInv`])[

  If $forall x, "occurs"(x, t) => Gamma_1(x) = Gamma_2(x)$, then
  $"check"(Gamma_1, t) = "check"(Gamma_2, t)$.

  Type-checking of a term depends only on the types assigned to variables that _occur_ in it.
]

#theorem([`CheckSuccessLookupSome`])[

  If $"check"(Gamma, t) = "some"(tau)$, then for every variable $x$ occurring in $t$,
  $exists tau', Gamma(x) = "some"(tau')$.

  Successful type-checking implies all occurring variables are bound in the context.
]

== Soundness of `unifyCtx'` and `unifyCtx`

#theorem([`UnifyCtxSound`])[

  If $"unifyCtx'"(l) = "some"("exs")$ and $(x, a, b) in l$, then letting
  $F = "exs"."foldl"(lambda "acc", "ex". "ex" compose "acc", "id")$, we have $F(a) = F(b)$.

  The composed substitution from `unifyCtx'` unifies every pair in the input list.
]

#theorem([`UnifyCtxMapCommon`])[

  If $"unifyCtx"(Gamma_1, Gamma_2) = "some"(s)$, $Gamma_1(x) = "some"(tau_1)$, and
  $Gamma_2(x) = "some"(tau_2)$, then $s("apply")(tau_1) = s("apply")(tau_2)$.

  The output substitution of `unifyCtx` equates all types assigned to common variables
  by the two input contexts.
]

== Invariant Lemmas for `pp'`

#theorem([`InferenceSubsetMap`])[

  If $"pp'"(Gamma, m) = "some"(chevron.l Gamma', tau chevron.r)$, then there exists a substitution $f$ such that
  $("applySubst"(f, Gamma))."env" subset.eq Gamma'."env"$.

  The output context contains (a substitution image of) the input context's bindings.
]

#theorem([`InferenceLookupInv`])[

  If $"pp'"(Gamma, m) = "some"(chevron.l Gamma', dots chevron.r)$, then there exists a substitution $f$
  such that:
  - $"lookup_inv"(f, Gamma, Gamma')$,
  - $"distributes"(f)$,
  - for any other $g$ with $"lookup_inv"(g, Gamma, Gamma')$, we have $"equiv_lookup_on"(f, g, Gamma)$.
]

#theorem([`InferenceCheckInv`])[

  If $"pp'"(Gamma, m) = "some"(chevron.l Gamma', dots chevron.r)$, then there exists a substitution $f$
  such that:
  - $"check_inv"(f, Gamma, Gamma')$,
  - $"distributes"(f)$,
  - for any other $g$ with $"check_inv"(g, Gamma, Gamma')$ on types derivable under $Gamma$, we have $"equiv_check_on"(f, g, Gamma)$.
]

= Resolution of open item in `InferenceSound'` <para_4>

The companion report left the _application_ case of the main soundness lemma as an open item (the proof contained a `sorry`). This case is now fully proved.

#theorem([`InferenceSound'`])[

  If $"pp'"(Gamma, t) = "some"(p)$ then $"check"(p."ctx", t) = "some"(p."ty")$.
]

The variable and abstraction cases were already proved in the companion report. The new work resolves the
application case:

*Setting.* Suppose $t = m " " n$. The algorithm proceeds as:
$
  (Gamma_m, tau_1) &= "pp'"(Gamma, m) \
  (Gamma_n, tau_2) &= "pp'"(Gamma_m, n) \
  alpha &= "next"(Gamma_n)."fst" \
  s_1 &= "unify"(tau_1, tau_2 arrow.r alpha) \
  s_2 &= "unifyCtx"(s_1(Gamma_m), s_1(Gamma_n)) \
  p."ctx" &= s_2(s_1(Gamma_n)), quad p."ty" = s_2(s_1(alpha)).
$

The proof proceeds by cases on $"check"(p."ctx", m)$ and $"check"(p."ctx", n)$.

#proof[
  1.
  $
    &"check" "pair.ctx" m\
    &= "check" ("applySubst" (s_2 compose s_1) "ctx_m") "m"
  $ (via `CheckEqIfOccursInv`)

  For every variable $x$ occurring in $m$, one shows $p."ctx"(x) = (s_2 compose s_1)(Gamma_m)(x)$ using `InferenceLookupInv` (to get a canonical $g$ from $Gamma_m$ to $Gamma_n$) and `UnifyCtxMapCommon` (to show $s_2$ equates the $s_1$-images of corresponding types).

  2.
  $
    &"check" ("applySubst" (s_2 ∘ s_1) "ctx_m") "m"\
    &= "some" ((s_2 compose s_1) p_1)
  $

  By the induction hypothesis on $m$ together with `CheckSubst`.

  3. $(s_2 ∘ s_1)(tau_1) = (s_2 ∘ s_1)(tau_2) → (s_2 ∘ s_1)(alpha)$

  From step 2, since $s_1(tau_1) = s_1(tau_2 → alpha)$ by `UnifySound`, and $s_2$ distributes over arrows.

  4.
    $
      "check" "pair.ctx" ("m" "n") = "some" p."ty"
    $

    By induction hypothesis on $n$ (giving $"check" "pair.ctx" n = "some" ((s_2 ∘ s_1) "p2")$) and the arrow type from step 3, which ensures the argument type matches; hence the result is $"some" p."ty"$ where $p."ty" = (s_2 ∘ s_1)(alpha)$.

    The `if`/`else` branches where `check` returns `none` are also handled by contradiction, using the same `InferenceLookupInv` + `CheckEqIfOccursInv` machinery.
]

#theorem([`InferenceSound`])[
  If $"pp"(t) = "some"(p)$ then $"check"(p."ctx", t) = "some"(p."ty")$.
]

#proof[
  $"pp"(t) = "pp'"(Gamma_emptyset, t)$. Apply `InferenceSound'` directly.
  The theorem is now proved with no remaining `sorry`.
]

= `NextFresh` Proved

#remark([`NextFresh`])[
  The assumption that `next ctx` always produces a fresh type variable is now fully proved.
  Formally:
  $
    "ctx"(x) = "some"(tau) arrow.l.r\
    ("add"(y, "next"("ctx")."fst", "next"("ctx")."snd"))(x) = "some"(tau).
  $
  The proof proceeds by unfolding `TypeCtx.lookup`, `add`, and `next` via `simp`, then
  closing with `grind`. The key insight is that `add` prepends a new binding for $y$, and
  since $x eq.not y$, the lookup of $x$ is unaffected; `grind` discharges the resulting
  equality automatically.
]

= Summary of Changes

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*File*], [*Change*], [*Status*]),
    [`inference.lean`], [`unifyCtx` refactored; `unifyCtx'` added], [Complete],
    [`proof.lean`], [`InferenceSubsetMap`], [Complete],
    [`proof.lean`], [`NextFresh`], [Complete],
    [`proof.lean`], [`SubstLookup`], [Complete],
    [`proof.lean`],
    [`distributes`, `lookup_inv`, `check_inv`,\ `equiv_lookup_on`, `equiv_check_on`],
    [Complete],

    [`proof.lean`], [`InferenceLookupInv`], [Complete],
    [`proof.lean`], [`InferenceCheckInv`], [Complete],
    [`proof.lean`], [`occursInTerm`], [Complete],
    [`proof.lean`], [`CheckEqIfOccursInv`], [Complete],
    [`proof.lean`],
    [`CheckSuccess`\
      `LookupSome`],
    [Complete],

    [`proof.lean`], [`LookupThenIn`, `FoldlInv`], [Complete],
    [`proof.lean`], [`UnifyCtxSound`], [Complete],
    [`proof.lean`], [`UnifyCtxMapCommon`], [Complete],
    [`proof.lean`], [`InferenceSound'` (application case)], [★ Complete],
    [`proof.lean`], [`InferenceSound`], [★ Complete],
  ),
  caption: [Summary of new and modified results.],
)
#pagebreak()
= AI Assistance Acknowledgement

The formalisation presented in this paper was developed with the assistance of an AI language model, specifically *DeepSeek* @deepseek. The AI was employed in two complementary roles:

1. *Initial verification of proof ideas*: Due to the originality of the proofs, I continuously propose new ideas and test their validity. AI assists me in quickly filtering out erroneous ideas and providing counterexamples, thereby saving time on manual verification.

2. *Proving intuitive results*: For certain intuitive lemmas that require detailed derivation (not directly tagged as solvable by `grind`), I use AI to generate preliminary lengthy proofs. I then refine them by removing parts that can be directly handled by automated tools like `grind`, ultimately producing rigorous proofs.

I ensure that all final submissions have been understood and reviewed by me. The use of AI is merely an auxiliary tool and does not replace my independent thinking or academic responsibility.
