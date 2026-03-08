#import "@preview/modern-cug-report:0.1.3": *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set heading(numbering: "1.1")

#show: doc => template(
  doc,
  footer: "简单类型λ演算的主类型推导",
)

#set text(font: "Source Han Serif", lang: "zh")
#show raw: set text(
  font: "Fira Code Retina",
  size: 0.85em,
)

// This fix prevents the "expected string or function" error in ctheorems
#show figure.where(kind: "theorem"): set figure(numbering: "1.1")

#let 定理 = thmbox("theorem", "定理", inset: 0em)
#let 引理 = thmbox("theorem", "引理", inset: 0em)
#let 推论 = thmplain("corollary", "推论", base: "theorem", inset: 0em)
#let 定义 = thmbox("definition", "定义", inset: 0em)
#let 注记 = thmbox("theorem", "注记", inset: 0em)
#let 例 = thmplain("example", "例").with(numbering: none)
#let 证明 = thmproof("proof", "证明")

#let rpl(a, s, t) = $#t [#a := #s]$

#show: thmrules

= 引言

简单类型λ演算（Simply Typed Lambda Calculus，STLC）由阿隆佐·丘奇 @church1940 引入，经哈斯凯尔·柯里 @curry1934 代数化研究，是有类型函数式编程的理论基础。其核心算法是*主类型推导*：给定项 $t$，计算最一般的类型判断 $Gamma tack.r t : tau$，使得所有其他类型判断都是它的特例。罗杰·欣德利 @hindley1969 证明了 STLC 的主类型始终存在；罗宾·米尔纳 @milner1978 与达马斯-米尔纳 @damas1982 将该结论推广至多态 $lambda$-演算。

罗宾逊合一算法 @robinson1965 是大多数类型推导过程的计算核心。其终止性论证需要以自由类型变量集合的势作为良基度量，并辅以一个挤压引理。

*本文内容一览*：

+ STLC 定义及类型检查器；
+ 主类型推导算法的 Lean 4 实现；
+ 利用 Lean 依赖类型系统对罗宾逊合一算法终止性的证明；
+ 类型推导算法的完整可靠性定理。

本文分发协议为#link("https://creativecommons.org/licenses/by-sa/4.0/")[*CC BY-SA*]，代码开源协议为#link("https://jxself.org/translations/gpl-3.zh.shtml")[*GPL V3*]。


= 背景与基本定义

== 简单柯里类型与λ演算

#定义[
  *简单柯里类型*（CurryType）定义如下：
  $
    tau, sigma ::= phi_p | tau arrow.r sigma
  $
  其中 $p$ 为类型变量的编号（本文使用字符表示），$arrow.r$ 为右结合的函数类型构造符。

  ```lean
  inductive CurryType : Type
  | phi   : Char → CurryType
  | arrow : CurryType → CurryType → CurryType
  ```
]

#定义[
  *λ表达式*（Term）定义如下：
  $
    t, s ::= x | lambda x . t | t" "s
  $
  其中 $x$ 为变量的编号（本文使用字符表示）。

  ```lean
  inductive Term : Type
  | var : Char → Term
  | abs : Char → Term → Term
  | app : Term → Term → Term
  ```
]

#定义[
  *类型上下文*（TypeCtx）是由偶对 $(x, tau) in "Char" times "CurryType"$ 组成的有限列表，加上一个计数器（用于生成新的类型变量）。记 $Gamma(x)$ 为 $Gamma$ 中 $x$ 对应的第一个类型（若存在）。空上下文为 $Gamma_emptyset = ([], "A")$。
  上下文扩展记作 $Gamma + (x : tau)$。

  ```lean
  structure TypeCtx where
    env   : List (Char × CurryType)
    label : Char
  ```

  `next ctx`返回一个新的类型变量并更新计数器；`add c ty ctx`向列表插入$(c, "ty")$。
]

#定义[
  类型 $tau$ 的*自由类型变量集合*（`vars`）定义为：
  $
    &"vars"(phi_p) = brace.l.stroked p brace.r.stroked \
    &"vars"(tau arrow.r sigma) = "vars"(tau) union "vars"(sigma)
  $
]

#定义[
  *类型赋值*（类型判断）$Gamma tack.r t : tau$ 由三条标准规则定义：
  $
    frac(Gamma(x) = tau, Gamma tack.r x : tau) quad
    frac(Gamma + (x : tau_1) tack.r m : tau_2, Gamma tack.r lambda x . m : tau_1 arrow.r tau_2) quad
    frac(Gamma tack.r m : tau_1 arrow.r tau_2 quad Gamma tack.r n : tau_1, Gamma tack.r m " " n : tau_2)
  $
]

== 类型替换

#定义[
  *类型分配律*：令$S : "CurryType" -> "CurryType"$，若$S(tau arrow.r sigma) = S(tau) arrow.r S(sigma)$，则称$S$满足类型分配律。
]

#定义[
  *类型替换*（`Subst`）是满足类型分配律的函数 $S : "CurryType" -> "CurryType"$。定义对上下文的逐点应用： $S(Gamma) = brace.l.stroked (x, S(tau)) | (x, tau) in Gamma brace.r.stroked$，在代码中通过 `applySubst` 实现。
]

#定义[
  对类型变量 $alpha$ 和类型 $sigma$，*替换* $rpl(alpha, sigma, tau)$ 将 $tau$ 中 $alpha$ 的所有自由出现替换为 $sigma$：
  $
    rpl(alpha, sigma, phi_alpha) &= sigma \
    rpl(alpha, sigma, phi_beta) &= phi_beta quad (beta eq.not alpha) \
    rpl(alpha, sigma, tau arrow.r tau') &= rpl(alpha, sigma, tau) arrow.r rpl(alpha, sigma, tau')
  $
  在 Lean 中实现为 `replaceVar`，仅在通过出现性检查（occurs check）$not "occursIn"(alpha, sigma)$ 后才构造为 `Subst`。
]

= 实现

== `check` 函数 <sec-check>

*类型检查函数* `check` 验证项是否符合类型赋值规则。它要求上下文已包含项中所有自由变量的类型绑定，作为形式化*规范*——推导算法 `pp'` 的可靠性正是相对于 `check` 的输出来陈述和证明的。

#定义[
  $
    "check"(Gamma, x) &= Gamma(x) \
    "check"(Gamma, lambda x . m) &=
    cases(
      "none" quad & "if" "check"(Gamma, m) = "none" "or" Gamma(x) = "none",
      "some"(tau' arrow.r tau) quad & "if" "check"(Gamma, m) = "some"(tau) "and" Gamma(x) = "some"(tau'),
    ) \
    "check"(Gamma, m " " n) &=
    cases(
      "some"(b) quad & "if" "check"(Gamma, m) = "some"(a arrow.r b) "and" "check"(Gamma, n) = "some"(a),
      "none" quad & "otherwise"
    )
  $

  Lean 实现：
  ```lean
  def check (ctx : TypeCtx) (t : Term) : Option CurryType :=
    match t with
    | .var c => ctx.lookup c
    | .abs x m =>
      match check ctx m with
      | none => none
      | some ty => match ctx.lookup x with
        | none    => none
        | some ty' => some (CurryType.arrow ty' ty)
    | .app m n =>
      match check ctx m, check ctx n with
      | some (.arrow a b), some ty_n => if a == ty_n then some b else none
      | _, _ => none
  ```
]

== `Subst` 类型

`Subst left right` 是一个依赖类型结构，将替换函数 `apply` 与三个性质打包在一起。这三个性质是终止性证明的关键：

$
  P_1 &: forall tau. "vars"("apply"(tau)) subset.eq "vars"("left") union "vars"("right") union "vars"(tau) \
  P_2 &: forall tau. lr(|"vars"("apply"(tau))|) = lr(|"vars"("left") union "vars"("right") union "vars"(tau)|) arrow.r.double "apply" = "id" \
  P_3 &: forall a, b. "apply"(a arrow.r b) = "apply"(a) arrow.r "apply"(b)
$

$P_1$ 限制了像的变量域；$P_2$ 声称：若像的变量集合势与原集合相等，则该替换必为恒等替换（这是终止性的关键约束）；$P_3$ 是分配律。`Subst` 有四种构造子：`id`（恒等）、`replace`/`replacer`（单变量替换）、`comp`（复合）。

== `unify` 算法 <sec-unify>

#定义[
  `unify` 接受两个类型并返回一个可选的合一替换：

  $
    &"unify"(phi_p, phi_p) = "some"("id") \
    &"unify"(phi_p, phi_q) = "some"("replace"(p, phi_q)) quad (p eq.not q) \
    &"unify"(phi_p, tau) = "some"("replace"(p, tau)) quad (not "occ"(p, tau)) \
    &"unify"(phi_p, tau) = "none" quad ("occ"(p, tau)) \
    &"unify"(tau, phi_p) = "some"("replacer"(p, tau)) quad (not "occ"(p, tau)) \
    &"unify"(tau arrow.r tau', sigma arrow.r sigma') =
    cases(
      "none" quad & "if" "unify"(tau, sigma) = "none",
      "none" quad & "if" "unify"(tau, sigma) = "some"(S_1) "and" "unify"(S_1(tau'), S_1(sigma')) = "none",
      "some"("comp"(S_1, S_2)) quad & "otherwise"
    )
  $
]

=== `unify` 的终止性

`unify` 的终止性并不显然，因为箭头情形进行了*两次*递归调用，且第二次调用作用于 $S_1$ 像——而非原始的子项，这使得测度递减的证明更加棘手。

#定理("unify 的终止性")[
  `unify` 在字典序度量
  $
    mu(tau_1, tau_2) = (lr(|"vars"(tau_1) union "vars"(tau_2)|), "sz"(tau_1) + "sz"(tau_2))
  $
  下终止。
]

#证明[
  *第一次调用* `unify(τ, σ)`：$"vars"(tau) union "vars"(sigma) subset.eq "vars"(tau arrow.r tau') union "vars"(sigma arrow.r sigma')$，
  势不增；尺寸严格缩小。字典序严格下降。

  *第二次调用* `unify(S₁(τ'), S₁(σ'))`：若势严格缩小则完成。否则势保持，由性质 $P_2$ 推得 $S_1 = "id"$；当 $S_1 = "id"$ 时化简后尺寸严格缩小。
]

终止性证明在 Lean 中通过定义一个自定义的良基关系（`WellFoundedRelation`）实现，将上述度量编码为 `Nat × Nat` 上的字典序。

== 上下文合一：`unifyCtx` 与 `unifyCtx'`

上下文合一将两个类型上下文中共有变量的类型两两合一。

先前的实现对每对共有变量*独立地*调用 `unify` 并组合结果——这是错误的：合一第一对产生的替换应当在合一第二对之前先作用于剩余所有对，正如罗宾逊算法所规定的。

为此引入递归辅助函数：

#定义[`unifyCtx'`][
  ```lean
  def unifyCtx' (commonVars : List (Char × CurryType × CurryType))
    : Option (List ExSubst) :=
    match commonVars with
    | [] => some []
    | (_, a, b) :: rest =>
      match unify a b with
      | none    => none
      | some s1 =>
        -- 将 s1 作用于所有剩余对，再递归处理
        let rest' := rest.map (fun (y, ty1, ty2) =>
                       (y, s1.apply ty1, s1.apply ty2))
        match unifyCtx' rest' with
        | none       => none
        | some substs => some (ExSubst.from s1 :: substs)
  ```

  其中 `ExSubst` 是对 `Subst` 的类型擦除包装，使得不同索引类型的替换可存入同质列表。
]

`unifyCtx` 基于 `unifyCtx'` 构建：收集所有共有变量三元组 $(x, Gamma_1(x), Gamma_2(x))$，调用 `unifyCtx'`，然后用 `foldl` 从左到右复合所有替换：

```lean
def unifyCtx (ctx1 ctx2 : TypeCtx) : Option (CtxSubst ctx1 ctx2) :=
  let commonVars := ctx1.env.filterMap (fun (x, a) =>
    ctx2.env.lookup x |>.map (fun b => (x, a, b)))
  match unifyCtx' commonVars with
  | none      => none
  | some exList =>
    let apply t := exList.foldl (fun acc ex => ex.cast acc) t
    some (CtxSubst.from commonVars apply ⋯ ctx1 ctx2)
```

== 主类型推导算法 `pp'` <sec-pp>

#定义[
  辅助函数 $"pp'" : "TypeCtx" times "Term" -> "Option"("PrincipalPair")$ 按项的结构分情形定义。

  *变量情形。* 设 $(alpha, Gamma') = "next"(Gamma)$：
  $
    "pp'"(Gamma, x) = cases(
      "some"(Gamma, tau) quad & "if" Gamma(x) = "some"(tau),
      "some"(Gamma' + (x : alpha), alpha) quad & "if" Gamma(x) = "none",
    )
  $

  *抽象情形。* 设 $(alpha, Gamma'') = "next"(Gamma')$：
  $
    "pp'"(Gamma, lambda x . m) = cases(
      "none" quad & "if" "pp'"(Gamma, m) = "none",
      "some"(Gamma', tau' arrow.r tau) quad & "if" Gamma'(x) = "some"(tau'),
      "some"(Gamma'' + (x : alpha), alpha arrow.r tau) quad & "if" Gamma'(x) = "none",
    )
  $

  *应用情形。* 设 $(Gamma_m, pi_1) = "pp'"(Gamma, m)$，$(Gamma_n, pi_2) = "pp'"(Gamma_m, n)$，$(alpha, Gamma_3) = "next"(Gamma_n)$，$S_1 = "unify"(pi_1, pi_2 arrow.r alpha)$，$S_2 = "unifyCtx"(S_1(Gamma_m), S_1(Gamma_3))$，则：
  $
    "pp'"(Gamma, m " " n) = "some"(S_2(S_1(Gamma_3)), S_2(S_1(alpha)))
  $
]

顶层函数 $"pp"(t) := "pp'"(Gamma_emptyset, t)$。

= 结构性引理

本章收录支撑主要可靠性定理的基础引理。

== 自由变量引理

#引理([`SizeGtZ`])[每个类型的结构尺寸严格大于零：$forall tau, "sz"(tau) > 0$。]

#引理([`VarsArrow`])[$forall tau, tau', "vars"(tau) subset.eq "vars"(tau arrow.r tau')$。]

#引理([`ReplaceVarScope`])[若 $not "occ"(alpha, sigma)$，则 $forall tau, "vars"(rpl(alpha, sigma, tau)) subset.eq brace.l.stroked alpha brace.r.stroked union "vars"(sigma) union "vars"(tau)$。证明对 $tau$ 作结构归纳。]

#引理([`OccursInIffInVars`])[$c in "vars"(tau) arrow.r.double "occursIn"(c, tau) = "true"$。建立了 `Finset` 与 `Bool` 两种自由变量表示之间的联系。]

#引理([`ReplaceElim`])[若 $not "occ"(alpha, sigma)$，则 $forall tau, alpha in.not "vars"(rpl(alpha, sigma, tau))$。出现性检查确保 $alpha$ 不会通过 $sigma$ 被重新引入。]

#引理([`ReplaceAddsNewVars`])[若 $not "occ"(alpha, sigma)$，则 $forall tau, lr(|"vars"(rpl(alpha, sigma, tau))|) eq.not lr(|brace.l.stroked alpha brace.r.stroked union "vars"(sigma) union "vars"(tau)|)$。]

#证明[
  设 $L = "vars"(rpl(alpha, sigma, tau))$，$R = brace.l.stroked alpha brace.r.stroked union "vars"(sigma) union "vars"(tau)$。假设 $|L| = |R|$。由 `ReplaceVarScope` 得 $L subset.eq R$；由 `ReplaceElim` 得 $alpha in.not L$；而 $alpha in R$，故 $L subset.neq R$。由 Mathlib 引理 `Finset.eq_of_subset_of_card_le`，$|R| lt.eq |L|$ 与 $L subset.eq R$ 合并推得 $L = R$，矛盾。
]

== `check` 的结构性质

#引理([`CheckInvUnderLabel`])[`check` 只依赖上下文的 `env` 字段，与 `label` 无关：若 $Gamma."env" = Gamma'."env"$，则 $"check"(Gamma, t) = "check"(Gamma', t)$。]

#引理([`CheckInvUnderAdd`])[若 $Gamma'(x) = "none"$，$"ctx" = Gamma' + (x : alpha)$，$m eq.not "var" x$，且 $"check"(Gamma', m) = "some"(pi)$，则 $"check"("ctx", m) = "some"(pi)$。即向上下文中添加一个未使用的变量绑定不影响不涉及该变量的项的类型检查。]

#证明[
  对 $m$ 作结构归纳。

  *$m = "var" c$，$c eq.not x$*：新上下文的 `env` 为 $(x, alpha) :: Gamma'."env"$；由 `LawfulBEq`，查找 $c$ 时跳过头部，回退到 $Gamma'."env"$，结果不变。

  *$m = lambda y . m'$*：归纳假设适用于 $m'$（若 $m' = "var" x$ 则 $"check"(Gamma', m') = "none"$，与前提矛盾）。查找 $y$ 时，因 $x eq.not y$（否则 $Gamma'(x) = "some"(dots)$，矛盾），结果同样不变。

  *$m = m_1 " " m_2$*：对 $m_1, m_2$ 分别应用归纳假设。
]

#引理([`LookupMap`])[列表查找与映射交换：若 $"lookup"(x, "xys") = "some"(y)$，则 $"lookup"(x, "xys"."map"(S)) = "some"(S(y))$。]

#引理([`SubstComp`])[$"applySubst"(f, "applySubst"(g, Gamma)) = "applySubst"(f compose g, Gamma)$。]

#定理([`CheckSubst`])[若 $"check"(Gamma, t) = "some"(tau)$ 且 $S$ 在箭头类型上满足分配律，则 $"check"("applySubst"(S, Gamma), t) = "some"(S(tau))$。]

#证明[
  对 $t$ 作结构归纳。

  *$t = "var" c$*：由 `LookupMap` 作用于假设 $Gamma(c) = tau$ 即得。

  *$t = lambda x . m$*：设 $"check"(Gamma, m) = "some"(tau_m)$，$Gamma(x) = "some"(tau')$。归纳假设给出 $"check"(S(Gamma), m) = "some"(S(tau_m))$；由 `LookupMap` 得 $S(Gamma)(x) = "some"(S(tau'))$。利用 $S$ 的分配律 $P_3$ 得 $"some"(S(tau') arrow.r S(tau_m)) = "some"(S(tau' arrow.r tau_m))$。

  *$t = m " " n$*：设 $"check"(Gamma, m) = "some"(a arrow.r b)$，$"check"(Gamma, n) = "some"(a)$。归纳假设给出 $"check"(S(Gamma), m) = "some"(S(a) arrow.r S(b))$（利用 $P_3$）和 $"check"(S(Gamma), n) = "some"(S(a))$。由 `LawfulBEq` 和 `beq_iff_eq` 得分支返回 $"some"(S(b)) = "some"(S(tau))$。
]

= 辅助定义与引理

本章的定义和引理为推导可靠性证明（第七章）提供关键支撑。

== 辅助定义

#定义([`distributes`])[
  $"distributes"(f) := forall a, b, quad f(a arrow.r b) = f(a) arrow.r f(b).$
  断言函数 $f$ 在箭头类型上满足分配律。`CheckSubst` 等引理需要此条件来在类型替换下推进 `check`。
]

#定义([`lookup_inv`])[
  $"lookup_inv"(f, Gamma, Gamma') := forall x, tau, quad Gamma(x) = "some"(tau) => Gamma'(x) = "some"(f(tau)).$
  $f$ 是从 $Gamma$ 到 $Gamma'$ 的*查找保持性*：若 $Gamma$ 将 $tau$ 赋给 $x$，则 $Gamma'$ 将 $f(tau)$ 赋给 $x$。
]

#定义([`check_inv`])[
  $"check_inv"(f, Gamma, Gamma') := forall t, tau, quad "check"(Gamma, t) = "some"(tau) => "check"(Gamma', t) = "some"(f(tau)).$
  $f$ 是从 $Gamma$ 到 $Gamma'$ 的*类型检查保持性*。
]

#定义([`equiv_lookup_on`, `equiv_check_on`])[
  $
    "equiv_lookup_on"(f, g, Gamma) &:= forall x, tau, quad Gamma(x) = "some"(tau) => g(tau) = f(tau). \
    "equiv_check_on"(f, g, Gamma) &:= forall t, tau, quad "check"(Gamma, t) = "some"(tau) => g(tau) = f(tau).
  $
  两个替换 $f, g$ 在 $Gamma$ 赋值（或 $Gamma$ 下可推导）的所有类型上相容。
]

#定义([`occursInTerm`])[
  谓词 $"occurs"(x, t)$ 表示变量 $x$ 在项 $t$ 中*语法出现*：
  $
    "occurs"(x, "var" y) &:= (x = y) \
    "occurs"(x, lambda y. m) &:= (x = y) or "occurs"(x, m) \
    "occurs"(x, m " " n) &:= "occurs"(x, m) or "occurs"(x, n).
  $
]

== 关键引理

#引理([`LookupThenIn`])[若 $"lookup"(x, l) = "some"(y)$，则 $(x, y) in l$。]

#引理([`SubstLookup`])[若 $Gamma(x) = "some"(tau)$，则 $("applySubst"(f, Gamma))(x) = "some"(f(tau))$。（`LookupMap` 的推论。）]

#引理([`FoldlInv`])[
  若 $f(a) = f(b)$，则对任意替换列表 $"es"$：
  $
    ("es"."foldl"(lambda "acc", "ex". "ex" compose "acc", f))(a) = ("es"."foldl"(lambda "acc", "ex". "ex" compose "acc", f))(b).
  $
  即在 $f$ 之后再左折叠更多替换，保持 $f(a) = f(b)$ 这一等式。证明对 $"es"$ 作列表归纳，每步利用下一个替换的函数性。
]

#引理([`CheckEqIfOccursInv`])[
  若 $forall x, "occurs"(x, t) => Gamma_1(x) = Gamma_2(x)$，则 $"check"(Gamma_1, t) = "check"(Gamma_2, t)$。

  类型检查仅依赖于在项中语法出现的变量的类型赋值。证明对 $t$ 作结构归纳，每步只需比较 $t$ 的子项中出现的变量。
]

#引理([`CheckSuccessLookupSome`])[若 $"check"(Gamma, t) = "some"(tau)$，则对 $t$ 中出现的每个变量 $x$，有 $exists tau', Gamma(x) = "some"(tau')$。类型检查成功蕴含所有出现的变量均在上下文中绑定。]

== `unifyCtx'` 与 `unifyCtx` 的可靠性

#引理([`UnifyCtxSound`])[
  若 $"unifyCtx'"(l) = "some"("exs")$，$(x, a, b) in l$，设 $F = "exs"."foldl"(lambda "acc", "ex". "ex" compose "acc", "id")$，则 $F(a) = F(b)$。

  `unifyCtx'` 的复合替换确实合一了输入列表中的每一对。证明对列表 $l$ 作归纳，利用 `UnifySound`（见第六章）和 `FoldlInv`。
]

#定理([`UnifyCtxMapCommon`])[
  若 $"unifyCtx"(Gamma_1, Gamma_2) = "some"(s)$，$Gamma_1(x) = "some"(tau_1)$，$Gamma_2(x) = "some"(tau_2)$，则 $s("apply")(tau_1) = s("apply")(tau_2)$。

  `unifyCtx` 的输出替换将两个上下文公共变量的类型赋值为相同的像。该定理是应用情形证明的关键：它联系了 `unifyCtx` 的操作行为与类型检查的语义要求。
]

== `pp'` 的性质

以下三个引理描述了 `pp'` 的输出上下文与输入上下文之间的关系。

#引理([`InferenceSubsetMap`])[
  若 $"pp'"(Gamma, m) = "some"(chevron.l Gamma', tau chevron.r)$，则存在替换 $f$ 使得
  $("applySubst"(f, Gamma))."env" subset.eq Gamma'."env"$。

  输出上下文包含（在某个替换 $f$ 的像下）输入上下文的所有绑定。证明对项作结构归纳，在每种情形下显式构造 $f$。
]

#引理([`InferenceLookupInv`])[
  若 $"pp'"(Gamma, m) = "some"(chevron.l Gamma', dots chevron.r)$，则存在替换 $f$ 使得：
  - $"lookup_inv"(f, Gamma, Gamma')$（查找保持性），
  - $"distributes"(f)$，
  - 对任何其他满足 $"lookup_inv"(g, Gamma, Gamma')$ 的 $g$，均有 $"equiv_lookup_on"(f, g, Gamma)$。

  此唯一性条件将推导的操作行为与语义可靠性联系起来：输入上下文在输出上下文中有一个典范的、唯一的（在 $Gamma$ 赋值的域上）替换像。
]

#引理([`InferenceCheckInv`])[
  若 $"pp'"(Gamma, m) = "some"(chevron.l Gamma', dots chevron.r)$，则存在替换 $f$ 使得：
  - $"check_inv"(f, Gamma, Gamma')$，
  - $"distributes"(f)$，
  - 对任何其他在 $Gamma$ 下可推导类型上满足 $"check_inv"(g, Gamma, Gamma')$ 的 $g$，均有 $"equiv_check_on"(f, g, Gamma)$。
]

= 合一的可靠性

#定理([`UnifySound`])[
  若 $"unify"(tau_1, tau_2) = "some"(S)$，则 $S(tau_1) = S(tau_2)$。
]

#证明[
  利用 Lean 4 的函数式归纳策略 `unify.induct` @lean4，对 `unify` 的每个分支生成一个证明目标。

  *$tau_1 = tau_2 = phi_p$*：$S = "id"$，显然。

  *$tau_1 = phi_p$，$tau_2 = phi_q$，$p eq.not q$*：$S = "replace"(p, phi_q)$。由 `replaceVar` 定义，$S(phi_p) = phi_q = S(phi_q)$。

  *$tau_1 = phi_p$，$tau_2 = tau$，$not "occ"(p, tau)$*：$S = "replace"(p, tau)$。$S(phi_p) = tau$；由辅助引理（对 $tau$ 归纳，利用 $not "occ"(p, tau)$）得 $S(tau) = tau$。

  *出现性检查失败或 `unify` 返回 `none`*：无 $S$ 须考虑。

  *$tau_1 = a arrow.r b$，$tau_2 = c arrow.r d$，$S = "comp"(S_1, S_2)$*：
  由归纳假设，$S_1(a) = S_1(c)$ 且 $S_2(S_1(b)) = S_2(S_1(d))$。利用 $S_1, S_2$ 的分配律 $P_3$：
  $
    S(a arrow.r b) = S_2(S_1(a) arrow.r S_1(b)) = S_2(S_1(a)) arrow.r S_2(S_1(b)) \
    S(c arrow.r d) = S_2(S_1(c) arrow.r S_1(d)) = S_2(S_1(c)) arrow.r S_2(S_1(d))
  $
  由上述两个归纳假设可知两侧相等。

  *对称情形 $tau_1 = tau$，$tau_2 = phi_p$*：`replacer` 与 `replace` 使用相同的底层函数，论证对称。
]

= 推导的可靠性

#引理([`InferenceSound'`])[
  若 $"pp'"(Gamma, t) = "some"(p)$，则 $"check"(p."ctx", t) = "some"(p."ty")$。
]

*变量情形与抽象情形*。

- *$t = "var" c$，$Gamma(c) = "some"(tau)$*：`pp'` 返回 $(Gamma, tau)$。`check(Γ, var c) = Γ(c) = some τ`。
- *$t = "var" c$，$Gamma(c) = "none"$*：设 $(alpha, Gamma') = "next"(Gamma)$。`pp'` 返回 $(Gamma' + (c: alpha), alpha)$。查找 $c$ 在 $((c, alpha) :: "env")$ 中立即成功。
- *$t = lambda x . m$，$Gamma'(x) = "some"(tau')$*：归纳假设给出 `check(Γ', m) = some τ`；`pp'` 返回 $(Gamma', tau' arrow.r tau)$，`check` 直接返回 `some (τ' → τ)`。
- *$t = lambda x . m$，$Gamma'(x) = "none"$*：`pp'` 分配 $alpha = "next"(Gamma')$，返回 $(Gamma'' + (x: alpha), alpha arrow.r tau)$。归纳假设加 `CheckInvUnderAdd`（唯一性条件 $m eq.not "var" x$ 由"若 $m = "var" x$ 则 `check(Γ', var x) = none`，与归纳假设矛盾"推得）将结论提升至扩展上下文。

*应用情形*。

#证明([应用情形])[

  设 $t = m " " n$，算法输出：$(Gamma_m, tau_1) = "pp'"(Gamma, m)$；$(Gamma_n, tau_2) = "pp'"(Gamma_m, n)$；$alpha = "next"(Gamma_n)."fst"$；$S_1 = "unify"(tau_1, tau_2 arrow.r alpha)$；$S_2 = "unifyCtx"(S_1(Gamma_m), S_1(Gamma_n))$；$p."ctx" = S_2(S_1(Gamma_n))$，$p."ty" = S_2(S_1(alpha))$。

  对 $"check"(p."ctx", m)$ 和 $"check"(p."ctx", n)$ 分情形。成功分支需证 `check p.ctx (app m n) = some p.ty`，论证分为以下关键环节：

  *环节一（上下文一致性）*：对 $m$ 中出现的每个变量 $x$，用 `InferenceLookupInv`（对 $m$）取得典范替换 $g$ 使得 $"lookup_inv"(g, Gamma_m, Gamma_n)$，再由 `UnifyCtxMapCommon` 得 $S_2$ 等同 $S_1(Gamma_m)(x)$ 与 $S_1(Gamma_n)(x)$ 在 $S_2$ 作用下的像；从而 $p."ctx"(x) = (S_2 compose S_1)(Gamma_m)(x)$。由 `CheckEqIfOccursInv`，`check(p.ctx, m) = check(applySubst (S₂∘S₁) Γₘ, m)`。

  *环节二（归纳假设在替换上下文中的应用）*：由对 $m$ 的归纳假设和 `CheckSubst`，$"check"("applySubst"(S_2 compose S_1, Gamma_m), m) = "some"((S_2 compose S_1)(tau_1))$。

  *环节三（箭头类型）*：由 `UnifySound`，$S_1(tau_1) = S_1(tau_2 arrow.r alpha) = S_1(tau_2) arrow.r S_1(alpha)$。再由 $S_2$ 的分配律，$(S_2 compose S_1)(tau_1) = (S_2 compose S_1)(tau_2) arrow.r (S_2 compose S_1)(alpha) = (S_2 compose S_1)(tau_2) arrow.r p."ty"$。

  *环节四（参数类型匹配）*：对 $n$ 类似地由环节一的对称版本和对 $n$ 的归纳假设加 `CheckSubst` 得 `check(p.ctx, n) = some ((S₂∘S₁)(τ₂))`。箭头类型的定义域与参数类型吻合，`check(p.ctx, app m n)` 返回 `some p.ty`。

  `check` 返回 `none` 的各分支通过 `InferenceLookupInv` + `CheckEqIfOccursInv` 的反证法处理。
]

#定理([`InferenceSound`])[
  若 $"pp"(t) = "some"(p)$，则 $"check"(p."ctx", t) = "some"(p."ty")$。
]

#证明[
  $"pp"(t) = "pp'"(Gamma_emptyset, t)$。直接应用 `InferenceSound'`。在 `NextFresh` 假设下。
]

#推论[
  若 $"pp"(t) = "some"(p)$，则 $p."ctx" tack.r t : p."ty"$（按定义 2.5 的类型赋值规则）。
]

= 遗留问题

#注记([`NextFresh`])[
  上述证明用到了以下假设：`next ctx` 始终产生一个相对于 `ctx` 的新变量 $alpha$——对 `ctx` 中任何现有变量 $x eq.not alpha$，向上下文中添加绑定 $(alpha, tau)$ 不影响对 $x$ 的查找：
  $
    "ctx"(x) = "some"(tau) arrow.l.r ("add"(y, "next"("ctx")."fst", "next"("ctx")."snd"))(x) = "some"(tau).
  $

  从实现来看，`next` 将 `label` 字符的序数加一，`add` 在环境前端插入新绑定，唯一性在直觉上显然成立。然而，严格的形式化证明需要对 `Char.ofNat (ctx.label.toNat + 1)` 进行单射性论证——本质上涉及 `Nat → Char` 的有界单射性，包含字符编码的细节。该性质目前以 `sorry` 接受为公理。考虑到一般性实现的自由性，不妨将该定理理解为任何`next`实现的性质要求。即，只要实现中的`next`满足此性质，即可通过本文描述的形式化方法证明其正确性。
]

= 结论

本文给出了简单柯里类型λ式主类型推导算法的完整 Lean 4 形式化证明，包括：

+ STLC 语法、类型赋值规则与类型检查函数 `check`；
+ 带终止性证明的罗宾逊合一算法，利用依赖类型结构将终止性度量内嵌于 `Subst` 类型；
+ 推导算法 `pp'` 关键结构性质的一套引理；
+ 完整的可靠性定理 `InferenceSound`，包括此前遗留的应用情形。

唯一的公理假设是 `NextFresh`（见第八章），其余所有结论均经过 Lean 4 机器检验。

未来工作方向包括：消除 `NextFresh` 公理（改用 `Nat` 索引的类型变量）；将框架推广至带名字和递归的 $lambda$-演算（LCNR）或米尔纳的 ML 类型系统。

= AI 辅助声明

本文形式化的开发借助了语言大模型DeepSeek @deepseek 的辅助。 所有 AI 生成的证明草稿均经过仔细审查、修正与简化。

#pagebreak()
#bibliography("refs.bib")
