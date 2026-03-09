#import "@preview/modern-cug-report:0.1.3": *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set heading(numbering: "1.1")

#show: doc => template(doc, footer: "简单类型λ演算的主类型推导")
#show: thmrules

#set text(font: "Source Han Serif", lang: "zh")
#show raw: set text(
  font: "Fira Code Retina",
  size: 0.85em,
)

#set math.cases(delim: math.brace.stroked)

#let 定义 = thmbox("definition", "定义", inset: 0em)
#let 定理 = thmbox("theorem", "定理", fill: rgb("eeffee"))
#let 引理 = thmbox("theorem", "引理", fill: rgb("eeffee"))
#let 推论 = thmbox("corollary", "推论", fill: rgb("eeffee"))
#let 注记 = thmbox("theorem", "注记", inset: 0em)
#let 证明 = thmproof("proof", [*证*])

#let rpl(a, s, t) = $#t [#a := #s]$

= 引言

简单类型λ演算（Simply Typed Lambda Calculus，STLC）由阿隆佐·丘奇 @church1940 引入，经哈斯凯尔·柯里 @curry1934 代数化研究，是有类型函数式编程的理论基础。其核心算法是*主类型推导*：给定项 $t$，计算最一般的类型判断 $Gamma tack.r t : tau$，使得所有其他类型判断都是它的特例。罗杰·欣德利 @hindley1969 证明了 STLC 的主类型始终存在；罗宾·米尔纳 @milner1978 与达马斯-米尔纳 @damas1982 将该结论推广至多态 $lambda$-演算。

罗宾逊合一算法 @robinson1965 是大多数类型推导过程的计算核心。其终止性证明需要用到自由类型变量集合的势作为良基的度量，同时还需要一个压缩引理。

本文面向熟悉Lean基础、对类型论有一定了解的本科生，希望能对读者有所裨益。

*本文内容一览*：

+ STLC 定义及类型检查器；
+ 主类型推导算法的 Lean 4 实现；
+ 利用 Lean 依赖类型系统对罗宾逊合一算法终止性的证明；
+ 类型推导算法的正确性证明。

本文分发协议为#link("https://creativecommons.org/licenses/by-sa/4.0/")[*CC BY-SA*]，代码开源协议为#link("https://jxself.org/translations/gpl-3.zh.shtml")[*GPL V3*]。

#pagebreak()

= 导读

== 什么是λ演算？

λ演算是由阿隆佐·丘奇在20世纪30年代提出的形式系统，用于研究函数定义、函数应用和递归。它构成了函数式编程语言的理论基础。最基本的λ项由变量、抽象（函数定义）和应用（函数调用）组成：

```
t ::= x | λx.t | t t
```

例如，恒等函数写作 `λx.x`，它接受一个参数`x`并直接返回`x`。

== 为什么要引入类型？

无类型λ演算虽然表达能力强，但允许一些“病态”的项，例如 `(λx.x x)(λx.x x)`，它会导致无限循环（Ω组合子）。为了排除这类无意义的程序，人们引入了类型系统。简单类型λ演算（Simply Typed Lambda Calculus, STLC）是最基础的类型系统，它为每个项赋予一个类型，类型由基本类型和函数类型构成：

```
τ ::= α | τ → τ
```

类型规则确保函数应用时参数类型匹配。例如，恒等函数 `λx.x` 的类型可以是 `α → α`，其中 `α` 是一个类型变量，表示“任意类型”。

== 什么是主类型推导？

给定一个项，我们可能想知道它是否能被赋予一个类型，如果能，最一般的类型是什么？这就是*主类型推导*问题。主类型（principal type）是指：项的所有可能类型都是该类型的某个替换实例。例如，恒等函数的主类型是 `α → α`，任何其他类型如 `(β → β) → (β → β)` 都可以通过将 `α` 替换为 `β → β` 得到。

主类型推导算法通常分为两步：
1. 为项生成一组类型约束（例如，应用时要求左项类型为函数，且右项类型与函数参数一致）。
2. 通过合一算法求解这些约束，得到最一般的替换。

== 一个简单的例子

考虑项 `λf.λx.f x`（即函数应用组合子）。我们手动推导其主类型：

- 假设 `f` 的类型为 `α`，`x` 的类型为 `β`。
- 应用 `f x` 要求 `f` 是函数类型，设 `α = γ → δ`，且 `x` 的类型 `β` 必须等于 `γ`。
- 于是 `f x` 的类型为 `δ`。
- 抽象 `x`：`λx.f x` 的类型为 `β → δ`，但已知 `β = γ`，所以为 `γ → δ`。
- 再抽象 `f`：`λf.λx.f x` 的类型为 `(γ → δ) → γ → δ`。

用类型变量替换 `γ, δ` 为任意类型，得到最一般的类型 `(α → β) → α → β`。这就是该组合子的主类型。

== 本文的价值

虽然STLC的主类型推导早已被形式化验证@MLCoq（例如在Coq中），但本文使用*Lean 4*——一个年轻但强大的定理证明器——重新实现了整个算法并证明了其正确性。

通过阅读本文，读者将能够：
- 理解STLC的语法、类型规则和类型检查器；
- 掌握罗宾逊合一算法的实现及其终止性证明；
- 见证主类型推导算法的完整正确性证明。

尽管Coq等工具早已有类似工作，但Lean 4的现代设计、简洁的语法和强大的社区支持，使得这一经典结果以新的形式呈现，为类型理论和定理证明的学习者提供了宝贵的资源。

#pagebreak()

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
    frac(Gamma tack.r m : tau_1 arrow.r tau_2 quad Gamma tack.r n : tau_1, Gamma tack.r m" "n : tau_2)
  $
] <type_assignment>

== 类型替换

#定义[
  *分配律*：令$S : "CurryType" -> "CurryType"$，若$S(tau arrow.r sigma) = S(tau) arrow.r S(sigma)$，则称$S$满足分配律。
]

#定义[
  *类型替换*是满足分配律的函数 $S : "CurryType" -> "CurryType"$。定义对上下文的逐点应用： $S(Gamma) = brace.l.stroked (x, S(tau)) | (x, tau) in Gamma brace.r.stroked$，在代码中通过 `applySubst` 实现。
]

#定义[
  对类型变量 $alpha$ 和类型 $sigma$，*替换* $rpl(alpha, sigma, tau)$ 将 $tau$ 中 $alpha$ 的所有自由出现替换为 $sigma$：
  $
    rpl(alpha, sigma, phi_alpha) &= sigma \
    rpl(alpha, sigma, phi_beta) &= phi_beta quad (beta eq.not alpha) \
    rpl(alpha, sigma, tau arrow.r tau') &= rpl(alpha, sigma, tau) arrow.r rpl(alpha, sigma, tau')
  $
]

= 实现

== `check` 函数 <sec-check>

*类型检查函数* `check` 验证项是否符合类型赋值规则。它要求上下文已包含项中所有自由变量的类型绑定，`check`的作用是描述何为正确的类型推导结果。

#定义[
  $
    "check"(Gamma, x) &= Gamma(x) \
    "check"(Gamma, lambda x . m) &=
    cases(
      "none" quad & "if" "check"(Gamma, m) = "none" "or" Gamma(x) = "none",
      "some"(tau' arrow.r tau) quad & "if" "check"(Gamma, m) = "some"(tau) "and" Gamma(x) = "some"(tau'),
    ) \
    "check"(Gamma, m" "n) &=
    cases(
      "some"(b) quad & "if" "check"(Gamma, m) = "some"(a arrow.r b) "and" "check"(Gamma, n) = "some"(a),
      "none" quad & "otherwise"
    )
  $

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

  容易观察到实现与 @type_assignment 一一对应。
]

== `Subst` 类型

`Subst left right` 是一个依赖类型结构，将替换函数 `apply` 与三个性质打包在一起。这三个性质是终止性证明的关键：

$
  P_1 &: forall tau. "vars"("apply"(tau)) subset.eq "vars"("left") union "vars"("right") union "vars"(tau) \
  P_2 &: forall tau. lr(|"vars"("apply"(tau))|) = lr(|"vars"("left") union "vars"("right") union "vars"(tau)|) arrow.r.double "apply" = "id" \
  P_3 &: forall a, b. "apply"(a arrow.r b) = "apply"(a) arrow.r "apply"(b)
$

$P_1$ 限制了像的变量域；$P_2$ 声称：若像的变量集合势与原集合相等，则该替换必为恒等替换（这是终止性的关键约束）；$P_3$ 是分配律。`Subst` 有四种构造子：`id`（恒等）、`replace`/`replacer`（单变量替换）、`comp`（复合）。

#beamer-block([
  何为依赖类型？

  注意到`Subst left right`中的`left`不是一个类型，而是一个值。这意味着`Subst`的类型_依赖_具体值，这被称为依赖类型。
])

== 合一算法 <sec-unify>

#定义[
  合一算法（`unify`）接受两个类型并返回一个可选的合一替换：

  $
    &"unify"(phi_p, phi_p) = "some"("id") \
    &"unify"(phi_p, phi_q) = "some"("replace"(p, phi_q)) quad "if" p eq.not q \
    &"unify"(phi_p, tau) = "some"("replace"(p, tau)) "if" not "occ"(p, tau) \
    &"unify"(phi_p, tau) = "none" "if" "occ"(p, tau) \
    &"unify"(tau, phi_p) = "some"("replacer"(p, tau)) "if" not "occ"(p, tau) \
    &"unify"(tau arrow.r tau', sigma arrow.r sigma') =\
    &cases(
      "none" quad &"if" "unify"(tau, sigma) = "none",
      "none" quad &"if" "unify"(tau, sigma) = "some"(S_1) "and" "unify"(S_1(tau'), S_1(sigma')) = "none",
      "some"("comp"(S_1, S_2)) quad &"otherwise"
    )
  $
]

=== 合一算法的终止性

#beamer-block([
  如何证明某递归算法终止？

  一般来说，需要为输入定义一个度量，证明每次递归输入都会变小，最终达到基础情况。例如：阶乘每次会将输入减一，列表映射每次会将输入列表长度减一，等等。
])

*如何证明合一算法的终止性？*
合一算法（`unify`）的终止性并不直观，因为它的递归调用可能作用于经过替换后的类型，而不再是原始项的子结构。例如，在箭头情形中，我们需要先合一参数类型得到替换 $S_1$，然后用$S_1$ 作用于返回类型再合一。第二次调用的参数可能比原始输入更大（在变量数量上），这使得简单的“结构大小”度量失效。

==== 度量的选择
我们采用字典序度量
$
  mu(tau_1, tau_2) = "vars"(tau_1) union "vars"(tau_2)|, "size"(tau_1) + "size"(tau_2))
$
其中第一分量是自由类型变量集合的势，第二分量是类型的结构大小（即语法树的节点数）。字典序保证：若第一分量严格减小，则整体度量减小；若第一分量不变，则依赖第二分量减小。

==== 终止性论证的要点
- *第一次调用* `unify(τ, σ)`：参数是原始类型的子项，结构大小严格减小，因此度量第二分量减小。无论第一分量如何，字典序整体下降。
- *第二次调用* `unify(S₁(τ'), S₁(σ'))`：由 P₁ 可知，变量集合不会扩大；即$|"vars"(S₁(τ')) union "vars"(S₁(σ'))| < |"vars"(tau') union "vars"(sigma') union "vars"("left") union "vars"("right")|$)，而后者正是第一次调用前变量集合的势。因此第一分量*不增*。
  - 若第一分量严格减小，则度量下降。
  - 若第一分量不变，则由 P₂ 推出$S_1 = "id"$)。此时第二次调用的参数简化为原始的$τ'$,$σ'$)，它们是原始箭头类型的子项，结构大小严格减小，因此第二分量下降，度量下降。
==== 在 Lean 中的实现
`Subst` 的每个构造子（如 `id`、`replace`、`comp`）都携带证明，确保它们满足上述三条性质。这样，当我们从 `unify` 返回一个替换时，它的类型本身就“记住”了这些性质，后续证明可以直接调用。例如，在第二次递归调用前，我们利用$P_1$ 和$P_2$ 分析$S_1$)，从而获得度量的递减保证。
这种将性质内嵌于类型的方式，使得终止性证明变得模块化且易于机器检查，也体现了依赖类型在形式化验证中的强大能力。

== 上下文合一
上下文合一将两个类型上下文中共有变量的类型两两合一。首先有递归辅助函数：
#定义[
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
        -- 因为后续合一必须在前一个替换的基础上进行，否则可能引入不一致。
        let rest' := rest.map (fun (y, ty1, ty2) =>
                       (y, s1.apply ty1, s1.apply ty2))
        match unifyCtx' rest' with
        | none       => none
        | some substs => some (ExSubst.from s1 :: substs)
  ```

  其中 `ExSubst` 是对 `Subst` 的类型擦除包装，使得不同索引类型的替换可存入同质列表。

]

`unifyCtx` 基于 `unifyCtx'` 构建：收集所有共有变量三元组$(x, Gamma_1(x), Gamma_2(x))$，调用 `unifyCtx'`，然后用 `foldl` 从左到右复合所有替换：

```lean
def unifyCtx (ctx1 ctx2 : TypeCtx) : Option (CtxSubst ctx1 ctx2) :=
  let commonVars := ctx1.env.filterMap (fun (x, a) =>
    (ctx2.env.lookup x).map (fun b => (x, a, b)))
  match unifyCtx' commonVars with
  | none => none
  | some exList =>
    let apply t := exList.foldl (fun acc ex => ex.cast acc) t
    some (CtxSubst.from commonVars apply ⋯  ctx1 ctx2)
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
  $ "pp'"(Gamma, m" "n) = "some"(S_2(S_1(Gamma_3)), S_2(S_1(alpha))) $
]
顶层函数$"pp"(t) := "pp'"(Gamma_emptyset, t)$。

= 结构性引理
本章收录支撑最终结果（主类型推导算法的正确性）的基础引理。

== 自由变量相关引理
#引理([类型的大小为正])[$forall tau, "sz"(tau) > 0$。]<size_gtz>
#引理([自由变量的包含性])[$forall tau, tau', "vars"(tau) subset.eq "vars"(tau arrow.r tau')$。]<vars_arrow>
#引理([替换后的自由变量范围])[若 $not "occ"(alpha, sigma)$，则 $forall tau, "vars"(rpl(alpha, sigma, tau)) subset.eq brace.l.stroked alpha brace.r.stroked union "vars"(sigma) union "vars"(tau)$。证明对 $tau$ 作结构归纳。] <replace_var_scope>
#引理([非自由变量出现于自由变量集])[$c in "vars"(tau) arrow.r.double "occursIn"(c, tau) = "true"$。]<occ_iff_in_vars>
#引理([替换的完全性])[若 $not "occ"(alpha, sigma)$，则 $forall tau, alpha in.not "vars"(rpl(alpha, sigma, tau))$。自由变量检查确保 $alpha$ 不会通过 $sigma$ 被重新引入。]<replace_elim>
#引理([替换必然引入新类型变量])[若 $not "occ"(alpha, sigma)$，则 $forall tau, lr(|"vars"(rpl(alpha, sigma, tau))|) eq.not lr(|brace.l.stroked alpha brace.r.stroked union "vars"(sigma) union "vars"(tau)|)$。]<replace_add_new_vars>
#证明[
  设 $L = "vars"(rpl(alpha, sigma, tau))$，$R = brace.l.stroked alpha brace.r.stroked union "vars"(sigma) union "vars"(tau)$。假设 $|L| = |R|$。由 @replace_var_scope 得 $L subset.eq R$；由 @replace_elim 得 $alpha in.not L$；而 $alpha in R$，故 $L subset.neq R$。那么，$|R| lt.eq |L|$ 与 $L subset.eq R$ 合并推得 $L = R$，矛盾。
]

== 上下文操作的基本性质
#引理([新变量的唯一性])[
  对 `ctx` 中任何现有变量 $x eq.not alpha$，向上下文中添加绑定 $(alpha, tau)$ 不影响对 $x$ 的查找：
  $
    "ctx"(x) = "some"(tau) arrow.l.r ("add"(y, "next"("ctx")."fst", "next"("ctx")."snd"))(x) = "some"(tau).
  $

  `next ctx` 始终产生一个相对于 `ctx` 的新变量 $alpha$
] <next_fresh>

== 类型检查的结构性质
#引理([检查不关心计数器])[`check` 只依赖上下文的 `env` 字段，与 `label` 无关：若 $Gamma."env" = Gamma'."env"$，则 $"check"(Gamma, t) = "check"(Gamma', t)$。<check_inv_under_label>]
#引理([添加新变量不影响检查])[若 $Gamma'(x) = "none"$，$"ctx" = Gamma' + (x : alpha)$，$m eq.not "var" x$，且 $"check"(Gamma', m) = "some"(pi)$，则 $"check"("ctx", m) = "some"(pi)$。<check_inv_under_add>]
#证明[
  对 $m$ 作结构归纳。

  *$m = "var" c$，$c eq.not x$*：新上下文的 `env` 为 $(x, alpha) :: Gamma'."env"$；由 `LawfulBEq`，查找 $c$ 时跳过头部，回退到 $Gamma'."env"$，结果不变。

  *$m = lambda y . m'$*：归纳假设适用于 $m'$（若 $m' = "var" x$ 则 $"check"(Gamma', m') = "none"$，与前提矛盾）。查找 $y$ 时，因 $x eq.not y$（否则 $Gamma'(x) = "some"(dots)$，矛盾），结果同样不变。

  *$m = m_1" "m_2$*：对 $m_1, m_2$ 分别应用归纳假设。
]
#引理([列表查找与映射交换])[若 $"lookup"(x, "xys") = "some"(y)$，则 $"lookup"(x, "xys"."map"(S)) = "some"(S(y))$。] <lookup_map>
#引理([替换的点应用可组合])[$"applySubst"(f, "applySubst"(g, Gamma)) = "applySubst"(f compose g, Gamma)$。] <subst_comp>
#定理([替换保持检查结果])[若 $"check"(Gamma, t) = "some"(tau)$ 且 $S$ 在箭头类型上满足分配律，则 $"check"("applySubst"(S, Gamma), t) = "some"(S(tau))$。] <check_subst>
#证明[
  对 $t$ 作结构归纳。

  *$t = "var" c$*：由@lookup_map 作用于假设 $Gamma(c) = tau$ 即得。

  *$t = lambda x . m$*：设 $"check"(Gamma, m) = "some"(tau_m)$，$Gamma(x) = "some"(tau')$。归纳假设给出 $"check"(S(Gamma), m) = "some"(S(tau_m))$；由 @lookup_map 得 $S(Gamma)(x) = "some"(S(tau'))$。利用 $S$ 的分配律 $P_3$ 得 $"some"(S(tau') arrow.r S(tau_m)) = "some"(S(tau' arrow.r tau_m))$。

  *$t = m" "n$*：设 $"check"(Gamma, m) = "some"(a arrow.r b)$，$"check"(Gamma, n) = "some"(a)$。归纳假设给出 $"check"(S(Gamma), m) = "some"(S(a) arrow.r S(b))$（利用 $P_3$）和 $"check"(S(Gamma), n) = "some"(S(a))$。由 `LawfulBEq` 和 `beq_iff_eq` 得分支返回 $"some"(S(b)) = "some"(S(tau))$。
]

== 辅助定义
#定义[
  $"distributes"(f) := forall a, b, quad f(a arrow.r b) = f(a) arrow.r f(b).$
  表示函数 $f$ 在箭头类型上满足分配律。@check_subst 等需要此条件来在类型替换下推进 `check`。
]
#定义[
  $"lookup_inv"(f, Gamma, Gamma') := forall x, tau, quad Gamma(x) = "some"(tau) => Gamma'(x) = "some"(f(tau)).$
  $f$ 是从 $Gamma$ 到 $Gamma'$ 的*查找保持性*：若 $Gamma$ 将 $tau$ 赋给 $x$，则 $Gamma'$ 将 $f(tau)$ 赋给 $x$。
]
#定义[
  $"check_inv"(f, Gamma, Gamma') := forall t, tau, quad "check"(Gamma, t) = "some"(tau) => "check"(Gamma', t) = "some"(f(tau)).$
  $f$ 是从 $Gamma$ 到 $Gamma'$ 的*类型检查保持性*。
]
#定义[
  $
    "equiv_lookup_on"(f, g, Gamma) &:= forall x, tau, quad Gamma(x) = "some"(tau) => g(tau) = f(tau). \
    "equiv_check_on"(f, g, Gamma) &:= forall t, tau, quad "check"(Gamma, t) = "some"(tau) => g(tau) = f(tau).
  $
  两个替换 $f, g$ 在 $Gamma$ 赋值（或 $Gamma$ 下可推导）的所有类型上相容。
]
#定义[
  谓词 $"occurs"(x, t)$ 表示变量 $x$ 在项 $t$ 中出现：
  $
    "occurs"(x, "var" y) &:= (x = y) \
    "occurs"(x, lambda y. m) &:= (x = y) or "occurs"(x, m) \
    "occurs"(x, m" "n) &:= "occurs"(x, m) or "occurs"(x, n).
  $
]

== 通用引理
#引理([替换后上下文查找])[若 $Gamma(x) = "some"(tau)$，则 $("applySubst"(f, Gamma))(x) = "some"(f(tau))$。（@lookup_map 的推论。） <SubstLookup>]
#引理([左折叠保持相等])[
  若 $f(a) = f(b)$，则对任意替换列表 $"es"$：
  $
    ("es"."foldl"(lambda "acc", "ex". "ex" compose "acc", f))(a) = ("es"."foldl"(lambda "acc", "ex". "ex" compose "acc", f))(b).
  $
  即$=$可以穿透$("es"."foldl"(lambda "acc", "ex". "ex" compose "acc", f))$。通过`congrArg`易证。]<FoldlInv>
#引理([类型检查依赖于出现变量])[
  若 $forall x, "occurs"(x, t) => Gamma_1(x) = Gamma_2(x)$，则 $"check"(Gamma_1, t) = "check"(Gamma_2, t)$。

  类型检查仅依赖于在项中语法出现的变量的类型赋值。证明对 $t$ 作结构归纳，每步只需比较 $t$ 的子项中出现的变量。]<CheckEqIfOccursInv>
#引理([检查成功则变量绑定])[若 $"check"(Gamma, t) = "some"(tau)$，则对 $t$ 中出现的每个变量 $x$，有 $exists tau', Gamma(x) = "some"(tau')$。类型检查成功蕴含所有出现的变量均在上下文中绑定。]<CheckSuccessLookupSome>

== 上下文合一正确性
#引理([上下文合一正确性])[
  若 $"unifyCtx'"(l) = "some"("exs")$，$(x, a, b) in l$，设 $F = "exs"."foldl"(lambda "acc", "ex". "ex" compose "acc", "id")$，则 $F(a) = F(b)$。

  `unifyCtx'` 的复合替换确实合一了输入列表中的每一对。证明对列表 $l$ 作归纳，利用 @unify_sound 和 @FoldlInv。]<UnifyCtxSound>
#定理([公共变量类型一致])[
  若 $"unifyCtx"(Gamma_1, Gamma_2) = "some"(s)$，$Gamma_1(x) = "some"(tau_1)$，$Gamma_2(x) = "some"(tau_2)$，则 $s("apply")(tau_1) = s("apply")(tau_2)$。

  `unifyCtx` 的输出替换将两个上下文公共变量的类型赋值为相同的像。该定理是应用情形证明的关键：它联系了 `unifyCtx` 的操作行为与类型检查的语义要求。]<UnifyCtxMapCommon>

== `pp'` 的性质
以下三个引理描述了 `pp'` 的输出上下文与输入上下文之间的关系。
#引理([输出上下文包含输入像])[
  若 $"pp'"(Gamma, m) = "some"(chevron.l Gamma', tau chevron.r)$，则存在替换 $f$ 使得
  $("applySubst"(f, Gamma))."env" subset.eq Gamma'."env"$。

  输出上下文包含（在某个替换 $f$ 的像下）输入上下文的所有绑定。证明对项作结构归纳，在每种情形下显式构造 $f$。]<InferenceSubsetMap>

#引理([推理查找保持唯一性])[
  若 $"pp'"(Gamma, m) = "some"(chevron.l Gamma', dots chevron.r)$，则存在替换 $f$ 使得：
  - $"lookup_inv"(f, Gamma, Gamma')$（查找保持性），
  - $"distributes"(f)$，
  - 对任何其他满足 $"lookup_inv"(g, Gamma, Gamma')$ 的 $g$，均有 $"equiv_lookup_on"(f, g, Gamma)$。

  此唯一性条件将推导的操作行为与语义正确性联系起来：输入上下文在输出上下文中有一个典范的、唯一的（在 $Gamma$ 赋值的域上）替换像。
]<InferenceLookupInv>
#引理([推理类型检查保持唯一性])[
  若 $"pp'"(Gamma, m) = "some"(chevron.l Gamma', dots chevron.r)$，则存在替换 $f$ 使得：
  - $"check_inv"(f, Gamma, Gamma')$，
  - $"distributes"(f)$，
  - 对任何其他在 $Gamma$ 下可推导类型上满足 $"check_inv"(g, Gamma, Gamma')$ 的 $g$，均有 $"equiv_check_on"(f, g, Gamma)$
]<InferenceCheckInv>
= 合一的可靠性
#定理([合一算法的正确性])[
  若 $"unify"(tau_1, tau_2) = "some"(S)$，则 $S(tau_1) = S(tau_2)$。
] <unify_sound>
#证明[
  利用 Lean 4 的函数式归纳策略 `unify.induct` @lean4，对 `unify` 的每个分支生成一个证明目标。

  *$tau_1 = tau_2 = phi_p$*：$S = "id"$，显然。

  *$tau_1 = phi_p$，$tau_2 = phi_q$，$p eq.not q$*：$S = "replace"(p, phi_q)$。由 `replaceVar` 定义，$S(phi_p) = phi_q = S(phi_q)$。

  *$tau_1 = phi_p$，$tau_2 = tau$，$not "occ"(p, tau)$*：$S = "replace"(p, tau)$。$S(phi_p) = tau$；由辅助引理（对 $tau$ 归纳，利用 $not "occ"(p, tau)$）得 $S(tau) = tau$。

  *自由变量检查失败或 `unify` 返回 `none`*：无 $S$ 须考虑。

  *$tau_1 = a arrow.r b$，$tau_2 = c arrow.r d$，$S = "comp"(S_1, S_2)$*：
  由归纳假设，$S_1(a) = S_1(c)$ 且 $S_2(S_1(b)) = S_2(S_1(d))$。利用 $S_1, S_2$ 的分配律 $P_3$：
  $
    S(a arrow.r b) = S_2(S_1(a) arrow.r S_1(b)) = S_2(S_1(a)) arrow.r S_2(S_1(b)) \
    S(c arrow.r d) = S_2(S_1(c) arrow.r S_1(d)) = S_2(S_1(c)) arrow.r S_2(S_1(d))
  $
  由上述两个归纳假设可知两侧相等。

  *对称情形 $tau_1 = tau$，$tau_2 = phi_p$*：`replacer` 与 `replace` 使用相同的底层函数，论证对称。
]

= 推导的正确性
#引理([主类型推导算法的正确性])[
  若 $"pp'"(Gamma, t) = "some"(p)$，则 $"check"(p."ctx", t) = "some"(p."ty")$。
] <inference_sound>
#证明[

  *变量情形与抽象情形*。
  - *$t = "var" c$，$Gamma(c) = "some"(tau)$*：`pp'` 返回$(Gamma, tau)$。`check(Γ, var c) = Γ(c) = some τ`。
  - *$t = "var" c$，$Gamma(c) = "none"$*：设$(alpha, Gamma') = "next"(Gamma)$。`pp'` 返回$(Gamma' + (c: alpha), alpha)$。查找$c$ 在 $((c, alpha) :: "env")$中立即成功。
  - *$t = lambda x . m$，$Gamma'(x) = "some"(tau')$*：归纳假设给出 `check(Γ', m) = some τ`；`pp'` 返回$(Gamma', tau' arrow.r tau)$，`check` 直接返回 `some (τ' → τ)`。
  - *$t = lambda x . m$，$Gamma'(x) = "none"$*：`pp'` 分配$alpha = "next"(Gamma')$，返回$(Gamma'' + (x: alpha), alpha arrow.r tau)$。归纳假设加 `CheckInvUnderAdd`（唯一性条件$m eq.not "var" x$由"若 $m = "var" x$ 则 `check(Γ', var x) = none`，与归纳假设矛盾"推得）将结论提升至扩展上下文。

  *应用情形*。
  设 $t = m" "n$，算法输出：$(Gamma_m, tau_1) = "pp'"(Gamma, m)$；$(Gamma_n, tau_2) = "pp'"(Gamma_m, n)$；$alpha = "next"(Gamma_n)."fst"$；$S_1 = "unify"(tau_1, tau_2 arrow.r alpha)$；$S_2 = "unifyCtx"(S_1(Gamma_m), S_1(Gamma_n))$；$p."ctx" = S_2(S_1(Gamma_n))$，$p."ty" = S_2(S_1(alpha))$。

  对 $"check"(p."ctx", m)$ 和 $"check"(p."ctx", n)$ 分情形。成功分支需证 `check p.ctx (app m n) = some p.ty`，论证分为以下关键环节：

  *环节一（上下文一致性）*：对 $m$ 中出现的每个变量 $x$，用@InferenceLookupInv（对 $m$）取得替换 $g$ 使得 $"lookup_inv"(g, Gamma_m, Gamma_n)$，再由 @UnifyCtxMapCommon 得 $S_2$ 等同 $S_1(Gamma_m)(x)$ 与 $S_1(Gamma_n)(x)$ 在 $S_2$ 作用下的像；从而 $p."ctx"(x) = (S_2 compose S_1)(Gamma_m)(x)$。由 @CheckEqIfOccursInv，`check(p.ctx, m) = check(applySubst (S₂∘S₁) Γₘ, m)`。

  *环节二（归纳假设在替换上下文中的应用）*：由对 $m$ 的归纳假设和@check_subst，$"check"("applySubst"(S_2 compose S_1, Gamma_m), m) = "some"((S_2 compose S_1)(tau_1))$。

  *环节三（箭头类型）*：由 @unify_sound，$S_1(tau_1) = S_1(tau_2 arrow.r alpha) = S_1(tau_2) arrow.r S_1(alpha)$。再由 $S_2$ 的分配律，$(S_2 compose S_1)(tau_1) = (S_2 compose S_1)(tau_2) arrow.r (S_2 compose S_1)(alpha) = (S_2 compose S_1)(tau_2) arrow.r p."ty"$。

  *环节四（参数类型匹配）*：对 $n$ 类似地由环节一的对称版本和对 $n$ 的归纳假设加 @check_subst 得 `check(p.ctx, n) = some ((S₂∘S₁)(τ₂))`。箭头类型的定义域与参数类型吻合，`check(p.ctx, app m n)` 返回 `some p.ty`。

  `check` 返回 `none` 的各分支通过 @InferenceLookupInv + @CheckEqIfOccursInv 的反证法处理。
]
#定理([`InferenceSound`])[
  若 $"pp"(t) = "some"(p)$，则 $"check"(p."ctx", t) = "some"(p."ty")$。
]
#证明[
  $"pp"(t) = "pp'"(Gamma_emptyset, t)$。直接应用@inference_sound。
]
#推论[
  若 $"pp"(t) = "some"(p)$，则 $p."ctx" tack.r t : p."ty"$（按定义 2.5 的类型赋值规则）。
]

= 结论
本文给出了简单柯里类型λ式主类型推导算法的完整 Lean 4 形式化证明，包括：
+ STLC 语法、类型赋值规则与类型检查函数；
+ 罗宾逊合一算法与其终止性证明；
+ 主类型推导算法的完整正确性证明。

未来工作方向包括：将框架推广至带名字和递归的$lambda$式（LCNR）或米尔纳的 ML 类型系统，证明主类型算法的完备性等。

= AI 辅助声明

本文形式化的开发借助了语言大模型DeepSeek @deepseek 的辅助。 所有 AI 生成的证明草稿均经过仔细审查、修正与简化。

#pagebreak()
#bibliography("refs.bib")
