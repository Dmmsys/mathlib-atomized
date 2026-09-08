/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon, Thomas Murrills, Mario Carneiro
-/
module

public meta import Qq
public meta import Mathlib.Util.AtomM
public import Mathlib.Data.List.TFAE  -- shake: keep (dependency of Qq output)
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Util.AtomM

/-!
# The Following Are Equivalent (TFAE)

This file provides the tactics `tfae_have` and `tfae_finish` for proving goals of the form
`TFAE [P₁, P₂, ...]`.
-/

public meta section

namespace Mathlib.Tactic.TFAE

/-! ### Parsing and syntax

We implement `tfae_have` in terms of a syntactic `have`. To support as much of the same syntax as
possible, we recreate the parsers for `have`, except with the changes necessary for `tfae_have`.
-/

open Lean.Parser Term

namespace Parser

-- An arrow of the form `←`, `→`, or `↔`.
/-
**Mathlib.Tactic.TFAE.Parser.impTo** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TFA
E.Parser`。
形式化陈述：impTo : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def impTo : Parser := leading_parser unicodeSymbol " → " " -> "
/-
**Mathlib.Tactic.TFAE.Parser.impFrom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.T
FAE.Parser`。
形式化陈述：impFrom : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def impFrom : Parser := leading_parser unicodeSymbol " ← " " <- "
/-
**Mathlib.Tactic.TFAE.Parser.impIff** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TF
AE.Parser`。
形式化陈述：impIff : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def impIff : Parser := leading_parser unicodeSymbol " ↔ " " <-> "
/-
**Mathlib.Tactic.TFAE.Parser.impArrow** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
TFAE.Parser`。
形式化陈述：impArrow : Parser
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def impArrow : Parser := leading_parser impTo <|> impFrom <|> impIff

attribute [nolint docBlame] impTo impFrom impIff impArrow

/-- A `tfae_have` type specification, e.g. `1 ↔ 3` The numbers refer to the proposition at the
corresponding position in the `TFAE` goal (starting at 1). -/
/-
**Mathlib.Tactic.TFAE.Parser.tfaeType** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.
TFAE.Parser`。
形式化陈述：tfaeType
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `tfae_have` type specification, e.g. `1 ↔ 3` The numbers refer to the proposit
ion at the
corresponding position in the `TFAE` goal (starting at 1).
-/
def tfaeType := leading_parser num >> impArrow >> num

/-!
The following parsers are similar to those for `have` in `Lean.Parser.Term`, but
instead of `optType`, we use `tfaeType := num >> impArrow >> num` (as a `tfae_have` invocation must
always include this specification). Also, we disallow including extra binders, as that makes no
sense in this context; we also include `" : "` after the binder to avoid breaking `tfae_have 1 → 2`
syntax (which, unlike `have`, omits `" : "`).
-/

/-- We need this to ensure `<|>` in `tfaeHaveIdLhs` takes in the same number of syntax trees on
each side. -/
/-
**Mathlib.Tactic.TFAE.Parser.binder** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TF
AE.Parser`。
形式化陈述：binder
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We need this to ensure `<|>` in `tfaeHaveIdLhs` takes in the same number of synt
ax trees on
each side.
-/
def binder := leading_parser ppSpace >> binderIdent >> " : "
/-- See `haveIdLhs`.

We omit `many (ppSpace >> letIdBinder)`, as it makes no sense to add extra arguments to a
`tfae_have` decl. -/
/-
**Mathlib.Tactic.TFAE.Parser.tfaeHaveIdLhs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ta
ctic.TFAE.Parser`。
形式化陈述：tfaeHaveIdLhs
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `haveIdLhs`.

We omit `many (ppSpace >> letIdBinder)`, as it makes no sense to add extra argum
ents to a
`tfae_have` decl.
-/
def tfaeHaveIdLhs := leading_parser
  (binder <|> hygieneInfo)  >> tfaeType
/-- See `haveIdDecl`. E.g. `h : 1 → 3 := term`. -/
/-
**Mathlib.Tactic.TFAE.Parser.tfaeHaveIdDecl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.T
actic.TFAE.Parser`。
形式化陈述：tfaeHaveIdDecl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `haveIdDecl`. E.g. `h : 1 → 3 := term`.
-/
def tfaeHaveIdDecl := leading_parser (withAnonymousAntiquot := false)
  atomic (tfaeHaveIdLhs >> " := ") >> termParser
/-- See `haveEqnsDecl`. E.g. `h : 1 → 3 | p => f p`. -/
/-
**Mathlib.Tactic.TFAE.Parser.tfaeHaveEqnsDecl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib
.Tactic.TFAE.Parser`。
形式化陈述：tfaeHaveEqnsDecl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `haveEqnsDecl`. E.g. `h : 1 → 3 | p => f p`.
-/
def tfaeHaveEqnsDecl := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdLhs >> matchAlts
/-- See `letPatDecl`. E.g. `⟨mp, mpr⟩ : 1 ↔ 3 := term`. -/
/-
**Mathlib.Tactic.TFAE.Parser.tfaeHavePatDecl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.
Tactic.TFAE.Parser`。
形式化陈述：tfaeHavePatDecl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `letPatDecl`. E.g. `⟨mp, mpr⟩ : 1 ↔ 3 := term`.
-/
def tfaeHavePatDecl := leading_parser (withAnonymousAntiquot := false)
  atomic (termParser >> pushNone >> " : " >> tfaeType >> " := ") >> termParser
/-- See `haveDecl`. Any of `tfaeHaveIdDecl`, `tfaeHavePatDecl`, or `tfaeHaveEqnsDecl`. -/
/-
**Mathlib.Tactic.TFAE.Parser.tfaeHaveDecl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic.TFAE.Parser`。
形式化陈述：tfaeHaveDecl
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `haveDecl`. Any of `tfaeHaveIdDecl`, `tfaeHavePatDecl`, or `tfaeHaveEqnsDecl
`.
-/
def tfaeHaveDecl := leading_parser (withAnonymousAntiquot := false)
  tfaeHaveIdDecl <|> (ppSpace >> tfaeHavePatDecl) <|> tfaeHaveEqnsDecl

-- Don't put doc-strings on these parsers in order to not override hover doc-strings.
attribute [nolint docBlame] binder
  tfaeHaveIdLhs tfaeHaveIdDecl tfaeHaveEqnsDecl tfaeHavePatDecl tfaeHaveDecl

end Parser

open Parser

/--
`tfae_have i → j := t`, where the goal is `TFAE [P₁, P₂, ...]` introduces a hypothesis
`tfae_i_to_j : Pᵢ → Pⱼ` and proof `t` to the local context. Note that `i` and `j` are
natural number literals (beginning at 1) used as indices to specify the propositions
`P₁, P₂, ...` that appear in the goal.

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

All features of `have` are supported by `tfae_have`, including naming, matching,
destructuring, and goal creation.

* `tfae_have i ← j := t` adds a hypothesis in the reverse direction, of type `Pⱼ → Pᵢ`.
* `tfae_have i ↔ j := t` adds a hypothesis in the both directions, of type `Pᵢ ↔ Pⱼ`.
* `tfae_have hij : i → j := t` names the introduced hypothesis `hij` instead of `tfae_i_to_j`.
* `tfae_have i j | p₁ => t₁ | ...` matches on the assumption `p : Pᵢ`.
* `tfae_have ⟨hij, hji⟩ : i ↔ j := t` destructures the bi-implication into `hij : Pᵢ → Pⱼ`
  and `hji : Pⱼ → Pⱼ`.
* `tfae_have i → j := t ?a` creates a new goal for `?a`.

Examples:
```lean4
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3 := h
  -- The resulting context now includes `tfae_1_to_3 : P → R`.
  sorry
```

```lean4
-- An example of `tfae_have` and `tfae_finish`:
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```

```lean4
-- All features of `have` are supported by `tfae_have`:
example : TFAE [P, Q] := by
  -- assert `tfae_1_to_2 : P → Q`:
  tfae_have 1 → 2 := sorry

  -- assert `hpq : P → Q`:
  tfae_have hpq : 1 → 2 := sorry

  -- match on `p : P` and prove `Q` via `f p`:
  tfae_have 1 → 2
  | p => f p

  -- assert `pq : P → Q`, `qp : Q → P`:
  tfae_have ⟨pq, qp⟩ : 1 ↔ 2 := sorry

  -- assert `h : P → Q`; `?a` is a new goal:
  tfae_have h : 1 → 2 := f ?a

  sorry
```
-/
syntax (name := tfaeHave) "tfae_have " tfaeHaveDecl : tactic

/--
`tfae_finish` closes goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean4
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := sorry /- proof of P → Q -/
  tfae_have 2 → 1 := sorry /- proof of Q → P -/
  tfae_have 2 ↔ 3 := sorry /- proof of Q ↔ R -/
  tfae_finish
```
-/
syntax (name := tfaeFinish) "tfae_finish" : tactic


/-! ### Setup -/

open List Lean Meta Expr Elab Tactic Mathlib.Tactic Qq

/-- Extract a list of `Prop` expressions from an expression of the form `TFAE [P₁, P₂, ...]` as
long as `[P₁, P₂, ...]` is an explicit list. -/
/-
**Mathlib.Tactic.TFAE.getTFAEList** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TFAE
`。
形式化陈述：Expr → MetaM (Q(List Prop) × List Q(Prop))
参数：Q(List Prop) × List Q(Prop)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract a list of `Prop` expressions from an expression of the form `TFAE [P₁, P
₂, ...]` as
long as `[P₁, P₂, ...]` is an explicit list.
-/
partial def getTFAEList (t : Expr) : MetaM (Q(List Prop) × List Q(Prop)) := do
  let .app tfae (l : Q(List Prop)) ← whnfR <|← instantiateMVars t
    | throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  unless (← withNewMCtxDepth <| isDefEq tfae q(TFAE)) do
    throwError "goal must be of the form TFAE [P₁, P₂, ...]"
  return (l, ← getExplicitList l)
where
  /-- Convert an expression representing an explicit list into a list of expressions. -/
  getExplicitList (l : Q(List Prop)) : MetaM (List Q(Prop)) := do
    match l with
    | ~q([]) => return ([] : List Expr)
    | ~q($a :: $l') => return (a :: (← getExplicitList l'))
    | e => throwError "{e} must be an explicit list of propositions"

/-! ### Proof construction -/

variable (hyps : Array (ℕ × ℕ × Expr)) (atoms : Array Q(Prop))

/-- Uses depth-first search to find a path from `P` to `P'`. -/
/-
**Mathlib.Tactic.TFAE.dfs** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tactic.TFAE`。
形式化陈述：Array (ℕ × ℕ × Expr) → Array Q(Prop) → ℕ → ℕ → (P P' : Q(Prop)) → Q(«$P») 
→ StateT (Std.HashSet ℕ) MetaM Q(«$P'»)
参数：ℕ × ℕ × Expr；Prop；P P' : Q(Prop)；«$P»；Std.HashSet ℕ；«$P'»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Uses depth-first search to find a path from `P` to `P'`.
-/
partial def dfs (i j : ℕ) (P P' : Q(Prop)) (hP : Q($P)) : StateT (Std.HashSet ℕ) MetaM Q($P') := do
  if i == j then
    return hP
  modify (·.insert i)
  for (a, b, h) in hyps do
    if i == a then
      if !(← get).contains b then
        have Q := atoms[b]!
        have h : Q($P → $Q) := h
        try return ← dfs b j Q P' q($h $hP) catch _ => pure ()
  failure

/-- Prove an implication via depth-first traversal. -/
/-
**Mathlib.Tactic.TFAE.proveImpl** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TFAE`。
形式化陈述：proveImpl (i j : Nat) (P P' : Q(Prop)) : MetaM Q($P -> $P')
参数：i j : Nat；P P' : Q(Prop)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prove an implication via depth-first traversal.
-/
def proveImpl (i j : ℕ) (P P' : Q(Prop)) : MetaM Q($P → $P') := do
  try
    withLocalDeclD (← mkFreshUserName `h) P fun (h : Q($P)) => do
      mkLambdaFVars #[h] <|← dfs hyps atoms i j P P' h |>.run' {}
  catch _ =>
    throwError "couldn't prove {P} → {P'}"

/-- Generate a proof of `Chain (· → ·) P l`. We assume `P : Prop` and `l : List Prop`, and that `l`
is an explicit list. -/
/-
**Mathlib.Tactic.TFAE.proveChain** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Tactic.TF
AE`。
形式化陈述：Array (ℕ × ℕ × Expr) →   Array Q(Prop) →     ℕ → List ℕ → (P : Q(Prop)) → 
(l : Q(List Prop)) → MetaM Q(List.IsChain (fun x1 x2 => x1 → x2) («$P» :: «$l»))
参数：ℕ × ℕ × Expr；Prop；P : Q(Prop)；l : Q(List Prop)；List.IsChain (fun x1 x2 => x1 
→ x2) («$P» :: «$l»)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generate a proof of `Chain (· → ·) P l`. We assume `P : Prop` and `l : List Prop
`, and that `l`
is an explicit list.
-/
partial def proveChain (i : ℕ) (is : List ℕ) (P : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(IsChain (· → ·) ($P :: $l)) := do
  match l with
  | ~q([]) => return q(.singleton _)
  | ~q($P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i' :: is' := id is | unreachable!
    have cl' : Q(IsChain (· → ·) ($P' :: $l')) := ← proveChain i' is' q($P') q($l')
    let p ← proveImpl hyps atoms i i' P P'
    return q(.cons_cons $p $cl')

/-- Attempt to prove `getLastD l P' → P` given an explicit list `l`. -/
/-
**Mathlib.Tactic.TFAE.proveGetLastDImpl** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Ta
ctic.TFAE`。
形式化陈述：Array (ℕ × ℕ × Expr) →   Array Q(Prop) → ℕ → ℕ → List ℕ → (P P' : Q(Prop))
 → (l : Q(List Prop)) → MetaM Q(«$l».getLastD «$P'» → «$P»)
参数：ℕ × ℕ × Expr；Prop；P P' : Q(Prop)；l : Q(List Prop)；«$l».getLastD «$P'» → «$P»。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attempt to prove `getLastD l P' → P` given an explicit list `l`.
-/
partial def proveGetLastDImpl (i i' : ℕ) (is : List ℕ) (P P' : Q(Prop)) (l : Q(List Prop)) :
    MetaM Q(getLastD $l $P' → $P) := do
  match l with
  | ~q([]) => proveImpl hyps atoms i' i P' P
  | ~q($P'' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i'' :: is' := id is | unreachable!
    proveGetLastDImpl i i'' is' P P'' l'

/-- Attempt to prove a statement of the form `TFAE [P₁, P₂, ...]`. -/
/-
**Mathlib.Tactic.TFAE.proveTFAE** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TFAE`。
形式化陈述：proveTFAE (is : List Nat) (l : Q(List Prop)) : MetaM Q(TFAE $l)
参数：is : List Nat；l : Q(List Prop)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Attempt to prove a statement of the form `TFAE [P₁, P₂, ...]`.
-/
def proveTFAE (is : List ℕ) (l : Q(List Prop)) : MetaM Q(TFAE $l) := do
  match l with
  | ~q([]) => return q(tfae_nil)
  | ~q([$P]) => return q(tfae_singleton $P)
  | ~q($P :: $P' :: $l') =>
    -- `id` is a workaround for https://github.com/leanprover-community/quote4/issues/30
    let i :: i' :: is' := id is | unreachable!
    let c ← proveChain hyps atoms i (i'::is') P q($P' :: $l')
    let il ← proveGetLastDImpl hyps atoms i i' is' P P' l'
    return q(tfae_of_cycle $c $il)

/-! ### `tfae_have` components -/

/-- Construct a name for a hypothesis introduced by `tfae_have`. -/
/-
**Mathlib.Tactic.TFAE.mkTFAEId** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TFAE`。
形式化陈述：TSyntax `Mathlib.Tactic.TFAE.Parser.tfaeType → MacroM Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a name for a hypothesis introduced by `tfae_have`.
-/
def mkTFAEId : TSyntax ``tfaeType → MacroM Name
  | `(tfaeType|$i:num $arr:impArrow $j:num) => do
    let arr ← match arr with
    | `(impArrow| ← ) => pure "from"
    | `(impArrow| → ) => pure "to"
    | `(impArrow| ↔ ) => pure "iff"
    | _ => Macro.throwUnsupported
    return .mkSimple <| String.intercalate "_" ["tfae", s!"{i.getNat}", arr, s!"{j.getNat}"]
  | _ => Macro.throwUnsupported

/-- Turn syntax for a given index into a natural number, as long as it lies between `1` and
`maxIndex`. -/
/-
**Mathlib.Tactic.TFAE.elabIndex** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TFAE`。
形式化陈述：elabIndex (i : TSyntax `num) (maxIndex : Nat) : MetaM Nat
参数：i : TSyntax `num；maxIndex : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn syntax for a given index into a natural number, as long as it lies between 
`1` and
`maxIndex`.
-/
def elabIndex (i : TSyntax `num) (maxIndex : ℕ) : MetaM ℕ := do
  let i' := i.getNat
  unless 1 ≤ i' && i' ≤ maxIndex do
    throwErrorAt i "{i} must be between 1 and {maxIndex}"
  return i'

/-! ### Tactic implementation -/

/-- Accesses the propositions at indices `i` and `j` of `tfaeList`, and constructs the expression
`Pi <arr> Pj`, which will be the type of our `tfae_have` hypothesis -/
/-
**Mathlib.Tactic.TFAE.elabTFAEType** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.TFA
E`。
形式化陈述：elabTFAEType (tfaeList : List Q(Prop)) : TSyntax ``tfaeType -> TermElabM E
xpr | stx@`(tfaeType|$i:num $arr:impArrow $j:num) => do let l
参数：tfaeList : List Q(Prop)。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Accesses the propositions at indices `i` and `j` of `tfaeList`, and constructs t
he expression
`Pi <arr> Pj`, which will be the type of our `tfae_have` hypothesis
-/
def elabTFAEType (tfaeList : List Q(Prop)) : TSyntax ``tfaeType → TermElabM Expr
  | stx@`(tfaeType|$i:num $arr:impArrow $j:num) => do
    let l := tfaeList.length
    let i' ← elabIndex i l
    let j' ← elabIndex j l
    let Pi := tfaeList[i'-1]!
    let Pj := tfaeList[j'-1]!
    /- TODO: this is a hack to show the types `Pi`, `Pj` on hover. See [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pre-RFC.3A.20Forcing.20terms.20to.20be.20shown.20in.20hover.3F). -/
    Term.addTermInfo' i q(sorry : $Pi) Pi
    Term.addTermInfo' j q(sorry : $Pj) Pj
    let (ty : Q(Prop)) ← match arr with
      | `(impArrow| ← ) => pure q($Pj → $Pi)
      | `(impArrow| → ) => pure q($Pi → $Pj)
      | `(impArrow| ↔ ) => pure q($Pi ↔ $Pj)
      | _ => throwUnsupportedSyntax
    Term.addTermInfo' stx q(sorry : $ty) ty
    return ty
  | _ => throwUnsupportedSyntax

/- Convert `tfae_have i <arr> j ...` to `tfae_have tfae_i_arr_j : i <arr> j ...`. See
`expandHave`, which is responsible for inserting `this` in `have : A := ...`. -/
macro_rules
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType := $val) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t := $val)
| `(tfaeHave|tfae_have $hy:hygieneInfo $t:tfaeType $alts:matchAlts) => do
  let id := HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true)
  `(tfaeHave|tfae_have $id : $t $alts)

open Term

elab_rules : tactic
| `(tfaeHave|tfae_have $d:tfaeHaveDecl) => withMainContext do
  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  withRef d do
    match d with
    | `(tfaeHaveDecl| $b : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $b : $(← exprToSyntax type) := $pf)
    | `(tfaeHaveDecl| $b : $t:tfaeType $alts:matchAlts) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $b : $(← exprToSyntax type) $alts:matchAlts)
    | `(tfaeHaveDecl| $pat:term : $t:tfaeType := $pf:term) =>
      let type ← elabTFAEType tfaeList t
      evalTactic <|← `(tactic|have $pat:term : $(← exprToSyntax type) := $pf)
    | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic| tfae_finish) => do
  let goal ← getMainGoal
  goal.withContext do
    let (tfaeListQ, tfaeList) ← getTFAEList (← goal.getType)
    closeMainGoal `tfae_finish <|← AtomM.run .reducible do
      let is ← tfaeList.mapM (fun e ↦ Prod.fst <$> AtomM.addAtom e)
      let mut hyps := #[]
      for hyp in ← getLocalHyps do
        let ty ← whnfR <|← instantiateMVars <|← inferType hyp
        if let (``Iff, #[p1, p2]) := ty.getAppFnArgs then
          let (q1, _) ← AtomM.addAtom p1
          let (q2, _) ← AtomM.addAtom p2
          hyps := hyps.push (q1, q2, ← mkAppM ``Iff.mp #[hyp])
          hyps := hyps.push (q2, q1, ← mkAppM ``Iff.mpr #[hyp])
        else if ty.isArrow then
          let (q1, _) ← AtomM.addAtom ty.bindingDomain!
          let (q2, _) ← AtomM.addAtom ty.bindingBody!
          hyps := hyps.push (q1, q2, hyp)
      proveTFAE hyps (← get).atoms is tfaeListQ

end Mathlib.Tactic.TFAE

/-!

### Deprecated "Goal-style" `tfae_have`

This syntax and its implementation, which behaves like "Mathlib `have`" is deprecated; we preserve
it here to provide graceful deprecation behavior.

-/

/-- Re-enables "goal-style" syntax for `tfae_have` when `true`. -/
register_option Mathlib.Tactic.TFAE.useDeprecated : Bool := {
  descr := "Re-enable \"goal-style\" 'tfae_have' syntax"
  defValue := false
}

namespace Mathlib.Tactic.TFAE

open Lean Parser Meta Elab Tactic

@[tactic_alt tfaeHave]
syntax (name := tfaeHave') "tfae_have " tfaeHaveIdLhs : tactic

extend_docs tfaeHave'
  before "\"Goal-style\" `tfae_have` syntax is deprecated. Now, `tfae_have ...` should be followed\
    by  `:= ...`; see below for the new behavior. This warning can be turned off with \
    `set_option Mathlib.Tactic.TFAE.useDeprecated true`.\n\n***"

elab_rules : tactic
| `(tfaeHave'|tfae_have $d:tfaeHaveIdLhs) => withMainContext do
  -- Deprecate syntax:
  let ref ← getRef
  unless useDeprecated.get (← getOptions) do
    logWarning <| .tagged ``Linter.deprecatedAttr m!"\
      \"Goal-style\" syntax '{ref}' is deprecated in favor of '{ref} := ...'.\n\n\
      To turn this warning off, use set_option Mathlib.Tactic.TFAE.useDeprecated true"

  let goal ← getMainGoal
  let (_, tfaeList) ← getTFAEList (← goal.getType)
  let (b, t) ← liftMacroM <| match d with
    | `(tfaeHaveIdLhs| $hy:hygieneInfo $t:tfaeType) => do
      pure (HygieneInfo.mkIdent hy (← mkTFAEId t) (canonical := true), t)
    | `(tfaeHaveIdLhs| $b:ident : $t:tfaeType) =>
      pure (b, t)
    | _ => Macro.throwUnsupported
  let n := b.getId
  let type ← elabTFAEType tfaeList t
  let p ← mkFreshExprMVar type MetavarKind.syntheticOpaque n
  let (fv, mainGoal) ← (← MVarId.assert goal n type p).intro1P
  mainGoal.withContext do
    Term.addTermInfo' (isBinder := true) b (mkFVar fv)
  replaceMainGoal [p.mvarId!, mainGoal]

end TFAE

end Mathlib.Tactic

