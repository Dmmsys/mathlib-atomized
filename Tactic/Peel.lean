/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public meta import Mathlib.Tactic.Basic
public import Mathlib.Order.Filter.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual

/-!
# The `peel` tactic

`peel h with h' idents*` tries to apply `forall_imp` (or `Exists.imp`, or `Filter.Eventually.mp`,
`Filter.Frequently.mp` and `Filter.Eventually.of_forall`) with the argument `h` and uses `idents*`
to introduce variables with the supplied names, giving the "peeled" argument the name `h'`.

One can provide a numeric argument as in `peel 4 h` which will peel 4 quantifiers off
the expressions automatically name any variables not specifically named in the `with` clause.

In addition, the user may supply a term `e` via `... using e` in order to close the goal
immediately. In particular, `peel h using e` is equivalent to `peel h; exact e`. The `using` syntax
may be paired with any of the other features of `peel`.
-/

public meta section

namespace Mathlib.Tactic.Peel
open Lean Expr Meta Elab Tactic

/--
Peels matching quantifiers off of a given term and the goal and introduces the relevant variables.

- `peel e` peels all quantifiers (at reducible transparency),
  using `this` for the name of the peeled hypothesis.
- `peel e with h` is `peel e` but names the peeled hypothesis `h`.
  If `h` is `_` then uses `this` for the name of the peeled hypothesis.
- `peel n e` peels `n` quantifiers (at default transparency).
- `peel n e with x y z ... h` peels `n` quantifiers, names the peeled hypothesis `h`,
  and uses `x`, `y`, `z`, and so on to name the introduced variables; these names may be `_`.
  If `h` is `_` then uses `this` for the name of the peeled hypothesis.
  The length of the list of variables does not need to equal `n`.
- `peel e with x₁ ... xₙ h` is `peel n e with x₁ ... xₙ h`.

There are also variants that apply to an iff in the goal:
- `peel n` peels `n` quantifiers in an iff.
- `peel with x₁ ... xₙ` peels `n` quantifiers in an iff and names them.

Given `p q : ℕ → Prop`, `h : ∀ x, p x`, and a goal `⊢ : ∀ x, q x`, the tactic `peel h with x h'`
will introduce `x : ℕ`, `h' : p x` into the context and the new goal will be `⊢ q x`. This works
with `∃`, as well as `∀ᶠ` and `∃ᶠ`, and it can even be applied to a sequence of quantifiers. Note
that this is a logically weaker setup, so using this tactic is not always feasible.

For a more complex example, given a hypothesis and a goal:
```
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
⊢ ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) ≤ ε
```
(which differ only in `<`/`≤`), applying `peel h with ε hε N n hn h_peel` will yield a tactic state:
```
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
ε : ℝ
hε : 0 < ε
N n : ℕ
hn : N ≤ n
h_peel : 1 / (n + 1 : ℝ) < ε
⊢ 1 / (n + 1 : ℝ) ≤ ε
```
and the goal can be closed with `exact h_peel.le`.
Note that in this example, `h` and the goal are logically equivalent statements, but `peel`
*cannot* be immediately applied to show that the goal implies `h`.

In addition, `peel` supports goals of the form `(∀ x, p x) ↔ ∀ x, q x`, or likewise for any
other quantifier. In this case, there is no hypothesis or term to supply, but otherwise the syntax
is the same. So for such goals, the syntax is `peel 1` or `peel with x`, and after which the
resulting goal is `p x ↔ q x`. The `congr!` tactic can also be applied to goals of this form using
`congr! 1 with x`. While `congr!` applies congruence lemmas in general, `peel` can be relied upon
to only apply to outermost quantifiers.

Finally, the user may supply a term `e` via `... using e` in order to close the goal
immediately. In particular, `peel h using e` is equivalent to `peel h; exact e`. The `using` syntax
may be paired with any of the other features of `peel`.

This tactic works by repeatedly applying lemmas such as `forall_imp`, `Exists.imp`,
`Filter.Eventually.mp`, `Filter.Frequently.mp`, and `Filter.Eventually.of_forall`.
-/
syntax (name := peel)
  "peel" (num)? (ppSpace colGt term)?
  (" with" (ppSpace colGt (ident <|> hole))+)? (usingArg)? : tactic

/--
lemma `and_imp_left_of_imp_imp` / 引理 `and_imp_left_of_imp_imp`

English:
lemma and_imp_left_of_imp_imp
  given: {p q r : Prop} (h : r -> p -> q)
  statement: r ∧ p -> r ∧ q
  proof: by tauto

中文:
引理 and_imp_left_of_imp_imp
  条件: {p q r : 命题} (h : r -> p -> q)
  结论: r ∧ p -> r ∧ q
  证明: by tauto
-/
lemma and_imp_left_of_imp_imp {p q r : Prop} (h : r -> p -> q) : r ∧ p -> r ∧ q := by tauto

/--
theorem `eventually_imp` / 定理 `eventually_imp`

English:
theorem eventually_imp
  statement: {α : Type*} {p q : α -> Prop} {f : Filter α}
  proof: Filter.Eventually.mp hp (Filter.Eventually.of_forall hq)

中文:
定理 eventually_imp
  结论: {α : 类型} {p q : α -> 命题} {f : 滤子 α}
  证明: Filter.Eventually.mp hp (Filter.Eventually.of_forall hq)

Depends on / 依赖: Eventually, Filter, Filter.Eventually.mp, Filter.Eventually.of_forall, of_forall
-/
theorem eventually_imp {α : Type*} {p q : α -> Prop} {f : Filter α}
    (hq : forall (x : α), p x -> q x) (hp : forallᶠ (x : α) in f, p x) : forallᶠ (x : α) in f, q x :=
  Filter.Eventually.mp hp (Filter.Eventually.of_forall hq)

/--
theorem `frequently_imp` / 定理 `frequently_imp`

English:
theorem frequently_imp
  statement: {α : Type*} {p q : α -> Prop} {f : Filter α}
  proof: Filter.Frequently.mp hp (Filter.Eventually.of_forall hq)

中文:
定理 frequently_imp
  结论: {α : 类型} {p q : α -> 命题} {f : 滤子 α}
  证明: Filter.Frequently.mp hp (Filter.Eventually.of_forall hq)

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, Filter.Frequently.mp, Frequently, of_forall
-/
theorem frequently_imp {α : Type*} {p q : α -> Prop} {f : Filter α}
    (hq : forall (x : α), p x -> q x) (hp : existsᶠ (x : α) in f, p x) : existsᶠ (x : α) in f, q x :=
  Filter.Frequently.mp hp (Filter.Eventually.of_forall hq)

/--
theorem `eventually_congr` / 定理 `eventually_congr`

English:
theorem eventually_congr
  statement: {α : Type*} {p q : α -> Prop} {f : Filter α}
  proof: by
  congr! 2; exact hq _

中文:
定理 eventually_congr
  结论: {α : 类型} {p q : α -> 命题} {f : 滤子 α}
  证明: by
  congr! 2; exact hq _
-/
theorem eventually_congr {α : Type*} {p q : α -> Prop} {f : Filter α}
    (hq : forall (x : α), p x ↔ q x) : (forallᶠ (x : α) in f, p x) ↔ forallᶠ (x : α) in f, q x := by
  congr! 2; exact hq _

/--
theorem `frequently_congr` / 定理 `frequently_congr`

English:
theorem frequently_congr
  statement: {α : Type*} {p q : α -> Prop} {f : Filter α}
  proof: by
  congr! 2; exact hq _

中文:
定理 frequently_congr
  结论: {α : 类型} {p q : α -> 命题} {f : 滤子 α}
  证明: by
  congr! 2; exact hq _
-/
theorem frequently_congr {α : Type*} {p q : α -> Prop} {f : Filter α}
    (hq : forall (x : α), p x ↔ q x) : (existsᶠ (x : α) in f, p x) ↔ existsᶠ (x : α) in f, q x := by
  congr! 2; exact hq _

/--
Definition of `quantifiers` / `quantifiers` 的定义

English:
definition quantifiers
  signature: : List Name
  body: [``Exists, ``And, ``Filter.Eventually, ``Filter.Frequently]

中文:
定义 quantifiers
  签名: : 列表 Name
  定义体: [``Exists, ``And, ``Filter.Eventually, ``Filter.Frequently]

Depends on / 依赖: Eventually, Exists, Filter, Filter.Eventually, Filter.Frequently, Frequently
-/
def quantifiers : List Name :=
  [``Exists, ``And, ``Filter.Eventually, ``Filter.Frequently]

/--
Definition of `whnfQuantifier` / `whnfQuantifier` 的定义

English:
definition whnfQuantifier
  signature: (p : Expr) (unfold : Bool)
  body: do
  if unfold then
    whnfHeadPred p fun e =>
      if let .const n .. := e.getAppFn then
        return !(n in quantifiers)
      else
        return false
  else
    whnfR p

中文:
定义 whnfQuantifier
  签名: (p : Expr) (unfold : 布尔值)
  定义体: do
  if unfold then
    whnfHeadPred p fun e =>
      if let .const n .. := e.getAppFn then
        return !(n in quantifiers)
      else
        return false
  else
    whnfR p
-/
def whnfQuantifier (p : Expr) (unfold : Bool) : MetaM Expr := do
  if unfold then
    whnfHeadPred p fun e =>
      if let .const n .. := e.getAppFn then
        return !(n in quantifiers)
      else
        return false
  else
    whnfR p

/--
Definition of `throwPeelError` / `throwPeelError` 的定义

English:
definition throwPeelError
  signature: {α : Type} (ty target : Expr)
  body: throwError "Tactic 'peel' could not match quantifiers in{indentD ty}\nand{indentD target}"

中文:
定义 throwPeelError
  签名: {α : 类型} (ty target : Expr)
  定义体: throwError "Tactic 'peel' could not match quantifiers in{indentD ty}\nand{indentD target}"

Depends on / 依赖: Tactic, indentD, quantifiers, target, throwError
-/
def throwPeelError {α : Type} (ty target : Expr) : MetaM α :=
  throwError "Tactic 'peel' could not match quantifiers in{indentD ty}\nand{indentD target}"

/--
Definition of `mkFreshBinderName` / `mkFreshBinderName` 的定义

English:
definition mkFreshBinderName
  signature: (f : Expr)
  body: mkFreshUserName (if let .lam n .. := f then n else `a)

中文:
定义 mkFreshBinderName
  签名: (f : Expr)
  定义体: mkFreshUserName (if let .lam n .. := f then n else `a)

Depends on / 依赖: mkFreshUserName
-/
def mkFreshBinderName (f : Expr) : MetaM Name :=
  mkFreshUserName (if let .lam n .. := f then n else `a)

/--
Definition of `applyPeelThm` / `applyPeelThm` 的定义

English:
definition applyPeelThm
  signature: (thm : Name) (goal : MVarId)
  body: do
let new_goal :: ge :: _ ← goal.applyConst thm > throwPeelError ty target
    | throwError "peel: internal error"
ge.assignIfDefEq e > throwPeelError ty target
  let (fvars, new_goal) ← new_goal.introN 2 [n, n']
  return (fvars[1]!, [new_goal])

中文:
定义 applyPeelThm
  签名: (thm : Name) (goal : MVarId)
  定义体: do
let new_goal :: ge :: _ ← goal.applyConst thm > throwPeelError ty target
    | throwError "peel: internal error"
ge.assignIfDefEq e > throwPeelError ty target
  let (fvars, new_goal) ← new_goal.introN 2 [n, n']
  return (fvars[1]!, [new_goal])
-/
def applyPeelThm (thm : Name) (goal : MVarId)
    (e : Expr) (ty target : Expr) (n : Name) (n' : Name) :
    MetaM (FVarId × List MVarId) := do
let new_goal :: ge :: _ ← goal.applyConst thm > throwPeelError ty target
    | throwError "peel: internal error"
ge.assignIfDefEq e > throwPeelError ty target
  let (fvars, new_goal) ← new_goal.introN 2 [n, n']
  return (fvars[1]!, [new_goal])

/--
Definition of `peelCore` / `peelCore` 的定义

English:
definition peelCore
  signature: (goal : MVarId) (e : Expr) (n? : Option Name) (n' : Name) (unfold : Bool)
  body: goal.withContext do
  let ty ← whnfQuantifier (← inferType e) unfold
  let target ← whnfQuantifier (← goal.getType) unfold
  if ty.isForall && target.isForall then
    applyPeelThm ``forall_imp goal e ty target (← n?.getDM (mkFreshUserName target.bindingName!)) n'
  else if ty.getAppFn.isConst
     

中文:
定义 peelCore
  签名: (goal : MVarId) (e : Expr) (n? : 选项类型 Name) (n' : Name) (unfold : 布尔值)
  定义体: goal.withContext do
  let ty ← whnfQuantifier (← inferType e) unfold
  let target ← whnfQuantifier (← goal.getType) unfold
  if ty.isForall && target.isForall then
    applyPeelThm ``forall_imp goal e ty target (← n?.getDM (mkFreshUserName target.bindingName!)) n'
  else if ty.getAppFn.isConst
     

Depends on / 依赖: goal.withContext, withContext
-/
def peelCore (goal : MVarId) (e : Expr) (n? : Option Name) (n' : Name) (unfold : Bool) :
    MetaM (FVarId × List MVarId) := goal.withContext do
  let ty ← whnfQuantifier (← inferType e) unfold
  let target ← whnfQuantifier (← goal.getType) unfold
  if ty.isForall && target.isForall then
    applyPeelThm ``forall_imp goal e ty target (← n?.getDM (mkFreshUserName target.bindingName!)) n'
  else if ty.getAppFn.isConst
            && ty.getAppNumArgs == target.getAppNumArgs
            && ty.getAppFn == target.getAppFn then
    match target.getAppFnArgs with
    | (``Exists, #[_, p]) =>
      applyPeelThm ``Exists.imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | (``And, #[_, _]) =>
      applyPeelThm ``and_imp_left_of_imp_imp goal e ty target (← n?.getDM (mkFreshUserName `p)) n'
    | (``Filter.Eventually, #[_, p, _]) =>
      applyPeelThm ``eventually_imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | (``Filter.Frequently, #[_, p, _]) =>
      applyPeelThm ``frequently_imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | _ => throwPeelError ty target
  else
    throwPeelError ty target

/--
Definition of `peelArgs` / `peelArgs` 的定义

English:
definition peelArgs
  signature: (e : Expr) (num : Nat) (l : List Name) (n? : Option Name) (unfold : Bool := true)
  body: do
  match num with
    | 0 => return
    | num + 1 =>
      let fvarId ← liftMetaTacticAux (peelCore · e l.head? (n?.getD `this) unfold)
      peelArgs (.fvar fvarId) num l.tail n?
      unless num == 0 do
        if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
          replac

中文:
定义 peelArgs
  签名: (e : Expr) (num : 自然数) (l : 列表 Name) (n? : 选项类型 Name) (unfold : 布尔值 := true)
  定义体: do
  match num with
    | 0 => return
    | num + 1 =>
      let fvarId ← liftMetaTacticAux (peelCore · e l.head? (n?.getD `this) unfold)
      peelArgs (.fvar fvarId) num l.tail n?
      unless num == 0 do
        if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
          replac
-/
def peelArgs (e : Expr) (num : Nat) (l : List Name) (n? : Option Name) (unfold : Bool := true) :
    TacticM Unit := do
  match num with
    | 0 => return
    | num + 1 =>
      let fvarId ← liftMetaTacticAux (peelCore · e l.head? (n?.getD `this) unfold)
      peelArgs (.fvar fvarId) num l.tail n?
      unless num == 0 do
        if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
          replaceMainGoal [mvarId]

/--
Definition of `peelUnbounded` / `peelUnbounded` 的定义

English:
definition peelUnbounded
  signature: (e : Expr) (n? : Option Name) (unfold : Bool := false)
  body: do
let fvarId? ← observing? liftMetaTacticAux (peelCore · e none (n?.getD `this) unfold)
  if let some fvarId := fvarId? then
    let peeled ← peelUnbounded (.fvar fvarId) n?
    if peeled then
      if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
        replaceMainGoal [mvarId

中文:
定义 peelUnbounded
  签名: (e : Expr) (n? : 选项类型 Name) (unfold : 布尔值 := false)
  定义体: do
let fvarId? ← observing? liftMetaTacticAux (peelCore · e none (n?.getD `this) unfold)
  if let some fvarId := fvarId? then
    let peeled ← peelUnbounded (.fvar fvarId) n?
    if peeled then
      if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
        replaceMainGoal [mvarId
-/
partial def peelUnbounded (e : Expr) (n? : Option Name) (unfold : Bool := false) :
    TacticM Bool := do
let fvarId? ← observing? liftMetaTacticAux (peelCore · e none (n?.getD `this) unfold)
  if let some fvarId := fvarId? then
    let peeled ← peelUnbounded (.fvar fvarId) n?
    if peeled then
      if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
        replaceMainGoal [mvarId]
    return true
  else
    return false

/--
Definition of `peelIffAux` / `peelIffAux` 的定义

English:
definition peelIffAux
  signature: : TacticM Unit
  body: do
  evalTactic (← `(tactic| focus
    first | apply forall_congr'
          | apply exists_congr
          | apply eventually_congr
          | apply frequently_congr
          | apply and_congr_right
          | fail "failed to apply a quantifier congruence lemma."))

中文:
定义 peelIffAux
  签名: : TacticM 单元
  定义体: do
  evalTactic (← `(tactic| focus
    first | apply forall_congr'
          | apply exists_congr
          | apply eventually_congr
          | apply frequently_congr
          | apply and_congr_right
          | fail "failed to apply a quantifier congruence lemma."))
-/
def peelIffAux : TacticM Unit := do
  evalTactic (← `(tactic| focus
    first | apply forall_congr'
          | apply exists_congr
          | apply eventually_congr
          | apply frequently_congr
          | apply and_congr_right
          | fail "failed to apply a quantifier congruence lemma."))

/--
Definition of `peelArgsIff` / `peelArgsIff` 的定义

English:
definition peelArgsIff
  signature: (l : List Name)
  body: withMainContext do
  match l with
    | [] => pure ()
    | h :: hs =>
      peelIffAux
      let goal ← getMainGoal
      let (_, new_goal) ← goal.intro h
      replaceMainGoal [new_goal]
      peelArgsIff hs

elab_rules : tactic
  | `(tactic| peel $[$num?:num]? $e:term $[with $l?* $n?]?) => withMa

中文:
定义 peelArgsIff
  签名: (l : 列表 Name)
  定义体: withMainContext do
  match l with
    | [] => pure ()
    | h :: hs =>
      peelIffAux
      let goal ← getMainGoal
      let (_, new_goal) ← goal.intro h
      replaceMainGoal [new_goal]
      peelArgsIff hs

elab_rules : tactic
  | `(tactic| peel $[$num?:num]? $e:term $[with $l?* $n?]?) => withMa

Depends on / 依赖: withMainContext
-/
def peelArgsIff (l : List Name) : TacticM Unit := withMainContext do
  match l with
    | [] => pure ()
    | h :: hs =>
      peelIffAux
      let goal ← getMainGoal
      let (_, new_goal) ← goal.intro h
      replaceMainGoal [new_goal]
      peelArgsIff hs

elab_rules : tactic
  | `(tactic| peel $[$num?:num]? $e:term $[with $l?* $n?]?) => withMainContext do
    /- we use `elabTermForApply` instead of `elabTerm` so that terms passed to `peel` can contain
    quantifiers with implicit bound variables without causing errors or requiring `@`. -/
    let e ← elabTermForApply e false
    let n? := n?.bind fun n => if n.raw.isIdent then pure n.raw.getId else none
.toList let l := (l?.getD #[]).map getNameOfIdent'
    -- If num is not present and if there are any provided variable names,
    -- use the number of variable names.
let num? := num?.map (·.getNat) > if l.isEmpty then none else l.length
    if let some num := num? then
      peelArgs e num l n?
    else
      unless ← peelUnbounded e n? do
        throwPeelError (← inferType e) (← getMainTarget)
| `(tactic| peel $n:num) => peelArgsIff .replicate n.getNat `_
  | `(tactic| peel with $args*) => peelArgsIff (args.map getNameOfIdent').toList

macro_rules
  | `(tactic| peel $[$n:num]? $[$e:term]? $[with $h*]? using $u:term) =>
    `(tactic| peel $[$n:num]? $[$e:term]? $[with $h*]?; exact $u)

end Mathlib.Tactic.Peel
