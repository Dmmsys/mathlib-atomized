/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public meta import Batteries.Lean.Expr
public meta import Batteries.Lean.Meta.UnusedNames
public meta import Lean.Elab.Tactic.RCases
public import Mathlib.Tactic.TypeStar

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

public meta section

/--
Definition of `CanLift` / `CanLift` 的定义

English:
class CanLift
  parameters: (α β : Sort*) (coe : outParam <| β -> α) (cond : outParam <| α -> Prop)
  axioms and operations (1):
    - prf : forall x : α, cond x -> exists y : β, coe y = x

中文:
类 CanLift
  参数: (α β : Sort*) (coe : outParam <| β -> α) (cond : outParam <| α -> 命题)
  公理与运算 (1 个):
    - prf : 对任意 x : α, cond x -> 存在 y : β, coe y = x
-/
class CanLift (α β : Sort*) (coe : outParam <| β -> α) (cond : outParam <| α -> Prop) : Prop where
  /-- An element of `α` that satisfies `cond` belongs to the range of `coe`. -/
  prf : forall x : α, cond x -> exists y : β, coe y = x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift Int Nat (fun n : Nat => n) (0 <= ·)
  body: ⟨fun n hn => ⟨n.natAbs, Int.natAbs_of_nonneg hn⟩⟩

中文:
实例 :
  签名: CanLift 整数 自然数 (fun n : 自然数 => n) (0 <= ·)
  定义体: ⟨fun n hn => ⟨n.natAbs, Int.natAbs_of_nonneg hn⟩⟩

Depends on / 依赖: Int.natAbs_of_nonneg, n.natAbs, natAbs, natAbs_of_nonneg
-/
instance : CanLift Int Nat (fun n : Nat => n) (0 <= ·) :=
  ⟨fun n hn => ⟨n.natAbs, Int.natAbs_of_nonneg hn⟩⟩

/--
Instance `Pi.canLift` / 实例 `Pi.canLift`

English:
instance Pi.canLift
  signature: (ι : Sort*) (α β : ι -> Sort*) (coe : forall i, β i -> α i) (P : forall i, α i -> Prop)
  body: ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩

中文:
实例 Pi.canLift
  签名: (ι : Sort*) (α β : ι -> Sort*) (coe : 对任意 i, β i -> α i) (P : 对任意 i, α i -> 命题)
  定义体: ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩

Depends on / 依赖: CanLift, CanLift.prf, Classical, Classical.choose
-/
instance Pi.canLift (ι : Sort*) (α β : ι -> Sort*) (coe : forall i, β i -> α i) (P : forall i, α i -> Prop)
    [forall i, CanLift (α i) (β i) (coe i) (P i)] :
    CanLift (forall i, α i) (forall i, β i) (fun f i => coe i (f i)) fun f => forall i, P i (f i) where
  prf f hf := ⟨fun i => Classical.choose (CanLift.prf (f i) (hf i)),
    funext fun i => Classical.choose_spec (CanLift.prf (f i) (hf i))⟩

/--
Instance `Prod.instCanLift` / 实例 `Prod.instCanLift`

English:
instance Prod.instCanLift
  signature: {α β γ δ : Type*} {coeβα condβα coeδγ condδγ} [CanLift α β coeβα condβα]
  body: by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rcases CanLift.prf (β := β) x hx with ⟨x, rfl⟩
    rcases CanLift.prf (β := δ) y hy with ⟨y, rfl⟩
    exact ⟨(x, y), by simp⟩

中文:
实例 Prod.instCanLift
  签名: {α β γ δ : 类型} {coeβα condβα coeδγ condδγ} [CanLift α β coeβα condβα]
  定义体: by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rcases CanLift.prf (β := β) x hx with ⟨x, rfl⟩
    rcases CanLift.prf (β := δ) y hy with ⟨y, rfl⟩
    exact ⟨(x, y), by simp⟩

Depends on / 依赖: CanLift, CanLift.prf
-/
instance Prod.instCanLift {α β γ δ : Type*} {coeβα condβα coeδγ condδγ} [CanLift α β coeβα condβα]
    [CanLift γ δ coeδγ condδγ] :
    CanLift (α × γ) (β × δ) (Prod.map coeβα coeδγ) (fun x => condβα x.1 ∧ condδγ x.2) where
  prf := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rcases CanLift.prf (β := β) x hx with ⟨x, rfl⟩
    rcases CanLift.prf (β := δ) y hy with ⟨y, rfl⟩
    exact ⟨(x, y), by simp⟩

/--
theorem `Subtype.exists_pi_extension` / 定理 `Subtype.exists_pi_extension`

English:
theorem Subtype.exists_pi_extension
  statement: {ι : Sort*} {α : ι -> Sort*} [ne : forall i, Nonempty (α i)]
  proof: by
  haveI : DecidablePred p := fun i => Classical.propDecidable (p i)
  exact ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (ne i),
    funext fun i => dif_pos i.2⟩

中文:
定理 Subtype.exists_pi_extension
  结论: {ι : Sort*} {α : ι -> Sort*} [ne : 对任意 i, Nonempty (α i)]
  证明: by
  haveI : DecidablePred p := fun i => Classical.propDecidable (p i)
  exact ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (ne i),
    funext fun i => dif_pos i.2⟩

Depends on / 依赖: Classical, Classical.choice, Classical.propDecidable, DecidablePred, choice, dif_pos, propDecidable
-/
theorem Subtype.exists_pi_extension {ι : Sort*} {α : ι -> Sort*} [ne : forall i, Nonempty (α i)]
    {p : ι -> Prop} (f : forall i : Subtype p, α i) :
    exists g : forall i : ι, α i, (fun i : Subtype p => g i) = f := by
  haveI : DecidablePred p := fun i => Classical.propDecidable (p i)
  exact ⟨fun i => if hi : p i then f ⟨i, hi⟩ else Classical.choice (ne i),
    funext fun i => dif_pos i.2⟩

/--
Instance `PiSubtype.canLift` / 实例 `PiSubtype.canLift`

English:
instance PiSubtype.canLift
  signature: (ι : Sort*) (α : ι -> Sort*) [forall i, Nonempty (α i)] (p : ι -> Prop)
  body: Subtype.exists_pi_extension f

中文:
实例 PiSubtype.canLift
  签名: (ι : Sort*) (α : ι -> Sort*) [对任意 i, Nonempty (α i)] (p : ι -> 命题)
  定义体: Subtype.exists_pi_extension f

Depends on / 依赖: Subtype, Subtype.exists_pi_extension, exists_pi_extension
-/
instance PiSubtype.canLift (ι : Sort*) (α : ι -> Sort*) [forall i, Nonempty (α i)] (p : ι -> Prop) :
    CanLift (forall i : Subtype p, α i) (forall i, α i) (fun f i => f i) fun _ => True where
  prf f _ := Subtype.exists_pi_extension f

-- TODO: test if we need this instance in Lean 4
/--
Instance `PiSubtype.canLift'` / 实例 `PiSubtype.canLift'`

English:
instance PiSubtype.canLift'
  signature: (ι : Sort*) (α : Sort*) [Nonempty α] (p : ι -> Prop)
  body: PiSubtype.canLift ι (fun _ => α) p

中文:
实例 PiSubtype.canLift'
  签名: (ι : Sort*) (α : Sort*) [Nonempty α] (p : ι -> 命题)
  定义体: PiSubtype.canLift ι (fun _ => α) p

Depends on / 依赖: PiSubtype, PiSubtype.canLift, canLift
-/
instance PiSubtype.canLift' (ι : Sort*) (α : Sort*) [Nonempty α] (p : ι -> Prop) :
    CanLift (Subtype p -> α) (ι -> α) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι (fun _ => α) p

/--
Instance `Subtype.canLift` / 实例 `Subtype.canLift`

English:
instance Subtype.canLift
  signature: {α : Sort*} (p : α -> Prop)
  body: ⟨⟨a, ha⟩, rfl⟩

中文:
实例 Subtype.canLift
  签名: {α : Sort*} (p : α -> 命题)
  定义体: ⟨⟨a, ha⟩, rfl⟩
-/
instance Subtype.canLift {α : Sort*} (p : α -> Prop) :
    CanLift α { x // p x } Subtype.val p where prf a ha :=
  ⟨⟨a, ha⟩, rfl⟩

namespace Mathlib.Tactic

open Lean Parser Elab Tactic Meta

/--
`lift e to t with x` lifts the expression `e` to the type `t` by introducing a new variable `x : t`
such that `↑x = e`, and then replacing occurrences of `e` with `↑x`. `lift` requires an instance of
the class `CanLift t' t coe cond`, where `t'` is the type of `e`, and creates a side goal for the
lifting condition, of the form `⊢ cond x`, placing this on top of the goal stack.

Given an instance `CanLift β γ`, `lift` can also lift `α → β` to `α → γ`; more generally, given
`β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, CanLift (β a) (γ a)]`, it
automatically generates an instance `CanLift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.

The `norm_cast` tactic can be used after `lift` to normalize introduced casts.

* `lift e to t using h with x` uses the expression `h` to prove the lifting condition `cond e`.
  If `h` is a variable, `lift` will try to clear it from the context. If you want to keep `h` in
  the context, write `lift e to t using h with x rfl h` (see below).
* If `e` is a variable, `lift e to t` is equivalent to `lift e to t with e`. The original variable
  `e` will be cleared from the context.
* `lift e to t with x hx` adds `hx : ↑x = e` to the context (and if `e` is a variable, does not
  clear it).
* `lift e to t with x hx h` adds `hx : ↑x = e` and `h : cond e` to the context (and if `e` is a
  variable, does not clear it). In particular, `lift e to t using h with x hx h`, where `h` is a
  variable, keeps `h` in the context.
* `lift e to t with x rfl h` adds `h : cond e` to the context (and if `e` is a variable, does not
  clear it). In particular, `lift e to t using h with x rfl h`, where `h` is a variable, keeps `h`
  in the context.

Examples:
```
def P (n : ℤ) : Prop := n = 3

example (n : ℤ) (h : P n) : n = 3 := by
  lift n to ℕ
  /-
  Two goals:
  n : ℤ, h : P n ⊢ n ≥ 0
  n : ℕ, h : P ↑n ⊢ ↑n = 3
  -/
  · unfold P at h; linarith
  · exact h

example (n : Int) (hn : n >= 0) (h : P n) : n = 3 := by
  lift n to Nat using hn
  /-
  One goal:
  n : ℕ
  h : P ↑n
  ⊢ ↑n = 3
  -/
  exact h

example (n : Int) (hn : n + 3 >= 0) (h : P (n + 3)) :
    n + 3 = n * 2 + 3 := by
  lift n + 3 to Nat using hn with k hk
  /-
  One goal:
  n : ℤ
  k : ℕ
  hk : ↑k = n + 3
  h : P ↑k
  ⊢ ↑k = 2 * n + 3
  -/
  unfold P at h; linarith
```
-/
syntax (name := lift) "lift " term " to " term (" using " term)?
  (" with " ident (ppSpace colGt ident)? (ppSpace colGt ident)?)? : tactic

/--
Definition of `Lift.getInst` / `Lift.getInst` 的定义

English:
definition Lift.getInst
  signature: (old_tp new_tp : Expr)
  body: do
  let coe ← mkFreshExprMVar (some <| .forallE `a new_tp old_tp .default)
  let p ← mkFreshExprMVar (some <| .forallE `a old_tp (.sort .zero) .default)
  let inst_type ← mkAppM ``CanLift #[old_tp, new_tp, coe, p]
  let inst ← synthInstance inst_type -- TODO: catch error
  return (← instantiateMVar

中文:
定义 Lift.getInst
  签名: (old_tp new_tp : Expr)
  定义体: do
  let coe ← mkFreshExprMVar (some <| .forallE `a new_tp old_tp .default)
  let p ← mkFreshExprMVar (some <| .forallE `a old_tp (.sort .zero) .default)
  let inst_type ← mkAppM ``CanLift #[old_tp, new_tp, coe, p]
  let inst ← synthInstance inst_type -- TODO: catch error
  return (← instantiateMVar
-/
def Lift.getInst (old_tp new_tp : Expr) : MetaM (Expr × Expr × Expr) := do
  let coe ← mkFreshExprMVar (some <| .forallE `a new_tp old_tp .default)
  let p ← mkFreshExprMVar (some <| .forallE `a old_tp (.sort .zero) .default)
  let inst_type ← mkAppM ``CanLift #[old_tp, new_tp, coe, p]
  let inst ← synthInstance inst_type -- TODO: catch error
  return (← instantiateMVars p, ← instantiateMVars coe, ← instantiateMVars inst)

/--
Definition of `Lift.main` / `Lift.main` 的定义

English:
definition Lift.main
  signature: (e t : TSyntax `term) (hUsing : Option (TSyntax `term))
  body: withMainContext do
  -- Are we using a new variable for the lifted var?
  let isNewVar := !newVarName.isNone
  -- Name of the new hypothesis containing the equality of the lifted variable with the old one
  -- rfl if none is given
  let newEqName := (newEqName.map Syntax.getId).getD `rfl
  -- Was a 

中文:
定义 Lift.main
  签名: (e t : TSyntax `term) (hUsing : Option (TSyntax `term))
  定义体: withMainContext do
  -- Are we using a new variable for the lifted var?
  let isNewVar := !newVarName.isNone
  -- Name of the new hypothesis containing the equality of the lifted variable with the old one
  -- rfl if none is given
  let newEqName := (newEqName.map Syntax.getId).getD `rfl
  -- Was a 

Depends on / 依赖: withMainContext
-/
def Lift.main (e t : TSyntax `term) (hUsing : Option (TSyntax `term))
    (newVarName newEqName : Option (TSyntax `ident)) (keepUsing : Bool) : TacticM Unit :=
    withMainContext do
  -- Are we using a new variable for the lifted var?
  let isNewVar := !newVarName.isNone
  -- Name of the new hypothesis containing the equality of the lifted variable with the old one
  -- rfl if none is given
  let newEqName := (newEqName.map Syntax.getId).getD `rfl
  -- Was a new hypothesis given?
  let isNewEq := newEqName != `rfl
  let e ← elabTerm e none
  let goal ← getMainGoal
  if !(← inferType (← instantiateMVars (← goal.getType))).isProp then throwError
    "lift tactic failed. Tactic is only applicable when the target is a proposition."
  if newVarName == none ∧ !e.isFVar then throwError
    "lift tactic failed. When lifting an expression, a new variable name must be given"
  let (p, coe, inst) ← Lift.getInst (← inferType e) (← Term.elabType t)
  let prf ← match hUsing with
    | some h => elabTermEnsuringType h (p.betaRev #[e])
    | none => mkFreshExprMVar (some (p.betaRev #[e]))
  let newVarName ← match newVarName with
                 | some v => pure v.getId
                 | none => e.fvarId!.getUserName
  let prfEx ← mkAppOptM ``CanLift.prf #[none, none, coe, p, inst, e, prf]
  let prfEx ← instantiateMVars prfEx
  let prfSyn ← prfEx.toSyntax
  -- if we have a new variable, but no hypothesis name was provided, we temporarily use a dummy
  -- hypothesis name
let newEqName ← if isNewVar && !isNewEq then withMainContext getUnusedUserName `tmpVar
               else pure newEqName
  let newEqIdent := mkIdent newEqName
  -- Run rcases on the proof of the lift condition
  replaceMainGoal (← Lean.Elab.Tactic.RCases.rcases #[(none, prfSyn)]
    (.tuple Syntax.missing <| [newVarName, newEqName].map (.one Syntax.missing)) goal)
  -- if we use a new variable, then substitute it everywhere
  if isNewVar then
    for decl in ← getLCtx do
      if decl.userName != newEqName then
        let declIdent := mkIdent decl.userName
        evalTactic (← `(tactic| simp -failIfUnchanged only [← $newEqIdent] at $declIdent:ident))
    evalTactic (← `(tactic| simp -failIfUnchanged only [← $newEqIdent]))
  -- Clear the temporary hypothesis used for the new variable name if applicable
  if isNewVar && !isNewEq then
    evalTactic (← `(tactic| clear $newEqIdent))
  -- Clear the "using" hypothesis if it's a variable in the context
  if prf.isFVar && !keepUsing then
    let some hUsingStx := hUsing | throwError "lift tactic failed: unreachable code was reached"
    evalTactic (← `(tactic| try clear $hUsingStx))
if hUsing.isNone then withMainContext setGoals (prf.mvarId! :: (← getGoals))

elab_rules : tactic
| `(tactic| lift $e to $t $[using $h]? $[with $newVarName $[$newEqName]? $[$newPrfName]?]?) =>
withMainContext
    let keepUsing := match h, newPrfName.join with
      | some h, some newPrfName => h.raw == newPrfName
      | _, _ => false
    Lift.main e t h newVarName newEqName.join keepUsing

end Mathlib.Tactic
