/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.ENat.Basic
public meta import Mathlib.Tactic.ToAdditive

/-!
# `enat_to_nat`

This file implements the `enat_to_nat` tactic that shifts `ENat`s in the context to `Nat`.

## Implementation details
The implementation follows these steps:
1. Apply the `cases` tactic to each `ENat` variable, producing two goals: one where the variable
   is `⊤`, and one where it is a finite natural number.
2. Simplify arithmetic expressions involving infinities, making (in)equalities either trivial
   or free of infinities. This step uses the `enat_to_nat_top` simp set.
3. Translate the remaining goals from `ENat` to `Nat` using the `enat_to_nat_coe` simp set.

-/

public meta section

namespace Mathlib.Tactic.ENatToNat

attribute [enat_to_nat_top] OfNat.ofNat_ne_zero ne_eq not_false_eq_true ENat.natCast_ne_top
  ENat.top_ne_natCast ENat.natCast_lt_top top_le_iff le_top
attribute [enat_to_nat_top] top_add ENat.sub_top ENat.top_sub_natCast ENat.mul_top ENat.top_mul

/-
**Mathlib.Tactic.ENatToNat.not_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
ENatToNat`。
形式化陈述：∀ (x : ℕ∞), ¬⊤ < x
参数：x : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[enat_to_nat_top] lemma not_lt_top (x : ENat) :
    ¬(⊤ < x) := by cases x <;> simp
/-
**Mathlib.Tactic.ENatToNat.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.ENa
tToNat`。
形式化陈述：∀ (m n : ℕ), ↑m + ↑n = ↑(m + n)
参数：m n : ℕ；m + n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[enat_to_nat_coe] lemma coe_add (m n : ℕ) :
    (m : ENat) + (n : ENat) = ((m + n : ℕ) : ENat) := rfl
/-
**Mathlib.Tactic.ENatToNat.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.ENa
tToNat`。
形式化陈述：∀ (m n : ℕ), ↑m - ↑n = ↑(m - n)
参数：m n : ℕ；m - n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[enat_to_nat_coe] lemma coe_sub (m n : ℕ) :
    (m : ENat) - (n : ENat) = ((m - n : ℕ) : ENat) := rfl
/-
**Mathlib.Tactic.ENatToNat.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.ENa
tToNat`。
形式化陈述：∀ (m n : ℕ), ↑m * ↑n = ↑(m * n)
参数：m n : ℕ；m * n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[enat_to_nat_coe] lemma coe_mul (m n : ℕ) :
    (m : ENat) * (n : ENat) = ((m * n : ℕ) : ENat) := rfl
/-
**Mathlib.Tactic.ENatToNat.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.E
NatToNat`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], OfNat.ofNat n = ↑(OfNat.ofNat n)
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[enat_to_nat_coe] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ENat) = (OfNat.ofNat n : ℕ) := rfl
/-
**Mathlib.Tactic.ENatToNat.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.EN
atToNat`。
形式化陈述：0 = ↑0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[enat_to_nat_coe] lemma coe_zero : (0 : ENat) = ((0 : ℕ) : ENat) := rfl
/-
**Mathlib.Tactic.ENatToNat.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.ENa
tToNat`。
形式化陈述：1 = ↑1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[enat_to_nat_coe] lemma coe_one : (1 : ENat) = ((1 : ℕ) : ENat) := rfl

attribute [enat_to_nat_coe] ENat.natCast_inj ENat.natCast_le_natCast ENat.natCast_lt_natCast

open Qq Lean Elab Tactic Term Meta in
/-- Finds the first `ENat` in the context and applies the `cases` tactic to it.
Then simplifies expressions involving `⊤` using the `enat_to_nat_top` simp set. -/
elab "cases_first_enat" : tactic => focus do
  let g ← getMainGoal
  g.withContext do
    let ctx ← getLCtx
    let decl? ← ctx.findDeclM? fun decl => do
      if ← (isExprDefEq (← inferType decl.toExpr) q(ENat)) then
        return Option.some decl
      else
        return Option.none
    let some decl := decl? | throwError "No ENats"
    let isInaccessible := ctx.inaccessibleFVars.find? (·.fvarId == decl.fvarId) |>.isSome
    if isInaccessible then
      let name : Name := `enat_to_nat_aux
      setGoals [← g.rename decl.fvarId name]
      let x := mkIdent name
      evalTactic (← `(tactic| cases $x:ident using ENat.recTopCoe))
    else
      let x := mkIdent decl.userName
      evalTactic
        (← `(tactic| cases $x:ident using ENat.recTopCoe with | top => _ | coe $x:ident => _))
    evalTactic (← `(tactic| all_goals try simp only [enat_to_nat_top] at *))

/-- `enat_to_nat` shifts all `ENat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `enat_to_nat; lia`. -/
macro "enat_to_nat" : tactic => `(tactic| focus (
    (repeat' cases_first_enat) <;>
    (try simp only [enat_to_nat_top, enat_to_nat_coe] at *)
  )
)

end Mathlib.Tactic.ENatToNat

