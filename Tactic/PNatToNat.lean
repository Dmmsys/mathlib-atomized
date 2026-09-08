/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Data.PNat.Basic
public meta import Mathlib.Tactic.ToAdditive


/-!
# `pnat_to_nat`

This file implements the `pnat_to_nat` tactic that shifts `PNat`s in the context to `Nat`.

## Implementation details
The implementation follows these steps:
1. For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`.
2. Translate arithmetic on `PNat` to `Nat` using the `pnat_to_nat_coe` simp set.

-/

public meta section

namespace Mathlib.Tactic.PNatToNat

open Lean Meta Elab Tactic Qq

/-- For each `x : PNat` in the context, add the hypothesis `0 < (↑x : ℕ)`. -/
elab "pnat_positivity" : tactic => withMainContext do
  let result ← (← getLCtx).foldlM (init := ← getMainGoal) fun g decl => do
    let ⟨1, declType, declExpr⟩ ← inferTypeQ decl.toExpr | return g
    let ~q(PNat) := declType | return g
    let pf := q(PNat.pos $declExpr)
    let ctx ← getLCtx
    let alreadyDeclared := Option.isSome <| ← ctx.findDeclM? fun ldecl => do
      if ← isDefEq ldecl.type q(0 < PNat.val $declExpr) then
        pure <| some ()
      else
        pure none
    if alreadyDeclared then
      return g
    let (_, mvarIdNew) ← (← g.assert .anonymous q(0 < PNat.val $declExpr) pf).intro1P
    return mvarIdNew
  setGoals [result]

@[pnat_to_nat_coe]
/-
**Mathlib.Tactic.PNatToNat.coe_inj** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.PNa
tToNat`。
形式化陈述：coe_inj (m n : PNat) : m = n ↔ (m : Nat) = (n : Nat)
参数：m n : PNat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_inj (m n : PNat) : m = n ↔ (m : ℕ) = (n : ℕ) := by simp

@[pnat_to_nat_coe]
/-
**Mathlib.Tactic.PNatToNat.coe_le_coe** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
PNatToNat`。
形式化陈述：coe_le_coe (m n : PNat) : m <= n ↔ (m : Nat) <= (n : Nat)
参数：m n : PNat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_le_coe (m n : PNat) : m ≤ n ↔ (m : ℕ) ≤ (n : ℕ) := by simp

@[pnat_to_nat_coe]
/-
**Mathlib.Tactic.PNatToNat.coe_lt_coe** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
PNatToNat`。
形式化陈述：coe_lt_coe (m n : PNat) : m < n ↔ (m : Nat) < (n : Nat)
参数：m n : PNat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_lt_coe (m n : PNat) : m < n ↔ (m : ℕ) < (n : ℕ) := by simp

attribute [pnat_to_nat_coe] PNat.add_coe PNat.mul_coe PNat.val_ofNat

set_option backward.isDefEq.respectTransparency false in
@[pnat_to_nat_coe]
/-
**Mathlib.Tactic.PNatToNat.sub_coe** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.PNa
tToNat`。
形式化陈述：sub_coe (a b : PNat) : ((a - b : PNat) : Nat) = a.val - 1 - b.val + 1
参数：a b : PNat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PNat.sub_coe`：sub_coe (a b : Nat+) : ((a - b : Nat+) : Nat) = ite (b < a
) (a - b : Nat) 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma sub_coe (a b : PNat) : ((a - b : PNat) : Nat) = a.val - 1 - b.val + 1 := by
  cases a
  cases b
  simp only [PNat.mk_coe, _root_.PNat.sub_coe, ← _root_.PNat.coe_lt_coe]
  split_ifs <;> lia

/-- `pnat_to_nat` shifts all `PNat`s in the context to `Nat`, rewriting propositions about them.
A typical use case is `pnat_to_nat; lia`. -/
macro "pnat_to_nat" : tactic => `(tactic| focus (
  pnat_positivity;
  simp only [pnat_to_nat_coe] at *)
)

end Mathlib.Tactic.PNatToNat

