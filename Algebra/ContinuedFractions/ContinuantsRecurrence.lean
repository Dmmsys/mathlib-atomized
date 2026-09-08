/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Translations

/-!
# Recurrence Lemmas for the Continuants (`conts`) Function of Continued Fractions

## Summary

Given a generalized continued fraction `g`, for all `n ≥ 1`, we prove that the continuants (`conts`)
function indeed satisfies the following recurrences:
- `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`, and
- `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/

public section


namespace GenContFract

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

/-
**GenContFract.contsAux_recurrence** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：contsAux_recurrence {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some
 gp) (nth_contsAux_eq : g.contsAux n = ppred) (succ_nth_contsAux_eq : g.contsAux
 (n + 1) = pred) : g.contsAux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * 
pred.b + gp.a * ppred.b⟩
参数：nth_s_eq : g.s.get? n = some gp；nth_contsAux_eq : g.contsAux n = ppred；succ_n
th_contsAux_eq : g.contsAux (n + 1) = pred。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem contsAux_recurrence {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.contsAux (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  simp [*, contsAux, nextConts, nextDen, nextNum]
/-
**GenContFract.conts_recurrenceAux** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：conts_recurrenceAux {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some
 gp) (nth_contsAux_eq : g.contsAux n = ppred) (succ_nth_contsAux_eq : g.contsAux
 (n + 1) = pred) : g.conts (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pre
d.b + gp.a * ppred.b⟩
参数：nth_s_eq : g.s.get? n = some gp；nth_contsAux_eq : g.contsAux n = ppred；succ_n
th_contsAux_eq : g.contsAux (n + 1) = pred。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.nth_cont_eq_succ_nth_contAux`：nth_cont_eq_succ_nth_contAux 
: g.conts n = g.contsAux (n + 1)
· 使用定理 `GenContFract.contsAux_recurrence`：contsAux_recurrence {gp ppred pred : P
air K} (nth_s_eq : g.s.get? n = some gp) (nth_contsAux_eq : g.contsAux n = ppred
) (succ_nth_contsAux_e…
-/
theorem conts_recurrenceAux {gp ppred pred : Pair K} (nth_s_eq : g.s.get? n = some gp)
    (nth_contsAux_eq : g.contsAux n = ppred)
    (succ_nth_contsAux_eq : g.contsAux (n + 1) = pred) :
    g.conts (n + 1) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ := by
  rw [nth_cont_eq_succ_nth_contAux,
    contsAux_recurrence nth_s_eq nth_contsAux_eq succ_nth_contsAux_eq]

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
/-
**GenContFract.conts_recurrence** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：conts_recurrence {gp ppred pred : Pair K} (succ_nth_s_eq : g.s.get? (n + 1
) = some gp) (nth_conts_eq : g.conts n = ppred) (succ_nth_conts_eq : g.conts (n 
+ 1) = pred) : g.conts (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b 
+ gp.a * ppred.b⟩
参数：succ_nth_s_eq : g.s.get? (n + 1) = some gp；nth_conts_eq : g.conts n = ppred；s
ucc_nth_conts_eq : g.conts (n + 1) = pred。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.contsAux_recurrence`：contsAux_recurrence {gp ppred pred : P
air K} (nth_s_eq : g.s.get? n = some gp) (nth_contsAux_eq : g.contsAux n = ppred
) (succ_nth_contsAux_e…

--- 原说明 ---
Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂` and `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/
theorem conts_recurrence {gp ppred pred : Pair K} (succ_nth_s_eq : g.s.get? (n + 1) = some gp)
    (nth_conts_eq : g.conts n = ppred) (succ_nth_conts_eq : g.conts (n + 1) = pred) :
    g.conts (n + 2) = ⟨gp.b * pred.a + gp.a * ppred.a, gp.b * pred.b + gp.a * ppred.b⟩ :=
  contsAux_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq

/-- Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`. -/
/-
**GenContFract.nums_recurrence** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：nums_recurrence {gp : Pair K} {ppredA predA : K} (succ_nth_s_eq : g.s.get?
 (n + 1) = some gp) (nth_num_eq : g.nums n = ppredA) (succ_nth_num_eq : g.nums (
n + 1) = predA) : g.nums (n + 2) = gp.b * predA + gp.a * ppredA
参数：succ_nth_s_eq : g.s.get? (n + 1) = some gp；nth_num_eq : g.nums n = ppredA；suc
c_nth_num_eq : g.nums (n + 1) = predA。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_conts_a_of_num`：exists_conts_a_of_num {A : K} (nth_n
um_eq : g.nums n = A) : exists conts, g.conts n = conts ∧ conts.a = A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.num_eq_conts_a`：num_eq_conts_a : g.nums n = (g.conts n).a
· 使用定理 `GenContFract.conts_recurrence`：conts_recurrence {gp ppred pred : Pair K}
 (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_conts_eq : g.conts n = ppred)
 (succ_nth_conts_eq…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Shows that `Aₙ = bₙ * Aₙ₋₁ + aₙ * Aₙ₋₂`.
-/
theorem nums_recurrence {gp : Pair K} {ppredA predA : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_num_eq : g.nums n = ppredA)
    (succ_nth_num_eq : g.nums (n + 1) = predA) :
    g.nums (n + 2) = gp.b * predA + gp.a * ppredA := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.conts n = conts ∧ conts.a = ppredA :=
    exists_conts_a_of_num nth_num_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      ∃ conts, g.conts (n + 1) = conts ∧ conts.a = predA :=
    exists_conts_a_of_num succ_nth_num_eq
  rw [num_eq_conts_a, conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

/-- Shows that `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`. -/
/-
**GenContFract.dens_recurrence** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：dens_recurrence {gp : Pair K} {ppredB predB : K} (succ_nth_s_eq : g.s.get?
 (n + 1) = some gp) (nth_den_eq : g.dens n = ppredB) (succ_nth_den_eq : g.dens (
n + 1) = predB) : g.dens (n + 2) = gp.b * predB + gp.a * ppredB
参数：succ_nth_s_eq : g.s.get? (n + 1) = some gp；nth_den_eq : g.dens n = ppredB；suc
c_nth_den_eq : g.dens (n + 1) = predB。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.exists_conts_b_of_den`：exists_conts_b_of_den {B : K} (nth_d
enom_eq : g.dens n = B) : exists conts, g.conts n = conts ∧ conts.b = B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.den_eq_conts_b`：den_eq_conts_b : g.dens n = (g.conts n).b
· 使用定理 `GenContFract.conts_recurrence`：conts_recurrence {gp ppred pred : Pair K}
 (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_conts_eq : g.conts n = ppred)
 (succ_nth_conts_eq…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Shows that `Bₙ = bₙ * Bₙ₋₁ + aₙ * Bₙ₋₂`.
-/
theorem dens_recurrence {gp : Pair K} {ppredB predB : K}
    (succ_nth_s_eq : g.s.get? (n + 1) = some gp) (nth_den_eq : g.dens n = ppredB)
    (succ_nth_den_eq : g.dens (n + 1) = predB) :
    g.dens (n + 2) = gp.b * predB + gp.a * ppredB := by
  obtain ⟨ppredConts, nth_conts_eq, ⟨rfl⟩⟩ : ∃ conts, g.conts n = conts ∧ conts.b = ppredB :=
    exists_conts_b_of_den nth_den_eq
  obtain ⟨predConts, succ_nth_conts_eq, ⟨rfl⟩⟩ :
      ∃ conts, g.conts (n + 1) = conts ∧ conts.b = predB :=
    exists_conts_b_of_den succ_nth_den_eq
  rw [den_eq_conts_b, conts_recurrence succ_nth_s_eq nth_conts_eq succ_nth_conts_eq]

end GenContFract

