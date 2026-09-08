/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Tactic.Ring

/-!
# Determinant Formula for Generalized Continued Fraction

We derive the so-called *determinant formula* for `GenContFract`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ)`.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/

public section

open GenContFract

variable {K : Type*} [Field K]

namespace GenContFract

variable {g : GenContFract K} {n : ℕ}

/-
**GenContFract.determinant_aux** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem determinant_aux (hyp : n = 0 ∨ ¬g.TerminatedAt (n - 1)) :
    (g.contsAux n).a * (g.contsAux (n + 1)).b -
      (g.contsAux n).b * (g.contsAux (n + 1)).a =
        ∏ i ∈ Finset.range n, - (g.partNums.get? i).getD 0 := by
  induction n with
  | zero => simp [contsAux]
  | succ n IH =>
    -- set up some shorthand notation
    let conts := contsAux g (n + 2)
    set pred_conts := contsAux g (n + 1) with pred_conts_eq
    set ppred_conts := contsAux g n with ppred_conts_eq
    let pA := pred_conts.a
    let pB := pred_conts.b
    let ppA := ppred_conts.a
    let ppB := ppred_conts.b
    -- let's change the goal to something more readable
    change pA * conts.b - pB * conts.a = ∏ i ∈ Finset.range (n + 1), -(g.partNums.get? i).getD 0
    have not_terminated_at_n : ¬TerminatedAt g n := Or.resolve_left hyp n.succ_ne_zero
    obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
      Option.ne_none_iff_exists'.1 not_terminated_at_n
    -- unfold the recurrence relation for `conts` once and simplify to derive the following
    suffices ppA * pB - ppB * pA = ∏ i ∈ Finset.range n, - (g.partNums.get? i).getD 0 by
      rw [Finset.prod_range_succ, ← this, partNum_eq_s_a s_nth_eq, Option.getD_some]
      subst conts
      rw [contsAux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq]
      ring
    exact IH <| Or.inr <| mt (terminated_stable <| n.sub_le 1) not_terminated_at_n

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ)`. -/
/-
**GenContFract.determinant** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：determinant : g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) = ∏ i 
in Finset.range (n + 1), - (g.partNums.get? i).getD 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.dens_stable_of_terminated`：dens_stable_of_terminated (n_le_
m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.dens m = g.dens n
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `GenContFract.nums_stable_of_terminated`：nums_stable_of_terminated (n_le_
m : n <= m) (terminatedAt_n : g.TerminatedAt n) : g.nums m = g.nums n
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.partNum_none_iff_s_none`：partNum_none_iff_s_none : g.partNu
ms.get? n = none ↔ g.s.get? n = none
· 使用定理 `_private.Mathlib.Algebra.ContinuedFractions.Determinant.0.GenContFract.d
eterminant_aux`：∀ {K : Type u_1} [inst : Field K] {g : GenContFract K} {n : ℕ}, 
  n = 0 ∨ ¬g.TerminatedAt (n - 1) →     (g.contsAux n).a * (g.contsAux (n + …

--- 原说明 ---
The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-a₀) * (-a₁) * .. * (-aₙ)`.
-/
theorem determinant :
    g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1) =
      ∏ i ∈ Finset.range (n + 1), - (g.partNums.get? i).getD 0 := by
  rcases em <| TerminatedAt g n with terminatedAt_n | not_terminatedAt_n
  · rw [dens_stable_of_terminated n.le_succ terminatedAt_n,
      nums_stable_of_terminated n.le_succ terminatedAt_n, Finset.prod_range_succ,
      partNum_none_iff_s_none.mpr terminatedAt_n]
    grind
  · exact determinant_aux <| Or.inr <| not_terminatedAt_n
end GenContFract

namespace SimpContFract

variable {s : SimpContFract K} {n : ℕ}

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1) ^ (n + 1)` for `SimpContFract`. -/
/-
**SimpContFract.determinant** 是 Mathlib 中的一个定理，位于命名空间 `SimpContFract`。
形式化陈述：determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
 (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) - (↑s : GenCo
ntFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1)
参数：not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.determinant`：determinant : g.nums n * g.dens (n + 1) - g.de
ns n * g.nums (n + 1) = ∏ i in Finset.range (n + 1), - (g.partNums.get? i).getD 
0
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `GenContFract.terminated_stable`：terminated_stable (n_le_m : n <= m) (ter
minatedAt_n : g.TerminatedAt n) : g.TerminatedAt m
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `GenContFract.partNum_eq_s_a`：partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.
s.get? n = some gp) : g.partNums.get? n = some gp.a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Option.getD_some`：∀ {α : Type u_1} {a b : α}, (some a).getD b = a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n

--- 原说明 ---
The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1) ^ (n + 1)` for `SimpContFr
act`.
-/
theorem determinant (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n) :
    (↑s : GenContFract K).nums n * (↑s : GenContFract K).dens (n + 1) -
      (↑s : GenContFract K).dens n * (↑s : GenContFract K).nums (n + 1) = (-1) ^ (n + 1) := calc
  _ = ∏ i ∈ Finset.range (n + 1), - ((↑s : GenContFract K).partNums.get? i).getD 0 :=
    (↑s : GenContFract K).determinant
  _ = ∏ i ∈ Finset.range (n + 1), -1 := Finset.prod_congr rfl fun i hi ↦ by
    rw [Finset.mem_range] at hi
    obtain ⟨gp, s_ith_eq⟩ : ∃ gp, (↑s : GenContFract K).s.get? i = some gp :=
      Option.ne_none_iff_exists'.1 <| mt (terminated_stable <| Nat.le_of_succ_le_succ hi) ‹_›
    rw [partNum_eq_s_a s_ith_eq, s.property i gp.a <| partNum_eq_s_a s_ith_eq, Option.getD_some]
  _ = (-1) ^ (n + 1) := by rw [Finset.prod_const, Finset.card_range]

end SimpContFract

