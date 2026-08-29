/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monovary
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-!
# Chebyshev's sum inequality

This file proves the Chebyshev sum inequality.

Chebyshev's inequality states `(∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ #s * ∑ i ∈ s, f i * g i`
when `f g : ι → α` monovary, and the reverse inequality when `f` and `g` antivary.


## Main declarations

* `MonovaryOn.sum_mul_sum_le_card_mul_sum`: Chebyshev's inequality.
* `AntivaryOn.card_mul_sum_le_sum_mul_sum`: Chebyshev's inequality, dual version.
* `sq_sum_le_card_mul_sum_sq`: Special case of Chebyshev's inequality when `f = g`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `Monotone`/`Antitone` pairs of functions over a `LinearOrder` is not deduced in this
file because it is easily deducible from the `Monovary` API.
-/

public section


open Equiv Equiv.Perm Finset Function OrderDual

variable {ι α β : Type*}

/-! ### Scalar multiplication versions -/


section SMul
variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι -> α} {g : ι -> β}

/--
theorem `MonovaryOn.sum_smul_sum_le_card_smul_sum` / 定理 `MonovaryOn.sum_smul_sum_le_card_smul_sum`

English:
theorem MonovaryOn.sum_smul_sum_le_card_smul_sum
  given: (hfg : MonovaryOn f g s)
  proof: by
  obtain ⟨σ, hσ, hs⟩ := s.countable_toSet.exists_cycleOn
  rw [← card_range #s]; rw [sum_smul_sum_eq_sum_perm hσ]
  exact sum_le_card_nsmul _ _ _ fun n _ =>
hfg.sum_smul_comp_perm_le_sum_smul fun x hx => hs fun h => hx IsFixedPt.perm_pow h _

中文:
定理 MonovaryOn.sum_smul_sum_le_card_smul_sum
  条件: (hfg : MonovaryOn f g s)
  证明: by
  obtain ⟨σ, hσ, hs⟩ := s.countable_toSet.exists_cycleOn
  rw [← card_range #s]; rw [sum_smul_sum_eq_sum_perm hσ]
  exact sum_le_card_nsmul _ _ _ fun n _ =>
hfg.sum_smul_comp_perm_le_sum_smul fun x hx => hs fun h => hx IsFixedPt.perm_pow h _

Depends on / 依赖: IsFixedPt, IsFixedPt.perm_pow, card_range, countable_toSet, exists_cycleOn, hfg.sum_smul_comp_perm_le_sum_smul, perm_pow, s.countable_toSet.exists_cycleOn, sum_le_card_nsmul, sum_smul_comp_perm_le_sum_smul, sum_smul_sum_eq_sum_perm
-/
theorem MonovaryOn.sum_smul_sum_le_card_smul_sum (hfg : MonovaryOn f g s) :
    (∑ i in s, f i) • ∑ i in s, g i <= #s • ∑ i in s, f i • g i := by
  obtain ⟨σ, hσ, hs⟩ := s.countable_toSet.exists_cycleOn
  rw [← card_range #s]; rw [sum_smul_sum_eq_sum_perm hσ]
  exact sum_le_card_nsmul _ _ _ fun n _ =>
hfg.sum_smul_comp_perm_le_sum_smul fun x hx => hs fun h => hx IsFixedPt.perm_pow h _

/--
theorem `AntivaryOn.card_smul_sum_le_sum_smul_sum` / 定理 `AntivaryOn.card_smul_sum_le_sum_smul_sum`

English:
theorem AntivaryOn.card_smul_sum_le_sum_smul_sum
  given: (hfg : AntivaryOn f g s)
  proof: hfg.dual_right.sum_smul_sum_le_card_smul_sum

中文:
定理 AntivaryOn.card_smul_sum_le_sum_smul_sum
  条件: (hfg : AntivaryOn f g s)
  证明: hfg.dual_right.sum_smul_sum_le_card_smul_sum

Depends on / 依赖: dual_right, hfg.dual_right.sum_smul_sum_le_card_smul_sum, sum_smul_sum_le_card_smul_sum
-/
theorem AntivaryOn.card_smul_sum_le_sum_smul_sum (hfg : AntivaryOn f g s) :
    #s • ∑ i in s, f i • g i <= (∑ i in s, f i) • ∑ i in s, g i :=
  hfg.dual_right.sum_smul_sum_le_card_smul_sum

variable [Fintype ι]

/--
theorem `Monovary.sum_smul_sum_le_card_smul_sum` / 定理 `Monovary.sum_smul_sum_le_card_smul_sum`

English:
theorem Monovary.sum_smul_sum_le_card_smul_sum
  given: (hfg : Monovary f g)
  proof: (hfg.monovaryOn _).sum_smul_sum_le_card_smul_sum

中文:
定理 Monovary.sum_smul_sum_le_card_smul_sum
  条件: (hfg : Monovary f g)
  证明: (hfg.monovaryOn _).sum_smul_sum_le_card_smul_sum

Depends on / 依赖: hfg.monovaryOn, monovaryOn, sum_smul_sum_le_card_smul_sum
-/
theorem Monovary.sum_smul_sum_le_card_smul_sum (hfg : Monovary f g) :
    (∑ i, f i) • ∑ i, g i <= Fintype.card ι • ∑ i, f i • g i :=
  (hfg.monovaryOn _).sum_smul_sum_le_card_smul_sum

/--
theorem `Antivary.card_smul_sum_le_sum_smul_sum` / 定理 `Antivary.card_smul_sum_le_sum_smul_sum`

English:
theorem Antivary.card_smul_sum_le_sum_smul_sum
  given: (hfg : Antivary f g)
  proof: (hfg.dual_right.monovaryOn _).sum_smul_sum_le_card_smul_sum

中文:
定理 Antivary.card_smul_sum_le_sum_smul_sum
  条件: (hfg : Antivary f g)
  证明: (hfg.dual_right.monovaryOn _).sum_smul_sum_le_card_smul_sum

Depends on / 依赖: dual_right, hfg.dual_right.monovaryOn, monovaryOn, sum_smul_sum_le_card_smul_sum
-/
theorem Antivary.card_smul_sum_le_sum_smul_sum (hfg : Antivary f g) :
    Fintype.card ι • ∑ i, f i • g i <= (∑ i, f i) • ∑ i, g i :=
  (hfg.dual_right.monovaryOn _).sum_smul_sum_le_card_smul_sum

end SMul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/


section Mul
variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {σ : Perm ι} {f g : ι -> α}

/--
theorem `MonovaryOn.sum_mul_sum_le_card_mul_sum` / 定理 `MonovaryOn.sum_mul_sum_le_card_mul_sum`

English:
theorem MonovaryOn.sum_mul_sum_le_card_mul_sum
  given: (hfg : MonovaryOn f g s)
  proof: by
  rw [← nsmul_eq_mul]
  exact hfg.sum_smul_sum_le_card_smul_sum

中文:
定理 MonovaryOn.sum_mul_sum_le_card_mul_sum
  条件: (hfg : MonovaryOn f g s)
  证明: by
  rw [← nsmul_eq_mul]
  exact hfg.sum_smul_sum_le_card_smul_sum

Depends on / 依赖: hfg.sum_smul_sum_le_card_smul_sum, nsmul_eq_mul, sum_smul_sum_le_card_smul_sum
-/
theorem MonovaryOn.sum_mul_sum_le_card_mul_sum (hfg : MonovaryOn f g s) :
    (∑ i in s, f i) * ∑ i in s, g i <= #s * ∑ i in s, f i * g i := by
  rw [← nsmul_eq_mul]
  exact hfg.sum_smul_sum_le_card_smul_sum

/--
theorem `AntivaryOn.card_mul_sum_le_sum_mul_sum` / 定理 `AntivaryOn.card_mul_sum_le_sum_mul_sum`

English:
theorem AntivaryOn.card_mul_sum_le_sum_mul_sum
  given: (hfg : AntivaryOn f g s)
  proof: by
  rw [← nsmul_eq_mul]
  exact hfg.card_smul_sum_le_sum_smul_sum

中文:
定理 AntivaryOn.card_mul_sum_le_sum_mul_sum
  条件: (hfg : AntivaryOn f g s)
  证明: by
  rw [← nsmul_eq_mul]
  exact hfg.card_smul_sum_le_sum_smul_sum

Depends on / 依赖: card_smul_sum_le_sum_smul_sum, hfg.card_smul_sum_le_sum_smul_sum, nsmul_eq_mul
-/
theorem AntivaryOn.card_mul_sum_le_sum_mul_sum (hfg : AntivaryOn f g s) :
    (#s : α) * ∑ i in s, f i * g i <= (∑ i in s, f i) * ∑ i in s, g i := by
  rw [← nsmul_eq_mul]
  exact hfg.card_smul_sum_le_sum_smul_sum

/--
lemma `pow_sum_le_card_mul_sum_pow` / 引理 `pow_sum_le_card_mul_sum_pow`

English:
lemma pow_sum_le_card_mul_sum_pow
  given: (hf : forall i in s, 0 <= f i)
  proof: by rw [pow_succ]
      _ <= (#s ^ n * ∑ i in s, f i ^ (n + 1)) * ∑ i in s, f i := by
        gcongr
        exacts [sum_nonneg hf, pow_sum_le_card_mul_sum_pow hf _]
      _ = #s ^ n * ((∑ i in s, f i ^ (n + 1)) * ∑ i in s, f i) := by rw [mul_assoc]
      _ <= #s ^ n * (#s * ∑ i in s, f i ^ (n + 1) *

中文:
引理 pow_sum_le_card_mul_sum_pow
  条件: (hf : 对任意 i in s, 0 <= f i)
  证明: by rw [pow_succ]
      _ <= (#s ^ n * ∑ i in s, f i ^ (n + 1)) * ∑ i in s, f i := by
        gcongr
        exacts [sum_nonneg hf, pow_sum_le_card_mul_sum_pow hf _]
      _ = #s ^ n * ((∑ i in s, f i ^ (n + 1)) * ∑ i in s, f i) := by rw [mul_assoc]
      _ <= #s ^ n * (#s * ∑ i in s, f i ^ (n + 1) *

Depends on / 依赖: exacts, monovaryOn_self, mul_assoc, pow_succ, pow_sum_le_card_mul_sum_pow, simp_rw, sum_mul_sum_le_card_mul_sum, sum_nonneg
-/
lemma pow_sum_le_card_mul_sum_pow (hf : forall i in s, 0 <= f i) :
    forall n, (∑ i in s, f i) ^ (n + 1) <= (#s : α) ^ n * ∑ i in s, f i ^ (n + 1)
  | 0 => by simp
  | n + 1 =>
    calc
      _ = (∑ i in s, f i) ^ (n + 1) * ∑ i in s, f i := by rw [pow_succ]
      _ <= (#s ^ n * ∑ i in s, f i ^ (n + 1)) * ∑ i in s, f i := by
        gcongr
        exacts [sum_nonneg hf, pow_sum_le_card_mul_sum_pow hf _]
      _ = #s ^ n * ((∑ i in s, f i ^ (n + 1)) * ∑ i in s, f i) := by rw [mul_assoc]
      _ <= #s ^ n * (#s * ∑ i in s, f i ^ (n + 1) * f i) := by
        gcongr _ * ?_
        exact ((monovaryOn_self ..).pow_left₀ hf _).sum_mul_sum_le_card_mul_sum
      _ = _ := by simp_rw [← mul_assoc, ← pow_succ]

/--
theorem `sq_sum_le_card_mul_sum_sq` / 定理 `sq_sum_le_card_mul_sum_sq`

English:
theorem sq_sum_le_card_mul_sum_sq
  statement: (∑ i in s, f i) ^ 2 <= #s * ∑ i in s, f i ^ 2
  proof: by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum

中文:
定理 sq_sum_le_card_mul_sum_sq
  结论: (∑ i in s, f i) ^ 2 <= #s * ∑ i in s, f i ^ 2
  证明: by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum

Depends on / 依赖: monovaryOn_self, simp_rw, sum_mul_sum_le_card_mul_sum
-/
theorem sq_sum_le_card_mul_sum_sq : (∑ i in s, f i) ^ 2 <= #s * ∑ i in s, f i ^ 2 := by
  simp_rw [sq]
  exact (monovaryOn_self _ _).sum_mul_sum_le_card_mul_sum

variable [Fintype ι]

/--
theorem `Monovary.sum_mul_sum_le_card_mul_sum` / 定理 `Monovary.sum_mul_sum_le_card_mul_sum`

English:
theorem Monovary.sum_mul_sum_le_card_mul_sum
  given: (hfg : Monovary f g)
  proof: (hfg.monovaryOn _).sum_mul_sum_le_card_mul_sum

中文:
定理 Monovary.sum_mul_sum_le_card_mul_sum
  条件: (hfg : Monovary f g)
  证明: (hfg.monovaryOn _).sum_mul_sum_le_card_mul_sum

Depends on / 依赖: hfg.monovaryOn, monovaryOn, sum_mul_sum_le_card_mul_sum
-/
theorem Monovary.sum_mul_sum_le_card_mul_sum (hfg : Monovary f g) :
    (∑ i, f i) * ∑ i, g i <= Fintype.card ι * ∑ i, f i * g i :=
  (hfg.monovaryOn _).sum_mul_sum_le_card_mul_sum

/--
theorem `Antivary.card_mul_sum_le_sum_mul_sum` / 定理 `Antivary.card_mul_sum_le_sum_mul_sum`

English:
theorem Antivary.card_mul_sum_le_sum_mul_sum
  given: (hfg : Antivary f g)
  proof: (hfg.antivaryOn _).card_mul_sum_le_sum_mul_sum

中文:
定理 Antivary.card_mul_sum_le_sum_mul_sum
  条件: (hfg : Antivary f g)
  证明: (hfg.antivaryOn _).card_mul_sum_le_sum_mul_sum

Depends on / 依赖: antivaryOn, card_mul_sum_le_sum_mul_sum, hfg.antivaryOn
-/
theorem Antivary.card_mul_sum_le_sum_mul_sum (hfg : Antivary f g) :
    Fintype.card ι * ∑ i, f i * g i <= (∑ i, f i) * ∑ i, g i :=
  (hfg.antivaryOn _).card_mul_sum_le_sum_mul_sum

end Mul

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  {s : Finset ι} {f : ι -> α}

/--
lemma `pow_sum_div_card_le_sum_pow` / 引理 `pow_sum_div_card_le_sum_pow`

English:
lemma pow_sum_div_card_le_sum_pow
  given: (hf : forall i in s, 0 <= f i) (n : Nat)
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_le_iff₀' (by positivity)]
  exact pow_sum_le_card_mul_sum_pow hf _

中文:
引理 pow_sum_div_card_le_sum_pow
  条件: (hf : 对任意 i in s, 0 <= f i) (n : 自然数)
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_le_iff₀' (by positivity)]
  exact pow_sum_le_card_mul_sum_pow hf _

Depends on / 依赖: eq_empty_or_nonempty, pow_sum_le_card_mul_sum_pow, s.eq_empty_or_nonempty
-/
lemma pow_sum_div_card_le_sum_pow (hf : forall i in s, 0 <= f i) (n : Nat) :
    (∑ i in s, f i) ^ (n + 1) / #s ^ n <= ∑ i in s, f i ^ (n + 1) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_le_iff₀' (by positivity)]
  exact pow_sum_le_card_mul_sum_pow hf _

/--
theorem `sum_div_card_sq_le_sum_sq_div_card` / 定理 `sum_div_card_sq_le_sum_sq_div_card`

English:
theorem sum_div_card_sq_le_sum_sq_div_card
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_pow]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; rw [sq (#s : α)]; rw [mul_left_comm]; rw [← mul_assoc]
  gcongr
  exact sq_sum_le_card_mul_sum_sq

中文:
定理 sum_div_card_sq_le_sum_sq_div_card
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_pow]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; rw [sq (#s : α)]; rw [mul_left_comm]; rw [← mul_assoc]
  gcongr
  exact sq_sum_le_card_mul_sum_sq

Depends on / 依赖: div_pow, eq_empty_or_nonempty, mul_assoc, mul_left_comm, s.eq_empty_or_nonempty, sq_sum_le_card_mul_sum_sq
-/
theorem sum_div_card_sq_le_sum_sq_div_card :
    ((∑ i in s, f i) / #s) ^ 2 <= (∑ i in s, f i ^ 2) / #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [div_pow]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; rw [sq (#s : α)]; rw [mul_left_comm]; rw [← mul_assoc]
  gcongr
  exact sq_sum_le_card_mul_sum_sq
