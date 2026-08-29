/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Infinite sum in a ring

This file provides lemmas about the interaction between infinite sums and multiplication.

## Main results

* `tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Cauchy product formula
* `Summable.tsum_pow_mul_one_sub`, `Summable.one_sub_mul_tsum_pow`: geometric series formula.
* `tprod_one_add`: expanding `∏' i : ι, (1 + f i)` as infinite sum.
-/

public section

open Filter Finset Function

variable {ι κ α : Type*} {L : SummationFilter ι}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α] {f : ι -> α}
  {a₁ : α}

/--
theorem `HasSum.mul_left` / 定理 `HasSum.mul_left`

English:
theorem HasSum.mul_left
  given: (a₂) (h : HasSum f a₁ L)
  statement: HasSum (fun i => a₂ * f i) (a₂ * a₁) L
  proof: by
  simpa only using! h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)

中文:
定理 HasSum.mul_left
  条件: (a₂) (h : HasSum f a₁ L)
  结论: HasSum (fun i => a₂ * f i) (a₂ * a₁) L
  证明: by
  simpa only using! h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, continuous_const, continuous_const.mul, continuous_id, h.map, mulLeft
-/
theorem HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun i => a₂ * f i) (a₂ * a₁) L := by
  simpa only using! h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)

/--
theorem `HasSum.mul_right` / 定理 `HasSum.mul_right`

English:
theorem HasSum.mul_right
  given: (a₂) (hf : HasSum f a₁ L)
  statement: HasSum (fun i => f i * a₂) (a₁ * a₂) L
  proof: by
  simpa only using! hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)

中文:
定理 HasSum.mul_right
  条件: (a₂) (hf : HasSum f a₁ L)
  结论: HasSum (fun i => f i * a₂) (a₁ * a₂) L
  证明: by
  simpa only using! hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulRight, continuous_const, continuous_id, continuous_id.mul, hf.map, mulRight
-/
theorem HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (fun i => f i * a₂) (a₁ * a₂) L := by
  simpa only using! hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)

/--
theorem `Summable.mul_left` / 定理 `Summable.mul_left`

English:
theorem Summable.mul_left
  given: (a) (hf : Summable f L)
  statement: Summable (fun i => a * f i) L
  proof: (hf.hasSum.mul_left _).summable

中文:
定理 Summable.mul_left
  条件: (a) (hf : Summable f L)
  结论: Summable (fun i => a * f i) L
  证明: (hf.hasSum.mul_left _).summable

Depends on / 依赖: hasSum, hf.hasSum.mul_left, mul_left, summable
-/
theorem Summable.mul_left (a) (hf : Summable f L) : Summable (fun i => a * f i) L :=
  (hf.hasSum.mul_left _).summable

/--
theorem `Summable.mul_right` / 定理 `Summable.mul_right`

English:
theorem Summable.mul_right
  given: (a) (hf : Summable f L)
  statement: Summable (fun i => f i * a) L
  proof: (hf.hasSum.mul_right _).summable

中文:
定理 Summable.mul_right
  条件: (a) (hf : Summable f L)
  结论: Summable (fun i => f i * a) L
  证明: (hf.hasSum.mul_right _).summable

Depends on / 依赖: hasSum, hf.hasSum.mul_right, mul_right, summable
-/
theorem Summable.mul_right (a) (hf : Summable f L) : Summable (fun i => f i * a) L :=
  (hf.hasSum.mul_right _).summable

section tsum

variable [T2Space α] [L.NeBot]

/--
theorem `Summable.tsum_mul_left` / 定理 `Summable.tsum_mul_left`

English:
theorem Summable.tsum_mul_left
  given: (a) (hf : Summable f L)
  proof: (hf.hasSum.mul_left _).tsum_eq

中文:
定理 Summable.tsum_mul_left
  条件: (a) (hf : Summable f L)
  证明: (hf.hasSum.mul_left _).tsum_eq
-/
protected theorem Summable.tsum_mul_left (a) (hf : Summable f L) :
      ∑'[L] i, a * f i = a * ∑'[L] i, f i :=
  (hf.hasSum.mul_left _).tsum_eq

/--
theorem `Summable.tsum_mul_right` / 定理 `Summable.tsum_mul_right`

English:
theorem Summable.tsum_mul_right
  given: (a) (hf : Summable f L)
  proof: (hf.hasSum.mul_right _).tsum_eq

中文:
定理 Summable.tsum_mul_right
  条件: (a) (hf : Summable f L)
  证明: (hf.hasSum.mul_right _).tsum_eq
-/
protected theorem Summable.tsum_mul_right (a) (hf : Summable f L) :
    ∑'[L] i, f i * a = (∑'[L] i, f i) * a :=
  (hf.hasSum.mul_right _).tsum_eq

/--
theorem `SemiconjBy.tsum_left` / 定理 `SemiconjBy.tsum_left`

English:
theorem SemiconjBy.tsum_left
  given: {a b : α} (h : forall (i : ι), SemiconjBy (f i) a b)
  proof: by
  by_cases hf : Summable f L
  · rw [SemiconjBy, ← hf.tsum_mul_right a, ← hf.tsum_mul_left b, tsum_congr h]
  · simp [tsum_eq_zero_of_not_summable hf]

中文:
定理 SemiconjBy.tsum_left
  条件: {a b : α} (h : 对任意 (i : ι), SemiconjBy (f i) a b)
  证明: by
  by_cases hf : Summable f L
  · rw [SemiconjBy, ← hf.tsum_mul_right a, ← hf.tsum_mul_left b, tsum_congr h]
  · simp [tsum_eq_zero_of_not_summable hf]

Depends on / 依赖: SemiconjBy, Summable, hf.tsum_mul_left, hf.tsum_mul_right, tsum_congr, tsum_eq_zero_of_not_summable, tsum_mul_left, tsum_mul_right
-/
theorem SemiconjBy.tsum_left {a b : α} (h : forall (i : ι), SemiconjBy (f i) a b) :
    SemiconjBy (∑'[L] (i : ι), f i) a b := by
  by_cases hf : Summable f L
  · rw [SemiconjBy, ← hf.tsum_mul_right a, ← hf.tsum_mul_left b, tsum_congr h]
  · simp [tsum_eq_zero_of_not_summable hf]

/--
theorem `SemiconjBy.tsum_right` / 定理 `SemiconjBy.tsum_right`

English:
theorem SemiconjBy.tsum_right
  statement: {f g : ι -> α} (a : α) (hf : Summable f L) (hg : Summable g L)
  proof: by
  rw [SemiconjBy]; rw [← hf.tsum_mul_left a]; rw [← hg.tsum_mul_right a]
  exact tsum_congr h

中文:
定理 SemiconjBy.tsum_right
  结论: {f g : ι -> α} (a : α) (hf : Summable f L) (hg : Summable g L)
  证明: by
  rw [SemiconjBy]; rw [← hf.tsum_mul_left a]; rw [← hg.tsum_mul_right a]
  exact tsum_congr h

Depends on / 依赖: SemiconjBy, hf.tsum_mul_left, hg.tsum_mul_right, tsum_congr, tsum_mul_left, tsum_mul_right
-/
theorem SemiconjBy.tsum_right {f g : ι -> α} (a : α) (hf : Summable f L) (hg : Summable g L)
    (h : forall (i : ι), SemiconjBy a (f i) (g i)) :
    SemiconjBy a (∑'[L] (i : ι), f i) (∑'[L] (i : ι), g i) := by
  rw [SemiconjBy]; rw [← hf.tsum_mul_left a]; rw [← hg.tsum_mul_right a]
  exact tsum_congr h

/--
theorem `Commute.tsum_left` / 定理 `Commute.tsum_left`

English:
theorem Commute.tsum_left
  given: (a) (h : forall i, Commute (f i) a)
  statement: Commute (∑'[L] i, f i) a
  proof: SemiconjBy.tsum_left h

中文:
定理 Commute.tsum_left
  条件: (a) (h : 对任意 i, Commute (f i) a)
  结论: Commute (∑'[L] i, f i) a
  证明: SemiconjBy.tsum_left h

Depends on / 依赖: SemiconjBy, SemiconjBy.tsum_left, tsum_left
-/
theorem Commute.tsum_left (a) (h : forall i, Commute (f i) a) : Commute (∑'[L] i, f i) a :=
  SemiconjBy.tsum_left h

/--
theorem `Commute.tsum_right` / 定理 `Commute.tsum_right`

English:
theorem Commute.tsum_right
  given: (a) (h : forall i, Commute a (f i))
  statement: Commute a (∑'[L] i, f i)
  proof: (Commute.tsum_left _ fun i => (h i).symm).symm

中文:
定理 Commute.tsum_right
  条件: (a) (h : 对任意 i, Commute a (f i))
  结论: Commute a (∑'[L] i, f i)
  证明: (Commute.tsum_left _ fun i => (h i).symm).symm

Depends on / 依赖: Commute, Commute.tsum_left, tsum_left
-/
theorem Commute.tsum_right (a) (h : forall i, Commute a (f i)) : Commute a (∑'[L] i, f i) :=
  (Commute.tsum_left _ fun i => (h i).symm).symm

end tsum

end NonUnitalNonAssocSemiring

section DivisionSemiring

variable [DivisionSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α]
    {f : ι -> α} {a a₁ a₂ : α}

/--
theorem `HasSum.div_const` / 定理 `HasSum.div_const`

English:
theorem HasSum.div_const
  given: (h : HasSum f a L) (b : α)
  statement: HasSum (fun i => f i / b) (a / b) L
  proof: by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]

中文:
定理 HasSum.div_const
  条件: (h : HasSum f a L) (b : α)
  结论: HasSum (fun i => f i / b) (a / b) L
  证明: by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]

Depends on / 依赖: div_eq_mul_inv, h.mul_right, mul_right
-/
theorem HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (fun i => f i / b) (a / b) L := by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]

/--
theorem `Summable.div_const` / 定理 `Summable.div_const`

English:
theorem Summable.div_const
  given: (h : Summable f L) (b : α)
  statement: Summable (fun i => f i / b) L
  proof: (h.hasSum.div_const _).summable

中文:
定理 Summable.div_const
  条件: (h : Summable f L) (b : α)
  结论: Summable (fun i => f i / b) L
  证明: (h.hasSum.div_const _).summable

Depends on / 依赖: div_const, h.hasSum.div_const, hasSum, summable
-/
theorem Summable.div_const (h : Summable f L) (b : α) : Summable (fun i => f i / b) L :=
  (h.hasSum.div_const _).summable

/--
theorem `hasSum_mul_left_iff` / 定理 `hasSum_mul_left_iff`

English:
theorem hasSum_mul_left_iff
  given: (h : a₂ != 0)
  statement: HasSum (fun i => a₂ * f i) (a₂ * a₁) L ↔ HasSum f a₁ L
  proof: ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, HasSum.mul_left _⟩

中文:
定理 hasSum_mul_left_iff
  条件: (h : a₂ != 0)
  结论: HasSum (fun i => a₂ * f i) (a₂ * a₁) L ↔ HasSum f a₁ L
  证明: ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, HasSum.mul_left _⟩

Depends on / 依赖: H.mul_left, HasSum, HasSum.mul_left, mul_left
-/
theorem hasSum_mul_left_iff (h : a₂ != 0) : HasSum (fun i => a₂ * f i) (a₂ * a₁) L ↔ HasSum f a₁ L :=
  ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, HasSum.mul_left _⟩

/--
theorem `hasSum_mul_right_iff` / 定理 `hasSum_mul_right_iff`

English:
theorem hasSum_mul_right_iff
  given: (h : a₂ != 0)
  statement: HasSum (fun i => f i * a₂) (a₁ * a₂) L ↔ HasSum f a₁ L
  proof: ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, HasSum.mul_right _⟩

中文:
定理 hasSum_mul_right_iff
  条件: (h : a₂ != 0)
  结论: HasSum (fun i => f i * a₂) (a₁ * a₂) L ↔ HasSum f a₁ L
  证明: ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, HasSum.mul_right _⟩

Depends on / 依赖: H.mul_right, HasSum, HasSum.mul_right, mul_right
-/
theorem hasSum_mul_right_iff (h : a₂ != 0) : HasSum (fun i => f i * a₂) (a₁ * a₂) L ↔ HasSum f a₁ L :=
  ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, HasSum.mul_right _⟩

/--
theorem `hasSum_div_const_iff` / 定理 `hasSum_div_const_iff`

English:
theorem hasSum_div_const_iff
  given: (h : a₂ != 0)
  proof: by
  simpa only [div_eq_mul_inv] using hasSum_mul_right_iff (inv_ne_zero h)

中文:
定理 hasSum_div_const_iff
  条件: (h : a₂ != 0)
  证明: by
  simpa only [div_eq_mul_inv] using hasSum_mul_right_iff (inv_ne_zero h)

Depends on / 依赖: div_eq_mul_inv, hasSum_mul_right_iff, inv_ne_zero
-/
theorem hasSum_div_const_iff (h : a₂ != 0) :
    HasSum (fun i => f i / a₂) (a₁ / a₂) L ↔ HasSum f a₁ L := by
  simpa only [div_eq_mul_inv] using hasSum_mul_right_iff (inv_ne_zero h)

/--
theorem `summable_mul_left_iff` / 定理 `summable_mul_left_iff`

English:
theorem summable_mul_left_iff
  given: (h : a != 0)
  statement: (Summable (fun i => a * f i) L) ↔ Summable f L
  proof: ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, fun H => H.mul_left _⟩

中文:
定理 summable_mul_left_iff
  条件: (h : a != 0)
  结论: (Summable (fun i => a * f i) L) ↔ Summable f L
  证明: ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, fun H => H.mul_left _⟩

Depends on / 依赖: H.mul_left, mul_left
-/
theorem summable_mul_left_iff (h : a != 0) : (Summable (fun i => a * f i) L) ↔ Summable f L :=
  ⟨fun H => by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, fun H => H.mul_left _⟩

/--
theorem `summable_mul_right_iff` / 定理 `summable_mul_right_iff`

English:
theorem summable_mul_right_iff
  given: (h : a != 0)
  statement: (Summable (fun i => f i * a) L) ↔ Summable f L
  proof: ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, fun H => H.mul_right _⟩

中文:
定理 summable_mul_right_iff
  条件: (h : a != 0)
  结论: (Summable (fun i => f i * a) L) ↔ Summable f L
  证明: ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, fun H => H.mul_right _⟩

Depends on / 依赖: H.mul_right, mul_right
-/
theorem summable_mul_right_iff (h : a != 0) : (Summable (fun i => f i * a) L) ↔ Summable f L :=
  ⟨fun H => by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, fun H => H.mul_right _⟩

/--
theorem `summable_div_const_iff` / 定理 `summable_div_const_iff`

English:
theorem summable_div_const_iff
  given: (h : a != 0)
  statement: (Summable (fun i => f i / a) L) ↔ Summable f L
  proof: by
  simpa only [div_eq_mul_inv] using summable_mul_right_iff (inv_ne_zero h)

中文:
定理 summable_div_const_iff
  条件: (h : a != 0)
  结论: (Summable (fun i => f i / a) L) ↔ Summable f L
  证明: by
  simpa only [div_eq_mul_inv] using summable_mul_right_iff (inv_ne_zero h)

Depends on / 依赖: div_eq_mul_inv, inv_ne_zero, summable_mul_right_iff
-/
theorem summable_div_const_iff (h : a != 0) : (Summable (fun i => f i / a) L) ↔ Summable f L := by
  simpa only [div_eq_mul_inv] using summable_mul_right_iff (inv_ne_zero h)

/--
theorem `tsum_mul_left` / 定理 `tsum_mul_left`

English:
theorem tsum_mul_left
  given: [T2Space α]
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulLeft₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulLeft a)).symm

中文:
定理 tsum_mul_left
  条件: [T2Space α]
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulLeft₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulLeft a)).symm

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, Homeomorph, Homeomorph.mulLeft, isClosedEmbedding, isClosedEmbedding.map_tsum, map_tsum, mulLeft
-/
theorem tsum_mul_left [T2Space α] :
    ∑'[L] x, a * f x = a * ∑'[L] x, f x := by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulLeft₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulLeft a)).symm

/--
theorem `tsum_mul_right` / 定理 `tsum_mul_right`

English:
theorem tsum_mul_right
  given: [T2Space α]
  statement: ∑'[L] x, f x * a = (∑'[L] x, f x) * a
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulRight₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulRight a)).symm

中文:
定理 tsum_mul_right
  条件: [T2Space α]
  结论: ∑'[L] x, f x * a = (∑'[L] x, f x) * a
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulRight₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulRight a)).symm

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulRight, Homeomorph, Homeomorph.mulRight, isClosedEmbedding, isClosedEmbedding.map_tsum, map_tsum, mulRight
-/
theorem tsum_mul_right [T2Space α] : ∑'[L] x, f x * a = (∑'[L] x, f x) * a := by
  by_cases ha : a = 0
  · simp [ha]
  · exact ((Homeomorph.mulRight₀ a ha).isClosedEmbedding.map_tsum f
      (g := AddMonoidHom.mulRight a)).symm

/--
theorem `tsum_div_const` / 定理 `tsum_div_const`

English:
theorem tsum_div_const
  given: [T2Space α]
  statement: ∑'[L] x, f x / a = (∑'[L] x, f x) / a
  proof: by
  simpa only [div_eq_mul_inv] using tsum_mul_right

中文:
定理 tsum_div_const
  条件: [T2Space α]
  结论: ∑'[L] x, f x / a = (∑'[L] x, f x) / a
  证明: by
  simpa only [div_eq_mul_inv] using tsum_mul_right

Depends on / 依赖: div_eq_mul_inv, tsum_mul_right
-/
theorem tsum_div_const [T2Space α] : ∑'[L] x, f x / a = (∑'[L] x, f x) / a := by
  simpa only [div_eq_mul_inv] using tsum_mul_right

/--
theorem `HasSum.const_div` / 定理 `HasSum.const_div`

English:
theorem HasSum.const_div
  given: (h : HasSum (fun x => 1 / f x) a L) (b : α)
  proof: by
  have := h.mul_left b
  simpa only [div_eq_mul_inv, one_mul] using this

中文:
定理 HasSum.const_div
  条件: (h : HasSum (fun x => 1 / f x) a L) (b : α)
  证明: by
  have := h.mul_left b
  simpa only [div_eq_mul_inv, one_mul] using this

Depends on / 依赖: div_eq_mul_inv, h.mul_left, mul_left, one_mul
-/
theorem HasSum.const_div (h : HasSum (fun x => 1 / f x) a L) (b : α) :
    HasSum (fun i => b / f i) (b * a) L := by
  have := h.mul_left b
  simpa only [div_eq_mul_inv, one_mul] using this

/--
theorem `Summable.const_div` / 定理 `Summable.const_div`

English:
theorem Summable.const_div
  given: (h : Summable (fun x => 1 / f x) L) (b : α)
  proof: (h.hasSum.const_div b).summable

中文:
定理 Summable.const_div
  条件: (h : Summable (fun x => 1 / f x) L) (b : α)
  证明: (h.hasSum.const_div b).summable

Depends on / 依赖: const_div, h.hasSum.const_div, hasSum, summable
-/
theorem Summable.const_div (h : Summable (fun x => 1 / f x) L) (b : α) :
    Summable (fun i => b / f i) L :=
  (h.hasSum.const_div b).summable

/--
theorem `hasSum_const_div_iff` / 定理 `hasSum_const_div_iff`

English:
theorem hasSum_const_div_iff
  given: (h : a₂ != 0)
  proof: by
  simpa only [div_eq_mul_inv, one_mul] using! hasSum_mul_left_iff h

中文:
定理 hasSum_const_div_iff
  条件: (h : a₂ != 0)
  证明: by
  simpa only [div_eq_mul_inv, one_mul] using! hasSum_mul_left_iff h

Depends on / 依赖: div_eq_mul_inv, hasSum_mul_left_iff, one_mul
-/
theorem hasSum_const_div_iff (h : a₂ != 0) :
    HasSum (fun i => a₂ / f i) (a₂ * a₁) L ↔ HasSum (1 / f) a₁ L := by
  simpa only [div_eq_mul_inv, one_mul] using! hasSum_mul_left_iff h

/--
theorem `summable_const_div_iff` / 定理 `summable_const_div_iff`

English:
theorem summable_const_div_iff
  given: (h : a != 0)
  proof: by
  simpa only [div_eq_mul_inv, one_mul] using! summable_mul_left_iff h

中文:
定理 summable_const_div_iff
  条件: (h : a != 0)
  证明: by
  simpa only [div_eq_mul_inv, one_mul] using! summable_mul_left_iff h

Depends on / 依赖: div_eq_mul_inv, one_mul, summable_mul_left_iff
-/
theorem summable_const_div_iff (h : a != 0) :
    (Summable (fun i => a / f i) L) ↔ Summable (1 / f) L := by
  simpa only [div_eq_mul_inv, one_mul] using! summable_mul_left_iff h

end DivisionSemiring

/-!
### Multiplying two infinite sums

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : κ, g y)`. Note that we
always assume that the family `fun x : ι × κ ↦ f x.1 * g x.2` is summable, since there is no way to
deduce this from the summabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `Analysis.Normed.Module.Basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `ι` and `κ`, and then we specialize to
`ι = κ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

#### Arbitrary index types
-/


section tsum_mul_tsum

variable [TopologicalSpace α] [T3Space α] [NonUnitalNonAssocSemiring α] [IsTopologicalSemiring α]
  {f : ι -> α} {g : κ -> α} {s t u : α}

/--
theorem `HasSum.mul_eq` / 定理 `HasSum.mul_eq`

English:
theorem HasSum.mul_eq
  statement: (hf : HasSum f s) (hg : HasSum g t)
  proof: have key₁ : HasSum (fun i => f i * t) (s * t) := hf.mul_right t
  have : forall i : ι, HasSum (fun c : κ => f i * g c) (f i * t) := fun i => hg.mul_left (f i)
  have key₂ : HasSum (fun i => f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

中文:
定理 HasSum.mul_eq
  结论: (hf : HasSum f s) (hg : HasSum g t)
  证明: have key₁ : HasSum (fun i => f i * t) (s * t) := hf.mul_right t
  have : forall i : ι, HasSum (fun c : κ => f i * g c) (f i * t) := fun i => hg.mul_left (f i)
  have key₂ : HasSum (fun i => f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

Depends on / 依赖: HasSum, HasSum.prod_fiberwise, hf.mul_right, hg.mul_left, mul_left, mul_right, prod_fiberwise, unique
-/
theorem HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ => f x.1 * g x.2) u) : s * t = u :=
  have key₁ : HasSum (fun i => f i * t) (s * t) := hf.mul_right t
  have : forall i : ι, HasSum (fun c : κ => f i * g c) (f i * t) := fun i => hg.mul_left (f i)
  have key₂ : HasSum (fun i => f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

/--
theorem `HasSum.mul` / 定理 `HasSum.mul`

English:
theorem HasSum.mul
  statement: (hf : HasSum f s) (hg : HasSum g t)
  proof: let ⟨_u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu

中文:
定理 HasSum.mul
  结论: (hf : HasSum f s) (hg : HasSum g t)
  证明: let ⟨_u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu

Depends on / 依赖: hf.mul_eq, mul_eq
-/
theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ => f x.1 * g x.2) :
    HasSum (fun x : ι × κ => f x.1 * g x.2) (s * t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu

/--
theorem `Summable.tsum_mul_tsum` / 定理 `Summable.tsum_mul_tsum`

English:
theorem Summable.tsum_mul_tsum
  statement: (hf : Summable f) (hg : Summable g)
  proof: hf.hasSum.mul_eq hg.hasSum hfg.hasSum

中文:
定理 Summable.tsum_mul_tsum
  结论: (hf : Summable f) (hg : Summable g)
  证明: hf.hasSum.mul_eq hg.hasSum hfg.hasSum
-/
protected theorem Summable.tsum_mul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ => f x.1 * g x.2) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × κ, f z.1 * g z.2 :=
  hf.hasSum.mul_eq hg.hasSum hfg.hasSum

end tsum_mul_tsum

/-!
#### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `Finset.range (n+1)`
involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.antidiagonal n`.
This in fact allows us to generalize to any type satisfying `[Finset.HasAntidiagonal A]`
-/


section CauchyProduct

section HasAntidiagonal
variable {A : Type*} [AddCommMonoid A] [HasAntidiagonal A]
variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : A -> α}

/--
theorem `summable_mul_prod_iff_summable_mul_sigma_antidiagonal` / 定理 `summable_mul_prod_iff_summable_mul_sigma_antidiagonal`

English:
theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal
  proof: Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.symm

中文:
定理 summable_mul_prod_iff_summable_mul_sigma_antidiagonal
  证明: Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.symm

Depends on / 依赖: Finset, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.symm, HasAntidiagonal, sigmaAntidiagonalEquivProd, summable_iff
-/
theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal :
    (Summable fun x : A × A => f x.1 * g x.2) ↔
      Summable fun x : Σ n : A, antidiagonal n => f (x.2 : A × A).1 * g (x.2 : A × A).2 :=
  Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.symm

variable [T3Space α] [IsTopologicalSemiring α]

/--
theorem `summable_sum_mul_antidiagonal_of_summable_mul` / 定理 `summable_sum_mul_antidiagonal_of_summable_mul`

English:
theorem summable_sum_mul_antidiagonal_of_summable_mul
  proof: by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact h.sigma' fun n => (hasSum_fintype _).summable

中文:
定理 summable_sum_mul_antidiagonal_of_summable_mul
  证明: by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact h.sigma' fun n => (hasSum_fintype _).summable

Depends on / 依赖: Finset, Finset.sum_finset_coe, h.sigma, hasSum_fintype, sum_finset_coe, summable, summable_mul_prod_iff_summable_mul_sigma_antidiagonal, tsum_fintype, unconditional
-/
theorem summable_sum_mul_antidiagonal_of_summable_mul
    (h : Summable fun x : A × A => f x.1 * g x.2) :
    Summable fun n => ∑ kl in antidiagonal n, f kl.1 * g kl.2 := by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  exact h.sigma' fun n => (hasSum_fintype _).summable

/--
theorem `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal` / 定理 `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`

English:
theorem Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
  statement: (hf : Summable f)
  proof: by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [hf.tsum_mul_tsum hg hfg]; rw [← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (_ : A × A -> α)]
  exact (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg).tsum_sigma'
    (fun n =

中文:
定理 Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
  结论: (hf : Summable f)
  证明: by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [hf.tsum_mul_tsum hg hfg]; rw [← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (_ : A × A -> α)]
  exact (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg).tsum_sigma'
    (fun n =
-/
protected theorem Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : Summable f)
    (hg : Summable g) (hfg : Summable fun x : A × A => f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
  rw [hf.tsum_mul_tsum hg hfg]; rw [← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (_ : A × A -> α)]
  exact (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg).tsum_sigma'
    (fun n => (hasSum_fintype _).summable)

end HasAntidiagonal

section Nat

variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : Nat -> α}
variable [T3Space α] [IsTopologicalSemiring α]

/--
theorem `summable_sum_mul_range_of_summable_mul` / 定理 `summable_sum_mul_range_of_summable_mul`

English:
theorem summable_sum_mul_range_of_summable_mul
  given: (h : Summable fun x : Nat × Nat => f x.1 * g x.2)
  proof: by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h

中文:
定理 summable_sum_mul_range_of_summable_mul
  条件: (h : Summable fun x : 自然数 × 自然数 => f x.1 * g x.2)
  证明: by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h

Depends on / 依赖: Nat.sum_antidiagonal_eq_sum_range_succ, simp_rw, sum_antidiagonal_eq_sum_range_succ, summable_sum_mul_antidiagonal_of_summable_mul
-/
theorem summable_sum_mul_range_of_summable_mul (h : Summable fun x : Nat × Nat => f x.1 * g x.2) :
    Summable fun n => ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h

/--
theorem `Summable.tsum_mul_tsum_eq_tsum_sum_range` / 定理 `Summable.tsum_mul_tsum_eq_tsum_sum_range`

English:
theorem Summable.tsum_mul_tsum_eq_tsum_sum_range
  statement: (hf : Summable f) (hg : Summable g)
  proof: by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg

中文:
定理 Summable.tsum_mul_tsum_eq_tsum_sum_range
  结论: (hf : Summable f) (hg : Summable g)
  证明: by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg
-/
protected theorem Summable.tsum_mul_tsum_eq_tsum_sum_range (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : Nat × Nat => f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg

end Nat

end CauchyProduct

section GeomSeries

/-!
### Geometric series `∑' n : ℕ, x ^ n`

This section gives a general result about geometric series without assuming additional structure on
the topological ring. For normed ring, see also `geom_series_mul_neg` and friends.
-/

variable [Ring α] [TopologicalSpace α] [IsTopologicalRing α] [T2Space α]

/--
theorem `Summable.tsum_pow_mul_one_sub` / 定理 `Summable.tsum_pow_mul_one_sub`

English:
theorem Summable.tsum_pow_mul_one_sub
  given: {x : α} (h : Summable (x ^ ·))
  proof: by
  refine tendsto_nhds_unique (h.hasSum.mul_right (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.sum_mul, geom_sum_mul_neg] using tendsto_const_nhds.sub h.tendsto_atTop_zero

中文:
定理 Summable.tsum_pow_mul_one_sub
  条件: {x : α} (h : Summable (x ^ ·))
  证明: by
  refine tendsto_nhds_unique (h.hasSum.mul_right (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.sum_mul, geom_sum_mul_neg] using tendsto_const_nhds.sub h.tendsto_atTop_zero

Depends on / 依赖: Finset, Finset.sum_mul, geom_sum_mul_neg, h.hasSum.mul_right, h.tendsto_atTop_zero, hasSum, mul_right, sum_mul, tendsto_atTop_zero, tendsto_const_nhds, tendsto_const_nhds.sub, tendsto_nhds_unique, tendsto_sum_nat
-/
theorem Summable.tsum_pow_mul_one_sub {x : α} (h : Summable (x ^ ·)) :
    (∑' (i : Nat), x ^ i) * (1 - x) = 1 := by
  refine tendsto_nhds_unique (h.hasSum.mul_right (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.sum_mul, geom_sum_mul_neg] using tendsto_const_nhds.sub h.tendsto_atTop_zero

/--
theorem `Summable.one_sub_mul_tsum_pow` / 定理 `Summable.one_sub_mul_tsum_pow`

English:
theorem Summable.one_sub_mul_tsum_pow
  given: {x : α} (h : Summable (x ^ ·))
  proof: by
  refine tendsto_nhds_unique (h.hasSum.mul_left (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.mul_sum, mul_neg_geom_sum] using tendsto_const_nhds.sub h.tendsto_atTop_zero

中文:
定理 Summable.one_sub_mul_tsum_pow
  条件: {x : α} (h : Summable (x ^ ·))
  证明: by
  refine tendsto_nhds_unique (h.hasSum.mul_left (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.mul_sum, mul_neg_geom_sum] using tendsto_const_nhds.sub h.tendsto_atTop_zero

Depends on / 依赖: Finset, Finset.mul_sum, h.hasSum.mul_left, h.tendsto_atTop_zero, hasSum, mul_left, mul_neg_geom_sum, mul_sum, tendsto_atTop_zero, tendsto_const_nhds, tendsto_const_nhds.sub, tendsto_nhds_unique, tendsto_sum_nat
-/
theorem Summable.one_sub_mul_tsum_pow {x : α} (h : Summable (x ^ ·)) :
    (1 - x) * ∑' (i : Nat), x ^ i = 1 := by
  refine tendsto_nhds_unique (h.hasSum.mul_left (1 - x)).tendsto_sum_nat ?_
  simpa [← Finset.mul_sum, mul_neg_geom_sum] using tendsto_const_nhds.sub h.tendsto_atTop_zero

end GeomSeries

section ProdOneSum

/-!
### Infinite product of `1 + f i`

This section extends `Finset.prod_one_add` to the infinite product
`∏' i : ι, (1 + f i) = ∑' s : Finset ι, ∏ i ∈ s, f i`.
-/

variable [CommSemiring α] [TopologicalSpace α] {f : ι -> α}

/--
theorem `hasProd_one_add_of_hasSum_prod` / 定理 `hasProd_one_add_of_hasSum_prod`

English:
theorem hasProd_one_add_of_hasSum_prod
  given: {a : α} (h : HasSum (∏ i in ·, f i) a)
  proof: by
  simp_rw [HasProd, prod_one_add]
  exact h.comp tendsto_finset_powerset_atTop_atTop

中文:
定理 hasProd_one_add_of_hasSum_prod
  条件: {a : α} (h : HasSum (∏ i in ·, f i) a)
  证明: by
  simp_rw [HasProd, prod_one_add]
  exact h.comp tendsto_finset_powerset_atTop_atTop

Depends on / 依赖: HasProd, h.comp, prod_one_add, simp_rw, tendsto_finset_powerset_atTop_atTop
-/
theorem hasProd_one_add_of_hasSum_prod {a : α} (h : HasSum (∏ i in ·, f i) a) :
    HasProd (1 + f ·) a := by
  simp_rw [HasProd, prod_one_add]
  exact h.comp tendsto_finset_powerset_atTop_atTop

/--
theorem `multipliable_one_add_of_summable_prod` / 定理 `multipliable_one_add_of_summable_prod`

English:
theorem multipliable_one_add_of_summable_prod
  given: (h : Summable (∏ i in ·, f i))
  proof: by
  obtain ⟨a, h⟩ := h
  exact ⟨a, hasProd_one_add_of_hasSum_prod h⟩

中文:
定理 multipliable_one_add_of_summable_prod
  条件: (h : Summable (∏ i in ·, f i))
  证明: by
  obtain ⟨a, h⟩ := h
  exact ⟨a, hasProd_one_add_of_hasSum_prod h⟩

Depends on / 依赖: hasProd_one_add_of_hasSum_prod
-/
theorem multipliable_one_add_of_summable_prod (h : Summable (∏ i in ·, f i)) :
    Multipliable (1 + f ·) := by
  obtain ⟨a, h⟩ := h
  exact ⟨a, hasProd_one_add_of_hasSum_prod h⟩

/--
theorem `tprod_one_add` / 定理 `tprod_one_add`

English:
theorem tprod_one_add
  given: [T2Space α] (h : Summable (∏ i in ·, f i))
  proof: HasProd.tprod_eq hasProd_one_add_of_hasSum_prod h.hasSum

中文:
定理 tprod_one_add
  条件: [T2Space α] (h : Summable (∏ i in ·, f i))
  证明: HasProd.tprod_eq hasProd_one_add_of_hasSum_prod h.hasSum

Depends on / 依赖: HasProd, HasProd.tprod_eq, h.hasSum, hasProd_one_add_of_hasSum_prod, hasSum, tprod_eq
-/
theorem tprod_one_add [T2Space α] (h : Summable (∏ i in ·, f i)) :
    ∏' i, (1 + f i) = ∑' s, ∏ i in s, f i :=
HasProd.tprod_eq hasProd_one_add_of_hasSum_prod h.hasSum

section Ordered
variable [LinearOrder ι] [LocallyFiniteOrderBot ι]

/--
theorem `tprod_one_add_ordered` / 定理 `tprod_one_add_ordered`

English:
theorem tprod_one_add_ordered
  statement: [T2Space α] [ContinuousAdd α]
  proof: by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp
  obtain ⟨x, hx⟩ := hprod
  obtain ⟨a, ha⟩ := hsum
  convert! hx.tprod_eq
  unfold HasProd at hx
  conv at hx in fun _ => _ => ext _; rw [prod_one_add_ordered] -- simp_rw would cause loop
  rw [ha.tsum_eq]
  refine (tendsto_nhds_unique (hx.comp t

中文:
定理 tprod_one_add_ordered
  结论: [T2Space α] [ContinuousAdd α]
  证明: by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp
  obtain ⟨x, hx⟩ := hprod
  obtain ⟨a, ha⟩ := hsum
  convert! hx.tprod_eq
  unfold HasProd at hx
  conv at hx in fun _ => _ => ext _; rw [prod_one_add_ordered] -- simp_rw would cause loop
  rw [ha.tsum_eq]
  refine (tendsto_nhds_unique (hx.comp t

Depends on / 依赖: HasProd, Tendsto, Tendsto.const_add, const_add, convert, ha.comp, ha.tsum_eq, hx.comp, hx.tprod_eq, isEmpty_or_nonempty, prod_one_add_ordered, simp_rw, sum_congr, tendsto_finset_Iic_atTop_atTop, tendsto_nhds_unique, tprod_eq, tsum_eq
-/
theorem tprod_one_add_ordered [T2Space α] [ContinuousAdd α]
    (hsum : Summable fun i => f i * ∏ j in Iio i, (1 + f j))
    (hprod : Multipliable (1 + f ·)) :
    ∏' i, (1 + f i) = 1 + ∑' i, f i * ∏ j in Iio i, (1 + f j) := by
  rcases isEmpty_or_nonempty ι with _ | _
  · simp
  obtain ⟨x, hx⟩ := hprod
  obtain ⟨a, ha⟩ := hsum
  convert! hx.tprod_eq
  unfold HasProd at hx
  conv at hx in fun _ => _ => ext _; rw [prod_one_add_ordered] -- simp_rw would cause loop
  rw [ha.tsum_eq]
  refine (tendsto_nhds_unique (hx.comp tendsto_finset_Iic_atTop_atTop) ?_).symm
  apply Tendsto.const_add
  convert! ha.comp tendsto_finset_Iic_atTop_atTop using 2 with s
  refine sum_congr rfl (fun i hi => ?_)
  congr
  grind

/--
theorem `tprod_one_sub_ordered` / 定理 `tprod_one_sub_ordered`

English:
theorem tprod_one_sub_ordered
  statement: {α : Type*} {f : ι -> α}
  proof: by
  simp_rw [sub_eq_add_neg] at hsum hprod ⊢
  obtain hsum' := hsum.neg
  simp_rw [← neg_mul] at hsum'
  simp_rw [← tsum_neg, ← neg_mul]
  exact tprod_one_add_ordered hsum' hprod

中文:
定理 tprod_one_sub_ordered
  结论: {α : 类型} {f : ι -> α}
  证明: by
  simp_rw [sub_eq_add_neg] at hsum hprod ⊢
  obtain hsum' := hsum.neg
  simp_rw [← neg_mul] at hsum'
  simp_rw [← tsum_neg, ← neg_mul]
  exact tprod_one_add_ordered hsum' hprod

Depends on / 依赖: hsum.neg, neg_mul, simp_rw, sub_eq_add_neg, tprod_one_add_ordered, tsum_neg
-/
theorem tprod_one_sub_ordered {α : Type*} {f : ι -> α}
    [CommRing α] [TopologicalSpace α] [T2Space α] [IsTopologicalAddGroup α]
    (hsum : Summable fun i => f i * ∏ j in Iio i, (1 - f j))
    (hprod : Multipliable (1 - f ·)) :
    ∏' i, (1 - f i) = 1 - ∑' i, f i * ∏ j in Iio i, (1 - f j) := by
  simp_rw [sub_eq_add_neg] at hsum hprod ⊢
  obtain hsum' := hsum.neg
  simp_rw [← neg_mul] at hsum'
  simp_rw [← tsum_neg, ← neg_mul]
  exact tprod_one_add_ordered hsum' hprod

end Ordered

end ProdOneSum
