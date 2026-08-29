/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Sums of translates of a continuous function is a period continuous function.

-/

public section
assert_not_exists StoneCech StarModule

namespace ContinuousMap

section Periodicity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Summing translates of a function -/

/--
theorem `periodic_tsum_comp_add_zsmul` / 定理 `periodic_tsum_comp_add_zsmul`

English:
theorem periodic_tsum_comp_add_zsmul
  statement: [AddCommGroup X] [ContinuousAdd X] [AddCommMonoid Y]
  proof: by
  intro x
  by_cases h : Summable fun n : Int => f.comp (ContinuousMap.addRight (n • p))
  · convert! congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : Int)).tsum_eq _) using 1
    -- This `have` unfolds the function composition in `Equiv.summable_iff`.

    -- This `have` unfolds the function composition in `Equiv.summable_iff`.
    have : Summable fun (c : Int) => f.comp (ContinuousMap.addRight (Equiv.addRight 1 c • p)) :=
      (Equiv.addRight (1 : Int)).summable_iff.mpr h
    simp_rw [← tsum_apply h, ← tsum_apply this]
    simp [Equiv.coe_addRight, comp_apply, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]

中文:
定理 periodic_tsum_comp_add_zsmul
  结论: [加法交换群 X] [连续加法 X] [加法交换幺半群 Y]
  证明: by
  intro x
  by_cases h : Summable fun n : Int => f.comp (ContinuousMap.addRight (n • p))
  · convert! congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : Int)).tsum_eq _) using 1
    -- This `have` unfolds the function composition in `Equiv.summable_iff`.

    -- This `have` unfolds the function composition in `Equiv.summable_iff`.
    have : Summable fun (c : Int) => f.comp (ContinuousMap.addRight (Equiv.addRight 1 c • p)) :=
      (Equiv.addRight (1 : Int)).summable_iff.mpr h
    simp_rw [← tsum_apply h, ← tsum_apply this]
    simp [Equiv.coe_addRight, comp_apply, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]

Depends on / 依赖: ContinuousMap, ContinuousMap.addRight, Equiv.addRight, Summable, addRight, congr_arg, convert, f.comp, tsum_eq
-/
theorem periodic_tsum_comp_add_zsmul [AddCommGroup X] [ContinuousAdd X] [AddCommMonoid Y]
    [ContinuousAdd Y] [T2Space Y] (f : C(X, Y)) (p : X) :
    Function.Periodic (⇑(∑' n : Int, f.comp (ContinuousMap.addRight (n • p)))) p := by
  intro x
  by_cases h : Summable fun n : Int => f.comp (ContinuousMap.addRight (n • p))
  · convert! congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : Int)).tsum_eq _) using 1
    -- This `have` unfolds the function composition in `Equiv.summable_iff`.

    -- This `have` unfolds the function composition in `Equiv.summable_iff`.
    have : Summable fun (c : Int) => f.comp (ContinuousMap.addRight (Equiv.addRight 1 c • p)) :=
      (Equiv.addRight (1 : Int)).summable_iff.mpr h
    simp_rw [← tsum_apply h, ← tsum_apply this]
    simp [Equiv.coe_addRight, comp_apply, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]

end Periodicity

end ContinuousMap
