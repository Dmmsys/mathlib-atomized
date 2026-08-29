/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue

/-!
# Admissible absolute value on the integers

This file defines an admissible absolute value `AbsoluteValue.absIsAdmissible`
which we use to show the class number of the ring of integers of a number field
is finite.

## Main results

* `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
  mapping negative `x` to `-x`, is admissible.
-/

@[expose] public section


namespace AbsoluteValue

open Int

/--
theorem `exists_partition_int` / 定理 `exists_partition_int`

English:
theorem exists_partition_int
  given: (n : Nat) {ε : Real} (hε : 0 < ε) {b : Int} (hb : b != 0) (A : Fin n -> Int)
  proof: by
  have hb' : (0 : Real) < ↑(abs b) := Int.cast_pos.mpr (abs_pos.mpr hb)
  have hbε : 0 < abs b • ε := by
    rw [Algebra.smul_def]
    exact mul_pos hb' hε
  have hfloor : forall i, 0 <= floor ((A i % b : Int) / abs b • ε : Real) :=
    fun _ => floor_nonneg.mpr (div_nonneg (cast_nonneg (emod_non

中文:
定理 存在_partition_int
  条件: (n : 自然数) {ε : 实数} (hε : 0 < ε) {b : 整数} (hb : b != 0) (A : 有限集 n -> 整数)
  证明: by
  have hb' : (0 : Real) < ↑(abs b) := Int.cast_pos.mpr (abs_pos.mpr hb)
  have hbε : 0 < abs b • ε := by
    rw [Algebra.smul_def]
    exact mul_pos hb' hε
  have hfloor : forall i, 0 <= floor ((A i % b : Int) / abs b • ε : Real) :=
    fun _ => floor_nonneg.mpr (div_nonneg (cast_nonneg (emod_non

Depends on / 依赖: Algebra, Algebra.smul_def, Int.cast_pos.mpr, abs_pos, abs_pos.mpr, cast_nonneg, cast_pos, div_div, div_nonneg, emod_nonneg, eq_intCast, floor_lt, floor_nonneg, floor_nonneg.mpr, hfloor, lt_of_lt_of_le, mul_pos, natAbs, natAbs_of_nonneg, ofNat_lt
-/
theorem exists_partition_int (n : Nat) {ε : Real} (hε : 0 < ε) {b : Int} (hb : b != 0) (A : Fin n -> Int) :
    exists t : Fin n -> Fin ⌈1 / ε⌉₊,
    forall i₀ i₁, t i₀ = t i₁ -> ↑(abs (A i₁ % b - A i₀ % b)) < abs b • ε := by
  have hb' : (0 : Real) < ↑(abs b) := Int.cast_pos.mpr (abs_pos.mpr hb)
  have hbε : 0 < abs b • ε := by
    rw [Algebra.smul_def]
    exact mul_pos hb' hε
  have hfloor : forall i, 0 <= floor ((A i % b : Int) / abs b • ε : Real) :=
    fun _ => floor_nonneg.mpr (div_nonneg (cast_nonneg (emod_nonneg _ hb)) hbε.le)
  refine ⟨fun i => ⟨natAbs (floor ((A i % b : Int) / abs b • ε : Real)), ?_⟩, ?_⟩
  · rw [← ofNat_lt, natAbs_of_nonneg (hfloor i), floor_lt, Algebra.smul_def, eq_intCast, ← div_div]
    apply lt_of_lt_of_le _ (Nat.le_ceil _)
    gcongr
    rw [div_lt_one hb']; rw [cast_lt]
    exact Int.emod_lt_abs _ hb
  intro i₀ i₁ hi
  have hi : (⌊↑(A i₀ % b) / abs b • ε⌋.natAbs : Int) = ⌊↑(A i₁ % b) / abs b • ε⌋.natAbs :=
    congr_arg ((↑) : Nat -> Int) (Fin.mk_eq_mk.mp hi)
  rw [natAbs_of_nonneg (hfloor i₀)]; rw [natAbs_of_nonneg (hfloor i₁)] at hi
  have hi := abs_sub_lt_one_of_floor_eq_floor hi
  rw [abs_sub_comm]; rw [← sub_div]; rw [abs_div]; rw [abs_of_nonneg hbε.le]; rw [div_lt_iff₀ hbε]; rw [one_mul] at hi
  rwa [Int.cast_abs, Int.cast_sub]

/--
Definition of `absIsAdmissible` / `absIsAdmissible` 的定义

English:
definition absIsAdmissible
  signature: : IsAdmissible AbsoluteValue.abs
  body: { AbsoluteValue.abs_isEuclidean with
    card := fun ε => ⌈1 / ε⌉₊
    exists_partition' := fun n _ hε _ hb => exists_partition_int n hε hb }

中文:
定义 absIsAdmissible
  签名: : 是Admissible 绝对值.abs
  定义体: { AbsoluteValue.abs_isEuclidean with
    card := fun ε => ⌈1 / ε⌉₊
    exists_partition' := fun n _ hε _ hb => exists_partition_int n hε hb }

Depends on / 依赖: AbsoluteValue, AbsoluteValue.abs_isEuclidean, abs_isEuclidean, exists_partition, exists_partition_int
-/
noncomputable def absIsAdmissible : IsAdmissible AbsoluteValue.abs :=
  { AbsoluteValue.abs_isEuclidean with
    card := fun ε => ⌈1 / ε⌉₊
    exists_partition' := fun n _ hε _ hb => exists_partition_int n hε hb }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (IsAdmissible AbsoluteValue.abs)
  body: ⟨absIsAdmissible⟩

中文:
实例 :
  签名: 可居 (是Admissible 绝对值.abs)
  定义体: ⟨absIsAdmissible⟩

Depends on / 依赖: absIsAdmissible
-/
noncomputable instance : Inhabited (IsAdmissible AbsoluteValue.abs) :=
  ⟨absIsAdmissible⟩

end AbsoluteValue
