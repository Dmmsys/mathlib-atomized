/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/

@[expose] public section


namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive (attr := simps) /-- The inclusion of locally-constant functions into continuous
functions as an additive monoid hom. -/]
/--
Definition of `toContinuousMapMonoidHom` / `toContinuousMapMonoidHom` 的定义

English:
definition toContinuousMapMonoidHom
  signature: [Monoid Y] [ContinuousMul Y]
  body: (↑)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

中文:
定义 toContinuousMapMonoidHom
  签名: [幺半群 Y] [连续乘法 Y]
  定义体: (↑)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
-/
def toContinuousMapMonoidHom [Monoid Y] [ContinuousMul Y] : LocallyConstant X Y ->* C(X, Y) where
  toFun := (↑)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
/--
Definition of `toContinuousMapLinearMap` / `toContinuousMapLinearMap` 的定义

English:
definition toContinuousMapLinearMap
  signature: (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
  body: (↑)
  __ := toContinuousMapAddMonoidHom
  map_smul' x y := by
    ext
    simp

中文:
定义 toContinuousMapLinearMap
  签名: (R : 类型) [半环 R] [加法交换幺半群 Y] [模 R Y]
  定义体: (↑)
  __ := toContinuousMapAddMonoidHom
  map_smul' x y := by
    ext
    simp
-/
def toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [ContinuousAdd Y] [ContinuousConstSMul R Y] : LocallyConstant X Y ->ₗ[R] C(X, Y) where
  toFun := (↑)
  __ := toContinuousMapAddMonoidHom
  map_smul' x y := by
    ext
    simp

/--
lemma `toAddMonoidHom_toContinuousMapLinearMap` / 引理 `toAddMonoidHom_toContinuousMapLinearMap`

English:
lemma toAddMonoidHom_toContinuousMapLinearMap
  statement: (R : Type*) [Semiring R] [AddCommMonoid Y]
  proof: rfl

中文:
引理 toAddMonoidHom_toContinuousMapLinearMap
  结论: (R : 类型) [半环 R] [加法交换幺半群 Y]
  证明: rfl
-/
@[simp] lemma toAddMonoidHom_toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] [ContinuousAdd Y] [ContinuousConstSMul R Y] :
    (toContinuousMapLinearMap R (X := X) (Y := Y)).toAddMonoidHom = toContinuousMapAddMonoidHom :=
  rfl

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
/--
Definition of `toContinuousMapAlgHom` / `toContinuousMapAlgHom` 的定义

English:
definition toContinuousMapAlgHom
  signature: (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
  body: (↑)
  __ := toContinuousMapMonoidHom
  __ := toContinuousMapAddMonoidHom
  commutes' r := by
    ext x
    simp [Algebra.smul_def]

中文:
定义 toContinuousMapAlgHom
  签名: (R : 类型) [交换半环 R] [半环 Y] [代数 R Y]
  定义体: (↑)
  __ := toContinuousMapMonoidHom
  __ := toContinuousMapAddMonoidHom
  commutes' r := by
    ext x
    simp [Algebra.smul_def]
-/
def toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [IsTopologicalSemiring Y] : LocallyConstant X Y ->ₐ[R] C(X, Y) where
  toFun := (↑)
  __ := toContinuousMapMonoidHom
  __ := toContinuousMapAddMonoidHom
  commutes' r := by
    ext x
    simp [Algebra.smul_def]

/--
lemma `toLinearMap_toContinuousMapAlgHom` / 引理 `toLinearMap_toContinuousMapAlgHom`

English:
lemma toLinearMap_toContinuousMapAlgHom
  statement: (R : Type*) [CommSemiring R] [Semiring Y]
  proof: rfl

中文:
引理 toLinearMap_toContinuousMapAlgHom
  结论: (R : 类型) [交换半环 R] [半环 Y]
  证明: rfl
-/
@[simp] lemma toLinearMap_toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y]
    [Algebra R Y] [IsTopologicalSemiring Y] :
    (toContinuousMapAlgHom R (X := X) (Y := Y)).toLinearMap = toContinuousMapLinearMap R := rfl

/--
theorem `separatesPoints_range_toContinuousMapAlgHom` / 定理 `separatesPoints_range_toContinuousMapAlgHom`

English:
theorem separatesPoints_range_toContinuousMapAlgHom
  statement: (R : Type*) [CommSemiring R]
  proof: fun _ _ hxy =>
  have ⟨_, hU, _, _⟩ := exists_isClopen_of_totally_separated hxy
  ⟨charFn Y hU, by simp_all [charFn]⟩

中文:
定理 separatesPoints_range_toContinuousMapAlgHom
  结论: (R : 类型) [交换半环 R]
  证明: fun _ _ hxy =>
  have ⟨_, hU, _, _⟩ := exists_isClopen_of_totally_separated hxy
  ⟨charFn Y hU, by simp_all [charFn]⟩
-/
theorem separatesPoints_range_toContinuousMapAlgHom (R : Type*) [CommSemiring R]
    [TotallySeparatedSpace X] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y] [Nontrivial Y] :
    (toContinuousMapAlgHom R : _ ->ₐ[R] C(X, Y)).range.SeparatesPoints := fun _ _ hxy =>
  have ⟨_, hU, _, _⟩ := exists_isClopen_of_totally_separated hxy
  ⟨charFn Y hU, by simp_all [charFn]⟩

end LocallyConstant
