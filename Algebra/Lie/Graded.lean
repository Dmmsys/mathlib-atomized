/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Lie.Derivation.Basic

/-!
# Graded Lie algebras

This file defines typeclasses `SetLike.GradedBracket` and `GradedLieAlgebra`, for working with Lie
algebras that are graded by a collection `ℒ` of submodules.

## Main definitions

* `SetLike.GradedBracket`: A typeclass for a bracket to respect an additive grading.
* `GradedLieAlgebra`: A typeclass for a Lie algebra to respect an additive grading.
* `LieDerivation.ofGradingSum`: A Lie derivation on the direct sum of graded pieces, that scalar-
  multiplies the pieces by an additive map applied to degree.
* `LieDerivation.ofGrading`: A Lie derivation on a graded Lie algebra, that scalar-multiplies graded
  pieces by an additive map applied to degree.

## Implementation notes

For now we only implement internally-graded Lie algebras; supporting the externally-graded case
would be achieved by generalizing the `LieRing (⨁ i, ℒ i)` instance to take a family of types,
and defining a new `GradedMonoid.GBracket` class to provide the data piecewise.

-/

@[expose] public section

open DirectSum

variable {ι σ R L : Type*}

section SetLike

/--
Definition of `SetLike.GradedBracket` / `SetLike.GradedBracket` 的定义

English:
class SetLike.GradedBracket
  parameters: [SetLike σ L] [Bracket L L] [Add ι] (ℒ : ι -> σ)
  axioms and operations (1):
    - bracket_mem : forall ⦃i j⦄ {gi gj}, gi in ℒ i -> gj in ℒ j -> ⁅gi, gj⁆ in ℒ (i + j)

中文:
类 集合状.GradedBracket
  参数: [集合状 σ L] [Bracket L L] [加法 ι] (ℒ : ι -> σ)
  公理与运算 (1 个):
    - bracket_mem : 对任意 ⦃i j⦄ {gi gj}, gi in ℒ i -> gj in ℒ j -> ⁅gi, gj⁆ in ℒ (i + j)
-/
class SetLike.GradedBracket [SetLike σ L] [Bracket L L] [Add ι] (ℒ : ι -> σ) : Prop where
  /-- Bracket is homogeneous -/
  bracket_mem : forall ⦃i j⦄ {gi gj}, gi in ℒ i -> gj in ℒ j -> ⁅gi, gj⁆ in ℒ (i + j)

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι -> Submodule R L)

/--
Definition of `GradedLieAlgebra` / `GradedLieAlgebra` 的定义

English:
class GradedLieAlgebra
  parameters: extends SetLike.GradedBracket ℒ, DirectSum.Decomposition ℒ
  extends: SetLike.GradedBracket ℒ, DirectSum.Decomposition ℒ
  (no additional axioms)

中文:
类 GradedLie代数
  参数: extends 集合状.GradedBracket ℒ, 直和.分解 ℒ
  继承: 集合状.GradedBracket ℒ, 直和.分解 ℒ
  (无附加公理)
-/
class GradedLieAlgebra extends SetLike.GradedBracket ℒ, DirectSum.Decomposition ℒ

end SetLike

namespace DirectSum

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι -> Submodule R L) [GradedLieAlgebra ℒ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (⨁ i, ℒ i)
  body: decomposeLinearEquiv ℒ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

中文:
实例 :
  签名: Lie环 (⨁ i, ℒ i)
  定义体: decomposeLinearEquiv ℒ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

Depends on / 依赖: decomposeLinearEquiv
-/
instance : LieRing (⨁ i, ℒ i) where
  bracket x y := decomposeLinearEquiv ℒ
    ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

/--
lemma `bracket_apply_apply` / 引理 `bracket_apply_apply`

English:
lemma bracket_apply_apply
  given: (x y : ⨁ i, ℒ i)
  proof: rfl

中文:
引理 bracket_apply_apply
  条件: (x y : ⨁ i, ℒ i)
  证明: rfl
-/
lemma bracket_apply_apply (x y : ⨁ i, ℒ i) :
    ⁅x, y⁆ =
      decomposeLinearEquiv ℒ ⁅(decomposeLinearEquiv ℒ).symm x, (decomposeLinearEquiv ℒ).symm y⁆ :=
  rfl

attribute [local simp] bracket_apply_apply

@[simp]
/--
lemma `decompose_bracket` / 引理 `decompose_bracket`

English:
lemma decompose_bracket
  given: (x y : L)
  statement: decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℒ y⁆
  proof: by
  simp only [← decomposeLinearEquiv_apply]
  simp

@[simp]

中文:
引理 decompose_bracket
  条件: (x y : L)
  结论: decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℒ y⁆
  证明: by
  simp only [← decomposeLinearEquiv_apply]
  simp

@[simp]

Depends on / 依赖: decomposeLinearEquiv_apply
-/
lemma decompose_bracket (x y : L) : decompose ℒ ⁅x, y⁆ = ⁅decompose ℒ x, decompose ℒ y⁆ := by
  simp only [← decomposeLinearEquiv_apply]
  simp

@[simp]
/--
lemma `decompose_symm_bracket` / 引理 `decompose_symm_bracket`

English:
lemma decompose_symm_bracket
  given: (x y : ⨁ i, ℒ i)
  proof: by
  simp only [← decomposeLinearEquiv_symm_apply]
  simp

中文:
引理 decompose_symm_bracket
  条件: (x y : ⨁ i, ℒ i)
  证明: by
  simp only [← decomposeLinearEquiv_symm_apply]
  simp

Depends on / 依赖: decomposeLinearEquiv_symm_apply
-/
lemma decompose_symm_bracket (x y : ⨁ i, ℒ i) :
    (decompose ℒ).symm ⁅x, y⁆ = ⁅(decompose ℒ).symm x, (decompose ℒ).symm y⁆ := by
  simp only [← decomposeLinearEquiv_symm_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieAlgebra R (⨁ i, ℒ i)
  body: by simp [add_smul]
  zero_smul _ := by simp
  lie_smul _ _ _ := by simp

中文:
实例 :
  签名: Lie代数 R (⨁ i, ℒ i)
  定义体: by simp [add_smul]
  zero_smul _ := by simp
  lie_smul _ _ _ := by simp

Depends on / 依赖: add_smul, lie_smul, zero_smul
-/
instance : LieAlgebra R (⨁ i, ℒ i) where
  add_smul _ _ _ := by simp [add_smul]
  zero_smul _ := by simp
  lie_smul _ _ _ := by simp

/--
Definition of `decomposeLieEquiv` / `decomposeLieEquiv` 的定义

English:
definition decomposeLieEquiv
  signature: : L ≃ₗ⁅R⁆ ⨁ i, ℒ i
  body: { decomposeLinearEquiv ℒ with
    map_lie' := by simp }

中文:
定义 decomposeLieEquiv
  签名: : L ≃ₗ⁅R⁆ ⨁ i, ℒ i
  定义体: { decomposeLinearEquiv ℒ with
    map_lie' := by simp }

Depends on / 依赖: decomposeLinearEquiv, map_lie
-/
def decomposeLieEquiv : L ≃ₗ⁅R⁆ ⨁ i, ℒ i :=
  { decomposeLinearEquiv ℒ with
    map_lie' := by simp }

end DirectSum

namespace LieDerivation

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι -> Submodule R L) [GradedLieAlgebra ℒ]

/--
Definition of `ofGradingSum` / `ofGradingSum` 的定义

English:
definition ofGradingSum
  signature: (φ : ι ->+ R)
  body: { __ := DirectSum.toModule R ι (⨁ i, ℒ i)
      fun i => (lof R ι (ℒ ·) i).comp (Module.End.smulLeft (φ i) (by simp))
    leibniz' x y := by
      have hM (k : ι) (b : ⨁ i, ℒ i) (hb : (decompose ℒ).symm b in ℒ k) :
          (toModule R ι (⨁ (i : ι), ℒ i) fun i => lof R ι (ℒ ·) i ∘ₗ (φ i • .id)) b =

中文:
定义 ofGradingSum
  签名: (φ : ι ->+ R)
  定义体: { __ := DirectSum.toModule R ι (⨁ i, ℒ i)
      fun i => (lof R ι (ℒ ·) i).comp (Module.End.smulLeft (φ i) (by simp))
    leibniz' x y := by
      have hM (k : ι) (b : ⨁ i, ℒ i) (hb : (decompose ℒ).symm b in ℒ k) :
          (toModule R ι (⨁ (i : ι), ℒ i) fun i => lof R ι (ℒ ·) i ∘ₗ (φ i • .id)) b =

Depends on / 依赖: DirectSum, DirectSum.induction_on, DirectSum.toModule, LinearMap, LinearMap.range, Module, Module.End.smulLeft, decompose, decompose_of_mem, induction_on, leibniz, lof_eq_of, smulLeft, toModule
-/
def ofGradingSum (φ : ι ->+ R) : LieDerivation R (⨁ i, ℒ i) (⨁ i, ℒ i) :=
  { __ := DirectSum.toModule R ι (⨁ i, ℒ i)
      fun i => (lof R ι (ℒ ·) i).comp (Module.End.smulLeft (φ i) (by simp))
    leibniz' x y := by
      have hM (k : ι) (b : ⨁ i, ℒ i) (hb : (decompose ℒ).symm b in ℒ k) :
          (toModule R ι (⨁ (i : ι), ℒ i) fun i => lof R ι (ℒ ·) i ∘ₗ (φ i • .id)) b = (φ k) • b := by
        obtain ⟨_, rfl⟩ : b in LinearMap.range (lof R ι (ℒ ·) k) := by
          use ⟨(decompose ℒ).symm b, hb⟩
          simp [lof_eq_of, ← decompose_of_mem]
        simp
      ext j
      induction x using DirectSum.induction_on' with
      | h0 => simp
      | hadd i a f _ _ ih =>
        simp only [Module.End.smulLeft_eq, DirectSum.sub_apply, AddSubgroupClass.coe_sub] at ih
        simp only [Module.End.smulLeft_eq, add_lie, map_add, DirectSum.add_apply, Submodule.coe_add,
          ih, lie_add, DirectSum.sub_apply, AddSubgroupClass.coe_sub]
        rw [add_sub_add_comm]; rw [add_right_cancel_iff]; rw [hM i (of (ℒ ·) i a) (by simp)]
        clear ih
        induction y using DirectSum.induction_on' with
        | h0 => simp
        | hadd k b f _ _ ih =>
          simp only [lie_add, map_add, DirectSum.add_apply, Submodule.coe_add, ih, lie_smul,
            add_lie, smul_add, add_sub, ← sub_sub]
          congr 1
          have : (decompose ℒ).symm ⁅of (fun i => ℒ i) i a, of (fun i => ℒ i) k b⁆ in ℒ (i + k) := by
            simp [SetLike.GradedBracket.bracket_mem (Submodule.coe_mem a) (Submodule.coe_mem b)]
          rw [hM _ _ this]; rw [hM k (of (ℒ ·) k b) (by simp)]; rw [← lie_skew (of (ℒ ·) k b)]; rw [add_sub_right_comm]; rw [add_right_cancel_iff]; rw [add_comm i k]; rw [map_add]; rw [add_smul]; rw [DirectSum.add_apply]; rw [Submodule.coe_add]; rw [sub_eq_add_neg]; rw [lie_smul]; rw [add_left_cancel_iff]; rw [smul_neg]; rw [← sub_eq_zero]; rw [sub_neg_eq_add]; rw [← Submodule.coe_add]; rw [Submodule.coe_eq_zero]; rw [← DirectSum.add_apply]; rw [add_neg_cancel]; rw [DirectSum.zero_apply] }

@[simp]
/--
lemma `ofGradingSum_of` / 引理 `ofGradingSum_of`

English:
lemma ofGradingSum_of
  given: (φ : ι ->+ R) (i : ι) (a : ℒ i)
  proof: by
  simp [← lof_eq_of R, ofGradingSum]

中文:
引理 ofGradingSum_of
  条件: (φ : ι ->+ R) (i : ι) (a : ℒ i)
  证明: by
  simp [← lof_eq_of R, ofGradingSum]

Depends on / 依赖: lof_eq_of, ofGradingSum
-/
lemma ofGradingSum_of (φ : ι ->+ R) (i : ι) (a : ℒ i) :
    ofGradingSum ℒ φ (of (ℒ ·) i a) = (φ i) • (of (ℒ ·) i a) := by
  simp [← lof_eq_of R, ofGradingSum]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofGrading` / `ofGrading` 的定义

English:
definition ofGrading
  signature: (φ : ι ->+ R)
  body: (decomposeLinearEquiv ℒ).symm ofGradingSum ℒ φ decomposeLinearEquiv ℒ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  leibniz' x y := by simp [decomposeLinearEquiv_apply, decomposeLinearEquiv_symm_apply]

中文:
定义 ofGrading
  签名: (φ : ι ->+ R)
  定义体: (decomposeLinearEquiv ℒ).symm ofGradingSum ℒ φ decomposeLinearEquiv ℒ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  leibniz' x y := by simp [decomposeLinearEquiv_apply, decomposeLinearEquiv_symm_apply]

Depends on / 依赖: decomposeLinearEquiv, ofGradingSum
-/
def ofGrading (φ : ι ->+ R) :
    LieDerivation R L L where
toFun x := (decomposeLinearEquiv ℒ).symm ofGradingSum ℒ φ decomposeLinearEquiv ℒ x
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  leibniz' x y := by simp [decomposeLinearEquiv_apply, decomposeLinearEquiv_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofGrading_apply_apply` / 引理 `ofGrading_apply_apply`

English:
lemma ofGrading_apply_apply
  given: (φ : ι ->+ R) {i : ι} {a : L} (ha : a in ℒ i)
  proof: by
  simp [ofGrading, decomposeLinearEquiv_apply, decompose_of_mem ℒ ha]
  simp [decomposeLinearEquiv_symm_apply]

中文:
引理 ofGrading_apply_apply
  条件: (φ : ι ->+ R) {i : ι} {a : L} (ha : a in ℒ i)
  证明: by
  simp [ofGrading, decomposeLinearEquiv_apply, decompose_of_mem ℒ ha]
  simp [decomposeLinearEquiv_symm_apply]

Depends on / 依赖: decomposeLinearEquiv_apply, decomposeLinearEquiv_symm_apply, decompose_of_mem, ofGrading
-/
lemma ofGrading_apply_apply (φ : ι ->+ R) {i : ι} {a : L} (ha : a in ℒ i) :
    ofGrading ℒ φ a = φ i • a := by
  simp [ofGrading, decomposeLinearEquiv_apply, decompose_of_mem ℒ ha]
  simp [decomposeLinearEquiv_symm_apply]

end LieDerivation
