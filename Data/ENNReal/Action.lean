/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.AddTorsor
public import Mathlib.Data.ENNReal.Operations

/-!
# Scalar multiplication on `ℝ≥0∞`.

This file defines basic scalar actions on extended nonnegative reals, showing that
`MulAction`s, `DistribMulAction`s, `Module`s and `Algebra`s restrict from `ℝ≥0∞` to `ℝ≥0`.
-/

@[expose] public section

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : Real>=0∞} {r p q : Real>=0}

-- TODO: generalize some of these to `WithTop α`
section Actions

noncomputable instance {M : Type*} [MulAction Real>=0∞ M] : SMul Real>=0 M :=
  ⟨fun c m => (c : Real>=0∞) • m⟩

/-- A `MulAction` over `ℝ≥0∞` restricts to a `MulAction` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [MulAction Real>=0∞ M] : MulAction Real>=0 M :=
  fast_instance% MulAction.compHom M ofNNRealHom.toMonoidHom

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: {M : Type*} [MulAction Real>=0∞ M] (c : Real>=0) (x : M)
  statement: c • x = (c : Real>=0∞) • x
  proof: rfl

@[simp]

中文:
定理 smul_def
  条件: {M : 类型} [乘法作用 实数>=0∞ M] (c : 实数>=0) (x : M)
  结论: c • x = (c : 实数>=0∞) • x
  证明: rfl

@[simp]
-/
theorem smul_def {M : Type*} [MulAction Real>=0∞ M] (c : Real>=0) (x : M) : c • x = (c : Real>=0∞) • x :=
  rfl

@[simp]
/--
theorem `smul_one` / 定理 `smul_one`

English:
theorem smul_one
  given: (c : Real>=0)
  statement: c • (1 : Real>=0∞) = (c : Real>=0∞)
  proof: by simp [smul_def]

中文:
定理 smul_one
  条件: (c : 实数>=0)
  结论: c • (1 : 实数>=0∞) = (c : 实数>=0∞)
  证明: by simp [smul_def]

Depends on / 依赖: smul_def
-/
theorem smul_one (c : Real>=0) : c • (1 : Real>=0∞) = (c : Real>=0∞) := by simp [smul_def]

instance {M N : Type*} [MulAction Real>=0∞ M] [MulAction Real>=0∞ N] [SMul M N] [IsScalarTower Real>=0∞ M N] :
    IsScalarTower Real>=0 M N where smul_assoc r := smul_assoc (r : Real>=0∞)

/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: {M N : Type*} [MulAction Real>=0∞ N] [SMul M N] [SMulCommClass Real>=0∞ M N]
  body: smul_comm (r : Real>=0∞)

中文:
实例 smulCommClass_left
  签名: {M N : 类型} [乘法作用 实数>=0∞ N] [标量乘法 M N] [标量交换类 实数>=0∞ M N]
  定义体: smul_comm (r : Real>=0∞)

Depends on / 依赖: smul_comm
-/
instance smulCommClass_left {M N : Type*} [MulAction Real>=0∞ N] [SMul M N] [SMulCommClass Real>=0∞ M N] :
    SMulCommClass Real>=0 M N where smul_comm r := smul_comm (r : Real>=0∞)

/--
Instance `smulCommClass_right` / 实例 `smulCommClass_right`

English:
instance smulCommClass_right
  signature: {M N : Type*} [MulAction Real>=0∞ N] [SMul M N] [SMulCommClass M Real>=0∞ N]
  body: smul_comm m (r : Real>=0∞)

中文:
实例 smulCommClass_right
  签名: {M N : 类型} [乘法作用 实数>=0∞ N] [标量乘法 M N] [标量交换类 M 实数>=0∞ N]
  定义体: smul_comm m (r : Real>=0∞)

Depends on / 依赖: smul_comm
-/
instance smulCommClass_right {M N : Type*} [MulAction Real>=0∞ N] [SMul M N] [SMulCommClass M Real>=0∞ N] :
    SMulCommClass M Real>=0 N where smul_comm m r := smul_comm m (r : Real>=0∞)

/-- A `DistribMulAction` over `ℝ≥0∞` restricts to a `DistribMulAction` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [AddMonoid M] [DistribMulAction Real>=0∞ M] :
    DistribMulAction Real>=0 M :=
  fast_instance% DistribMulAction.compHom M ofNNRealHom.toMonoidHom

/-- A `Module` over `ℝ≥0∞` restricts to a `Module` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [AddCommMonoid M] [Module Real>=0∞ M] : Module Real>=0 M :=
  fast_instance% Module.compHom M ofNNRealHom

set_option backward.isDefEq.respectTransparency false in
/-- An `Algebra` over `ℝ≥0∞` restricts to an `Algebra` over `ℝ≥0`. -/
noncomputable instance {A : Type*} [Semiring A] [Algebra Real>=0∞ A] : Algebra Real>=0 A where
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : Real>=0∞) x, smul_def]
  algebraMap := (algebraMap Real>=0∞ A).comp (ofNNRealHom : Real>=0 ->+* Real>=0∞)

-- verify that the above produces instances we might care about
noncomputable example : Algebra Real>=0 Real>=0∞ := inferInstance

noncomputable example : DistribMulAction Real>=0ˣ Real>=0∞ := inferInstance

/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  statement: {R} (r : R) (s : Real>=0) [SMul R Real>=0] [SMul R Real>=0∞] [IsScalarTower R Real>=0 Real>=0]
  proof: by
  rw [← smul_one_smul Real>=0 r (s : Real>=0∞)]; rw [smul_def]; rw [smul_eq_mul]; rw [← ENNReal.coe_mul]; rw [smul_mul_assoc]; rw [one_mul]

中文:
定理 coe_smul
  结论: {R} (r : R) (s : 实数>=0) [标量乘法 R 实数>=0] [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0 实数>=0]
  证明: by
  rw [← smul_one_smul Real>=0 r (s : Real>=0∞)]; rw [smul_def]; rw [smul_eq_mul]; rw [← ENNReal.coe_mul]; rw [smul_mul_assoc]; rw [one_mul]

Depends on / 依赖: ENNReal, ENNReal.coe_mul, coe_mul, one_mul, smul_def, smul_eq_mul, smul_mul_assoc, smul_one_smul
-/
theorem coe_smul {R} (r : R) (s : Real>=0) [SMul R Real>=0] [SMul R Real>=0∞] [IsScalarTower R Real>=0 Real>=0]
    [IsScalarTower R Real>=0 Real>=0∞] : (↑(r • s) : Real>=0∞) = (r : R) • (s : Real>=0∞) := by
  rw [← smul_one_smul Real>=0 r (s : Real>=0∞)]; rw [smul_def]; rw [smul_eq_mul]; rw [← ENNReal.coe_mul]; rw [smul_mul_assoc]; rw [one_mul]

/--
theorem `smul_top` / 定理 `smul_top`

English:
theorem smul_top
  statement: {R : Type*} [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: by
  rw [← smul_one_mul]; rw [mul_top']
  simp_rw [smul_eq_zero, or_iff_left one_ne_zero]

中文:
定理 smul_top
  结论: {R : 类型} [半环 R] [是整环 R] [模 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: by
  rw [← smul_one_mul]; rw [mul_top']
  simp_rw [smul_eq_zero, or_iff_left one_ne_zero]

Depends on / 依赖: mul_top, one_ne_zero, or_iff_left, simp_rw, smul_eq_zero, smul_one_mul
-/
theorem smul_top {R : Type*} [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    [Module.IsTorsionFree R Real>=0∞] [DecidableEq R] (c : R) :
    c • ∞ = if c = 0 then 0 else ∞ := by
  rw [← smul_one_mul]; rw [mul_top']
  simp_rw [smul_eq_zero, or_iff_left one_ne_zero]

/--
lemma `nnreal_smul_lt_top` / 引理 `nnreal_smul_lt_top`

English:
lemma nnreal_smul_lt_top
  given: {x : Real>=0} {y : Real>=0∞} (hy : y < ⊤)
  statement: x • y < ⊤
  proof: mul_lt_top (by simp) hy

中文:
引理 nnreal_smul_lt_top
  条件: {x : 实数>=0} {y : 实数>=0∞} (hy : y < ⊤)
  结论: x • y < ⊤
  证明: mul_lt_top (by simp) hy

Depends on / 依赖: mul_lt_top
-/
lemma nnreal_smul_lt_top {x : Real>=0} {y : Real>=0∞} (hy : y < ⊤) : x • y < ⊤ := mul_lt_top (by simp) hy
/--
lemma `nnreal_smul_ne_top` / 引理 `nnreal_smul_ne_top`

English:
lemma nnreal_smul_ne_top
  given: {x : Real>=0} {y : Real>=0∞} (hy : y != ⊤)
  statement: x • y != ⊤
  proof: mul_ne_top (by simp) hy

中文:
引理 nnreal_smul_ne_top
  条件: {x : 实数>=0} {y : 实数>=0∞} (hy : y != ⊤)
  结论: x • y != ⊤
  证明: mul_ne_top (by simp) hy

Depends on / 依赖: mul_ne_top
-/
lemma nnreal_smul_ne_top {x : Real>=0} {y : Real>=0∞} (hy : y != ⊤) : x • y != ⊤ := mul_ne_top (by simp) hy

/--
lemma `nnreal_smul_ne_top_iff` / 引理 `nnreal_smul_ne_top_iff`

English:
lemma nnreal_smul_ne_top_iff
  given: {x : Real>=0} {y : Real>=0∞} (hx : x != 0)
  statement: x • y != ⊤ ↔ y != ⊤
  proof: ⟨by rintro h rfl; simp [smul_top (R := Real>=0), hx] at h, nnreal_smul_ne_top⟩

中文:
引理 nnreal_smul_ne_top_iff
  条件: {x : 实数>=0} {y : 实数>=0∞} (hx : x != 0)
  结论: x • y != ⊤ ↔ y != ⊤
  证明: ⟨by rintro h rfl; simp [smul_top (R := Real>=0), hx] at h, nnreal_smul_ne_top⟩

Depends on / 依赖: nnreal_smul_ne_top, smul_top
-/
lemma nnreal_smul_ne_top_iff {x : Real>=0} {y : Real>=0∞} (hx : x != 0) : x • y != ⊤ ↔ y != ⊤ :=
  ⟨by rintro h rfl; simp [smul_top (R := Real>=0), hx] at h, nnreal_smul_ne_top⟩

/--
lemma `nnreal_smul_lt_top_iff` / 引理 `nnreal_smul_lt_top_iff`

English:
lemma nnreal_smul_lt_top_iff
  given: {x : Real>=0} {y : Real>=0∞} (hx : x != 0)
  statement: x • y < ⊤ ↔ y < ⊤
  proof: by
  rw [lt_top_iff_ne_top]; rw [lt_top_iff_ne_top]; rw [nnreal_smul_ne_top_iff hx]

@[simp]

中文:
引理 nnreal_smul_lt_top_iff
  条件: {x : 实数>=0} {y : 实数>=0∞} (hx : x != 0)
  结论: x • y < ⊤ ↔ y < ⊤
  证明: by
  rw [lt_top_iff_ne_top]; rw [lt_top_iff_ne_top]; rw [nnreal_smul_ne_top_iff hx]

@[simp]

Depends on / 依赖: lt_top_iff_ne_top, nnreal_smul_ne_top_iff
-/
lemma nnreal_smul_lt_top_iff {x : Real>=0} {y : Real>=0∞} (hx : x != 0) : x • y < ⊤ ↔ y < ⊤ := by
  rw [lt_top_iff_ne_top]; rw [lt_top_iff_ne_top]; rw [nnreal_smul_ne_top_iff hx]

@[simp]
/--
theorem `smul_toNNReal` / 定理 `smul_toNNReal`

English:
theorem smul_toNNReal
  given: (a : Real>=0) (b : Real>=0∞)
  statement: (a • b).toNNReal = a * b.toNNReal
  proof: by
  change ((a : Real>=0∞) * b).toNNReal = a * b.toNNReal
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

中文:
定理 smul_toNN实数
  条件: (a : 实数>=0) (b : 实数>=0∞)
  结论: (a • b).toNN实数 = a * b.toNN实数
  证明: by
  change ((a : Real>=0∞) * b).toNNReal = a * b.toNNReal
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_coe, ENNReal.toNNReal_mul, b.toNNReal, toNNReal, toNNReal_coe, toNNReal_mul
-/
theorem smul_toNNReal (a : Real>=0) (b : Real>=0∞) : (a • b).toNNReal = a * b.toNNReal := by
  change ((a : Real>=0∞) * b).toNNReal = a * b.toNNReal
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

/--
theorem `toReal_smul` / 定理 `toReal_smul`

English:
theorem toReal_smul
  given: (r : Real>=0) (s : Real>=0∞)
  statement: (r • s).toReal = r • s.toReal
  proof: by
  rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [toReal_mul]; rw [coe_toReal]
  rfl

中文:
定理 to实数_smul
  条件: (r : 实数>=0) (s : 实数>=0∞)
  结论: (r • s).to实数 = r • s.to实数
  证明: by
  rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [toReal_mul]; rw [coe_toReal]
  rfl

Depends on / 依赖: ENNReal, ENNReal.smul_def, coe_toReal, smul_def, smul_eq_mul, toReal_mul
-/
theorem toReal_smul (r : Real>=0) (s : Real>=0∞) : (r • s).toReal = r • s.toReal := by
  rw [ENNReal.smul_def]; rw [smul_eq_mul]; rw [toReal_mul]; rw [coe_toReal]
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PosSMulStrictMono Real>=0 Real>=0∞
  body: ENNReal.mul_lt_mul_right (coe_pos.2 hr).ne' coe_ne_top hab

中文:
实例 :
  签名: 正标量乘严格递增 实数>=0 实数>=0∞
  定义体: ENNReal.mul_lt_mul_right (coe_pos.2 hr).ne' coe_ne_top hab

Depends on / 依赖: ENNReal, ENNReal.mul_lt_mul_right, coe_ne_top, coe_pos, mul_lt_mul_right
-/
instance : PosSMulStrictMono Real>=0 Real>=0∞ where
  smul_lt_smul_of_pos_left _r hr _a _b hab :=
    ENNReal.mul_lt_mul_right (coe_pos.2 hr).ne' coe_ne_top hab

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulPosMono Real>=0 Real>=0∞
  body: _root_.mul_le_mul_left (coe_le_coe.2 hab) _

中文:
实例 :
  签名: 标量乘正递增 实数>=0 实数>=0∞
  定义体: _root_.mul_le_mul_left (coe_le_coe.2 hab) _

Depends on / 依赖: _root_, _root_.mul_le_mul_left, coe_le_coe, mul_le_mul_left
-/
instance : SMulPosMono Real>=0 Real>=0∞ where
  smul_le_smul_of_nonneg_right _r _ _a _b hab := _root_.mul_le_mul_left (coe_le_coe.2 hab) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedModule Real>=0 Real>=0∞
  body: inferInstance

中文:
实例 :
  签名: 是Ordered模 实数>=0 实数>=0∞
  定义体: inferInstance
-/
instance : IsOrderedModule Real>=0 Real>=0∞ where

example : CovariantClass Real>=0∞ Real>=0∞ (· • ·) (· <= ·) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedSMul Real>=0 Real>=0∞
  body: by gcongr
  smul_le_smul_right a b hab c := by gcongr

example : CovariantClass Real>=0 Real>=0∞ (· • ·) (· <= ·) := inferInstance

中文:
实例 :
  签名: 是OrderedSMul 实数>=0 实数>=0∞
  定义体: by gcongr
  smul_le_smul_right a b hab c := by gcongr

example : CovariantClass Real>=0 Real>=0∞ (· • ·) (· <= ·) := inferInstance

Depends on / 依赖: smul_le_smul_right
-/
instance : IsOrderedSMul Real>=0 Real>=0∞ where
  smul_le_smul_left a b hab c := by gcongr
  smul_le_smul_right a b hab c := by gcongr

example : CovariantClass Real>=0 Real>=0∞ (· • ·) (· <= ·) := inferInstance

end Actions

end ENNReal
