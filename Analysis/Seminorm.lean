/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
module

public import Mathlib.Algebra.Order.AddTorsor
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Real.Pointwise

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets, and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For a module over a normed ring:
* `Seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `normSeminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm, locally convex, LCTVS
-/

@[expose] public section

assert_not_exists balancedCore

open NormedField Set Filter

open scoped NNReal Pointwise Topology Uniformity

variable {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F ι : Type*}

/--
Definition of `Seminorm` / `Seminorm` 的定义

English:
structure Seminorm
  parameters: (𝕜 : Type*) (E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
  axioms and operations (1):
    - smul' : forall (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x

中文:
结构 半范数
  参数: (𝕜 : 类型) (E : 类型) [Seminormed环 𝕜] [加法群 E] [标量乘法 𝕜 E]
  公理与运算 (1 个):
    - smul' : 对任意 (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x
-/
structure Seminorm (𝕜 : Type*) (E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] extends
  AddGroupSeminorm E where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  smul' : forall (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x

attribute [nolint docBlame] Seminorm.toAddGroupSeminorm

/--
Definition of `SeminormClass` / `SeminormClass` 的定义

English:
class SeminormClass
  parameters: (F : Type*) (𝕜 E : outParam Type*) [SeminormedRing 𝕜] [AddGroup E]
  extends: AddGroupSeminormClass F E Real
  axioms and operations (1):
    - map_smul_eq_mul((f : F) (a : 𝕜) (x : E)) : f (a • x) = ‖a‖ * f x

中文:
类 半范数类
  参数: (F : 类型) (𝕜 E : outParam 类型) [Seminormed环 𝕜] [加法群 E]
  继承: 加法群半范数类 F E 实数
  公理与运算 (1 个):
    - map_smul_eq_mul((f : F) (a : 𝕜) (x : E)) : f (a • x) = ‖a‖ * f x
-/
class SeminormClass (F : Type*) (𝕜 E : outParam Type*) [SeminormedRing 𝕜] [AddGroup E]
  [SMul 𝕜 E] [FunLike F E Real] : Prop extends AddGroupSeminormClass F E Real where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  map_smul_eq_mul (f : F) (a : 𝕜) (x : E) : f (a • x) = ‖a‖ * f x

export SeminormClass (map_smul_eq_mul)

section Of

/--
Definition of `Seminorm.of` / `Seminorm.of` 的定义

English:
definition Seminorm.of
  signature: [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E -> Real)
  body: f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]

中文:
定义 半范数.of
  签名: [Seminormed环 𝕜] [加法交换群 E] [模 𝕜 E] (f : E -> 实数)
  定义体: f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]
-/
def Seminorm.of [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E -> Real)
    (add_le : forall x y : E, f (x + y) <= f x + f y) (smul : forall (a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x) :
    Seminorm 𝕜 E where
  toFun := f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]

/--
Definition of `Seminorm.ofSMulLE` / `Seminorm.ofSMulLE` 的定义

English:
definition Seminorm.ofSMulLE
  signature: [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E -> Real) (map_zero : f 0 = 0)
  body: Seminorm.of f add_le fun r x => by
    refine le_antisymm (smul_le r x) ?_
    by_cases h : r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] a

中文:
定义 半范数.ofSMulLE
  签名: [赋范域 𝕜] [加法交换群 E] [模 𝕜 E] (f : E -> 实数) (map_zero : f 0 = 0)
  定义体: Seminorm.of f add_le fun r x => by
    refine le_antisymm (smul_le r x) ?_
    by_cases h : r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] a

Depends on / 依赖: Seminorm, Seminorm.of, add_le, convert, inv_pos, inv_pos.mpr, le_antisymm, map_zero, norm_inv, norm_ne_zero_iff, norm_ne_zero_iff.mpr, norm_pos_iff, norm_pos_iff.mpr, smul_le, specialize
-/
def Seminorm.ofSMulLE [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E -> Real) (map_zero : f 0 = 0)
    (add_le : forall x y, f (x + y) <= f x + f y) (smul_le : forall (r : 𝕜) (x), f (r • x) <= ‖r‖ * f x) :
    Seminorm 𝕜 E :=
  Seminorm.of f add_le fun r x => by
    refine le_antisymm (smul_le r x) ?_
    by_cases h : r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] at smul_le
    convert! smul_le
    simp [h]

end Of

namespace Seminorm

section SeminormedRing

variable [SeminormedRing 𝕜]

section AddGroup

variable [AddGroup E]

section SMul

variable [SMul 𝕜 E]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Seminorm 𝕜 E) E Real where
  body: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_⟩⟩
    rcases g with ⟨⟨_⟩⟩
    congr

中文:
实例 instFunLike
  签名: : 函数状 (半范数 𝕜 E) E 实数 where
  定义体: f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_⟩⟩
    rcases g with ⟨⟨_⟩⟩
    congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (Seminorm 𝕜 E) E Real where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_⟩⟩
    rcases g with ⟨⟨_⟩⟩
    congr

/--
Instance `instSeminormClass` / 实例 `instSeminormClass`

English:
instance instSeminormClass
  signature: : SeminormClass (Seminorm 𝕜 E) 𝕜 E where
  body: f.map_zero'
  map_add_le_add f := f.add_le'
  map_neg_eq_map f := f.neg'
  map_smul_eq_mul f := f.smul'

@[ext]

中文:
实例 instSeminormClass
  签名: : 半范数类 (半范数 𝕜 E) 𝕜 E where
  定义体: f.map_zero'
  map_add_le_add f := f.add_le'
  map_neg_eq_map f := f.neg'
  map_smul_eq_mul f := f.smul'

@[ext]

Depends on / 依赖: f.map_zero, map_zero
-/
instance instSeminormClass : SeminormClass (Seminorm 𝕜 E) 𝕜 E where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_neg_eq_map f := f.neg'
  map_smul_eq_mul f := f.smul'

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x = q x)
  statement: p = q
  proof: DFunLike.ext p q h

中文:
定理 ext
  条件: {p q : 半范数 𝕜 E} (h : 对任意 x, (p : E -> 实数) x = q x)
  结论: p = q
  证明: DFunLike.ext p q h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x = q x) : p = q :=
  DFunLike.ext p q h

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (Seminorm 𝕜 E)
  body: ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with
    smul' := fun _ _ => (mul_zero _).symm }⟩

中文:
实例 instZero
  签名: : 零 (半范数 𝕜 E)
  定义体: ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with
    smul' := fun _ _ => (mul_zero _).symm }⟩

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.instZeroAddGroupSeminorm.zero, instZeroAddGroupSeminorm, mul_zero
-/
instance instZero : Zero (Seminorm 𝕜 E) :=
  ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with
    smul' := fun _ _ => (mul_zero _).symm }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (Seminorm 𝕜 E) E Real
  body: rfl

@[deprecated (since := "2026-06-22")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-22")] protected alias zero_apply := zero_apply

中文:
实例 :
  签名: 是ZeroApply (半范数 𝕜 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-06-22")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-22")] protected alias zero_apply := zero_apply
-/
instance : IsZeroApply (Seminorm 𝕜 E) E Real where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-22")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-22")] protected alias zero_apply := zero_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Seminorm 𝕜 E)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (半范数 𝕜 E)
  定义体: ⟨0⟩
-/
instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨0⟩

variable (p : Seminorm 𝕜 E) (x : E) (r : Real)

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real]
  body: { r • p.toAddGroupSeminorm with
      toFun := fun x => r • p x
      smul' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul]
        rw [map_smul_eq_mul]; rw [mul_left_comm] }

中文:
实例 instSMul
  签名: [标量乘法 R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数]
  定义体: { r • p.toAddGroupSeminorm with
      toFun := fun x => r • p x
      smul' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul]
        rw [map_smul_eq_mul]; rw [mul_left_comm] }

Depends on / 依赖: NNReal, NNReal.smul_def, map_smul_eq_mul, mul_left_comm, p.toAddGroupSeminorm, smul_def, smul_eq_mul, smul_one_smul, toAddGroupSeminorm
-/
instance instSMul [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] : SMul R (Seminorm 𝕜 E) where
  smul r p :=
    { r • p.toAddGroupSeminorm with
      toFun := fun x => r • p x
      smul' := fun _ _ => by
        simp only [← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def, smul_eq_mul]
        rw [map_smul_eq_mul]; rw [mul_left_comm] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] : IsSMulApply R (Seminorm 𝕜 E) E Real where
  body: rfl

中文:
实例 [标量乘法
  签名: R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数] : 是SMulApply R (半范数 𝕜 E) E 实数 where
  定义体: rfl
-/
instance [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] : IsSMulApply R (Seminorm 𝕜 E) E Real where
  smul_apply _ _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] [SMul R' Real] [SMul R' Real>=0]
  body: FunLike.isScalarTower

@[deprecated (since := "2026-06-22")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-22")] protected alias smul_apply := smul_apply

中文:
实例 [标量乘法
  签名: R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数] [标量乘法 R' 实数] [标量乘法 R' 实数>=0]
  定义体: FunLike.isScalarTower

@[deprecated (since := "2026-06-22")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-22")] protected alias smul_apply := smul_apply

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] [SMul R' Real] [SMul R' Real>=0]
    [IsScalarTower R' Real>=0 Real] [SMul R R'] [IsScalarTower R R' Real] :
    IsScalarTower R R' (Seminorm 𝕜 E) := FunLike.isScalarTower

@[deprecated (since := "2026-06-22")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-22")] protected alias smul_apply := smul_apply

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (Seminorm 𝕜 E) where
  body: { p.toAddGroupSeminorm + q.toAddGroupSeminorm with
      toFun := fun x => p x + q x
      smul' := fun a x => by simp only [map_smul_eq_mul, map_smul_eq_mul, mul_add] }

中文:
实例 instAdd
  签名: : 加法 (半范数 𝕜 E) where
  定义体: { p.toAddGroupSeminorm + q.toAddGroupSeminorm with
      toFun := fun x => p x + q x
      smul' := fun a x => by simp only [map_smul_eq_mul, map_smul_eq_mul, mul_add] }

Depends on / 依赖: map_smul_eq_mul, mul_add, p.toAddGroupSeminorm, q.toAddGroupSeminorm, toAddGroupSeminorm
-/
instance instAdd : Add (Seminorm 𝕜 E) where
  add p q :=
    { p.toAddGroupSeminorm + q.toAddGroupSeminorm with
      toFun := fun x => p x + q x
      smul' := fun a x => by simp only [map_smul_eq_mul, map_smul_eq_mul, mul_add] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (Seminorm 𝕜 E) E Real
  body: rfl

@[deprecated (since := "2026-06-22")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-22")] protected alias add_apply := add_apply

中文:
实例 :
  签名: 是加法Apply (半范数 𝕜 E) E 实数
  定义体: rfl

@[deprecated (since := "2026-06-22")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-22")] protected alias add_apply := add_apply
-/
instance : IsAddApply (Seminorm 𝕜 E) E Real where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-22")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-22")] protected alias add_apply := add_apply

/--
Instance `instAddMonoid` / 实例 `instAddMonoid`

English:
instance instAddMonoid
  signature: : AddMonoid (Seminorm 𝕜 E)
  body: fast_instance% FunLike.addMonoid

中文:
实例 instAddMonoid
  签名: : 加法幺半群 (半范数 𝕜 E)
  定义体: fast_instance% FunLike.addMonoid

Depends on / 依赖: FunLike, FunLike.addMonoid, addMonoid, fast_instance
-/
instance instAddMonoid : AddMonoid (Seminorm 𝕜 E) := fast_instance% FunLike.addMonoid

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (Seminorm 𝕜 E)
  body: fast_instance% FunLike.addCommMonoid

中文:
实例 instAddCommMonoid
  签名: : 加法交换幺半群 (半范数 𝕜 E)
  定义体: fast_instance% FunLike.addCommMonoid

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
instance instAddCommMonoid : AddCommMonoid (Seminorm 𝕜 E) := fast_instance% FunLike.addCommMonoid

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (Seminorm 𝕜 E)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 instPartialOrder
  签名: : 偏序 (半范数 𝕜 E)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance instPartialOrder : PartialOrder (Seminorm 𝕜 E) :=
  PartialOrder.lift _ DFunLike.coe_injective

/--
Instance `instIsOrderedCancelAddMonoid` / 实例 `instIsOrderedCancelAddMonoid`

English:
instance instIsOrderedCancelAddMonoid
  signature: : IsOrderedCancelAddMonoid (Seminorm 𝕜 E)
  body: Function.Injective.isOrderedCancelAddMonoid DFunLike.coe FunLike.coe_add .rfl

中文:
实例 instIsOrderedCancelAddMonoid
  签名: : 是OrderedCancelAdd幺半群 (半范数 𝕜 E)
  定义体: Function.Injective.isOrderedCancelAddMonoid DFunLike.coe FunLike.coe_add .rfl

Depends on / 依赖: DFunLike, DFunLike.coe, FunLike, FunLike.coe_add, Function, Function.Injective.isOrderedCancelAddMonoid, Injective, coe_add, isOrderedCancelAddMonoid
-/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid (Seminorm 𝕜 E) :=
  Function.Injective.isOrderedCancelAddMonoid DFunLike.coe FunLike.coe_add .rfl

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid R] [MulAction R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real]
  body: fast_instance% FunLike.mulAction

中文:
实例 instMulAction
  签名: [幺半群 R] [乘法作用 R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数]
  定义体: fast_instance% FunLike.mulAction

Depends on / 依赖: FunLike, FunLike.mulAction, fast_instance, mulAction
-/
instance instMulAction [Monoid R] [MulAction R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] :
    MulAction R (Seminorm 𝕜 E) := fast_instance% FunLike.mulAction

variable (𝕜 E)

@[deprecated (since := "2026-06-22")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-22")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-22")] alias coeFnAddMonoidHom_injective :=
  FunLike.coeAddMonoidHom_injective

variable {𝕜 E}

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid R] [DistribMulAction R Real] [SMul R Real>=0]
  body: fast_instance%
  FunLike.distribMulAction

中文:
实例 instDistribMulAction
  签名: [幺半群 R] [分配乘法作用 R 实数] [标量乘法 R 实数>=0]
  定义体: fast_instance%
  FunLike.distribMulAction

Depends on / 依赖: fast_instance
-/
instance instDistribMulAction [Monoid R] [DistribMulAction R Real] [SMul R Real>=0]
    [IsScalarTower R Real>=0 Real] : DistribMulAction R (Seminorm 𝕜 E) := fast_instance%
  FunLike.distribMulAction

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [Module R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real]
  body: fast_instance% FunLike.module

中文:
实例 instModule
  签名: [半环 R] [模 R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数]
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance instModule [Semiring R] [Module R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] :
    Module R (Seminorm 𝕜 E) := fast_instance% FunLike.module

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max (Seminorm 𝕜 E) where
  body: { p.toAddGroupSeminorm ⊔ q.toAddGroupSeminorm with
      toFun := p ⊔ q
      smul' := fun x v =>
(congr_arg₂ max (map_smul_eq_mul p x v) (map_smul_eq_mul q x v)).trans
          (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]

中文:
实例 instSup
  签名: : 最大值 (半范数 𝕜 E) where
  定义体: { p.toAddGroupSeminorm ⊔ q.toAddGroupSeminorm with
      toFun := p ⊔ q
      smul' := fun x v =>
(congr_arg₂ max (map_smul_eq_mul p x v) (map_smul_eq_mul q x v)).trans
          (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]

Depends on / 依赖: map_smul_eq_mul, mul_max_of_nonneg, norm_nonneg, p.toAddGroupSeminorm, q.toAddGroupSeminorm, toAddGroupSeminorm
-/
instance instSup : Max (Seminorm 𝕜 E) where
  max p q :=
    { p.toAddGroupSeminorm ⊔ q.toAddGroupSeminorm with
      toFun := p ⊔ q
      smul' := fun x v =>
(congr_arg₂ max (map_smul_eq_mul p x v) (map_smul_eq_mul q x v)).trans
          (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (p q : Seminorm 𝕜 E)
  statement: ⇑(p ⊔ q) = (p : E -> Real) ⊔ (q : E -> Real)
  proof: rfl

中文:
定理 coe_sup
  条件: (p q : 半范数 𝕜 E)
  结论: ⇑(p ⊔ q) = (p : E -> 实数) ⊔ (q : E -> 实数)
  证明: rfl
-/
theorem coe_sup (p q : Seminorm 𝕜 E) : ⇑(p ⊔ q) = (p : E -> Real) ⊔ (q : E -> Real) :=
  rfl

/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (p q : Seminorm 𝕜 E) (x : E)
  statement: (p ⊔ q) x = p x ⊔ q x
  proof: rfl

中文:
定理 sup_apply
  条件: (p q : 半范数 𝕜 E) (x : E)
  结论: (p ⊔ q) x = p x ⊔ q x
  证明: rfl

Depends on / 依赖: S.hom
-/
theorem sup_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  given: [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] (r : R) (p q : Seminorm 𝕜 E)
  proof: have real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => real.smul_max _ _

@[simp, norm_c

中文:
定理 smul_sup
  条件: [标量乘法 R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数] (r : R) (p q : 半范数 𝕜 E)
  证明: have real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => real.smul_max _ _

@[simp, norm_c

Depends on / 依赖: NNReal, NNReal.smul_def, coe_nonneg, mul_max_of_nonneg, real.smul_max, smul_def, smul_eq_mul, smul_max, smul_one_smul
-/
theorem smul_sup [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : forall x y : Real, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul Real>=0 r (_ : Real)] using
      mul_max_of_nonneg x y (r • (1 : Real>=0) : Real>=0).coe_nonneg
  ext fun _ => real.smul_max _ _

@[simp, norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: {p q : Seminorm 𝕜 E}
  statement: (p : E -> Real) <= q ↔ p <= q
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 coe_le_coe
  条件: {p q : 半范数 𝕜 E}
  结论: (p : E -> 实数) <= q ↔ p <= q
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe {p q : Seminorm 𝕜 E} : (p : E -> Real) <= q ↔ p <= q :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  given: {p q : Seminorm 𝕜 E}
  statement: (p : E -> Real) < q ↔ p < q
  proof: Iff.rfl

中文:
定理 coe_lt_coe
  条件: {p q : 半范数 𝕜 E}
  结论: (p : E -> 实数) < q ↔ p < q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe {p q : Seminorm 𝕜 E} : (p : E -> Real) < q ↔ p < q :=
  Iff.rfl

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {p q : Seminorm 𝕜 E}
  statement: p <= q ↔ forall x, p x <= q x
  proof: Iff.rfl

中文:
定理 le_def
  条件: {p q : 半范数 𝕜 E}
  结论: p <= q ↔ 对任意 x, p x <= q x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def {p q : Seminorm 𝕜 E} : p <= q ↔ forall x, p x <= q x :=
  Iff.rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: {p q : Seminorm 𝕜 E}
  statement: p < q ↔ p <= q ∧ exists x, p x < q x
  proof: @Pi.lt_def _ _ _ p q

中文:
定理 lt_def
  条件: {p q : 半范数 𝕜 E}
  结论: p < q ↔ p <= q ∧ 存在 x, p x < q x
  证明: @Pi.lt_def _ _ _ p q

Depends on / 依赖: Pi.lt_def, lt_def
-/
theorem lt_def {p q : Seminorm 𝕜 E} : p < q ↔ p <= q ∧ exists x, p x < q x :=
  @Pi.lt_def _ _ _ p q

/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: : SemilatticeSup (Seminorm 𝕜 E)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

中文:
实例 instSemilatticeSup
  签名: : SemilatticeSup (半范数 𝕜 E)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, coe_sup, semilatticeSup
-/
instance instSemilatticeSup : SemilatticeSup (Seminorm 𝕜 E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] [Preorder R] [Zero R]
  body: calc
    _ <= (c • (1 : Real>=0)) • p x := by simp
    _ <= _ := by grw [hpq x]; simp
  smul_le_smul_right a b hab p x := by
    grw [smul_apply, hab, smul_apply]

中文:
实例 [标量乘法
  签名: R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数] [预序 R] [零 R]
  定义体: calc
    _ <= (c • (1 : Real>=0)) • p x := by simp
    _ <= _ := by grw [hpq x]; simp
  smul_le_smul_right a b hab p x := by
    grw [smul_apply, hab, smul_apply]
-/
instance [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] [Preorder R] [Zero R]
    [IsOrderedModule R Real] : IsOrderedSMul R (Seminorm 𝕜 E) where
  smul_le_smul_left p q hpq c x := calc
    _ <= (c • (1 : Real>=0)) • p x := by simp
    _ <= _ := by grw [hpq x]; simp
  smul_le_smul_right a b hab p x := by
    grw [smul_apply, hab, smul_apply]

end SMul

end AddGroup

section Module

variable [SeminormedRing 𝕜₂] [SeminormedRing 𝕜₃]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]
variable {σ₂₃ : 𝕜₂ ->+* 𝕜₃} [RingHomIsometric σ₂₃]
variable {σ₁₃ : 𝕜 ->+* 𝕜₃} [RingHomIsometric σ₁₃]
variable [AddCommGroup E] [AddCommGroup E₂] [AddCommGroup E₃]
variable [Module 𝕜 E] [Module 𝕜₂ E₂] [Module 𝕜₃ E₃]
variable [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂)
  body: { p.toAddGroupSeminorm.comp f.toAddMonoidHom with
    toFun := fun x => p (f x)
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` to `map_smulₛₗ _`
    smul' _ _ := by simp only [map_smulₛₗ _, map_smul_eq_mul, RingHomIsometric.norm_map] }

中文:
定义 comp
  签名: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂)
  定义体: { p.toAddGroupSeminorm.comp f.toAddMonoidHom with
    toFun := fun x => p (f x)
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` to `map_smulₛₗ _`
    smul' _ _ := by simp only [map_smulₛₗ _, map_smul_eq_mul, RingHomIsometric.norm_map] }

Depends on / 依赖: f.toAddMonoidHom, p.toAddGroupSeminorm.comp, toAddGroupSeminorm, toAddMonoidHom
-/
def comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E :=
  { p.toAddGroupSeminorm.comp f.toAddMonoidHom with
    toFun := fun x => p (f x)
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` to `map_smulₛₗ _`
    smul' _ _ := by simp only [map_smulₛₗ _, map_smul_eq_mul, RingHomIsometric.norm_map] }

/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂)
  statement: ⇑(p.comp f) = p ∘ f
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂)
  结论: ⇑(p.comp f) = p ∘ f
  证明: rfl

@[simp]
-/
theorem coe_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) : ⇑(p.comp f) = p ∘ f :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E)
  statement: (p.comp f) x = p (f x)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E)
  结论: (p.comp f) x = p (f x)
  证明: rfl

@[simp]
-/
theorem comp_apply (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) : (p.comp f) x = p (f x) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (p : Seminorm 𝕜 E)
  statement: p.comp LinearMap.id = p
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (p : 半范数 𝕜 E)
  结论: p.comp 线性映射.id = p
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  given: (p : Seminorm 𝕜₂ E₂)
  statement: p.comp (0 : E ->ₛₗ[σ₁₂] E₂) = 0
  proof: ext fun _ => map_zero p

@[simp]

中文:
定理 comp_zero
  条件: (p : 半范数 𝕜₂ E₂)
  结论: p.comp (0 : E ->ₛₗ[σ₁₂] E₂) = 0
  证明: ext fun _ => map_zero p

@[simp]

Depends on / 依赖: map_zero
-/
theorem comp_zero (p : Seminorm 𝕜₂ E₂) : p.comp (0 : E ->ₛₗ[σ₁₂] E₂) = 0 :=
  ext fun _ => map_zero p

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: (f : E ->ₛₗ[σ₁₂] E₂)
  statement: (0 : Seminorm 𝕜₂ E₂).comp f = 0
  proof: ext fun _ => rfl

中文:
定理 zero_comp
  条件: (f : E ->ₛₗ[σ₁₂] E₂)
  结论: (0 : 半范数 𝕜₂ E₂).comp f = 0
  证明: ext fun _ => rfl
-/
theorem zero_comp (f : E ->ₛₗ[σ₁₂] E₂) : (0 : Seminorm 𝕜₂ E₂).comp f = 0 :=
  ext fun _ => rfl

/--
theorem `comp_comp` / 定理 `comp_comp`

English:
theorem comp_comp
  statement: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (p : Seminorm 𝕜₃ E₃) (g : E₂ ->ₛₗ[σ₂₃] E₃)
  proof: ext fun _ => rfl

中文:
定理 comp_comp
  结论: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (p : 半范数 𝕜₃ E₃) (g : E₂ ->ₛₗ[σ₂₃] E₃)
  证明: ext fun _ => rfl
-/
theorem comp_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (p : Seminorm 𝕜₃ E₃) (g : E₂ ->ₛₗ[σ₂₃] E₃)
    (f : E ->ₛₗ[σ₁₂] E₂) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

/--
theorem `add_comp` / 定理 `add_comp`

English:
theorem add_comp
  given: (p q : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂)
  proof: ext fun _ => rfl

中文:
定理 add_comp
  条件: (p q : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂)
  证明: ext fun _ => rfl
-/
theorem add_comp (p q : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) :
    (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

/--
theorem `comp_add_le` / 定理 `comp_add_le`

English:
theorem comp_add_le
  given: (p : Seminorm 𝕜₂ E₂) (f g : E ->ₛₗ[σ₁₂] E₂)
  proof: fun _ => map_add_le_add p _ _

中文:
定理 comp_add_le
  条件: (p : 半范数 𝕜₂ E₂) (f g : E ->ₛₗ[σ₁₂] E₂)
  证明: fun _ => map_add_le_add p _ _

Depends on / 依赖: map_add_le_add
-/
theorem comp_add_le (p : Seminorm 𝕜₂ E₂) (f g : E ->ₛₗ[σ₁₂] E₂) :
    p.comp (f + g) <= p.comp f + p.comp g := fun _ => map_add_le_add p _ _

/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  given: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : R)
  proof: ext fun _ => rfl

中文:
定理 smul_comp
  条件: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : R)
  证明: ext fun _ => rfl
-/
theorem smul_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : R) :
    (c • p).comp f = c • p.comp f :=
  ext fun _ => rfl

/--
theorem `comp_mono` / 定理 `comp_mono`

English:
theorem comp_mono
  given: {p q : Seminorm 𝕜₂ E₂} (f : E ->ₛₗ[σ₁₂] E₂) (hp : p <= q)
  statement: p.comp f <= q.comp f
  proof: fun _ => hp _

中文:
定理 comp_mono
  条件: {p q : 半范数 𝕜₂ E₂} (f : E ->ₛₗ[σ₁₂] E₂) (hp : p <= q)
  结论: p.comp f <= q.comp f
  证明: fun _ => hp _
-/
theorem comp_mono {p q : Seminorm 𝕜₂ E₂} (f : E ->ₛₗ[σ₁₂] E₂) (hp : p <= q) : p.comp f <= q.comp f :=
  fun _ => hp _

/-- The composition as an `AddMonoidHom`. -/
@[simps]
/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (f : E ->ₛₗ[σ₁₂] E₂)
  body: fun p => p.comp f
  map_zero' := zero_comp f
  map_add' := fun p q => add_comp p q f

中文:
定义 pullback
  签名: (f : E ->ₛₗ[σ₁₂] E₂)
  定义体: fun p => p.comp f
  map_zero' := zero_comp f
  map_add' := fun p q => add_comp p q f

Depends on / 依赖: p.comp
-/
def pullback (f : E ->ₛₗ[σ₁₂] E₂) : Seminorm 𝕜₂ E₂ ->+ Seminorm 𝕜 E where
  toFun := fun p => p.comp f
  map_zero' := zero_comp f
  map_add' := fun p q => add_comp p q f

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot (Seminorm 𝕜 E) where
  body: 0
  bot_le := apply_nonneg

@[simp]

中文:
实例 instOrderBot
  签名: : 有底序 (半范数 𝕜 E) where
  定义体: 0
  bot_le := apply_nonneg

@[simp]
-/
instance instOrderBot : OrderBot (Seminorm 𝕜 E) where
  bot := 0
  bot_le := apply_nonneg

@[simp]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ⇑(⊥ : Seminorm 𝕜 E) = 0
  proof: rfl

中文:
定理 coe_bot
  结论: ⇑(⊥ : 半范数 𝕜 E) = 0
  证明: rfl
-/
theorem coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : Seminorm 𝕜 E) = 0
  proof: rfl

@[deprecated IsOrderedSMul.smul_le_smul (since := "2026-07-31")]

中文:
定理 bot_eq_zero
  结论: (⊥ : 半范数 𝕜 E) = 0
  证明: rfl

@[deprecated IsOrderedSMul.smul_le_smul (since := "2026-07-31")]
-/
theorem bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

@[deprecated IsOrderedSMul.smul_le_smul (since := "2026-07-31")]
/--
theorem `smul_le_smul` / 定理 `smul_le_smul`

English:
theorem smul_le_smul
  given: {p q : Seminorm 𝕜 E} {a b : Real>=0} (hpq : p <= q) (hab : a <= b)
  proof: by
  simp_rw [le_def]
  intro x
  exact mul_le_mul hab (hpq x) (apply_nonneg p x) (NNReal.coe_nonneg b)

中文:
定理 smul_le_smul
  条件: {p q : 半范数 𝕜 E} {a b : 实数>=0} (hpq : p <= q) (hab : a <= b)
  证明: by
  simp_rw [le_def]
  intro x
  exact mul_le_mul hab (hpq x) (apply_nonneg p x) (NNReal.coe_nonneg b)
-/
protected theorem smul_le_smul {p q : Seminorm 𝕜 E} {a b : Real>=0} (hpq : p <= q) (hab : a <= b) :
    a • p <= b • q := by
  simp_rw [le_def]
  intro x
  exact mul_le_mul hab (hpq x) (apply_nonneg p x) (NNReal.coe_nonneg b)

/--
theorem `finset_sup_apply` / 定理 `finset_sup_apply`

English:
theorem finset_sup_apply
  given: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E)
  proof: by
  induction s using Finset.cons_induction_on with
  | empty =>
    rw [Finset.sup_empty]; rw [Finset.sup_empty]; rw [coe_bot]; rw [_root_.bot_eq_zero]; rw [Pi.zero_apply]
    norm_cast
  | cons a s ha ih =>
    rw [Finset.sup_cons]; rw [Finset.sup_cons]; rw [coe_sup]; rw [Pi.sup_apply]; rw [NNRea

中文:
定理 finset_sup_apply
  条件: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (x : E)
  证明: by
  induction s using Finset.cons_induction_on with
  | empty =>
    rw [Finset.sup_empty]; rw [Finset.sup_empty]; rw [coe_bot]; rw [_root_.bot_eq_zero]; rw [Pi.zero_apply]
    norm_cast
  | cons a s ha ih =>
    rw [Finset.sup_cons]; rw [Finset.sup_cons]; rw [coe_sup]; rw [Pi.sup_apply]; rw [NNRea

Depends on / 依赖: Finset, Finset.cons_induction_on, Finset.sup_cons, Finset.sup_empty, NNReal, NNReal.coe_max, NNReal.coe_mk, Pi.sup_apply, Pi.zero_apply, _root_, _root_.bot_eq_zero, bot_eq_zero, coe_bot, coe_max, coe_mk, coe_sup, cons_induction_on, sup_apply, sup_cons, sup_empty
-/
theorem finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonneg (p i) x)) := by
  induction s using Finset.cons_induction_on with
  | empty =>
    rw [Finset.sup_empty]; rw [Finset.sup_empty]; rw [coe_bot]; rw [_root_.bot_eq_zero]; rw [Pi.zero_apply]
    norm_cast
  | cons a s ha ih =>
    rw [Finset.sup_cons]; rw [Finset.sup_cons]; rw [coe_sup]; rw [Pi.sup_apply]; rw [NNReal.coe_max]; rw [NNReal.coe_mk]; rw [ih]

/--
theorem `exists_apply_eq_finset_sup` / 定理 `exists_apply_eq_finset_sup`

English:
theorem exists_apply_eq_finset_sup
  given: (p : ι -> Seminorm 𝕜 E) {s : Finset ι} (hs : s.Nonempty) (x : E)
  proof: by
  rcases Finset.exists_mem_eq_sup s hs (fun i => (⟨p i x, apply_nonneg _ _⟩ : Real>=0)) with ⟨i, hi, hix⟩
  rw [finset_sup_apply]
  exact ⟨i, hi, congr_arg _ hix⟩

中文:
定理 存在_apply_eq_finset_sup
  条件: (p : ι -> 半范数 𝕜 E) {s : 有限集 ι} (hs : s.非空) (x : E)
  证明: by
  rcases Finset.exists_mem_eq_sup s hs (fun i => (⟨p i x, apply_nonneg _ _⟩ : Real>=0)) with ⟨i, hi, hix⟩
  rw [finset_sup_apply]
  exact ⟨i, hi, congr_arg _ hix⟩

Depends on / 依赖: Finset, Finset.exists_mem_eq_sup, apply_nonneg, congr_arg, exists_mem_eq_sup, finset_sup_apply
-/
theorem exists_apply_eq_finset_sup (p : ι -> Seminorm 𝕜 E) {s : Finset ι} (hs : s.Nonempty) (x : E) :
    exists i in s, s.sup p x = p i x := by
  rcases Finset.exists_mem_eq_sup s hs (fun i => (⟨p i x, apply_nonneg _ _⟩ : Real>=0)) with ⟨i, hi, hix⟩
  rw [finset_sup_apply]
  exact ⟨i, hi, congr_arg _ hix⟩

/--
theorem `zero_or_exists_apply_eq_finset_sup` / 定理 `zero_or_exists_apply_eq_finset_sup`

English:
theorem zero_or_exists_apply_eq_finset_sup
  given: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E)
  proof: by
  rcases Finset.eq_empty_or_nonempty s with (rfl | hs)
  · left; rfl
  · right; exact exists_apply_eq_finset_sup p hs x

中文:
定理 zero_or_存在_apply_eq_finset_sup
  条件: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (x : E)
  证明: by
  rcases Finset.eq_empty_or_nonempty s with (rfl | hs)
  · left; rfl
  · right; exact exists_apply_eq_finset_sup p hs x

Depends on / 依赖: Finset, Finset.eq_empty_or_nonempty, eq_empty_or_nonempty, exists_apply_eq_finset_sup
-/
theorem zero_or_exists_apply_eq_finset_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = 0 ∨ exists i in s, s.sup p x = p i x := by
  rcases Finset.eq_empty_or_nonempty s with (rfl | hs)
  · left; rfl
  · right; exact exists_apply_eq_finset_sup p hs x

/--
theorem `finset_sup_smul` / 定理 `finset_sup_smul`

English:
theorem finset_sup_smul
  given: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (C : Real>=0)
  proof: by
  ext x
  rw [smul_apply]; rw [finset_sup_apply]; rw [finset_sup_apply]
  symm
  exact congr_arg ((↑) : Real>=0 -> Real) (NNReal.mul_finset_sup C s (fun i => ⟨p i x, apply_nonneg _ _⟩))

中文:
定理 finset_sup_smul
  条件: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (C : 实数>=0)
  证明: by
  ext x
  rw [smul_apply]; rw [finset_sup_apply]; rw [finset_sup_apply]
  symm
  exact congr_arg ((↑) : Real>=0 -> Real) (NNReal.mul_finset_sup C s (fun i => ⟨p i x, apply_nonneg _ _⟩))

Depends on / 依赖: NNReal, NNReal.mul_finset_sup, apply_nonneg, congr_arg, finset_sup_apply, mul_finset_sup, smul_apply
-/
theorem finset_sup_smul (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (C : Real>=0) :
    s.sup (C • p) = C • s.sup p := by
  ext x
  rw [smul_apply]; rw [finset_sup_apply]; rw [finset_sup_apply]
  symm
  exact congr_arg ((↑) : Real>=0 -> Real) (NNReal.mul_finset_sup C s (fun i => ⟨p i x, apply_nonneg _ _⟩))

/--
theorem `finset_sup_le_sum` / 定理 `finset_sup_le_sum`

English:
theorem finset_sup_le_sum
  given: (p : ι -> Seminorm 𝕜 E) (s : Finset ι)
  statement: s.sup p <= ∑ i in s, p i
  proof: by
  classical
  refine Finset.sup_le_iff.mpr ?_
  intro i hi
  rw [Finset.sum_eq_sum_sdiff_singleton_add hi]; rw [le_add_iff_nonneg_left]
  exact bot_le

中文:
定理 finset_sup_le_sum
  条件: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι)
  结论: s.上确界 p <= ∑ i in s, p i
  证明: by
  classical
  refine Finset.sup_le_iff.mpr ?_
  intro i hi
  rw [Finset.sum_eq_sum_sdiff_singleton_add hi]; rw [le_add_iff_nonneg_left]
  exact bot_le

Depends on / 依赖: Finset, Finset.sum_eq_sum_sdiff_singleton_add, Finset.sup_le_iff.mpr, bot_le, classical, le_add_iff_nonneg_left, sum_eq_sum_sdiff_singleton_add, sup_le_iff
-/
theorem finset_sup_le_sum (p : ι -> Seminorm 𝕜 E) (s : Finset ι) : s.sup p <= ∑ i in s, p i := by
  classical
  refine Finset.sup_le_iff.mpr ?_
  intro i hi
  rw [Finset.sum_eq_sum_sdiff_singleton_add hi]; rw [le_add_iff_nonneg_left]
  exact bot_le

/--
theorem `finset_sup_apply_le` / 定理 `finset_sup_apply_le`

English:
theorem finset_sup_apply_le
  statement: {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : Real} (ha : 0 <= a)
  proof: by
  lift a to Real>=0 using ha
  rw [finset_sup_apply]; rw [NNReal.coe_le_coe]
  exact Finset.sup_le h

中文:
定理 finset_sup_apply_le
  结论: {p : ι -> 半范数 𝕜 E} {s : 有限集 ι} {x : E} {a : 实数} (ha : 0 <= a)
  证明: by
  lift a to Real>=0 using ha
  rw [finset_sup_apply]; rw [NNReal.coe_le_coe]
  exact Finset.sup_le h

Depends on / 依赖: Finset, Finset.sup_le, NNReal, NNReal.coe_le_coe, coe_le_coe, finset_sup_apply, sup_le
-/
theorem finset_sup_apply_le {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : Real} (ha : 0 <= a)
    (h : forall i, i in s -> p i x <= a) : s.sup p x <= a := by
  lift a to Real>=0 using ha
  rw [finset_sup_apply]; rw [NNReal.coe_le_coe]
  exact Finset.sup_le h

/--
theorem `le_finset_sup_apply` / 定理 `le_finset_sup_apply`

English:
theorem le_finset_sup_apply
  statement: {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {i : ι}
  proof: (Finset.le_sup hi : p i <= s.sup p) x

中文:
定理 le_finset_sup_apply
  结论: {p : ι -> 半范数 𝕜 E} {s : 有限集 ι} {x : E} {i : ι}
  证明: (Finset.le_sup hi : p i <= s.sup p) x

Depends on / 依赖: Finset, Finset.le_sup, le_sup, s.sup
-/
theorem le_finset_sup_apply {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {i : ι}
    (hi : i in s) : p i x <= s.sup p x :=
  (Finset.le_sup hi : p i <= s.sup p) x

/--
theorem `finset_sup_apply_lt` / 定理 `finset_sup_apply_lt`

English:
theorem finset_sup_apply_lt
  statement: {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : Real} (ha : 0 < a)
  proof: by
  lift a to Real>=0 using ha.le
  rw [finset_sup_apply]; rw [NNReal.coe_lt_coe]; rw [Finset.sup_lt_iff]
  · exact h
  · exact NNReal.coe_pos.mpr ha

中文:
定理 finset_sup_apply_lt
  结论: {p : ι -> 半范数 𝕜 E} {s : 有限集 ι} {x : E} {a : 实数} (ha : 0 < a)
  证明: by
  lift a to Real>=0 using ha.le
  rw [finset_sup_apply]; rw [NNReal.coe_lt_coe]; rw [Finset.sup_lt_iff]
  · exact h
  · exact NNReal.coe_pos.mpr ha

Depends on / 依赖: Finset, Finset.sup_lt_iff, NNReal, NNReal.coe_lt_coe, NNReal.coe_pos.mpr, coe_lt_coe, coe_pos, finset_sup_apply, ha.le, sup_lt_iff
-/
theorem finset_sup_apply_lt {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : Real} (ha : 0 < a)
    (h : forall i, i in s -> p i x < a) : s.sup p x < a := by
  lift a to Real>=0 using ha.le
  rw [finset_sup_apply]; rw [NNReal.coe_lt_coe]; rw [Finset.sup_lt_iff]
  · exact h
  · exact NNReal.coe_pos.mpr ha

/--
theorem `norm_sub_map_le_sub` / 定理 `norm_sub_map_le_sub`

English:
theorem norm_sub_map_le_sub
  given: (p : Seminorm 𝕜 E) (x y : E)
  statement: ‖p x - p y‖ <= p (x - y)
  proof: abs_sub_map_le_sub p x y

中文:
定理 norm_sub_map_le_sub
  条件: (p : 半范数 𝕜 E) (x y : E)
  结论: ‖p x - p y‖ <= p (x - y)
  证明: abs_sub_map_le_sub p x y

Depends on / 依赖: abs_sub_map_le_sub
-/
theorem norm_sub_map_le_sub (p : Seminorm 𝕜 E) (x y : E) : ‖p x - p y‖ <= p (x - y) :=
  abs_sub_map_le_sub p x y

end Module

end SeminormedRing

section SeminormedCommRing

variable [SeminormedRing 𝕜] [SeminormedCommRing 𝕜₂]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]
variable [AddCommGroup E] [AddCommGroup E₂] [Module 𝕜 E] [Module 𝕜₂ E₂]

/--
theorem `comp_smul` / 定理 `comp_smul`

English:
theorem comp_smul
  given: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂)
  proof: by
  ext; simp [NNReal.smul_def, map_smul_eq_mul]

中文:
定理 comp_smul
  条件: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂)
  证明: by
  ext; simp [NNReal.smul_def, map_smul_eq_mul]

Depends on / 依赖: NNReal, NNReal.smul_def, map_smul_eq_mul, smul_def
-/
theorem comp_smul (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂) :
    p.comp (c • f) = ‖c‖₊ • p.comp f := by
  ext; simp [NNReal.smul_def, map_smul_eq_mul]

/--
theorem `comp_smul_apply` / 定理 `comp_smul_apply`

English:
theorem comp_smul_apply
  given: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E)
  proof: map_smul_eq_mul p _ _

中文:
定理 comp_smul_apply
  条件: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E)
  证明: map_smul_eq_mul p _ _

Depends on / 依赖: map_smul_eq_mul
-/
theorem comp_smul_apply (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E) :
    p.comp (c • f) x = ‖c‖ * p (f x) :=
  map_smul_eq_mul p _ _

end SeminormedCommRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {p q : Seminorm 𝕜 E} {x : E}

/--
theorem `bddBelow_range_add` / 定理 `bddBelow_range_add`

English:
theorem bddBelow_range_add
  statement: BddBelow (range fun u => p u + q (x - u))
  proof: ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp; positivity⟩

中文:
定理 bddBelow_range_add
  结论: BddBelow (range fun u => p u + q (x - u))
  证明: ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp; positivity⟩
-/
theorem bddBelow_range_add : BddBelow (range fun u => p u + q (x - u)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp; positivity⟩

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (Seminorm 𝕜 E) where
  body: { p.toAddGroupSeminorm ⊓ q.toAddGroupSeminorm with
      toFun := fun x => ⨅ u : E, p u + q (x - u)
      smul' := by
        intro a x
        obtain rfl | ha := eq_or_ne a 0
        · rw [norm_zero, zero_mul, zero_smul]
          refine
            ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
    

中文:
实例 instInf
  签名: : 最小值 (半范数 𝕜 E) where
  定义体: { p.toAddGroupSeminorm ⊓ q.toAddGroupSeminorm with
      toFun := fun x => ⨅ u : E, p u + q (x - u)
      smul' := by
        intro a x
        obtain rfl | ha := eq_or_ne a 0
        · rw [norm_zero, zero_mul, zero_smul]
          refine
            ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
    

Depends on / 依赖: Function, Function.Surjective.iInf_congr, Real.mul_iInf_of_nonneg, Surjective, add_zero, ciInf_eq_of_forall_ge_of_forall_gt_exists_lt, eq_or_ne, iInf_congr, map_smul_eq_mul, map_zero, mul_add, mul_iInf_of_nonneg, norm_nonneg, norm_zero, p.toAddGroupSeminorm, q.toAddGroupSeminorm, simp_rw, smul_sub, sub_zero, toAddGroupSeminorm
-/
noncomputable instance instInf : Min (Seminorm 𝕜 E) where
  min p q :=
    { p.toAddGroupSeminorm ⊓ q.toAddGroupSeminorm with
      toFun := fun x => ⨅ u : E, p u + q (x - u)
      smul' := by
        intro a x
        obtain rfl | ha := eq_or_ne a 0
        · rw [norm_zero, zero_mul, zero_smul]
          refine
            ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
              (fun i => by positivity)
              fun x hx => ⟨0, by rwa [map_zero, sub_zero, map_zero, add_zero]⟩
        simp_rw [Real.mul_iInf_of_nonneg (norm_nonneg a), mul_add, ← map_smul_eq_mul p, ←
          map_smul_eq_mul q, smul_sub]
        refine
          Function.Surjective.iInf_congr ((a⁻¹ • ·) : E -> E)
            (fun u => ⟨a • u, inv_smul_smul₀ ha u⟩) fun u => ?_
        rw [smul_inv_smul₀ ha] }

@[simp]
/--
theorem `inf_apply` / 定理 `inf_apply`

English:
theorem inf_apply
  given: (p q : Seminorm 𝕜 E) (x : E)
  statement: (p ⊓ q) x = ⨅ u : E, p u + q (x - u)
  proof: rfl

中文:
定理 inf_apply
  条件: (p q : 半范数 𝕜 E) (x : E)
  结论: (p ⊓ q) x = ⨅ u : E, p u + q (x - u)
  证明: rfl
-/
theorem inf_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊓ q) x = ⨅ u : E, p u + q (x - u) :=
  rfl

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: : Lattice (Seminorm 𝕜 E)
  body: { Seminorm.instSemilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
ciInf_le_of_le bddBelow_range_add x by
        simp only [sub_self, map_zero, add_zero]; rfl
    inf_le_right := fun p q x =>
ciInf_le_of_le bddBelow_range_add 0 by
        simp only [map_zero, zero_add, sub_zero];

中文:
实例 instLattice
  签名: : 格 (半范数 𝕜 E)
  定义体: { Seminorm.instSemilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
ciInf_le_of_le bddBelow_range_add x by
        simp only [sub_self, map_zero, add_zero]; rfl
    inf_le_right := fun p q x =>
ciInf_le_of_le bddBelow_range_add 0 by
        simp only [map_zero, zero_add, sub_zero];

Depends on / 依赖: Seminorm, Seminorm.instSemilatticeSup, add_le_add, add_zero, bddBelow_range_add, ciInf_le_of_le, inf_le_left, inf_le_right, instSemilatticeSup, le_ciInf, le_inf, le_map_add_map_sub, map_zero, sub_self, sub_zero, zero_add
-/
noncomputable instance instLattice : Lattice (Seminorm 𝕜 E) :=
  { Seminorm.instSemilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
ciInf_le_of_le bddBelow_range_add x by
        simp only [sub_self, map_zero, add_zero]; rfl
    inf_le_right := fun p q x =>
ciInf_le_of_le bddBelow_range_add 0 by
        simp only [map_zero, zero_add, sub_zero]; rfl
    le_inf := fun a _ _ hab hac _ =>
le_ciInf fun _ => (le_map_add_map_sub a _ _).trans add_le_add (hab _) (hac _) }

/--
theorem `smul_inf` / 定理 `smul_inf`

English:
theorem smul_inf
  given: [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] (r : R) (p q : Seminorm 𝕜 E)
  proof: by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def,
    smul_eq_mul, Real.mul_iInf_of_nonneg (NNReal.coe_nonneg _), mul_add]

中文:
定理 smul_inf
  条件: [标量乘法 R 实数] [标量乘法 R 实数>=0] [标量塔 R 实数>=0 实数] (r : R) (p q : 半范数 𝕜 E)
  证明: by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def,
    smul_eq_mul, Real.mul_iInf_of_nonneg (NNReal.coe_nonneg _), mul_add]

Depends on / 依赖: NNReal, NNReal.coe_nonneg, NNReal.smul_def, Real.mul_iInf_of_nonneg, coe_nonneg, inf_apply, mul_add, mul_iInf_of_nonneg, simp_rw, smul_apply, smul_def, smul_eq_mul, smul_one_smul
-/
theorem smul_inf [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊓ q) = r • p ⊓ r • q := by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul Real>=0 r (_ : Real), NNReal.smul_def,
    smul_eq_mul, Real.mul_iInf_of_nonneg (NNReal.coe_nonneg _), mul_add]

section Classical

open scoped Classical in
/--
Instance `instSupSet` / 实例 `instSupSet`

English:
instance instSupSet
  signature: : SupSet (Seminorm 𝕜 E) where
  body: if h : BddAbove ((↑) '' s : Set (E -> Real)) then
      { toFun := ⨆ p : s, ((p : Seminorm 𝕜 E) : E -> Real)
        map_zero' := by
          rw [iSup_apply]; rw [← @Real.iSup_const_zero s]
          congr!
          rename_i _ _ _ i
          exact map_zero i.1
        add_le' := fun x y => by
   

中文:
实例 instSupSet
  签名: : 上确界集 (半范数 𝕜 E) where
  定义体: if h : BddAbove ((↑) '' s : Set (E -> Real)) then
      { toFun := ⨆ p : s, ((p : Seminorm 𝕜 E) : E -> Real)
        map_zero' := by
          rw [iSup_apply]; rw [← @Real.iSup_const_zero s]
          congr!
          rename_i _ _ _ i
          exact map_zero i.1
        add_le' := fun x y => by
   

Depends on / 依赖: BddAbove, Nonempty, Real.iSup_const_zero, Real.iSup_of_isEmpty, Seminorm, add_le, add_le_add, ciSup_le, coe_sort, eq_empty_or_nonempty, h.coe_sort, iSup_apply, iSup_const_zero, iSup_of_isEmpty, map_zero, rename_i, s.eq_empty_or_nonempty
-/
noncomputable instance instSupSet : SupSet (Seminorm 𝕜 E) where
  sSup s :=
    if h : BddAbove ((↑) '' s : Set (E -> Real)) then
      { toFun := ⨆ p : s, ((p : Seminorm 𝕜 E) : E -> Real)
        map_zero' := by
          rw [iSup_apply]; rw [← @Real.iSup_const_zero s]
          congr!
          rename_i _ _ _ i
          exact map_zero i.1
        add_le' := fun x y => by
          rcases h with ⟨q, hq⟩
          obtain rfl | h := s.eq_empty_or_nonempty
          · simp [Real.iSup_of_isEmpty]
          have : Nonempty ↑s := h.coe_sort
          simp only [iSup_apply]
          refine ciSup_le fun i =>
((i : Seminorm 𝕜 E).add_le' x y).trans add_le_add
              -- Porting note: `f` is provided to force `Subtype.val` to appear.
              -- A type ascription on `_` would have also worked, but would have been more verbose.
              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun x) ⟨q x, ?_⟩ i)
              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun y) ⟨q y, ?_⟩ i)
          <;> rw [mem_upperBounds, forall_mem_range]
          <;> exact fun j => hq (mem_image_of_mem _ j.2) _
        neg' := fun x => by
          simp only [iSup_apply]
          congr! 2
          rename_i _ _ _ i
          exact i.1.neg' _
        smul' := fun a x => by
          simp only [iSup_apply]
          rw [← smul_eq_mul]; rw [Real.smul_iSup_of_nonneg (norm_nonneg a) fun i : s => (i : Seminorm 𝕜 E) x]
          congr!
          rename_i _ _ _ i
          exact i.1.smul' a x }
    else ⊥

/--
theorem `coe_sSup_eq'` / 定理 `coe_sSup_eq'`

English:
theorem coe_sSup_eq'
  statement: {s : Set <| Seminorm 𝕜 E}
  proof: congr_arg _ (dif_pos hs)

中文:
定理 coe_sSup_eq'
  结论: {s : 集合 <| 半范数 𝕜 E}
  证明: congr_arg _ (dif_pos hs)
-/
protected theorem coe_sSup_eq' {s : Set <| Seminorm 𝕜 E}
    (hs : BddAbove ((↑) '' s : Set (E -> Real))) : ↑(sSup s) = ⨆ p : s, ((p : Seminorm 𝕜 E) : E -> Real) :=
  congr_arg _ (dif_pos hs)

/--
theorem `bddAbove_iff` / 定理 `bddAbove_iff`

English:
theorem bddAbove_iff
  given: {s : Set <| Seminorm 𝕜 E}
  proof: ⟨fun ⟨q, hq⟩ => ⟨q, forall_mem_image.2 fun _ hp => hq hp⟩, fun H =>
    ⟨sSup s, fun p hp x => by
      dsimp
      rw [Seminorm.coe_sSup_eq' H]; rw [iSup_apply]
      rcases H with ⟨q, hq⟩
      exact
        le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩⟩⟩

中文:
定理 bddAbove_iff
  条件: {s : 集合 <| 半范数 𝕜 E}
  证明: ⟨fun ⟨q, hq⟩ => ⟨q, forall_mem_image.2 fun _ hp => hq hp⟩, fun H =>
    ⟨sSup s, fun p hp x => by
      dsimp
      rw [Seminorm.coe_sSup_eq' H]; rw [iSup_apply]
      rcases H with ⟨q, hq⟩
      exact
        le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩⟩⟩
-/
protected theorem bddAbove_iff {s : Set <| Seminorm 𝕜 E} :
    BddAbove s ↔ BddAbove ((↑) '' s : Set (E -> Real)) :=
  ⟨fun ⟨q, hq⟩ => ⟨q, forall_mem_image.2 fun _ hp => hq hp⟩, fun H =>
    ⟨sSup s, fun p hp x => by
      dsimp
      rw [Seminorm.coe_sSup_eq' H]; rw [iSup_apply]
      rcases H with ⟨q, hq⟩
      exact
        le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩⟩⟩

/--
theorem `bddAbove_range_iff` / 定理 `bddAbove_range_iff`

English:
theorem bddAbove_range_iff
  given: {ι : Sort*} {p : ι -> Seminorm 𝕜 E}
  proof: by
  rw [Seminorm.bddAbove_iff]; rw [← range_comp]; rw [bddAbove_range_pi]; rfl

中文:
定理 bddAbove_range_iff
  条件: {ι : 类型层*} {p : ι -> 半范数 𝕜 E}
  证明: by
  rw [Seminorm.bddAbove_iff]; rw [← range_comp]; rw [bddAbove_range_pi]; rfl
-/
protected theorem bddAbove_range_iff {ι : Sort*} {p : ι -> Seminorm 𝕜 E} :
    BddAbove (range p) ↔ forall x, BddAbove (range fun i => p i x) := by
  rw [Seminorm.bddAbove_iff]; rw [← range_comp]; rw [bddAbove_range_pi]; rfl

/--
theorem `coe_sSup_eq` / 定理 `coe_sSup_eq`

English:
theorem coe_sSup_eq
  given: {s : Set <| Seminorm 𝕜 E} (hs : BddAbove s)
  proof: Seminorm.coe_sSup_eq' (Seminorm.bddAbove_iff.mp hs)

中文:
定理 coe_sSup_eq
  条件: {s : 集合 <| 半范数 𝕜 E} (hs : BddAbove s)
  证明: Seminorm.coe_sSup_eq' (Seminorm.bddAbove_iff.mp hs)
-/
protected theorem coe_sSup_eq {s : Set <| Seminorm 𝕜 E} (hs : BddAbove s) :
    ↑(sSup s) = ⨆ p : s, ((p : Seminorm 𝕜 E) : E -> Real) :=
  Seminorm.coe_sSup_eq' (Seminorm.bddAbove_iff.mp hs)

/--
theorem `coe_iSup_eq` / 定理 `coe_iSup_eq`

English:
theorem coe_iSup_eq
  given: {ι : Sort*} {p : ι -> Seminorm 𝕜 E} (hp : BddAbove (range p))
  proof: by
  rw [← sSup_range]; rw [Seminorm.coe_sSup_eq hp]
  exact iSup_range' (fun p : Seminorm 𝕜 E => (p : E -> Real)) p

中文:
定理 coe_iSup_eq
  条件: {ι : 类型层*} {p : ι -> 半范数 𝕜 E} (hp : BddAbove (range p))
  证明: by
  rw [← sSup_range]; rw [Seminorm.coe_sSup_eq hp]
  exact iSup_range' (fun p : Seminorm 𝕜 E => (p : E -> Real)) p
-/
protected theorem coe_iSup_eq {ι : Sort*} {p : ι -> Seminorm 𝕜 E} (hp : BddAbove (range p)) :
    ↑(⨆ i, p i) = ⨆ i, ((p i : Seminorm 𝕜 E) : E -> Real) := by
  rw [← sSup_range]; rw [Seminorm.coe_sSup_eq hp]
  exact iSup_range' (fun p : Seminorm 𝕜 E => (p : E -> Real)) p

/--
theorem `sSup_apply` / 定理 `sSup_apply`

English:
theorem sSup_apply
  given: {s : Set (Seminorm 𝕜 E)} (hp : BddAbove s) {x : E}
  proof: by
  rw [Seminorm.coe_sSup_eq hp]; rw [iSup_apply]

中文:
定理 sSup_apply
  条件: {s : 集合 (半范数 𝕜 E)} (hp : BddAbove s) {x : E}
  证明: by
  rw [Seminorm.coe_sSup_eq hp]; rw [iSup_apply]
-/
protected theorem sSup_apply {s : Set (Seminorm 𝕜 E)} (hp : BddAbove s) {x : E} :
    (sSup s) x = ⨆ p : s, (p : E -> Real) x := by
  rw [Seminorm.coe_sSup_eq hp]; rw [iSup_apply]

/--
theorem `iSup_apply` / 定理 `iSup_apply`

English:
theorem iSup_apply
  statement: {ι : Sort*} {p : ι -> Seminorm 𝕜 E}
  proof: by
  rw [Seminorm.coe_iSup_eq hp]; rw [iSup_apply]

中文:
定理 iSup_apply
  结论: {ι : 类型层*} {p : ι -> 半范数 𝕜 E}
  证明: by
  rw [Seminorm.coe_iSup_eq hp]; rw [iSup_apply]
-/
protected theorem iSup_apply {ι : Sort*} {p : ι -> Seminorm 𝕜 E}
    (hp : BddAbove (range p)) {x : E} : (⨆ i, p i) x = ⨆ i, p i x := by
  rw [Seminorm.coe_iSup_eq hp]; rw [iSup_apply]

/--
theorem `sSup_empty` / 定理 `sSup_empty`

English:
theorem sSup_empty
  statement: sSup (∅ : Set (Seminorm 𝕜 E)) = ⊥
  proof: by
  ext
  rw [Seminorm.sSup_apply bddAbove_empty]; rw [Real.iSup_of_isEmpty]
  rfl

中文:
定理 sSup_empty
  结论: sSup (∅ : 集合 (半范数 𝕜 E)) = ⊥
  证明: by
  ext
  rw [Seminorm.sSup_apply bddAbove_empty]; rw [Real.iSup_of_isEmpty]
  rfl
-/
protected theorem sSup_empty : sSup (∅ : Set (Seminorm 𝕜 E)) = ⊥ := by
  ext
  rw [Seminorm.sSup_apply bddAbove_empty]; rw [Real.iSup_of_isEmpty]
  rfl

set_option backward.privateInPublic true in
/--
theorem `isLUB_sSup` / 定理 `isLUB_sSup`

English:
theorem isLUB_sSup
  given: (s : Set (Seminorm 𝕜 E)) (hs₁ : BddAbove s) (hs₂ : s.Nonempty)
  proof: by
  refine ⟨fun p hp x => ?_, fun p hp x => ?_⟩ <;> have : Nonempty ↑s := hs₂.coe_sort <;>
    dsimp <;> rw [Seminorm.coe_sSup_eq hs₁, iSup_apply]
  · rcases hs₁ with ⟨q, hq⟩
    exact le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq i.2 x⟩ ⟨p, hp⟩
  · exact ciSup_le fun q => hp q.2 x

中文:
定理 isLUB_sSup
  条件: (s : 集合 (半范数 𝕜 E)) (hs₁ : BddAbove s) (hs₂ : s.非空)
  证明: by
  refine ⟨fun p hp x => ?_, fun p hp x => ?_⟩ <;> have : Nonempty ↑s := hs₂.coe_sort <;>
    dsimp <;> rw [Seminorm.coe_sSup_eq hs₁, iSup_apply]
  · rcases hs₁ with ⟨q, hq⟩
    exact le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq i.2 x⟩ ⟨p, hp⟩
  · exact ciSup_le fun q => hp q.2 x
-/
private theorem isLUB_sSup (s : Set (Seminorm 𝕜 E)) (hs₁ : BddAbove s) (hs₂ : s.Nonempty) :
    IsLUB s (sSup s) := by
  refine ⟨fun p hp x => ?_, fun p hp x => ?_⟩ <;> have : Nonempty ↑s := hs₂.coe_sort <;>
    dsimp <;> rw [Seminorm.coe_sSup_eq hs₁, iSup_apply]
  · rcases hs₁ with ⟨q, hq⟩
    exact le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq i.2 x⟩ ⟨p, hp⟩
  · exact ciSup_le fun q => hp q.2 x

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instConditionallyCompleteLattice` / 实例 `instConditionallyCompleteLattice`

English:
instance instConditionallyCompleteLattice
  signature: :
  body: conditionallyCompleteLatticeOfLatticeOfsSup (Seminorm 𝕜 E) Seminorm.isLUB_sSup

中文:
实例 instConditionallyCompleteLattice
  签名: :
  定义体: conditionallyCompleteLatticeOfLatticeOfsSup (Seminorm 𝕜 E) Seminorm.isLUB_sSup

Depends on / 依赖: Seminorm, Seminorm.isLUB_sSup, conditionallyCompleteLatticeOfLatticeOfsSup, isLUB_sSup
-/
noncomputable instance instConditionallyCompleteLattice :
    ConditionallyCompleteLattice (Seminorm 𝕜 E) :=
  conditionallyCompleteLatticeOfLatticeOfsSup (Seminorm 𝕜 E) Seminorm.isLUB_sSup

end Classical

end NormedField

/-! ### Seminorm ball -/


section SeminormedRing

variable [SeminormedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E]

section SMul

variable [SMul 𝕜 E] (p : Seminorm 𝕜 E)

/--
Definition of `ball` / `ball` 的定义

English:
definition ball
  signature: (x : E) (r : Real)
  body: { y : E | p (y - x) < r }

中文:
定义 ball
  签名: (x : E) (r : 实数)
  定义体: { y : E | p (y - x) < r }
-/
def ball (x : E) (r : Real) :=
  { y : E | p (y - x) < r }

/--
Definition of `closedBall` / `closedBall` 的定义

English:
definition closedBall
  signature: (x : E) (r : Real)
  body: { y : E | p (y - x) <= r }

中文:
定义 closedBall
  签名: (x : E) (r : 实数)
  定义体: { y : E | p (y - x) <= r }

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory.category, category
-/
def closedBall (x : E) (r : Real) :=
  { y : E | p (y - x) <= r }

variable {x y : E} {r : Real}

@[simp]
/--
theorem `mem_ball` / 定理 `mem_ball`

English:
theorem mem_ball
  statement: y in ball p x r ↔ p (y - x) < r
  proof: Iff.rfl

@[simp]

中文:
定理 mem_ball
  结论: y in ball p x r ↔ p (y - x) < r
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_ball : y in ball p x r ↔ p (y - x) < r :=
  Iff.rfl

@[simp]
/--
theorem `mem_closedBall` / 定理 `mem_closedBall`

English:
theorem mem_closedBall
  statement: y in closedBall p x r ↔ p (y - x) <= r
  proof: Iff.rfl

中文:
定理 mem_closedBall
  结论: y in closedBall p x r ↔ p (y - x) <= r
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_closedBall : y in closedBall p x r ↔ p (y - x) <= r :=
  Iff.rfl

/--
theorem `mem_ball_self` / 定理 `mem_ball_self`

English:
theorem mem_ball_self
  given: (hr : 0 < r)
  statement: x in ball p x r
  proof: by simp [hr]

中文:
定理 mem_ball_self
  条件: (hr : 0 < r)
  结论: x in ball p x r
  证明: by simp [hr]

Depends on / 依赖: ObjectProperty, ObjectProperty.full_
-/
theorem mem_ball_self (hr : 0 < r) : x in ball p x r := by simp [hr]

/--
theorem `mem_closedBall_self` / 定理 `mem_closedBall_self`

English:
theorem mem_closedBall_self
  given: (hr : 0 <= r)
  statement: x in closedBall p x r
  proof: by simp [hr]

中文:
定理 mem_closedBall_self
  条件: (hr : 0 <= r)
  结论: x in closedBall p x r
  证明: by simp [hr]

Depends on / 依赖: ObjectProperty, ObjectProperty.faithful_
-/
theorem mem_closedBall_self (hr : 0 <= r) : x in closedBall p x r := by simp [hr]

/--
theorem `mem_ball_zero` / 定理 `mem_ball_zero`

English:
theorem mem_ball_zero
  statement: y in ball p 0 r ↔ p y < r
  proof: by rw [mem_ball, sub_zero]

中文:
定理 mem_ball_zero
  结论: y in ball p 0 r ↔ p y < r
  证明: by rw [mem_ball, sub_zero]

Depends on / 依赖: mem_ball, sub_zero
-/
theorem mem_ball_zero : y in ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]

/--
theorem `mem_closedBall_zero` / 定理 `mem_closedBall_zero`

English:
theorem mem_closedBall_zero
  statement: y in closedBall p 0 r ↔ p y <= r
  proof: by rw [mem_closedBall, sub_zero]

中文:
定理 mem_closedBall_zero
  结论: y in closedBall p 0 r ↔ p y <= r
  证明: by rw [mem_closedBall, sub_zero]

Depends on / 依赖: mem_closedBall, sub_zero
-/
theorem mem_closedBall_zero : y in closedBall p 0 r ↔ p y <= r := by rw [mem_closedBall, sub_zero]

/--
theorem `ball_zero_eq` / 定理 `ball_zero_eq`

English:
theorem ball_zero_eq
  statement: ball p 0 r = { y : E | p y < r }
  proof: Set.ext fun _ => p.mem_ball_zero

中文:
定理 ball_zero_eq
  结论: ball p 0 r = { y : E | p y < r }
  证明: Set.ext fun _ => p.mem_ball_zero

Depends on / 依赖: Set.ext, mem_ball_zero, p.mem_ball_zero
-/
theorem ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
  Set.ext fun _ => p.mem_ball_zero

/--
theorem `closedBall_zero_eq` / 定理 `closedBall_zero_eq`

English:
theorem closedBall_zero_eq
  statement: closedBall p 0 r = { y : E | p y <= r }
  proof: Set.ext fun _ => p.mem_closedBall_zero

中文:
定理 closedBall_zero_eq
  结论: closedBall p 0 r = { y : E | p y <= r }
  证明: Set.ext fun _ => p.mem_closedBall_zero

Depends on / 依赖: Set.ext, mem_closedBall_zero, p.mem_closedBall_zero
-/
theorem closedBall_zero_eq : closedBall p 0 r = { y : E | p y <= r } :=
  Set.ext fun _ => p.mem_closedBall_zero

/--
theorem `ball_subset_closedBall` / 定理 `ball_subset_closedBall`

English:
theorem ball_subset_closedBall
  given: (x r)
  statement: ball p x r subseteq closedBall p x r
  proof: fun _ h =>
  (mem_closedBall _).mpr ((mem_ball _).mp h).le

中文:
定理 ball_subset_closedBall
  条件: (x r)
  结论: ball p x r subseteq closedBall p x r
  证明: fun _ h =>
  (mem_closedBall _).mpr ((mem_ball _).mp h).le
-/
theorem ball_subset_closedBall (x r) : ball p x r subseteq closedBall p x r := fun _ h =>
  (mem_closedBall _).mpr ((mem_ball _).mp h).le

/--
theorem `closedBall_eq_biInter_ball` / 定理 `closedBall_eq_biInter_ball`

English:
theorem closedBall_eq_biInter_ball
  given: (x r)
  statement: closedBall p x r = ⋂ ρ > r, ball p x ρ
  proof: by
  ext y; simp_rw [mem_closedBall, mem_iInter₂, mem_ball, ← forall_gt_iff_le]

@[simp]

中文:
定理 closedBall_eq_bi整数er_ball
  条件: (x r)
  结论: closedBall p x r = ⋂ ρ > r, ball p x ρ
  证明: by
  ext y; simp_rw [mem_closedBall, mem_iInter₂, mem_ball, ← forall_gt_iff_le]

@[simp]

Depends on / 依赖: forall_gt_iff_le, mem_ball, mem_closedBall, simp_rw
-/
theorem closedBall_eq_biInter_ball (x r) : closedBall p x r = ⋂ ρ > r, ball p x ρ := by
  ext y; simp_rw [mem_closedBall, mem_iInter₂, mem_ball, ← forall_gt_iff_le]

@[simp]
/--
theorem `ball_zero'` / 定理 `ball_zero'`

English:
theorem ball_zero'
  given: (x : E) (hr : 0 < r)
  statement: ball (0 : Seminorm 𝕜 E) x r = Set.univ
  proof: by
  rw [Set.eq_univ_iff_forall]; rw [ball]
  simp [hr]

@[simp]

中文:
定理 ball_zero'
  条件: (x : E) (hr : 0 < r)
  结论: ball (0 : 半范数 𝕜 E) x r = 集合.univ
  证明: by
  rw [Set.eq_univ_iff_forall]; rw [ball]
  simp [hr]

@[simp]

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall
-/
theorem ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminorm 𝕜 E) x r = Set.univ := by
  rw [Set.eq_univ_iff_forall]; rw [ball]
  simp [hr]

@[simp]
/--
theorem `closedBall_zero'` / 定理 `closedBall_zero'`

English:
theorem closedBall_zero'
  given: (x : E) (hr : 0 < r)
  statement: closedBall (0 : Seminorm 𝕜 E) x r = Set.univ
  proof: eq_univ_of_subset (ball_subset_closedBall _ _ _) (ball_zero' x hr)

中文:
定理 closedBall_zero'
  条件: (x : E) (hr : 0 < r)
  结论: closedBall (0 : 半范数 𝕜 E) x r = 集合.univ
  证明: eq_univ_of_subset (ball_subset_closedBall _ _ _) (ball_zero' x hr)

Depends on / 依赖: ball_subset_closedBall, ball_zero, eq_univ_of_subset
-/
theorem closedBall_zero' (x : E) (hr : 0 < r) : closedBall (0 : Seminorm 𝕜 E) x r = Set.univ :=
  eq_univ_of_subset (ball_subset_closedBall _ _ _) (ball_zero' x hr)

/--
theorem `ball_smul` / 定理 `ball_smul`

English:
theorem ball_smul
  given: (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : Real) (x : E)
  proof: by
  ext
  rw [mem_ball]; rw [mem_ball]; rw [smul_apply]; rw [NNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm]; rw [lt_div_iff₀ (NNReal.coe_pos.mpr hc)]

中文:
定理 ball_smul
  条件: (p : 半范数 𝕜 E) {c : 非负实数} (hc : 0 < c) (r : 实数) (x : E)
  证明: by
  ext
  rw [mem_ball]; rw [mem_ball]; rw [smul_apply]; rw [NNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm]; rw [lt_div_iff₀ (NNReal.coe_pos.mpr hc)]

Depends on / 依赖: NNReal, NNReal.coe_pos.mpr, NNReal.smul_def, coe_pos, mem_ball, mul_comm, smul_apply, smul_def, smul_eq_mul
-/
theorem ball_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : Real) (x : E) :
    (c • p).ball x r = p.ball x (r / c) := by
  ext
  rw [mem_ball]; rw [mem_ball]; rw [smul_apply]; rw [NNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm]; rw [lt_div_iff₀ (NNReal.coe_pos.mpr hc)]

/--
theorem `closedBall_smul` / 定理 `closedBall_smul`

English:
theorem closedBall_smul
  given: (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : Real) (x : E)
  proof: by
  ext
  rw [mem_closedBall]; rw [mem_closedBall]; rw [smul_apply]; rw [NNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm]; rw [le_div_iff₀ (NNReal.coe_pos.mpr hc)]

中文:
定理 closedBall_smul
  条件: (p : 半范数 𝕜 E) {c : 非负实数} (hc : 0 < c) (r : 实数) (x : E)
  证明: by
  ext
  rw [mem_closedBall]; rw [mem_closedBall]; rw [smul_apply]; rw [NNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm]; rw [le_div_iff₀ (NNReal.coe_pos.mpr hc)]

Depends on / 依赖: NNReal, NNReal.coe_pos.mpr, NNReal.smul_def, coe_pos, mem_closedBall, mul_comm, smul_apply, smul_def, smul_eq_mul
-/
theorem closedBall_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : Real) (x : E) :
    (c • p).closedBall x r = p.closedBall x (r / c) := by
  ext
  rw [mem_closedBall]; rw [mem_closedBall]; rw [smul_apply]; rw [NNReal.smul_def]; rw [smul_eq_mul]; rw [mul_comm]; rw [le_div_iff₀ (NNReal.coe_pos.mpr hc)]

/--
theorem `ball_sup` / 定理 `ball_sup`

English:
theorem ball_sup
  given: (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : Real)
  proof: by
  simp_rw [ball, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_lt_iff]

中文:
定理 ball_sup
  条件: (p : 半范数 𝕜 E) (q : 半范数 𝕜 E) (e : E) (r : 实数)
  证明: by
  simp_rw [ball, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_lt_iff]

Depends on / 依赖: Pi.sup_apply, Set.ofPred_and, coe_sup, ofPred_and, simp_rw, sup_apply, sup_lt_iff
-/
theorem ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : Real) :
    ball (p ⊔ q) e r = ball p e r inter ball q e r := by
  simp_rw [ball, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_lt_iff]

/--
theorem `closedBall_sup` / 定理 `closedBall_sup`

English:
theorem closedBall_sup
  given: (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : Real)
  proof: by
  simp_rw [closedBall, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_le_iff]

中文:
定理 closedBall_sup
  条件: (p : 半范数 𝕜 E) (q : 半范数 𝕜 E) (e : E) (r : 实数)
  证明: by
  simp_rw [closedBall, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_le_iff]

Depends on / 依赖: Pi.sup_apply, Set.ofPred_and, closedBall, coe_sup, ofPred_and, simp_rw, sup_apply, sup_le_iff
-/
theorem closedBall_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : Real) :
    closedBall (p ⊔ q) e r = closedBall p e r inter closedBall q e r := by
  simp_rw [closedBall, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_le_iff]

/--
theorem `ball_finset_sup'` / 定理 `ball_finset_sup'`

English:
theorem ball_finset_sup'
  given: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E) (r : Real)
  proof: by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]

中文:
定理 ball_finset_sup'
  条件: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (H : s.非空) (e : E) (r : 实数)
  证明: by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.inf, Finset.sup, Nonempty, _cons, ball_sup, cons_induction, inf_eq_inter, singleton
-/
theorem ball_finset_sup' (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E) (r : Real) :
    ball (s.sup' H p) e r = s.inf' H fun i => ball (p i) e r := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]

/--
theorem `closedBall_finset_sup'` / 定理 `closedBall_finset_sup'`

English:
theorem closedBall_finset_sup'
  statement: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E)
  proof: by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, closedBall_sup, inf_eq_inter, ih]

@[gcongr]

中文:
定理 closedBall_finset_sup'
  结论: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (H : s.非空) (e : E)
  证明: by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, closedBall_sup, inf_eq_inter, ih]

@[gcongr]

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Finset.inf, Finset.sup, Nonempty, _cons, closedBall_sup, cons_induction, inf_eq_inter, singleton
-/
theorem closedBall_finset_sup' (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E)
    (r : Real) : closedBall (s.sup' H p) e r = s.inf' H fun i => closedBall (p i) e r := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, closedBall_sup, inf_eq_inter, ih]

@[gcongr]
/--
theorem `ball_mono` / 定理 `ball_mono`

English:
theorem ball_mono
  given: {p : Seminorm 𝕜 E} {r₁ r₂ : Real} (h : r₁ <= r₂)
  statement: p.ball x r₁ subseteq p.ball x r₂
  proof: fun _ (hx : _ < _) => hx.trans_le h

@[gcongr]

中文:
定理 ball_mono
  条件: {p : 半范数 𝕜 E} {r₁ r₂ : 实数} (h : r₁ <= r₂)
  结论: p.ball x r₁ subseteq p.ball x r₂
  证明: fun _ (hx : _ < _) => hx.trans_le h

@[gcongr]

Depends on / 依赖: hx.trans_le, trans_le
-/
theorem ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : Real} (h : r₁ <= r₂) : p.ball x r₁ subseteq p.ball x r₂ :=
  fun _ (hx : _ < _) => hx.trans_le h

@[gcongr]
/--
theorem `closedBall_mono` / 定理 `closedBall_mono`

English:
theorem closedBall_mono
  given: {p : Seminorm 𝕜 E} {r₁ r₂ : Real} (h : r₁ <= r₂)
  proof: fun _ (hx : _ <= _) => hx.trans h

中文:
定理 closedBall_mono
  条件: {p : 半范数 𝕜 E} {r₁ r₂ : 实数} (h : r₁ <= r₂)
  证明: fun _ (hx : _ <= _) => hx.trans h

Depends on / 依赖: hx.trans
-/
theorem closedBall_mono {p : Seminorm 𝕜 E} {r₁ r₂ : Real} (h : r₁ <= r₂) :
    p.closedBall x r₁ subseteq p.closedBall x r₂ := fun _ (hx : _ <= _) => hx.trans h

/--
theorem `ball_antitone` / 定理 `ball_antitone`

English:
theorem ball_antitone
  given: {p q : Seminorm 𝕜 E} (h : q <= p)
  statement: p.ball x r subseteq q.ball x r
  proof: fun _ =>
  (h _).trans_lt

中文:
定理 ball_antitone
  条件: {p q : 半范数 𝕜 E} (h : q <= p)
  结论: p.ball x r subseteq q.ball x r
  证明: fun _ =>
  (h _).trans_lt
-/
theorem ball_antitone {p q : Seminorm 𝕜 E} (h : q <= p) : p.ball x r subseteq q.ball x r := fun _ =>
  (h _).trans_lt

/--
theorem `closedBall_antitone` / 定理 `closedBall_antitone`

English:
theorem closedBall_antitone
  given: {p q : Seminorm 𝕜 E} (h : q <= p)
  proof: fun _ => (h _).trans

中文:
定理 closedBall_antitone
  条件: {p q : 半范数 𝕜 E} (h : q <= p)
  证明: fun _ => (h _).trans
-/
theorem closedBall_antitone {p q : Seminorm 𝕜 E} (h : q <= p) :
    p.closedBall x r subseteq q.closedBall x r := fun _ => (h _).trans

/--
theorem `ball_add_ball_subset` / 定理 `ball_add_ball_subset`

English:
theorem ball_add_ball_subset
  given: (p : Seminorm 𝕜 E) (r₁ r₂ : Real) (x₁ x₂ : E)
  proof: by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_ball]; rw [add_sub_add_comm]
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂)

中文:
定理 ball_add_ball_subset
  条件: (p : 半范数 𝕜 E) (r₁ r₂ : 实数) (x₁ x₂ : E)
  证明: by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_ball]; rw [add_sub_add_comm]
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂)

Depends on / 依赖: add_lt_add, add_sub_add_comm, map_add_le_add, mem_ball, trans_lt
-/
theorem ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : Real) (x₁ x₂ : E) :
    p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ subseteq p.ball (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_ball]; rw [add_sub_add_comm]
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂)

/--
theorem `closedBall_add_closedBall_subset` / 定理 `closedBall_add_closedBall_subset`

English:
theorem closedBall_add_closedBall_subset
  given: (p : Seminorm 𝕜 E) (r₁ r₂ : Real) (x₁ x₂ : E)
  proof: by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_closedBall]; rw [add_sub_add_comm]
  exact (map_add_le_add p _ _).trans (add_le_add hy₁ hy₂)

中文:
定理 closedBall_add_closedBall_subset
  条件: (p : 半范数 𝕜 E) (r₁ r₂ : 实数) (x₁ x₂ : E)
  证明: by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_closedBall]; rw [add_sub_add_comm]
  exact (map_add_le_add p _ _).trans (add_le_add hy₁ hy₂)

Depends on / 依赖: add_le_add, add_sub_add_comm, map_add_le_add, mem_closedBall
-/
theorem closedBall_add_closedBall_subset (p : Seminorm 𝕜 E) (r₁ r₂ : Real) (x₁ x₂ : E) :
    p.closedBall (x₁ : E) r₁ + p.closedBall (x₂ : E) r₂ subseteq p.closedBall (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_closedBall]; rw [add_sub_add_comm]
  exact (map_add_le_add p _ _).trans (add_le_add hy₁ hy₂)

/--
theorem `sub_mem_ball` / 定理 `sub_mem_ball`

English:
theorem sub_mem_ball
  given: (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : Real)
  proof: by simp_rw [mem_ball, sub_sub]

中文:
定理 sub_mem_ball
  条件: (p : 半范数 𝕜 E) (x₁ x₂ y : E) (r : 实数)
  证明: by simp_rw [mem_ball, sub_sub]

Depends on / 依赖: mem_ball, simp_rw, sub_sub
-/
theorem sub_mem_ball (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : Real) :
    x₁ - x₂ in p.ball y r ↔ x₁ in p.ball (x₂ + y) r := by simp_rw [mem_ball, sub_sub]

/--
theorem `sub_mem_closedBall` / 定理 `sub_mem_closedBall`

English:
theorem sub_mem_closedBall
  given: (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : Real)
  proof: by
  simp_rw [mem_closedBall, sub_sub]

中文:
定理 sub_mem_closedBall
  条件: (p : 半范数 𝕜 E) (x₁ x₂ y : E) (r : 实数)
  证明: by
  simp_rw [mem_closedBall, sub_sub]

Depends on / 依赖: mem_closedBall, simp_rw, sub_sub
-/
theorem sub_mem_closedBall (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : Real) :
    x₁ - x₂ in p.closedBall y r ↔ x₁ in p.closedBall (x₂ + y) r := by
  simp_rw [mem_closedBall, sub_sub]

/--
lemma `ball_eq_metric` / 引理 `ball_eq_metric`

English:
lemma ball_eq_metric
  proof: AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.ball x r = Metric.ball x r := by
  ext
  simp only [mem_ball_iff_norm]
  rfl

中文:
引理 ball_eq_metric
  证明: AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.ball x r = Metric.ball x r := by
  ext
  simp only [mem_ball_iff_norm]
  rfl

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toSeminormedAddCommGroup, p.toAddGroupSeminorm, toAddGroupSeminorm, toSeminormedAddCommGroup
-/
lemma ball_eq_metric :
    letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.ball x r = Metric.ball x r := by
  ext
  simp only [mem_ball_iff_norm]
  rfl

/--
lemma `closedBall_eq_metric` / 引理 `closedBall_eq_metric`

English:
lemma closedBall_eq_metric
  proof: AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.closedBall x r = Metric.closedBall x r := by
  ext
  simp only [mem_closedBall_iff_norm]
  rfl

中文:
引理 closedBall_eq_metric
  证明: AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.closedBall x r = Metric.closedBall x r := by
  ext
  simp only [mem_closedBall_iff_norm]
  rfl

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toSeminormedAddCommGroup, p.toAddGroupSeminorm, toAddGroupSeminorm, toSeminormedAddCommGroup
-/
lemma closedBall_eq_metric :
    letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.closedBall x r = Metric.closedBall x r := by
  ext
  simp only [mem_closedBall_iff_norm]
  rfl

/--
theorem `vadd_ball` / 定理 `vadd_ball`

English:
theorem vadd_ball
  given: (p : Seminorm 𝕜 E)
  statement: x +ᵥ p.ball y r = p.ball (x +ᵥ y) r
  proof: by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [ball_eq_metric]

中文:
定理 vadd_ball
  条件: (p : 半范数 𝕜 E)
  结论: x +ᵥ p.ball y r = p.ball (x +ᵥ y) r
  证明: by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [ball_eq_metric]

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toSeminormedAddCommGroup, ball_eq_metric, p.toAddGroupSeminorm, toAddGroupSeminorm, toSeminormedAddCommGroup
-/
theorem vadd_ball (p : Seminorm 𝕜 E) : x +ᵥ p.ball y r = p.ball (x +ᵥ y) r := by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [ball_eq_metric]

/--
theorem `vadd_closedBall` / 定理 `vadd_closedBall`

English:
theorem vadd_closedBall
  given: (p : Seminorm 𝕜 E)
  statement: x +ᵥ p.closedBall y r = p.closedBall (x +ᵥ y) r
  proof: by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [closedBall_eq_metric]

中文:
定理 vadd_closedBall
  条件: (p : 半范数 𝕜 E)
  结论: x +ᵥ p.closedBall y r = p.closedBall (x +ᵥ y) r
  证明: by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [closedBall_eq_metric]

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toSeminormedAddCommGroup, closedBall_eq_metric, p.toAddGroupSeminorm, toAddGroupSeminorm, toSeminormedAddCommGroup
-/
theorem vadd_closedBall (p : Seminorm 𝕜 E) : x +ᵥ p.closedBall y r = p.closedBall (x +ᵥ y) r := by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [closedBall_eq_metric]

end SMul

section Module

variable [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup E₂] [Module 𝕜₂ E₂]
variable {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]

/--
theorem `ball_comp` / 定理 `ball_comp`

English:
theorem ball_comp
  given: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : Real)
  proof: by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]

中文:
定理 ball_comp
  条件: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : 实数)
  证明: by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]

Depends on / 依赖: Set.mem_ofPred_eq, comp_apply, map_sub, mem_ofPred_eq, mem_preimage, simp_rw
-/
theorem ball_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : Real) :
    (p.comp f).ball x r = f ⁻¹' p.ball (f x) r := by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]

/--
theorem `closedBall_comp` / 定理 `closedBall_comp`

English:
theorem closedBall_comp
  given: (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : Real)
  proof: by
  ext
  simp_rw [closedBall, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]

中文:
定理 closedBall_comp
  条件: (p : 半范数 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : 实数)
  证明: by
  ext
  simp_rw [closedBall, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]

Depends on / 依赖: Set.mem_ofPred_eq, closedBall, comp_apply, map_sub, mem_ofPred_eq, mem_preimage, simp_rw
-/
theorem closedBall_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : Real) :
    (p.comp f).closedBall x r = f ⁻¹' p.closedBall (f x) r := by
  ext
  simp_rw [closedBall, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]

variable (p : Seminorm 𝕜 E)

/--
theorem `preimage_metric_ball` / 定理 `preimage_metric_ball`

English:
theorem preimage_metric_ball
  given: {r : Real}
  statement: p ⁻¹' Metric.ball 0 r = { x | p x < r }
  proof: by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_ball_zero_iff, Real.norm_of_nonneg (apply_nonneg p _)]

中文:
定理 preimage_metric_ball
  条件: {r : 实数}
  结论: p ⁻¹' Metric.ball 0 r = { x | p x < r }
  证明: by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_ball_zero_iff, Real.norm_of_nonneg (apply_nonneg p _)]

Depends on / 依赖: Real.norm_of_nonneg, apply_nonneg, mem_ball_zero_iff, mem_ofPred, mem_preimage, norm_of_nonneg
-/
theorem preimage_metric_ball {r : Real} : p ⁻¹' Metric.ball 0 r = { x | p x < r } := by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_ball_zero_iff, Real.norm_of_nonneg (apply_nonneg p _)]

/--
theorem `preimage_metric_closedBall` / 定理 `preimage_metric_closedBall`

English:
theorem preimage_metric_closedBall
  given: {r : Real}
  statement: p ⁻¹' Metric.closedBall 0 r = { x | p x <= r }
  proof: by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_closedBall_zero_iff,
    Real.norm_of_nonneg (apply_nonneg p _)]

中文:
定理 preimage_metric_closedBall
  条件: {r : 实数}
  结论: p ⁻¹' Metric.closedBall 0 r = { x | p x <= r }
  证明: by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_closedBall_zero_iff,
    Real.norm_of_nonneg (apply_nonneg p _)]

Depends on / 依赖: Real.norm_of_nonneg, apply_nonneg, mem_closedBall_zero_iff, mem_ofPred, mem_preimage, norm_of_nonneg
-/
theorem preimage_metric_closedBall {r : Real} : p ⁻¹' Metric.closedBall 0 r = { x | p x <= r } := by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_closedBall_zero_iff,
    Real.norm_of_nonneg (apply_nonneg p _)]

/--
theorem `ball_zero_eq_preimage_ball` / 定理 `ball_zero_eq_preimage_ball`

English:
theorem ball_zero_eq_preimage_ball
  given: {r : Real}
  statement: p.ball 0 r = p ⁻¹' Metric.ball 0 r
  proof: by
  rw [ball_zero_eq]; rw [preimage_metric_ball]

中文:
定理 ball_zero_eq_preimage_ball
  条件: {r : 实数}
  结论: p.ball 0 r = p ⁻¹' Metric.ball 0 r
  证明: by
  rw [ball_zero_eq]; rw [preimage_metric_ball]

Depends on / 依赖: ball_zero_eq, preimage_metric_ball
-/
theorem ball_zero_eq_preimage_ball {r : Real} : p.ball 0 r = p ⁻¹' Metric.ball 0 r := by
  rw [ball_zero_eq]; rw [preimage_metric_ball]

/--
theorem `closedBall_zero_eq_preimage_closedBall` / 定理 `closedBall_zero_eq_preimage_closedBall`

English:
theorem closedBall_zero_eq_preimage_closedBall
  given: {r : Real}
  proof: by
  rw [closedBall_zero_eq]; rw [preimage_metric_closedBall]

@[simp]

中文:
定理 closedBall_zero_eq_preimage_closedBall
  条件: {r : 实数}
  证明: by
  rw [closedBall_zero_eq]; rw [preimage_metric_closedBall]

@[simp]

Depends on / 依赖: closedBall_zero_eq, preimage_metric_closedBall
-/
theorem closedBall_zero_eq_preimage_closedBall {r : Real} :
    p.closedBall 0 r = p ⁻¹' Metric.closedBall 0 r := by
  rw [closedBall_zero_eq]; rw [preimage_metric_closedBall]

@[simp]
/--
theorem `ball_bot` / 定理 `ball_bot`

English:
theorem ball_bot
  given: {r : Real} (x : E) (hr : 0 < r)
  statement: ball (⊥ : Seminorm 𝕜 E) x r = Set.univ
  proof: ball_zero' x hr

@[simp]

中文:
定理 ball_bot
  条件: {r : 实数} (x : E) (hr : 0 < r)
  结论: ball (⊥ : 半范数 𝕜 E) x r = 集合.univ
  证明: ball_zero' x hr

@[simp]

Depends on / 依赖: ball_zero
-/
theorem ball_bot {r : Real} (x : E) (hr : 0 < r) : ball (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  ball_zero' x hr

@[simp]
/--
theorem `closedBall_bot` / 定理 `closedBall_bot`

English:
theorem closedBall_bot
  given: {r : Real} (x : E) (hr : 0 < r)
  proof: closedBall_zero' x hr

中文:
定理 closedBall_bot
  条件: {r : 实数} (x : E) (hr : 0 < r)
  证明: closedBall_zero' x hr

Depends on / 依赖: closedBall_zero
-/
theorem closedBall_bot {r : Real} (x : E) (hr : 0 < r) :
    closedBall (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  closedBall_zero' x hr

/--
theorem `balanced_ball_zero` / 定理 `balanced_ball_zero`

English:
theorem balanced_ball_zero
  given: (r : Real)
  statement: Balanced 𝕜 (ball p 0 r)
  proof: by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero]; rw [← hx]; rw [map_smul_eq_mul]
  calc
    _ <= p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ < r := by rwa [mem_ball_zero] at hy

中文:
定理 balanced_ball_zero
  条件: (r : 实数)
  结论: Balanced 𝕜 (ball p 0 r)
  证明: by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero]; rw [← hx]; rw [map_smul_eq_mul]
  calc
    _ <= p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ < r := by rwa [mem_ball_zero] at hy

Depends on / 依赖: apply_nonneg, map_smul_eq_mul, mem_ball_zero, mul_le_of_le_one_left
-/
theorem balanced_ball_zero (r : Real) : Balanced 𝕜 (ball p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero]; rw [← hx]; rw [map_smul_eq_mul]
  calc
    _ <= p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ < r := by rwa [mem_ball_zero] at hy

/--
theorem `balanced_closedBall_zero` / 定理 `balanced_closedBall_zero`

English:
theorem balanced_closedBall_zero
  given: (r : Real)
  statement: Balanced 𝕜 (closedBall p 0 r)
  proof: by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_closedBall_zero]; rw [← hx]; rw [map_smul_eq_mul]
  calc
    _ <= p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ <= r := by rwa [mem_closedBall_zero] at hy

中文:
定理 balanced_closedBall_zero
  条件: (r : 实数)
  结论: Balanced 𝕜 (closedBall p 0 r)
  证明: by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_closedBall_zero]; rw [← hx]; rw [map_smul_eq_mul]
  calc
    _ <= p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ <= r := by rwa [mem_closedBall_zero] at hy

Depends on / 依赖: apply_nonneg, map_smul_eq_mul, mem_closedBall_zero, mul_le_of_le_one_left
-/
theorem balanced_closedBall_zero (r : Real) : Balanced 𝕜 (closedBall p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_closedBall_zero]; rw [← hx]; rw [map_smul_eq_mul]
  calc
    _ <= p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ <= r := by rwa [mem_closedBall_zero] at hy

/--
theorem `ball_finset_sup_eq_iInter` / 定理 `ball_finset_sup_eq_iInter`

English:
theorem ball_finset_sup_eq_iInter
  statement: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real}
  proof: by
  lift r to NNReal using hr.le
  simp_rw [ball, iInter_ofPred, finset_sup_apply, NNReal.coe_lt_coe,
    Finset.sup_lt_iff (show ⊥ < r from hr), ← NNReal.coe_lt_coe, NNReal.coe_mk]

中文:
定理 ball_finset_sup_eq_i整数er
  结论: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (x : E) {r : 实数}
  证明: by
  lift r to NNReal using hr.le
  simp_rw [ball, iInter_ofPred, finset_sup_apply, NNReal.coe_lt_coe,
    Finset.sup_lt_iff (show ⊥ < r from hr), ← NNReal.coe_lt_coe, NNReal.coe_mk]

Depends on / 依赖: Finset, Finset.sup_lt_iff, NNReal, NNReal.coe_lt_coe, NNReal.coe_mk, coe_lt_coe, coe_mk, finset_sup_apply, hr.le, iInter_ofPred, simp_rw, sup_lt_iff
-/
theorem ball_finset_sup_eq_iInter (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real}
    (hr : 0 < r) : ball (s.sup p) x r = ⋂ i in s, ball (p i) x r := by
  lift r to NNReal using hr.le
  simp_rw [ball, iInter_ofPred, finset_sup_apply, NNReal.coe_lt_coe,
    Finset.sup_lt_iff (show ⊥ < r from hr), ← NNReal.coe_lt_coe, NNReal.coe_mk]

/--
theorem `closedBall_finset_sup_eq_iInter` / 定理 `closedBall_finset_sup_eq_iInter`

English:
theorem closedBall_finset_sup_eq_iInter
  statement: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real}
  proof: by
  lift r to NNReal using hr
  simp_rw [closedBall, iInter_ofPred, finset_sup_apply, NNReal.coe_le_coe, Finset.sup_le_iff, ←
    NNReal.coe_le_coe, NNReal.coe_mk]

中文:
定理 closedBall_finset_sup_eq_i整数er
  结论: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (x : E) {r : 实数}
  证明: by
  lift r to NNReal using hr
  simp_rw [closedBall, iInter_ofPred, finset_sup_apply, NNReal.coe_le_coe, Finset.sup_le_iff, ←
    NNReal.coe_le_coe, NNReal.coe_mk]

Depends on / 依赖: Finset, Finset.sup_le_iff, NNReal, NNReal.coe_le_coe, NNReal.coe_mk, closedBall, coe_le_coe, coe_mk, finset_sup_apply, iInter_ofPred, simp_rw, sup_le_iff
-/
theorem closedBall_finset_sup_eq_iInter (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real}
    (hr : 0 <= r) : closedBall (s.sup p) x r = ⋂ i in s, closedBall (p i) x r := by
  lift r to NNReal using hr
  simp_rw [closedBall, iInter_ofPred, finset_sup_apply, NNReal.coe_le_coe, Finset.sup_le_iff, ←
    NNReal.coe_le_coe, NNReal.coe_mk]

/--
theorem `ball_finset_sup` / 定理 `ball_finset_sup`

English:
theorem ball_finset_sup
  given: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 < r)
  proof: by
  rw [Finset.inf_eq_iInf]
  exact ball_finset_sup_eq_iInter _ _ _ hr

中文:
定理 ball_finset_sup
  条件: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (x : E) {r : 实数} (hr : 0 < r)
  证明: by
  rw [Finset.inf_eq_iInf]
  exact ball_finset_sup_eq_iInter _ _ _ hr

Depends on / 依赖: Finset, Finset.inf_eq_iInf, ball_finset_sup_eq_iInter, inf_eq_iInf
-/
theorem ball_finset_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 < r) :
    ball (s.sup p) x r = s.inf fun i => ball (p i) x r := by
  rw [Finset.inf_eq_iInf]
  exact ball_finset_sup_eq_iInter _ _ _ hr

/--
theorem `closedBall_finset_sup` / 定理 `closedBall_finset_sup`

English:
theorem closedBall_finset_sup
  given: (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 <= r)
  proof: by
  rw [Finset.inf_eq_iInf]
  exact closedBall_finset_sup_eq_iInter _ _ _ hr

@[simp]

中文:
定理 closedBall_finset_sup
  条件: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι) (x : E) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [Finset.inf_eq_iInf]
  exact closedBall_finset_sup_eq_iInter _ _ _ hr

@[simp]

Depends on / 依赖: Finset, Finset.inf_eq_iInf, closedBall_finset_sup_eq_iInter, inf_eq_iInf
-/
theorem closedBall_finset_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 <= r) :
    closedBall (s.sup p) x r = s.inf fun i => closedBall (p i) x r := by
  rw [Finset.inf_eq_iInf]
  exact closedBall_finset_sup_eq_iInter _ _ _ hr

@[simp]
/--
theorem `ball_eq_emptyset` / 定理 `ball_eq_emptyset`

English:
theorem ball_eq_emptyset
  given: (p : Seminorm 𝕜 E) {x : E} {r : Real} (hr : r <= 0)
  statement: p.ball x r = ∅
  proof: by
  ext
  rw [Seminorm.mem_ball]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_lt]
  exact hr.trans (apply_nonneg p _)

@[simp]

中文:
定理 ball_eq_emptyset
  条件: (p : 半范数 𝕜 E) {x : E} {r : 实数} (hr : r <= 0)
  结论: p.ball x r = ∅
  证明: by
  ext
  rw [Seminorm.mem_ball]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_lt]
  exact hr.trans (apply_nonneg p _)

@[simp]

Depends on / 依赖: Seminorm, Seminorm.mem_ball, Set.mem_empty_iff_false, apply_nonneg, hr.trans, iff_false, mem_ball, mem_empty_iff_false, not_lt
-/
theorem ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : Real} (hr : r <= 0) : p.ball x r = ∅ := by
  ext
  rw [Seminorm.mem_ball]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_lt]
  exact hr.trans (apply_nonneg p _)

@[simp]
/--
theorem `closedBall_eq_emptyset` / 定理 `closedBall_eq_emptyset`

English:
theorem closedBall_eq_emptyset
  given: (p : Seminorm 𝕜 E) {x : E} {r : Real} (hr : r < 0)
  proof: by
  ext
  rw [Seminorm.mem_closedBall]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_le]
  exact hr.trans_le (apply_nonneg _ _)

中文:
定理 closedBall_eq_emptyset
  条件: (p : 半范数 𝕜 E) {x : E} {r : 实数} (hr : r < 0)
  证明: by
  ext
  rw [Seminorm.mem_closedBall]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_le]
  exact hr.trans_le (apply_nonneg _ _)

Depends on / 依赖: Seminorm, Seminorm.mem_closedBall, Set.mem_empty_iff_false, apply_nonneg, hr.trans_le, iff_false, mem_closedBall, mem_empty_iff_false, not_le, trans_le
-/
theorem closedBall_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : Real} (hr : r < 0) :
    p.closedBall x r = ∅ := by
  ext
  rw [Seminorm.mem_closedBall]; rw [Set.mem_empty_iff_false]; rw [iff_false]; rw [not_le]
  exact hr.trans_le (apply_nonneg _ _)

/--
theorem `closedBall_smul_ball` / 定理 `closedBall_smul_ball`

English:
theorem closedBall_smul_ball
  given: (p : Seminorm 𝕜 E) {r₁ : Real} (hr₁ : r₁ != 0) (r₂ : Real)
  proof: by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  refine fun a ha b hb => mul_lt_mul' ha hb (apply_nonneg _ _) ?_
exact hr₁.lt_or_gt.resolve_left ((norm_nonneg a).trans ha).not_gt

中文:
定理 closedBall_smul_ball
  条件: (p : 半范数 𝕜 E) {r₁ : 实数} (hr₁ : r₁ != 0) (r₂ : 实数)
  证明: by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  refine fun a ha b hb => mul_lt_mul' ha hb (apply_nonneg _ _) ?_
exact hr₁.lt_or_gt.resolve_left ((norm_nonneg a).trans ha).not_gt

Depends on / 依赖: apply_nonneg, lt_or_gt, lt_or_gt.resolve_left, map_smul_eq_mul, mem_ball_zero, mem_closedBall_zero_iff, mul_lt_mul, norm_nonneg, not_gt, resolve_left, smul_subset_iff
-/
theorem closedBall_smul_ball (p : Seminorm 𝕜 E) {r₁ : Real} (hr₁ : r₁ != 0) (r₂ : Real) :
    Metric.closedBall (0 : 𝕜) r₁ • p.ball 0 r₂ subseteq p.ball 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  refine fun a ha b hb => mul_lt_mul' ha hb (apply_nonneg _ _) ?_
exact hr₁.lt_or_gt.resolve_left ((norm_nonneg a).trans ha).not_gt

/--
theorem `ball_smul_closedBall` / 定理 `ball_smul_closedBall`

English:
theorem ball_smul_closedBall
  given: (p : Seminorm 𝕜 E) (r₁ : Real) {r₂ : Real} (hr₂ : r₂ != 0)
  proof: by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero, mem_ball_zero_iff,
    map_smul_eq_mul]
  intro a ha b hb
  rw [mul_comm]; rw [mul_comm r₁]
  refine mul_lt_mul' hb ha (norm_nonneg _) (hr₂.lt_or_gt.resolve_left ?_)
  exact ((apply_nonneg p b).trans hb).not_gt

中文:
定理 ball_smul_closedBall
  条件: (p : 半范数 𝕜 E) (r₁ : 实数) {r₂ : 实数} (hr₂ : r₂ != 0)
  证明: by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero, mem_ball_zero_iff,
    map_smul_eq_mul]
  intro a ha b hb
  rw [mul_comm]; rw [mul_comm r₁]
  refine mul_lt_mul' hb ha (norm_nonneg _) (hr₂.lt_or_gt.resolve_left ?_)
  exact ((apply_nonneg p b).trans hb).not_gt

Depends on / 依赖: apply_nonneg, lt_or_gt, lt_or_gt.resolve_left, map_smul_eq_mul, mem_ball_zero, mem_ball_zero_iff, mem_closedBall_zero, mul_comm, mul_lt_mul, norm_nonneg, not_gt, resolve_left, smul_subset_iff
-/
theorem ball_smul_closedBall (p : Seminorm 𝕜 E) (r₁ : Real) {r₂ : Real} (hr₂ : r₂ != 0) :
    Metric.ball (0 : 𝕜) r₁ • p.closedBall 0 r₂ subseteq p.ball 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero, mem_ball_zero_iff,
    map_smul_eq_mul]
  intro a ha b hb
  rw [mul_comm]; rw [mul_comm r₁]
  refine mul_lt_mul' hb ha (norm_nonneg _) (hr₂.lt_or_gt.resolve_left ?_)
  exact ((apply_nonneg p b).trans hb).not_gt

/--
theorem `ball_smul_ball` / 定理 `ball_smul_ball`

English:
theorem ball_smul_ball
  given: (p : Seminorm 𝕜 E) (r₁ r₂ : Real)
  proof: by
  rcases eq_or_ne r₂ 0 with rfl | hr₂
  · simp
  · exact (smul_subset_smul_left (ball_subset_closedBall _ _ _)).trans
      (ball_smul_closedBall _ _ hr₂)

中文:
定理 ball_smul_ball
  条件: (p : 半范数 𝕜 E) (r₁ r₂ : 实数)
  证明: by
  rcases eq_or_ne r₂ 0 with rfl | hr₂
  · simp
  · exact (smul_subset_smul_left (ball_subset_closedBall _ _ _)).trans
      (ball_smul_closedBall _ _ hr₂)

Depends on / 依赖: ball_smul_closedBall, ball_subset_closedBall, eq_or_ne, smul_subset_smul_left
-/
theorem ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : Real) :
    Metric.ball (0 : 𝕜) r₁ • p.ball 0 r₂ subseteq p.ball 0 (r₁ * r₂) := by
  rcases eq_or_ne r₂ 0 with rfl | hr₂
  · simp
  · exact (smul_subset_smul_left (ball_subset_closedBall _ _ _)).trans
      (ball_smul_closedBall _ _ hr₂)

/--
theorem `closedBall_smul_closedBall` / 定理 `closedBall_smul_closedBall`

English:
theorem closedBall_smul_closedBall
  given: (p : Seminorm 𝕜 E) (r₁ r₂ : Real)
  proof: by
  simp only [smul_subset_iff, mem_closedBall_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  intro a ha b hb
  gcongr
  exact (norm_nonneg _).trans ha

中文:
定理 closedBall_smul_closedBall
  条件: (p : 半范数 𝕜 E) (r₁ r₂ : 实数)
  证明: by
  simp only [smul_subset_iff, mem_closedBall_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  intro a ha b hb
  gcongr
  exact (norm_nonneg _).trans ha

Depends on / 依赖: map_smul_eq_mul, mem_closedBall_zero, mem_closedBall_zero_iff, norm_nonneg, smul_subset_iff
-/
theorem closedBall_smul_closedBall (p : Seminorm 𝕜 E) (r₁ r₂ : Real) :
    Metric.closedBall (0 : 𝕜) r₁ • p.closedBall 0 r₂ subseteq p.closedBall 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_closedBall_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  intro a ha b hb
  gcongr
  exact (norm_nonneg _).trans ha

/--
theorem `neg_mem_ball_zero` / 定理 `neg_mem_ball_zero`

English:
theorem neg_mem_ball_zero
  given: {r : Real} {x : E}
  statement: -x in ball p 0 r ↔ x in ball p 0 r
  proof: by
  simp only [mem_ball_zero, map_neg_eq_map]

中文:
定理 neg_mem_ball_zero
  条件: {r : 实数} {x : E}
  结论: -x in ball p 0 r ↔ x in ball p 0 r
  证明: by
  simp only [mem_ball_zero, map_neg_eq_map]

Depends on / 依赖: map_neg_eq_map, mem_ball_zero
-/
theorem neg_mem_ball_zero {r : Real} {x : E} : -x in ball p 0 r ↔ x in ball p 0 r := by
  simp only [mem_ball_zero, map_neg_eq_map]

/--
theorem `neg_mem_closedBall_zero` / 定理 `neg_mem_closedBall_zero`

English:
theorem neg_mem_closedBall_zero
  given: {r : Real} {x : E}
  statement: -x in closedBall p 0 r ↔ x in closedBall p 0 r
  proof: by
  simp only [mem_closedBall_zero, map_neg_eq_map]

@[simp]

中文:
定理 neg_mem_closedBall_zero
  条件: {r : 实数} {x : E}
  结论: -x in closedBall p 0 r ↔ x in closedBall p 0 r
  证明: by
  simp only [mem_closedBall_zero, map_neg_eq_map]

@[simp]

Depends on / 依赖: map_neg_eq_map, mem_closedBall_zero
-/
theorem neg_mem_closedBall_zero {r : Real} {x : E} : -x in closedBall p 0 r ↔ x in closedBall p 0 r := by
  simp only [mem_closedBall_zero, map_neg_eq_map]

@[simp]
/--
theorem `neg_ball` / 定理 `neg_ball`

English:
theorem neg_ball
  given: (p : Seminorm 𝕜 E) (r : Real) (x : E)
  statement: -ball p x r = ball p (-x) r
  proof: by
  ext
  rw [Set.mem_neg]; rw [mem_ball]; rw [mem_ball]; rw [← neg_add']; rw [sub_neg_eq_add]; rw [map_neg_eq_map]

@[simp]

中文:
定理 neg_ball
  条件: (p : 半范数 𝕜 E) (r : 实数) (x : E)
  结论: -ball p x r = ball p (-x) r
  证明: by
  ext
  rw [Set.mem_neg]; rw [mem_ball]; rw [mem_ball]; rw [← neg_add']; rw [sub_neg_eq_add]; rw [map_neg_eq_map]

@[simp]

Depends on / 依赖: Set.mem_neg, map_neg_eq_map, mem_ball, mem_neg, neg_add, sub_neg_eq_add
-/
theorem neg_ball (p : Seminorm 𝕜 E) (r : Real) (x : E) : -ball p x r = ball p (-x) r := by
  ext
  rw [Set.mem_neg]; rw [mem_ball]; rw [mem_ball]; rw [← neg_add']; rw [sub_neg_eq_add]; rw [map_neg_eq_map]

@[simp]
/--
theorem `neg_closedBall` / 定理 `neg_closedBall`

English:
theorem neg_closedBall
  given: (p : Seminorm 𝕜 E) (r : Real) (x : E)
  proof: by
  ext
  rw [Set.mem_neg]; rw [mem_closedBall]; rw [mem_closedBall]; rw [← neg_add']; rw [sub_neg_eq_add]; rw [map_neg_eq_map]

中文:
定理 neg_closedBall
  条件: (p : 半范数 𝕜 E) (r : 实数) (x : E)
  证明: by
  ext
  rw [Set.mem_neg]; rw [mem_closedBall]; rw [mem_closedBall]; rw [← neg_add']; rw [sub_neg_eq_add]; rw [map_neg_eq_map]

Depends on / 依赖: Set.mem_neg, map_neg_eq_map, mem_closedBall, mem_neg, neg_add, sub_neg_eq_add
-/
theorem neg_closedBall (p : Seminorm 𝕜 E) (r : Real) (x : E) :
    -closedBall p x r = closedBall p (-x) r := by
  ext
  rw [Set.mem_neg]; rw [mem_closedBall]; rw [mem_closedBall]; rw [← neg_add']; rw [sub_neg_eq_add]; rw [map_neg_eq_map]

end Module

end AddCommGroup

end SeminormedRing

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {r : Real} {x : E}

/--
theorem `ball_norm_mul_subset` / 定理 `ball_norm_mul_subset`

English:
theorem ball_norm_mul_subset
  given: {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real}
  proof: by
  rcases eq_or_ne k 0 with (rfl | hk)
  · rw [norm_zero, zero_mul, ball_eq_emptyset _ le_rfl]
    exact empty_subset _
  · intro x
    rw [Set.mem_smul_set]; rw [Seminorm.mem_ball_zero]
    refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
    · rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ←
mul_lt_m

中文:
定理 ball_norm_mul_subset
  条件: {p : 半范数 𝕜 E} {k : 𝕜} {r : 实数}
  证明: by
  rcases eq_or_ne k 0 with (rfl | hk)
  · rw [norm_zero, zero_mul, ball_eq_emptyset _ le_rfl]
    exact empty_subset _
  · intro x
    rw [Set.mem_smul_set]; rw [Seminorm.mem_ball_zero]
    refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
    · rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ←
mul_lt_m

Depends on / 依赖: Seminorm, Seminorm.mem_ball_zero, Set.mem_smul_set, ball_eq_emptyset, div_eq_mul_inv, div_self, empty_subset, eq_or_ne, le_rfl, map_smul_eq_mul, mem_ball_zero, mem_smul_set, mul_assoc, ne_of_gt, norm_inv, norm_pos_iff, norm_pos_iff.mpr, norm_zero, one_mul, one_smul
-/
theorem ball_norm_mul_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} :
    p.ball 0 (‖k‖ * r) subseteq k • p.ball 0 r := by
  rcases eq_or_ne k 0 with (rfl | hk)
  · rw [norm_zero, zero_mul, ball_eq_emptyset _ le_rfl]
    exact empty_subset _
  · intro x
    rw [Set.mem_smul_set]; rw [Seminorm.mem_ball_zero]
    refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
    · rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ←
mul_lt_mul_iff_right₀ norm_pos_iff.mpr hk, ← mul_assoc, ← div_eq_mul_inv ‖k‖ ‖k‖,
        div_self (ne_of_gt <| norm_pos_iff.mpr hk), one_mul]
    rw [← smul_assoc]; rw [smul_eq_mul]; rw [← div_eq_mul_inv]; rw [div_self hk]; rw [one_smul]

/--
theorem `smul_ball_zero` / 定理 `smul_ball_zero`

English:
theorem smul_ball_zero
  given: {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} (hk : k != 0)
  proof: by
  ext
  rw [mem_smul_set_iff_inv_smul_mem₀ hk]; rw [p.mem_ball_zero]; rw [p.mem_ball_zero]; rw [map_smul_eq_mul]; rw [norm_inv]; rw [← div_eq_inv_mul]; rw [div_lt_iff₀ (norm_pos_iff.2 hk)]; rw [mul_comm]

中文:
定理 smul_ball_zero
  条件: {p : 半范数 𝕜 E} {k : 𝕜} {r : 实数} (hk : k != 0)
  证明: by
  ext
  rw [mem_smul_set_iff_inv_smul_mem₀ hk]; rw [p.mem_ball_zero]; rw [p.mem_ball_zero]; rw [map_smul_eq_mul]; rw [norm_inv]; rw [← div_eq_inv_mul]; rw [div_lt_iff₀ (norm_pos_iff.2 hk)]; rw [mul_comm]

Depends on / 依赖: div_eq_inv_mul, map_smul_eq_mul, mem_ball_zero, mul_comm, norm_inv, norm_pos_iff, p.mem_ball_zero
-/
theorem smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} (hk : k != 0) :
    k • p.ball 0 r = p.ball 0 (‖k‖ * r) := by
  ext
  rw [mem_smul_set_iff_inv_smul_mem₀ hk]; rw [p.mem_ball_zero]; rw [p.mem_ball_zero]; rw [map_smul_eq_mul]; rw [norm_inv]; rw [← div_eq_inv_mul]; rw [div_lt_iff₀ (norm_pos_iff.2 hk)]; rw [mul_comm]

/--
theorem `smul_closedBall_subset` / 定理 `smul_closedBall_subset`

English:
theorem smul_closedBall_subset
  given: {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real}
  proof: by
  rintro x ⟨y, hy, h⟩
  rw [Seminorm.mem_closedBall_zero]; rw [← h]; rw [map_smul_eq_mul]
  rw [Seminorm.mem_closedBall_zero] at hy
  gcongr

中文:
定理 smul_closedBall_subset
  条件: {p : 半范数 𝕜 E} {k : 𝕜} {r : 实数}
  证明: by
  rintro x ⟨y, hy, h⟩
  rw [Seminorm.mem_closedBall_zero]; rw [← h]; rw [map_smul_eq_mul]
  rw [Seminorm.mem_closedBall_zero] at hy
  gcongr

Depends on / 依赖: Seminorm, Seminorm.mem_closedBall_zero, map_smul_eq_mul, mem_closedBall_zero
-/
theorem smul_closedBall_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} :
    k • p.closedBall 0 r subseteq p.closedBall 0 (‖k‖ * r) := by
  rintro x ⟨y, hy, h⟩
  rw [Seminorm.mem_closedBall_zero]; rw [← h]; rw [map_smul_eq_mul]
  rw [Seminorm.mem_closedBall_zero] at hy
  gcongr

/--
theorem `smul_closedBall_zero` / 定理 `smul_closedBall_zero`

English:
theorem smul_closedBall_zero
  given: {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} (hk : 0 < ‖k‖)
  proof: by
  refine subset_antisymm smul_closedBall_subset ?_
  intro x
  rw [Set.mem_smul_set]; rw [Seminorm.mem_closedBall_zero]
  refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
  · rwa [Seminorm.mem_closedBall_zero, map_smul_eq_mul, norm_inv, inv_mul_le_iff₀ hk]
  rw [← smul_assoc]; rw [smul_eq_mul]; rw [← div_eq_mu

中文:
定理 smul_closedBall_zero
  条件: {p : 半范数 𝕜 E} {k : 𝕜} {r : 实数} (hk : 0 < ‖k‖)
  证明: by
  refine subset_antisymm smul_closedBall_subset ?_
  intro x
  rw [Set.mem_smul_set]; rw [Seminorm.mem_closedBall_zero]
  refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
  · rwa [Seminorm.mem_closedBall_zero, map_smul_eq_mul, norm_inv, inv_mul_le_iff₀ hk]
  rw [← smul_assoc]; rw [smul_eq_mul]; rw [← div_eq_mu

Depends on / 依赖: Seminorm, Seminorm.mem_closedBall_zero, Set.mem_smul_set, div_eq_mul_inv, div_self, map_smul_eq_mul, mem_closedBall_zero, mem_smul_set, norm_inv, norm_pos_iff, norm_pos_iff.mp, one_smul, smul_assoc, smul_closedBall_subset, smul_eq_mul, subset_antisymm
-/
theorem smul_closedBall_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} (hk : 0 < ‖k‖) :
    k • p.closedBall 0 r = p.closedBall 0 (‖k‖ * r) := by
  refine subset_antisymm smul_closedBall_subset ?_
  intro x
  rw [Set.mem_smul_set]; rw [Seminorm.mem_closedBall_zero]
  refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
  · rwa [Seminorm.mem_closedBall_zero, map_smul_eq_mul, norm_inv, inv_mul_le_iff₀ hk]
  rw [← smul_assoc]; rw [smul_eq_mul]; rw [← div_eq_mul_inv]; rw [div_self (norm_pos_iff.mp hk)]; rw [one_smul]

/--
theorem `ball_zero_absorbs_ball_zero` / 定理 `ball_zero_absorbs_ball_zero`

English:
theorem ball_zero_absorbs_ball_zero
  given: (p : Seminorm 𝕜 E) {r₁ r₂ : Real} (hr₁ : 0 < r₁)
  proof: by
  rcases exists_pos_lt_mul hr₁ r₂ with ⟨r, hr₀, hr⟩
  refine .of_norm ⟨r, fun a ha x hx => ?_⟩
  rw [smul_ball_zero (norm_pos_iff.1 <| hr₀.trans_le ha)]; rw [p.mem_ball_zero]
  rw [p.mem_ball_zero] at hx
  exact hx.trans (hr.trans_le <| by gcongr)

中文:
定理 ball_zero_absorbs_ball_zero
  条件: (p : 半范数 𝕜 E) {r₁ r₂ : 实数} (hr₁ : 0 < r₁)
  证明: by
  rcases exists_pos_lt_mul hr₁ r₂ with ⟨r, hr₀, hr⟩
  refine .of_norm ⟨r, fun a ha x hx => ?_⟩
  rw [smul_ball_zero (norm_pos_iff.1 <| hr₀.trans_le ha)]; rw [p.mem_ball_zero]
  rw [p.mem_ball_zero] at hx
  exact hx.trans (hr.trans_le <| by gcongr)

Depends on / 依赖: exists_pos_lt_mul, hr.trans_le, hx.trans, mem_ball_zero, norm_pos_iff, of_norm, p.mem_ball_zero, smul_ball_zero, trans_le
-/
theorem ball_zero_absorbs_ball_zero (p : Seminorm 𝕜 E) {r₁ r₂ : Real} (hr₁ : 0 < r₁) :
    Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) := by
  rcases exists_pos_lt_mul hr₁ r₂ with ⟨r, hr₀, hr⟩
  refine .of_norm ⟨r, fun a ha x hx => ?_⟩
  rw [smul_ball_zero (norm_pos_iff.1 <| hr₀.trans_le ha)]; rw [p.mem_ball_zero]
  rw [p.mem_ball_zero] at hx
  exact hx.trans (hr.trans_le <| by gcongr)

/--
theorem `absorbent_ball_zero` / 定理 `absorbent_ball_zero`

English:
theorem absorbent_ball_zero
  given: (hr : 0 < r)
  statement: Absorbent 𝕜 (ball p (0 : E) r)
  proof: absorbent_iff_forall_absorbs_singleton.2 fun _ =>
(p.ball_zero_absorbs_ball_zero hr).mono_right
singleton_subset_iff.2 p.mem_ball_zero.2 lt_add_one _

中文:
定理 absorbent_ball_zero
  条件: (hr : 0 < r)
  结论: Absorbent 𝕜 (ball p (0 : E) r)
  证明: absorbent_iff_forall_absorbs_singleton.2 fun _ =>
(p.ball_zero_absorbs_ball_zero hr).mono_right
singleton_subset_iff.2 p.mem_ball_zero.2 lt_add_one _
-/
protected theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (ball p (0 : E) r) :=
  absorbent_iff_forall_absorbs_singleton.2 fun _ =>
(p.ball_zero_absorbs_ball_zero hr).mono_right
singleton_subset_iff.2 p.mem_ball_zero.2 lt_add_one _

/--
theorem `absorbent_closedBall_zero` / 定理 `absorbent_closedBall_zero`

English:
theorem absorbent_closedBall_zero
  given: (hr : 0 < r)
  statement: Absorbent 𝕜 (closedBall p (0 : E) r)
  proof: (p.absorbent_ball_zero hr).mono (p.ball_subset_closedBall _ _)

中文:
定理 absorbent_closedBall_zero
  条件: (hr : 0 < r)
  结论: Absorbent 𝕜 (closedBall p (0 : E) r)
  证明: (p.absorbent_ball_zero hr).mono (p.ball_subset_closedBall _ _)
-/
protected theorem absorbent_closedBall_zero (hr : 0 < r) : Absorbent 𝕜 (closedBall p (0 : E) r) :=
  (p.absorbent_ball_zero hr).mono (p.ball_subset_closedBall _ _)

/--
theorem `absorbent_ball` / 定理 `absorbent_ball`

English:
theorem absorbent_ball
  given: (hpr : p x < r)
  statement: Absorbent 𝕜 (ball p x r)
  proof: by
  refine (p.absorbent_ball_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt <| add_lt_of_lt_sub_right hy)

中文:
定理 absorbent_ball
  条件: (hpr : p x < r)
  结论: Absorbent 𝕜 (ball p x r)
  证明: by
  refine (p.absorbent_ball_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt <| add_lt_of_lt_sub_right hy)
-/
protected theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (ball p x r) := by
  refine (p.absorbent_ball_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt <| add_lt_of_lt_sub_right hy)

/--
theorem `absorbent_closedBall` / 定理 `absorbent_closedBall`

English:
theorem absorbent_closedBall
  given: (hpr : p x < r)
  statement: Absorbent 𝕜 (closedBall p x r)
  proof: by
  refine (p.absorbent_closedBall_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_closedBall_zero] at hy
  exact p.mem_closedBall.2 ((map_sub_le_add p _ _).trans <| add_le_of_le_sub_right hy)

@[simp]

中文:
定理 absorbent_closedBall
  条件: (hpr : p x < r)
  结论: Absorbent 𝕜 (closedBall p x r)
  证明: by
  refine (p.absorbent_closedBall_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_closedBall_zero] at hy
  exact p.mem_closedBall.2 ((map_sub_le_add p _ _).trans <| add_le_of_le_sub_right hy)

@[simp]
-/
protected theorem absorbent_closedBall (hpr : p x < r) : Absorbent 𝕜 (closedBall p x r) := by
  refine (p.absorbent_closedBall_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_closedBall_zero] at hy
  exact p.mem_closedBall.2 ((map_sub_le_add p _ _).trans <| add_le_of_le_sub_right hy)

@[simp]
/--
theorem `smul_ball_preimage` / 定理 `smul_ball_preimage`

English:
theorem smul_ball_preimage
  given: (p : Seminorm 𝕜 E) (y : E) (r : Real) (a : 𝕜) (ha : a != 0)
  proof: Set.ext fun _ => by
    rw [mem_preimage]; rw [mem_ball]; rw [mem_ball]; rw [lt_div_iff₀ (norm_pos_iff.mpr ha)]; rw [mul_comm]; rw [←
      map_smul_eq_mul p]; rw [smul_sub]; rw [smul_inv_smul₀ ha]

@[simp]

中文:
定理 smul_ball_preimage
  条件: (p : 半范数 𝕜 E) (y : E) (r : 实数) (a : 𝕜) (ha : a != 0)
  证明: Set.ext fun _ => by
    rw [mem_preimage]; rw [mem_ball]; rw [mem_ball]; rw [lt_div_iff₀ (norm_pos_iff.mpr ha)]; rw [mul_comm]; rw [←
      map_smul_eq_mul p]; rw [smul_sub]; rw [smul_inv_smul₀ ha]

@[simp]

Depends on / 依赖: Set.ext, map_smul_eq_mul, mem_ball, mem_preimage, mul_comm, norm_pos_iff, norm_pos_iff.mpr, smul_sub
-/
theorem smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : Real) (a : 𝕜) (ha : a != 0) :
    (a • ·) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ‖a‖) :=
  Set.ext fun _ => by
    rw [mem_preimage]; rw [mem_ball]; rw [mem_ball]; rw [lt_div_iff₀ (norm_pos_iff.mpr ha)]; rw [mul_comm]; rw [←
      map_smul_eq_mul p]; rw [smul_sub]; rw [smul_inv_smul₀ ha]

@[simp]
/--
theorem `smul_closedBall_preimage` / 定理 `smul_closedBall_preimage`

English:
theorem smul_closedBall_preimage
  given: (p : Seminorm 𝕜 E) (y : E) (r : Real) (a : 𝕜) (ha : a != 0)
  proof: Set.ext fun _ => by
    rw [mem_preimage]; rw [mem_closedBall]; rw [mem_closedBall]; rw [le_div_iff₀ (norm_pos_iff.mpr ha)]; rw [mul_comm]; rw [←
      map_smul_eq_mul p]; rw [smul_sub]; rw [smul_inv_smul₀ ha]

中文:
定理 smul_closedBall_preimage
  条件: (p : 半范数 𝕜 E) (y : E) (r : 实数) (a : 𝕜) (ha : a != 0)
  证明: Set.ext fun _ => by
    rw [mem_preimage]; rw [mem_closedBall]; rw [mem_closedBall]; rw [le_div_iff₀ (norm_pos_iff.mpr ha)]; rw [mul_comm]; rw [←
      map_smul_eq_mul p]; rw [smul_sub]; rw [smul_inv_smul₀ ha]

Depends on / 依赖: Set.ext, map_smul_eq_mul, mem_closedBall, mem_preimage, mul_comm, norm_pos_iff, norm_pos_iff.mpr, smul_sub
-/
theorem smul_closedBall_preimage (p : Seminorm 𝕜 E) (y : E) (r : Real) (a : 𝕜) (ha : a != 0) :
    (a • ·) ⁻¹' p.closedBall y r = p.closedBall (a⁻¹ • y) (r / ‖a‖) :=
  Set.ext fun _ => by
    rw [mem_preimage]; rw [mem_closedBall]; rw [mem_closedBall]; rw [le_div_iff₀ (norm_pos_iff.mpr ha)]; rw [mul_comm]; rw [←
      map_smul_eq_mul p]; rw [smul_sub]; rw [smul_inv_smul₀ ha]

end NormedDivisionRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {r : Real} {x : E}

/--
theorem `closedBall_iSup` / 定理 `closedBall_iSup`

English:
theorem closedBall_iSup
  statement: {ι : Sort*} {p : ι -> Seminorm 𝕜 E} (hp : BddAbove (range p)) (e : E)
  proof: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iInter_of_empty, Seminorm.sSup_empty]
    exact closedBall_bot _ hr
  · ext x
    have := Seminorm.bddAbove_range_iff.mp hp (x - e)
    simp only [mem_closedBall, mem_iInter, Seminorm.iSup_apply hp, ciSup_le_iff this]

中文:
定理 closedBall_iSup
  结论: {ι : 类型层*} {p : ι -> 半范数 𝕜 E} (hp : BddAbove (range p)) (e : E)
  证明: by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iInter_of_empty, Seminorm.sSup_empty]
    exact closedBall_bot _ hr
  · ext x
    have := Seminorm.bddAbove_range_iff.mp hp (x - e)
    simp only [mem_closedBall, mem_iInter, Seminorm.iSup_apply hp, ciSup_le_iff this]

Depends on / 依赖: Seminorm, Seminorm.bddAbove_range_iff.mp, Seminorm.iSup_apply, Seminorm.sSup_empty, bddAbove_range_iff, ciSup_le_iff, closedBall_bot, iInter_of_empty, iSup_apply, iSup_of_empty, isEmpty_or_nonempty, mem_closedBall, mem_iInter, sSup_empty
-/
theorem closedBall_iSup {ι : Sort*} {p : ι -> Seminorm 𝕜 E} (hp : BddAbove (range p)) (e : E)
    {r : Real} (hr : 0 < r) : closedBall (⨆ i, p i) e r = ⋂ i, closedBall (p i) e r := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iInter_of_empty, Seminorm.sSup_empty]
    exact closedBall_bot _ hr
  · ext x
    have := Seminorm.bddAbove_range_iff.mp hp (x - e)
    simp only [mem_closedBall, mem_iInter, Seminorm.iSup_apply hp, ciSup_le_iff this]

end NormedField

section Convex

variable [NormedField 𝕜] [AddCommGroup E] [SMul Real 𝕜] [NormSMulClass Real 𝕜] [Module 𝕜 E]

section SMul

variable [SMul Real E] [IsScalarTower Real 𝕜 E] (p : Seminorm 𝕜 E)

/--
theorem `convexOn` / 定理 `convexOn`

English:
theorem convexOn
  statement: ConvexOn Real univ p
  proof: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc
    p (a • x + b • y) <= p (a • x) + p (b • y) := map_add_le_add p _ _
    _ = ‖a • (1 : 𝕜)‖ * p x + ‖b • (1 : 𝕜)‖ * p y := by
      rw [← map_smul_eq_mul p]; rw [← map_smul_eq_mul p]; rw [smul_one_smul]; rw [smul_one_smul]
    _ = a * 

中文:
定理 convexOn
  结论: ConvexOn 实数 univ p
  证明: by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc
    p (a • x + b • y) <= p (a • x) + p (b • y) := map_add_le_add p _ _
    _ = ‖a • (1 : 𝕜)‖ * p x + ‖b • (1 : 𝕜)‖ * p y := by
      rw [← map_smul_eq_mul p]; rw [← map_smul_eq_mul p]; rw [smul_one_smul]; rw [smul_one_smul]
    _ = a * 
-/
protected theorem convexOn : ConvexOn Real univ p := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc
    p (a • x + b • y) <= p (a • x) + p (b • y) := map_add_le_add p _ _
    _ = ‖a • (1 : 𝕜)‖ * p x + ‖b • (1 : 𝕜)‖ * p y := by
      rw [← map_smul_eq_mul p]; rw [← map_smul_eq_mul p]; rw [smul_one_smul]; rw [smul_one_smul]
    _ = a * p x + b * p y := by
      rw [norm_smul]; rw [norm_smul]; rw [norm_one]; rw [mul_one]; rw [mul_one]; rw [Real.norm_of_nonneg ha]; rw [Real.norm_of_nonneg hb]

end SMul

section Module

variable [Module Real E] [IsScalarTower Real 𝕜 E] (p : Seminorm 𝕜 E) (x : E) (r : Real)

/--
theorem `convex_ball` / 定理 `convex_ball`

English:
theorem convex_ball
  statement: Convex Real (ball p x r)
  proof: by
  convert! (p.convexOn.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ]; rw [sep_univ]; rw [p.mem_ball]; rw [sub_eq_add_neg]
  rfl

中文:
定理 convex_ball
  结论: 凸 实数 (ball p x r)
  证明: by
  convert! (p.convexOn.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ]; rw [sep_univ]; rw [p.mem_ball]; rw [sub_eq_add_neg]
  rfl

Depends on / 依赖: convert, convexOn, convex_lt, mem_ball, p.convexOn.translate_left, p.mem_ball, preimage_univ, sep_univ, sub_eq_add_neg, translate_left
-/
theorem convex_ball : Convex Real (ball p x r) := by
  convert! (p.convexOn.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ]; rw [sep_univ]; rw [p.mem_ball]; rw [sub_eq_add_neg]
  rfl

/--
theorem `convex_closedBall` / 定理 `convex_closedBall`

English:
theorem convex_closedBall
  statement: Convex Real (closedBall p x r)
  proof: by
  rw [closedBall_eq_biInter_ball]
  exact convex_iInter₂ fun _ _ => convex_ball _ _ _

中文:
定理 convex_closedBall
  结论: 凸 实数 (closedBall p x r)
  证明: by
  rw [closedBall_eq_biInter_ball]
  exact convex_iInter₂ fun _ _ => convex_ball _ _ _

Depends on / 依赖: closedBall_eq_biInter_ball, convex_ball
-/
theorem convex_closedBall : Convex Real (closedBall p x r) := by
  rw [closedBall_eq_biInter_ball]
  exact convex_iInter₂ fun _ _ => convex_ball _ _ _

end Module

end Convex

section RestrictScalars

variable (𝕜) {𝕜' : Type*} [NormedField 𝕜] [SeminormedRing 𝕜'] [SMul 𝕜 𝕜'] [NormSMulClass 𝕜 𝕜']
  [NormOneClass 𝕜'] [AddCommGroup E] [Module 𝕜' E] [SMul 𝕜 E] [IsScalarTower 𝕜 𝕜' E]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (p : Seminorm 𝕜' E)
  body: { p with
    smul' := fun a x => by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one] }

@[simp]

中文:
定义 restrictScalars
  签名: (p : 半范数 𝕜' E)
  定义体: { p with
    smul' := fun a x => by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one] }

@[simp]
-/
protected def restrictScalars (p : Seminorm 𝕜' E) : Seminorm 𝕜 E :=
  { p with
    smul' := fun a x => by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one] }

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (p : Seminorm 𝕜' E)
  statement: (p.restrictScalars 𝕜 : E -> Real) = p
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: (p : 半范数 𝕜' E)
  结论: (p.restrictScalars 𝕜 : E -> 实数) = p
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜 : E -> Real) = p :=
  rfl

@[simp]
/--
theorem `restrictScalars_ball` / 定理 `restrictScalars_ball`

English:
theorem restrictScalars_ball
  given: (p : Seminorm 𝕜' E)
  statement: (p.restrictScalars 𝕜).ball = p.ball
  proof: rfl

@[simp]

中文:
定理 restrictScalars_ball
  条件: (p : 半范数 𝕜' E)
  结论: (p.restrictScalars 𝕜).ball = p.ball
  证明: rfl

@[simp]
-/
theorem restrictScalars_ball (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜).ball = p.ball :=
  rfl

@[simp]
/--
theorem `restrictScalars_closedBall` / 定理 `restrictScalars_closedBall`

English:
theorem restrictScalars_closedBall
  given: (p : Seminorm 𝕜' E)
  proof: rfl

中文:
定理 restrictScalars_closedBall
  条件: (p : 半范数 𝕜' E)
  证明: rfl
-/
theorem restrictScalars_closedBall (p : Seminorm 𝕜' E) :
    (p.restrictScalars 𝕜).closedBall = p.closedBall :=
  rfl

end RestrictScalars

/-! ### Continuity criteria for seminorms -/


section Continuity

variable [NontriviallyNormedField 𝕜] [SeminormedRing 𝕝] [AddCommGroup E] [Module 𝕜 E]
variable [Module 𝕝 E]

/--
theorem `continuousAt_zero_of_forall'` / 定理 `continuousAt_zero_of_forall'`

English:
theorem continuousAt_zero_of_forall'
  statement: [TopologicalSpace E] {p : Seminorm 𝕝 E}
  proof: by
  simp_rw [Seminorm.closedBall_zero_eq_preimage_closedBall] at hp
  rwa [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff, map_zero]

中文:
定理 continuousAt_zero_of_对任意'
  结论: [拓扑空间 E] {p : 半范数 𝕝 E}
  证明: by
  simp_rw [Seminorm.closedBall_zero_eq_preimage_closedBall] at hp
  rwa [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff, map_zero]

Depends on / 依赖: ContinuousAt, Metric, Metric.nhds_basis_closedBall.tendsto_right_iff, Seminorm, Seminorm.closedBall_zero_eq_preimage_closedBall, closedBall_zero_eq_preimage_closedBall, map_zero, nhds_basis_closedBall, simp_rw, tendsto_right_iff
-/
theorem continuousAt_zero_of_forall' [TopologicalSpace E] {p : Seminorm 𝕝 E}
    (hp : forall r > 0, p.closedBall 0 r in (𝓝 0 : Filter E)) :
    ContinuousAt p 0 := by
  simp_rw [Seminorm.closedBall_zero_eq_preimage_closedBall] at hp
  rwa [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff, map_zero]

/--
theorem `continuousAt_zero'` / 定理 `continuousAt_zero'`

English:
theorem continuousAt_zero'
  statement: [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E}
  proof: by
  refine continuousAt_zero_of_forall' fun ε hε => ?_
  obtain ⟨k, hk₀, hk⟩ : exists k : 𝕜, 0 < ‖k‖ ∧ ‖k‖ * r < ε := by
    rcases le_or_gt r 0 with hr | hr
    · use 1; simpa using hr.trans_lt hε
    · simpa [lt_div_iff₀ hr] using exists_norm_lt 𝕜 (div_pos hε hr)
  grw [← hk]
  rwa [← set_smul_me

中文:
定理 continuousAt_zero'
  结论: [拓扑空间 E] [连续常数标量乘法 𝕜 E] {p : 半范数 𝕜 E}
  证明: by
  refine continuousAt_zero_of_forall' fun ε hε => ?_
  obtain ⟨k, hk₀, hk⟩ : exists k : 𝕜, 0 < ‖k‖ ∧ ‖k‖ * r < ε := by
    rcases le_or_gt r 0 with hr | hr
    · use 1; simpa using hr.trans_lt hε
    · simpa [lt_div_iff₀ hr] using exists_norm_lt 𝕜 (div_pos hε hr)
  grw [← hk]
  rwa [← set_smul_me

Depends on / 依赖: continuousAt_zero_of_forall, div_pos, exists_norm_lt, hr.trans_lt, le_or_gt, norm_pos_iff, set_smul_mem_nhds_zero_iff, smul_closedBall_zero, trans_lt
-/
theorem continuousAt_zero' [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E}
    {r : Real} (hp : p.closedBall 0 r in (𝓝 0 : Filter E)) : ContinuousAt p 0 := by
  refine continuousAt_zero_of_forall' fun ε hε => ?_
  obtain ⟨k, hk₀, hk⟩ : exists k : 𝕜, 0 < ‖k‖ ∧ ‖k‖ * r < ε := by
    rcases le_or_gt r 0 with hr | hr
    · use 1; simpa using hr.trans_lt hε
    · simpa [lt_div_iff₀ hr] using exists_norm_lt 𝕜 (div_pos hε hr)
  grw [← hk]
  rwa [← set_smul_mem_nhds_zero_iff (norm_pos_iff.1 hk₀), smul_closedBall_zero hk₀] at hp

/--
theorem `continuousAt_zero_of_forall` / 定理 `continuousAt_zero_of_forall`

English:
theorem continuousAt_zero_of_forall
  statement: [TopologicalSpace E] {p : Seminorm 𝕝 E}
  proof: continuousAt_zero_of_forall'
    (fun r hr => Filter.mem_of_superset (hp r hr) <| p.ball_subset_closedBall _ _)

中文:
定理 continuousAt_zero_of_对任意
  结论: [拓扑空间 E] {p : 半范数 𝕝 E}
  证明: continuousAt_zero_of_forall'
    (fun r hr => Filter.mem_of_superset (hp r hr) <| p.ball_subset_closedBall _ _)

Depends on / 依赖: Filter, Filter.mem_of_superset, ball_subset_closedBall, continuousAt_zero_of_forall, mem_of_superset, p.ball_subset_closedBall
-/
theorem continuousAt_zero_of_forall [TopologicalSpace E] {p : Seminorm 𝕝 E}
    (hp : forall r > 0, p.ball 0 r in (𝓝 0 : Filter E)) :
    ContinuousAt p 0 :=
  continuousAt_zero_of_forall'
    (fun r hr => Filter.mem_of_superset (hp r hr) <| p.ball_subset_closedBall _ _)

/--
theorem `continuousAt_zero` / 定理 `continuousAt_zero`

English:
theorem continuousAt_zero
  statement: [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real}
  proof: continuousAt_zero' (Filter.mem_of_superset hp <| p.ball_subset_closedBall _ _)

中文:
定理 continuousAt_zero
  结论: [拓扑空间 E] [连续常数标量乘法 𝕜 E] {p : 半范数 𝕜 E} {r : 实数}
  证明: continuousAt_zero' (Filter.mem_of_superset hp <| p.ball_subset_closedBall _ _)

Depends on / 依赖: Filter, Filter.mem_of_superset, ball_subset_closedBall, continuousAt_zero, mem_of_superset, p.ball_subset_closedBall
-/
theorem continuousAt_zero [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real}
    (hp : p.ball 0 r in (𝓝 0 : Filter E)) : ContinuousAt p 0 :=
  continuousAt_zero' (Filter.mem_of_superset hp <| p.ball_subset_closedBall _ _)

/--
theorem `uniformContinuous_of_continuousAt_zero` / 定理 `uniformContinuous_of_continuousAt_zero`

English:
theorem uniformContinuous_of_continuousAt_zero
  statement: [UniformSpace E] [IsUniformAddGroup E]
  proof: by
  have hp : Filter.Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp
  rw [UniformContinuous]; rw [uniformity_eq_comap_nhds_zero_swapped]; rw [Metric.uniformity_eq_comap_nhds_zero]; rw [Filter.tendsto_comap_iff]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp.comp Filter.tends

中文:
定理 uniformContinuous_of_continuousAt_zero
  结论: [一致空间 E] [是UniformAdd群 E]
  证明: by
  have hp : Filter.Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp
  rw [UniformContinuous]; rw [uniformity_eq_comap_nhds_zero_swapped]; rw [Metric.uniformity_eq_comap_nhds_zero]; rw [Filter.tendsto_comap_iff]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp.comp Filter.tends
-/
protected theorem uniformContinuous_of_continuousAt_zero [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : UniformContinuous p := by
  have hp : Filter.Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp
  rw [UniformContinuous]; rw [uniformity_eq_comap_nhds_zero_swapped]; rw [Metric.uniformity_eq_comap_nhds_zero]; rw [Filter.tendsto_comap_iff]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp.comp Filter.tendsto_comap)
      (fun xy => dist_nonneg) fun xy => p.norm_sub_map_le_sub _ _

/--
theorem `continuous_of_continuousAt_zero` / 定理 `continuous_of_continuousAt_zero`

English:
theorem continuous_of_continuousAt_zero
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: by
  let := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact (Seminorm.uniformContinuous_of_continuousAt_zero hp).continuous

中文:
定理 continuous_of_continuousAt_zero
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: by
  let := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact (Seminorm.uniformContinuous_of_continuousAt_zero hp).continuous
-/
protected theorem continuous_of_continuousAt_zero [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : Continuous p := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact (Seminorm.uniformContinuous_of_continuousAt_zero hp).continuous

/--
theorem `uniformContinuous_of_forall` / 定理 `uniformContinuous_of_forall`

English:
theorem uniformContinuous_of_forall
  statement: [UniformSpace E] [IsUniformAddGroup E]
  proof: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)

中文:
定理 uniformContinuous_of_对任意
  结论: [一致空间 E] [是UniformAdd群 E]
  证明: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)
-/
protected theorem uniformContinuous_of_forall [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : forall r > 0, p.ball 0 r in (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  statement: [UniformSpace E] [IsUniformAddGroup E]
  proof: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero hp)

中文:
定理 uniformContinuous
  结论: [一致空间 E] [是UniformAdd群 E]
  证明: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero hp)
-/
protected theorem uniformContinuous [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hp : p.ball 0 r in (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero hp)

/--
theorem `uniformContinuous_of_forall'` / 定理 `uniformContinuous_of_forall'`

English:
theorem uniformContinuous_of_forall'
  statement: [UniformSpace E] [IsUniformAddGroup E]
  proof: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)

中文:
定理 uniformContinuous_of_对任意'
  结论: [一致空间 E] [是UniformAdd群 E]
  证明: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)
-/
protected theorem uniformContinuous_of_forall' [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : forall r > 0, p.closedBall 0 r in (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)

/--
theorem `uniformContinuous'` / 定理 `uniformContinuous'`

English:
theorem uniformContinuous'
  statement: [UniformSpace E] [IsUniformAddGroup E]
  proof: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero' hp)

中文:
定理 uniformContinuous'
  结论: [一致空间 E] [是UniformAdd群 E]
  证明: Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero' hp)
-/
protected theorem uniformContinuous' [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real}
    (hp : p.closedBall 0 r in (𝓝 0 : Filter E)) : UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero' hp)

/--
theorem `continuous_of_forall` / 定理 `continuous_of_forall`

English:
theorem continuous_of_forall
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)

中文:
定理 continuous_of_对任意
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)
-/
protected theorem continuous_of_forall [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : forall r > 0, p.ball 0 r in (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero hp)

中文:
定理 continuous
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero hp)
-/
protected theorem continuous [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hp : p.ball 0 r in (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero hp)

/--
theorem `continuous_iff` / 定理 `continuous_iff`

English:
theorem continuous_iff
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: ⟨fun H => p.ball_zero_eq ▸ (H.tendsto' 0 0 (map_zero p)).eventually_lt_const hr, p.continuous⟩

中文:
定理 continuous_iff
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: ⟨fun H => p.ball_zero_eq ▸ (H.tendsto' 0 0 (map_zero p)).eventually_lt_const hr, p.continuous⟩
-/
protected theorem continuous_iff [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hr : 0 < r) :
    Continuous p ↔ p.ball 0 r in 𝓝 0 :=
  ⟨fun H => p.ball_zero_eq ▸ (H.tendsto' 0 0 (map_zero p)).eventually_lt_const hr, p.continuous⟩

/--
theorem `continuous_of_forall'` / 定理 `continuous_of_forall'`

English:
theorem continuous_of_forall'
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)

中文:
定理 continuous_of_对任意'
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)
-/
protected theorem continuous_of_forall' [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : forall r > 0, p.closedBall 0 r in (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)

/--
theorem `continuous'` / 定理 `continuous'`

English:
theorem continuous'
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero' hp)

中文:
定理 continuous'
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: Seminorm.continuous_of_continuousAt_zero (continuousAt_zero' hp)
-/
protected theorem continuous' [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real}
    (hp : p.closedBall 0 r in (𝓝 0 : Filter E)) : Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero' hp)

/--
theorem `continuous_of_le` / 定理 `continuous_of_le`

English:
theorem continuous_of_le
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: by
  refine Seminorm.continuous_of_forall (fun r hr => Filter.mem_of_superset
    (IsOpen.mem_nhds ?_ <| q.mem_ball_self hr) (ball_antitone hpq))
  rw [ball_zero_eq]
  exact isOpen_lt hq continuous_const

中文:
定理 continuous_of_le
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: by
  refine Seminorm.continuous_of_forall (fun r hr => Filter.mem_of_superset
    (IsOpen.mem_nhds ?_ <| q.mem_ball_self hr) (ball_antitone hpq))
  rw [ball_zero_eq]
  exact isOpen_lt hq continuous_const

Depends on / 依赖: Filter, Filter.mem_of_superset, IsOpen, IsOpen.mem_nhds, Seminorm, Seminorm.continuous_of_forall, ball_antitone, ball_zero_eq, continuous_const, continuous_of_forall, isOpen_lt, mem_ball_self, mem_nhds, mem_of_superset, q.mem_ball_self
-/
theorem continuous_of_le [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p q : Seminorm 𝕝 E} (hq : Continuous q) (hpq : p <= q) : Continuous p := by
  refine Seminorm.continuous_of_forall (fun r hr => Filter.mem_of_superset
    (IsOpen.mem_nhds ?_ <| q.mem_ball_self hr) (ball_antitone hpq))
  rw [ball_zero_eq]
  exact isOpen_lt hq continuous_const

/--
theorem `continuous_finsetSum` / 定理 `continuous_finsetSum`

English:
theorem continuous_finsetSum
  statement: [TopologicalSpace E]
  proof: by
  change Continuous (fun x => FunLike.coeAddMonoidHom _ _ _ (∑ i in s, p i) x)
  simp_rw [map_sum, Finset.sum_apply]
  exact _root_.continuous_finsetSum s hp

中文:
定理 continuous_finsetSum
  结论: [拓扑空间 E]
  证明: by
  change Continuous (fun x => FunLike.coeAddMonoidHom _ _ _ (∑ i in s, p i) x)
  simp_rw [map_sum, Finset.sum_apply]
  exact _root_.continuous_finsetSum s hp

Depends on / 依赖: Continuous, Finset, Finset.sum_apply, FunLike, FunLike.coeAddMonoidHom, _root_, _root_.continuous_finsetSum, coeAddMonoidHom, continuous_finsetSum, map_sum, simp_rw, sum_apply
-/
theorem continuous_finsetSum [TopologicalSpace E]
    {p : ι -> Seminorm 𝕝 E} {s : Finset ι} (hp : forall i in s, Continuous (p i)) :
    Continuous ((∑ i in s, p i : Seminorm 𝕝 E) : E -> Real) := by
  change Continuous (fun x => FunLike.coeAddMonoidHom _ _ _ (∑ i in s, p i) x)
  simp_rw [map_sum, Finset.sum_apply]
  exact _root_.continuous_finsetSum s hp

/--
theorem `continuous_finsetSup` / 定理 `continuous_finsetSup`

English:
theorem continuous_finsetSup
  statement: [TopologicalSpace E] [IsTopologicalAddGroup E]
  proof: by
  exact continuous_of_le (continuous_finsetSum hp) (finset_sup_le_sum p s)

中文:
定理 continuous_finsetSup
  结论: [拓扑空间 E] [是拓扑加群 E]
  证明: by
  exact continuous_of_le (continuous_finsetSum hp) (finset_sup_le_sum p s)

Depends on / 依赖: continuous_finsetSum, continuous_of_le, finset_sup_le_sum
-/
theorem continuous_finsetSup [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : ι -> Seminorm 𝕝 E} {s : Finset ι} (hp : forall i in s, Continuous (p i)) :
    Continuous ((s.sup p : Seminorm 𝕝 E) : E -> Real) := by
  exact continuous_of_le (continuous_finsetSum hp) (finset_sup_le_sum p s)

/--
lemma `ball_mem_nhds` / 引理 `ball_mem_nhds`

English:
lemma ball_mem_nhds
  statement: [TopologicalSpace E] {p : Seminorm 𝕝 E} (hp : Continuous p) {r : Real}
  proof: by
  have : Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp.tendsto 0
  simpa only [p.ball_zero_eq] using! this (Iio_mem_nhds hr)

中文:
引理 ball_mem_nhds
  结论: [拓扑空间 E] {p : 半范数 𝕝 E} (hp : 连续 p) {r : 实数}
  证明: by
  have : Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp.tendsto 0
  simpa only [p.ball_zero_eq] using! this (Iio_mem_nhds hr)

Depends on / 依赖: Iio_mem_nhds, Tendsto, ball_zero_eq, hp.tendsto, map_zero, p.ball_zero_eq, tendsto
-/
lemma ball_mem_nhds [TopologicalSpace E] {p : Seminorm 𝕝 E} (hp : Continuous p) {r : Real}
    (hr : 0 < r) : p.ball 0 r in (𝓝 0 : Filter E) := by
  have : Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp.tendsto 0
  simpa only [p.ball_zero_eq] using! this (Iio_mem_nhds hr)

/--
lemma `uniformSpace_eq_of_hasBasis` / 引理 `uniformSpace_eq_of_hasBasis`

English:
lemma uniformSpace_eq_of_hasBasis
  proof: by
  refine IsUniformAddGroup.ext ‹_›
    p.toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup ?_
  apply le_antisymm
  · rw [← @comap_norm_nhds_zero E p.toAddGroupSeminorm.toSeminormedAddGroup, ← tendsto_iff_comap]
    suffices Continuous p from this.tendsto' 0 _ (map_zero p)
    rcas

中文:
引理 uniformSpace_eq_of_hasBasis
  证明: by
  refine IsUniformAddGroup.ext ‹_›
    p.toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup ?_
  apply le_antisymm
  · rw [← @comap_norm_nhds_zero E p.toAddGroupSeminorm.toSeminormedAddGroup, ← tendsto_iff_comap]
    suffices Continuous p from this.tendsto' 0 _ (map_zero p)
    rcas

Depends on / 依赖: Continuous, IsUniformAddGroup, IsUniformAddGroup.ext, NormedAddGroup, NormedAddGroup.nhds_zero_basis_norm_lt, comap_norm_nhds_zero, continuous, le_antisymm, le_basis_iff, map_zero, mem_ball_zero, nhds_zero_basis_norm_lt, p.continuous, p.toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup, p.toAddGroupSeminorm.toSeminormedAddGroup, subset_def, tendsto, tendsto_iff_comap, this.tendsto, toAddGroupSeminorm
-/
lemma uniformSpace_eq_of_hasBasis
    {ι} [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p' : ι -> Prop} {s : ι -> Set E} (p : Seminorm 𝕜 E) (hb : (𝓝 0 : Filter E).HasBasis p' s)
    (h₁ : exists r, p.closedBall 0 r in 𝓝 0) (h₂ : forall i, p' i -> exists r > 0, p.ball 0 r subseteq s i) :
    ‹UniformSpace E› = p.toAddGroupSeminorm.toSeminormedAddGroup.toUniformSpace := by
  refine IsUniformAddGroup.ext ‹_›
    p.toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup ?_
  apply le_antisymm
  · rw [← @comap_norm_nhds_zero E p.toAddGroupSeminorm.toSeminormedAddGroup, ← tendsto_iff_comap]
    suffices Continuous p from this.tendsto' 0 _ (map_zero p)
    rcases h₁ with ⟨r, hr⟩
    exact p.continuous' hr
  · rw [(@NormedAddGroup.nhds_zero_basis_norm_lt E
      p.toAddGroupSeminorm.toSeminormedAddGroup).le_basis_iff hb]
    simpa only [subset_def, mem_ball_zero] using! h₂

/--
lemma `uniformity_eq_of_hasBasis` / 引理 `uniformity_eq_of_hasBasis`

English:
lemma uniformity_eq_of_hasBasis
  proof: by
  rw [uniformSpace_eq_of_hasBasis p hb h₁ h₂]
  simp only [sub_eq_add_neg, ← map_neg_add p]
  rfl

中文:
引理 uniformity_eq_of_hasBasis
  证明: by
  rw [uniformSpace_eq_of_hasBasis p hb h₁ h₂]
  simp only [sub_eq_add_neg, ← map_neg_add p]
  rfl

Depends on / 依赖: map_neg_add, sub_eq_add_neg, uniformSpace_eq_of_hasBasis
-/
lemma uniformity_eq_of_hasBasis
    {ι} [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p' : ι -> Prop} {s : ι -> Set E} (p : Seminorm 𝕜 E) (hb : (𝓝 0 : Filter E).HasBasis p' s)
    (h₁ : exists r, p.closedBall 0 r in 𝓝 0) (h₂ : forall i, p' i -> exists r > 0, p.ball 0 r subseteq s i) :
    𝓤 E = ⨅ r > 0, 𝓟 {x | p (x.1 - x.2) < r} := by
  rw [uniformSpace_eq_of_hasBasis p hb h₁ h₂]
  simp only [sub_eq_add_neg, ← map_neg_add p]
  rfl

end Continuity

section ShellLemmas

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
lemma `rescale_to_shell_zpow` / 引理 `rescale_to_shell_zpow`

English:
lemma rescale_to_shell_zpow
  statement: (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real}
  proof: by
  have xεpos : 0 < (p x) / ε := by positivity
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := by positivity
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by rw [norm_zpow]; exact xεpos.trans hn.2
  refine ⟨-(n + 1), ?_, ?_, ?_, ?_⟩
  · show c ^ (-(n + 1)) != 0; exact zpow_ne_zer

中文:
引理 rescale_to_shell_zpow
  结论: (p : 半范数 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : 实数}
  证明: by
  have xεpos : 0 < (p x) / ε := by positivity
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := by positivity
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by rw [norm_zpow]; exact xεpos.trans hn.2
  refine ⟨-(n + 1), ?_, ?_, ?_, ?_⟩
  · show c ^ (-(n + 1)) != 0; exact zpow_ne_zer

Depends on / 依赖: div_eq_inv_mul, exists_mem_Ico_zpow, map_smul_eq_mul, mul_comm, norm_inv, norm_pos_iff, norm_zpow, pos.trans, zpow_ne_zero, zpow_neg
-/
lemma rescale_to_shell_zpow (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real}
    (εpos : 0 < ε) {x : E} (hx : p x != 0) : exists n : Int, c ^ n != 0 ∧
    p (c ^ n • x) < ε ∧ (ε / ‖c‖ <= p (c ^ n • x)) ∧ (‖c ^ n‖⁻¹ <= ε⁻¹ * ‖c‖ * p x) := by
  have xεpos : 0 < (p x) / ε := by positivity
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := by positivity
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by rw [norm_zpow]; exact xεpos.trans hn.2
  refine ⟨-(n + 1), ?_, ?_, ?_, ?_⟩
  · show c ^ (-(n + 1)) != 0; exact zpow_ne_zero _ (norm_pos_iff.1 cpos)
  · show p ((c ^ (-(n + 1))) • x) < ε
    rw [map_smul_eq_mul]; rw [zpow_neg]; rw [norm_inv]; rw [← div_eq_inv_mul]; rw [div_lt_iff₀ cnpos]; rw [mul_comm]; rw [norm_zpow]
    exact (div_lt_iff₀ εpos).1 (hn.2)
  · show ε / ‖c‖ <= p (c ^ (-(n + 1)) • x)
    rw [zpow_neg]; rw [div_le_iff₀ cpos]; rw [map_smul_eq_mul]; rw [norm_inv]; rw [norm_zpow]; rw [zpow_add₀ (ne_of_gt cpos)]; rw [zpow_one]; rw [mul_inv_rev]; rw [mul_comm]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_inv_cancel₀ (ne_of_gt cpos)]; rw [one_mul]; rw [← div_eq_inv_mul]; rw [le_div_iff₀ (zpow_pos cpos _)]; rw [mul_comm]
    exact (le_div_iff₀ εpos).1 hn.1
  · show ‖(c ^ (-(n + 1)))‖⁻¹ <= ε⁻¹ * ‖c‖ * p x
    have : ε⁻¹ * ‖c‖ * p x = ε⁻¹ * p x * ‖c‖ := by ring
    rw [zpow_neg]; rw [norm_inv]; rw [inv_inv]; rw [norm_zpow]; rw [zpow_add₀ (ne_of_gt cpos)]; rw [zpow_one]; rw [this]; rw [← div_eq_inv_mul]
    gcongr; exact hn.1

/--
lemma `rescale_to_shell` / 引理 `rescale_to_shell`

English:
lemma rescale_to_shell
  statement: (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E}
  proof: let ⟨_, hn⟩ := p.rescale_to_shell_zpow hc εpos hx; ⟨_, hn⟩

中文:
引理 rescale_to_shell
  结论: (p : 半范数 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : 实数} (εpos : 0 < ε) {x : E}
  证明: let ⟨_, hn⟩ := p.rescale_to_shell_zpow hc εpos hx; ⟨_, hn⟩

Depends on / 依赖: p.rescale_to_shell_zpow, rescale_to_shell_zpow
-/
lemma rescale_to_shell (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E}
    (hx : p x != 0) :
    exists d : 𝕜, d != 0 ∧ p (d • x) < ε ∧ (ε / ‖c‖ <= p (d • x)) ∧ (‖d‖⁻¹ <= ε⁻¹ * ‖c‖ * p x) :=
let ⟨_, hn⟩ := p.rescale_to_shell_zpow hc εpos hx; ⟨_, hn⟩

/--
lemma `bound_of_shell` / 引理 `bound_of_shell`

English:
lemma bound_of_shell
  proof: by
  rcases p.rescale_to_shell hc ε_pos hx with ⟨δ, hδ, δxle, leδx, -⟩
  simpa only [map_smul_eq_mul, mul_left_comm C, mul_le_mul_iff_right₀ (norm_pos_iff.2 hδ)]
    using hf (δ • x) leδx δxle

中文:
引理 bound_of_shell
  证明: by
  rcases p.rescale_to_shell hc ε_pos hx with ⟨δ, hδ, δxle, leδx, -⟩
  simpa only [map_smul_eq_mul, mul_left_comm C, mul_le_mul_iff_right₀ (norm_pos_iff.2 hδ)]
    using hf (δ • x) leδx δxle

Depends on / 依赖: map_smul_eq_mul, mul_left_comm, norm_pos_iff, p.rescale_to_shell, rescale_to_shell
-/
lemma bound_of_shell
    (p q : Seminorm 𝕜 E) {ε C : Real} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : forall x, ε / ‖c‖ <= p x -> p x < ε -> q x <= C * p x) {x : E} (hx : p x != 0) :
    q x <= C * p x := by
  rcases p.rescale_to_shell hc ε_pos hx with ⟨δ, hδ, δxle, leδx, -⟩
  simpa only [map_smul_eq_mul, mul_left_comm C, mul_le_mul_iff_right₀ (norm_pos_iff.2 hδ)]
    using hf (δ • x) leδx δxle

/--
lemma `bound_of_shell_smul` / 引理 `bound_of_shell_smul`

English:
lemma bound_of_shell_smul
  proof: Seminorm.bound_of_shell p q ε_pos hc hf hx

中文:
引理 bound_of_shell_smul
  证明: Seminorm.bound_of_shell p q ε_pos hc hf hx

Depends on / 依赖: Seminorm, Seminorm.bound_of_shell, bound_of_shell
-/
lemma bound_of_shell_smul
    (p q : Seminorm 𝕜 E) {ε : Real} {C : Real>=0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : forall x, ε / ‖c‖ <= p x -> p x < ε -> q x <= (C • p) x) {x : E} (hx : p x != 0) :
    q x <= (C • p) x :=
  Seminorm.bound_of_shell p q ε_pos hc hf hx

/--
lemma `bound_of_shell_sup` / 引理 `bound_of_shell_sup`

English:
lemma bound_of_shell_sup
  statement: (p : ι -> Seminorm 𝕜 E) (s : Finset ι)
  proof: by
  rcases hx with ⟨j, hj, hjx⟩
  have : (s.sup p) x != 0 :=
    ne_of_gt ((hjx.symm.lt_of_le <| apply_nonneg _ _).trans_le (le_finset_sup_apply hj))
  refine (s.sup p).bound_of_shell_smul q ε_pos hc (fun y hle hlt => ?_) this
  rcases exists_apply_eq_finset_sup p ⟨j, hj⟩ y with ⟨i, hi, hiy⟩
  rw [

中文:
引理 bound_of_shell_sup
  结论: (p : ι -> 半范数 𝕜 E) (s : 有限集 ι)
  证明: by
  rcases hx with ⟨j, hj, hjx⟩
  have : (s.sup p) x != 0 :=
    ne_of_gt ((hjx.symm.lt_of_le <| apply_nonneg _ _).trans_le (le_finset_sup_apply hj))
  refine (s.sup p).bound_of_shell_smul q ε_pos hc (fun y hle hlt => ?_) this
  rcases exists_apply_eq_finset_sup p ⟨j, hj⟩ y with ⟨i, hi, hiy⟩
  rw [

Depends on / 依赖: apply_nonneg, bound_of_shell_smul, exists_apply_eq_finset_sup, hjx.symm.lt_of_le, le_finset_sup_apply, lt_of_le, ne_of_gt, s.sup, smul_apply, trans_le, trans_lt
-/
lemma bound_of_shell_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι)
    (q : Seminorm 𝕜 E) {ε : Real} {C : Real>=0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : forall x, (forall i in s, p i x < ε) -> forall j in s, ε / ‖c‖ <= p j x -> q x <= (C • p j) x)
    {x : E} (hx : exists j, j in s ∧ p j x != 0) :
    q x <= (C • s.sup p) x := by
  rcases hx with ⟨j, hj, hjx⟩
  have : (s.sup p) x != 0 :=
    ne_of_gt ((hjx.symm.lt_of_le <| apply_nonneg _ _).trans_le (le_finset_sup_apply hj))
  refine (s.sup p).bound_of_shell_smul q ε_pos hc (fun y hle hlt => ?_) this
  rcases exists_apply_eq_finset_sup p ⟨j, hj⟩ y with ⟨i, hi, hiy⟩
  rw [smul_apply]; rw [hiy]
  exact hf y (fun k hk => (le_finset_sup_apply hk).trans_lt hlt) i hi (hiy ▸ hle)

end ShellLemmas

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
lemma `bddAbove_of_absorbent` / 引理 `bddAbove_of_absorbent`

English:
lemma bddAbove_of_absorbent
  statement: {ι : Sort*} {p : ι -> Seminorm 𝕜 E} {s : Set E} (hs : Absorbent 𝕜 s)
  proof: by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨c, hc₀, hc⟩ : exists c != 0, (c : 𝕜) • x in s :=
    (eventually_mem_nhdsWithin.and (hs.eventually_nhdsNE_zero x)).exists
  rcases h _ hc with ⟨M, hM⟩
  refine ⟨M / ‖c‖, forall_mem_range.mpr fun i => (le_div_iff₀' (norm_pos_iff.2 hc₀)).2 ?_⟩


中文:
引理 bddAbove_of_absorbent
  结论: {ι : 类型层*} {p : ι -> 半范数 𝕜 E} {s : 集合 E} (hs : Absorbent 𝕜 s)
  证明: by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨c, hc₀, hc⟩ : exists c != 0, (c : 𝕜) • x in s :=
    (eventually_mem_nhdsWithin.and (hs.eventually_nhdsNE_zero x)).exists
  rcases h _ hc with ⟨M, hM⟩
  refine ⟨M / ‖c‖, forall_mem_range.mpr fun i => (le_div_iff₀' (norm_pos_iff.2 hc₀)).2 ?_⟩


Depends on / 依赖: Seminorm, Seminorm.bddAbove_range_iff, bddAbove_range_iff, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.and, eventually_nhdsNE_zero, forall_mem_range, forall_mem_range.mpr, hs.eventually_nhdsNE_zero, map_smul_eq_mul, norm_pos_iff
-/
lemma bddAbove_of_absorbent {ι : Sort*} {p : ι -> Seminorm 𝕜 E} {s : Set E} (hs : Absorbent 𝕜 s)
    (h : forall x in s, BddAbove (range (p · x))) : BddAbove (range p) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨c, hc₀, hc⟩ : exists c != 0, (c : 𝕜) • x in s :=
    (eventually_mem_nhdsWithin.and (hs.eventually_nhdsNE_zero x)).exists
  rcases h _ hc with ⟨M, hM⟩
  refine ⟨M / ‖c‖, forall_mem_range.mpr fun i => (le_div_iff₀' (norm_pos_iff.2 hc₀)).2 ?_⟩
  exact hM ⟨i, map_smul_eq_mul ..⟩

end NontriviallyNormedField

end Seminorm

/-! ### The norm as a seminorm -/


section normSeminorm

variable (𝕜) (E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {r : Real}

/--
Definition of `normSeminorm` / `normSeminorm` 的定义

English:
definition normSeminorm
  signature: : Seminorm 𝕜 E
  body: { normAddGroupSeminorm E with smul' := norm_smul }

@[simp]

中文:
定义 normSeminorm
  签名: : 半范数 𝕜 E
  定义体: { normAddGroupSeminorm E with smul' := norm_smul }

@[simp]

Depends on / 依赖: normAddGroupSeminorm, norm_smul
-/
def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }

@[simp]
/--
theorem `coe_normSeminorm` / 定理 `coe_normSeminorm`

English:
theorem coe_normSeminorm
  statement: ⇑(normSeminorm 𝕜 E) = norm
  proof: rfl

@[simp]

中文:
定理 coe_normSeminorm
  结论: ⇑(normSeminorm 𝕜 E) = norm
  证明: rfl

@[simp]
-/
theorem coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm :=
  rfl

@[simp]
/--
theorem `ball_normSeminorm` / 定理 `ball_normSeminorm`

English:
theorem ball_normSeminorm
  statement: (normSeminorm 𝕜 E).ball = Metric.ball
  proof: by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]

@[simp]

中文:
定理 ball_normSeminorm
  结论: (normSeminorm 𝕜 E).ball = Metric.ball
  证明: by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]

@[simp]

Depends on / 依赖: Metric, Metric.mem_ball, Seminorm, Seminorm.mem_ball, coe_normSeminorm, dist_eq_norm, mem_ball
-/
theorem ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.ball := by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]

@[simp]
/--
theorem `closedBall_normSeminorm` / 定理 `closedBall_normSeminorm`

English:
theorem closedBall_normSeminorm
  statement: (normSeminorm 𝕜 E).closedBall = Metric.closedBall
  proof: by
  ext x r y
  simp only [Seminorm.mem_closedBall, Metric.mem_closedBall, coe_normSeminorm, dist_eq_norm]

中文:
定理 closedBall_normSeminorm
  结论: (normSeminorm 𝕜 E).closedBall = Metric.closedBall
  证明: by
  ext x r y
  simp only [Seminorm.mem_closedBall, Metric.mem_closedBall, coe_normSeminorm, dist_eq_norm]

Depends on / 依赖: Metric, Metric.mem_closedBall, Seminorm, Seminorm.mem_closedBall, coe_normSeminorm, dist_eq_norm, mem_closedBall
-/
theorem closedBall_normSeminorm : (normSeminorm 𝕜 E).closedBall = Metric.closedBall := by
  ext x r y
  simp only [Seminorm.mem_closedBall, Metric.mem_closedBall, coe_normSeminorm, dist_eq_norm]

variable {𝕜 E} {x : E}

/--
theorem `absorbent_ball_zero` / 定理 `absorbent_ball_zero`

English:
theorem absorbent_ball_zero
  given: (hr : 0 < r)
  statement: Absorbent 𝕜 (Metric.ball (0 : E) r)
  proof: by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball_zero hr

中文:
定理 absorbent_ball_zero
  条件: (hr : 0 < r)
  结论: Absorbent 𝕜 (Metric.ball (0 : E) r)
  证明: by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball_zero hr

Depends on / 依赖: absorbent_ball_zero, ball_normSeminorm, normSeminorm
-/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball_zero hr

/--
theorem `absorbent_ball` / 定理 `absorbent_ball`

English:
theorem absorbent_ball
  given: (hx : ‖x‖ < r)
  statement: Absorbent 𝕜 (Metric.ball x r)
  proof: by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball hx

中文:
定理 absorbent_ball
  条件: (hx : ‖x‖ < r)
  结论: Absorbent 𝕜 (Metric.ball x r)
  证明: by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball hx

Depends on / 依赖: absorbent_ball, ball_normSeminorm, normSeminorm
-/
theorem absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball x r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball hx

/--
theorem `balanced_ball_zero` / 定理 `balanced_ball_zero`

English:
theorem balanced_ball_zero
  statement: Balanced 𝕜 (Metric.ball (0 : E) r)
  proof: by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

中文:
定理 balanced_ball_zero
  结论: Balanced 𝕜 (Metric.ball (0 : E) r)
  证明: by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

Depends on / 依赖: balanced_ball_zero, ball_normSeminorm, normSeminorm
-/
theorem balanced_ball_zero : Balanced 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

/--
theorem `balanced_closedBall_zero` / 定理 `balanced_closedBall_zero`

English:
theorem balanced_closedBall_zero
  statement: Balanced 𝕜 (Metric.closedBall (0 : E) r)
  proof: by
  rw [← closedBall_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_closedBall_zero r

中文:
定理 balanced_closedBall_zero
  结论: Balanced 𝕜 (Metric.closedBall (0 : E) r)
  证明: by
  rw [← closedBall_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_closedBall_zero r

Depends on / 依赖: balanced_closedBall_zero, closedBall_normSeminorm, normSeminorm
-/
theorem balanced_closedBall_zero : Balanced 𝕜 (Metric.closedBall (0 : E) r) := by
  rw [← closedBall_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_closedBall_zero r

/--
lemma `rescale_to_shell_semi_normed_zpow` / 引理 `rescale_to_shell_semi_normed_zpow`

English:
lemma rescale_to_shell_semi_normed_zpow
  statement: {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E}
  proof: (normSeminorm 𝕜 E).rescale_to_shell_zpow hc εpos hx

中文:
引理 rescale_to_shell_semi_normed_zpow
  结论: {c : 𝕜} (hc : 1 < ‖c‖) {ε : 实数} (εpos : 0 < ε) {x : E}
  证明: (normSeminorm 𝕜 E).rescale_to_shell_zpow hc εpos hx

Depends on / 依赖: normSeminorm, rescale_to_shell_zpow
-/
lemma rescale_to_shell_semi_normed_zpow {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E}
    (hx : ‖x‖ != 0) :
    exists n : Int, c ^ n != 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ <= ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ <= ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell_zpow hc εpos hx

/--
lemma `rescale_to_shell_semi_normed` / 引理 `rescale_to_shell_semi_normed`

English:
lemma rescale_to_shell_semi_normed
  statement: {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε)
  proof: (normSeminorm 𝕜 E).rescale_to_shell hc εpos hx

中文:
引理 rescale_to_shell_semi_normed
  结论: {c : 𝕜} (hc : 1 < ‖c‖) {ε : 实数} (εpos : 0 < ε)
  证明: (normSeminorm 𝕜 E).rescale_to_shell hc εpos hx

Depends on / 依赖: normSeminorm, rescale_to_shell
-/
lemma rescale_to_shell_semi_normed {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε)
    {x : E} (hx : ‖x‖ != 0) :
    exists d : 𝕜, d != 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ <= ‖d • x‖) ∧ (‖d‖⁻¹ <= ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell hc εpos hx

/--
lemma `rescale_to_shell_zpow` / 引理 `rescale_to_shell_zpow`

English:
lemma rescale_to_shell_zpow
  statement: [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
  proof: rescale_to_shell_semi_normed_zpow hc εpos (norm_ne_zero_iff.mpr hx)

中文:
引理 rescale_to_shell_zpow
  结论: [赋范交换加群 F] [赋范空间 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
  证明: rescale_to_shell_semi_normed_zpow hc εpos (norm_ne_zero_iff.mpr hx)

Depends on / 依赖: norm_ne_zero_iff, norm_ne_zero_iff.mpr, rescale_to_shell_semi_normed_zpow
-/
lemma rescale_to_shell_zpow [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : Real} (εpos : 0 < ε) {x : F} (hx : x != 0) :
    exists n : Int, c ^ n != 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ <= ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ <= ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed_zpow hc εpos (norm_ne_zero_iff.mpr hx)

/--
lemma `rescale_to_shell` / 引理 `rescale_to_shell`

English:
lemma rescale_to_shell
  statement: [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
  proof: rescale_to_shell_semi_normed hc εpos (norm_ne_zero_iff.mpr hx)

中文:
引理 rescale_to_shell
  结论: [赋范交换加群 F] [赋范空间 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
  证明: rescale_to_shell_semi_normed hc εpos (norm_ne_zero_iff.mpr hx)

Depends on / 依赖: norm_ne_zero_iff, norm_ne_zero_iff.mpr, rescale_to_shell_semi_normed
-/
lemma rescale_to_shell [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : Real} (εpos : 0 < ε) {x : F} (hx : x != 0) :
    exists d : 𝕜, d != 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ <= ‖d • x‖) ∧ (‖d‖⁻¹ <= ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed hc εpos (norm_ne_zero_iff.mpr hx)

end normSeminorm
