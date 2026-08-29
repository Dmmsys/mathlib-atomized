/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Subgroup
public import Mathlib.Analysis.Normed.Group.Submodule

import Mathlib.Data.Fintype.Order

/-!
# Normed rings

In this file we define (semi)normed rings. We also prove some theorems about these definitions.

A normed ring instance can be constructed from a given real absolute value on a ring via
`AbsoluteValue.toNormedRing`.
-/

@[expose] public section

-- Guard against import creep.
assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg
  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real
  RestrictScalars

variable {G α β ι : Type*}

open Filter
open scoped Topology NNReal

/--
Definition of `NonUnitalSeminormedRing` / `NonUnitalSeminormedRing` 的定义

English:
class NonUnitalSeminormedRing
  parameters: (α : Type*)
  extends: Norm α, NonUnitalRing α, 
  axioms and operations (2):
    - dist_eq : forall x y, dist x y = norm (-x + y)
    - norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

中文:
类 非幺Seminormed环
  参数: (α : 类型)
  继承: 范数 α, 非幺环 α, 
  公理与运算 (2 个):
    - dist_eq : 对任意 x y, dist x y = norm (-x + y)
    - norm_mul_le : 对任意 a b, norm (a * b) <= norm a * norm b
-/
class NonUnitalSeminormedRing (α : Type*) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : forall x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  protected norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalSeminormedRing.toNonUnitalRing

/--
Definition of `SeminormedRing` / `SeminormedRing` 的定义

English:
class SeminormedRing
  parameters: (α : Type*)
  extends: Norm α, Ring α, PseudoMetricSpace α
  axioms and operations (2):
    - dist_eq : forall x y, dist x y = norm (-x + y)
    - norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

中文:
类 Seminormed环
  参数: (α : 类型)
  继承: 范数 α, 环 α, 伪度量空间 α
  公理与运算 (2 个):
    - dist_eq : 对任意 x y, dist x y = norm (-x + y)
    - norm_mul_le : 对任意 a b, norm (a * b) <= norm a * norm b
-/
class SeminormedRing (α : Type*) extends Norm α, Ring α, PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : forall x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] SeminormedRing.toRing

-- see Note [lower instance priority]
/-- A seminormed ring is a non-unital seminormed ring. -/
instance (priority := 100) SeminormedRing.toNonUnitalSeminormedRing [β : SeminormedRing α] :
    NonUnitalSeminormedRing α :=
  { β with }

/--
Definition of `NonUnitalNormedRing` / `NonUnitalNormedRing` 的定义

English:
class NonUnitalNormedRing
  parameters: (α : Type*)
  extends: Norm α, NonUnitalRing α, MetricSpace α
  axioms and operations (2):
    - dist_eq : forall x y, dist x y = norm (-x + y)
    - norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

中文:
类 非幺赋范环
  参数: (α : 类型)
  继承: 范数 α, 非幺环 α, 度量空间 α
  公理与运算 (2 个):
    - dist_eq : 对任意 x y, dist x y = norm (-x + y)
    - norm_mul_le : 对任意 a b, norm (a * b) <= norm a * norm b
-/
class NonUnitalNormedRing (α : Type*) extends Norm α, NonUnitalRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : forall x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalNormedRing.toNonUnitalRing

-- see Note [lower instance priority]
/-- A non-unital normed ring is a non-unital seminormed ring. -/
instance (priority := 100) NonUnitalNormedRing.toNonUnitalSeminormedRing
    [β : NonUnitalNormedRing α] : NonUnitalSeminormedRing α :=
  { β with }

/--
Definition of `NormedRing` / `NormedRing` 的定义

English:
class NormedRing
  parameters: (α : Type*)
  extends: Norm α, Ring α, MetricSpace α
  axioms and operations (2):
    - dist_eq : forall x y, dist x y = norm (-x + y)
    - norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

中文:
类 赋范环
  参数: (α : 类型)
  继承: 范数 α, 环 α, 度量空间 α
  公理与运算 (2 个):
    - dist_eq : 对任意 x y, dist x y = norm (-x + y)
    - norm_mul_le : 对任意 a b, norm (a * b) <= norm a * norm b
-/
class NormedRing (α : Type*) extends Norm α, Ring α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : forall x y, dist x y = norm (-x + y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : forall a b, norm (a * b) <= norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NormedRing.toRing

-- see Note [lower instance priority]
/-- A normed ring is a seminormed ring. -/
instance (priority := 100) NormedRing.toSeminormedRing [β : NormedRing α] : SeminormedRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed ring is a non-unital normed ring. -/
instance (priority := 100) NormedRing.toNonUnitalNormedRing [β : NormedRing α] :
    NonUnitalNormedRing α :=
  { β with }

/--
Definition of `NonUnitalSeminormedCommRing` / `NonUnitalSeminormedCommRing` 的定义

English:
class NonUnitalSeminormedCommRing
  parameters: (α : Type*)
  extends: NonUnitalSeminormedRing α, NonUnitalCommRing α
  (no additional axioms)

中文:
类 非幺SeminormedComm环
  参数: (α : 类型)
  继承: 非幺Seminormed环 α, 非幺交换环 α
  (无附加公理)
-/
class NonUnitalSeminormedCommRing (α : Type*)
    extends NonUnitalSeminormedRing α, NonUnitalCommRing α where

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalSeminormedCommRing.toNonUnitalCommRing

/--
Definition of `NonUnitalNormedCommRing` / `NonUnitalNormedCommRing` 的定义

English:
class NonUnitalNormedCommRing
  parameters: (α : Type*)
  extends: NonUnitalNormedRing α, NonUnitalCommRing α
  (no additional axioms)

中文:
类 非幺NormedComm环
  参数: (α : 类型)
  继承: 非幺赋范环 α, 非幺交换环 α
  (无附加公理)
-/
class NonUnitalNormedCommRing (α : Type*) extends NonUnitalNormedRing α, NonUnitalCommRing α where

-- see Note [lower instance priority]
attribute [instance 10] NonUnitalNormedCommRing.toNonUnitalCommRing

-- see Note [lower instance priority]
/-- A non-unital normed commutative ring is a non-unital seminormed commutative ring. -/
instance (priority := 100) NonUnitalNormedCommRing.toNonUnitalSeminormedCommRing
    [β : NonUnitalNormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

/--
Definition of `SeminormedCommRing` / `SeminormedCommRing` 的定义

English:
class SeminormedCommRing
  parameters: (α : Type*)
  extends: SeminormedRing α, CommRing α
  (no additional axioms)

中文:
类 SeminormedComm环
  参数: (α : 类型)
  继承: Seminormed环 α, 交换环 α
  (无附加公理)
-/
class SeminormedCommRing (α : Type*) extends SeminormedRing α, CommRing α where

-- see Note [lower instance priority]
attribute [instance 10] SeminormedCommRing.toCommRing

/--
Definition of `NormedCommRing` / `NormedCommRing` 的定义

English:
class NormedCommRing
  parameters: (α : Type*)
  extends: NormedRing α, CommRing α
  (no additional axioms)

中文:
类 NormedComm环
  参数: (α : 类型)
  继承: 赋范环 α, 交换环 α
  (无附加公理)
-/
class NormedCommRing (α : Type*) extends NormedRing α, CommRing α where

-- see Note [lower instance priority]
attribute [instance 10] NormedCommRing.toCommRing

-- see Note [lower instance priority]
/-- A seminormed commutative ring is a non-unital seminormed commutative ring. -/
instance (priority := 100) SeminormedCommRing.toNonUnitalSeminormedCommRing
    [β : SeminormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed commutative ring is a non-unital normed commutative ring. -/
instance (priority := 100) NormedCommRing.toNonUnitalNormedCommRing
    [β : NormedCommRing α] : NonUnitalNormedCommRing α :=
  { β with }

-- see Note [lower instance priority]
/-- A normed commutative ring is a seminormed commutative ring. -/
instance (priority := 100) NormedCommRing.toSeminormedCommRing [β : NormedCommRing α] :
    SeminormedCommRing α :=
  { β with }

/--
Instance `PUnit.normedCommRing` / 实例 `PUnit.normedCommRing`

English:
instance PUnit.normedCommRing
  signature: : NormedCommRing PUnit
  body: { PUnit.normedAddCommGroup, PUnit.commRing with
    norm_mul_le _ _ := by simp }

中文:
实例 命题单元.normedCommRing
  签名: : NormedComm环 命题单元
  定义体: { PUnit.normedAddCommGroup, PUnit.commRing with
    norm_mul_le _ _ := by simp }

Depends on / 依赖: PUnit.commRing, PUnit.normedAddCommGroup, commRing, norm_mul_le, normedAddCommGroup
-/
instance PUnit.normedCommRing : NormedCommRing PUnit :=
  { PUnit.normedAddCommGroup, PUnit.commRing with
    norm_mul_le _ _ := by simp }

section NormOneClass

/--
Definition of `NormOneClass` / `NormOneClass` 的定义

English:
class NormOneClass
  parameters: (α : Type*) [Norm α] [One α]
  axioms and operations (1):
    - norm_one : ‖(1 : α)‖ = 1

中文:
类 NormOne类
  参数: (α : 类型) [范数 α] [幺 α]
  公理与运算 (1 个):
    - norm_one : ‖(1 : α)‖ = 1
-/
class NormOneClass (α : Type*) [Norm α] [One α] : Prop where
  /-- The norm of the multiplicative identity is 1. -/
  norm_one : ‖(1 : α)‖ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup G] [One G] [NormOneClass G]

/--
lemma `nnnorm_one` / 引理 `nnnorm_one`

English:
lemma nnnorm_one
  statement: ‖(1 : G)‖₊ = 1
  proof: NNReal.eq norm_one

中文:
引理 nnnorm_one
  结论: ‖(1 : G)‖₊ = 1
  证明: NNReal.eq norm_one
-/
@[simp] lemma nnnorm_one : ‖(1 : G)‖₊ = 1 := NNReal.eq norm_one
/--
lemma `enorm_one` / 引理 `enorm_one`

English:
lemma enorm_one
  statement: ‖(1 : G)‖ₑ = 1
  proof: by simp [enorm]

中文:
引理 enorm_one
  结论: ‖(1 : G)‖ₑ = 1
  证明: by simp [enorm]
-/
@[simp] lemma enorm_one : ‖(1 : G)‖ₑ = 1 := by simp [enorm]

/--
theorem `NormOneClass.nontrivial` / 定理 `NormOneClass.nontrivial`

English:
theorem NormOneClass.nontrivial
  statement: Nontrivial G
  proof: nontrivial_of_ne 0 1 ne_of_apply_ne norm by simp

中文:
定理 NormOne类.nontrivial
  结论: 非平凡 G
  证明: nontrivial_of_ne 0 1 ne_of_apply_ne norm by simp

Depends on / 依赖: ne_of_apply_ne, nontrivial_of_ne
-/
theorem NormOneClass.nontrivial : Nontrivial G :=
nontrivial_of_ne 0 1 ne_of_apply_ne norm by simp

end SeminormedAddCommGroup

end NormOneClass

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalNormedRing.toNormedAddCommGroup [β : NonUnitalNormedRing α] :
    NormedAddCommGroup α :=
  { β with }

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSeminormedRing.toSeminormedAddCommGroup
    [NonUnitalSeminormedRing α] : SeminormedAddCommGroup α :=
  { ‹NonUnitalSeminormedRing α› with }

/--
Instance `ULift.normOneClass` / 实例 `ULift.normOneClass`

English:
instance ULift.normOneClass
  signature: [SeminormedAddCommGroup α] [One α] [NormOneClass α]
  body: ⟨by simp [ULift.norm_def]⟩

中文:
实例 类型层提升.normOneClass
  签名: [SeminormedAddComm群 α] [幺 α] [NormOne类 α]
  定义体: ⟨by simp [ULift.norm_def]⟩

Depends on / 依赖: ULift.norm_def, norm_def
-/
instance ULift.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩

/--
Instance `Prod.normOneClass` / 实例 `Prod.normOneClass`

English:
instance Prod.normOneClass
  signature: [SeminormedAddCommGroup α] [One α] [NormOneClass α]
  body: ⟨by simp [Prod.norm_def]⟩

中文:
实例 积类型.normOneClass
  签名: [SeminormedAddComm群 α] [幺 α] [NormOne类 α]
  定义体: ⟨by simp [Prod.norm_def]⟩

Depends on / 依赖: Prod.norm_def, norm_def
-/
instance Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α]
    [SeminormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩

/--
Instance `Pi.normOneClass` / 实例 `Pi.normOneClass`

English:
instance Pi.normOneClass
  signature: {ι : Type*} {α : ι -> Type*} [Nonempty ι] [Fintype ι]
  body: ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩

中文:
实例 依赖函数类型.normOneClass
  签名: {ι : 类型} {α : ι -> 类型} [非空 ι] [有限类型 ι]
  定义体: ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩

Depends on / 依赖: Finset, Finset.sup_const, Finset.univ_nonempty, Pi.norm_def, norm_def, sup_const, univ_nonempty
-/
instance Pi.normOneClass {ι : Type*} {α : ι -> Type*} [Nonempty ι] [Fintype ι]
    [forall i, SeminormedAddCommGroup (α i)] [forall i, One (α i)] [forall i, NormOneClass (α i)] :
    NormOneClass (forall i, α i) :=
  ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩

/--
Instance `MulOpposite.normOneClass` / 实例 `MulOpposite.normOneClass`

English:
instance MulOpposite.normOneClass
  signature: [SeminormedAddCommGroup α] [One α] [NormOneClass α]
  body: ⟨@norm_one α _ _ _⟩

中文:
实例 MulOpposite.normOneClass
  签名: [SeminormedAddComm群 α] [幺 α] [NormOne类 α]
  定义体: ⟨@norm_one α _ _ _⟩

Depends on / 依赖: norm_one
-/
instance MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α] {a a₁ a₂ b c : α}

/--
theorem `norm_mul_le` / 定理 `norm_mul_le`

English:
theorem norm_mul_le
  given: (a b : α)
  statement: ‖a * b‖ <= ‖a‖ * ‖b‖
  proof: NonUnitalSeminormedRing.norm_mul_le a b

中文:
定理 norm_mul_le
  条件: (a b : α)
  结论: ‖a * b‖ <= ‖a‖ * ‖b‖
  证明: NonUnitalSeminormedRing.norm_mul_le a b

Depends on / 依赖: NonUnitalSeminormedRing, NonUnitalSeminormedRing.norm_mul_le, norm_mul_le
-/
theorem norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖ :=
  NonUnitalSeminormedRing.norm_mul_le a b

/--
theorem `nnnorm_mul_le` / 定理 `nnnorm_mul_le`

English:
theorem nnnorm_mul_le
  given: (a b : α)
  statement: ‖a * b‖₊ <= ‖a‖₊ * ‖b‖₊
  proof: norm_mul_le a b

中文:
定理 nnnorm_mul_le
  条件: (a b : α)
  结论: ‖a * b‖₊ <= ‖a‖₊ * ‖b‖₊
  证明: norm_mul_le a b

Depends on / 依赖: norm_mul_le
-/
theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ <= ‖a‖₊ * ‖b‖₊ := norm_mul_le a b

/--
lemma `norm_mul_le_of_le` / 引理 `norm_mul_le_of_le`

English:
lemma norm_mul_le_of_le
  given: {r₁ r₂ : Real} (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂)
  statement: ‖a₁ * a₂‖ <= r₁ * r₂
  proof: (norm_mul_le ..).trans mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

中文:
引理 norm_mul_le_of_le
  条件: {r₁ r₂ : 实数} (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂)
  结论: ‖a₁ * a₂‖ <= r₁ * r₂
  证明: (norm_mul_le ..).trans mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

Depends on / 依赖: mul_le_mul, norm_mul_le, norm_nonneg
-/
lemma norm_mul_le_of_le {r₁ r₂ : Real} (h₁ : ‖a₁‖ <= r₁) (h₂ : ‖a₂‖ <= r₂) : ‖a₁ * a₂‖ <= r₁ * r₂ :=
(norm_mul_le ..).trans mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

/--
lemma `nnnorm_mul_le_of_le` / 引理 `nnnorm_mul_le_of_le`

English:
lemma nnnorm_mul_le_of_le
  given: {r₁ r₂ : Real>=0} (h₁ : ‖a₁‖₊ <= r₁) (h₂ : ‖a₂‖₊ <= r₂)
  proof: (nnnorm_mul_le ..).trans mul_le_mul' h₁ h₂

中文:
引理 nnnorm_mul_le_of_le
  条件: {r₁ r₂ : 实数>=0} (h₁ : ‖a₁‖₊ <= r₁) (h₂ : ‖a₂‖₊ <= r₂)
  证明: (nnnorm_mul_le ..).trans mul_le_mul' h₁ h₂

Depends on / 依赖: mul_le_mul, nnnorm_mul_le
-/
lemma nnnorm_mul_le_of_le {r₁ r₂ : Real>=0} (h₁ : ‖a₁‖₊ <= r₁) (h₂ : ‖a₂‖₊ <= r₂) :
‖a₁ * a₂‖₊ <= r₁ * r₂ := (nnnorm_mul_le ..).trans mul_le_mul' h₁ h₂

/--
lemma `norm_mul₃_le` / 引理 `norm_mul₃_le`

English:
lemma norm_mul₃_le
  statement: ‖a * b * c‖ <= ‖a‖ * ‖b‖ * ‖c‖
  proof: norm_mul_le_of_le (norm_mul_le ..) le_rfl

中文:
引理 norm_mul₃_le
  结论: ‖a * b * c‖ <= ‖a‖ * ‖b‖ * ‖c‖
  证明: norm_mul_le_of_le (norm_mul_le ..) le_rfl

Depends on / 依赖: le_rfl, norm_mul_le, norm_mul_le_of_le
-/
lemma norm_mul₃_le : ‖a * b * c‖ <= ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl

/--
lemma `nnnorm_mul₃_le` / 引理 `nnnorm_mul₃_le`

English:
lemma nnnorm_mul₃_le
  statement: ‖a * b * c‖₊ <= ‖a‖₊ * ‖b‖₊ * ‖c‖₊
  proof: nnnorm_mul_le_of_le (norm_mul_le ..) le_rfl

中文:
引理 nnnorm_mul₃_le
  结论: ‖a * b * c‖₊ <= ‖a‖₊ * ‖b‖₊ * ‖c‖₊
  证明: nnnorm_mul_le_of_le (norm_mul_le ..) le_rfl

Depends on / 依赖: le_rfl, nnnorm_mul_le_of_le, norm_mul_le
-/
lemma nnnorm_mul₃_le : ‖a * b * c‖₊ <= ‖a‖₊ * ‖b‖₊ * ‖c‖₊ :=
  nnnorm_mul_le_of_le (norm_mul_le ..) le_rfl

/--
theorem `one_le_norm_one` / 定理 `one_le_norm_one`

English:
theorem one_le_norm_one
  given: (β) [NormedRing β] [Nontrivial β]
  statement: 1 <= ‖(1 : β)‖
  proof: (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) != 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

中文:
定理 one_le_norm_one
  条件: (β) [赋范环 β] [非平凡 β]
  结论: 1 <= ‖(1 : β)‖
  证明: (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) != 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

Depends on / 依赖: le_mul_iff_one_le_left, mul_one, norm_mul_le, norm_pos_iff, norm_pos_iff.mpr, one_ne_zero
-/
theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 <= ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) != 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

/--
theorem `one_le_nnnorm_one` / 定理 `one_le_nnnorm_one`

English:
theorem one_le_nnnorm_one
  given: (β) [NormedRing β] [Nontrivial β]
  statement: 1 <= ‖(1 : β)‖₊
  proof: one_le_norm_one β

中文:
定理 one_le_nnnorm_one
  条件: (β) [赋范环 β] [非平凡 β]
  结论: 1 <= ‖(1 : β)‖₊
  证明: one_le_norm_one β

Depends on / 依赖: one_le_norm_one
-/
theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 <= ‖(1 : β)‖₊ :=
  one_le_norm_one β

/--
theorem `mulLeft_bound` / 定理 `mulLeft_bound`

English:
theorem mulLeft_bound
  given: (x : α)
  statement: forall y : α, ‖AddMonoidHom.mulLeft x y‖ <= ‖x‖ * ‖y‖
  proof: norm_mul_le x

中文:
定理 mulLeft_bound
  条件: (x : α)
  结论: 对任意 y : α, ‖加法幺半群态射.mulLeft x y‖ <= ‖x‖ * ‖y‖
  证明: norm_mul_le x

Depends on / 依赖: norm_mul_le
-/
theorem mulLeft_bound (x : α) : forall y : α, ‖AddMonoidHom.mulLeft x y‖ <= ‖x‖ * ‖y‖ :=
  norm_mul_le x

/--
theorem `mulRight_bound` / 定理 `mulRight_bound`

English:
theorem mulRight_bound
  given: (x : α)
  statement: forall y : α, ‖AddMonoidHom.mulRight x y‖ <= ‖x‖ * ‖y‖
  proof: fun y => by
  rw [mul_comm]
  exact norm_mul_le y x

中文:
定理 mulRight_bound
  条件: (x : α)
  结论: 对任意 y : α, ‖加法幺半群态射.mulRight x y‖ <= ‖x‖ * ‖y‖
  证明: fun y => by
  rw [mul_comm]
  exact norm_mul_le y x

Depends on / 依赖: mul_comm, norm_mul_le
-/
theorem mulRight_bound (x : α) : forall y : α, ‖AddMonoidHom.mulRight x y‖ <= ‖x‖ * ‖y‖ := fun y => by
  rw [mul_comm]
  exact norm_mul_le y x

/--
Instance `NonUnitalSubalgebra.nonUnitalSeminormedRing` / 实例 `NonUnitalSubalgebra.nonUnitalSeminormedRing`

English:
instance NonUnitalSubalgebra.nonUnitalSeminormedRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
  body: { s.toSubmodule.seminormedAddCommGroup, s.toNonUnitalRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

中文:
实例 NonUnital子代数.nonUnitalSeminormedRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型}
  定义体: { s.toSubmodule.seminormedAddCommGroup, s.toNonUnitalRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

Depends on / 依赖: norm_mul_le, s.toNonUnitalRing, s.toSubmodule.seminormedAddCommGroup, seminormedAddCommGroup, toNonUnitalRing, toSubmodule
-/
instance NonUnitalSubalgebra.nonUnitalSeminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toNonUnitalRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalSeminormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalSeminormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalSeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, NonUnitalSubringClass.toNonUnitalRing s with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/--
Instance `NonUnitalSubalgebra.nonUnitalNormedRing` / 实例 `NonUnitalSubalgebra.nonUnitalNormedRing`

English:
instance NonUnitalSubalgebra.nonUnitalNormedRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
  body: { s.nonUnitalSeminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 NonUnital子代数.nonUnitalNormedRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型}
  定义体: { s.nonUnitalSeminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: eq_of_dist_eq_zero, nonUnitalSeminormedRing, s.nonUnitalSeminormedRing
-/
instance NonUnitalSubalgebra.nonUnitalNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : NonUnitalNormedRing s :=
  { s.nonUnitalSeminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring,
with the restriction of the norm. -/
instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalNormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalNormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalNormedRing s :=
  { nonUnitalSeminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/--
Instance `ULift.nonUnitalSeminormedRing` / 实例 `ULift.nonUnitalSeminormedRing`

English:
instance ULift.nonUnitalSeminormedRing
  signature: : NonUnitalSeminormedRing (ULift α)
  body: { ULift.seminormedAddCommGroup, ULift.nonUnitalRing with
    norm_mul_le x y := norm_mul_le x.down y.down }

中文:
实例 类型层提升.nonUnitalSeminormedRing
  签名: : 非幺Seminormed环 (类型层提升 α)
  定义体: { ULift.seminormedAddCommGroup, ULift.nonUnitalRing with
    norm_mul_le x y := norm_mul_le x.down y.down }

Depends on / 依赖: ULift.nonUnitalRing, ULift.seminormedAddCommGroup, nonUnitalRing, norm_mul_le, seminormedAddCommGroup, x.down, y.down
-/
instance ULift.nonUnitalSeminormedRing : NonUnitalSeminormedRing (ULift α) :=
  { ULift.seminormedAddCommGroup, ULift.nonUnitalRing with
    norm_mul_le x y := norm_mul_le x.down y.down }

/--
Instance `Prod.nonUnitalSeminormedRing` / 实例 `Prod.nonUnitalSeminormedRing`

English:
instance Prod.nonUnitalSeminormedRing
  signature: [NonUnitalSeminormedRing β]
  body: { seminormedAddCommGroup, instNonUnitalRing with
    norm_mul_le x y := calc
      ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
      _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
      _ <= max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
        (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
      _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
      _ <= max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
        apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
      _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
      _ = ‖x‖ * ‖y‖ := rfl }

中文:
实例 积类型.nonUnitalSeminormedRing
  签名: [非幺Seminormed环 β]
  定义体: { seminormedAddCommGroup, instNonUnitalRing with
    norm_mul_le x y := calc
      ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
      _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
      _ <= max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
        (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
      _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
      _ <= max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
        apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
      _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
      _ = ‖x‖ * ‖y‖ := rfl }

Depends on / 依赖: instNonUnitalRing, max_comm, max_le_max, max_mul_mul_le_max_mul_max, mul_comm, norm_mul_le, norm_nonneg, seminormedAddCommGroup
-/
instance Prod.nonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing (α × β) :=
  { seminormedAddCommGroup, instNonUnitalRing with
    norm_mul_le x y := calc
      ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
      _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
      _ <= max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
        (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
      _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
      _ <= max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
        apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
      _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
      _ = ‖x‖ * ‖y‖ := rfl }

/--
Instance `MulOpposite.instNonUnitalSeminormedRing` / 实例 `MulOpposite.instNonUnitalSeminormedRing`

English:
instance MulOpposite.instNonUnitalSeminormedRing
  signature: : NonUnitalSeminormedRing αᵐᵒᵖ where
  body: instNonUnitalRing
  __ := instSeminormedAddCommGroup
  norm_mul_le := MulOpposite.rec' fun x => MulOpposite.rec' fun y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

中文:
实例 MulOpposite.instNonUnitalSeminormedRing
  签名: : 非幺Seminormed环 αᵐᵒᵖ where
  定义体: instNonUnitalRing
  __ := instSeminormedAddCommGroup
  norm_mul_le := MulOpposite.rec' fun x => MulOpposite.rec' fun y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

Depends on / 依赖: instNonUnitalRing
-/
instance MulOpposite.instNonUnitalSeminormedRing : NonUnitalSeminormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instSeminormedAddCommGroup
  norm_mul_le := MulOpposite.rec' fun x => MulOpposite.rec' fun y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α] {a b c : α}

/--
Instance `Subalgebra.seminormedRing` / 实例 `Subalgebra.seminormedRing`

English:
instance Subalgebra.seminormedRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedRing E]
  body: { s.toSubmodule.seminormedAddCommGroup, s.toRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

中文:
实例 子代数.seminormedRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型} [Seminormed环 E]
  定义体: { s.toSubmodule.seminormedAddCommGroup, s.toRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

Depends on / 依赖: norm_mul_le, s.toRing, s.toSubmodule.seminormedAddCommGroup, seminormedAddCommGroup, toRing, toSubmodule
-/
instance Subalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
instance (priority := 75) SubalgebraClass.seminormedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [SeminormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : SeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, SubringClass.toRing s with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/--
Instance `Subalgebra.normedRing` / 实例 `Subalgebra.normedRing`

English:
instance Subalgebra.normedRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedRing E]
  body: { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 子代数.normedRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型} [赋范环 E]
  定义体: { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: eq_of_dist_eq_zero, s.seminormedRing, seminormedRing
-/
instance Subalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the
norm. -/
instance (priority := 75) SubalgebraClass.normedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [NormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : NormedRing s :=
  { seminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }


/--
theorem `Nat.norm_cast_le` / 定理 `Nat.norm_cast_le`

English:
theorem Nat.norm_cast_le
  statement: forall n : Nat, ‖(n : α)‖ <= n * ‖(1 : α)‖

中文:
定理 自然数.norm_cast_le
  结论: 对任意 n : 自然数, ‖(n : α)‖ <= n * ‖(1 : α)‖
-/
theorem Nat.norm_cast_le : forall n : Nat, ‖(n : α)‖ <= n * ‖(1 : α)‖
  | 0 => by simp
  | n + 1 => by
    rw [n.cast_succ]; rw [n.cast_succ]; rw [add_mul]; rw [one_mul]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl

/--
theorem `List.norm_prod_le'` / 定理 `List.norm_prod_le'`

English:
theorem List.norm_prod_le'
  statement: forall {l : List α}, l != [] -> ‖l.prod‖ <= (l.map norm).prod

中文:
定理 列表.norm_prod_le'
  结论: 对任意 {l : 列表 α}, l != [] -> ‖l.乘积‖ <= (l.map norm).乘积
-/
theorem List.norm_prod_le' : forall {l : List α}, l != [] -> ‖l.prod‖ <= (l.map norm).prod
  | [], h => (h rfl).elim
  | [a], _ => by simp
  | a::b::l, _ => by
    rw [List.map_cons]; rw [List.prod_cons]; rw [List.prod_cons (a := ‖a‖)]
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)

/--
theorem `List.nnnorm_prod_le'` / 定理 `List.nnnorm_prod_le'`

English:
theorem List.nnnorm_prod_le'
  given: {l : List α} (hl : l != [])
  statement: ‖l.prod‖₊ <= (l.map nnnorm).prod
  proof: (List.norm_prod_le' hl).trans_eq by simp [NNReal.coe_list_prod, List.map_map]

中文:
定理 列表.nnnorm_prod_le'
  条件: {l : 列表 α} (hl : l != [])
  结论: ‖l.乘积‖₊ <= (l.map nnnorm).乘积
  证明: (List.norm_prod_le' hl).trans_eq by simp [NNReal.coe_list_prod, List.map_map]

Depends on / 依赖: List.map_map, List.norm_prod_le, NNReal, NNReal.coe_list_prod, coe_list_prod, map_map, norm_prod_le, trans_eq
-/
theorem List.nnnorm_prod_le' {l : List α} (hl : l != []) : ‖l.prod‖₊ <= (l.map nnnorm).prod :=
(List.norm_prod_le' hl).trans_eq by simp [NNReal.coe_list_prod, List.map_map]

/--
theorem `List.norm_prod_le` / 定理 `List.norm_prod_le`

English:
theorem List.norm_prod_le
  given: [NormOneClass α]
  statement: forall l : List α, ‖l.prod‖ <= (l.map norm).prod

中文:
定理 列表.norm_prod_le
  条件: [NormOne类 α]
  结论: 对任意 l : 列表 α, ‖l.乘积‖ <= (l.map norm).乘积
-/
theorem List.norm_prod_le [NormOneClass α] : forall l : List α, ‖l.prod‖ <= (l.map norm).prod
  | [] => by simp
  | a::l => List.norm_prod_le' (List.cons_ne_nil a l)

/--
theorem `List.nnnorm_prod_le` / 定理 `List.nnnorm_prod_le`

English:
theorem List.nnnorm_prod_le
  given: [NormOneClass α] (l : List α)
  statement: ‖l.prod‖₊ <= (l.map nnnorm).prod
  proof: l.norm_prod_le.trans_eq by simp [NNReal.coe_list_prod, List.map_map]

中文:
定理 列表.nnnorm_prod_le
  条件: [NormOne类 α] (l : 列表 α)
  结论: ‖l.乘积‖₊ <= (l.map nnnorm).乘积
  证明: l.norm_prod_le.trans_eq by simp [NNReal.coe_list_prod, List.map_map]

Depends on / 依赖: List.map_map, NNReal, NNReal.coe_list_prod, coe_list_prod, l.norm_prod_le.trans_eq, map_map, norm_prod_le, trans_eq
-/
theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.prod‖₊ <= (l.map nnnorm).prod :=
l.norm_prod_le.trans_eq by simp [NNReal.coe_list_prod, List.map_map]

/--
theorem `Finset.norm_prod_le'` / 定理 `Finset.norm_prod_le'`

English:
theorem Finset.norm_prod_le'
  statement: {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
  proof: by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f != [] := by simpa using! hs
  simpa using! List.norm_prod_le' this

中文:
定理 有限集.norm_prod_le'
  结论: {α : 类型} [NormedComm环 α] (s : 有限集 ι) (hs : s.非空)
  证明: by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f != [] := by simpa using! hs
  simpa using! List.norm_prod_le' this

Depends on / 依赖: List.norm_prod_le, l.map, norm_prod_le
-/
theorem Finset.norm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f != [] := by simpa using! hs
  simpa using! List.norm_prod_le' this

/--
theorem `Finset.nnnorm_prod_le'` / 定理 `Finset.nnnorm_prod_le'`

English:
theorem Finset.nnnorm_prod_le'
  statement: {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
  proof: (s.norm_prod_le' hs f).trans_eq by simp [NNReal.coe_prod]

中文:
定理 有限集.nnnorm_prod_le'
  结论: {α : 类型} [NormedComm环 α] (s : 有限集 ι) (hs : s.非空)
  证明: (s.norm_prod_le' hs f).trans_eq by simp [NNReal.coe_prod]

Depends on / 依赖: NNReal, NNReal.coe_prod, coe_prod, norm_prod_le, s.norm_prod_le, trans_eq
-/
theorem Finset.nnnorm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι -> α) : ‖∏ i in s, f i‖₊ <= ∏ i in s, ‖f i‖₊ :=
(s.norm_prod_le' hs f).trans_eq by simp [NNReal.coe_prod]

/--
theorem `Finset.norm_prod_le` / 定理 `Finset.norm_prod_le`

English:
theorem Finset.norm_prod_le
  statement: {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
  proof: by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using! (l.map f).norm_prod_le

中文:
定理 有限集.norm_prod_le
  结论: {α : 类型} [NormedComm环 α] [NormOne类 α] (s : 有限集 ι)
  证明: by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using! (l.map f).norm_prod_le

Depends on / 依赖: l.map, norm_prod_le
-/
theorem Finset.norm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using! (l.map f).norm_prod_le

/--
theorem `Finset.nnnorm_prod_le` / 定理 `Finset.nnnorm_prod_le`

English:
theorem Finset.nnnorm_prod_le
  statement: {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
  proof: (s.norm_prod_le f).trans_eq by simp [NNReal.coe_prod]

中文:
定理 有限集.nnnorm_prod_le
  结论: {α : 类型} [NormedComm环 α] [NormOne类 α] (s : 有限集 ι)
  证明: (s.norm_prod_le f).trans_eq by simp [NNReal.coe_prod]

Depends on / 依赖: NNReal, NNReal.coe_prod, coe_prod, norm_prod_le, s.norm_prod_le, trans_eq
-/
theorem Finset.nnnorm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι -> α) : ‖∏ i in s, f i‖₊ <= ∏ i in s, ‖f i‖₊ :=
(s.norm_prod_le f).trans_eq by simp [NNReal.coe_prod]

/--
lemma `norm_natAbs` / 引理 `norm_natAbs`

English:
lemma norm_natAbs
  given: (z : Int)
  proof: by
  rcases z.natAbs_eq with hz | hz
  · rw [← Int.cast_natCast, ← hz]
  · rw [← Int.cast_natCast, ← norm_neg, ← Int.cast_neg, ← hz]

中文:
引理 norm_natAbs
  条件: (z : 整数)
  证明: by
  rcases z.natAbs_eq with hz | hz
  · rw [← Int.cast_natCast, ← hz]
  · rw [← Int.cast_natCast, ← norm_neg, ← Int.cast_neg, ← hz]

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, cast_natCast, cast_neg, natAbs_eq, norm_neg, z.natAbs_eq
-/
lemma norm_natAbs (z : Int) :
    ‖(z.natAbs : α)‖ = ‖(z : α)‖ := by
  rcases z.natAbs_eq with hz | hz
  · rw [← Int.cast_natCast, ← hz]
  · rw [← Int.cast_natCast, ← norm_neg, ← Int.cast_neg, ← hz]

/--
lemma `nnnorm_natAbs` / 引理 `nnnorm_natAbs`

English:
lemma nnnorm_natAbs
  given: (z : Int)
  proof: by
  simp [← NNReal.coe_inj, -Nat.cast_natAbs, norm_natAbs]

中文:
引理 nnnorm_natAbs
  条件: (z : 整数)
  证明: by
  simp [← NNReal.coe_inj, -Nat.cast_natAbs, norm_natAbs]

Depends on / 依赖: NNReal, NNReal.coe_inj, Nat.cast_natAbs, cast_natAbs, coe_inj, norm_natAbs
-/
lemma nnnorm_natAbs (z : Int) :
    ‖(z.natAbs : α)‖₊ = ‖(z : α)‖₊ := by
  simp [← NNReal.coe_inj, -Nat.cast_natAbs, norm_natAbs]

/--
lemma `norm_intCast_abs` / 引理 `norm_intCast_abs`

English:
lemma norm_intCast_abs
  given: (z : Int)
  proof: by
  simp [← norm_natAbs]

中文:
引理 norm_intCast_abs
  条件: (z : 整数)
  证明: by
  simp [← norm_natAbs]
-/
@[simp] lemma norm_intCast_abs (z : Int) :
    ‖((|z| : Int) : α)‖ = ‖(z : α)‖ := by
  simp [← norm_natAbs]

/--
lemma `nnnorm_intCast_abs` / 引理 `nnnorm_intCast_abs`

English:
lemma nnnorm_intCast_abs
  given: (z : Int)
  proof: by
  simp [← nnnorm_natAbs]

中文:
引理 nnnorm_intCast_abs
  条件: (z : 整数)
  证明: by
  simp [← nnnorm_natAbs]
-/
@[simp] lemma nnnorm_intCast_abs (z : Int) :
    ‖((|z| : Int) : α)‖₊ = ‖(z : α)‖₊ := by
  simp [← nnnorm_natAbs]

/--
theorem `nnnorm_pow_le'` / 定理 `nnnorm_pow_le'`

English:
theorem nnnorm_pow_le'
  given: (a : α)
  statement: forall {n : Nat}, 0 < n -> ‖a ^ n‖₊ <= ‖a‖₊ ^ n

中文:
定理 nnnorm_pow_le'
  条件: (a : α)
  结论: 对任意 {n : 自然数}, 0 < n -> ‖a ^ n‖₊ <= ‖a‖₊ ^ n
-/
theorem nnnorm_pow_le' (a : α) : forall {n : Nat}, 0 < n -> ‖a ^ n‖₊ <= ‖a‖₊ ^ n
  | 1, _ => by simp only [pow_one, le_rfl]
  | n + 2, _ => by
    simpa only [pow_succ' _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_right (nnnorm_pow_le' a n.succ_pos) _)

/--
theorem `nnnorm_pow_le` / 定理 `nnnorm_pow_le`

English:
theorem nnnorm_pow_le
  given: [NormOneClass α] (a : α) (n : Nat)
  statement: ‖a ^ n‖₊ <= ‖a‖₊ ^ n
  proof: Nat.recOn n (by simp)
    fun k _hk => nnnorm_pow_le' a k.succ_pos

中文:
定理 nnnorm_pow_le
  条件: [NormOne类 α] (a : α) (n : 自然数)
  结论: ‖a ^ n‖₊ <= ‖a‖₊ ^ n
  证明: Nat.recOn n (by simp)
    fun k _hk => nnnorm_pow_le' a k.succ_pos

Depends on / 依赖: Nat.recOn, k.succ_pos, nnnorm_pow_le, succ_pos
-/
theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : Nat) : ‖a ^ n‖₊ <= ‖a‖₊ ^ n :=
  Nat.recOn n (by simp)
    fun k _hk => nnnorm_pow_le' a k.succ_pos

/--
theorem `norm_pow_le'` / 定理 `norm_pow_le'`

English:
theorem norm_pow_le'
  given: (a : α) {n : Nat} (h : 0 < n)
  statement: ‖a ^ n‖ <= ‖a‖ ^ n
  proof: by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)

中文:
定理 norm_pow_le'
  条件: (a : α) {n : 自然数} (h : 0 < n)
  结论: ‖a ^ n‖ <= ‖a‖ ^ n
  证明: by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)

Depends on / 依赖: NNReal, NNReal.coe_mono, NNReal.coe_pow, coe_mono, coe_nnnorm, coe_pow, nnnorm_pow_le
-/
theorem norm_pow_le' (a : α) {n : Nat} (h : 0 < n) : ‖a ^ n‖ <= ‖a‖ ^ n := by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)

/--
theorem `norm_pow_le` / 定理 `norm_pow_le`

English:
theorem norm_pow_le
  given: [NormOneClass α] (a : α) (n : Nat)
  statement: ‖a ^ n‖ <= ‖a‖ ^ n
  proof: Nat.recOn n (by simp)
    fun n _hn => norm_pow_le' a n.succ_pos

中文:
定理 norm_pow_le
  条件: [NormOne类 α] (a : α) (n : 自然数)
  结论: ‖a ^ n‖ <= ‖a‖ ^ n
  证明: Nat.recOn n (by simp)
    fun n _hn => norm_pow_le' a n.succ_pos

Depends on / 依赖: Nat.recOn, n.succ_pos, norm_pow_le, succ_pos
-/
theorem norm_pow_le [NormOneClass α] (a : α) (n : Nat) : ‖a ^ n‖ <= ‖a‖ ^ n :=
  Nat.recOn n (by simp)
    fun n _hn => norm_pow_le' a n.succ_pos

/--
theorem `eventually_norm_pow_le` / 定理 `eventually_norm_pow_le`

English:
theorem eventually_norm_pow_le
  given: (a : α)
  statement: forallᶠ n : Nat in atTop, ‖a ^ n‖ <= ‖a‖ ^ n
  proof: eventually_atTop.mpr ⟨1, fun _b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

中文:
定理 eventually_norm_pow_le
  条件: (a : α)
  结论: 对任意ᶠ n : 自然数 in atTop, ‖a ^ n‖ <= ‖a‖ ^ n
  证明: eventually_atTop.mpr ⟨1, fun _b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

Depends on / 依赖: Nat.succ_le_iff.mp, eventually_atTop, eventually_atTop.mpr, norm_pow_le, succ_le_iff
-/
theorem eventually_norm_pow_le (a : α) : forallᶠ n : Nat in atTop, ‖a ^ n‖ <= ‖a‖ ^ n :=
  eventually_atTop.mpr ⟨1, fun _b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

/--
Instance `ULift.seminormedRing` / 实例 `ULift.seminormedRing`

English:
instance ULift.seminormedRing
  signature: : SeminormedRing (ULift α)
  body: { ULift.nonUnitalSeminormedRing, ULift.ring with }

中文:
实例 类型层提升.seminormedRing
  签名: : Seminormed环 (类型层提升 α)
  定义体: { ULift.nonUnitalSeminormedRing, ULift.ring with }

Depends on / 依赖: ULift.nonUnitalSeminormedRing, ULift.ring, nonUnitalSeminormedRing
-/
instance ULift.seminormedRing : SeminormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.ring with }

/--
Instance `Prod.seminormedRing` / 实例 `Prod.seminormedRing`

English:
instance Prod.seminormedRing
  signature: [SeminormedRing β]
  body: { nonUnitalSeminormedRing, instRing with }

中文:
实例 积类型.seminormedRing
  签名: [Seminormed环 β]
  定义体: { nonUnitalSeminormedRing, instRing with }

Depends on / 依赖: instRing, nonUnitalSeminormedRing
-/
instance Prod.seminormedRing [SeminormedRing β] : SeminormedRing (α × β) :=
  { nonUnitalSeminormedRing, instRing with }

/--
Instance `MulOpposite.instSeminormedRing` / 实例 `MulOpposite.instSeminormedRing`

English:
instance MulOpposite.instSeminormedRing
  signature: : SeminormedRing αᵐᵒᵖ where
  body: instRing
  __ := instNonUnitalSeminormedRing

中文:
实例 MulOpposite.instSeminormedRing
  签名: : Seminormed环 αᵐᵒᵖ where
  定义体: instRing
  __ := instNonUnitalSeminormedRing

Depends on / 依赖: instRing
-/
instance MulOpposite.instSeminormedRing : SeminormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instNonUnitalSeminormedRing

/--
lemma `norm_sub_mul_le` / 引理 `norm_sub_mul_le`

English:
lemma norm_sub_mul_le
  given: (ha : ‖a‖ <= 1)
  statement: ‖c - a * b‖ <= ‖c - a‖ + ‖1 - b‖
  proof: calc
    _ <= ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ <= ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ <= ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

中文:
引理 norm_sub_mul_le
  条件: (ha : ‖a‖ <= 1)
  结论: ‖c - a * b‖ <= ‖c - a‖ + ‖1 - b‖
  证明: calc
    _ <= ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ <= ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ <= ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

Depends on / 依赖: mul_one_sub, norm_mul_le, norm_sub_le_norm_sub_add_norm_sub
-/
lemma norm_sub_mul_le (ha : ‖a‖ <= 1) : ‖c - a * b‖ <= ‖c - a‖ + ‖1 - b‖ :=
  calc
    _ <= ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ <= ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ <= ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

/--
lemma `norm_sub_mul_le'` / 引理 `norm_sub_mul_le'`

English:
lemma norm_sub_mul_le'
  given: (hb : ‖b‖ <= 1)
  statement: ‖c - a * b‖ <= ‖1 - a‖ + ‖c - b‖
  proof: by
  rw [add_comm]; exact norm_sub_mul_le (α := αᵐᵒᵖ) hb

中文:
引理 norm_sub_mul_le'
  条件: (hb : ‖b‖ <= 1)
  结论: ‖c - a * b‖ <= ‖1 - a‖ + ‖c - b‖
  证明: by
  rw [add_comm]; exact norm_sub_mul_le (α := αᵐᵒᵖ) hb

Depends on / 依赖: add_comm, norm_sub_mul_le
-/
lemma norm_sub_mul_le' (hb : ‖b‖ <= 1) : ‖c - a * b‖ <= ‖1 - a‖ + ‖c - b‖ := by
  rw [add_comm]; exact norm_sub_mul_le (α := αᵐᵒᵖ) hb

/--
lemma `nnnorm_sub_mul_le` / 引理 `nnnorm_sub_mul_le`

English:
lemma nnnorm_sub_mul_le
  given: (ha : ‖a‖₊ <= 1)
  statement: ‖c - a * b‖₊ <= ‖c - a‖₊ + ‖1 - b‖₊
  proof: norm_sub_mul_le ha

中文:
引理 nnnorm_sub_mul_le
  条件: (ha : ‖a‖₊ <= 1)
  结论: ‖c - a * b‖₊ <= ‖c - a‖₊ + ‖1 - b‖₊
  证明: norm_sub_mul_le ha

Depends on / 依赖: norm_sub_mul_le
-/
lemma nnnorm_sub_mul_le (ha : ‖a‖₊ <= 1) : ‖c - a * b‖₊ <= ‖c - a‖₊ + ‖1 - b‖₊ := norm_sub_mul_le ha

/--
lemma `nnnorm_sub_mul_le'` / 引理 `nnnorm_sub_mul_le'`

English:
lemma nnnorm_sub_mul_le'
  given: (hb : ‖b‖₊ <= 1)
  statement: ‖c - a * b‖₊ <= ‖1 - a‖₊ + ‖c - b‖₊
  proof: norm_sub_mul_le' hb

中文:
引理 nnnorm_sub_mul_le'
  条件: (hb : ‖b‖₊ <= 1)
  结论: ‖c - a * b‖₊ <= ‖1 - a‖₊ + ‖c - b‖₊
  证明: norm_sub_mul_le' hb

Depends on / 依赖: norm_sub_mul_le
-/
lemma nnnorm_sub_mul_le' (hb : ‖b‖₊ <= 1) : ‖c - a * b‖₊ <= ‖1 - a‖₊ + ‖c - b‖₊ := norm_sub_mul_le' hb

/--
lemma `norm_commutator_units_sub_one_le` / 引理 `norm_commutator_units_sub_one_le`

English:
lemma norm_commutator_units_sub_one_le
  given: (a b : αˣ)
  proof: calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a) * a⁻¹.val * b⁻¹.val‖ := by simp [sub_mul, *]
    _ <= ‖(a * b - b * a : α)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le
    _ = ‖(a - 1 : α) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ <= (‖(a - 1 : α) * (b - 1)‖ + ‖(b - 1 : α) * (a - 1)‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr; exact norm_sub_le ..
    _ <= (‖a.val - 1‖ * ‖b.val - 1‖ + ‖b.val - 1‖ * ‖a.val - 1‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr <;> exact norm_mul_le ..
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring

中文:
引理 norm_commutator_units_sub_one_le
  条件: (a b : αˣ)
  证明: calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a) * a⁻¹.val * b⁻¹.val‖ := by simp [sub_mul, *]
    _ <= ‖(a * b - b * a : α)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le
    _ = ‖(a - 1 : α) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ <= (‖(a - 1 : α) * (b - 1)‖ + ‖(b - 1 : α) * (a - 1)‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr; exact norm_sub_le ..
    _ <= (‖a.val - 1‖ * ‖b.val - 1‖ + ‖b.val - 1‖ * ‖a.val - 1‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr <;> exact norm_mul_le ..
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring

Depends on / 依赖: a.val, abel_nf, b.val, mul_sub_one, norm_sub_le, simp_rw, sub_mul, sub_one_mul
-/
lemma norm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ <= 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ :=
  calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a) * a⁻¹.val * b⁻¹.val‖ := by simp [sub_mul, *]
    _ <= ‖(a * b - b * a : α)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le
    _ = ‖(a - 1 : α) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ <= (‖(a - 1 : α) * (b - 1)‖ + ‖(b - 1 : α) * (a - 1)‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr; exact norm_sub_le ..
    _ <= (‖a.val - 1‖ * ‖b.val - 1‖ + ‖b.val - 1‖ * ‖a.val - 1‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr <;> exact norm_mul_le ..
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring

/--
lemma `nnnorm_commutator_units_sub_one_le` / 引理 `nnnorm_commutator_units_sub_one_le`

English:
lemma nnnorm_commutator_units_sub_one_le
  given: (a b : αˣ)
  proof: by
  simpa using! norm_commutator_units_sub_one_le a b

中文:
引理 nnnorm_commutator_units_sub_one_le
  条件: (a b : αˣ)
  证明: by
  simpa using! norm_commutator_units_sub_one_le a b

Depends on / 依赖: norm_commutator_units_sub_one_le
-/
lemma nnnorm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖₊ <= 2 * ‖a⁻¹.val‖₊ * ‖b⁻¹.val‖₊ * ‖a.val - 1‖₊ * ‖b.val - 1‖₊ := by
  simpa using! norm_commutator_units_sub_one_le a b

/--
Definition of `RingHom.IsBounded` / `RingHom.IsBounded` 的定义

English:
definition RingHom.IsBounded
  signature: {α : Type*} [SeminormedRing α] {β : Type*} [SeminormedRing β]
  body: exists C : Real, 0 < C ∧ forall x : α, norm (f x) <= C * norm x

中文:
定义 环态射.IsBounded
  签名: {α : 类型} [Seminormed环 α] {β : 类型} [Seminormed环 β]
  定义体: exists C : Real, 0 < C ∧ forall x : α, norm (f x) <= C * norm x
-/
def RingHom.IsBounded {α : Type*} [SeminormedRing α] {β : Type*} [SeminormedRing β]
    (f : α ->+* β) : Prop :=
  exists C : Real, 0 < C ∧ forall x : α, norm (f x) <= C * norm x

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

/--
Instance `ULift.nonUnitalNormedRing` / 实例 `ULift.nonUnitalNormedRing`

English:
instance ULift.nonUnitalNormedRing
  signature: : NonUnitalNormedRing (ULift α)
  body: { ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup with }

中文:
实例 类型层提升.nonUnitalNormedRing
  签名: : 非幺赋范环 (类型层提升 α)
  定义体: { ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup with }

Depends on / 依赖: ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup, nonUnitalSeminormedRing, normedAddCommGroup
-/
instance ULift.nonUnitalNormedRing : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup with }

/--
Instance `Prod.nonUnitalNormedRing` / 实例 `Prod.nonUnitalNormedRing`

English:
instance Prod.nonUnitalNormedRing
  signature: [NonUnitalNormedRing β]
  body: { Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup with }

中文:
实例 积类型.nonUnitalNormedRing
  签名: [非幺赋范环 β]
  定义体: { Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup with }

Depends on / 依赖: Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup, nonUnitalSeminormedRing, normedAddCommGroup
-/
instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup with }

/--
Instance `MulOpposite.instNonUnitalNormedRing` / 实例 `MulOpposite.instNonUnitalNormedRing`

English:
instance MulOpposite.instNonUnitalNormedRing
  signature: : NonUnitalNormedRing αᵐᵒᵖ where
  body: instNonUnitalRing
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

中文:
实例 MulOpposite.instNonUnitalNormedRing
  签名: : 非幺赋范环 αᵐᵒᵖ where
  定义体: instNonUnitalRing
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

Depends on / 依赖: instNonUnitalRing
-/
instance MulOpposite.instNonUnitalNormedRing : NonUnitalNormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

/--
theorem `Units.norm_pos` / 定理 `Units.norm_pos`

English:
theorem Units.norm_pos
  given: [Nontrivial α] (x : αˣ)
  statement: 0 < ‖(x : α)‖
  proof: norm_pos_iff.mpr (Units.ne_zero x)

中文:
定理 单位群.norm_pos
  条件: [非平凡 α] (x : αˣ)
  结论: 0 < ‖(x : α)‖
  证明: norm_pos_iff.mpr (Units.ne_zero x)

Depends on / 依赖: Units.ne_zero, ne_zero, norm_pos_iff, norm_pos_iff.mpr
-/
theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)

/--
theorem `Units.nnnorm_pos` / 定理 `Units.nnnorm_pos`

English:
theorem Units.nnnorm_pos
  given: [Nontrivial α] (x : αˣ)
  statement: 0 < ‖(x : α)‖₊
  proof: x.norm_pos

中文:
定理 单位群.nnnorm_pos
  条件: [非平凡 α] (x : αˣ)
  结论: 0 < ‖(x : α)‖₊
  证明: x.norm_pos

Depends on / 依赖: norm_pos, x.norm_pos
-/
theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos

/--
Instance `ULift.normedRing` / 实例 `ULift.normedRing`

English:
instance ULift.normedRing
  signature: : NormedRing (ULift α)
  body: { ULift.seminormedRing, ULift.normedAddCommGroup with }

中文:
实例 类型层提升.normedRing
  签名: : 赋范环 (类型层提升 α)
  定义体: { ULift.seminormedRing, ULift.normedAddCommGroup with }

Depends on / 依赖: ULift.normedAddCommGroup, ULift.seminormedRing, normedAddCommGroup, seminormedRing
-/
instance ULift.normedRing : NormedRing (ULift α) :=
  { ULift.seminormedRing, ULift.normedAddCommGroup with }

/--
Instance `Prod.normedRing` / 实例 `Prod.normedRing`

English:
instance Prod.normedRing
  signature: [NormedRing β]
  body: { nonUnitalNormedRing, instRing with }

中文:
实例 积类型.normedRing
  签名: [赋范环 β]
  定义体: { nonUnitalNormedRing, instRing with }

Depends on / 依赖: instRing, nonUnitalNormedRing
-/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { nonUnitalNormedRing, instRing with }

/--
Instance `MulOpposite.instNormedRing` / 实例 `MulOpposite.instNormedRing`

English:
instance MulOpposite.instNormedRing
  signature: : NormedRing αᵐᵒᵖ where
  body: instRing
  __ := instSeminormedRing
  __ := instNormedAddCommGroup

中文:
实例 MulOpposite.instNormedRing
  签名: : 赋范环 αᵐᵒᵖ where
  定义体: instRing
  __ := instSeminormedRing
  __ := instNormedAddCommGroup

Depends on / 依赖: instRing
-/
instance MulOpposite.instNormedRing : NormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instSeminormedRing
  __ := instNormedAddCommGroup

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

/--
Instance `ULift.nonUnitalSeminormedCommRing` / 实例 `ULift.nonUnitalSeminormedCommRing`

English:
instance ULift.nonUnitalSeminormedCommRing
  signature: : NonUnitalSeminormedCommRing (ULift α)
  body: { ULift.nonUnitalSeminormedRing, ULift.nonUnitalCommRing with }

中文:
实例 类型层提升.nonUnitalSeminormedCommRing
  签名: : 非幺SeminormedComm环 (类型层提升 α)
  定义体: { ULift.nonUnitalSeminormedRing, ULift.nonUnitalCommRing with }

Depends on / 依赖: ULift.nonUnitalCommRing, ULift.nonUnitalSeminormedRing, nonUnitalCommRing, nonUnitalSeminormedRing
-/
instance ULift.nonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.nonUnitalCommRing with }

/--
Instance `Prod.nonUnitalSeminormedCommRing` / 实例 `Prod.nonUnitalSeminormedCommRing`

English:
instance Prod.nonUnitalSeminormedCommRing
  signature: [NonUnitalSeminormedCommRing β]
  body: { nonUnitalSeminormedRing, instNonUnitalCommRing with }

中文:
实例 积类型.nonUnitalSeminormedCommRing
  签名: [非幺SeminormedComm环 β]
  定义体: { nonUnitalSeminormedRing, instNonUnitalCommRing with }

Depends on / 依赖: instNonUnitalCommRing, nonUnitalSeminormedRing
-/
instance Prod.nonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing (α × β) :=
  { nonUnitalSeminormedRing, instNonUnitalCommRing with }

/--
Instance `MulOpposite.instNonUnitalSeminormedCommRing` / 实例 `MulOpposite.instNonUnitalSeminormedCommRing`

English:
instance MulOpposite.instNonUnitalSeminormedCommRing
  signature: : NonUnitalSeminormedCommRing αᵐᵒᵖ where
  body: instNonUnitalSeminormedRing
  __ := instNonUnitalCommRing

中文:
实例 MulOpposite.instNonUnitalSeminormedCommRing
  签名: : 非幺SeminormedComm环 αᵐᵒᵖ where
  定义体: instNonUnitalSeminormedRing
  __ := instNonUnitalCommRing

Depends on / 依赖: instNonUnitalSeminormedRing
-/
instance MulOpposite.instNonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalSeminormedRing
  __ := instNonUnitalCommRing

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/--
Instance `NonUnitalSubalgebra.nonUnitalSeminormedCommRing` / 实例 `NonUnitalSubalgebra.nonUnitalSeminormedCommRing`

English:
instance NonUnitalSubalgebra.nonUnitalSeminormedCommRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
  body: { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

中文:
实例 NonUnital子代数.nonUnitalSeminormedCommRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型}
  定义体: { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

Depends on / 依赖: nonUnitalSeminormedRing, s.nonUnitalSeminormedRing, s.toNonUnitalCommRing, toNonUnitalCommRing
-/
instance NonUnitalSubalgebra.nonUnitalSeminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedCommRing s :=
  { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

/--
Instance `NonUnitalSubalgebra.nonUnitalNormedCommRing` / 实例 `NonUnitalSubalgebra.nonUnitalNormedCommRing`

English:
instance NonUnitalSubalgebra.nonUnitalNormedCommRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
  body: { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }

中文:
实例 NonUnital子代数.nonUnitalNormedCommRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型}
  定义体: { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }

Depends on / 依赖: nonUnitalNormedRing, nonUnitalSeminormedCommRing, s.nonUnitalNormedRing, s.nonUnitalSeminormedCommRing
-/
instance NonUnitalSubalgebra.nonUnitalNormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalNormedCommRing s :=
  { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }

/--
Instance `ULift.nonUnitalNormedCommRing` / 实例 `ULift.nonUnitalNormedCommRing`

English:
instance ULift.nonUnitalNormedCommRing
  signature: : NonUnitalNormedCommRing (ULift α)
  body: { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

中文:
实例 类型层提升.nonUnitalNormedCommRing
  签名: : 非幺NormedComm环 (类型层提升 α)
  定义体: { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

Depends on / 依赖: ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup, nonUnitalSeminormedCommRing, normedAddCommGroup
-/
instance ULift.nonUnitalNormedCommRing : NonUnitalNormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

/--
Instance `Prod.nonUnitalNormedCommRing` / 实例 `Prod.nonUnitalNormedCommRing`

English:
instance Prod.nonUnitalNormedCommRing
  signature: [NonUnitalNormedCommRing β]
  body: { Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup with }

中文:
实例 积类型.nonUnitalNormedCommRing
  签名: [非幺NormedComm环 β]
  定义体: { Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup with }

Depends on / 依赖: Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup, nonUnitalSeminormedCommRing, normedAddCommGroup
-/
instance Prod.nonUnitalNormedCommRing [NonUnitalNormedCommRing β] :
    NonUnitalNormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup with }

/--
Instance `MulOpposite.instNonUnitalNormedCommRing` / 实例 `MulOpposite.instNonUnitalNormedCommRing`

English:
instance MulOpposite.instNonUnitalNormedCommRing
  signature: : NonUnitalNormedCommRing αᵐᵒᵖ where
  body: instNonUnitalNormedRing
  __ := instNonUnitalSeminormedCommRing

中文:
实例 MulOpposite.instNonUnitalNormedCommRing
  签名: : 非幺NormedComm环 αᵐᵒᵖ where
  定义体: instNonUnitalNormedRing
  __ := instNonUnitalSeminormedCommRing

Depends on / 依赖: instNonUnitalNormedRing
-/
instance MulOpposite.instNonUnitalNormedCommRing : NonUnitalNormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalNormedRing
  __ := instNonUnitalSeminormedCommRing

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

/--
Instance `ULift.seminormedCommRing` / 实例 `ULift.seminormedCommRing`

English:
instance ULift.seminormedCommRing
  signature: : SeminormedCommRing (ULift α)
  body: { ULift.nonUnitalSeminormedRing, ULift.commRing with }

中文:
实例 类型层提升.seminormedCommRing
  签名: : SeminormedComm环 (类型层提升 α)
  定义体: { ULift.nonUnitalSeminormedRing, ULift.commRing with }

Depends on / 依赖: ULift.commRing, ULift.nonUnitalSeminormedRing, commRing, nonUnitalSeminormedRing
-/
instance ULift.seminormedCommRing : SeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.commRing with }

/--
Instance `Prod.seminormedCommRing` / 实例 `Prod.seminormedCommRing`

English:
instance Prod.seminormedCommRing
  signature: [SeminormedCommRing β]
  body: { Prod.nonUnitalSeminormedCommRing, instCommRing with }

中文:
实例 积类型.seminormedCommRing
  签名: [SeminormedComm环 β]
  定义体: { Prod.nonUnitalSeminormedCommRing, instCommRing with }

Depends on / 依赖: Prod.nonUnitalSeminormedCommRing, instCommRing, nonUnitalSeminormedCommRing
-/
instance Prod.seminormedCommRing [SeminormedCommRing β] : SeminormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, instCommRing with }

/--
Instance `MulOpposite.instSeminormedCommRing` / 实例 `MulOpposite.instSeminormedCommRing`

English:
instance MulOpposite.instSeminormedCommRing
  signature: : SeminormedCommRing αᵐᵒᵖ where
  body: instSeminormedRing
  __ := instNonUnitalSeminormedCommRing

中文:
实例 MulOpposite.instSeminormedCommRing
  签名: : SeminormedComm环 αᵐᵒᵖ where
  定义体: instSeminormedRing
  __ := instNonUnitalSeminormedCommRing

Depends on / 依赖: instSeminormedRing
-/
instance MulOpposite.instSeminormedCommRing : SeminormedCommRing αᵐᵒᵖ where
  __ := instSeminormedRing
  __ := instNonUnitalSeminormedCommRing

end SeminormedCommRing

section NormedCommRing

/--
Instance `Subalgebra.seminormedCommRing` / 实例 `Subalgebra.seminormedCommRing`

English:
instance Subalgebra.seminormedCommRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
  body: { s.seminormedRing, s.toCommRing with }

中文:
实例 子代数.seminormedCommRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型} [SeminormedComm环 E]
  定义体: { s.seminormedRing, s.toCommRing with }

Depends on / 依赖: s.seminormedRing, s.toCommRing, seminormedRing, toCommRing
-/
instance Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedCommRing s :=
  { s.seminormedRing, s.toCommRing with }

/--
Instance `Subalgebra.normedCommRing` / 实例 `Subalgebra.normedCommRing`

English:
instance Subalgebra.normedCommRing
  signature: {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
  body: { s.seminormedCommRing, s.normedRing with }

中文:
实例 子代数.normedCommRing
  签名: {𝕜 : 类型} [交换环 𝕜] {E : 类型} [NormedComm环 E]
  定义体: { s.seminormedCommRing, s.normedRing with }

Depends on / 依赖: normedRing, s.normedRing, s.seminormedCommRing, seminormedCommRing
-/
instance Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedCommRing s :=
  { s.seminormedCommRing, s.normedRing with }

variable [NormedCommRing α]

/--
Instance `ULift.normedCommRing` / 实例 `ULift.normedCommRing`

English:
instance ULift.normedCommRing
  signature: : NormedCommRing (ULift α)
  body: { ULift.normedRing (α := α), ULift.seminormedCommRing with }

中文:
实例 类型层提升.normedCommRing
  签名: : NormedComm环 (类型层提升 α)
  定义体: { ULift.normedRing (α := α), ULift.seminormedCommRing with }

Depends on / 依赖: ULift.normedRing, ULift.seminormedCommRing, normedRing, seminormedCommRing
-/
instance ULift.normedCommRing : NormedCommRing (ULift α) :=
  { ULift.normedRing (α := α), ULift.seminormedCommRing with }

/--
Instance `Prod.normedCommRing` / 实例 `Prod.normedCommRing`

English:
instance Prod.normedCommRing
  signature: [NormedCommRing β]
  body: { nonUnitalNormedRing, instCommRing with }

中文:
实例 积类型.normedCommRing
  签名: [NormedComm环 β]
  定义体: { nonUnitalNormedRing, instCommRing with }

Depends on / 依赖: instCommRing, nonUnitalNormedRing
-/
instance Prod.normedCommRing [NormedCommRing β] : NormedCommRing (α × β) :=
  { nonUnitalNormedRing, instCommRing with }

/--
Instance `MulOpposite.instNormedCommRing` / 实例 `MulOpposite.instNormedCommRing`

English:
instance MulOpposite.instNormedCommRing
  signature: : NormedCommRing αᵐᵒᵖ where
  body: instNormedRing
  __ := instSeminormedCommRing

中文:
实例 MulOpposite.instNormedCommRing
  签名: : NormedComm环 αᵐᵒᵖ where
  定义体: instNormedRing
  __ := instSeminormedCommRing

Depends on / 依赖: instNormedRing
-/
instance MulOpposite.instNormedCommRing : NormedCommRing αᵐᵒᵖ where
  __ := instNormedRing
  __ := instSeminormedCommRing

/--
theorem `IsPowMul.restriction` / 定理 `IsPowMul.restriction`

English:
theorem IsPowMul.restriction
  statement: {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
  proof: fun x n hn => by
  simpa using hf_pm (↑x) hn

中文:
定理 IsPowMul.restriction
  结论: {R S : 类型} [交换环 R] [环 S] [代数 R S]
  证明: fun x n hn => by
  simpa using hf_pm (↑x) hn

Depends on / 依赖: hf_pm
-/
theorem IsPowMul.restriction {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (A : Subalgebra R S) {f : S -> Real} (hf_pm : IsPowMul f) :
    IsPowMul fun x : A => f x.val := fun x n hn => by
  simpa using hf_pm (↑x) hn

end NormedCommRing

/--
Instance `Real.normedCommRing` / 实例 `Real.normedCommRing`

English:
instance Real.normedCommRing
  signature: : NormedCommRing Real
  body: { Real.normedAddCommGroup, Real.commRing with norm_mul_le x y := (abs_mul x y).le }

中文:
实例 实数.normedCommRing
  签名: : NormedComm环 实数
  定义体: { Real.normedAddCommGroup, Real.commRing with norm_mul_le x y := (abs_mul x y).le }

Depends on / 依赖: Real.commRing, Real.normedAddCommGroup, abs_mul, commRing, norm_mul_le, normedAddCommGroup
-/
instance Real.normedCommRing : NormedCommRing Real :=
  { Real.normedAddCommGroup, Real.commRing with norm_mul_le x y := (abs_mul x y).le }

namespace NNReal

open NNReal

/--
theorem `norm_eq` / 定理 `norm_eq`

English:
theorem norm_eq
  given: (x : Real>=0)
  statement: ‖(x : Real)‖ = x
  proof: by rw [Real.norm_eq_abs, x.abs_eq]

中文:
定理 norm_eq
  条件: (x : 实数>=0)
  结论: ‖(x : 实数)‖ = x
  证明: by rw [Real.norm_eq_abs, x.abs_eq]

Depends on / 依赖: Real.norm_eq_abs, abs_eq, norm_eq_abs, x.abs_eq
-/
theorem norm_eq (x : Real>=0) : ‖(x : Real)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]

/--
lemma `nnnorm_eq` / 引理 `nnnorm_eq`

English:
lemma nnnorm_eq
  given: (x : Real>=0)
  statement: ‖(x : Real)‖₊ = x
  proof: by ext; simp [nnnorm]

中文:
引理 nnnorm_eq
  条件: (x : 实数>=0)
  结论: ‖(x : 实数)‖₊ = x
  证明: by ext; simp [nnnorm]
-/
@[simp] lemma nnnorm_eq (x : Real>=0) : ‖(x : Real)‖₊ = x := by ext; simp [nnnorm]
/--
lemma `enorm_eq` / 引理 `enorm_eq`

English:
lemma enorm_eq
  given: (x : Real>=0)
  statement: ‖(x : Real)‖ₑ = x
  proof: by simp [enorm]

中文:
引理 enorm_eq
  条件: (x : 实数>=0)
  结论: ‖(x : 实数)‖ₑ = x
  证明: by simp [enorm]
-/
@[simp] lemma enorm_eq (x : Real>=0) : ‖(x : Real)‖ₑ = x := by simp [enorm]

end NNReal

/--
theorem `NormedAddCommGroup.tendsto_atTop` / 定理 `NormedAddCommGroup.tendsto_atTop`

English:
theorem NormedAddCommGroup.tendsto_atTop
  statement: [Nonempty α] [Preorder α] [IsDirectedOrder α]
  proof: (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

中文:
定理 赋范交换加群.tendsto_atTop
  结论: [非空 α] [预序 α] [IsDirectedOrder α]
  证明: (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

Depends on / 依赖: Metric, Metric.nhds_basis_ball, atTop_basis, atTop_basis.tendsto_iff, dist_eq_norm, nhds_basis_ball, tendsto_iff
-/
theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {β : Type*} [SeminormedAddCommGroup β] {f : α -> β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ forall ε, 0 < ε -> exists N, forall n, N <= n -> ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/--
theorem `NormedAddCommGroup.tendsto_atTop'` / 定理 `NormedAddCommGroup.tendsto_atTop'`

English:
theorem NormedAddCommGroup.tendsto_atTop'
  statement: [Nonempty α] [Preorder α] [IsDirectedOrder α]
  proof: (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

中文:
定理 赋范交换加群.tendsto_atTop'
  结论: [非空 α] [预序 α] [IsDirectedOrder α]
  证明: (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

Depends on / 依赖: Metric, Metric.nhds_basis_ball, atTop_basis_Ioi, atTop_basis_Ioi.tendsto_iff, dist_eq_norm, nhds_basis_ball, tendsto_iff
-/
theorem NormedAddCommGroup.tendsto_atTop' [Nonempty α] [Preorder α] [IsDirectedOrder α]
    [NoMaxOrder α] {β : Type*} [SeminormedAddCommGroup β] {f : α -> β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ forall ε, 0 < ε -> exists N, forall n, N < n -> ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

section RingHomIsometric

variable {R₁ R₂ : Type*}

/--
Definition of `RingHomIsometric` / `RingHomIsometric` 的定义

English:
class RingHomIsometric
  parameters: [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ ->+* R₂)
  axioms and operations (1):
    - norm_map : forall {x : R₁}, ‖σ x‖ = ‖x‖

中文:
类 RingHomIsometric
  参数: [半环 R₁] [半环 R₂] [范数 R₁] [范数 R₂] (σ : R₁ ->+* R₂)
  公理与运算 (1 个):
    - norm_map : 对任意 {x : R₁}, ‖σ x‖ = ‖x‖
-/
class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ ->+* R₂) : Prop where
  /-- The ring homomorphism is an isometry. -/
  norm_map : forall {x : R₁}, ‖σ x‖ = ‖x‖

attribute [simp] RingHomIsometric.norm_map

@[simp]
/--
theorem `RingHomIsometric.nnnorm_map` / 定理 `RingHomIsometric.nnnorm_map`

English:
theorem RingHomIsometric.nnnorm_map
  statement: [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ ->+* R₂)
  proof: NNReal.eq norm_map

@[simp]

中文:
定理 RingHomIsometric.nnnorm_map
  结论: [Seminormed环 R₁] [Seminormed环 R₂] (σ : R₁ ->+* R₂)
  证明: NNReal.eq norm_map

@[simp]

Depends on / 依赖: NNReal, NNReal.eq, norm_map
-/
theorem RingHomIsometric.nnnorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ ->+* R₂)
    [RingHomIsometric σ] (x : R₁) : ‖σ x‖₊ = ‖x‖₊ :=
  NNReal.eq norm_map

@[simp]
/--
theorem `RingHomIsometric.enorm_map` / 定理 `RingHomIsometric.enorm_map`

English:
theorem RingHomIsometric.enorm_map
  statement: [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ ->+* R₂)
  proof: congrArg ENNReal.ofNNReal nnnorm_map σ x

中文:
定理 RingHomIsometric.enorm_map
  结论: [Seminormed环 R₁] [Seminormed环 R₂] (σ : R₁ ->+* R₂)
  证明: congrArg ENNReal.ofNNReal nnnorm_map σ x

Depends on / 依赖: ENNReal, ENNReal.ofNNReal, nnnorm_map, ofNNReal
-/
theorem RingHomIsometric.enorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ ->+* R₂)
    [RingHomIsometric σ] (x : R₁) : ‖σ x‖ₑ = ‖x‖ₑ :=
congrArg ENNReal.ofNNReal nnnorm_map σ x

variable [SeminormedRing R₁]

/--
Instance `RingHomIsometric.ids` / 实例 `RingHomIsometric.ids`

English:
instance RingHomIsometric.ids
  signature: : RingHomIsometric (RingHom.id R₁)
  body: ⟨rfl⟩

中文:
实例 RingHomIsometric.ids
  签名: : RingHomIsometric (环态射.id R₁)
  定义体: ⟨rfl⟩
-/
instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨rfl⟩

end RingHomIsometric

section NormMulClass

/--
Definition of `NormMulClass` / `NormMulClass` 的定义

English:
class NormMulClass
  parameters: (α : Type*) [Norm α] [Mul α]
  axioms and operations (1):
    - norm_mul : forall (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖

中文:
类 NormMul类
  参数: (α : 类型) [范数 α] [乘法 α]
  公理与运算 (1 个):
    - norm_mul : 对任意 (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
-/
class NormMulClass (α : Type*) [Norm α] [Mul α] : Prop where
  /-- The norm is multiplicative. -/
  protected norm_mul : forall (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖

/--
lemma `norm_mul` / 引理 `norm_mul`

English:
lemma norm_mul
  given: [Norm α] [Mul α] [NormMulClass α] (a b : α)
  proof: NormMulClass.norm_mul a b

中文:
引理 norm_mul
  条件: [范数 α] [乘法 α] [NormMul类 α] (a b : α)
  证明: NormMulClass.norm_mul a b
-/
@[simp] lemma norm_mul [Norm α] [Mul α] [NormMulClass α] (a b : α) :
    ‖a * b‖ = ‖a‖ * ‖b‖ :=
  NormMulClass.norm_mul a b

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [Mul α] [NormMulClass α] (a b : α)

/--
lemma `nnnorm_mul` / 引理 `nnnorm_mul`

English:
lemma nnnorm_mul
  statement: ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
  proof: NNReal.eq norm_mul a b

中文:
引理 nnnorm_mul
  结论: ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
  证明: NNReal.eq norm_mul a b
-/
@[simp] lemma nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ := NNReal.eq norm_mul a b

/--
lemma `enorm_mul` / 引理 `enorm_mul`

English:
lemma enorm_mul
  statement: ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
  proof: by simp [enorm]

中文:
引理 enorm_mul
  结论: ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
  证明: by simp [enorm]
-/
@[simp] lemma enorm_mul : ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by simp [enorm]

end SeminormedAddCommGroup

section SeminormedRing

variable [SeminormedRing α] [NormOneClass α] [NormMulClass α]

/-- `norm` as a `MonoidWithZeroHom`. -/
@[simps]
/--
Definition of `normHom` / `normHom` 的定义

English:
definition normHom
  signature: : α ->*₀ Real where
  body: (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul

中文:
定义 normHom
  签名: : α ->*₀ 实数 where
  定义体: (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul
-/
def normHom : α ->*₀ Real where
  toFun := (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul

/-- `nnnorm` as a `MonoidWithZeroHom`. -/
@[simps]
/--
Definition of `nnnormHom` / `nnnormHom` 的定义

English:
definition nnnormHom
  signature: : α ->*₀ Real>=0 where
  body: (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul

@[simp]

中文:
定义 nnnormHom
  签名: : α ->*₀ 实数>=0 where
  定义体: (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul

@[simp]
-/
def nnnormHom : α ->*₀ Real>=0 where
  toFun := (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul

@[simp]
/--
theorem `norm_pow` / 定理 `norm_pow`

English:
theorem norm_pow
  given: (a : α)
  statement: forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
  proof: (normHom.toMonoidHom : α ->* Real).map_pow a

@[simp]

中文:
定理 norm_pow
  条件: (a : α)
  结论: 对任意 n : 自然数, ‖a ^ n‖ = ‖a‖ ^ n
  证明: (normHom.toMonoidHom : α ->* Real).map_pow a

@[simp]

Depends on / 依赖: map_pow, normHom, normHom.toMonoidHom, toMonoidHom
-/
theorem norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n :=
  (normHom.toMonoidHom : α ->* Real).map_pow a

@[simp]
/--
theorem `nnnorm_pow` / 定理 `nnnorm_pow`

English:
theorem nnnorm_pow
  given: (a : α) (n : Nat)
  statement: ‖a ^ n‖₊ = ‖a‖₊ ^ n
  proof: (nnnormHom.toMonoidHom : α ->* Real>=0).map_pow a n

中文:
定理 nnnorm_pow
  条件: (a : α) (n : 自然数)
  结论: ‖a ^ n‖₊ = ‖a‖₊ ^ n
  证明: (nnnormHom.toMonoidHom : α ->* Real>=0).map_pow a n

Depends on / 依赖: map_pow, nnnormHom, nnnormHom.toMonoidHom, toMonoidHom
-/
theorem nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  (nnnormHom.toMonoidHom : α ->* Real>=0).map_pow a n

/--
lemma `enorm_pow` / 引理 `enorm_pow`

English:
lemma enorm_pow
  given: (a : α) (n : Nat)
  statement: ‖a ^ n‖ₑ = ‖a‖ₑ ^ n
  proof: by simp [enorm]

中文:
引理 enorm_pow
  条件: (a : α) (n : 自然数)
  结论: ‖a ^ n‖ₑ = ‖a‖ₑ ^ n
  证明: by simp [enorm]
-/
@[simp] lemma enorm_pow (a : α) (n : Nat) : ‖a ^ n‖ₑ = ‖a‖ₑ ^ n := by simp [enorm]

/--
theorem `List.norm_prod` / 定理 `List.norm_prod`

English:
theorem List.norm_prod
  given: (l : List α)
  statement: ‖l.prod‖ = (l.map norm).prod
  proof: map_list_prod (normHom.toMonoidHom : α ->* Real) _

中文:
定理 列表.norm_prod
  条件: (l : 列表 α)
  结论: ‖l.乘积‖ = (l.map norm).乘积
  证明: map_list_prod (normHom.toMonoidHom : α ->* Real) _
-/
protected theorem List.norm_prod (l : List α) : ‖l.prod‖ = (l.map norm).prod :=
  map_list_prod (normHom.toMonoidHom : α ->* Real) _

/--
theorem `List.nnnorm_prod` / 定理 `List.nnnorm_prod`

English:
theorem List.nnnorm_prod
  given: (l : List α)
  statement: ‖l.prod‖₊ = (l.map nnnorm).prod
  proof: map_list_prod (nnnormHom.toMonoidHom : α ->* Real>=0) _

中文:
定理 列表.nnnorm_prod
  条件: (l : 列表 α)
  结论: ‖l.乘积‖₊ = (l.map nnnorm).乘积
  证明: map_list_prod (nnnormHom.toMonoidHom : α ->* Real>=0) _
-/
protected theorem List.nnnorm_prod (l : List α) : ‖l.prod‖₊ = (l.map nnnorm).prod :=
  map_list_prod (nnnormHom.toMonoidHom : α ->* Real>=0) _

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing α] [NormMulClass α] [NormOneClass α]

@[simp]
/--
theorem `norm_prod` / 定理 `norm_prod`

English:
theorem norm_prod
  given: (s : Finset β) (f : β -> α)
  statement: ‖∏ b in s, f b‖ = ∏ b in s, ‖f b‖
  proof: map_prod normHom.toMonoidHom f s

@[simp]

中文:
定理 norm_prod
  条件: (s : 有限集 β) (f : β -> α)
  结论: ‖∏ b in s, f b‖ = ∏ b in s, ‖f b‖
  证明: map_prod normHom.toMonoidHom f s

@[simp]

Depends on / 依赖: map_prod, normHom, normHom.toMonoidHom, toMonoidHom
-/
theorem norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b in s, ‖f b‖ :=
  map_prod normHom.toMonoidHom f s

@[simp]
/--
theorem `nnnorm_prod` / 定理 `nnnorm_prod`

English:
theorem nnnorm_prod
  given: (s : Finset β) (f : β -> α)
  statement: ‖∏ b in s, f b‖₊ = ∏ b in s, ‖f b‖₊
  proof: map_prod nnnormHom.toMonoidHom f s

中文:
定理 nnnorm_prod
  条件: (s : 有限集 β) (f : β -> α)
  结论: ‖∏ b in s, f b‖₊ = ∏ b in s, ‖f b‖₊
  证明: map_prod nnnormHom.toMonoidHom f s

Depends on / 依赖: map_prod, nnnormHom, nnnormHom.toMonoidHom, toMonoidHom
-/
theorem nnnorm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖₊ = ∏ b in s, ‖f b‖₊ :=
  map_prod nnnormHom.toMonoidHom f s

end SeminormedCommRing

section NormedAddCommGroup
variable [NormedAddCommGroup α] [MulOneClass α] [NormMulClass α] [Nontrivial α]

/--
lemma `NormMulClass.toNormOneClass` / 引理 `NormMulClass.toNormOneClass`

English:
lemma NormMulClass.toNormOneClass
  statement: NormOneClass α where
  proof: by
    obtain ⟨u, hu⟩ := exists_ne (0 : α)
    simpa [mul_eq_left₀ (norm_ne_zero_iff.mpr hu)] using (norm_mul u 1).symm

中文:
引理 NormMul类.toNormOneClass
  结论: NormOne类 α where
  证明: by
    obtain ⟨u, hu⟩ := exists_ne (0 : α)
    simpa [mul_eq_left₀ (norm_ne_zero_iff.mpr hu)] using (norm_mul u 1).symm

Depends on / 依赖: exists_ne, norm_mul, norm_ne_zero_iff, norm_ne_zero_iff.mpr
-/
lemma NormMulClass.toNormOneClass : NormOneClass α where
  norm_one := by
    obtain ⟨u, hu⟩ := exists_ne (0 : α)
    simpa [mul_eq_left₀ (norm_ne_zero_iff.mpr hu)] using (norm_mul u 1).symm

end NormedAddCommGroup

section NormedRing
variable [NormedRing α] [NormMulClass α]

/--
Instance `NormMulClass.isAbsoluteValue_norm` / 实例 `NormMulClass.isAbsoluteValue_norm`

English:
instance NormMulClass.isAbsoluteValue_norm
  signature: : IsAbsoluteValue (norm : α -> Real) where
  body: norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := norm_mul

中文:
实例 NormMul类.isAbsoluteValue_norm
  签名: : 是绝对值 (norm : α -> 实数) where
  定义体: norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := norm_mul

Depends on / 依赖: norm_nonneg
-/
instance NormMulClass.isAbsoluteValue_norm : IsAbsoluteValue (norm : α -> Real) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := norm_mul

/--
Instance `NormMulClass.toNoZeroDivisors` / 实例 `NormMulClass.toNoZeroDivisors`

English:
instance NormMulClass.toNoZeroDivisors
  signature: : NoZeroDivisors α where
  body: by
    simpa only [← norm_eq_zero (E := α), norm_mul, mul_eq_zero] using h

中文:
实例 NormMul类.toNoZeroDivisors
  签名: : 无零因子 α where
  定义体: by
    simpa only [← norm_eq_zero (E := α), norm_mul, mul_eq_zero] using h

Depends on / 依赖: mul_eq_zero, norm_eq_zero, norm_mul
-/
instance NormMulClass.toNoZeroDivisors : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero h := by
    simpa only [← norm_eq_zero (E := α), norm_mul, mul_eq_zero] using h

end NormedRing

end NormMulClass

/-! ### Induced normed structures -/

section Induced

variable {F : Type*} (R S : Type*) [FunLike F R S]

/--
Definition of `NonUnitalSeminormedRing.induced` / `NonUnitalSeminormedRing.induced` 的定义

English:
abbreviation NonUnitalSeminormedRing.induced
  signature: [NonUnitalRing R] [NonUnitalSeminormedRing S]
  body: fast_instance%
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul_le x y := show ‖f _‖ <= _ from (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

中文:
缩写 非幺Seminormed环.induced
  签名: [非幺环 R] [非幺Seminormed环 S]
  定义体: fast_instance%
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul_le x y := show ‖f _‖ <= _ from (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

Depends on / 依赖: fast_instance
-/
abbrev NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R := fast_instance%
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul_le x y := show ‖f _‖ <= _ from (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

/--
Definition of `NonUnitalNormedRing.induced` / `NonUnitalNormedRing.induced` 的定义

English:
abbreviation NonUnitalNormedRing.induced
  signature: [NonUnitalRing R] [NonUnitalNormedRing S]
  body: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

中文:
缩写 非幺赋范环.induced
  签名: [非幺环 R] [非幺赋范环 S]
  定义体: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

Depends on / 依赖: fast_instance
-/
abbrev NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) :
    NonUnitalNormedRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

/--
Definition of `SeminormedRing.induced` / `SeminormedRing.induced` 的定义

English:
abbreviation SeminormedRing.induced
  signature: [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F)
  body: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }

中文:
缩写 Seminormed环.induced
  签名: [环 R] [Seminormed环 S] [非幺环态射类 F R S] (f : F)
  定义体: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }

Depends on / 依赖: fast_instance
-/
abbrev SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SeminormedRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }

/--
Definition of `NormedRing.induced` / `NormedRing.induced` 的定义

English:
abbreviation NormedRing.induced
  signature: [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
  body: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }

中文:
缩写 赋范环.induced
  签名: [环 R] [赋范环 S] [非幺环态射类 F R S] (f : F)
  定义体: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }

Depends on / 依赖: fast_instance
-/
abbrev NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }

/--
Definition of `NonUnitalSeminormedCommRing.induced` / `NonUnitalSeminormedCommRing.induced` 的定义

English:
abbreviation NonUnitalSeminormedCommRing.induced
  signature: [NonUnitalCommRing R] [NonUnitalSeminormedCommRing S]
  body: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

中文:
缩写 非幺SeminormedComm环.induced
  签名: [非幺交换环 R] [非幺SeminormedComm环 S]
  定义体: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

Depends on / 依赖: fast_instance
-/
abbrev NonUnitalSeminormedCommRing.induced [NonUnitalCommRing R] [NonUnitalSeminormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedCommRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

/--
Definition of `NonUnitalNormedCommRing.induced` / `NonUnitalNormedCommRing.induced` 的定义

English:
abbreviation NonUnitalNormedCommRing.induced
  signature: [NonUnitalCommRing R] [NonUnitalNormedCommRing S]
  body: fast_instance%
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }

中文:
缩写 非幺NormedComm环.induced
  签名: [非幺交换环 R] [非幺NormedComm环 S]
  定义体: fast_instance%
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }

Depends on / 依赖: fast_instance
-/
abbrev NonUnitalNormedCommRing.induced [NonUnitalCommRing R] [NonUnitalNormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) :
    NonUnitalNormedCommRing R := fast_instance%
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }
/--
Definition of `SeminormedCommRing.induced` / `SeminormedCommRing.induced` 的定义

English:
abbreviation SeminormedCommRing.induced
  signature: [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
  body: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }

中文:
缩写 SeminormedComm环.induced
  签名: [交换环 R] [Seminormed环 S] [非幺环态射类 F R S]
  定义体: fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }

Depends on / 依赖: fast_instance
-/
abbrev SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SeminormedCommRing R := fast_instance%
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }

/--
Definition of `NormedCommRing.induced` / `NormedCommRing.induced` 的定义

English:
abbreviation NormedCommRing.induced
  signature: [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
  body: fast_instance%
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

中文:
缩写 NormedComm环.induced
  签名: [交换环 R] [赋范环 S] [非幺环态射类 F R S] (f : F)
  定义体: fast_instance%
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

Depends on / 依赖: fast_instance
-/
abbrev NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R := fast_instance%
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

/--
theorem `NormOneClass.induced` / 定理 `NormOneClass.induced`

English:
theorem NormOneClass.induced
  statement: {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
  proof: let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

中文:
定理 NormOne类.induced
  结论: {F : 类型} (R S : 类型) [环 R] [Seminormed环 S]
  证明: let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

Depends on / 依赖: SeminormedRing, SeminormedRing.induced, congr_arg, induced, map_one, norm_one
-/
theorem NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SeminormedRing.induced R S f).toNorm _ :=
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

/--
theorem `NormMulClass.induced` / 定理 `NormMulClass.induced`

English:
theorem NormMulClass.induced
  statement: {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
  proof: let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_mul x y := (congr_arg norm (map_mul f x y)).trans <| norm_mul _ _ }

中文:
定理 NormMul类.induced
  结论: {F : 类型} (R S : 类型) [环 R] [Seminormed环 S]
  证明: let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_mul x y := (congr_arg norm (map_mul f x y)).trans <| norm_mul _ _ }

Depends on / 依赖: SeminormedRing, SeminormedRing.induced, congr_arg, induced, map_mul, norm_mul
-/
theorem NormMulClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormMulClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormMulClass R (SeminormedRing.induced R S f).toNorm _ :=
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_mul x y := (congr_arg norm (map_mul f x y)).trans <| norm_mul _ _ }

end Induced

namespace SubringClass

variable {S R : Type*} [SetLike S R]

/--
Instance `toSeminormedRing` / 实例 `toSeminormedRing`

English:
instance toSeminormedRing
  signature: [SeminormedRing R] [SubringClass S R] (s : S)
  body: fast_instance% SeminormedRing.induced s R (SubringClass.subtype s)

中文:
实例 toSeminormedRing
  签名: [Seminormed环 R] [子环类 S R] (s : S)
  定义体: fast_instance% SeminormedRing.induced s R (SubringClass.subtype s)

Depends on / 依赖: SeminormedRing, SeminormedRing.induced, SubringClass, SubringClass.subtype, fast_instance, induced, subtype
-/
instance toSeminormedRing [SeminormedRing R] [SubringClass S R] (s : S) : SeminormedRing s :=
  fast_instance% SeminormedRing.induced s R (SubringClass.subtype s)

/--
Instance `toNormedRing` / 实例 `toNormedRing`

English:
instance toNormedRing
  signature: [NormedRing R] [SubringClass S R] (s : S)
  body: fast_instance% NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective

中文:
实例 toNormedRing
  签名: [赋范环 R] [子环类 S R] (s : S)
  定义体: fast_instance% NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective

Depends on / 依赖: NormedRing, NormedRing.induced, SubringClass, SubringClass.subtype, Subtype, Subtype.val_injective, fast_instance, induced, subtype, val_injective
-/
instance toNormedRing [NormedRing R] [SubringClass S R] (s : S) : NormedRing s :=
  fast_instance% NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective

/--
Instance `toSeminormedCommRing` / 实例 `toSeminormedCommRing`

English:
instance toSeminormedCommRing
  signature: [SeminormedCommRing R] [_h : SubringClass S R] (s : S)
  body: fast_instance% SeminormedCommRing.induced s R (SubringClass.subtype s)

中文:
实例 toSeminormedCommRing
  签名: [SeminormedComm环 R] [_h : 子环类 S R] (s : S)
  定义体: fast_instance% SeminormedCommRing.induced s R (SubringClass.subtype s)

Depends on / 依赖: SeminormedCommRing, SeminormedCommRing.induced, SubringClass, SubringClass.subtype, fast_instance, induced, subtype
-/
instance toSeminormedCommRing [SeminormedCommRing R] [_h : SubringClass S R] (s : S) :
    SeminormedCommRing s :=
  fast_instance% SeminormedCommRing.induced s R (SubringClass.subtype s)

/--
Instance `toNormedCommRing` / 实例 `toNormedCommRing`

English:
instance toNormedCommRing
  signature: [NormedCommRing R] [SubringClass S R] (s : S)
  body: fast_instance% NormedCommRing.induced s R (SubringClass.subtype s) Subtype.val_injective

中文:
实例 toNormedCommRing
  签名: [NormedComm环 R] [子环类 S R] (s : S)
  定义体: fast_instance% NormedCommRing.induced s R (SubringClass.subtype s) Subtype.val_injective

Depends on / 依赖: NormedCommRing, NormedCommRing.induced, SubringClass, SubringClass.subtype, Subtype, Subtype.val_injective, fast_instance, induced, subtype, val_injective
-/
instance toNormedCommRing [NormedCommRing R] [SubringClass S R] (s : S) : NormedCommRing s :=
  fast_instance% NormedCommRing.induced s R (SubringClass.subtype s) Subtype.val_injective

/--
Instance `toNormOneClass` / 实例 `toNormOneClass`

English:
instance toNormOneClass
  signature: [SeminormedRing R] [NormOneClass R] [SubringClass S R] (s : S)
  body: .induced s R SubringClass.subtype _

中文:
实例 toNormOneClass
  签名: [Seminormed环 R] [NormOne类 R] [子环类 S R] (s : S)
  定义体: .induced s R SubringClass.subtype _

Depends on / 依赖: SubringClass, SubringClass.subtype, induced, subtype
-/
instance toNormOneClass [SeminormedRing R] [NormOneClass R] [SubringClass S R] (s : S) :
    NormOneClass s :=
.induced s R SubringClass.subtype _

/--
Instance `toNormMulClass` / 实例 `toNormMulClass`

English:
instance toNormMulClass
  signature: [SeminormedRing R] [NormMulClass R] [SubringClass S R] (s : S)
  body: .induced s R SubringClass.subtype _

中文:
实例 toNormMulClass
  签名: [Seminormed环 R] [NormMul类 R] [子环类 S R] (s : S)
  定义体: .induced s R SubringClass.subtype _

Depends on / 依赖: SubringClass, SubringClass.subtype, induced, subtype
-/
instance toNormMulClass [SeminormedRing R] [NormMulClass R] [SubringClass S R] (s : S) :
    NormMulClass s :=
.induced s R SubringClass.subtype _

end SubringClass

namespace AbsoluteValue

/-- A real absolute value on a ring determines a `NormedRing` structure. -/
@[instance_reducible]
/--
Definition of `toNormedRing` / `toNormedRing` 的定义

English:
definition toNormedRing
  signature: {R : Type*} [Ring R] (v : AbsoluteValue R Real)
  body: v
  dist x y := v (-x + y)
  dist_eq _ _ := rfl
  dist_self x := by simp
  dist_comm x y := by rw [add_comm (-x), add_comm (-y), ← sub_eq_add_neg, v.map_sub, sub_eq_add_neg]
  dist_triangle x y z := by simpa [neg_add_eq_sub, add_comm (v (y - x))] using v.sub_le z y x
  edist_dist x y := rfl
  norm_mul_le x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by
    intro x y hxy
    rw [add_comm]; rw [← sub_eq_add_neg]; rw [AbsoluteValue.map_sub_eq_zero_iff] at hxy
    exact hxy.symm

中文:
定义 toNormedRing
  签名: {R : 类型} [环 R] (v : 绝对值 R 实数)
  定义体: v
  dist x y := v (-x + y)
  dist_eq _ _ := rfl
  dist_self x := by simp
  dist_comm x y := by rw [add_comm (-x), add_comm (-y), ← sub_eq_add_neg, v.map_sub, sub_eq_add_neg]
  dist_triangle x y z := by simpa [neg_add_eq_sub, add_comm (v (y - x))] using v.sub_le z y x
  edist_dist x y := rfl
  norm_mul_le x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by
    intro x y hxy
    rw [add_comm]; rw [← sub_eq_add_neg]; rw [AbsoluteValue.map_sub_eq_zero_iff] at hxy
    exact hxy.symm
-/
noncomputable def toNormedRing {R : Type*} [Ring R] (v : AbsoluteValue R Real) : NormedRing R where
  norm := v
  dist x y := v (-x + y)
  dist_eq _ _ := rfl
  dist_self x := by simp
  dist_comm x y := by rw [add_comm (-x), add_comm (-y), ← sub_eq_add_neg, v.map_sub, sub_eq_add_neg]
  dist_triangle x y z := by simpa [neg_add_eq_sub, add_comm (v (y - x))] using v.sub_le z y x
  edist_dist x y := rfl
  norm_mul_le x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by
    intro x y hxy
    rw [add_comm]; rw [← sub_eq_add_neg]; rw [AbsoluteValue.map_sub_eq_zero_iff] at hxy
    exact hxy.symm

end AbsoluteValue

namespace Real

/-
Note: We cannot easily generalize this to targets other than `ℝ`, because we need
the fact that `⨆ i, f i = 0` when the indexing type is empty (`Real.iSup_of_isEmpty`).
-/

section mul

variable {R ι ι' : Type*} [Semiring R] [Finite ι] [Finite ι']

/--
lemma `iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg` / 引理 `iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg`

English:
lemma iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg
  statement: {F : Type*} [FunLike F R Real]
  proof: by
  simp_rw [Real.iSup_mul_of_nonneg (iSup_nonneg fun i => apply_nonneg v (y i)),
    Real.mul_iSup_of_nonneg (apply_nonneg v _), map_mul, Finite.ciSup_prod]

中文:
引理 iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg
  结论: {F : 类型} [函数状 F R 实数]
  证明: by
  simp_rw [Real.iSup_mul_of_nonneg (iSup_nonneg fun i => apply_nonneg v (y i)),
    Real.mul_iSup_of_nonneg (apply_nonneg v _), map_mul, Finite.ciSup_prod]

Depends on / 依赖: Finite, Finite.ciSup_prod, Real.iSup_mul_of_nonneg, Real.mul_iSup_of_nonneg, apply_nonneg, ciSup_prod, iSup_mul_of_nonneg, iSup_nonneg, map_mul, mul_iSup_of_nonneg, simp_rw
-/
lemma iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg {F : Type*} [FunLike F R Real]
    [NonnegHomClass F R Real] [MulHomClass F R Real] (v : F) (x : ι -> R) (y : ι' -> R) :
    ⨆ a : ι × ι', v (x a.1 * y a.2) = (⨆ i, v (x i)) * ⨆ j, v (y j) := by
  simp_rw [Real.iSup_mul_of_nonneg (iSup_nonneg fun i => apply_nonneg v (y i)),
    Real.mul_iSup_of_nonneg (apply_nonneg v _), map_mul, Finite.ciSup_prod]

end mul

/-
Note: We cannot easily generalize this to targets other than `ℝ`, because we need
the fact that `⨆ i, f i = 0` when the indexing type is empty (`Real.iSup_of_isEmpty`).
-/

section prod

universe u v

variable {α R : Type*} [Fintype α] {ι : α -> Type u} [forall a, Finite (ι a)]

/--
lemma `iSup_prod_eq_prod_iSup_of_nonneg` / 引理 `iSup_prod_eq_prod_iSup_of_nonneg`

English:
lemma iSup_prod_eq_prod_iSup_of_nonneg
  given: {f : (a : α) -> ι a -> Real} (hf₀ : forall a i, 0 <= f a i)
  proof: by
  rcases isEmpty_or_nonempty ((a : α) -> ι a) with h | h
  · rw [iSup_of_isEmpty, eq_comm, Finset.prod_eq_zero_iff]
    obtain ⟨a, ha⟩ := isEmpty_pi.mp h
    exact ⟨a, by simp⟩
  refine le_antisymm ?_ ?_
  · exact ciSup_le fun i => Finset.prod_le_prod (by simp [hf₀])
      fun a ha => Finite.le_ciSup_of_le _ le_rfl
  · rw [Classical.nonempty_pi] at h
    have H a : exists i : ι a, f a i = ⨆ i, f a i := exists_eq_ciSup_of_finite
    choose i hi using H
    simp only [← hi]
    exact Finite.le_ciSup_of_le i le_rfl

中文:
引理 iSup_prod_eq_prod_iSup_of_nonneg
  条件: {f : (a : α) -> ι a -> 实数} (hf₀ : 对任意 a i, 0 <= f a i)
  证明: by
  rcases isEmpty_or_nonempty ((a : α) -> ι a) with h | h
  · rw [iSup_of_isEmpty, eq_comm, Finset.prod_eq_zero_iff]
    obtain ⟨a, ha⟩ := isEmpty_pi.mp h
    exact ⟨a, by simp⟩
  refine le_antisymm ?_ ?_
  · exact ciSup_le fun i => Finset.prod_le_prod (by simp [hf₀])
      fun a ha => Finite.le_ciSup_of_le _ le_rfl
  · rw [Classical.nonempty_pi] at h
    have H a : exists i : ι a, f a i = ⨆ i, f a i := exists_eq_ciSup_of_finite
    choose i hi using H
    simp only [← hi]
    exact Finite.le_ciSup_of_le i le_rfl

Depends on / 依赖: Classical, Classical.nonempty_pi, Finite, Finite.le_ciSup_of_le, Finset, Finset.prod_eq_zero_iff, Finset.prod_le_prod, ciSup_le, eq_comm, exists_eq_ciSup_of_finite, iSup_of_isEmpty, isEmpty_or_nonempty, isEmpty_pi, isEmpty_pi.mp, le_antisymm, le_ciSup_of_le, le_rfl, nonempty_pi, prod_eq_zero_iff, prod_le_prod
-/
lemma iSup_prod_eq_prod_iSup_of_nonneg {f : (a : α) -> ι a -> Real} (hf₀ : forall a i, 0 <= f a i) :
    ⨆ (i : (a : α) -> ι a), ∏ a, f a (i a) = ∏ a, ⨆ i, f a i := by
  rcases isEmpty_or_nonempty ((a : α) -> ι a) with h | h
  · rw [iSup_of_isEmpty, eq_comm, Finset.prod_eq_zero_iff]
    obtain ⟨a, ha⟩ := isEmpty_pi.mp h
    exact ⟨a, by simp⟩
  refine le_antisymm ?_ ?_
  · exact ciSup_le fun i => Finset.prod_le_prod (by simp [hf₀])
      fun a ha => Finite.le_ciSup_of_le _ le_rfl
  · rw [Classical.nonempty_pi] at h
    have H a : exists i : ι a, f a i = ⨆ i, f a i := exists_eq_ciSup_of_finite
    choose i hi using H
    simp only [← hi]
    exact Finite.le_ciSup_of_le i le_rfl

/--
lemma `iSup_prod_eq_prod_iSup_of_nonnegHomClass` / 引理 `iSup_prod_eq_prod_iSup_of_nonnegHomClass`

English:
lemma iSup_prod_eq_prod_iSup_of_nonnegHomClass
  statement: {F : Type*} [FunLike F R Real]
  proof: Real.iSup_prod_eq_prod_iSup_of_nonneg (f := fun a i => v (x a i)) (fun _ _ => apply_nonneg v _)

中文:
引理 iSup_prod_eq_prod_iSup_of_nonnegHomClass
  结论: {F : 类型} [函数状 F R 实数]
  证明: Real.iSup_prod_eq_prod_iSup_of_nonneg (f := fun a i => v (x a i)) (fun _ _ => apply_nonneg v _)

Depends on / 依赖: Real.iSup_prod_eq_prod_iSup_of_nonneg, apply_nonneg, iSup_prod_eq_prod_iSup_of_nonneg
-/
lemma iSup_prod_eq_prod_iSup_of_nonnegHomClass {F : Type*} [FunLike F R Real]
    [NonnegHomClass F R Real] (v : F) {x : (a : α) -> ι a -> R} :
    ⨆ (i : (a : α) -> ι a), ∏ a, v (x a (i a)) = ∏ a, ⨆ i, v (x a i) :=
  Real.iSup_prod_eq_prod_iSup_of_nonneg (f := fun a i => v (x a i)) (fun _ _ => apply_nonneg v _)

end prod

end Real
