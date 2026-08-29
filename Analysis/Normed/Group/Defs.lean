/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Topology.Order.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Tactic.Group
public import Mathlib.Topology.MetricSpace.Defs

/-!
# (Semi)normed groups: definitions

In this file we define 10 classes:

* `Norm`, `NNNorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `‖x‖`) and `nnnorm : α → ℝ≥0` (notation: `‖x‖₊`), respectively;
* `Seminormed...Group`: A seminormed (additive) (commutative) group is an (additive) (commutative)
  group with a norm and a compatible pseudometric space structure:
  `∀ x y, dist x y = ‖x⁻¹ * y‖` or `∀ x y, dist x y = ‖-x + y‖`, depending on the group operation.
* `Normed...Group`: A normed (additive) (commutative) group is an (additive) (commutative) group
  with a norm and a compatible metric space structure.

We also provide some instances relating these classes.

## Notes

The current convention `dist x y = ‖-x + y‖` means that the distance is invariant under left
addition. This is especially relevant in multiplicative contexts: in the Cayley graph of the
free group, for instance, we want `w` to be joined by an edge to `ws` when `s` is a generator,
so these points should be at distance `1`, and moreover left multiplication should be an isometry.
This is the case with the formula `dist x y = ‖x⁻¹ * y‖` we use, while it would be wrong with
`‖x * y⁻¹‖`.

The normed group hierarchy would lend itself well to a mixin design (that is, having
`SeminormedGroup` and `SeminormedAddGroup` not extend `Group` and `AddGroup`), but we choose not
to for performance concerns.

## Tags

normed group
-/

public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ` with notation `‖x‖`. This
class is designed to be extended in more interesting classes specifying the properties of the norm.
-/
@[notation_class]
/--
Definition of `Norm` / `Norm` 的定义

English:
class Norm
  parameters: (E : Type*)
  axioms and operations (1):
    - norm : E -> Real

中文:
类 Norm
  参数: (E : 类型)
  公理与运算 (1 个):
    - norm : E -> 实数
-/
class Norm (E : Type*) where
  /-- the `ℝ`-valued norm function. -/
  norm : E -> Real

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0` with notation `‖x‖₊`. -/
@[notation_class]
/--
Definition of `NNNorm` / `NNNorm` 的定义

English:
class NNNorm
  parameters: (E : Type*)
  axioms and operations (1):
    - nnnorm : E -> Real>=0

中文:
类 NNNorm
  参数: (E : 类型)
  公理与运算 (1 个):
    - nnnorm : E -> 实数>=0
-/
class NNNorm (E : Type*) where
  /-- the `ℝ≥0`-valued norm function. -/
  nnnorm : E -> Real>=0

/-- Auxiliary class, endowing a type `α` with a function `enorm : α → ℝ≥0∞` with notation `‖x‖ₑ`. -/
@[notation_class]
/--
Definition of `ENorm` / `ENorm` 的定义

English:
class ENorm
  parameters: (E : Type*)
  axioms and operations (1):
    - enorm : E -> Real>=0∞

中文:
类 ENorm
  参数: (E : 类型)
  公理与运算 (1 个):
    - enorm : E -> 实数>=0∞
-/
class ENorm (E : Type*) where
  /-- the `ℝ≥0∞`-valued norm function. -/
  enorm : E -> Real>=0∞

export Norm (norm)
export NNNorm (nnnorm)
export ENorm (enorm)

@[inherit_doc] notation "‖" e "‖" => norm e
@[inherit_doc] notation "‖" e "‖₊" => nnnorm e
@[inherit_doc] notation "‖" e "‖ₑ" => enorm e

section ENorm
variable {E : Type*} [NNNorm E] {x : E} {r : Real>=0}

/--
Instance `NNNorm.toENorm` / 实例 `NNNorm.toENorm`

English:
instance NNNorm.toENorm
  signature: : ENorm E where enorm
  body: (‖·‖₊ : E -> Real>=0∞)

中文:
实例 NNNorm.toENorm
  签名: : ENorm E where enorm
  定义体: (‖·‖₊ : E -> Real>=0∞)
-/
instance NNNorm.toENorm : ENorm E where enorm := (‖·‖₊ : E -> Real>=0∞)

/--
lemma `enorm_eq_nnnorm` / 引理 `enorm_eq_nnnorm`

English:
lemma enorm_eq_nnnorm
  given: (x : E)
  statement: ‖x‖ₑ = ‖x‖₊
  proof: rfl

中文:
引理 enorm_eq_nnnorm
  条件: (x : E)
  结论: ‖x‖ₑ = ‖x‖₊
  证明: rfl
-/
lemma enorm_eq_nnnorm (x : E) : ‖x‖ₑ = ‖x‖₊ := rfl

/--
lemma `toNNReal_enorm` / 引理 `toNNReal_enorm`

English:
lemma toNNReal_enorm
  given: (x : E)
  statement: ‖x‖ₑ.toNNReal = ‖x‖₊
  proof: rfl

中文:
引理 toNNReal_enorm
  条件: (x : E)
  结论: ‖x‖ₑ.toNN实数 = ‖x‖₊
  证明: rfl
-/
@[simp] lemma toNNReal_enorm (x : E) : ‖x‖ₑ.toNNReal = ‖x‖₊ := rfl

/--
lemma `coe_le_enorm` / 引理 `coe_le_enorm`

English:
lemma coe_le_enorm
  statement: r <= ‖x‖ₑ ↔ r <= ‖x‖₊
  proof: by simp [enorm]

中文:
引理 coe_le_enorm
  结论: r <= ‖x‖ₑ ↔ r <= ‖x‖₊
  证明: by simp [enorm]
-/
@[simp, norm_cast] lemma coe_le_enorm : r <= ‖x‖ₑ ↔ r <= ‖x‖₊ := by simp [enorm]
/--
lemma `enorm_le_coe` / 引理 `enorm_le_coe`

English:
lemma enorm_le_coe
  statement: ‖x‖ₑ <= r ↔ ‖x‖₊ <= r
  proof: by simp [enorm]

中文:
引理 enorm_le_coe
  结论: ‖x‖ₑ <= r ↔ ‖x‖₊ <= r
  证明: by simp [enorm]
-/
@[simp, norm_cast] lemma enorm_le_coe : ‖x‖ₑ <= r ↔ ‖x‖₊ <= r := by simp [enorm]
/--
lemma `coe_lt_enorm` / 引理 `coe_lt_enorm`

English:
lemma coe_lt_enorm
  statement: r < ‖x‖ₑ ↔ r < ‖x‖₊
  proof: by simp [enorm]

中文:
引理 coe_lt_enorm
  结论: r < ‖x‖ₑ ↔ r < ‖x‖₊
  证明: by simp [enorm]
-/
@[simp, norm_cast] lemma coe_lt_enorm : r < ‖x‖ₑ ↔ r < ‖x‖₊ := by simp [enorm]
/--
lemma `enorm_lt_coe` / 引理 `enorm_lt_coe`

English:
lemma enorm_lt_coe
  statement: ‖x‖ₑ < r ↔ ‖x‖₊ < r
  proof: by simp [enorm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]

中文:
引理 enorm_lt_coe
  结论: ‖x‖ₑ < r ↔ ‖x‖₊ < r
  证明: by simp [enorm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
-/
@[simp, norm_cast] lemma enorm_lt_coe : ‖x‖ₑ < r ↔ ‖x‖₊ < r := by simp [enorm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
/--
lemma `enorm_ne_top` / 引理 `enorm_ne_top`

English:
lemma enorm_ne_top
  statement: ‖x‖ₑ != ∞
  proof: by simp [enorm]

中文:
引理 enorm_ne_top
  结论: ‖x‖ₑ != ∞
  证明: by simp [enorm]

Depends on / 依赖: enorm_lt_top
-/
lemma enorm_ne_top : ‖x‖ₑ != ∞ := by simp [enorm]
/--
lemma `enorm_lt_top` / 引理 `enorm_lt_top`

English:
lemma enorm_lt_top
  statement: ‖x‖ₑ < ∞
  proof: by simp [enorm]

中文:
引理 enorm_lt_top
  结论: ‖x‖ₑ < ∞
  证明: by simp [enorm]
-/
@[simp] lemma enorm_lt_top : ‖x‖ₑ < ∞ := by simp [enorm]

end ENorm

/--
Definition of `ContinuousENorm` / `ContinuousENorm` 的定义

English:
class ContinuousENorm
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ENorm E
  axioms and operations (1):
    - continuous_enorm : Continuous enorm

中文:
类 ContinuousENorm
  参数: (E : 类型) [TopologicalSpace E]
  继承: ENorm E
  公理与运算 (1 个):
    - continuous_enorm : Continuous enorm
-/
class ContinuousENorm (E : Type*) [TopologicalSpace E] extends ENorm E where
  continuous_enorm : Continuous enorm

/--
Definition of `ESeminormedAddMonoid` / `ESeminormedAddMonoid` 的定义

English:
class ESeminormedAddMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ContinuousENorm E, AddMonoid E
  axioms and operations (2):
    - enorm_zero : ‖(0 : E)‖ₑ = 0
    - enorm_add_le : forall x y : E, ‖x + y‖ₑ <= ‖x‖ₑ + ‖y‖ₑ

中文:
类 ESeminormedAddMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ContinuousENorm E, AddMonoid E
  公理与运算 (2 个):
    - enorm_zero : ‖(0 : E)‖ₑ = 0
    - enorm_add_le : 对任意 x y : E, ‖x + y‖ₑ <= ‖x‖ₑ + ‖y‖ₑ
-/
class ESeminormedAddMonoid (E : Type*) [TopologicalSpace E]
    extends ContinuousENorm E, AddMonoid E where
  enorm_zero : ‖(0 : E)‖ₑ = 0
  protected enorm_add_le : forall x y : E, ‖x + y‖ₑ <= ‖x‖ₑ + ‖y‖ₑ

-- see Note [lower instance priority]
attribute [instance 10] ESeminormedAddMonoid.toAddMonoid

/--
Definition of `ENormedAddMonoid` / `ENormedAddMonoid` 的定义

English:
class ENormedAddMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ESeminormedAddMonoid E
  axioms and operations (1):
    - enorm_eq_zero : forall x : E, ‖x‖ₑ = 0 ↔ x = 0

中文:
类 ENormedAddMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ESeminormedAddMonoid E
  公理与运算 (1 个):
    - enorm_eq_zero : 对任意 x : E, ‖x‖ₑ = 0 ↔ x = 0
-/
class ENormedAddMonoid (E : Type*) [TopologicalSpace E]
    extends ESeminormedAddMonoid E where
  enorm_eq_zero : forall x : E, ‖x‖ₑ = 0 ↔ x = 0

/-- An e-seminormed monoid is a monoid endowed with a continuous enorm.
Note that we only ask for the enorm to be a semi-norm: non-trivial elements may have enorm zero. -/
@[to_additive]
/--
Definition of `ESeminormedMonoid` / `ESeminormedMonoid` 的定义

English:
class ESeminormedMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ContinuousENorm E, Monoid E
  axioms and operations (2):
    - enorm_zero : ‖(1 : E)‖ₑ = 0
    - enorm_mul_le : forall x y : E, ‖x * y‖ₑ <= ‖x‖ₑ + ‖y‖ₑ

中文:
类 ESeminormedMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ContinuousENorm E, Monoid E
  公理与运算 (2 个):
    - enorm_zero : ‖(1 : E)‖ₑ = 0
    - enorm_mul_le : 对任意 x y : E, ‖x * y‖ₑ <= ‖x‖ₑ + ‖y‖ₑ
-/
class ESeminormedMonoid (E : Type*) [TopologicalSpace E] extends ContinuousENorm E, Monoid E where
  enorm_zero : ‖(1 : E)‖ₑ = 0
  enorm_mul_le : forall x y : E, ‖x * y‖ₑ <= ‖x‖ₑ + ‖y‖ₑ

-- see Note [lower instance priority]
attribute [instance 10] ESeminormedMonoid.toMonoid

/-- An enormed monoid is a monoid endowed with a continuous enorm,
which is positive definite: in other words, this is an `ESeminormedMonoid` with a positive
definiteness condition added. -/
@[to_additive]
/--
Definition of `ENormedMonoid` / `ENormedMonoid` 的定义

English:
class ENormedMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ESeminormedMonoid E
  axioms and operations (1):
    - enorm_eq_zero : forall x : E, ‖x‖ₑ = 0 ↔ x = 1

中文:
类 ENormedMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ESeminormedMonoid E
  公理与运算 (1 个):
    - enorm_eq_zero : 对任意 x : E, ‖x‖ₑ = 0 ↔ x = 1
-/
class ENormedMonoid (E : Type*) [TopologicalSpace E] extends ESeminormedMonoid E where
  enorm_eq_zero : forall x : E, ‖x‖ₑ = 0 ↔ x = 1

/--
Definition of `ESeminormedAddCommMonoid` / `ESeminormedAddCommMonoid` 的定义

English:
class ESeminormedAddCommMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ESeminormedAddMonoid E, AddCommMonoid E
  (no additional axioms)

中文:
类 ESeminormedAddCommMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ESeminormedAddMonoid E, AddCommMonoid E
  (无附加公理)
-/
class ESeminormedAddCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedAddMonoid E, AddCommMonoid E where

-- see Note [lower instance priority]
attribute [instance 10] ESeminormedAddCommMonoid.toAddCommMonoid

/--
Definition of `ENormedAddCommMonoid` / `ENormedAddCommMonoid` 的定义

English:
class ENormedAddCommMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ESeminormedAddCommMonoid E, ENormedAddMonoid E
  (no additional axioms)

中文:
类 ENormedAddCommMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ESeminormedAddCommMonoid E, ENormedAddMonoid E
  (无附加公理)
-/
class ENormedAddCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedAddCommMonoid E, ENormedAddMonoid E where

/-- An e-seminormed commutative monoid is a commutative monoid endowed with a continuous enorm. -/
@[to_additive]
/--
Definition of `ESeminormedCommMonoid` / `ESeminormedCommMonoid` 的定义

English:
class ESeminormedCommMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ESeminormedMonoid E, CommMonoid E
  (no additional axioms)

中文:
类 ESeminormedCommMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ESeminormedMonoid E, CommMonoid E
  (无附加公理)
-/
class ESeminormedCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedMonoid E, CommMonoid E where

-- see Note [lower instance priority]
attribute [instance 10] ESeminormedCommMonoid.toCommMonoid

/-- An enormed commutative monoid is a commutative monoid endowed with a continuous enorm
which is positive definite. -/
@[to_additive]
/--
Definition of `ENormedCommMonoid` / `ENormedCommMonoid` 的定义

English:
class ENormedCommMonoid
  parameters: (E : Type*) [TopologicalSpace E]
  extends: ESeminormedCommMonoid E, ENormedMonoid E
  (no additional axioms)

中文:
类 ENormedCommMonoid
  参数: (E : 类型) [TopologicalSpace E]
  继承: ESeminormedCommMonoid E, ENormedMonoid E
  (无附加公理)
-/
class ENormedCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedCommMonoid E, ENormedMonoid E where

/--
Definition of `SeminormedAddGroup` / `SeminormedAddGroup` 的定义

English:
class SeminormedAddGroup
  parameters: (E : Type*)
  extends: Norm E, AddGroup E, PseudoMetricSpace E
  axioms and operations (2):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : forall x y, dist x y = ‖-x + y‖  [default: by aesop]

中文:
类 SeminormedAddGroup
  参数: (E : 类型)
  继承: Norm E, AddGroup E, PseudoMetricSpace E
  公理与运算 (2 个):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : 对任意 x y, dist x y = ‖-x + y‖  [默认: by aesop]
-/
class SeminormedAddGroup (E : Type*) extends Norm E, AddGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖-x + y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] SeminormedAddGroup.toAddGroup

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖` defines a
pseudometric space structure. -/
@[to_additive]
/--
Definition of `SeminormedGroup` / `SeminormedGroup` 的定义

English:
class SeminormedGroup
  parameters: (E : Type*)
  extends: Norm E, Group E, PseudoMetricSpace E
  axioms and operations (2):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖  [default: by aesop]

中文:
类 SeminormedGroup
  参数: (E : 类型)
  继承: Norm E, Group E, PseudoMetricSpace E
  公理与运算 (2 个):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : 对任意 x y, dist x y = ‖x⁻¹ * y‖  [默认: by aesop]
-/
class SeminormedGroup (E : Type*) extends Norm E, Group E, PseudoMetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] SeminormedGroup.toGroup

/--
Definition of `NormedAddGroup` / `NormedAddGroup` 的定义

English:
class NormedAddGroup
  parameters: (E : Type*)
  extends: Norm E, AddGroup E, MetricSpace E
  axioms and operations (2):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : forall x y, dist x y = ‖-x + y‖  [default: by aesop]

中文:
类 NormedAddGroup
  参数: (E : 类型)
  继承: Norm E, AddGroup E, MetricSpace E
  公理与运算 (2 个):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : 对任意 x y, dist x y = ‖-x + y‖  [默认: by aesop]
-/
class NormedAddGroup (E : Type*) extends Norm E, AddGroup E, MetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖-x + y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] NormedAddGroup.toAddGroup

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖` defines a metric
space structure. -/
@[to_additive]
/--
Definition of `NormedGroup` / `NormedGroup` 的定义

English:
class NormedGroup
  parameters: (E : Type*)
  extends: Norm E, Group E, MetricSpace E
  axioms and operations (2):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖  [default: by aesop]

中文:
类 NormedGroup
  参数: (E : 类型)
  继承: Norm E, Group E, MetricSpace E
  公理与运算 (2 个):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : 对任意 x y, dist x y = ‖x⁻¹ * y‖  [默认: by aesop]
-/
class NormedGroup (E : Type*) extends Norm E, Group E, MetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] NormedGroup.toGroup

/--
Definition of `SeminormedAddCommGroup` / `SeminormedAddCommGroup` 的定义

English:
class SeminormedAddCommGroup
  parameters: (E : Type*)
  extends: Norm E, AddCommGroup E, 
  axioms and operations (2):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : forall x y, dist x y = ‖-x + y‖  [default: by aesop]

中文:
类 SeminormedAddCommGroup
  参数: (E : 类型)
  继承: Norm E, AddCommGroup E, 
  公理与运算 (2 个):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : 对任意 x y, dist x y = ‖-x + y‖  [默认: by aesop]
-/
class SeminormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E,
  PseudoMetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖-x + y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] SeminormedAddCommGroup.toAddCommGroup

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖`
defines a pseudometric space structure. -/
@[to_additive]
/--
Definition of `SeminormedCommGroup` / `SeminormedCommGroup` 的定义

English:
class SeminormedCommGroup
  parameters: (E : Type*)
  extends: Norm E, CommGroup E, PseudoMetricSpace E
  axioms and operations (2):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖  [default: by aesop]

中文:
类 SeminormedCommGroup
  参数: (E : 类型)
  继承: Norm E, CommGroup E, PseudoMetricSpace E
  公理与运算 (2 个):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : 对任意 x y, dist x y = ‖x⁻¹ * y‖  [默认: by aesop]
-/
class SeminormedCommGroup (E : Type*) extends Norm E, CommGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] SeminormedCommGroup.toCommGroup

/--
Definition of `NormedAddCommGroup` / `NormedAddCommGroup` 的定义

English:
class NormedAddCommGroup
  parameters: (E : Type*)
  extends: Norm E, AddCommGroup E, MetricSpace E
  axioms and operations (2):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : forall x y, dist x y = ‖-x + y‖  [default: by aesop]

中文:
类 NormedAddCommGroup
  参数: (E : 类型)
  继承: Norm E, AddCommGroup E, MetricSpace E
  公理与运算 (2 个):
    - dist : = fun x y => ‖-x + y‖
    - dist_eq : 对任意 x y, dist x y = ‖-x + y‖  [默认: by aesop]
-/
class NormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E, MetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖-x + y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] NormedAddCommGroup.toAddCommGroup

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖` defines a metric
space structure. -/
@[to_additive]
/--
Definition of `NormedCommGroup` / `NormedCommGroup` 的定义

English:
class NormedCommGroup
  parameters: (E : Type*)
  extends: Norm E, CommGroup E, MetricSpace E
  axioms and operations (2):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖  [default: by aesop]

中文:
类 NormedCommGroup
  参数: (E : 类型)
  继承: Norm E, CommGroup E, MetricSpace E
  公理与运算 (2 个):
    - dist : = fun x y => ‖x⁻¹ * y‖
    - dist_eq : 对任意 x y, dist x y = ‖x⁻¹ * y‖  [默认: by aesop]
-/
class NormedCommGroup (E : Type*) extends Norm E, CommGroup E, MetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : forall x y, dist x y = ‖x⁻¹ * y‖ := by aesop

-- see Note [lower instance priority]
attribute [instance 10] NormedCommGroup.toCommGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedGroup.toSeminormedGroup [NormedGroup E] : SeminormedGroup E :=
  { ‹NormedGroup E› with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toSeminormedCommGroup [NormedCommGroup E] :
    SeminormedCommGroup E :=
  { ‹NormedCommGroup E› with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toSeminormedGroup [SeminormedCommGroup E] :
    SeminormedGroup E :=
  { ‹SeminormedCommGroup E› with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toNormedGroup [NormedCommGroup E] : NormedGroup E :=
  { ‹NormedCommGroup E› with }

-- See note [reducible non-instances]
/-- Construct a `NormedGroup` from a `SeminormedGroup` satisfying `∀ x, ‖x‖ = 0 → x = 1`. This
avoids having to go back to the `(Pseudo)MetricSpace` level when declaring a `NormedGroup`
instance as a special case of a more general `SeminormedGroup` instance. -/
@[to_additive /-- Construct a `NormedAddGroup` from a `SeminormedAddGroup`
satisfying `∀ x, ‖x‖ = 0 → x = 0`. This avoids having to go back to the `(Pseudo)MetricSpace`
level when declaring a `NormedAddGroup` instance as a special case of a more general
`SeminormedAddGroup` instance. -/]
/--
Definition of `NormedGroup.ofSeparation` / `NormedGroup.ofSeparation` 的定义

English:
abbreviation NormedGroup.ofSeparation
  signature: [SeminormedGroup E] (h : forall x : E, ‖x‖ = 0 -> x = 1)
  body: ‹SeminormedGroup E›.dist_eq
  toMetricSpace :=
    { eq_of_dist_eq_zero := fun hxy =>
inv_mul_eq_one.1 h _ (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy }

中文:
缩写 NormedGroup.ofSeparation
  签名: [SeminormedGroup E] (h : 对任意 x : E, ‖x‖ = 0 -> x = 1)
  定义体: ‹SeminormedGroup E›.dist_eq
  toMetricSpace :=
    { eq_of_dist_eq_zero := fun hxy =>
inv_mul_eq_one.1 h _ (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy }

Depends on / 依赖: SeminormedGroup, dist_eq
-/
abbrev NormedGroup.ofSeparation [SeminormedGroup E] (h : forall x : E, ‖x‖ = 0 -> x = 1) :
    NormedGroup E where
  dist_eq := ‹SeminormedGroup E›.dist_eq
  toMetricSpace :=
    { eq_of_dist_eq_zero := fun hxy =>
inv_mul_eq_one.1 h _ (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy }

-- See note [reducible non-instances]
/-- Construct a `NormedCommGroup` from a `SeminormedCommGroup` satisfying
`∀ x, ‖x‖ = 0 → x = 1`. This avoids having to go back to the `(Pseudo)MetricSpace` level when
declaring a `NormedCommGroup` instance as a special case of a more general `SeminormedCommGroup`
instance. -/
@[to_additive /-- Construct a `NormedAddCommGroup` from a
`SeminormedAddCommGroup` satisfying `∀ x, ‖x‖ = 0 → x = 0`. This avoids having to go back to the
`(Pseudo)MetricSpace` level when declaring a `NormedAddCommGroup` instance as a special case
of a more general `SeminormedAddCommGroup` instance. -/]
/--
Definition of `NormedCommGroup.ofSeparation` / `NormedCommGroup.ofSeparation` 的定义

English:
abbreviation NormedCommGroup.ofSeparation
  signature: [SeminormedCommGroup E] (h : forall x : E, ‖x‖ = 0 -> x = 1)
  body: { ‹SeminormedCommGroup E›, NormedGroup.ofSeparation h with }

中文:
缩写 NormedCommGroup.ofSeparation
  签名: [SeminormedCommGroup E] (h : 对任意 x : E, ‖x‖ = 0 -> x = 1)
  定义体: { ‹SeminormedCommGroup E›, NormedGroup.ofSeparation h with }

Depends on / 依赖: NormedGroup, NormedGroup.ofSeparation, SeminormedCommGroup, ofSeparation
-/
abbrev NormedCommGroup.ofSeparation [SeminormedCommGroup E] (h : forall x : E, ‖x‖ = 0 -> x = 1) :
    NormedCommGroup E :=
  { ‹SeminormedCommGroup E›, NormedGroup.ofSeparation h with }

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant distance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant distance. -/]
/--
Definition of `SeminormedGroup.ofMulDist` / `SeminormedGroup.ofMulDist` 的定义

English:
abbreviation SeminormedGroup.ofMulDist
  signature: [Norm E] [Group E] [PseudoMetricSpace E]
  body: by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x

中文:
缩写 SeminormedGroup.ofMulDist
  签名: [Norm E] [Group E] [PseudoMetricSpace E]
  定义体: by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel, le_antisymm, mul_assoc, mul_inv_cancel, mul_one, one_mul
-/
abbrev SeminormedGroup.ofMulDist [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : forall x : E, ‖x‖ = dist 1 x) (h₂ : forall x y z : E, dist x y <= dist (z * x) (z * y)) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
/--
Definition of `SeminormedGroup.ofMulDist'` / `SeminormedGroup.ofMulDist'` 的定义

English:
abbreviation SeminormedGroup.ofMulDist'
  signature: [Norm E] [Group E] [PseudoMetricSpace E]
  body: by
    rw [h₁]; apply le_antisymm
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹

中文:
缩写 SeminormedGroup.ofMulDist'
  签名: [Norm E] [Group E] [PseudoMetricSpace E]
  定义体: by
    rw [h₁]; apply le_antisymm
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel, le_antisymm, mul_assoc, mul_inv_cancel, mul_one, one_mul
-/
abbrev SeminormedGroup.ofMulDist' [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : forall x : E, ‖x‖ = dist 1 x) (h₂ : forall x y z : E, dist (z * x) (z * y) <= dist x y) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
/--
Definition of `SeminormedCommGroup.ofMulDist` / `SeminormedCommGroup.ofMulDist` 的定义

English:
abbreviation SeminormedCommGroup.ofMulDist
  signature: [Norm E] [CommGroup E] [PseudoMetricSpace E]
  body: { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

中文:
缩写 SeminormedCommGroup.ofMulDist
  签名: [Norm E] [CommGroup E] [PseudoMetricSpace E]
  定义体: { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

Depends on / 依赖: SeminormedGroup, SeminormedGroup.ofMulDist, mul_comm, ofMulDist
-/
abbrev SeminormedCommGroup.ofMulDist [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : forall x : E, ‖x‖ = dist 1 x) (h₂ : forall x y z : E, dist x y <= dist (z * x) (z * y)) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
/--
Definition of `SeminormedCommGroup.ofMulDist'` / `SeminormedCommGroup.ofMulDist'` 的定义

English:
abbreviation SeminormedCommGroup.ofMulDist'
  signature: [Norm E] [CommGroup E] [PseudoMetricSpace E]
  body: { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

中文:
缩写 SeminormedCommGroup.ofMulDist'
  签名: [Norm E] [CommGroup E] [PseudoMetricSpace E]
  定义体: { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

Depends on / 依赖: SeminormedGroup, SeminormedGroup.ofMulDist, mul_comm, ofMulDist
-/
abbrev SeminormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : forall x : E, ‖x‖ = dist 1 x) (h₂ : forall x y z : E, dist (z * x) (z * y) <= dist x y) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant distance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant distance. -/]
/--
Definition of `NormedGroup.ofMulDist` / `NormedGroup.ofMulDist` 的定义

English:
abbreviation NormedGroup.ofMulDist
  signature: [Norm E] [Group E] [MetricSpace E] (h₁ : forall x : E, ‖x‖ = dist 1 x)
  body: { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
缩写 NormedGroup.ofMulDist
  签名: [Norm E] [Group E] [MetricSpace E] (h₁ : 对任意 x : E, ‖x‖ = dist 1 x)
  定义体: { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: SeminormedGroup, SeminormedGroup.ofMulDist, eq_of_dist_eq_zero, ofMulDist
-/
abbrev NormedGroup.ofMulDist [Norm E] [Group E] [MetricSpace E] (h₁ : forall x : E, ‖x‖ = dist 1 x)
    (h₂ : forall x y z : E, dist x y <= dist (z * x) (z * y)) : NormedGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant pseudodistance. -/]
/--
Definition of `NormedGroup.ofMulDist'` / `NormedGroup.ofMulDist'` 的定义

English:
abbreviation NormedGroup.ofMulDist'
  signature: [Norm E] [Group E] [MetricSpace E] (h₁ : forall x : E, ‖x‖ = dist 1 x)
  body: { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
缩写 NormedGroup.ofMulDist'
  签名: [Norm E] [Group E] [MetricSpace E] (h₁ : 对任意 x : E, ‖x‖ = dist 1 x)
  定义体: { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: SeminormedGroup, SeminormedGroup.ofMulDist, eq_of_dist_eq_zero, ofMulDist
-/
abbrev NormedGroup.ofMulDist' [Norm E] [Group E] [MetricSpace E] (h₁ : forall x : E, ‖x‖ = dist 1 x)
    (h₂ : forall x y z : E, dist (z * x) (z * y) <= dist x y) : NormedGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
/-- Construct a normed group from a translation-invariant pseudodistance. -/]
/--
Definition of `NormedCommGroup.ofMulDist` / `NormedCommGroup.ofMulDist` 的定义

English:
abbreviation NormedCommGroup.ofMulDist
  signature: [Norm E] [CommGroup E] [MetricSpace E]
  body: { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

中文:
缩写 NormedCommGroup.ofMulDist
  签名: [Norm E] [CommGroup E] [MetricSpace E]
  定义体: { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

Depends on / 依赖: NormedGroup, NormedGroup.ofMulDist, mul_comm, ofMulDist
-/
abbrev NormedCommGroup.ofMulDist [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : forall x : E, ‖x‖ = dist 1 x) (h₂ : forall x y z : E, dist x y <= dist (z * x) (z * y)) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant pseudodistance. -/]
/--
Definition of `NormedCommGroup.ofMulDist'` / `NormedCommGroup.ofMulDist'` 的定义

English:
abbreviation NormedCommGroup.ofMulDist'
  signature: [Norm E] [CommGroup E] [MetricSpace E]
  body: { NormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

中文:
缩写 NormedCommGroup.ofMulDist'
  签名: [Norm E] [CommGroup E] [MetricSpace E]
  定义体: { NormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

Depends on / 依赖: NormedGroup, NormedGroup.ofMulDist, mul_comm, ofMulDist
-/
abbrev NormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : forall x : E, ‖x‖ = dist 1 x) (h₂ : forall x y z : E, dist (z * x) (z * y) <= dist x y) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive
  /-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`). -/]
/--
Definition of `GroupSeminorm.toSeminormedGroup` / `GroupSeminorm.toSeminormedGroup` 的定义

English:
abbreviation GroupSeminorm.toSeminormedGroup
  signature: [Group E] (f : GroupSeminorm E)
  body: f (x⁻¹ * y)
  norm := f
  dist_eq _ _ := rfl
  dist_self x := by simp only [inv_mul_cancel, map_one_eq_zero]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group
  dist_comm x y := by convert! map_inv_eq_map f (y⁻¹ * x) using 2; group

中文:
缩写 GroupSeminorm.toSeminormedGroup
  签名: [Group E] (f : GroupSeminorm E)
  定义体: f (x⁻¹ * y)
  norm := f
  dist_eq _ _ := rfl
  dist_self x := by simp only [inv_mul_cancel, map_one_eq_zero]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group
  dist_comm x y := by convert! map_inv_eq_map f (y⁻¹ * x) using 2; group
-/
abbrev GroupSeminorm.toSeminormedGroup [Group E] (f : GroupSeminorm E) : SeminormedGroup E where
  dist x y := f (x⁻¹ * y)
  norm := f
  dist_eq _ _ := rfl
  dist_self x := by simp only [inv_mul_cancel, map_one_eq_zero]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group
  dist_comm x y := by convert! map_inv_eq_map f (y⁻¹ * x) using 2; group

-- See note [reducible non-instances]
/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive
  /-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`). -/]
/--
Definition of `GroupSeminorm.toSeminormedCommGroup` / `GroupSeminorm.toSeminormedCommGroup` 的定义

English:
abbreviation GroupSeminorm.toSeminormedCommGroup
  signature: [CommGroup E] (f : GroupSeminorm E)
  body: { f.toSeminormedGroup with
    mul_comm := mul_comm }

中文:
缩写 GroupSeminorm.toSeminormedCommGroup
  签名: [CommGroup E] (f : GroupSeminorm E)
  定义体: { f.toSeminormedGroup with
    mul_comm := mul_comm }

Depends on / 依赖: f.toSeminormedGroup, mul_comm, toSeminormedGroup
-/
abbrev GroupSeminorm.toSeminormedCommGroup [CommGroup E] (f : GroupSeminorm E) :
    SeminormedCommGroup E :=
  { f.toSeminormedGroup with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive
  /-- Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`). -/]
/--
Definition of `GroupNorm.toNormedGroup` / `GroupNorm.toNormedGroup` 的定义

English:
abbreviation GroupNorm.toNormedGroup
  signature: [Group E] (f : GroupNorm E)
  body: { f.toGroupSeminorm.toSeminormedGroup with
eq_of_dist_eq_zero := fun h => inv_mul_eq_one.1 eq_one_of_map_eq_zero f h }

中文:
缩写 GroupNorm.toNormedGroup
  签名: [Group E] (f : GroupNorm E)
  定义体: { f.toGroupSeminorm.toSeminormedGroup with
eq_of_dist_eq_zero := fun h => inv_mul_eq_one.1 eq_one_of_map_eq_zero f h }

Depends on / 依赖: eq_of_dist_eq_zero, eq_one_of_map_eq_zero, f.toGroupSeminorm.toSeminormedGroup, inv_mul_eq_one, toGroupSeminorm, toSeminormedGroup
-/
abbrev GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E :=
  { f.toGroupSeminorm.toSeminormedGroup with
eq_of_dist_eq_zero := fun h => inv_mul_eq_one.1 eq_one_of_map_eq_zero f h }

-- See note [reducible non-instances]
/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive
  /-- Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`). -/]
/--
Definition of `GroupNorm.toNormedCommGroup` / `GroupNorm.toNormedCommGroup` 的定义

English:
abbreviation GroupNorm.toNormedCommGroup
  signature: [CommGroup E] (f : GroupNorm E)
  body: { f.toNormedGroup with
    mul_comm := mul_comm }

中文:
缩写 GroupNorm.toNormedCommGroup
  签名: [CommGroup E] (f : GroupNorm E)
  定义体: { f.toNormedGroup with
    mul_comm := mul_comm }

Depends on / 依赖: f.toNormedGroup, mul_comm, toNormedGroup
-/
abbrev GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E :=
  { f.toNormedGroup with
    mul_comm := mul_comm }
