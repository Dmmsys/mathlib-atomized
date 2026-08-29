/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Normed division rings and fields

In this file we define normed fields, and (more generally) normed division rings. We also prove
some theorems about these definitions.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `norm_eq_one_iff_ne_zero_of_discrete`

Methods for constructing a normed field instance from a given real absolute value on a field are
given in:
* AbsoluteValue.toNormedField
-/

@[expose] public section

-- Guard against import creep.
assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg
  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real
  RestrictScalars

variable {G α β ι : Type*}

open Filter
open scoped Topology NNReal ENNReal

/--
Definition of `NormedDivisionRing` / `NormedDivisionRing` 的定义

English:
class NormedDivisionRing
  parameters: (α : Type*)
  extends: Norm α, DivisionRing α, MetricSpace α
  axioms and operations (2):
    - dist_eq : forall x y, dist x y = norm (-x + y)
    - norm_mul : forall a b, norm (a * b) = norm a * norm b

中文:
类 NormedDivision环
  参数: (α : 类型)
  继承: 范数 α, 除环 α, 度量空间 α
  公理与运算 (2 个):
    - dist_eq : 对任意 x y, dist x y = norm (-x + y)
    - norm_mul : 对任意 a b, norm (a * b) = norm a * norm b
-/
class NormedDivisionRing (α : Type*) extends Norm α, DivisionRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : forall x y, dist x y = norm (-x + y)
  /-- The norm is multiplicative. -/
  protected norm_mul : forall a b, norm (a * b) = norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NormedDivisionRing.toDivisionRing

-- see Note [lower instance priority]
/-- A normed division ring is a normed ring. -/
instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] :
    NormedRing α :=
  { β with norm_mul_le a b := (NormedDivisionRing.norm_mul a b).le }

-- see Note [lower instance priority]
/-- The norm on a normed division ring is strictly multiplicative. -/
instance (priority := 100) NormedDivisionRing.toNormMulClass [NormedDivisionRing α] :
    NormMulClass α where
  norm_mul := NormedDivisionRing.norm_mul

section NormedDivisionRing

variable [NormedDivisionRing α] {a b : α}

instance (priority := 900) NormedDivisionRing.to_normOneClass : NormOneClass α :=
⟨mul_left_cancel₀ (mt norm_eq_zero.1 (one_ne_zero' α)) by rw [← norm_mul, mul_one, mul_one]⟩

@[simp]
/--
theorem `norm_div` / 定理 `norm_div`

English:
theorem norm_div
  given: (a b : α)
  statement: ‖a / b‖ = ‖a‖ / ‖b‖
  proof: map_div₀ (normHom : α ->*₀ Real) a b

@[simp]

中文:
定理 norm_div
  条件: (a b : α)
  结论: ‖a / b‖ = ‖a‖ / ‖b‖
  证明: map_div₀ (normHom : α ->*₀ Real) a b

@[simp]

Depends on / 依赖: normHom
-/
theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
  map_div₀ (normHom : α ->*₀ Real) a b

@[simp]
/--
theorem `nnnorm_div` / 定理 `nnnorm_div`

English:
theorem nnnorm_div
  given: (a b : α)
  statement: ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊
  proof: map_div₀ (nnnormHom : α ->*₀ Real>=0) a b

@[simp]

中文:
定理 nnnorm_div
  条件: (a b : α)
  结论: ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊
  证明: map_div₀ (nnnormHom : α ->*₀ Real>=0) a b

@[simp]

Depends on / 依赖: nnnormHom
-/
theorem nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊ :=
  map_div₀ (nnnormHom : α ->*₀ Real>=0) a b

@[simp]
/--
theorem `norm_inv` / 定理 `norm_inv`

English:
theorem norm_inv
  given: (a : α)
  statement: ‖a⁻¹‖ = ‖a‖⁻¹
  proof: map_inv₀ (normHom : α ->*₀ Real) a

@[simp]

中文:
定理 norm_inv
  条件: (a : α)
  结论: ‖a⁻¹‖ = ‖a‖⁻¹
  证明: map_inv₀ (normHom : α ->*₀ Real) a

@[simp]

Depends on / 依赖: normHom
-/
theorem norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹ :=
  map_inv₀ (normHom : α ->*₀ Real) a

@[simp]
/--
theorem `nnnorm_inv` / 定理 `nnnorm_inv`

English:
theorem nnnorm_inv
  given: (a : α)
  statement: ‖a⁻¹‖₊ = ‖a‖₊⁻¹
  proof: NNReal.eq by simp

@[simp]

中文:
定理 nnnorm_inv
  条件: (a : α)
  结论: ‖a⁻¹‖₊ = ‖a‖₊⁻¹
  证明: NNReal.eq by simp

@[simp]

Depends on / 依赖: NNReal, NNReal.eq
-/
theorem nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹ :=
NNReal.eq by simp

@[simp]
/--
lemma `enorm_inv` / 引理 `enorm_inv`

English:
lemma enorm_inv
  given: {a : α} (ha : a != 0)
  statement: ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
  proof: by simp [enorm, ENNReal.coe_inv, ha]

@[simp]

中文:
引理 enorm_inv
  条件: {a : α} (ha : a != 0)
  结论: ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
  证明: by simp [enorm, ENNReal.coe_inv, ha]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_inv, coe_inv
-/
lemma enorm_inv {a : α} (ha : a != 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹ := by simp [enorm, ENNReal.coe_inv, ha]

@[simp]
/--
theorem `norm_zpow` / 定理 `norm_zpow`

English:
theorem norm_zpow
  statement: forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
  proof: map_zpow₀ (normHom : α ->*₀ Real)

@[simp]

中文:
定理 norm_zpow
  结论: 对任意 (a : α) (n : 整数), ‖a ^ n‖ = ‖a‖ ^ n
  证明: map_zpow₀ (normHom : α ->*₀ Real)

@[simp]

Depends on / 依赖: normHom
-/
theorem norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n :=
  map_zpow₀ (normHom : α ->*₀ Real)

@[simp]
/--
theorem `nnnorm_zpow` / 定理 `nnnorm_zpow`

English:
theorem nnnorm_zpow
  statement: forall (a : α) (n : Int), ‖a ^ n‖₊ = ‖a‖₊ ^ n
  proof: map_zpow₀ (nnnormHom : α ->*₀ Real>=0)

中文:
定理 nnnorm_zpow
  结论: 对任意 (a : α) (n : 整数), ‖a ^ n‖₊ = ‖a‖₊ ^ n
  证明: map_zpow₀ (nnnormHom : α ->*₀ Real>=0)

Depends on / 依赖: nnnormHom
-/
theorem nnnorm_zpow : forall (a : α) (n : Int), ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  map_zpow₀ (nnnormHom : α ->*₀ Real>=0)

/--
theorem `dist_inv_inv₀` / 定理 `dist_inv_inv₀`

English:
theorem dist_inv_inv₀
  given: {z w : α} (hz : z != 0) (hw : w != 0)
  proof: by
  rw [dist_eq_norm]; rw [inv_sub_inv' hz hw]; rw [norm_mul]; rw [norm_mul]; rw [norm_inv]; rw [norm_inv]; rw [mul_comm ‖z‖⁻¹]; rw [mul_assoc]; rw [dist_eq_norm']; rw [div_eq_mul_inv]; rw [mul_inv]

中文:
定理 dist_inv_inv₀
  条件: {z w : α} (hz : z != 0) (hw : w != 0)
  证明: by
  rw [dist_eq_norm]; rw [inv_sub_inv' hz hw]; rw [norm_mul]; rw [norm_mul]; rw [norm_inv]; rw [norm_inv]; rw [mul_comm ‖z‖⁻¹]; rw [mul_assoc]; rw [dist_eq_norm']; rw [div_eq_mul_inv]; rw [mul_inv]

Depends on / 依赖: dist_eq_norm, div_eq_mul_inv, inv_sub_inv, mul_assoc, mul_comm, mul_inv, norm_inv, norm_mul
-/
theorem dist_inv_inv₀ {z w : α} (hz : z != 0) (hw : w != 0) :
    dist z⁻¹ w⁻¹ = dist z w / (‖z‖ * ‖w‖) := by
  rw [dist_eq_norm]; rw [inv_sub_inv' hz hw]; rw [norm_mul]; rw [norm_mul]; rw [norm_inv]; rw [norm_inv]; rw [mul_comm ‖z‖⁻¹]; rw [mul_assoc]; rw [dist_eq_norm']; rw [div_eq_mul_inv]; rw [mul_inv]

/--
theorem `nndist_inv_inv₀` / 定理 `nndist_inv_inv₀`

English:
theorem nndist_inv_inv₀
  given: {z w : α} (hz : z != 0) (hw : w != 0)
  proof: NNReal.eq dist_inv_inv₀ hz hw

中文:
定理 nndist_inv_inv₀
  条件: {z w : α} (hz : z != 0) (hw : w != 0)
  证明: NNReal.eq dist_inv_inv₀ hz hw

Depends on / 依赖: NNReal, NNReal.eq
-/
theorem nndist_inv_inv₀ {z w : α} (hz : z != 0) (hw : w != 0) :
    nndist z⁻¹ w⁻¹ = nndist z w / (‖z‖₊ * ‖w‖₊) :=
NNReal.eq dist_inv_inv₀ hz hw

/--
lemma `norm_commutator_sub_one_le` / 引理 `norm_commutator_sub_one_le`

English:
lemma norm_commutator_sub_one_le
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  simpa using norm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

中文:
引理 norm_commutator_sub_one_le
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  simpa using norm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

Depends on / 依赖: norm_commutator_units_sub_one_le
-/
lemma norm_commutator_sub_one_le (ha : a != 0) (hb : b != 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖ <= 2 * ‖a‖⁻¹ * ‖b‖⁻¹ * ‖a - 1‖ * ‖b - 1‖ := by
  simpa using norm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

/--
lemma `nnnorm_commutator_sub_one_le` / 引理 `nnnorm_commutator_sub_one_le`

English:
lemma nnnorm_commutator_sub_one_le
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  simpa using nnnorm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

中文:
引理 nnnorm_commutator_sub_one_le
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  simpa using nnnorm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

Depends on / 依赖: nnnorm_commutator_units_sub_one_le
-/
lemma nnnorm_commutator_sub_one_le (ha : a != 0) (hb : b != 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖₊ <= 2 * ‖a‖₊⁻¹ * ‖b‖₊⁻¹ * ‖a - 1‖₊ * ‖b - 1‖₊ := by
  simpa using nnnorm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

namespace NormedDivisionRing

section Discrete

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [DiscreteTopology 𝕜]

/--
lemma `norm_eq_one_iff_ne_zero_of_discrete` / 引理 `norm_eq_one_iff_ne_zero_of_discrete`

English:
lemma norm_eq_one_iff_ne_zero_of_discrete
  given: {x : 𝕜}
  statement: ‖x‖ = 1 ↔ x != 0
  proof: by
  constructor <;> intro hx
  · contrapose! hx
    simp [hx]
  · have : IsOpen {(0 : 𝕜)} := isOpen_discrete {0}
    simp_rw [Metric.isOpen_singleton_iff, dist_eq_norm, sub_zero] at this
    obtain ⟨ε, εpos, h'⟩ := this
    wlog! h : ‖x‖ < 1 generalizing 𝕜 with H
    · rcases h.eq_or_lt with h | h
      · rw [h]
      replace h := norm_inv x ▸ inv_lt_one_of_one_lt₀ h
      rw [← inv_inj]; rw [inv_one]; rw [← norm_inv]
      exact H (by simpa) h' h
    obtain ⟨k, hk⟩ : exists k : Nat, ‖x‖ ^ k < ε := exists_pow_lt_of_lt_one εpos h
    rw [← norm_pow] at hk
    specialize h' _ hk
    simp [hx] at h'

@[simp]

中文:
引理 norm_eq_one_iff_ne_zero_of_discrete
  条件: {x : 𝕜}
  结论: ‖x‖ = 1 ↔ x != 0
  证明: by
  constructor <;> intro hx
  · contrapose! hx
    simp [hx]
  · have : IsOpen {(0 : 𝕜)} := isOpen_discrete {0}
    simp_rw [Metric.isOpen_singleton_iff, dist_eq_norm, sub_zero] at this
    obtain ⟨ε, εpos, h'⟩ := this
    wlog! h : ‖x‖ < 1 generalizing 𝕜 with H
    · rcases h.eq_or_lt with h | h
      · rw [h]
      replace h := norm_inv x ▸ inv_lt_one_of_one_lt₀ h
      rw [← inv_inj]; rw [inv_one]; rw [← norm_inv]
      exact H (by simpa) h' h
    obtain ⟨k, hk⟩ : exists k : Nat, ‖x‖ ^ k < ε := exists_pow_lt_of_lt_one εpos h
    rw [← norm_pow] at hk
    specialize h' _ hk
    simp [hx] at h'

@[simp]

Depends on / 依赖: IsOpen, Metric, Metric.isOpen_singleton_iff, contrapose, dist_eq_norm, eq_or_lt, exists_pow_lt_of_lt_one, generalizing, h.eq_or_lt, inv_inj, inv_one, isOpen_discrete, isOpen_singleton_iff, norm_inv, norm_pow, replace, simp_rw, sub_zero
-/
lemma norm_eq_one_iff_ne_zero_of_discrete {x : 𝕜} : ‖x‖ = 1 ↔ x != 0 := by
  constructor <;> intro hx
  · contrapose! hx
    simp [hx]
  · have : IsOpen {(0 : 𝕜)} := isOpen_discrete {0}
    simp_rw [Metric.isOpen_singleton_iff, dist_eq_norm, sub_zero] at this
    obtain ⟨ε, εpos, h'⟩ := this
    wlog! h : ‖x‖ < 1 generalizing 𝕜 with H
    · rcases h.eq_or_lt with h | h
      · rw [h]
      replace h := norm_inv x ▸ inv_lt_one_of_one_lt₀ h
      rw [← inv_inj]; rw [inv_one]; rw [← norm_inv]
      exact H (by simpa) h' h
    obtain ⟨k, hk⟩ : exists k : Nat, ‖x‖ ^ k < ε := exists_pow_lt_of_lt_one εpos h
    rw [← norm_pow] at hk
    specialize h' _ hk
    simp [hx] at h'

@[simp]
/--
lemma `norm_le_one_of_discrete` / 引理 `norm_le_one_of_discrete`

English:
lemma norm_le_one_of_discrete
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [norm_eq_one_iff_ne_zero_of_discrete.mpr hx]

中文:
引理 norm_le_one_of_discrete
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [norm_eq_one_iff_ne_zero_of_discrete.mpr hx]

Depends on / 依赖: eq_or_ne, norm_eq_one_iff_ne_zero_of_discrete, norm_eq_one_iff_ne_zero_of_discrete.mpr
-/
lemma norm_le_one_of_discrete
    (x : 𝕜) : ‖x‖ <= 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [norm_eq_one_iff_ne_zero_of_discrete.mpr hx]

/--
lemma `unitClosedBall_eq_univ_of_discrete` / 引理 `unitClosedBall_eq_univ_of_discrete`

English:
lemma unitClosedBall_eq_univ_of_discrete
  statement: (Metric.closedBall 0 1 : Set 𝕜) = Set.univ
  proof: by
  ext
  simp

中文:
引理 unitClosedBall_eq_univ_of_discrete
  结论: (Metric.closedBall 0 1 : 集合 𝕜) = 集合.univ
  证明: by
  ext
  simp
-/
lemma unitClosedBall_eq_univ_of_discrete : (Metric.closedBall 0 1 : Set 𝕜) = Set.univ := by
  ext
  simp

end Discrete

end NormedDivisionRing

end NormedDivisionRing

/--
Definition of `NormedField` / `NormedField` 的定义

English:
class NormedField
  parameters: (α : Type*)
  extends: Norm α, Field α, MetricSpace α
  axioms and operations (2):
    - dist_eq : forall x y, dist x y = norm (-x + y)
    - norm_mul : forall a b, norm (a * b) = norm a * norm b

中文:
类 赋范域
  参数: (α : 类型)
  继承: 范数 α, 域 α, 度量空间 α
  公理与运算 (2 个):
    - dist_eq : 对任意 x y, dist x y = norm (-x + y)
    - norm_mul : 对任意 a b, norm (a * b) = norm a * norm b
-/
class NormedField (α : Type*) extends Norm α, Field α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : forall x y, dist x y = norm (-x + y)
  /-- The norm is multiplicative. -/
  protected norm_mul : forall a b, norm (a * b) = norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NormedField.toField

/--
Definition of `NontriviallyNormedField` / `NontriviallyNormedField` 的定义

English:
class NontriviallyNormedField
  parameters: (α : Type*)
  extends: NormedField α
  axioms and operations (1):
    - non_trivial : exists x : α, 1 < ‖x‖

中文:
类 NontriviallyNormedField
  参数: (α : 类型)
  继承: 赋范域 α
  公理与运算 (1 个):
    - non_trivial : 存在 x : α, 1 < ‖x‖
-/
class NontriviallyNormedField (α : Type*) extends NormedField α where
  /-- The norm attains a value exceeding 1. -/
  non_trivial : exists x : α, 1 < ‖x‖

/--
Definition of `DenselyNormedField` / `DenselyNormedField` 的定义

English:
class DenselyNormedField
  parameters: (α : Type*)
  extends: NormedField α
  axioms and operations (1):
    - lt_norm_lt : forall x y : Real, 0 <= x -> x < y -> exists a : α, x < ‖a‖ ∧ ‖a‖ < y

中文:
类 DenselyNormedField
  参数: (α : 类型)
  继承: 赋范域 α
  公理与运算 (1 个):
    - lt_norm_lt : 对任意 x y : 实数, 0 <= x -> x < y -> 存在 a : α, x < ‖a‖ ∧ ‖a‖ < y
-/
class DenselyNormedField (α : Type*) extends NormedField α where
  /-- The range of the norm is dense in the collection of nonnegative real numbers. -/
  lt_norm_lt : forall x y : Real, 0 <= x -> x < y -> exists a : α, x < ‖a‖ ∧ ‖a‖ < y

section NormedField

/-- A densely normed field is always a nontrivially normed field.
See note [lower instance priority]. -/
instance (priority := 100) DenselyNormedField.toNontriviallyNormedField [DenselyNormedField α] :
    NontriviallyNormedField α where
  non_trivial :=
    let ⟨a, h, _⟩ := DenselyNormedField.lt_norm_lt 1 2 zero_le_one one_lt_two
    ⟨a, h⟩

variable [NormedField α]

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul_le a b := (norm_mul a b).le }

end NormedField

namespace NormedField

section Nontrivially

variable (α) [NontriviallyNormedField α]

/--
theorem `exists_one_lt_norm` / 定理 `exists_one_lt_norm`

English:
theorem exists_one_lt_norm
  statement: exists x : α, 1 < ‖x‖
  proof: ‹NontriviallyNormedField α›.non_trivial

中文:
定理 存在_one_lt_norm
  结论: 存在 x : α, 1 < ‖x‖
  证明: ‹NontriviallyNormedField α›.non_trivial

Depends on / 依赖: NontriviallyNormedField, non_trivial
-/
theorem exists_one_lt_norm : exists x : α, 1 < ‖x‖ :=
  ‹NontriviallyNormedField α›.non_trivial

/--
theorem `exists_one_lt_nnnorm` / 定理 `exists_one_lt_nnnorm`

English:
theorem exists_one_lt_nnnorm
  statement: exists x : α, 1 < ‖x‖₊
  proof: exists_one_lt_norm α

中文:
定理 存在_one_lt_nnnorm
  结论: 存在 x : α, 1 < ‖x‖₊
  证明: exists_one_lt_norm α

Depends on / 依赖: exists_one_lt_norm
-/
theorem exists_one_lt_nnnorm : exists x : α, 1 < ‖x‖₊ := exists_one_lt_norm α

/--
theorem `exists_one_lt_enorm` / 定理 `exists_one_lt_enorm`

English:
theorem exists_one_lt_enorm
  statement: exists x : α, 1 < ‖x‖ₑ
  proof: .imp fun _ => ENNReal.coe_lt_coe.mpr exists_one_lt_nnnorm α

中文:
定理 存在_one_lt_enorm
  结论: 存在 x : α, 1 < ‖x‖ₑ
  证明: .imp fun _ => ENNReal.coe_lt_coe.mpr exists_one_lt_nnnorm α

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe.mpr, coe_lt_coe, exists_one_lt_nnnorm
-/
theorem exists_one_lt_enorm : exists x : α, 1 < ‖x‖ₑ :=
.imp fun _ => ENNReal.coe_lt_coe.mpr exists_one_lt_nnnorm α

/--
theorem `exists_lt_norm` / 定理 `exists_lt_norm`

English:
theorem exists_lt_norm
  given: (r : Real)
  statement: exists x : α, r < ‖x‖
  proof: let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩

中文:
定理 存在_lt_norm
  条件: (r : 实数)
  结论: 存在 x : α, r < ‖x‖
  证明: let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩

Depends on / 依赖: exists_one_lt_norm, norm_pow, pow_unbounded_of_one_lt
-/
theorem exists_lt_norm (r : Real) : exists x : α, r < ‖x‖ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩

/--
theorem `exists_lt_nnnorm` / 定理 `exists_lt_nnnorm`

English:
theorem exists_lt_nnnorm
  given: (r : Real>=0)
  statement: exists x : α, r < ‖x‖₊
  proof: exists_lt_norm α r

中文:
定理 存在_lt_nnnorm
  条件: (r : 实数>=0)
  结论: 存在 x : α, r < ‖x‖₊
  证明: exists_lt_norm α r

Depends on / 依赖: exists_lt_norm
-/
theorem exists_lt_nnnorm (r : Real>=0) : exists x : α, r < ‖x‖₊ := exists_lt_norm α r

/--
theorem `exists_lt_enorm` / 定理 `exists_lt_enorm`

English:
theorem exists_lt_enorm
  given: {r : Real>=0∞} (hr : r != ∞)
  statement: exists x : α, r < ‖x‖ₑ
  proof: by
  lift r to Real>=0 using hr
  exact mod_cast exists_lt_nnnorm α r

中文:
定理 存在_lt_enorm
  条件: {r : 实数>=0∞} (hr : r != ∞)
  结论: 存在 x : α, r < ‖x‖ₑ
  证明: by
  lift r to Real>=0 using hr
  exact mod_cast exists_lt_nnnorm α r

Depends on / 依赖: exists_lt_nnnorm, mod_cast
-/
theorem exists_lt_enorm {r : Real>=0∞} (hr : r != ∞) : exists x : α, r < ‖x‖ₑ := by
  lift r to Real>=0 using hr
  exact mod_cast exists_lt_nnnorm α r

/--
theorem `exists_norm_lt` / 定理 `exists_norm_lt`

English:
theorem exists_norm_lt
  given: {r : Real} (hr : 0 < r)
  statement: exists x : α, 0 < ‖x‖ ∧ ‖x‖ < r
  proof: let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩

中文:
定理 存在_norm_lt
  条件: {r : 实数} (hr : 0 < r)
  结论: 存在 x : α, 0 < ‖x‖ ∧ ‖x‖ < r
  证明: let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩

Depends on / 依赖: Set.inv_Ioo_0_left, Set.mem_Ioo, Set.mem_inv, exists_lt_norm, inv_Ioo_0_left, mem_Ioo, mem_inv, norm_inv
-/
theorem exists_norm_lt {r : Real} (hr : 0 < r) : exists x : α, 0 < ‖x‖ ∧ ‖x‖ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩

/--
theorem `exists_nnnorm_lt` / 定理 `exists_nnnorm_lt`

English:
theorem exists_nnnorm_lt
  given: {r : Real>=0} (hr : 0 < r)
  statement: exists x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < r
  proof: exists_norm_lt α hr

中文:
定理 存在_nnnorm_lt
  条件: {r : 实数>=0} (hr : 0 < r)
  结论: 存在 x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < r
  证明: exists_norm_lt α hr

Depends on / 依赖: exists_norm_lt
-/
theorem exists_nnnorm_lt {r : Real>=0} (hr : 0 < r) : exists x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < r :=
  exists_norm_lt α hr

/--
theorem `exists_enorm_lt` / 定理 `exists_enorm_lt`

English:
theorem exists_enorm_lt
  given: {r : Real>=0∞} (hr : 0 < r)
  statement: exists x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < r
  proof: match r with
.imp fun _ hx => ⟨zero_le_one.trans_lt hx, ENNReal.coe_lt_top⟩ | ∞ => exists_one_lt_enorm α
.imp fun _ => | (r : Real>=0) => exists_nnnorm_lt α (ENNReal.coe_pos.mp hr)
    And.imp ENNReal.coe_pos.mpr ENNReal.coe_lt_coe.mpr

中文:
定理 存在_enorm_lt
  条件: {r : 实数>=0∞} (hr : 0 < r)
  结论: 存在 x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < r
  证明: match r with
.imp fun _ hx => ⟨zero_le_one.trans_lt hx, ENNReal.coe_lt_top⟩ | ∞ => exists_one_lt_enorm α
.imp fun _ => | (r : Real>=0) => exists_nnnorm_lt α (ENNReal.coe_pos.mp hr)
    And.imp ENNReal.coe_pos.mpr ENNReal.coe_lt_coe.mpr

Depends on / 依赖: And.imp, ENNReal, ENNReal.coe_lt_coe.mpr, ENNReal.coe_lt_top, ENNReal.coe_pos.mp, ENNReal.coe_pos.mpr, coe_lt_coe, coe_lt_top, coe_pos, exists_nnnorm_lt, exists_one_lt_enorm, trans_lt, zero_le_one, zero_le_one.trans_lt
-/
theorem exists_enorm_lt {r : Real>=0∞} (hr : 0 < r) : exists x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < r :=
  match r with
.imp fun _ hx => ⟨zero_le_one.trans_lt hx, ENNReal.coe_lt_top⟩ | ∞ => exists_one_lt_enorm α
.imp fun _ => | (r : Real>=0) => exists_nnnorm_lt α (ENNReal.coe_pos.mp hr)
    And.imp ENNReal.coe_pos.mpr ENNReal.coe_lt_coe.mpr

/--
theorem `exists_norm_lt_one` / 定理 `exists_norm_lt_one`

English:
theorem exists_norm_lt_one
  statement: exists x : α, 0 < ‖x‖ ∧ ‖x‖ < 1
  proof: exists_norm_lt α one_pos

中文:
定理 存在_norm_lt_one
  结论: 存在 x : α, 0 < ‖x‖ ∧ ‖x‖ < 1
  证明: exists_norm_lt α one_pos

Depends on / 依赖: exists_norm_lt, one_pos
-/
theorem exists_norm_lt_one : exists x : α, 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_lt α one_pos

/--
theorem `exists_nnnorm_lt_one` / 定理 `exists_nnnorm_lt_one`

English:
theorem exists_nnnorm_lt_one
  statement: exists x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < 1
  proof: exists_norm_lt_one _

中文:
定理 存在_nnnorm_lt_one
  结论: 存在 x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < 1
  证明: exists_norm_lt_one _

Depends on / 依赖: exists_norm_lt_one
-/
theorem exists_nnnorm_lt_one : exists x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 := exists_norm_lt_one _

/--
theorem `exists_enorm_lt_one` / 定理 `exists_enorm_lt_one`

English:
theorem exists_enorm_lt_one
  statement: exists x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < 1
  proof: exists_enorm_lt _ one_pos

中文:
定理 存在_enorm_lt_one
  结论: 存在 x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < 1
  证明: exists_enorm_lt _ one_pos

Depends on / 依赖: exists_enorm_lt, one_pos
-/
theorem exists_enorm_lt_one : exists x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < 1 := exists_enorm_lt _ one_pos

variable {α}

@[instance]
/--
theorem `nhdsNE_neBot` / 定理 `nhdsNE_neBot`

English:
theorem nhdsNE_neBot
  given: (x : α)
  statement: NeBot (𝓝[!=] x)
  proof: by
  rw [← mem_closure_iff_nhdsWithin_neBot]; rw [Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
refine ⟨x + b, mt (Set.mem_singleton_iff.trans add_eq_left).1 norm_pos_iff.1 hb0, ?_⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

@[instance]

中文:
定理 nhdsNE_neBot
  条件: (x : α)
  结论: NeBot (𝓝[!=] x)
  证明: by
  rw [← mem_closure_iff_nhdsWithin_neBot]; rw [Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
refine ⟨x + b, mt (Set.mem_singleton_iff.trans add_eq_left).1 norm_pos_iff.1 hb0, ?_⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

@[instance]

Depends on / 依赖: Metric, Metric.mem_closure_iff, Set.mem_singleton_iff.trans, add_eq_left, add_sub_cancel_left, dist_comm, dist_eq_norm, exists_norm_lt, mem_closure_iff, mem_closure_iff_nhdsWithin_neBot, mem_singleton_iff, norm_pos_iff
-/
theorem nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x) := by
  rw [← mem_closure_iff_nhdsWithin_neBot]; rw [Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
refine ⟨x + b, mt (Set.mem_singleton_iff.trans add_eq_left).1 norm_pos_iff.1 hb0, ?_⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

@[instance]
/--
theorem `nhdsWithin_isUnit_neBot` / 定理 `nhdsWithin_isUnit_neBot`

English:
theorem nhdsWithin_isUnit_neBot
  statement: NeBot (𝓝[{ x : α | IsUnit x }] 0)
  proof: by
  simpa only [isUnit_iff_ne_zero] using! nhdsNE_neBot (0 : α)

中文:
定理 nhdsWithin_isUnit_neBot
  结论: NeBot (𝓝[{ x : α | 是单位 x }] 0)
  证明: by
  simpa only [isUnit_iff_ne_zero] using! nhdsNE_neBot (0 : α)

Depends on / 依赖: isUnit_iff_ne_zero, nhdsNE_neBot
-/
theorem nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [isUnit_iff_ne_zero] using! nhdsNE_neBot (0 : α)

end Nontrivially

section Densely

variable (α) [DenselyNormedField α]

/--
theorem `exists_lt_norm_lt` / 定理 `exists_lt_norm_lt`

English:
theorem exists_lt_norm_lt
  given: {r₁ r₂ : Real} (h₀ : 0 <= r₁) (h : r₁ < r₂)
  statement: exists x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂
  proof: DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h

中文:
定理 存在_lt_norm_lt
  条件: {r₁ r₂ : 实数} (h₀ : 0 <= r₁) (h : r₁ < r₂)
  结论: 存在 x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂
  证明: DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h

Depends on / 依赖: DenselyNormedField, DenselyNormedField.lt_norm_lt, lt_norm_lt
-/
theorem exists_lt_norm_lt {r₁ r₂ : Real} (h₀ : 0 <= r₁) (h : r₁ < r₂) : exists x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂ :=
  DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h

/--
theorem `exists_lt_nnnorm_lt` / 定理 `exists_lt_nnnorm_lt`

English:
theorem exists_lt_nnnorm_lt
  given: {r₁ r₂ : Real>=0} (h : r₁ < r₂)
  statement: exists x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂
  proof: mod_cast exists_lt_norm_lt α r₁.prop h

中文:
定理 存在_lt_nnnorm_lt
  条件: {r₁ r₂ : 实数>=0} (h : r₁ < r₂)
  结论: 存在 x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂
  证明: mod_cast exists_lt_norm_lt α r₁.prop h

Depends on / 依赖: exists_lt_norm_lt, mod_cast
-/
theorem exists_lt_nnnorm_lt {r₁ r₂ : Real>=0} (h : r₁ < r₂) : exists x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂ :=
  mod_cast exists_lt_norm_lt α r₁.prop h

/--
Instance `denselyOrdered_range_norm` / 实例 `denselyOrdered_range_norm`

English:
instance denselyOrdered_range_norm
  signature: : DenselyOrdered (Set.range (norm : α -> Real)) where
  body: by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
    exact ⟨⟨‖z‖, z, rfl⟩, h⟩

中文:
实例 denselyOrdered_range_norm
  签名: : 稠密序 (集合.range (norm : α -> 实数)) where
  定义体: by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
    exact ⟨⟨‖z‖, z, rfl⟩, h⟩

Depends on / 依赖: exists_lt_norm_lt, norm_nonneg
-/
instance denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α -> Real)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
    exact ⟨⟨‖z‖, z, rfl⟩, h⟩

/--
Instance `denselyOrdered_range_nnnorm` / 实例 `denselyOrdered_range_nnnorm`

English:
instance denselyOrdered_range_nnnorm
  signature: : DenselyOrdered (Set.range (nnnorm : α -> Real>=0)) where
  body: by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
    exact ⟨⟨‖z‖₊, z, rfl⟩, h⟩

中文:
实例 denselyOrdered_range_nnnorm
  签名: : 稠密序 (集合.range (nnnorm : α -> 实数>=0)) where
  定义体: by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
    exact ⟨⟨‖z‖₊, z, rfl⟩, h⟩

Depends on / 依赖: exists_lt_nnnorm_lt
-/
instance denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α -> Real>=0)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
    exact ⟨⟨‖z‖₊, z, rfl⟩, h⟩

end Densely

end NormedField

/-- A normed field is nontrivially normed
provided that the norm of some nonzero element is not one. -/
@[instance_reducible]
/--
Definition of `NontriviallyNormedField.ofNormNeOne` / `NontriviallyNormedField.ofNormNeOne` 的定义

English:
definition NontriviallyNormedField.ofNormNeOne
  signature: {𝕜 : Type*} [h' : NormedField 𝕜]
  body: h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_gt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 hx)).2 hlt
    · exact ⟨x, hlt⟩

中文:
定义 NontriviallyNormedField.ofNormNeOne
  签名: {𝕜 : 类型} [h' : 赋范域 𝕜]
  定义体: h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_gt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 hx)).2 hlt
    · exact ⟨x, hlt⟩
-/
def NontriviallyNormedField.ofNormNeOne {𝕜 : Type*} [h' : NormedField 𝕜]
    (h : exists x : 𝕜, x != 0 ∧ ‖x‖ != 1) : NontriviallyNormedField 𝕜 where
  toNormedField := h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_gt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 hx)).2 hlt
    · exact ⟨x, hlt⟩

/--
Instance `Real.normedField` / 实例 `Real.normedField`

English:
instance Real.normedField
  signature: : NormedField Real
  body: { Real.normedAddCommGroup, Real.instField with
    norm_mul := abs_mul }

中文:
实例 实数.normedField
  签名: : 赋范域 实数
  定义体: { Real.normedAddCommGroup, Real.instField with
    norm_mul := abs_mul }

Depends on / 依赖: Real.instField, Real.normedAddCommGroup, abs_mul, instField, norm_mul, normedAddCommGroup
-/
noncomputable instance Real.normedField : NormedField Real :=
  { Real.normedAddCommGroup, Real.instField with
    norm_mul := abs_mul }

/--
Instance `Real.denselyNormedField` / 实例 `Real.denselyNormedField`

English:
instance Real.denselyNormedField
  signature: : DenselyNormedField Real where
  body: let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

中文:
实例 实数.denselyNormedField
  签名: : DenselyNormedField 实数 where
  定义体: let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

Depends on / 依赖: Real.norm_eq_abs, abs_of_nonneg, exists_between, norm_eq_abs
-/
noncomputable instance Real.denselyNormedField : DenselyNormedField Real where
  lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

/--
theorem `toNNReal_mul_nnnorm` / 定理 `toNNReal_mul_nnnorm`

English:
theorem toNNReal_mul_nnnorm
  given: {x : Real} (y : Real) (hx : 0 <= x)
  statement: x.toNNReal * ‖y‖₊ = ‖x * y‖₊
  proof: by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]

中文:
定理 toNN实数_mul_nnnorm
  条件: {x : 实数} (y : 实数) (hx : 0 <= x)
  结论: x.toNN实数 * ‖y‖₊ = ‖x * y‖₊
  证明: by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]

Depends on / 依赖: NNReal, NNReal.coe_mk, NNReal.coe_mul, Real.toNNReal_of_nonneg, coe_mk, coe_mul, coe_nnnorm, nnnorm_mul, norm_of_nonneg, toNNReal_of_nonneg
-/
theorem toNNReal_mul_nnnorm {x : Real} (y : Real) (hx : 0 <= x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]

/--
theorem `nnnorm_mul_toNNReal` / 定理 `nnnorm_mul_toNNReal`

English:
theorem nnnorm_mul_toNNReal
  given: (x : Real) {y : Real} (hy : 0 <= y)
  statement: ‖x‖₊ * y.toNNReal = ‖x * y‖₊
  proof: by
  rw [mul_comm]; rw [mul_comm x]; rw [toNNReal_mul_nnnorm x hy]

中文:
定理 nnnorm_mul_toNN实数
  条件: (x : 实数) {y : 实数} (hy : 0 <= y)
  结论: ‖x‖₊ * y.toNN实数 = ‖x * y‖₊
  证明: by
  rw [mul_comm]; rw [mul_comm x]; rw [toNNReal_mul_nnnorm x hy]

Depends on / 依赖: mul_comm, toNNReal_mul_nnnorm
-/
theorem nnnorm_mul_toNNReal (x : Real) {y : Real} (hy : 0 <= y) : ‖x‖₊ * y.toNNReal = ‖x * y‖₊ := by
  rw [mul_comm]; rw [mul_comm x]; rw [toNNReal_mul_nnnorm x hy]

end Real

/-! ### Induced normed structures -/

section Induced

variable {F : Type*} (R S : Type*) [FunLike F R S]

/--
Definition of `NormedDivisionRing.induced` / `NormedDivisionRing.induced` 的定义

English:
abbreviation NormedDivisionRing.induced
  signature: [DivisionRing R] [NormedDivisionRing S]
  body: fast_instance% { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul x y := show ‖f _‖ = _ from (map_mul f x y).symm ▸ norm_mul (f x) (f y) }

中文:
缩写 NormedDivision环.induced
  签名: [除环 R] [NormedDivision环 S]
  定义体: fast_instance% { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul x y := show ‖f _‖ = _ from (map_mul f x y).symm ▸ norm_mul (f x) (f y) }

Depends on / 依赖: DivisionRing, NormedAddCommGroup, NormedAddCommGroup.induced, fast_instance, induced, map_mul, norm_mul
-/
abbrev NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  fast_instance% { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul x y := show ‖f _‖ = _ from (map_mul f x y).symm ▸ norm_mul (f x) (f y) }

/--
Definition of `NormedField.induced` / `NormedField.induced` 的定义

English:
abbreviation NormedField.induced
  signature: [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
  body: fast_instance% { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }

中文:
缩写 赋范域.induced
  签名: [域 R] [赋范域 S] [非幺环态射类 F R S] (f : F)
  定义体: fast_instance% { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }

Depends on / 依赖: NormedDivisionRing, NormedDivisionRing.induced, fast_instance, induced, mul_comm
-/
abbrev NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  fast_instance% { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }

end Induced

namespace SubfieldClass

variable {S F : Type*} [SetLike S F]

/--
Instance `toNormedField` / 实例 `toNormedField`

English:
instance toNormedField
  signature: [NormedField F] [SubfieldClass S F] (s : S)
  body: fast_instance% NormedField.induced s F (SubringClass.subtype s) Subtype.val_injective

中文:
实例 toNormedField
  签名: [赋范域 F] [子域类 S F] (s : S)
  定义体: fast_instance% NormedField.induced s F (SubringClass.subtype s) Subtype.val_injective

Depends on / 依赖: NormedField, NormedField.induced, SubringClass, SubringClass.subtype, Subtype, Subtype.val_injective, fast_instance, induced, subtype, val_injective
-/
instance toNormedField [NormedField F] [SubfieldClass S F] (s : S) : NormedField s :=
  fast_instance% NormedField.induced s F (SubringClass.subtype s) Subtype.val_injective

end SubfieldClass

namespace AbsoluteValue

/-- A real absolute value on a field determines a `NormedField` structure. -/
@[instance_reducible]
/--
Definition of `toNormedField` / `toNormedField` 的定义

English:
definition toNormedField
  signature: {K : Type*} [Field K] (v : AbsoluteValue K Real)
  body: inferInstanceAs (Field K)
  __ := v.toNormedRing
  norm_mul := v.map_mul

中文:
定义 toNormedField
  签名: {K : 类型} [域 K] (v : 绝对值 K 实数)
  定义体: inferInstanceAs (Field K)
  __ := v.toNormedRing
  norm_mul := v.map_mul
-/
noncomputable def toNormedField {K : Type*} [Field K] (v : AbsoluteValue K Real) : NormedField K where
  toField := inferInstanceAs (Field K)
  __ := v.toNormedRing
  norm_mul := v.map_mul

end AbsoluteValue
