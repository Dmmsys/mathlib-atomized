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

/-- A normed division ring is a division ring endowed with a seminorm which satisfies the equality
`‖x y‖ = ‖x‖ ‖y‖`. -/
/-
**NormedDivisionRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed division ring is a division ring endowed with a seminorm which satisfie
s the equality
`‖x y‖ = ‖x‖ ‖y‖`.
-/
class NormedDivisionRing (α : Type*) extends Norm α, DivisionRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is multiplicative. -/
  protected norm_mul : ∀ a b, norm (a * b) = norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NormedDivisionRing.toDivisionRing

-- see Note [lower instance priority]
/-- A normed division ring is a normed ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed division ring is a normed ring.
-/
instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] :
    NormedRing α :=
  { β with norm_mul_le a b := (NormedDivisionRing.norm_mul a b).le }

-- see Note [lower instance priority]
/-- The norm on a normed division ring is strictly multiplicative. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm on a normed division ring is strictly multiplicative.
-/
instance (priority := 100) NormedDivisionRing.toNormMulClass [NormedDivisionRing α] :
    NormMulClass α where
  norm_mul := NormedDivisionRing.norm_mul

section NormedDivisionRing

variable [NormedDivisionRing α] {a b : α}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) NormedDivisionRing.to_normOneClass : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (one_ne_zero' α)) <| by rw [← norm_mul, mul_one, mul_one]⟩

@[simp]
/-
**norm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
  map_div₀ (normHom : α →*₀ ℝ) a b

@[simp]
/-
**nnnorm_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊ :=
  map_div₀ (nnnormHom : α →*₀ ℝ≥0) a b

@[simp]
/-
**norm_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹ :=
  map_inv₀ (normHom : α →*₀ ℝ) a

@[simp]
/-
**nnnorm_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹ :=
  NNReal.eq <| by simp

@[simp]
/-
**enorm_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_inv {a : α} (ha : a != 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_inv {a : α} (ha : a ≠ 0) : ‖a⁻¹‖ₑ = ‖a‖ₑ⁻¹ := by simp [enorm, ENNReal.coe_inv, ha]

@[simp]
/-
**norm_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem norm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖ = ‖a‖ ^ n :=
  map_zpow₀ (normHom : α →*₀ ℝ)

@[simp]
/-
**nnnorm_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_zpow : forall (a : α) (n : Int), ‖a ^ n‖₊ = ‖a‖₊ ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow₀`：map_zpow₀ {F G₀ G₀' : Type*} [GroupWithZero G₀] [GroupWithZer
o G₀'] [FunLike F G₀ G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (x : G₀) (n…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  map_zpow₀ (nnnormHom : α →*₀ ℝ≥0)
/-
**dist_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] [IsIsom
etricSMul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.dist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   dist (h x) 
(h y) = dis…
-/
theorem dist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    dist z⁻¹ w⁻¹ = dist z w / (‖z‖ * ‖w‖) := by
  rw [dist_eq_norm, inv_sub_inv' hz hw, norm_mul, norm_mul, norm_inv, norm_inv, mul_comm ‖z‖⁻¹,
    mul_assoc, dist_eq_norm', div_eq_mul_inv, mul_inv]
/-
**nndist_inv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_inv_inv [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G] [IsIs
ometricSMul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.nndist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   nndist (h
 x) (h y) = n…
-/
theorem nndist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    nndist z⁻¹ w⁻¹ = nndist z w / (‖z‖₊ * ‖w‖₊) :=
  NNReal.eq <| dist_inv_inv₀ hz hw
/-
**norm_commutator_sub_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_commutator_sub_one_le (ha : a != 0) (hb : b != 0) : ‖a * b * a⁻¹ * b⁻
¹ - 1‖ <= 2 * ‖a‖⁻¹ * ‖b‖⁻¹ * ‖a - 1‖ * ‖b - 1‖
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `norm_commutator_units_sub_one_le`：norm_commutator_units_sub_one_le (a b 
: αˣ) : ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ <= 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖
 * ‖b.val - 1‖
-/
lemma norm_commutator_sub_one_le (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖ ≤ 2 * ‖a‖⁻¹ * ‖b‖⁻¹ * ‖a - 1‖ * ‖b - 1‖ := by
  simpa using norm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)
/-
**nnnorm_commutator_sub_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_commutator_sub_one_le (ha : a != 0) (hb : b != 0) : ‖a * b * a⁻¹ * 
b⁻¹ - 1‖₊ <= 2 * ‖a‖₊⁻¹ * ‖b‖₊⁻¹ * ‖a - 1‖₊ * ‖b - 1‖₊
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用引理 `nnnorm_commutator_units_sub_one_le`：nnnorm_commutator_units_sub_one_le (
a b : αˣ) : ‖(a * b * a⁻¹ * b⁻¹).val - 1‖₊ <= 2 * ‖a⁻¹.val‖₊ * ‖b⁻¹.val‖₊ * ‖a.v
al - 1‖₊ * ‖b.val - 1‖₊
-/
lemma nnnorm_commutator_sub_one_le (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖₊ ≤ 2 * ‖a‖₊⁻¹ * ‖b‖₊⁻¹ * ‖a - 1‖₊ * ‖b - 1‖₊ := by
  simpa using nnnorm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

namespace NormedDivisionRing

section Discrete

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [DiscreteTopology 𝕜]

/-
**NormedDivisionRing.norm_eq_one_iff_ne_zero_of_discrete** 是 Mathlib 中的一个引理，位于命名
空间 `NormedDivisionRing`。
形式化陈述：norm_eq_one_iff_ne_zero_of_discrete {x : 𝕜} : ‖x‖ = 1 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 33 条，此处仅展示前 30 条）
-/
lemma norm_eq_one_iff_ne_zero_of_discrete {x : 𝕜} : ‖x‖ = 1 ↔ x ≠ 0 := by
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
      rw [← inv_inj, inv_one, ← norm_inv]
      exact H (by simpa) h' h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖x‖ ^ k < ε := exists_pow_lt_of_lt_one εpos h
    rw [← norm_pow] at hk
    specialize h' _ hk
    simp [hx] at h'

@[simp]
/-
**NormedDivisionRing.norm_le_one_of_discrete** 是 Mathlib 中的一个引理，位于命名空间 `NormedDi
visionRing`。
形式化陈述：norm_le_one_of_discrete (x : 𝕜) : ‖x‖ <= 1
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `NormedDivisionRing.norm_eq_one_iff_ne_zero_of_discrete`：norm_eq_one_iff_
ne_zero_of_discrete {x : 𝕜} : ‖x‖ = 1 ↔ x != 0
-/
lemma norm_le_one_of_discrete
    (x : 𝕜) : ‖x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [norm_eq_one_iff_ne_zero_of_discrete.mpr hx]
/-
**NormedDivisionRing.unitClosedBall_eq_univ_of_discrete** 是 Mathlib 中的一个引理，位于命名空
间 `NormedDivisionRing`。
形式化陈述：unitClosedBall_eq_univ_of_discrete : (Metric.closedBall 0 1 : Set 𝕜) = Set
.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma unitClosedBall_eq_univ_of_discrete : (Metric.closedBall 0 1 : Set 𝕜) = Set.univ := by
  ext
  simp

end Discrete

end NormedDivisionRing

end NormedDivisionRing

/-- A normed field is a field with a norm satisfying ‖x y‖ = ‖x‖ ‖y‖. -/
/-
**NormedField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed field is a field with a norm satisfying ‖x y‖ = ‖x‖ ‖y‖.
-/
class NormedField (α : Type*) extends Norm α, Field α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (-x + y)
  /-- The norm is multiplicative. -/
  protected norm_mul : ∀ a b, norm (a * b) = norm a * norm b

-- see Note [lower instance priority]
attribute [instance 10] NormedField.toField

/-- A nontrivially normed field is a normed field in which there is an element of norm different
from `0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by
multiplication by the powers of any element, and thus to relate algebra and topology. -/
/-
**NontriviallyNormedField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nontrivially normed field is a normed field in which there is an element of no
rm different
from `0` and `1`. This makes it possible to bring any element arbitrarily close 
to `0` by
multiplication by the powers of any element, and thus to relate algebra and topo
logy.
-/
class NontriviallyNormedField (α : Type*) extends NormedField α where
  /-- The norm attains a value exceeding 1. -/
  non_trivial : ∃ x : α, 1 < ‖x‖

/-- A densely normed field is a normed field for which the image of the norm is dense in `ℝ≥0`,
which means it is also nontrivially normed. However, not all nontrivially normed fields are densely
normed; in particular, the `Padic`s exhibit this fact. -/
/-
**DenselyNormedField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A densely normed field is a normed field for which the image of the norm is dens
e in `ℝ≥0`,
which means it is also nontrivially normed. However, not all nontrivially normed
 fields are densely
normed; in particular, the `Padic`s exhibit this fact.
-/
class DenselyNormedField (α : Type*) extends NormedField α where
  /-- The range of the norm is dense in the collection of nonnegative real numbers. -/
  lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ‖a‖ ∧ ‖a‖ < y

section NormedField

/-- A densely normed field is always a nontrivially normed field.
See note [lower instance priority]. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A densely normed field is always a nontrivially normed field.
See note [lower instance priority].
-/
instance (priority := 100) DenselyNormedField.toNontriviallyNormedField [DenselyNormedField α] :
    NontriviallyNormedField α where
  non_trivial :=
    let ⟨a, h, _⟩ := DenselyNormedField.lt_norm_lt 1 2 zero_le_one one_lt_two
    ⟨a, h⟩

variable [NormedField α]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul_le a b := (norm_mul a b).le }

end NormedField

namespace NormedField

section Nontrivially

variable (α) [NontriviallyNormedField α]

/-
**NormedField.exists_one_lt_norm** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_one_lt_norm : exists x : α, 1 < ‖x‖
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NontriviallyNormedField.non_trivial`：∀ {α : Type u_5} [self : Nontrivial
lyNormedField α], ∃ x, 1 < ‖x‖
-/
theorem exists_one_lt_norm : ∃ x : α, 1 < ‖x‖ :=
  ‹NontriviallyNormedField α›.non_trivial
/-
**NormedField.exists_one_lt_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_one_lt_nnnorm : exists x : α, 1 < ‖x‖₊
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
-/
theorem exists_one_lt_nnnorm : ∃ x : α, 1 < ‖x‖₊ := exists_one_lt_norm α
/-
**NormedField.exists_one_lt_enorm** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_one_lt_enorm : exists x : α, 1 < ‖x‖ₑ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `NormedField.exists_one_lt_nnnorm`：exists_one_lt_nnnorm : exists x : α, 1
 < ‖x‖₊
-/
theorem exists_one_lt_enorm : ∃ x : α, 1 < ‖x‖ₑ :=
  exists_one_lt_nnnorm α |>.imp fun _ => ENNReal.coe_lt_coe.mpr
/-
**NormedField.exists_lt_norm** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_lt_norm (r : Real) : exists x : α, r < ‖x‖
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用引理 `pow_unbounded_of_one_lt`：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : 
R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ‖x‖ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩
/-
**NormedField.exists_lt_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_lt_nnnorm (r : Real>=0) : exists x : α, r < ‖x‖₊
参数：r : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
-/
theorem exists_lt_nnnorm (r : ℝ≥0) : ∃ x : α, r < ‖x‖₊ := exists_lt_norm α r
/-
**NormedField.exists_lt_enorm** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_lt_enorm {r : Real>=0∞} (hr : r != ∞) : exists x : α, r < ‖x‖ₑ
参数：hr : r != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedField.exists_lt_nnnorm`：exists_lt_nnnorm (r : Real>=0) : exists x 
: α, r < ‖x‖₊
-/
theorem exists_lt_enorm {r : ℝ≥0∞} (hr : r ≠ ∞) : ∃ x : α, r < ‖x‖ₑ := by
  lift r to ℝ≥0 using hr
  exact mod_cast exists_lt_nnnorm α r
/-
**NormedField.exists_norm_lt** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_norm_lt {r : Real} (hr : 0 < r) : exists x : α, 0 < ‖x‖ ∧ ‖x‖ < r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Set.mem_inv`：mem_inv : a in s⁻¹ ↔ a⁻¹ in s
· 使用定理 `Set.inv_Ioo_0_left`：inv_Ioo_0_left (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩
/-
**NormedField.exists_nnnorm_lt** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_nnnorm_lt {r : Real>=0} (hr : 0 < r) : exists x : α, 0 < ‖x‖₊ ∧ ‖x‖
₊ < r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
-/
theorem exists_nnnorm_lt {r : ℝ≥0} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < r :=
  exists_norm_lt α hr

/-- TODO: merge with `_root_.exists_enorm_lt`. -/
/-
**NormedField.exists_enorm_lt** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_enorm_lt {r : Real>=0∞} (hr : 0 < r) : exists x : α, 0 < ‖x‖ₑ ∧ ‖x‖
ₑ < r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `NormedField.exists_one_lt_enorm`：exists_one_lt_enorm : exists x : α, 1 <
 ‖x‖ₑ
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `NormedField.exists_nnnorm_lt`：exists_nnnorm_lt {r : Real>=0} (hr : 0 < r
) : exists x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
TODO: merge with `_root_.exists_enorm_lt`.
-/
theorem exists_enorm_lt {r : ℝ≥0∞} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < r :=
  match r with
  | ∞ => exists_one_lt_enorm α |>.imp fun _ hx => ⟨zero_le_one.trans_lt hx, ENNReal.coe_lt_top⟩
  | (r : ℝ≥0) => exists_nnnorm_lt α (ENNReal.coe_pos.mp hr) |>.imp fun _ =>
    And.imp ENNReal.coe_pos.mpr ENNReal.coe_lt_coe.mpr
/-
**NormedField.exists_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_norm_lt_one : exists x : α, 0 < ‖x‖ ∧ ‖x‖ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem exists_norm_lt_one : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_lt α one_pos
/-
**NormedField.exists_nnnorm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_nnnorm_lt_one : exists x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_norm_lt_one`：exists_norm_lt_one : exists x : α, 0 < ‖
x‖ ∧ ‖x‖ < 1
-/
theorem exists_nnnorm_lt_one : ∃ x : α, 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 := exists_norm_lt_one _
/-
**NormedField.exists_enorm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_enorm_lt_one : exists x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_enorm_lt`：exists_enorm_lt {r : Real>=0∞} (hr : 0 < r)
 : exists x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < r
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem exists_enorm_lt_one : ∃ x : α, 0 < ‖x‖ₑ ∧ ‖x‖ₑ < 1 := exists_enorm_lt _ one_pos

variable {α}

@[instance]
/-
**NormedField.nhdsNE_neBot** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem nhdsNE_neBot (x : α) : NeBot (𝓝[≠] x) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine ⟨x + b, mt (Set.mem_singleton_iff.trans add_eq_left).1 <| norm_pos_iff.1 hb0, ?_⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

@[instance]
/-
**NormedField.nhdsWithin_isUnit_neBot** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
-/
theorem nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [isUnit_iff_ne_zero] using! nhdsNE_neBot (0 : α)

end Nontrivially

section Densely

variable (α) [DenselyNormedField α]

/-
**NormedField.exists_lt_norm_lt** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_lt_norm_lt {r₁ r₂ : Real} (h₀ : 0 <= r₁) (h : r₁ < r₂) : exists x :
 α, r₁ < ‖x‖ ∧ ‖x‖ < r₂
参数：h₀ : 0 <= r₁；h : r₁ < r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenselyNormedField.lt_norm_lt`：∀ {α : Type u_5} [self : DenselyNormedFie
ld α] (x y : ℝ), 0 ≤ x → x < y → ∃ a, x < ‖a‖ ∧ ‖a‖ < y
-/
theorem exists_lt_norm_lt {r₁ r₂ : ℝ} (h₀ : 0 ≤ r₁) (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂ :=
  DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h
/-
**NormedField.exists_lt_nnnorm_lt** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：exists_lt_nnnorm_lt {r₁ r₂ : Real>=0} (h : r₁ < r₂) : exists x : α, r₁ < ‖
x‖₊ ∧ ‖x‖₊ < r₂
参数：h : r₁ < r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_lt_norm_lt`：exists_lt_norm_lt {r₁ r₂ : Real} (h₀ : 0 
<= r₁) (h : r₁ < r₂) : exists x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem exists_lt_nnnorm_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂ :=
  mod_cast exists_lt_norm_lt α r₁.prop h
/-
**NormedField.denselyOrdered_range_norm** 是 Mathlib 中的一个实例，位于命名空间 `NormedField`。
形式化陈述：denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α -> Real)) 
where dense
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_lt_norm_lt`：exists_lt_norm_lt {r₁ r₂ : Real} (h₀ : 0 
<= r₁) (h : r₁ < r₂) : exists x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
instance denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α → ℝ)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
    exact ⟨⟨‖z‖, z, rfl⟩, h⟩
/-
**NormedField.denselyOrdered_range_nnnorm** 是 Mathlib 中的一个实例，位于命名空间 `NormedField
`。
形式化陈述：denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α -> Rea
l>=0)) where dense
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_lt_nnnorm_lt`：exists_lt_nnnorm_lt {r₁ r₂ : Real>=0} (
h : r₁ < r₂) : exists x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂
-/
instance denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α → ℝ≥0)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
    exact ⟨⟨‖z‖₊, z, rfl⟩, h⟩

end Densely

end NormedField

/-- A normed field is nontrivially normed
provided that the norm of some nonzero element is not one. -/
@[instance_reducible]
/-
**NontriviallyNormedField.ofNormNeOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NontriviallyNormedField.ofNormNeOne {𝕜 : Type*} [h' : NormedField 𝕜] (h : 
exists x : 𝕜, x != 0 ∧ ‖x‖ != 1) : NontriviallyNormedField 𝕜 where toNormedField
参数：h : exists x : 𝕜, x != 0 ∧ ‖x‖ != 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed field is nontrivially normed
provided that the norm of some nonzero element is not one.
-/
def NontriviallyNormedField.ofNormNeOne {𝕜 : Type*} [h' : NormedField 𝕜]
    (h : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1) : NontriviallyNormedField 𝕜 where
  toNormedField := h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_gt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 hx)).2 hlt
    · exact ⟨x, hlt⟩
/-
**Real.normedField** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.normedField : NormedField Real
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.div_eq_mul_inv`：∀ {K : Type u} [self : Field K] (a b : K), a / b =
 a * b⁻¹
· 使用定理 `Field.zpow_zero'`：∀ {K : Type u} [self : Field K] (a : K), a ^ 0 = 1
· 使用定理 `Field.zpow_succ'`：∀ {K : Type u} [self : Field K] (n : ℕ) (a : K), a ^ ↑
n.succ = a ^ ↑n * a
· 使用定理 `Field.zpow_neg'`：∀ {K : Type u} [self : Field K] (n : ℕ) (a : K), a ^ In
t.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `Field.toNontrivial`：∀ {K : Type u} [self : Field K], Nontrivial K
· 使用定理 `Field.mul_inv_cancel`：∀ {K : Type u} [self : Field K] (a : K), a ≠ 0 → a
 * a⁻¹ = 1
· 使用定理 `Field.inv_zero`：∀ {K : Type u} [self : Field K], 0⁻¹ = 0
· 使用定理 `Field.nnratCast_def`：∀ {K : Type u} [self : Field K] (q : ℚ≥0), ↑q = ↑q.
num / ↑q.den
· 使用定理 `Field.nnqsmul_def`：∀ {K : Type u} [self : Field K] (q : ℚ≥0) (a : K), Fi
eld.nnqsmul q a = ↑q * a
· 使用定理 `Field.ratCast_def`：∀ {K : Type u} [self : Field K] (q : ℚ), ↑q = ↑q.num 
/ ↑q.den
· 使用定理 `Field.qsmul_def`：∀ {K : Type u} [self : Field K] (a : ℚ) (x : K), Field.
qsmul a x = ↑a * x
· 使用定理 `NormedAddCommGroup.dist_eq`：∀ {E : Type u_8} [self : NormedAddCommGroup 
E] (x y : E), dist x y = ‖-x + y‖
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
-/
noncomputable instance Real.normedField : NormedField ℝ :=
  { Real.normedAddCommGroup, Real.instField with
    norm_mul := abs_mul }
/-
**Real.denselyNormedField** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.denselyNormedField : DenselyNormedField Real where lt_norm_lt _ _ h₀ 
hr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Real.denselyNormedField : DenselyNormedField ℝ where
  lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

/-
**Real.toNNReal_mul_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：toNNReal_mul_nnnorm {x : Real} (y : Real) (hx : 0 <= x) : x.toNNReal * ‖y‖
₊ = ‖x * y‖₊
参数：y : Real；hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.toNNReal_of_nonneg`：∀ {r : ℝ} (hr : 0 ≤ r), r.toNNReal = NNReal.mk 
r hr
· 使用定理 `nnnorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 :
 Mul α] [NormMulClass α] (a b : α), ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toNNReal_mul_nnnorm {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]
/-
**Real.nnnorm_mul_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nnnorm_mul_toNNReal (x : Real) {y : Real} (hy : 0 <= y) : ‖x‖₊ * y.toNNRea
l = ‖x * y‖₊
参数：x : Real；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.toNNReal_mul_nnnorm`：toNNReal_mul_nnnorm {x : Real} (y : Real) (hx 
: 0 <= x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊
-/
theorem nnnorm_mul_toNNReal (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : ‖x‖₊ * y.toNNReal = ‖x * y‖₊ := by
  rw [mul_comm, mul_comm x, toNNReal_mul_nnnorm x hy]

end Real

/-! ### Induced normed structures -/

section Induced

variable {F : Type*} (R S : Type*) [FunLike F R S]

/-- An injective non-unital ring homomorphism from a `DivisionRing` to a `NormedRing` induces a
`NormedDivisionRing` structure on the domain.

See note [reducible non-instances] -/
/-
**NormedDivisionRing.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S] [NonUni
talRingHomClass F R S] (f : F) (hf : Function.Injective f) : NormedDivisionRing 
R
参数：f : F；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective non-unital ring homomorphism from a `DivisionRing` to a `NormedRing
` induces a
`NormedDivisionRing` structure on the domain.

See note [reducible non-instances]
-/
abbrev NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  fast_instance% { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul x y := show ‖f _‖ = _ from (map_mul f x y).symm ▸ norm_mul (f x) (f y) }

/-- An injective non-unital ring homomorphism from a `Field` to a `NormedRing` induces a
`NormedField` structure on the domain.

See note [reducible non-instances] -/
/-
**NormedField.induced** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S
] (f : F) (hf : Function.Injective f) : NormedField R
参数：f : F；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective non-unital ring homomorphism from a `Field` to a `NormedRing` induc
es a
`NormedField` structure on the domain.

See note [reducible non-instances]
-/
abbrev NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  fast_instance% { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }

end Induced

namespace SubfieldClass

variable {S F : Type*} [SetLike S F]

/--
If `s` is a subfield of a normed field `F`, then `s` is equipped with an induced normed
field structure.
-/
/-
**SubfieldClass.toNormedField** 是 Mathlib 中的一个实例，位于命名空间 `SubfieldClass`。
形式化陈述：toNormedField [NormedField F] [SubfieldClass S F] (s : S) : NormedField s
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a subfield of a normed field `F`, then `s` is equipped with an induced
 normed
field structure.
-/
instance toNormedField [NormedField F] [SubfieldClass S F] (s : S) : NormedField s :=
  fast_instance% NormedField.induced s F (SubringClass.subtype s) Subtype.val_injective

end SubfieldClass

namespace AbsoluteValue

/-- A real absolute value on a field determines a `NormedField` structure. -/
@[instance_reducible]
/-
**AbsoluteValue.toNormedField** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：toNormedField {K : Type*} [Field K] (v : AbsoluteValue K Real) : NormedFie
ld K where toField
参数：v : AbsoluteValue K Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedRing.dist_eq`：∀ {α : Type u_5} [self : NormedRing α] (x y : α), di
st x y = ‖-x + y‖

--- 原说明 ---
A real absolute value on a field determines a `NormedField` structure.
-/
noncomputable def toNormedField {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : NormedField K where
  toField := inferInstanceAs (Field K)
  __ := v.toNormedRing
  norm_mul := v.map_mul

end AbsoluteValue

