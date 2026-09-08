/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.WithOne.Map
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Set.Function

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: `Γ ∪ {0}`.

The disadvantage is that a type such as `NNReal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

@[expose] public section

variable {α β : Type*}

/-- A linearly ordered commutative monoid with a zero element. -/
/-
**LinearOrderedCommMonoidWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linearly ordered commutative monoid with a zero element.
-/
class LinearOrderedCommMonoidWithZero (α : Type*) extends CommMonoidWithZero α, LinearOrder α,
    PosMulStrictMono α, OrderBot α, IsBotZeroClass α where

/-- A linearly ordered commutative group with a zero element. -/
/-
**LinearOrderedCommGroupWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linearly ordered commutative group with a zero element.
-/
class LinearOrderedCommGroupWithZero (α : Type*) extends LinearOrderedCommMonoidWithZero α,
  CommGroupWithZero α

section LinearOrderedCommMonoidWithZero
variable [LinearOrderedCommMonoidWithZero α] {a b : α} {n : ℕ}

/-!
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrderedCommMonoidWithZero.toMulPosStrictMono :
    MulPosStrictMono α := posMulStrictMono_iff_mulPosStrictMono.1 inferInstance

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrderedCommMonoidWithZero.toIsOrderedMonoid :
    IsOrderedMonoid α where
  mul_le_mul_left a b hab c := by
    obtain rfl | hc := eq_or_ne c 0
    · simp
    obtain rfl | hab := hab.eq_or_lt
    · simp
    · exact (mul_lt_mul_of_pos_right hab hc.pos).le

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha := (strictMono_mul_left_of_pos ha.pos).injective
  mul_right_cancel_of_ne_zero ha := (strictMono_mul_right_of_pos ha.pos).injective

/-- Pullback a `LinearOrderedCommMonoidWithZero` under an injective map.
See note [reducible non-instances]. -/
/-
**Function.Injective.linearOrderedCommMonoidWithZero** 是 Mathlib 中的一个缩写定义，位于命名空间
 ``。
形式化陈述：Function.Injective.linearOrderedCommMonoidWithZero {β : Type*} [Zero β] [B
ot β] [One β] [Mul β] [Pow β Nat] [LE β] [LT β] [Max β] [Min β] [Ord β] [Decidab
leEq β] [DecidableLE β] [DecidableLT β] (f : β -> α) (hf : Function.Injective f)
 (zero : f 0 = 0) (one : f 1 = 1) (mul : forall x y, f (x * y) = f x * f y) (npo
w : forall (x) (n : Nat), f (x ^ n) = f x ^ n) (le : forall {x y}, f x <= f y ↔ 
x <= y) (lt : forall {x y}, f x < f y ↔ x < y) (hsup : forall x y, f (x ⊔ y) = m
ax (f x) (f y)) (hinf : fo
参数：f : β -> α；hf : Function.Injective f；zero : f 0 = 0；one : f 1 = 1；mul : foral
l x y, f (x * y) = f x * f y；npow : forall (x) (n : Nat), f (x ^ n) = f x ^ n；le
 : forall {x y}, f x <= f y ↔ x <= y；lt : forall {x y}, f x < f y ↔ x < y；hsup :
 forall x y, f (x ⊔ y) = max (f x) (f y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback a `LinearOrderedCommMonoidWithZero` under an injective map.
See note [reducible non-instances].
-/
abbrev Function.Injective.linearOrderedCommMonoidWithZero {β : Type*} [Zero β] [Bot β] [One β]
    [Mul β] [Pow β ℕ] [LE β] [LT β] [Max β] [Min β] [Ord β]
    [DecidableEq β] [DecidableLE β] [DecidableLT β]
    (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y))
    (bot : f ⊥ = ⊥)
    (compare : ∀ x y, compare (f x) (f y) = compare x y) :
    LinearOrderedCommMonoidWithZero β where
  __ := hf.linearOrder f le lt hinf hsup compare
  __ := hf.commMonoidWithZero f zero one mul npow
  __ := Function.Injective.posMulStrictMono f zero mul lt
  isBot_zero _ := le.1 <| zero ▸ zero_le
  bot_le _ := le.1 <| bot ▸ bot_le
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) LinearOrderedCommMonoidWithZero.toIsMulTorsionFree :
    IsMulTorsionFree α where
  pow_left_injective n hn := by simpa using (pow_left_strictMonoOn₀ (M₀ := α) hn).injOn
/-
**instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual** 是 Mathlib 中的一个实例，位于命名
空间 ``。
形式化陈述：instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual : LinearOrderedAddC
ommMonoidWithTop (Additive αᵒᵈ) where top_add' a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual :
    LinearOrderedAddCommMonoidWithTop (Additive αᵒᵈ) where
  top_add' a := by ext; simp [bot_eq_zero]
  isAddLeftRegular_of_ne_top := by simp +contextual [IsRegular.of_ne_zero, bot_eq_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**instLinearOrderedAddCommMonoidWithTopOrderDualAdditive** 是 Mathlib 中的一个实例，位于命名
空间 ``。
形式化陈述：instLinearOrderedAddCommMonoidWithTopOrderDualAdditive : LinearOrderedAddC
ommMonoidWithTop (Additive α)ᵒᵈ where top_add' a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrderedAddCommMonoidWithTopOrderDualAdditive :
    LinearOrderedAddCommMonoidWithTop (Additive α)ᵒᵈ where
  top_add' a := by ext; simp; simp [bot_eq_zero (α := α)]
  isAddLeftRegular_of_ne_top := by simp; simp +contextual [bot_eq_zero, IsRegular.of_ne_zero]

variable [IsReduced α]
/-
**pow_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_pos_iff (hn : n != 0) : 0 < a ^ n ↔ 0 < a
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_ne_zero_iff`：pow_ne_zero_iff (hn : n != 0) : a ^ n != 0 ↔ a != 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pow_pos_iff (hn : n ≠ 0) : 0 < a ^ n ↔ 0 < a := by
  simp_rw [pos_iff_ne_zero, pow_ne_zero_iff hn]

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero
variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

@[simp]
/-
**Units.zero_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.zero_lt (u : αˣ) : (0 : α) < u
参数：u : αˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  u.ne_zero.pos
/-
**mul_inv_lt_of_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_inv_lt_of_lt_mul₀ (h : a < b * c) : a * c⁻¹ < b := by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul₀ zero_le zero_le h
/-
**inv_mul_lt_of_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Group α] [inst_1 : LT α] [MulLeftStrictMono α] {a b
 c : α}, a < b * c → b⁻¹ * a < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_mul_lt_iff_lt_mul`：inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c
-/
theorem inv_mul_lt_of_lt_mul₀ (h : a < b * c) : b⁻¹ * a < c := by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h
/-
**lt_of_mul_lt_mul_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d := by
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  rw [← inv_le_inv₀ ha.pos hc] at hh
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ hc.ne']
    using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hh h zero_le (inv_pos.2 hc)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) where
  top_add' := by simp
  neg_top := by ext; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrderedAddCommGroupWithTop (Additive α)ᵒᵈ where
  top_add' := by simp
  neg_top := by ext; simp; simp [bot_eq_zero]
  add_neg_cancel_of_ne_top := by
    simp
    simp +contextual [bot_eq_zero, Additive.ext_iff, OrderDual.ext_iff, -Additive.toMul_eq_top,
      -ofDual_eq_zero]

-- Counterexample with monoid for the backward direction:
-- Take `Mᵐ⁰` where `M := ℚ ×ₗ ℕ`.
/-
**denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units : DenselyOrde
red α ↔ Nontrivial αˣ ∧ DenselyOrdered αˣ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.val_lt_val`：val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α
) < b ↔ a < b
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `exists_one_lt'`：exists_one_lt' [Nontrivial α] : exists a : α, 1 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 31 条，此处仅展示前 30 条）
-/
lemma denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units :
    DenselyOrdered α ↔ Nontrivial αˣ ∧ DenselyOrdered αˣ := by
  refine ⟨fun H ↦ ⟨?_, ?_⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_between (zero_lt_one' α)
    exact ⟨Units.mk0 x hx.ne', 1, by simpa [Units.ext_iff] using hx'.ne⟩
  · refine ⟨fun x y h ↦ ?_⟩
    obtain ⟨z, hz⟩ := exists_between (Units.val_lt_val.mpr h)
    refine ⟨Units.mk0 z (ne_zero_of_lt hz.1), by simp [← Units.val_lt_val, hz]⟩
  · refine ⟨fun x y h ↦ ?_⟩
    lift y to αˣ using (ne_zero_of_lt h).isUnit
    obtain rfl | hx := eq_zero_or_pos x
    · obtain ⟨z, hz⟩ := exists_one_lt' (α := αˣ)
      exact ⟨(y * z⁻¹ : αˣ), by simp, Units.val_lt_val.mpr <| by simp [hz]⟩
    · lift x to αˣ using hx.ne'.isUnit
      obtain ⟨z, hz, hz'⟩ := H₂.dense x y (Units.val_lt_val.mpr h)
      exact ⟨z, by simp [hz, hz']⟩

-- Counterexample with monoid: `{ x : ℝ | 0 ≤ x ≤ 1 }`
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DenselyOrdered α] : Nontrivial αˣ := by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

-- Counterexample with monoid:
-- `{ x : ℝ | x = 0 ∨ ∃ (a : ℤ) (b c : ℕ), x = Real.exp (a + b * √2 - c * √3) }`
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DenselyOrdered α] : DenselyOrdered αˣ := by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto
/-
**denselyOrdered_units_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：denselyOrdered_units_iff [Nontrivial αˣ] : DenselyOrdered αˣ ↔ DenselyOrde
red α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units`：denselyOrd
ered_iff_denselyOrdered_units_and_nontrivial_units : DenselyOrdered α ↔ Nontrivi
al αˣ ∧ DenselyOrdered αˣ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma denselyOrdered_units_iff [Nontrivial αˣ] : DenselyOrdered αˣ ↔ DenselyOrdered α := by
  have := denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units (α := α)
  tauto

end LinearOrderedCommGroupWithZero

/-
**instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual** 是 Mathlib 中的一个实例，
位于命名空间 ``。
形式化陈述：instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual [LinearOrderedA
ddCommMonoidWithTop α] : LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) wh
ere zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual
    [LinearOrderedAddCommMonoidWithTop α] :
    LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) where
  zero := .ofAdd <| .toDual ⊤
  zero_mul := @top_add _ (_)
  mul_zero := @add_top _ (_)
  isBot_zero _ := (le_top : _ ≤ ⊤)
  mul_lt_mul_of_pos_left := by
    simpa [← ofAdd_add, ← toDual_add]
      using! fun a ha b c hbc ↦ add_right_strictMono_of_ne_top (by simpa using! ha.ne') hbc

@[simp]
/-
**ofDual_toAdd_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_toAdd_zero [LinearOrderedAddCommMonoidWithTop α] : OrderDual.ofDual
 (0 : Multiplicative αᵒᵈ).toAdd = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_toAdd_zero [LinearOrderedAddCommMonoidWithTop α] :
    OrderDual.ofDual (0 : Multiplicative αᵒᵈ).toAdd = ⊤ := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrderedAddCommGroupWithTop α] :
    LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ) where
  inv_zero := LinearOrderedAddCommGroupWithTop.neg_top (α := α)
  mul_inv_cancel := LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top (α := α)

namespace WithZero

section Bot

/-
**WithZero.instBot** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instBot : Bot (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBot : Bot (WithZero α) :=
  ⟨none⟩

@[simp← ]
/-
**WithZero.zero_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：zero_eq_bot : (0 : WithZero α) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_eq_bot : (0 : WithZero α) = ⊥ := rfl

end Bot

section LE
variable [LE α] {x y : WithZero α} {a b : α}

/-
**WithZero.** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) le : LE (WithZero α) := inferInstanceAs <| LE (WithBot α)
/-
**WithZero.le_def** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_def : x <= y ↔ forall a : α, x = ↑a -> exists b : α, y = ↑b ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.le_iff_forall`：le_iff_forall : x <= y ↔ forall a : α, x = ↑a -> 
exists b : α, y = ↑b ∧ a <= b
-/
lemma le_def : x ≤ y ↔ ∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b := WithBot.le_iff_forall
/-
**WithZero.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
@[simp, norm_cast] lemma coe_le_coe : (a : WithZero α) ≤ b ↔ a ≤ b := WithBot.coe_le_coe
/-
**WithZero.not_coe_le_zero** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：not_coe_le_zero (a : α) : ¬(a : WithZero α) <= 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.not_coe_le_bot`：not_coe_le_bot (a : α) : ¬(a : WithBot α) <= ⊥
-/
lemma not_coe_le_zero (a : α) : ¬(a : WithZero α) ≤ 0 := WithBot.not_coe_le_bot _
/-
**WithZero.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instOrderBot : OrderBot (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot : OrderBot (WithZero α) := inferInstanceAs <| OrderBot (WithBot α)
/-
**WithZero.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instBoundedOrder [OrderTop α] : BoundedOrder (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder [OrderTop α] : BoundedOrder (WithZero α) :=
  inferInstanceAs <| BoundedOrder (WithBot α)
/-
**WithZero.** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsBotZeroClass (WithZero α) where
  isBot_zero _ := bot_le

@[deprecated _root_.zero_le (since := "2026-05-06")]
/-
**WithZero.zero_le** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] (a : WithZero α), 0 ≤ a
参数：a : WithZero α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
-/
protected lemma zero_le (a : WithZero α) : 0 ≤ a := by simp

/-- There is a general version `le_zero_iff`, but this lemma does not require a `PartialOrder`. -/
@[simp]
/-
**WithZero.nonpos_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] {x : WithZero α}, x ≤ 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.le_bot_iff`：∀ {α : Type u_1} [inst : LE α] {x : WithBot α}, x ≤ 
⊥ ↔ x = ⊥

--- 原说明 ---
There is a general version `le_zero_iff`, but this lemma does not require a `Par
tialOrder`.
-/
protected lemma nonpos_iff_eq_zero : x ≤ 0 ↔ x = 0 := WithBot.le_bot_iff
/-
**WithZero.coe_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：coe_le_iff : a <= x ↔ exists b : α, x = b ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.coe_le_iff`：coe_le_iff : a <= x ↔ exists b : α, x = b ∧ a <= b
-/
lemma coe_le_iff : a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b := WithBot.coe_le_iff
/-
**WithZero.le_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_coe_iff : x <= b ↔ forall a : α, x = ↑a -> a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.le_coe_iff`：le_coe_iff : x <= b ↔ forall a : α, x = ↑a -> a <= b
-/
lemma le_coe_iff : x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b := WithBot.le_coe_iff
/-
**WithZero._root_.IsMax.withZero** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.IsMax.withZero (h : IsMax a) : IsMax (a : WithZero α) := h.withBot
/-
**WithZero.le_unzero_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_unzero_iff (hy : y != 0) : a <= unzero hy ↔ a <= y
参数：hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.le_unbot_iff`：le_unbot_iff (hx : x != ⊥) : a <= unbot x hx ↔ a <
= x
-/
lemma le_unzero_iff (hy : y ≠ 0) : a ≤ unzero hy ↔ a ≤ y := WithBot.le_unbot_iff _
/-
**WithZero.unbot_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：unbot_le_iff (hx : x != 0) : unzero hx <= b ↔ x <= b
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.unbot_le_iff`：unbot_le_iff (hx : x != ⊥) : unbot x hx <= a ↔ x <
= a
-/
lemma unbot_le_iff (hx : x ≠ 0) : unzero hx ≤ b ↔ x ≤ b := WithBot.unbot_le_iff _
/-
**WithZero.one_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] {a : α} [inst_1 : One α], 1 ≤ ↑a ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
-/
@[simp, norm_cast] lemma one_le_coe [One α] : 1 ≤ (a : WithZero α) ↔ 1 ≤ a := coe_le_coe
/-
**WithZero.coe_le_one** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] {a : α} [inst_1 : One α], ↑a ≤ 1 ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
-/
@[simp, norm_cast] lemma coe_le_one [One α] : (a : WithZero α) ≤ 1 ↔ a ≤ 1 := coe_le_coe
/-
**WithZero.unzero_le_unzero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] {x y : WithZero α} (hx : x ≠ 0) (hy : y ≠ 0
),   WithZero.unzero hx ≤ WithZero.unzero hy ↔ x ≤ y
参数：hx : x ≠ 0；hy : y ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.unbot_le_unbot_iff`：unbot_le_unbot_iff (hx : x != ⊥) (hy : y != 
⊥) : x.unbot hx <= y.unbot hy ↔ x <= y
-/
@[simp] lemma unzero_le_unzero (hx : x ≠ 0) (hy : y ≠ 0) : unzero hx ≤ unzero hy ↔ x ≤ y :=
  WithBot.unbot_le_unbot_iff ..

end LE

section LT

variable [LT α] {x y : WithZero α} {a b : α}

/-- The order on `WithZero α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`. -/
/-
**WithZero.** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order on `WithZero α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`.
-/
instance (priority := 10) instLT : LT (WithZero α) := inferInstanceAs <| LT (WithBot α)
/-
**WithZero.lt_def** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_def : x < y ↔ x = 0 ∧ (exists b : α, y = b) ∨ exists a b : α, a < b ∧ x
 = ↑a ∧ y = ↑b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.lt_def`：WithBot.lt_def {x y : WithBot α} : x < y ↔ (x = ⊥ ∧ exis
ts b : α, y = b) ∨ exists a b : α, a < b ∧ x = a ∧ y = b
-/
lemma lt_def : x < y ↔ x = 0 ∧ (∃ b : α, y = b) ∨ ∃ a b : α, a < b ∧ x = ↑a ∧ y = ↑b :=
  WithBot.lt_def
/-
**WithZero.lt_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_iff_exists : x < y ↔ exists b : α, y = ↑b ∧ forall a : α, x = ↑a -> a <
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.lt_iff_exists`：lt_iff_exists : x < y ↔ exists b : α, y = ↑b ∧ fo
rall a : α, x = ↑a -> a < b
-/
lemma lt_iff_exists : x < y ↔ ∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b := WithBot.lt_iff_exists
/-
**WithZero.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] {a b : α}, ↑a < ↑b ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma coe_lt_coe : (a : WithZero α) < b ↔ a < b := by simp [lt_def]
/-
**WithZero.zero_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] (a : α), 0 < ↑a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
@[simp] lemma zero_lt_coe (a : α) : 0 < (a : WithZero α) := by simp [lt_def]
/-
**WithZero.not_lt_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] (a : WithZero α), ¬a < 0
参数：a : WithZero α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] protected lemma not_lt_zero (a : WithZero α) : ¬a < 0 := by simp [lt_def]
/-
**WithZero.lt_iff_exists_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_iff_exists_coe : x < y ↔ exists b : α, y = b ∧ x < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.lt_iff_exists_coe`：lt_iff_exists_coe : x < y ↔ exists b : α, y =
 b ∧ x < b
-/
lemma lt_iff_exists_coe : x < y ↔ ∃ b : α, y = b ∧ x < b := WithBot.lt_iff_exists_coe
/-
**WithZero.lt_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_coe_iff : x < b ↔ forall a : α, x = a -> a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.lt_coe_iff`：lt_coe_iff : x < b ↔ forall a : α, x = a -> a < b
-/
lemma lt_coe_iff : x < b ↔ ∀ a : α, x = a → a < b := WithBot.lt_coe_iff

/-- A version of `pos_iff_ne_zero` for `WithZero` that only requires `LT α`,
not `PartialOrder α`. -/
/-
**WithZero.pos_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] {x : WithZero α}, 0 < x ↔ x ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithBot.bot_lt_iff_ne_bot`：∀ {α : Type u_1} [inst : LT α] {x : WithBot α
}, ⊥ < x ↔ x ≠ ⊥

--- 原说明 ---
A version of `pos_iff_ne_zero` for `WithZero` that only requires `LT α`,
not `PartialOrder α`.
-/
protected lemma pos_iff_ne_zero : 0 < x ↔ x ≠ 0 := WithBot.bot_lt_iff_ne_bot
/-
**WithZero.lt_unzero_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_unzero_iff (hy : y != 0) : a < unzero hy ↔ a < y
参数：hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.lt_unbot_iff`：lt_unbot_iff (hx : x != ⊥) : a < unbot x hx ↔ a < 
x
-/
lemma lt_unzero_iff (hy : y ≠ 0) : a < unzero hy ↔ a < y := WithBot.lt_unbot_iff _
/-
**WithZero.unzero_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：unzero_lt_iff (hx : x != 0) : unzero hx < b ↔ x < b
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.unbot_lt_iff`：unbot_lt_iff (hx : x != ⊥) : unbot x hx < b ↔ x < 
b
-/
lemma unzero_lt_iff (hx : x ≠ 0) : unzero hx < b ↔ x < b := WithBot.unbot_lt_iff _
/-
**WithZero.one_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] {a : α} [inst_1 : One α], 1 < ↑a ↔ 1 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.coe_lt_coe`：∀ {α : Type u_1} [inst : LT α] {a b : α}, ↑a < ↑b ↔
 a < b
-/
@[simp, norm_cast] lemma one_lt_coe [One α] : 1 < (a : WithZero α) ↔ 1 < a := coe_lt_coe
/-
**WithZero.coe_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LT α] {a : α} [inst_1 : One α], ↑a < 1 ↔ a < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.coe_lt_coe`：∀ {α : Type u_1} [inst : LT α] {a b : α}, ↑a < ↑b ↔
 a < b
-/
@[simp, norm_cast] lemma coe_lt_one [One α] : (a : WithZero α) < 1 ↔ a < 1 := coe_lt_coe

end LT

section Preorder

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

/-
**WithZero.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instPreorder : Preorder (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorder : Preorder (WithZero α) := inferInstanceAs <| Preorder (WithBot α)
/-
**WithZero.instMulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instMulLeftMono [Mul α] [MulLeftMono α] : MulLeftMono (WithZero α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithZero.coe_le_iff`：coe_le_iff : a <= x ↔ exists b : α, x = b ∧ a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.coe_mul`：∀ {α : Type u_1} [inst : Mul α] (a b : α), ↑(a * b) = 
↑a * ↑b
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
instance instMulLeftMono [Mul α] [MulLeftMono α] :
    MulLeftMono (WithZero α) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a; · exact zero_le
  induction b; · exact zero_le
  rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul _ c, ← coe_mul, coe_le_coe]
  exact mul_le_mul_right hbc' _
/-
**WithZero.addLeftMono** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : AddZeroClass α] [AddLeftMon
o α],   (∀ (a : α), 0 ≤ a) → AddLeftMono (WithZero α)
参数：∀ (a : α), 0 ≤ a；WithZero α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a
 + ↑b
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithZero.coe_le_iff`：coe_le_iff : a <= x ↔ exists b : α, x = b ∧ a <= b
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
-/
protected lemma addLeftMono [AddZeroClass α] [AddLeftMono α]
    (h : ∀ a : α, 0 ≤ a) : AddLeftMono (WithZero α) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a
  · rwa [zero_add, zero_add]
  induction b
  · rw [add_zero]
    induction c
    · rw [add_zero]
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithZero.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add, ← coe_add _ c, coe_le_coe]
    gcongr
/-
**WithZero.instExistsAddOfLE** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instExistsAddOfLE [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithZero α) w
here exists_add_of_le {a b}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance instExistsAddOfLE [Add α] [ExistsAddOfLE α] : ExistsAddOfLE (WithZero α) where
  exists_add_of_le {a b} := by
    induction a
    · simp
    induction b
    · simp
    intro h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩
/-
**WithZero.map'_mono** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : MulOneClass α]   [inst_3 : MulOneClass β] {f : α →* β}, Monotone ⇑f → 
Monotone ⇑(WithZero.map' f)
参数：WithZero.map' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma map'_mono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : Monotone f) :
    Monotone (map' f) := by simpa [Monotone, WithZero.forall]
/-
**WithZero.map'_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : MulOneClass α]   [inst_3 : MulOneClass β] {f : α →* β}, StrictMono ⇑f 
→ StrictMono ⇑(WithZero.map' f)
参数：WithZero.map' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma map'_strictMono [MulOneClass α] [MulOneClass β] {f : α →* β} (hf : StrictMono f) :
    StrictMono (map' f) := by simpa [StrictMono, WithZero.forall]
/-
**WithZero.exists_ne_zero_and_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：exists_ne_zero_and_lt [NoMinOrder α] (hx : x != 0) : exists y, y != 0 ∧ y 
< x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.coe_lt_coe`：∀ {α : Type u_1} [inst : LT α] {a b : α}, ↑a < ↑b ↔
 a < b
-/
theorem exists_ne_zero_and_lt [NoMinOrder α] (hx : x ≠ 0) :
    ∃ y, y ≠ 0 ∧ y < x := by
  obtain ⟨z, hlt⟩ := exists_lt (WithZero.unzero hx)
  rw [← WithZero.coe_lt_coe, WithZero.coe_unzero hx] at hlt
  exact ⟨z, WithZero.coe_ne_zero, hlt⟩

section Multiplicative

open Multiplicative

/-
**WithZero.toAdd_unzero_lt_of_lt_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toAdd_unzero_lt_of_lt_ofAdd {a : WithZero (Multiplicative α)} {b : α} (ha 
: a != 0) (h : a < ofAdd b) : toAdd (unzero ha) < b
参数：Multiplicative α；ha : a != 0；h : a < ofAdd b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toAdd_ofAdd`：toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiplicative.toAdd_lt`：toAdd_lt {a b : Multiplicative α} : a.toAdd < b
.toAdd ↔ a < b
· 使用定理 `WithZero.coe_lt_coe`：∀ {α : Type u_1} [inst : LT α] {a b : α}, ↑a < ↑b ↔
 a < b
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
-/
theorem toAdd_unzero_lt_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a < ofAdd b) :
    toAdd (unzero ha) < b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← toAdd_lt, toAdd_ofAdd] at h
/-
**WithZero.lt_ofAdd_of_toAdd_unzero_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：lt_ofAdd_of_toAdd_unzero_lt {a : WithZero (Multiplicative α)} {b : α} (ha 
: a != 0) (h : toAdd (unzero ha) < b) : a < ofAdd b
参数：Multiplicative α；ha : a != 0；h : toAdd (unzero ha) < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
· 使用定理 `WithZero.coe_lt_coe`：∀ {α : Type u_1} [inst : LT α] {a b : α}, ↑a < ↑b ↔
 a < b
· 使用定理 `ofAdd_toAdd`：ofAdd_toAdd (x : Multiplicative α) : ofAdd x.toAdd = x
· 使用定理 `Multiplicative.ofAdd_lt`：ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b
-/
theorem lt_ofAdd_of_toAdd_unzero_lt
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : toAdd (unzero ha) < b) :
    a < ofAdd b := by
  rwa [← coe_unzero ha, coe_lt_coe, ← ofAdd_toAdd (unzero ha), ofAdd_lt]
/-
**WithZero.lt_ofAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：lt_ofAdd_iff {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) : a <
 ofAdd b ↔ toAdd (unzero ha) < b
参数：Multiplicative α；ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.toAdd_unzero_lt_of_lt_ofAdd`：toAdd_unzero_lt_of_lt_ofAdd {a : W
ithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : a < ofAdd b) : toAdd (unz
ero ha) < b
· 使用定理 `WithZero.lt_ofAdd_of_toAdd_unzero_lt`：lt_ofAdd_of_toAdd_unzero_lt {a : W
ithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : toAdd (unzero ha) < b) : 
a < ofAdd b
-/
theorem lt_ofAdd_iff
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) :
    a < ofAdd b ↔ toAdd (unzero ha) < b :=
  ⟨toAdd_unzero_lt_of_lt_ofAdd ha, lt_ofAdd_of_toAdd_unzero_lt ha⟩
/-
**WithZero.toAdd_unzero_le_of_lt_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：toAdd_unzero_le_of_lt_ofAdd {a : WithZero (Multiplicative α)} {b : α} (ha 
: a != 0) (h : a <= ofAdd b) : toAdd (unzero ha) <= b
参数：Multiplicative α；ha : a != 0；h : a <= ofAdd b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toAdd_ofAdd`：toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiplicative.toAdd_le`：toAdd_le {a b : Multiplicative α} : a.toAdd <= 
b.toAdd ↔ a <= b
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
-/
theorem toAdd_unzero_le_of_lt_ofAdd
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : a ≤ ofAdd b) :
    toAdd (unzero ha) ≤ b := by
  rwa [← coe_unzero ha, coe_le_coe, ← toAdd_le, toAdd_ofAdd] at h
/-
**WithZero.le_ofAdd_of_toAdd_unzero_le** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：le_ofAdd_of_toAdd_unzero_le {a : WithZero (Multiplicative α)} {b : α} (ha 
: a != 0) (h : toAdd (unzero ha) <= b) : a <= ofAdd b
参数：Multiplicative α；ha : a != 0；h : toAdd (unzero ha) <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
· 使用定理 `ofAdd_toAdd`：ofAdd_toAdd (x : Multiplicative α) : ofAdd x.toAdd = x
· 使用定理 `Multiplicative.ofAdd_le`：ofAdd_le {a b : α} : ofAdd a <= ofAdd b ↔ a <= 
b
-/
theorem le_ofAdd_of_toAdd_unzero_le
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) (h : toAdd (unzero ha) ≤ b) :
    a ≤ ofAdd b := by
  rwa [← coe_unzero ha, coe_le_coe, ← ofAdd_toAdd (unzero ha), ofAdd_le]
/-
**WithZero.le_ofAdd_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：le_ofAdd_iff {a : WithZero (Multiplicative α)} {b : α} (ha : a != 0) : a <
= ofAdd b ↔ toAdd (unzero ha) <= b
参数：Multiplicative α；ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.toAdd_unzero_le_of_lt_ofAdd`：toAdd_unzero_le_of_lt_ofAdd {a : W
ithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : a <= ofAdd b) : toAdd (un
zero ha) <= b
· 使用定理 `WithZero.le_ofAdd_of_toAdd_unzero_le`：le_ofAdd_of_toAdd_unzero_le {a : W
ithZero (Multiplicative α)} {b : α} (ha : a != 0) (h : toAdd (unzero ha) <= b) :
 a <= ofAdd b
-/
theorem le_ofAdd_iff
    {a : WithZero (Multiplicative α)} {b : α} (ha : a ≠ 0) :
    a ≤ ofAdd b ↔ toAdd (unzero ha) ≤ b :=
  ⟨toAdd_unzero_le_of_lt_ofAdd ha, le_ofAdd_of_toAdd_unzero_le ha⟩
/-
**WithZero.toAdd_unzero_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：toAdd_unzero_eq_iff {α : Type*} {a : WithZero (Multiplicative α)} (h : a !
= 0) (b : α) : (WithZero.unzero h).toAdd = b ↔ a = Multiplicative.ofAdd b
参数：Multiplicative α；h : a != 0；b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
-/
lemma toAdd_unzero_eq_iff {α : Type*} {a : WithZero (Multiplicative α)} (h : a ≠ 0)
    (b : α) : (WithZero.unzero h).toAdd = b ↔ a = Multiplicative.ofAdd b :=
  ⟨fun k ↦ by subst k; exact (coe_unzero h).symm, fun k ↦ by subst k; rfl⟩

end Multiplicative

end Preorder

section PartialOrder
variable [PartialOrder α]

/-
**WithZero.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instPartialOrder : PartialOrder (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder (WithZero α) :=
  inferInstanceAs <| PartialOrder (WithBot α)
/-
**WithZero.instMulLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instMulLeftReflectLT [Mul α] [MulLeftReflectLT α] : MulLeftReflectLT (With
Zero α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithZero.zero_lt_coe`：∀ {α : Type u_1} [inst : LT α] (a : α), 0 < ↑a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithZero.coe_lt_coe`：∀ {α : Type u_1} [inst : LT α] {a b : α}, ↑a < ↑b ↔
 a < b
· 使用定理 `lt_of_mul_lt_mul_left'`：lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b
 c : α} (bc : a * b < a * c) : b < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
instance instMulLeftReflectLT [Mul α] [MulLeftReflectLT α] :
    MulLeftReflectLT (WithZero α) := by
  refine ⟨fun a b c h => ?_⟩
  have := h.ne_zero
  induction a
  · simp at this
  induction c
  · simp at this
  induction b
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

end PartialOrder


section Lattice

/-
**WithZero.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithZero α) where sup 
-- note this is `Option.merge`, but with the right defeq when unfolding | 0, 0 =
> 0 | (a : α), 0 => a | 0, (b : α) => b | (a : α), (b : α) => ↑(a ⊔ b) le_sup_le
ft x y
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithZero α) where
  sup
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | 0, 0 => 0
    | (a : α), 0 => a
    | 0, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊔ b)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le
/-
**WithZero.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithZero α) = (a : W
ithZero α) ⊔ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithZero α) = (a : WithZero α) ⊔ b :=
  rfl
/-
**WithZero.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithZero α) where inf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithZero α) where
  inf := .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf
/-
**WithZero.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithZero α) = (a : W
ithZero α) ⊓ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithZero α) = (a : WithZero α) ⊓ b :=
  rfl
/-
**WithZero.instLattice** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [Lattice α] → Lattice (WithZero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice [Lattice α] : Lattice (WithZero α) where

end Lattice

/-
**WithZero.decidableEq** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：decidableEq [DecidableEq α] : DecidableEq (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEq [DecidableEq α] : DecidableEq (WithZero α) :=
  inferInstanceAs <| DecidableEq (Option α)
/-
**WithZero.decidableLE** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → [DecidableLE α] → DecidableLE (With
Zero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLE [Preorder α] [DecidableLE α] : DecidableLE (WithZero α)
  | 0, _ => isTrue <| by simp
  | (a : α), 0 => isFalse <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe
/-
**WithZero.decidableLT** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → [DecidableLT α] → DecidableLT (With
Zero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableLT [Preorder α] [DecidableLT α] : DecidableLT (WithZero α)
  | _, 0 => isFalse <| by simp
  | 0, (a : α) => isTrue <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe
/-
**WithZero.total_le** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：total_le [Preorder α] [@Std.Total α (· <= ·)] : @Std.Total (WithZero α) (·
 <= ·) where total x y
参数：· <= ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
instance total_le [Preorder α] [@Std.Total α (· ≤ ·)] : @Std.Total (WithZero α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

section LinearOrder
variable [LinearOrder α] {a b c : α} {x y : WithZero α}

/-
**WithZero.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instLinearOrder : LinearOrder (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrder : LinearOrder (WithZero α) := Lattice.toLinearOrder _
/-
**WithZero.le_max_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, ↑a ≤ max ↑b ↑c ↔ a ≤ 
max b c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma le_max_iff : (a : WithZero α) ≤ max (b : WithZero α) c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]
/-
**WithZero.min_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, min ↑a ↑b ≤ ↑c ↔ min 
a b ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma min_le_iff : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]
/-
**WithZero.exists_ne_zero_and_le_and_le** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：exists_ne_zero_and_le_and_le (hx : x != 0) (hy : y != 0) : exists z, z != 
0 ∧ z <= x ∧ z <= y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem exists_ne_zero_and_le_and_le (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z ≤ x ∧ z ≤ y :=
  ⟨x ⊓ y, by simp [min_eq_iff, hx, hy], by simp, by simp⟩
/-
**WithZero.exists_ne_zero_and_lt_and_lt** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：exists_ne_zero_and_lt_and_lt [NoMinOrder α] (hx : x != 0) (hy : y != 0) : 
exists z, z != 0 ∧ z < x ∧ z < y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.exists_ne_zero_and_le_and_le`：exists_ne_zero_and_le_and_le (hx 
: x != 0) (hy : y != 0) : exists z, z != 0 ∧ z <= x ∧ z <= y
· 使用定理 `WithZero.exists_ne_zero_and_lt`：exists_ne_zero_and_lt [NoMinOrder α] (hx
 : x != 0) : exists y, y != 0 ∧ y < x
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem exists_ne_zero_and_lt_and_lt [NoMinOrder α] (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z < x ∧ z < y := by
  obtain ⟨z', hnz', hzx, hzy⟩ := exists_ne_zero_and_le_and_le hx hy
  obtain ⟨z, hnz, hlt⟩ := exists_ne_zero_and_lt hnz'
  use z, hnz
  constructor <;> exact lt_of_lt_of_le hlt ‹z' ≤ _›

end LinearOrder

/-
**WithZero.isOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] : IsOrdere
dMonoid (WithZero α) where mul_le_mul_left _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
instance isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedMonoid (WithZero α) where
  mul_le_mul_left _ _ := mul_le_mul_left

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
/-- If `0` is the least element in `α`, then `WithZero α` is an ordered `AddMonoid`. -/
-- See note [reducible non-instances]
/-
**WithZero.isOrderedAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredAddMonoid α],   (∀ (a : α), 0 ≤ a) → IsOrderedAddMonoid (WithZero α)
参数：∀ (a : α), 0 ≤ a；WithZero α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.addLeftMono`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Add
ZeroClass α] [AddLeftMono α],   (∀ (a : α), 0 ≤ a) → AddLeftMono (WithZero α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected lemma isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (zero_le : ∀ a : α, 0 ≤ a) :
    IsOrderedAddMonoid (WithZero α) := by
  have := WithZero.addLeftMono zero_le
  exact ⟨fun _ _ ↦ add_le_add_left, by simpa [add_comm] using fun _ _ ↦ add_le_add_left⟩

/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
/-
**WithZero.instCanonicallyOrderedAdd** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] [Canonicall
yOrderedAdd α],   CanonicallyOrderedAdd (WithZero α)
参数：WithZero α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithZero.coe_le_coe`：∀ {α : Type u_1} [inst : LE α] {a b : α}, ↑a ≤ ↑b ↔
 a ≤ b
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b

--- 原说明 ---
Adding a new zero to a canonically ordered additive monoid produces another one.
-/
instance instCanonicallyOrderedAdd [AddZeroClass α] [Preorder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedAdd (WithZero α) where
  le_add_self
  | 0, _ => bot_le
  | (a : α), 0 => le_rfl
  | (a : α), (b : α) => WithZero.coe_le_coe.2 le_add_self
  le_self_add
  | 0, _ => bot_le
  | (a : α), 0 => le_rfl
  | (a : α), (b : α) => WithZero.coe_le_coe.2 le_self_add
/-
**WithZero.instLinearOrderedCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithZe
ro`。
形式化陈述：instLinearOrderedCommMonoidWithZero [CommMonoid α] [LinearOrder α] [IsOrde
redCancelMonoid α] : LinearOrderedCommMonoidWithZero (WithZero α) where isBot_ze
ro _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrderedCommMonoidWithZero [CommMonoid α] [LinearOrder α]
    [IsOrderedCancelMonoid α] : LinearOrderedCommMonoidWithZero (WithZero α) where
  isBot_zero _ := zero_le
  mul_lt_mul_of_pos_left
  | (a : α), _, 0, (c : α), _ => by simp [← WithZero.coe_mul]
  | (a : α), _, (b : α), (c : α), hbc => by norm_cast at *; exact mul_lt_mul_right hbc _
/-
**WithZero.instLinearOrderedCommGroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `WithZer
o`。
形式化陈述：{α : Type u_1} →   [inst : CommGroup α] → [inst_1 : LinearOrder α] → [IsOr
deredMonoid α] → LinearOrderedCommGroupWithZero (WithZero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrderedCommGroupWithZero [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] :
    LinearOrderedCommGroupWithZero (WithZero α) where

-- Add a shortcut instance for the common case, to speed up unification.
/-
**WithZero.** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrderedCommGroupWithZero ℤᵐ⁰ := inferInstance

/-! ### Exponential and logarithm -/

variable {G : Type*} [Preorder G] {a b : G}

/-
**WithZero.exp_le_exp** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_3} [inst : Preorder G] {a b : G}, WithZero.exp a ≤ WithZero.
exp b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma exp_le_exp : exp a ≤ exp b ↔ a ≤ b := by simp [exp]
/-
**WithZero.exp_lt_exp** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_3} [inst : Preorder G] {a b : G}, WithZero.exp a < WithZero.
exp b ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma exp_lt_exp : exp a < exp b ↔ a < b := by simp [exp]
/-
**WithZero.exp_pos** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_3} [inst : Preorder G] {a : G}, 0 < WithZero.exp a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
@[simp] lemma exp_pos : 0 < exp a := by simp [exp]

variable [AddGroup G] {x y : Gᵐ⁰}
/-
**WithZero.log_le_iff_le_exp** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：log_le_iff_le_exp (hx : x != 0) : log x <= a ↔ x <= exp a
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.toAdd_unzero_eq_log`：toAdd_unzero_eq_log {x : Mᵐ⁰} (hx : x != 0
) : (unzero hx).toAdd = log x
· 使用定理 `WithZero.le_ofAdd_iff`：le_ofAdd_iff {a : WithZero (Multiplicative α)} {b
 : α} (ha : a != 0) : a <= ofAdd b ↔ toAdd (unzero ha) <= b
· 使用定理 `WithZero.exp.eq_1`：∀ {M : Type u_4} (a : M), WithZero.exp a = ↑(Multipli
cative.ofAdd a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma log_le_iff_le_exp (hx : x ≠ 0) : log x ≤ a ↔ x ≤ exp a := by
  rw [← toAdd_unzero_eq_log hx, ← le_ofAdd_iff hx, exp]
/-
**WithZero.log_lt_iff_lt_exp** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：log_lt_iff_lt_exp (hx : x != 0) : log x < a ↔ x < exp a
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.toAdd_unzero_eq_log`：toAdd_unzero_eq_log {x : Mᵐ⁰} (hx : x != 0
) : (unzero hx).toAdd = log x
· 使用定理 `WithZero.lt_ofAdd_iff`：lt_ofAdd_iff {a : WithZero (Multiplicative α)} {b
 : α} (ha : a != 0) : a < ofAdd b ↔ toAdd (unzero ha) < b
· 使用定理 `WithZero.exp.eq_1`：∀ {M : Type u_4} (a : M), WithZero.exp a = ↑(Multipli
cative.ofAdd a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma log_lt_iff_lt_exp (hx : x ≠ 0) : log x < a ↔ x < exp a := by
  rw [← toAdd_unzero_eq_log hx, ← lt_ofAdd_iff hx, exp]
/-
**WithZero.log_le_log** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddGroup G] {x y : WithZero
 (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log ≤ y.log ↔ x ≤ y)
参数：Multiplicative G；x.log ≤ y.log ↔ x ≤ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithZero.log_le_iff_le_exp`：log_le_iff_le_exp (hx : x != 0) : log x <= a
 ↔ x <= exp a
· 使用定理 `WithZero.exp_log`：∀ {M : Type u_4} [inst : AddMonoid M] {x : WithZero (M
ultiplicative M)}, x ≠ 0 → WithZero.exp x.log = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma log_le_log (hx : x ≠ 0) (hy : y ≠ 0) : log x ≤ log y ↔ x ≤ y := by
  rw [log_le_iff_le_exp hx, exp_log hy]
/-
**WithZero.log_lt_log** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddGroup G] {x y : WithZero
 (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log < y.log ↔ x < y)
参数：Multiplicative G；x.log < y.log ↔ x < y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithZero.log_lt_iff_lt_exp`：log_lt_iff_lt_exp (hx : x != 0) : log x < a 
↔ x < exp a
· 使用定理 `WithZero.exp_log`：∀ {M : Type u_4} [inst : AddMonoid M] {x : WithZero (M
ultiplicative M)}, x ≠ 0 → WithZero.exp x.log = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma log_lt_log (hx : x ≠ 0) (hy : y ≠ 0) : log x < log y ↔ x < y := by
  rw [log_lt_iff_lt_exp hx, exp_log hy]
/-
**WithZero.le_log_iff_exp_le** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_log_iff_exp_le (hx : x != 0) : a <= log x ↔ exp a <= x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.log_le_log`：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddG
roup G] {x y : WithZero (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log ≤ y.log ↔ 
x ≤ y)
· 使用定理 `WithZero.exp_ne_zero`：∀ {M : Type u_4} {a : M}, WithZero.exp a ≠ 0
· 使用定理 `WithZero.log_exp`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M), (WithZe
ro.exp a).log = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_log_iff_exp_le (hx : x ≠ 0) : a ≤ log x ↔ exp a ≤ x := by
  rw [← log_le_log exp_ne_zero hx, log_exp]
/-
**WithZero.lt_log_iff_exp_lt** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_log_iff_exp_lt (hx : x != 0) : a < log x ↔ exp a < x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.log_lt_log`：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddG
roup G] {x y : WithZero (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log < y.log ↔ 
x < y)
· 使用定理 `WithZero.exp_ne_zero`：∀ {M : Type u_4} {a : M}, WithZero.exp a ≠ 0
· 使用定理 `WithZero.log_exp`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M), (WithZe
ro.exp a).log = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_log_iff_exp_lt (hx : x ≠ 0) : a < log x ↔ exp a < x := by
  rw [← log_lt_log exp_ne_zero hx, log_exp]
/-
**WithZero.le_exp_of_log_le** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_exp_of_log_le (hxa : log x <= a) : x <= exp a
参数：hxa : log x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma le_exp_of_log_le (hxa : log x ≤ a) : x ≤ exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_le_iff_le_exp, *]
/-
**WithZero.lt_exp_of_log_lt** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_exp_of_log_lt (hxa : log x < a) : x < exp a
参数：hxa : log x < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma lt_exp_of_log_lt (hxa : log x < a) : x < exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← log_lt_iff_lt_exp, *]
/-
**WithZero.le_log_of_exp_le** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_log_of_exp_le (hax : exp a <= x) : a <= log x
参数：hax : exp a <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithZero.le_log_iff_exp_le`：le_log_iff_exp_le (hx : x != 0) : a <= log x
 ↔ exp a <= x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `WithZero.exp_pos`：∀ {G : Type u_3} [inst : Preorder G] {a : G}, 0 < With
Zero.exp a
-/
lemma le_log_of_exp_le (hax : exp a ≤ x) : a ≤ log x :=
  (le_log_iff_exp_le (exp_pos.trans_le hax).ne').2 hax
/-
**WithZero.lt_log_of_exp_lt** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_log_of_exp_lt (hax : exp a < x) : a < log x
参数：hax : exp a < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithZero.lt_log_iff_exp_lt`：lt_log_iff_exp_lt (hx : x != 0) : a < log x 
↔ exp a < x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `WithZero.exp_pos`：∀ {G : Type u_3} [inst : Preorder G] {a : G}, 0 < With
Zero.exp a
-/
lemma lt_log_of_exp_lt (hax : exp a < x) : a < log x :=
  (lt_log_iff_exp_lt (exp_pos.trans hax).ne').2 hax

/-- The exponential map as an order isomorphism between `G` and `Gᵐ⁰ˣ`. -/
/-
**WithZero.expOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{G : Type u_3} → [inst : Preorder G] → [inst_1 : AddGroup G] → G ≃o (WithZ
ero (Multiplicative G))ˣ
参数：WithZero (Multiplicative G)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exponential map as an order isomorphism between `G` and `Gᵐ⁰ˣ`.
-/
@[simps! -isSimp] def expOrderIso : G ≃o Gᵐ⁰ˣ where
  __ := expEquiv
  map_rel_iff' := by simp [← Units.val_le_val]

/-- The logarithm as an order isomorphism between `Gᵐ⁰ˣ` and `G`. -/
/-
**WithZero.logOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{G : Type u_3} → [inst : Preorder G] → [inst_1 : AddGroup G] → (WithZero (
Multiplicative G))ˣ ≃o G
参数：WithZero (Multiplicative G)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithm as an order isomorphism between `Gᵐ⁰ˣ` and `G`.
-/
@[simps! -isSimp] def logOrderIso : Gᵐ⁰ˣ ≃o G where
  __ := logEquiv
  map_rel_iff' := by simp
/-
**WithZero.lt_mul_exp_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_mul_exp_iff_le {x y : Intᵐ⁰} (hy : y != 0) : x < y * exp 1 ↔ x <= y
参数：hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.log_le_log`：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddG
roup G] {x y : WithZero (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log ≤ y.log ↔ 
x ≤ y)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `WithZero.log_lt_log`：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddG
roup G] {x y : WithZero (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log < y.log ↔ 
x < y)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `WithZero.log_mul`：log_mul {x y : Mᵐ⁰} (hx : x != 0) (hy : y != 0) : log 
(x * y) = log x + log y
-/
lemma lt_mul_exp_iff_le {x y : ℤᵐ⁰} (hy : y ≠ 0) : x < y * exp 1 ↔ x ≤ y := by
  lift y to Multiplicative ℤ using hy
  obtain rfl | hx := eq_or_ne x 0
  · simp
  lift x to Multiplicative ℤ using hx
  rw [← log_le_log, ← log_lt_log] <;> simp [log_mul, Int.lt_add_one_iff]
/-
**WithZero.exists_exp_neg_natCast_lt** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：exists_exp_neg_natCast_lt {x : Intᵐ⁰} (hx : x != 0) : exists (k : Nat), ex
p (-(k : Int)) < x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.exists_ne_zero_and_lt`：exists_ne_zero_and_lt [NoMinOrder α] (hx
 : x != 0) : exists y, y != 0 ∧ y < x
· 使用定理 `LinearOrderedCommGroup.to_noMinOrder`：∀ {α : Type u} [inst : CommGroup α
] [inst_1 : LinearOrder α] [IsOrderedMonoid α] [Nontrivial α], NoMinOrder α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.le_log_iff_exp_le`：le_log_iff_exp_le (hx : x != 0) : a <= log x
 ↔ exp a <= x
· 使用定理 `Int.neg_le_iff`：∀ {x y : ℤ}, -x ≤ y ↔ -y ≤ x
· 使用定理 `Int.self_le_toNat`：∀ (a : ℤ), a ≤ ↑a.toNat
-/
lemma exists_exp_neg_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), exp (-(k : ℤ)) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  use (-y.log).toNat
  apply lt_of_le_of_lt _ hyx
  rw [← WithZero.le_log_iff_exp_le hnz, Int.neg_le_iff]
  exact Int.self_le_toNat _
/-
**WithZero.exists_exp_neg_natCast_lt_and_lt** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`
。
形式化陈述：exists_exp_neg_natCast_lt_and_lt {x y : Intᵐ⁰} (hx : x != 0) (hy : y != 0)
 : exists (k : Nat), exp (-(k : Int)) < x ∧ exp (-(k : Int)) < y
参数：hx : x != 0；hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.exists_ne_zero_and_le_and_le`：exists_ne_zero_and_le_and_le (hx 
: x != 0) (hy : y != 0) : exists z, z != 0 ∧ z <= x ∧ z <= y
· 使用引理 `WithZero.exists_exp_neg_natCast_lt`：exists_exp_neg_natCast_lt {x : Intᵐ⁰
} (hx : x != 0) : exists (k : Nat), exp (-(k : Int)) < x
-/
lemma exists_exp_neg_natCast_lt_and_lt {x y : ℤᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (k : ℕ), exp (-(k : ℤ)) < x ∧ exp (-(k : ℤ)) < y  := by
  obtain ⟨z, hz, hzx, hzy⟩ := WithZero.exists_ne_zero_and_le_and_le hx hy
  obtain ⟨k, hk⟩ := exists_exp_neg_natCast_lt hz
  grind
/-
**WithZero.le_exp_log** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_exp_log {x : Gᵐ⁰} : x <= exp (log x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma le_exp_log {x : Gᵐ⁰} :
    x ≤ exp (log x) := by
  cases x
  · simp
  · rfl

section LE

-- This section is not generated by `to_additive` because `WithOne` does not have a `LE` instance.

variable [LE α] {x y : WithZero α} {a b : α}

/-
**WithZero.le_unzeroD_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_unzeroD_iff (hx : x != 0) : b <= x.unzeroD a ↔ b <= x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_unzeroD_iff (hx : x ≠ 0) : b ≤ x.unzeroD a ↔ b ≤ x := by
  lift x to α using hx; simp
/-
**WithZero.unzeroD_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：unzeroD_le_iff (hx : x = 0 -> a <= b) : x.unzeroD a <= b ↔ x <= b
参数：hx : x = 0 -> a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma unzeroD_le_iff (hx : x = 0 → a ≤ b) : x.unzeroD a ≤ b ↔ x ≤ b := by
  cases x <;> simp [hx]
/-
**WithZero.unzeroD_mono** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：unzeroD_mono (hx : x != 0) (h : x <= y) : x.unzeroD a <= y.unzeroD a
参数：hx : x != 0；h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma unzeroD_mono (hx : x ≠ 0) (h : x ≤ y) : x.unzeroD a ≤ y.unzeroD a := by
  lift x to α using hx
  cases y <;> simp_all

end LE

section LT

variable [LT α] {x y : WithZero α} {a b : α}

/-
**WithZero.lt_unzeroD_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：lt_unzeroD_iff (hx : x != 0) : b < x.unzeroD a ↔ b < x
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_unzeroD_iff (hx : x ≠ 0) : b < x.unzeroD a ↔ b < x := by
  lift x to α using hx; simp
/-
**WithZero.unzeroD_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：unzeroD_lt_iff (hx : x = 0 -> a < b) : x.unzeroD a < b ↔ x < b
参数：hx : x = 0 -> a < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma unzeroD_lt_iff (hx : x = 0 → a < b) : x.unzeroD a < b ↔ x < b := by
  cases x <;> simp [hx]

end LT

section Preorder

variable [Preorder α] {x y : WithZero α} {a b : α}

/-
**WithZero.le_coe_unzeroD** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：le_coe_unzeroD (x : WithZero α) (b : α) : x <= x.unzeroD b
参数：x : WithZero α；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_coe_unzeroD (x : WithZero α) (b : α) : x ≤ x.unzeroD b := by cases x <;> simp

end Preorder

section PartialOrder

variable [PartialOrder α] {x y : WithZero α} {a b : α}

/-
**WithZero.le_unzeroD** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：le_unzeroD (hy : b <= y) : b <= y.unzeroD a
参数：hy : b <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithZero.le_unzeroD_iff`：le_unzeroD_iff (hx : x != 0) : b <= x.unzeroD a
 ↔ b <= x
-/
lemma le_unzeroD (hy : b ≤ y) : b ≤ y.unzeroD a := by
  have hne : y ≠ 0 := ne_bot_of_le_ne_bot WithZero.coe_ne_zero hy
  rwa [le_unzeroD_iff hne]

end PartialOrder

end WithZero

