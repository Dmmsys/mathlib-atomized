/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Field.Canonical
public import Mathlib.Algebra.Order.Nonneg.Ring
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Semifield structure on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.
-/

@[expose] public section

assert_not_exists abs_inv

open Set

variable {α : Type*}

section NNRat
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

/-
**NNRat.cast_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
lemma NNRat.cast_nonneg (q : ℚ≥0) : 0 ≤ (q : α) := by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg
/-
**nnqsmul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnqsmul_nonneg (q : Rat>=0) (ha : 0 <= a) : 0 <= q • a
参数：q : Rat>=0；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `NNRat.cast_nonneg`：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
-/
lemma nnqsmul_nonneg (q : ℚ≥0) (ha : 0 ≤ a) : 0 ≤ q • a := by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

end NNRat

namespace Nonneg

/-- In an ordered field, the units of the nonnegative elements are the positive elements. -/
@[simps]
/-
**Nonneg.unitsEquivPos** 是 Mathlib 中的一个定义，位于命名空间 `Nonneg`。
形式化陈述：unitsEquivPos (R : Type*) [DivisionSemiring R] [PartialOrder R] [IsStrictO
rderedRing R] [PosMulReflectLT R] : { r : R // 0 <= r }ˣ ≃* { r : R // 0 < r } w
here toFun r
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an ordered field, the units of the nonnegative elements are the positive elem
ents.
-/
def unitsEquivPos (R : Type*) [DivisionSemiring R] [PartialOrder R]
    [IsStrictOrderedRing R] [PosMulReflectLT R] :
    { r : R // 0 ≤ r }ˣ ≃* { r : R // 0 < r } where
  toFun r := ⟨r, lt_of_le_of_ne r.1.2 (Subtype.val_injective.ne r.ne_zero.symm)⟩
  invFun r := ⟨⟨r.1, r.2.le⟩, ⟨r.1⁻¹, inv_nonneg.mpr r.2.le⟩,
    by ext; simp [r.2.ne'], by ext; simp [r.2.ne']⟩
  left_inv r := by ext; rfl
  right_inv r := by ext; rfl
  map_mul' _ _ := rfl

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

/-
**Nonneg.inv** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：inv : Inv { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inv : Inv { x : α // 0 ≤ x } :=
  ⟨fun x => ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]
/-
**Nonneg.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Semifield α] [inst_1 : LinearOrder α] [inst_2 : I
sStrictOrderedRing α] (a : { x // 0 ≤ x }),   ↑a⁻¹ = (↑a)⁻¹
参数：a : { x // 0 ≤ x }；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_inv (a : { x : α // 0 ≤ x }) : ((a⁻¹ : { x : α // 0 ≤ x }) : α) = (a : α)⁻¹ :=
  rfl

@[simp]
/-
**Nonneg.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：inv_mk (hx : 0 <= x) : (⟨x, hx⟩ : { x : α // 0 <= x })⁻¹ = ⟨x⁻¹, inv_nonne
g.2 hx⟩
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mk (hx : 0 ≤ x) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x })⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ :=
  rfl
/-
**Nonneg.div** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：div : Div { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance div : Div { x : α // 0 ≤ x } :=
  ⟨fun x y => ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast]
/-
**Nonneg.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Semifield α] [inst_1 : LinearOrder α] [inst_2 : I
sStrictOrderedRing α] (a b : { x // 0 ≤ x }),   ↑(a / b) = ↑a / ↑b
参数：a b : { x // 0 ≤ x }；a / b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_div (a b : { x : α // 0 ≤ x }) : ((a / b : { x : α // 0 ≤ x }) : α) = a / b :=
  rfl

@[simp]
/-
**Nonneg.mk_div_mk** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_div_mk (hx : 0 <= x) (hy : 0 <= y) : (⟨x, hx⟩ : { x : α // 0 <= x }) / 
⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
  rfl
/-
**Nonneg.zpow** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：zpow : Pow { x : α // 0 <= x } Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zpow : Pow { x : α // 0 ≤ x } ℤ :=
  ⟨fun a n => ⟨(a : α) ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast]
/-
**Nonneg.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Semifield α] [inst_1 : LinearOrder α] [inst_2 : I
sStrictOrderedRing α] (a : { x // 0 ≤ x })   (n : ℤ), ↑(a ^ n) = ↑a ^ n
参数：a : { x // 0 ≤ x }；n : ℤ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_zpow (a : { x : α // 0 ≤ x }) (n : ℤ) :
    ((a ^ n : { x : α // 0 ≤ x }) : α) = (a : α) ^ n :=
  rfl

@[simp]
/-
**Nonneg.mk_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：mk_zpow (hx : 0 <= x) (n : Int) : (⟨x, hx⟩ : { x : α // 0 <= x }) ^ n = ⟨x
 ^ n, zpow_nonneg hx n⟩
参数：hx : 0 <= x；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) :
    (⟨x, hx⟩ : { x : α // 0 ≤ x }) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ :=
  rfl
/-
**Nonneg.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instNNRatCast : NNRatCast {x : α // 0 <= x}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NNRat.cast_nonneg`：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
-/
instance instNNRatCast : NNRatCast {x : α // 0 ≤ x} := ⟨fun q ↦ ⟨q, q.cast_nonneg⟩⟩
/-
**Nonneg.instNNRatSMul** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instNNRatSMul : SMul Rat>=0 {x : α // 0 <= x} where smul q a
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNRatSMul : SMul ℚ≥0 {x : α // 0 ≤ x} where
  smul q a := ⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg a.2⟩
/-
**Nonneg.coe_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Semifield α] [inst_1 : LinearOrder α] [inst_2 : I
sStrictOrderedRing α] (q : ℚ≥0), ↑↑q = ↑q
参数：q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nnratCast (q : ℚ≥0) : (q : {x : α // 0 ≤ x}) = (q : α) := rfl
/-
**Nonneg.mk_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Semifield α] [inst_1 : LinearOrder α] [inst_2 : I
sStrictOrderedRing α] (q : ℚ≥0), ⟨↑q, ⋯⟩ = ↑q
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNRat.cast_nonneg`：NNRat.cast_nonneg (q : Rat>=0) : 0 <= (q : α)
-/
@[simp] lemma mk_nnratCast (q : ℚ≥0) : (⟨q, q.cast_nonneg⟩ : {x : α // 0 ≤ x}) = q := rfl
/-
**Nonneg.coe_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Semifield α] [inst_1 : LinearOrder α] [inst_2 : I
sStrictOrderedRing α] (q : ℚ≥0)   (a : { x // 0 ≤ x }), ↑(q • a) = q • ↑a
参数：q : ℚ≥0；a : { x // 0 ≤ x }；q • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_nnqsmul (q : ℚ≥0) (a : {x : α // 0 ≤ x}) :
    ↑(q • a) = (q • a : α) := rfl
/-
**Nonneg.mk_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 `Nonneg`。
形式化陈述：∀ {α : Type u_1} [inst : Semifield α] [inst_1 : LinearOrder α] [inst_2 : I
sStrictOrderedRing α] (q : ℚ≥0) (a : α)   (ha : 0 ≤ a), ↑⟨q • a, ⋯⟩ = q • a
参数：q : ℚ≥0；a : α；ha : 0 ≤ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_nnqsmul (q : ℚ≥0) (a : α) (ha : 0 ≤ a) :
    (⟨q • a, by rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha⟩ : {x : α // 0 ≤ x}) =
      q • a := rfl
/-
**Nonneg.semifield** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：semifield : Semifield { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semifield : Semifield { x : α // 0 ≤ x } := fast_instance%
  Subtype.coe_injective.semifield _ Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul Nonneg.coe_inv Nonneg.coe_div (fun _ _ => rfl) coe_nnqsmul Nonneg.coe_pow
    Nonneg.coe_zpow Nonneg.coe_natCast coe_nnratCast

end LinearOrderedSemifield

/-
**Nonneg.linearOrderedCommGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：linearOrderedCommGroupWithZero [Field α] [LinearOrder α] [IsStrictOrderedR
ing α] : LinearOrderedCommGroupWithZero { x : α // 0 <= x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrderedCommGroupWithZero [Field α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommGroupWithZero { x : α // 0 ≤ x } :=
  fast_instance% CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

end Nonneg

