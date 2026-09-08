/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Operations

/-!
# Results about division in extended non-negative reals

This file establishes basic properties related to the inversion and division operations on `ℝ≥0∞`.
For instance, as a consequence of being a `DivInvOneMonoid`, `ℝ≥0∞` inherits a power operation
with integer exponent.

## Main results

A few order isomorphisms are worthy of mention:

  - `OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ`: The map `x ↦ x⁻¹` as an order isomorphism to the dual.

  - `orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞)`: The birational order isomorphism between
    `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)` given by `x ↦ (x⁻¹ + 1)⁻¹` with inverse
    `x ↦ (x⁻¹ - 1)⁻¹`

  - `orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a`: Order isomorphism between an initial
    interval in `ℝ≥0∞` and an initial interval in `ℝ≥0` given by the identity map.

  - `orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1`: An order isomorphism between
    the extended nonnegative real numbers and the unit interval. This is `orderIsoIicOneBirational`
    composed with the identity order isomorphism between `Iic (1 : ℝ≥0∞)` and `Icc (0 : ℝ) 1`.
-/

@[expose] public section

assert_not_exists Finset

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

/-
**ENNReal.div_eq_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a / b = b⁻¹ * a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]
/-
**ENNReal.div_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a / b / c = a / c / b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem div_right_comm : a / b / c = a / c / b := by
  simp only [div_eq_mul_inv, mul_right_comm]
/-
**ENNReal.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：0⁻¹ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
  show sInf { b : ℝ≥0∞ | 1 ≤ 0 * b } = ∞ by simp
/-
**ENNReal.inv_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：⊤⁻¹ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <| le_of_forall_gt_imp_ge_of_dense fun a (h : 0 < a) => sInf_le <| by
    simp [*, h.ne', top_mul]
/-
**ENNReal.coe_inv_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_inv_le : (↑r⁻¹ : Real>=0∞) <= (↑r)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_iff`：coe_le_iff : ↑r <= a ↔ forall p : Real>=0, a = p -> 
r <= p
· 使用定理 `NNReal.inv_le_of_le_mul`：inv_le_of_le_mul {r p : Real>=0} (h : 1 <= r * 
p) : r⁻¹ <= p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_one`：↑1 = 1
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
-/
theorem coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
  le_sInf fun b (hb : 1 ≤ ↑r * b) =>
    coe_le_iff.2 <| by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb

@[simp, norm_cast]
/-
**ENNReal.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ENNReal.coe_inv_le`：coe_inv_le : (↑r⁻¹ : Real>=0∞) <= (↑r)⁻¹
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `ENNReal.coe_one`：↑1 = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
  coe_inv_le.antisymm <| sInf_le <| mem_ofPred.2 <| by rw [← coe_mul, mul_inv_cancel₀ hr, coe_one]

@[simp, norm_cast]
/-
**ENNReal.coe_inv'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_inv' [NeZero r] : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem coe_inv' [NeZero r] : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ := coe_inv (NeZero.ne r)

@[norm_cast]
/-
**ENNReal.coe_inv_two** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_inv_two : ((2⁻¹ : Real>=0) : Real>=0∞) = 2⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `ENNReal.coe_two`：coe_two : ((2 : Real>=0) : Real>=0∞) = 2
-/
theorem coe_inv_two : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast]
/-
**ENNReal.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
-/
theorem coe_div (hr : r ≠ 0) : (↑(p / r) : ℝ≥0∞) = p / r := by
  rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]

@[simp, norm_cast]
/-
**ENNReal.coe_div'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_div' [NeZero r] : (↑(p / r) : Real>=0∞) = p / r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem coe_div' [NeZero r] : (↑(p / r) : ℝ≥0∞) = p / r := coe_div (NeZero.ne r)
/-
**ENNReal.coe_div_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：coe_div_le : ↑(p / r) <= (p / r : Real>=0∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.coe_inv_le`：coe_inv_le : (↑r⁻¹ : Real>=0∞) <= (↑r)⁻¹
-/
lemma coe_div_le : ↑(p / r) ≤ (p / r : ℝ≥0∞) := by
  simpa only [div_eq_mul_inv, coe_mul] using _root_.mul_le_mul_right coe_inv_le _
/-
**ENNReal.div_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_zero (h : a != 0) : a / 0 = ∞
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_zero (h : a ≠ 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DivInvOneMonoid ℝ≥0∞ :=
  { (inferInstance : DivInvMonoid ℝ≥0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_inj.2 inv_one }
/-
**ENNReal.inv_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
参数：a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.top_pow`：∀ {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
-/
protected theorem inv_pow : ∀ {a : ℝ≥0∞} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
  | _, 0 => by simp only [pow_zero, inv_one]
  | ⊤, n + 1 => by simp [top_pow]
  | (a : ℝ≥0), n + 1 => by
    rcases eq_or_ne a 0 with (rfl | ha)
    · simp [top_pow]
    · have := pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]
/-
**ENNReal.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
-/
protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℝ≥0 using ht
  norm_cast at h0; norm_cast
  exact mul_inv_cancel₀ h0
/-
**ENNReal.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
protected theorem inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht

/-- See `ENNReal.inv_mul_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
/-
**ENNReal.inv_mul_cancel_left'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b = 0) → a⁻¹ * (a * b) = b
参数：a = 0 → b = 0；a = ⊤ → b = 0；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
See `ENNReal.inv_mul_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞
`.
-/
protected lemma inv_mul_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a⁻¹ * (a * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.inv_mul_cancel, *]

/-- See `ENNReal.inv_mul_cancel_left'` for a stronger version. -/
/-
**ENNReal.inv_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * (a * b) = b
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.inv_mul_cancel_left'`：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = 
⊤ → b = 0) → a⁻¹ * (a * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.inv_mul_cancel_left'` for a stronger version.
-/
protected lemma inv_mul_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a⁻¹ * (a * b) = b :=
  ENNReal.inv_mul_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_inv_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
/-
**ENNReal.mul_inv_cancel_left'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b = 0) → a * (a⁻¹ * b) = b
参数：a = 0 → b = 0；a = ⊤ → b = 0；a⁻¹ * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
See `ENNReal.mul_inv_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞
`.
-/
protected lemma mul_inv_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a * (a⁻¹ * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.mul_inv_cancel, *]

/-- See `ENNReal.mul_inv_cancel_left'` for a stronger version. -/
/-
**ENNReal.mul_inv_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (a⁻¹ * b) = b
参数：a⁻¹ * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_inv_cancel_left'`：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = 
⊤ → b = 0) → a * (a⁻¹ * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.mul_inv_cancel_left'` for a stronger version.
-/
protected lemma mul_inv_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * (a⁻¹ * b) = b :=
  ENNReal.mul_inv_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_inv_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
/-
**ENNReal.mul_inv_cancel_right'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b = ⊤ → a = 0) → a * b * b⁻¹ = a
参数：b = 0 → a = 0；b = ⊤ → a = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
See `ENNReal.mul_inv_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ 
∞`.
-/
protected lemma mul_inv_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b * b⁻¹ = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.mul_inv_cancel, *]

/-- See `ENNReal.mul_inv_cancel_right'` for a stronger version. -/
/-
**ENNReal.mul_inv_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → a * b * b⁻¹ = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_inv_cancel_right'`：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b =
 ⊤ → a = 0) → a * b * b⁻¹ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.mul_inv_cancel_right'` for a stronger version.
-/
protected lemma mul_inv_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b * b⁻¹ = a :=
  ENNReal.mul_inv_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNReal.inv_mul_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
/-
**ENNReal.inv_mul_cancel_right'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b = ⊤ → a = 0) → a * b⁻¹ * b = a
参数：b = 0 → a = 0；b = ⊤ → a = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
See `ENNReal.inv_mul_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ 
∞`.
-/
protected lemma inv_mul_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b⁻¹ * b = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.inv_mul_cancel, *]

/-- See `ENNReal.inv_mul_cancel_right'` for a stronger version. -/
/-
**ENNReal.inv_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → a * b⁻¹ * b = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.inv_mul_cancel_right'`：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b =
 ⊤ → a = 0) → a * b⁻¹ * b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.inv_mul_cancel_right'` for a stronger version.
-/
protected lemma inv_mul_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b⁻¹ * b = a :=
  ENNReal.inv_mul_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNReal.mul_div_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
/-
**ENNReal.mul_div_cancel_right'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b = ⊤ → a = 0) → a * b / b = a
参数：b = 0 → a = 0；b = ⊤ → a = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_inv_cancel_right'`：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b =
 ⊤ → a = 0) → a * b * b⁻¹ = a

--- 原说明 ---
See `ENNReal.mul_div_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ 
∞`.
-/
protected lemma mul_div_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b / b = a := ENNReal.mul_inv_cancel_right' hb₀ hb

/-- See `ENNReal.mul_div_cancel_right'` for a stronger version. -/
/-
**ENNReal.mul_div_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → a * b / b = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_div_cancel_right'`：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b =
 ⊤ → a = 0) → a * b / b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.mul_div_cancel_right'` for a stronger version.
-/
protected lemma mul_div_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b / b = a :=
  ENNReal.mul_div_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNReal.div_mul_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
/-
**ENNReal.div_mul_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b = 0) → b / a * a = b
参数：a = 0 → b = 0；a = ⊤ → b = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.inv_mul_cancel_right'`：∀ {a b : ENNReal}, (b = 0 → a = 0) → (b =
 ⊤ → a = 0) → a * b⁻¹ * b = a

--- 原说明 ---
See `ENNReal.div_mul_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`.
-/
protected lemma div_mul_cancel' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) : b / a * a = b :=
  ENNReal.inv_mul_cancel_right' ha₀ ha

/-- See `ENNReal.div_mul_cancel'` for a stronger version. -/
/-
**ENNReal.div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → b / a * a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_mul_cancel'`：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b
 = 0) → b / a * a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.div_mul_cancel'` for a stronger version.
-/
protected lemma div_mul_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) : b / a * a = b :=
  ENNReal.div_mul_cancel' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
/-
**ENNReal.mul_div_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b = 0) → a * (b / a) = b
参数：a = 0 → b = 0；a = ⊤ → b = 0；b / a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.div_mul_cancel'`：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b
 = 0) → b / a * a = b

--- 原说明 ---
See `ENNReal.mul_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`.
-/
protected lemma mul_div_cancel' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) : a * (b / a) = b := by
  rw [mul_comm, ENNReal.div_mul_cancel' ha₀ ha]

/-- See `ENNReal.mul_div_cancel'` for a stronger version. -/
/-
**ENNReal.mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) = b
参数：b / a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_div_cancel'`：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b
 = 0) → a * (b / a) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.mul_div_cancel'` for a stronger version.
-/
protected lemma mul_div_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * (b / a) = b :=
  ENNReal.mul_div_cancel' (by simp [ha₀]) (by simp [ha])
/-
**ENNReal.mul_comm_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a / b * c = a * (c / b)
参数：c / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_comm_div : a / b * c = a * (c / b) := by
  simp only [div_eq_mul_inv, mul_left_comm, mul_comm]
/-
**ENNReal.mul_div_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a * b / c = a / c * b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_div_right_comm : a * b / c = a / c * b := by
  simp only [div_eq_mul_inv, mul_right_comm]
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveInv ℝ≥0∞ where
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [-coe_inv, (coe_inv _).symm]
/-
**ENNReal.inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a⁻¹ = 1 ↔ a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] protected lemma inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [← inv_inj, inv_inv, inv_one]
/-
**ENNReal.inv_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a⁻¹ = ⊤ ↔ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
-/
@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj
/-
**ENNReal.inv_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[aesop (rule_sets := [finiteness]) safe apply]
protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNReal.inv_ne_top

@[simp]
/-
**ENNReal.inv_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_lt_top {x : Real>=0∞} : x⁻¹ < ∞ ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]
/-
**ENNReal.div_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_lt_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y != 0) : x / y < ∞
参数：h1 : x != ∞；h2 : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
-/
theorem div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
  mul_lt_top h1.lt_top (inv_ne_top.mpr h2).lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
/-
**ENNReal.div_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_ne_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y != 0) : x / y != ∞
参数：h1 : x != ∞；h2 : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.div_lt_top`：div_lt_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y !=
 0) : x / y < ∞
-/
theorem div_ne_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y ≠ ∞ := (div_lt_top h1 h2).ne

@[simp]
/-
**ENNReal.inv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a⁻¹ = 0 ↔ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
-/
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj
/-
**ENNReal.inv_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp
/-
**ENNReal.div_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_pos`：mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
-/
protected theorem div_pos (ha : a ≠ 0) (hb : b ≠ ∞) : 0 < a / b :=
  ENNReal.mul_pos ha <| ENNReal.inv_ne_zero.2 hb
/-
**ENNReal.inv_mul_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y z : ENNReal}, x ≠ 0 → x ≠ ⊤ → (x⁻¹ * y ≤ z ↔ y ≤ x * z)
参数：x⁻¹ * y ≤ z ↔ y ≤ x * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_le_mul_iff_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * 
b ≤ a * c ↔ b ≤ c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem inv_mul_le_iff {x y z : ℝ≥0∞} (h1 : x ≠ 0) (h2 : x ≠ ∞) :
    x⁻¹ * y ≤ z ↔ y ≤ x * z := by
  rw [← ENNReal.mul_le_mul_iff_right h1 h2, ← mul_assoc, ENNReal.mul_inv_cancel h1 h2, one_mul]
/-
**ENNReal.mul_inv_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x * y⁻¹ ≤ z ↔ x ≤ z * y)
参数：x * y⁻¹ ≤ z ↔ x ≤ z * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.inv_mul_le_iff`：∀ {x y z : ENNReal}, x ≠ 0 → x ≠ ⊤ → (x⁻¹ * y ≤ 
z ↔ y ≤ x * z)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem mul_inv_le_iff {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x * y⁻¹ ≤ z ↔ x ≤ z * y := by
  rw [mul_comm, ENNReal.inv_mul_le_iff h1 h2, mul_comm]
/-
**ENNReal.div_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x / y ≤ z ↔ x ≤ z * y)
参数：x / y ≤ z ↔ x ≤ z * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv_le_iff`：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x * y⁻¹ ≤ 
z ↔ x ≤ z * y)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem div_le_iff {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ z * y := by
  rw [div_eq_mul_inv, ENNReal.mul_inv_le_iff h1 h2]
/-
**ENNReal.div_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x / y ≤ z ↔ x ≤ y * z)
参数：x / y ≤ z ↔ x ≤ y * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.div_le_iff`：∀ {x y z : ENNReal}, y ≠ 0 → y ≠ ⊤ → (x / y ≤ z ↔ x 
≤ z * y)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem div_le_iff' {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ y * z := by
  rw [mul_comm, ENNReal.div_le_iff h1 h2]
/-
**ENNReal.mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a * b)⁻¹ = a⁻¹ * b⁻¹
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
protected theorem mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  cases b
  case top =>
    simp_all only [Ne, not_true_eq_false, or_false, top_ne_zero, not_false_eq_true, or_true,
      mul_top, inv_top, mul_zero]
  cases a
  case top =>
    simp_all only [Ne, top_ne_zero, not_false_eq_true, coe_ne_top, or_self, not_true_eq_false,
      coe_eq_zero, false_or, top_mul, inv_top, zero_mul]
  grind [_=_ coe_mul, coe_zero, inv_zero, = mul_inv, coe_ne_top, ENNReal.inv_eq_zero,
    =_ coe_inv, zero_mul, = mul_eq_zero, mul_top, mul_zero, top_mul]
/-
**ENNReal.inv_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, b ≠ ⊤ ∨ a ≠ ⊤ → b ≠ 0 ∨ a ≠ 0 → (a / b)⁻¹ = b / a
参数：a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
protected theorem inv_div {a b : ℝ≥0∞} (htop : b ≠ ∞ ∨ a ≠ ∞) (hzero : b ≠ 0 ∨ a ≠ 0) :
    (a / b)⁻¹ = b / a := by
  rw [← ENNReal.inv_ne_zero] at htop
  rw [← ENNReal.inv_ne_top] at hzero
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv htop hzero, mul_comm, inv_inv]
/-
**ENNReal.mul_div_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {c : ENNReal} (a b : ENNReal), c ≠ 0 → c ≠ ⊤ → c * a / (c * b) = a / b
参数：a b : ENNReal；c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem mul_div_mul_left (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc) (Or.inl hc'), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', one_mul]
/-
**ENNReal.mul_div_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {c : ENNReal} (a b : ENNReal), c ≠ 0 → c ≠ ⊤ → a * c / (b * c) = a / b
参数：a b : ENNReal；b * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
protected theorem mul_div_mul_right (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    a * c / (b * c) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hc') (Or.inr hc), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', mul_one]
/-
**ENNReal.sub_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ 0) → (a - b) / c = a / c - b / c
参数：0 < b → b < a → c ≠ 0；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.sub_mul`：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ ⊤) → (a - b) 
* c = a * c - b * c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected theorem sub_div (h : 0 < b → b < a → c ≠ 0) : (a - b) / c = a / c - b / c := by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.sub_mul (by simpa using h)

@[simp]
/-
**ENNReal.inv_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, 0 < a⁻¹ ↔ a ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
-/
protected theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans ENNReal.inv_ne_zero
/-
**ENNReal.inv_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_strictAnti : StrictAnti (Inv.inv : Real>=0∞ -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `NNReal.inv_lt_inv`：inv_lt_inv {x y : Real>=0} (hx : x != 0) (h : x < y) 
: y⁻¹ < x⁻¹
-/
theorem inv_strictAnti : StrictAnti (Inv.inv : ℝ≥0∞ → ℝ≥0∞) := by
  intro a b h
  lift a to ℝ≥0 using h.ne_top
  cases b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe]
  exact NNReal.inv_lt_inv ha h

@[simp]
/-
**ENNReal.inv_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a⁻¹ < b⁻¹ ↔ b < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `ENNReal.inv_strictAnti`：inv_strictAnti : StrictAnti (Inv.inv : Real>=0∞ 
-> Real>=0∞)
-/
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_gt
/-
**ENNReal.inv_lt_iff_inv_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.inv_lt_inv`：∀ {a b : ENNReal}, a⁻¹ < b⁻¹ ↔ b < a
-/
theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹
/-
**ENNReal.lt_inv_iff_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.inv_lt_inv`：∀ {a b : ENNReal}, a⁻¹ < b⁻¹ ↔ b < a
-/
theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b

@[simp]
/-
**ENNReal.inv_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a⁻¹ ≤ b⁻¹ ↔ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `ENNReal.inv_strictAnti`：inv_strictAnti : StrictAnti (Inv.inv : Real>=0∞ 
-> Real>=0∞)
-/
protected theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strictAnti.le_iff_ge
/-
**ENNReal.inv_le_iff_inv_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_le_iff_inv_le : a⁻¹ <= b ↔ b⁻¹ <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.inv_le_inv`：∀ {a b : ENNReal}, a⁻¹ ≤ b⁻¹ ↔ b ≤ a
-/
theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹
/-
**ENNReal.le_inv_iff_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_inv_iff_le_inv : a <= b⁻¹ ↔ b <= a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.inv_le_inv`：∀ {a b : ENNReal}, a⁻¹ ≤ b⁻¹ ↔ b ≤ a
-/
theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b
/-
**ENNReal.inv_le_inv'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≤ b → b⁻¹ ≤ a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用定理 `ENNReal.inv_strictAnti`：inv_strictAnti : StrictAnti (Inv.inv : Real>=0∞ 
-> Real>=0∞)
-/
@[gcongr] protected theorem inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h
/-
**ENNReal.inv_lt_inv'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a < b → b⁻¹ < a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.inv_strictAnti`：inv_strictAnti : StrictAnti (Inv.inv : Real>=0∞ 
-> Real>=0∞)
-/
@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

@[simp]
/-
**ENNReal.inv_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a⁻¹ ≤ 1 ↔ 1 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_le_iff_inv_le`：inv_le_iff_inv_le : a⁻¹ <= b ↔ b⁻¹ <= a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, inv_one]
/-
**ENNReal.one_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, 1 ≤ a⁻¹ ↔ a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.le_inv_iff_le_inv`：le_inv_iff_le_inv : a <= b⁻¹ ↔ b <= a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, inv_one]

@[simp]
/-
**ENNReal.inv_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a⁻¹ < 1 ↔ 1 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_lt_iff_inv_lt`：inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]

@[simp]
/-
**ENNReal.one_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, 1 < a⁻¹ ↔ a < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.lt_inv_iff_lt_inv`：lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]

/-- The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `OrderDual` -/
@[simps! apply]
/-
**ENNReal._root_.OrderIso.invENNReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `Or
derDual`
-/
def _root_.OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ where
  map_rel_iff' := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv ℝ≥0∞).trans OrderDual.toDual

@[simp]
/-
**ENNReal._root_.OrderIso.invENNReal_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ENNRe
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.invENNReal_symm_apply (a : ℝ≥0∞ᵒᵈ) :
    OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl
/-
**ENNReal.div_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a / ⊤ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]
/-
**ENNReal.top_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_div : ∞ / a = if a = ∞ then 0 else ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.top_mul'`：top_mul' : ∞ * a = if a = 0 then 0 else ∞
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by simp [div_eq_mul_inv, top_mul']
/-
**ENNReal.top_div_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_div_of_ne_top (h : a != ∞) : ∞ / a = ∞
参数：h : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_div`：top_div : ∞ / a = if a = ∞ then 0 else ∞
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by simp [top_div, h]
/-
**ENNReal.top_div_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {p : NNReal}, ⊤ / ↑p = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.top_div_of_ne_top`：top_div_of_ne_top (h : a != ∞) : ∞ / a = ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
@[simp] theorem top_div_coe : ∞ / p = ∞ := top_div_of_ne_top coe_ne_top
/-
**ENNReal.top_div_of_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞
参数：h : a < ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.top_div_of_ne_top`：top_div_of_ne_top (h : a != ∞) : ∞ / a = ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ := top_div_of_ne_top h.ne
/-
**ENNReal.zero_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, 0 / a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
@[simp] protected theorem zero_div : 0 / a = 0 := zero_mul a⁻¹
/-
**ENNReal.div_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_eq_top : a / b = ∞ ↔ a != 0 ∧ b = 0 ∨ a = ∞ ∧ b != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_eq_top : a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]

/-- See `ENNReal.div_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
/-
**ENNReal.div_div_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b = 0) → a / (a / b) = b
参数：a = 0 → b = 0；a = ⊤ → b = 0；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.top_div_of_lt_top`：top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `ENNReal.inv_div`：∀ {a b : ENNReal}, b ≠ ⊤ ∨ a ≠ ⊤ → b ≠ 0 ∨ a ≠ 0 → (a /
 b)⁻¹ = b / a
· 使用定理 `ENNReal.div_mul_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → b / a * a = b

--- 原说明 ---
See `ENNReal.div_div_cancel` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`.
-/
protected lemma div_div_cancel' (h₀ : a = 0 → b = 0) (h₁ : a = ∞ → b = 0) :
    a / (a / b) = b := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [h₀]
  obtain rfl | ha' := eq_or_ne a ∞
  · simp [h₁, top_div_of_lt_top]
  rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inr ha') (Or.inr ha),
    ENNReal.div_mul_cancel ha ha']

/-- See `ENNReal.div_div_cancel'` for a stronger version. -/
/-
**ENNReal.div_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / (a / b) = b
参数：a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_div_cancel'`：∀ {a b : ENNReal}, (a = 0 → b = 0) → (a = ⊤ → b
 = 0) → a / (a / b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
See `ENNReal.div_div_cancel'` for a stronger version.
-/
protected lemma div_div_cancel {a b : ℝ≥0∞} (h₀ : a ≠ 0) (h₁ : a ≠ ∞) :
    a / (a / b) = b :=
  ENNReal.div_div_cancel' (by simp [h₀]) (by simp [h₁])
/-
**ENNReal.le_div_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ 
c)
参数：a ≤ c / b ↔ a * b ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Or.neg_resolve_left`：∀ {a b : Prop}, ¬a ∨ b → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.div_zero`：div_zero (h : a != 0) : a / 0 = ∞
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.mul_le_mul_iff_left`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c
 ≤ b * c ↔ a ≤ b)
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.div_mul_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → b / a * a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
    a ≤ c / b ↔ a * b ≤ c := by
  cases b with
  | top =>
    lift c to ℝ≥0 using ht.neg_resolve_left rfl
    rw [div_top, nonpos_iff_eq_zero]
    rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
  | coe b => ?_
  rcases eq_or_ne b 0 with (rfl | hb)
  · have hc : c ≠ 0 := h0.neg_resolve_left rfl
    simp [div_zero hc]
  · rw [← coe_ne_zero] at hb
    rw [← ENNReal.mul_le_mul_iff_left hb coe_ne_top, ENNReal.div_mul_cancel hb coe_ne_top]
/-
**ENNReal.div_le_iff_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ c ≠ 0 → (a / b ≤ c ↔ a ≤ c * 
b)
参数：a / b ≤ c ↔ a ≤ c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
protected theorem div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    a / b ≤ c ↔ a ≤ c * b := by
  suffices a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹ by simpa [div_eq_mul_inv]
  refine (ENNReal.le_div_iff_mul_le ?_ ?_).symm <;> simpa
/-
**ENNReal.lt_div_iff_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ c ≠ 0 → (c < a / b ↔ c * b < 
a)
参数：c < a / b ↔ c * b < a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
-/
protected theorem lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    c < a / b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul hb0 hbt)
/-
**ENNReal.div_le_of_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_le_of_le_mul (h : a <= b * c) : a / c <= b
参数：h : a <= b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
-/
theorem div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b := by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h
/-
**ENNReal.div_le_of_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_le_of_le_mul' (h : a <= b * c) : a / b <= c
参数：h : a <= b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_le_of_le_mul`：div_le_of_le_mul (h : a <= b * c) : a / c <= b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
/-
**ENNReal.div_self_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a / a ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_le_of_le_mul`：div_le_of_le_mul (h : a <= b * c) : a / c <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[simp] protected theorem div_self_le_one : a / a ≤ 1 := div_le_of_le_mul <| by rw [one_mul]
/-
**ENNReal.mul_inv_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : ENNReal), a * a⁻¹ ≤ 1
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_self_le_one`：∀ {a : ENNReal}, a / a ≤ 1
-/
@[simp] protected lemma mul_inv_le_one (a : ℝ≥0∞) : a * a⁻¹ ≤ 1 := ENNReal.div_self_le_one
/-
**ENNReal.inv_mul_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : ENNReal), a⁻¹ * a ≤ 1
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
@[simp] protected lemma inv_mul_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by simp [mul_comm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
/-
**ENNReal.mul_inv_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_inv_ne_top (a : Real>=0∞) : a * a⁻¹ != ⊤
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `ENNReal.mul_inv_le_one`：∀ (a : ENNReal), a * a⁻¹ ≤ 1
-/
lemma mul_inv_ne_top (a : ℝ≥0∞) : a * a⁻¹ ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[aesop (rule_sets := [finiteness]) safe apply, simp]
/-
**ENNReal.inv_mul_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：inv_mul_ne_top (a : Real>=0∞) : a⁻¹ * a != ⊤
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma inv_mul_ne_top (a : ℝ≥0∞) : a⁻¹ * a ≠ ⊤ := by simp [mul_comm]
/-
**ENNReal.mul_le_of_le_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_le_of_le_div (h : a <= b / c) : a * c <= b
参数：h : a <= b / c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.div_le_of_le_mul`：div_le_of_le_mul (h : a <= b * c) : a / c <= b
-/
theorem mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b := by
  rw [← inv_inv c]
  exact div_le_of_le_mul h
/-
**ENNReal.mul_le_of_le_div'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_le_of_le_div' (h : a <= b / c) : c * a <= b
参数：h : a <= b / c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_le_of_le_div`：mul_le_of_le_div (h : a <= b / c) : a * c <= b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h
/-
**ENNReal.div_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ → (c / b < a ↔ c < a * 
b)
参数：c / b < a ↔ c < a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
-/
protected theorem div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : c / b < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le <| ENNReal.le_div_iff_mul_le h0 ht
/-
**ENNReal.mul_lt_of_lt_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_lt_of_lt_div (h : a < b / c) : a * c < b
参数：h : a < b / c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.div_le_of_le_mul`：div_le_of_le_mul (h : a <= b * c) : a / c <= b
-/
theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h
/-
**ENNReal.mul_lt_of_lt_div'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_lt_of_lt_div' (h : a < b / c) : c * a < b
参数：h : a < b / c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_lt_of_lt_div`：mul_lt_of_lt_div (h : a < b / c) : a * c < b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h
/-
**ENNReal.div_lt_of_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_lt_of_lt_mul (h : a < b * c) : a / c < b
参数：h : a < b * c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_lt_of_lt_div`：mul_lt_of_lt_div (h : a < b / c) : a * c < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem div_lt_of_lt_mul (h : a < b * c) : a / c < b :=
  mul_lt_of_lt_div <| by rwa [div_eq_mul_inv, inv_inv]
/-
**ENNReal.div_lt_of_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_lt_of_lt_mul' (h : a < b * c) : a / b < c
参数：h : a < b * c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_lt_of_lt_mul`：div_lt_of_lt_mul (h : a < b * c) : a / c < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem div_lt_of_lt_mul' (h : a < b * c) : a / b < c :=
  div_lt_of_lt_mul <| by rwa [mul_comm]
/-
**ENNReal.div_lt_div_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a / c < b / c ↔ a < b)
参数：a / c < b / c ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_lt_mul_iff_left`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c
 < b * c ↔ a < b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected lemma div_lt_div_iff_left (hc₀ : c ≠ 0) (hc : c ≠ ∞) : a / c < b / c ↔ a < b :=
  ENNReal.mul_lt_mul_iff_left (by simpa) (by simpa)
/-
**ENNReal.div_lt_div_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a / b < a / c ↔ c < b)
参数：a / b < a / c ↔ c < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ENNReal.mul_lt_mul_iff_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * 
b < a * c ↔ b < c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma div_lt_div_iff_right (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a / b < a / c ↔ c < b :=
  (ENNReal.mul_lt_mul_iff_right ha₀ ha).trans (by simp)

@[gcongr]
/-
**ENNReal.div_lt_div_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → a < b → a / c < b / c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.div_lt_div_iff_left`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a / c
 < b / c ↔ a < b)
-/
protected lemma div_lt_div_right (hc₀ : c ≠ 0) (hc : c ≠ ∞) (hab : a < b) : a / c < b / c :=
  (ENNReal.div_lt_div_iff_left hc₀ hc).2 hab

@[gcongr]
/-
**ENNReal.div_lt_div_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → c < b → a / b < a / c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.div_lt_div_iff_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a / 
b < a / c ↔ c < b)
-/
protected lemma div_lt_div_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) (hcb : c < b) : a / b < a / c :=
  (ENNReal.div_lt_div_iff_right ha₀ ha).2 hcb
/-
**ENNReal.exists_pos_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ 0 → ∃ c, 0 < c ∧ c * a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_pos`：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
· 使用定理 `ENNReal.Finiteness.add_ne_top`：∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ ⊤ → a + b 
≠ ⊤
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `ENNReal.mul_lt_of_lt_div`：mul_lt_of_lt_div (h : a < b / c) : a * c < b
· 使用定理 `ENNReal.div_lt_div_left`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → c < b → a 
/ b < a / c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
protected lemma exists_pos_mul_lt (ha : a ≠ ∞) (hb₀ : b ≠ 0) : ∃ c, 0 < c ∧ c * a < b := by
  obtain rfl | hb := eq_or_ne b ∞
  · exact ⟨1, by simpa [lt_top_iff_ne_top]⟩
  refine ⟨b / (a + 1), ENNReal.div_pos hb₀ (by finiteness), ENNReal.mul_lt_of_lt_div ?_⟩
  gcongr
  exact ENNReal.lt_add_right ha one_ne_zero
/-
**ENNReal.inv_le_iff_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_le_iff_le_mul (h₁ : b = ∞ -> a != 0) (h₂ : a = ∞ -> b != 0) : a⁻¹ <= b
 ↔ 1 <= a * b
参数：h₁ : b = ∞ -> a != 0；h₂ : a = ∞ -> b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
· 使用定理 `or_not_of_imp`：or_not_of_imp : (a -> b) -> b ∨ ¬a
· 使用定理 `not_or_of_imp`：not_or_of_imp : (a -> b) -> ¬a ∨ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_div, ENNReal.div_le_iff_le_mul, mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]

@[simp 900]
/-
**ENNReal.le_inv_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_inv_iff_mul_le : a <= b⁻¹ ↔ a * b <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, ENNReal.le_div_iff_mul_le] <;>
    · right
      simp
/-
**ENNReal.div_le_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_le_inv`：∀ {a b : ENNReal}, a⁻¹ ≤ b⁻¹ ↔ b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
@[gcongr] protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)
/-
**ENNReal.div_le_div_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≤ b → ∀ (c : ENNReal), c / b ≤ c / a
参数：c : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
  ENNReal.div_le_div le_rfl h
/-
**ENNReal.div_le_div_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a ≤ b → ∀ (c : ENNReal), a / c ≤ b / c
参数：c : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
protected theorem div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
  ENNReal.div_le_div h le_rfl
/-
**ENNReal.eq_inv_of_mul_eq_one_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a * b = 1 → a = b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `right_ne_zero_of_mul_eq_one`：right_ne_zero_of_mul_eq_one (h : a * b = 1)
 : b != 0
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `left_ne_zero_of_mul_eq_one`：left_ne_zero_of_mul_eq_one (h : a * b = 1) :
 a != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h
/-
**ENNReal.mul_le_iff_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_le_iff_le_inv {a b r : Real>=0∞} (hr₀ : r != 0) (hr₁ : r != ∞) : r * a
 <= b ↔ a <= r⁻¹ * b
参数：hr₀ : r != 0；hr₁ : r != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_le_mul_iff_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → (a * 
b ≤ a * c ↔ b ≤ c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @ENNReal.mul_le_mul_iff_right _ a _ hr₀ hr₁, ← mul_assoc, ENNReal.mul_inv_cancel hr₀ hr₁,
    one_mul]
/-
**ENNReal.le_of_forall_nnreal_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_of_forall_nnreal_lt {x y : Real>=0∞} (h : forall r : Real>=0, ↑r < x ->
 ↑r <= y) : x <= y
参数：h : forall r : Real>=0, ↑r < x -> ↑r <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
-/
theorem le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr
/-
**ENNReal.eq_of_forall_nnreal_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：eq_of_forall_nnreal_le_iff {x y : Real>=0∞} : (forall r : Real>=0, ↑r <= x
 ↔ ↑r <= y) -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.eq_of_forall_coe_le_iff`：∀ {α : Type u_1} [inst : PartialOrder α
] {x y : WithTop α} [NoTopOrder α], (∀ (a : α), ↑a ≤ x ↔ ↑a ≤ y) → x = y
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
lemma eq_of_forall_nnreal_le_iff {x y : ℝ≥0∞} : (∀ r : ℝ≥0, ↑r ≤ x ↔ ↑r ≤ y) → x = y :=
  WithTop.eq_of_forall_coe_le_iff
/-
**ENNReal.eq_of_forall_le_nnreal_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：eq_of_forall_le_nnreal_iff {x y : Real>=0∞} : (forall r : Real>=0, x <= r 
↔ y <= r) -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.eq_of_forall_le_coe_iff`：∀ {α : Type u_1} [inst : PartialOrder α
] {x y : WithTop α} [NoTopOrder α], (∀ (a : α), x ≤ ↑a ↔ y ≤ ↑a) → x = y
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
lemma eq_of_forall_le_nnreal_iff {x y : ℝ≥0∞} : (∀ r : ℝ≥0, x ≤ r ↔ y ≤ r) → x = y :=
  WithTop.eq_of_forall_le_coe_iff
/-
**ENNReal.le_of_forall_pos_nnreal_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_of_forall_pos_nnreal_lt {x y : Real>=0∞} (h : forall r : Real>=0, 0 < r
 -> ↑r < x -> ↑r <= y) : x <= y
参数：h : forall r : Real>=0, 0 < r -> ↑r < x -> ↑r <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nnreal_lt fun r hr =>
    (eq_zero_or_pos r).elim (fun h => h ▸ zero_le) fun h0 => h r h0 hr
/-
**ENNReal.eq_top_of_forall_nnreal_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：eq_top_of_forall_nnreal_le {x : Real>=0∞} (h : forall r : Real>=0, ↑r <= x
) : x = ∞
参数：h : forall r : Real>=0, ↑r <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
-/
theorem eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nnreal_lt fun r _ => h r
/-
**ENNReal.add_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
protected theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹
/-
**ENNReal.div_add_div_same** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c : ENNReal}, a / c + b / c = (a + b) / c
参数：a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_div`：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
-/
protected theorem div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
  ENNReal.add_div.symm
/-
**ENNReal.div_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
-/
protected theorem div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
  ENNReal.mul_inv_cancel h0 hI
/-
**ENNReal.mul_div_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_div_le : a * (b / a) <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_le_of_le_div'`：mul_le_of_le_div' (h : a <= b / c) : c * a <=
 b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mul_div_le : a * (b / a) ≤ b :=
  mul_le_of_le_div' le_rfl
/-
**ENNReal.eq_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：eq_div_iff (ha : a != 0) (ha' : a != ∞) : b = c / a ↔ a * b = c
参数：ha : a != 0；ha' : a != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_div_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) =
 b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
-/
theorem eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) : b = c / a ↔ a * b = c :=
  ⟨fun h => by rw [h, ENNReal.mul_div_cancel ha ha'], fun h => by
    rw [← h, mul_div_assoc, ENNReal.mul_div_cancel ha ha']⟩
/-
**ENNReal.div_eq_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c d : ENNReal}, a ≠ 0 → a ≠ ⊤ → b ≠ 0 → b ≠ ⊤ → (c / b = d / a ↔ a 
* c = b * d)
参数：c / b = d / a ↔ a * c = b * d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.eq_div_iff`：eq_div_iff (ha : a != 0) (ha' : a != ∞) : b = c / a 
↔ a * b = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) :
    c / b = d / a ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb', mul_div_assoc, eq_comm]
/-
**ENNReal.div_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_eq_one_iff {a b : Real>=0∞} (hb₀ : b != 0) (hb₁ : b != ∞) : a / b = 1 
↔ a = b
参数：hb₀ : b != 0；hb₁ : b != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.eq_div_iff`：eq_div_iff (ha : a != 0) (ha' : a != ∞) : b = c / a 
↔ a * b = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
-/
theorem div_eq_one_iff {a b : ℝ≥0∞} (hb₀ : b ≠ 0) (hb₁ : b ≠ ∞) : a / b = 1 ↔ a = b :=
  ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩
/-
**ENNReal.inv_two_add_inv_two** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_two_add_inv_two : (2 : Real>=0∞)⁻¹ + 2⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
-/
theorem inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ← div_eq_mul_inv, ENNReal.div_self two_ne_zero ofNat_ne_top]
/-
**ENNReal.inv_three_add_inv_three** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_three_add_inv_three : (3 : Real>=0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用引理 `three_ne_zero`：three_ne_zero [OfNat α 3] [NeZero (3 : α)] : (3 : α) != 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 32 条，此处仅展示前 30 条）
-/
theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by
  rw [← ENNReal.mul_inv_cancel three_ne_zero ofNat_ne_top]
  ring

@[simp]
/-
**ENNReal.add_halves** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : ENNReal), a / 2 + a / 2 = a
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `ENNReal.inv_two_add_inv_two`：inv_two_add_inv_two : (2 : Real>=0∞)⁻¹ + 2⁻
¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
protected theorem add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp]
/-
**ENNReal.add_thirds** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：add_thirds (a : Real>=0∞) : a / 3 + a / 3 + a / 3 = a
参数：a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `ENNReal.inv_three_add_inv_three`：inv_three_add_inv_three : (3 : Real>=0∞
)⁻¹ + 3⁻¹ + 3⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]
/-
**ENNReal.div_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a / b = 0 ↔ a = 0 ∨ b = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]
/-
**ENNReal.div_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ := by simp [pos_iff_ne_zero, not_or]
/-
**ENNReal.div_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b : ENNReal}, a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.div_pos_iff`：∀ {a b : ENNReal}, 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma div_ne_zero : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ ∞ := by
  rw [← pos_iff_ne_zero, div_pos_iff]
/-
**ENNReal.div_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {b c : ENNReal} (a : ENNReal), b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ → a / b * c
 = a / (b / c)
参数：a : ENNReal；b / c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
protected lemma div_mul (a : ℝ≥0∞) (h0 : b ≠ 0 ∨ c ≠ 0) (htop : b ≠ ∞ ∨ c ≠ ∞) :
    a / b * c = a / (b / c) := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv, inv_inv]
  · ring
  · simpa
  · simpa
/-
**ENNReal.mul_div_mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a b c d : ENNReal}, c ≠ 0 ∨ d ≠ ⊤ → c ≠ ⊤ ∨ d ≠ 0 → a * b / (c * d) = a
 / c * (b / d)
参数：c * d；b / d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
protected lemma mul_div_mul_comm (hc : c ≠ 0 ∨ d ≠ ∞) (hd : c ≠ ∞ ∨ d ≠ 0) :
    a * b / (c * d) = a / c * (b / d) := by
  simp only [div_eq_mul_inv, ENNReal.mul_inv hc hd]
  ring
/-
**ENNReal.half_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_pos`：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
-/
protected theorem half_pos (h : a ≠ 0) : 0 < a / 2 :=
  ENNReal.div_pos h ofNat_ne_top
/-
**ENNReal.one_half_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：2⁻¹ < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.inv_lt_one`：∀ {a : ENNReal}, a⁻¹ < 1 ↔ 1 < a
· 使用定理 `ENNReal.one_lt_two`：one_lt_two : (1 : Real>=0∞) < 2
-/
protected theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  ENNReal.inv_lt_one.2 <| one_lt_two
/-
**ENNReal.half_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / 2 < a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_two`：coe_two : ((2 : Real>=0) : Real>=0∞) = 2
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `NNReal.half_lt_self`：∀ {a : NNReal}, a ≠ 0 → a / 2 < a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
-/
protected theorem half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a := by
  lift a to ℝ≥0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two, ← coe_div, coe_lt_coe]
  exacts [NNReal.half_lt_self hz, two_ne_zero' _]
/-
**ENNReal.half_le_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a / 2 ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a
-/
protected theorem half_le_self : a / 2 ≤ a :=
  le_add_self.trans_eq <| ENNReal.add_halves _
/-
**ENNReal.sub_half** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：sub_half (h : a != ∞) : a - a / 2 = a / 2
参数：h : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.sub_eq_of_eq_add'`：∀ {a b c : ENNReal}, a ≠ ⊤ → a = c + b → a - 
b = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a
-/
theorem sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 := ENNReal.sub_eq_of_eq_add' h a.add_halves.symm

@[simp]
/-
**ENNReal.one_sub_inv_two** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.sub_half`：sub_half (h : a != ∞) : a - a / 2 = a / 2
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
-/
theorem one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
  rw [← one_div, sub_half one_ne_top]
/-
**ENNReal.exists_lt_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_mul_left {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc, ha'⟩ := exists_between (ENNReal.div_lt_of_lt_mul hc)
  exact ⟨_, ha', (ENNReal.div_lt_iff (.inl <| by rintro rfl; simp at *)
    (.inr <| by rintro rfl; simp at *)).1 hc⟩
/-
**ENNReal.exists_lt_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_mul_right {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ b' < b, c < a * b' := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_lt_mul_left hc
/-
**ENNReal.mul_le_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_le_of_forall_lt {a b c : Real>=0∞} (h : forall a' < a, forall b' < b, 
a' * b' <= c) : a * b <= c
参数：h : forall a' < a, forall b' < b, a' * b' <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `_private.Mathlib.Data.ENNReal.Inv.0.ENNReal.exists_lt_mul_left`：∀ {a b c
 : ENNReal}, c < a * b → ∃ a' < a, c < a' * b
· 使用定理 `_private.Mathlib.Data.ENNReal.Inv.0.ENNReal.exists_lt_mul_right`：∀ {a b 
c : ENNReal}, c < a * b → ∃ b' < b, c < a * b'
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma mul_le_of_forall_lt {a b c : ℝ≥0∞} (h : ∀ a' < a, ∀ b' < b, a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact le_trans hd.le <| h _ ha' _ hb'
/-
**ENNReal.le_mul_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：le_mul_of_forall_lt {a b c : Real>=0∞} (h₁ : a != 0 ∨ b != ∞) (h₂ : a != ∞
 ∨ b != 0) (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a * b
参数：h₁ : a != 0 ∨ b != ∞；h₂ : a != ∞ ∨ b != 0；h : forall a' > a, forall b' > b, c
 <= a' * b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_le_inv`：∀ {a b : ENNReal}, a⁻¹ ≤ b⁻¹ ↔ b ≤ a
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用引理 `ENNReal.mul_le_of_forall_lt`：mul_le_of_forall_lt {a b c : Real>=0∞} (h :
 forall a' < a, forall b' < b, a' * b' <= c) : a * b <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.le_inv_iff_le_inv`：le_inv_iff_le_inv : a <= b⁻¹ ↔ b <= a⁻¹
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ENNReal.lt_inv_iff_lt_inv`：lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
-/
lemma le_mul_of_forall_lt {a b c : ℝ≥0∞} (h₁ : a ≠ 0 ∨ b ≠ ∞) (h₂ : a ≠ ∞ ∨ b ≠ 0)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  rw [← ENNReal.inv_le_inv, ENNReal.mul_inv h₁ h₂]
  exact mul_le_of_forall_lt fun a' ha' b' hb' ↦ ENNReal.le_inv_iff_le_inv.1 <|
    (h _ (ENNReal.lt_inv_iff_lt_inv.1 ha') _ (ENNReal.lt_inv_iff_lt_inv.1 hb')).trans_eq
    (ENNReal.mul_inv (Or.inr hb'.ne_top) (Or.inl ha'.ne_top)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)`. -/
@[simps! apply_coe]
/-
**ENNReal.orderIsoIicOneBirational** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：orderIsoIicOneBirational : Real>=0∞ ≃o Iic (1 : Real>=0∞)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The birational order isomorphism between `ℝ≥0∞` and the unit interval `Set.Iic (
1 : ℝ≥0∞)`.
-/
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℝ≥0∞) ≤ x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, tsub_add_cancel_of_le this]

@[simp]
/-
**ENNReal.orderIsoIicOneBirational_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal
`。
形式化陈述：orderIsoIicOneBirational_symm_apply (x : Iic (1 : Real>=0∞)) : orderIsoIic
OneBirational.symm x = (x.1⁻¹ - 1)⁻¹
参数：x : Iic (1 : Real>=0∞)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
    orderIsoIicOneBirational.symm x = (x.1⁻¹ - 1)⁻¹ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps! apply_coe]
/-
**ENNReal.orderIsoIicCoe** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：orderIsoIicCoe (a : Real>=0) : Iic (a : Real>=0∞) ≃o Iic a
参数：a : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval 
in `ℝ≥0`.
-/
def orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
      invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 <| coe_toNNReal_le_self.trans x.2⟩
      left_inv := fun _ => Subtype.ext <| toNNReal_coe _
      right_inv := fun x => Subtype.ext <| coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

@[simp]
/-
**ENNReal.orderIsoIicCoe_symm_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：orderIsoIicCoe_symm_apply_coe (a : Real>=0) (b : Iic a) : ((orderIsoIicCoe
 a).symm b : Real>=0∞) = b
参数：a : Real>=0；b : Iic a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoIicCoe_symm_apply_coe (a : ℝ≥0) (b : Iic a) :
    ((orderIsoIicCoe a).symm b : ℝ≥0∞) = b :=
  rfl

/-- An order isomorphism between the extended nonnegative real numbers and the unit interval. -/
/-
**ENNReal.orderIsoUnitIntervalBirational** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：orderIsoUnitIntervalBirational : Real>=0∞ ≃o Icc (0 : Real) 1
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order isomorphism between the extended nonnegative real numbers and the unit 
interval.
-/
def orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
  orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (NNReal.orderIsoIccZeroCoe 1).symm

@[simp]
/-
**ENNReal.orderIsoUnitIntervalBirational_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `EN
NReal`。
形式化陈述：orderIsoUnitIntervalBirational_apply_coe (x : Real>=0∞) : (orderIsoUnitInt
ervalBirational x : Real) = (x⁻¹ + 1)⁻¹.toReal
参数：x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoUnitIntervalBirational_apply_coe (x : ℝ≥0∞) :
    (orderIsoUnitIntervalBirational x : ℝ) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl
/-
**ENNReal.exists_inv_nat_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_inv_nat_lt {a : Real>=0∞} (h : a != 0) : exists n : Nat, (n : Real>
=0∞)⁻¹ < a
参数：h : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.exists_nat_gt`：∀ {r : ENNReal}, r ≠ ⊤ → ∃ n, r < ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) : ∃ n : ℕ, (n : ℝ≥0∞)⁻¹ < a :=
  inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]
/-
**ENNReal.exists_nat_pos_mul_gt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_nat_pos_mul_gt (ha : a != 0) (hb : b != ∞) : exists n > 0, b < (n :
 Nat) * a
参数：ha : a != 0；hb : b != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_nat_gt`：∀ {r : ENNReal}, r ≠ ⊤ → ∃ n, r < ↑n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.div_lt_top`：div_lt_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y !=
 0) : x / y < ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_lt_iff`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ c ≠ ⊤ →
 (c / b < a ↔ c < a * b)
-/
theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a :=
  let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 hn.pos, by
    rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩
/-
**ENNReal.exists_nat_mul_gt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_nat_mul_gt (ha : a != 0) (hb : b != ∞) : exists n : Nat, b < n * a
参数：ha : a != 0；hb : b != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.exists_nat_pos_mul_gt`：exists_nat_pos_mul_gt (ha : a != 0) (hb :
 b != ∞) : exists n > 0, b < (n : Nat) * a
-/
theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right
/-
**ENNReal.exists_nat_pos_inv_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_nat_pos_inv_mul_lt (ha : a != ∞) (hb : b != 0) : exists n > 0, ((n 
: Nat) : Real>=0∞)⁻¹ * a < b
参数：ha : a != ∞；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_nat_pos_mul_gt`：exists_nat_pos_mul_gt (ha : a != 0) (hb :
 b != ∞) : exists n > 0, b < (n : Nat) * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `ENNReal.div_lt_of_lt_mul'`：div_lt_of_lt_mul' (h : a < b * c) : a / b < c
-/
theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
    ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b := by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [← ENNReal.div_eq_inv_mul]
  exact div_lt_of_lt_mul' hn
/-
**ENNReal.exists_nnreal_pos_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_nnreal_pos_mul_lt (ha : a != ∞) (hb : b != 0) : exists n > 0, ↑(n :
 Real>=0) * a < b
参数：ha : a != ∞；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_nat_pos_inv_mul_lt`：exists_nat_pos_inv_mul_lt (ha : a != 
∞) (hb : b != 0) : exists n > 0, ((n : Nat) : Real>=0∞)⁻¹ * a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℝ≥0) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : ℝ≥0)⁻¹
  simp [*, npos.ne']
/-
**ENNReal.exists_inv_two_pow_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_inv_two_pow_lt (ha : a != 0) : exists n : Nat, 2⁻¹ ^ n < a
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.exists_inv_nat_lt`：exists_inv_nat_lt {a : Real>=0∞} (h : a != 0)
 : exists n : Nat, (n : Real>=0∞)⁻¹ < a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `ENNReal.inv_lt_inv`：∀ {a b : ENNReal}, a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Nat.lt_two_pow_self`：∀ {n : ℕ}, n < 2 ^ n
-/
theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine ⟨n, lt_trans ?_ hn⟩
  rw [← ENNReal.inv_pow, ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow_self

@[simp, norm_cast]
/-
**ENNReal.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_zpow (hr : r != 0) (n : Int) : (↑(r ^ n) : Real>=0∞) = (r : Real>=0∞) 
^ n
参数：hr : r != 0；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
-/
theorem coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r ^ n) : ℝ≥0∞) = (r : ℝ≥0∞) ^ n := by
  rcases n with n | n
  · simp only [Int.ofNat_eq_natCast, coe_pow, zpow_natCast]
  · have : r ^ n.succ ≠ 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]
/-
**ENNReal.zero_zpow_def** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：zero_zpow_def (n : Int) : (0 : Real>=0∞) ^ n = if n = 0 then 1 else if 0 <
 n then 0 else ⊤
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
-/
lemma zero_zpow_def (n : ℤ) : (0 : ℝ≥0∞) ^ n = if n = 0 then 1 else if 0 < n then 0 else ⊤ := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]
/-
**ENNReal.top_zpow_def** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：top_zpow_def (n : Int) : (⊤ : Real>=0∞) ^ n = if n = 0 then 1 else if 0 < 
n then ⊤ else 0
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `ENNReal.top_pow`：∀ {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
-/
lemma top_zpow_def (n : ℤ) : (⊤ : ℝ≥0∞) ^ n = if n = 0 then 1 else if 0 < n then ⊤ else 0 := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]
/-
**ENNReal.zpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zpow_pos (ha : a != 0) (h'a : a != ∞) (n : Int) : 0 < a ^ n
参数：ha : a != 0；h'a : a != ∞；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `ENNReal.pow_pos`：∀ {a : ENNReal}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · simpa using ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne, ENNReal.inv_pos, false_and,
      not_false_eq_true]
/-
**ENNReal.zpow_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zpow_lt_top (ha : a != 0) (h'a : a != ∞) (n : Int) : a ^ n < ∞
参数：ha : a != 0；h'a : a != ∞；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `ENNReal.pow_lt_top`：pow_lt_top (ha : a < ∞) : a ^ n < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.pow_pos`：∀ {a : ENNReal}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · simpa using ENNReal.pow_lt_top h'a.lt_top
  · simp only [ENNReal.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]

@[aesop (rule_sets := [finiteness]) unsafe apply]
/-
**ENNReal.zpow_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：zpow_ne_top {a : Real>=0∞} (ha : a != 0) (h'a : a != ∞) (n : Int) : a ^ n 
!= ∞
参数：ha : a != 0；h'a : a != ∞；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.zpow_lt_top`：zpow_lt_top (ha : a != 0) (h'a : a != ∞) (n : Int) 
: a ^ n < ∞
-/
lemma zpow_ne_top {a : ℝ≥0∞} (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n ≠ ∞ :=
  (ENNReal.zpow_lt_top ha h'a n).ne
/-
**ENNReal.exists_mem_Ico_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_mem_Ico_zpow {x y : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 
< y) (h'y : y != ⊤) : exists n : Int, x in Ico (y ^ n) (y ^ (n + 1))
参数：hx : x != 0；h'x : x != ∞；hy : 1 < y；h'y : y != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `NNReal.exists_mem_Ico_zpow`：∀ {x y : NNReal}, x ≠ 0 → 1 < y → ∃ n, x ∈ S
et.Ico (y ^ n) (y ^ (n + 1))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.one_lt_coe_iff`：one_lt_coe_iff : 1 < (↑p : Real>=0∞) ↔ 1 < p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_zpow`：coe_zpow (hr : r != 0) (n : Int) : (↑(r ^ n) : Real>=0
∞) = (r : Real>=0∞) ^ n
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
theorem exists_mem_Ico_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
    refine NNReal.exists_mem_Ico_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
/-
**ENNReal.exists_mem_Ioc_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_mem_Ioc_zpow {x y : Real>=0∞} (hx : x != 0) (h'x : x != ∞) (hy : 1 
< y) (h'y : y != ⊤) : exists n : Int, x in Ioc (y ^ n) (y ^ (n + 1))
参数：hx : x != 0；h'x : x != ∞；hy : 1 < y；h'y : y != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `NNReal.exists_mem_Ioc_zpow`：∀ {x y : NNReal}, x ≠ 0 → 1 < y → ∃ n, x ∈ S
et.Ioc (y ^ n) (y ^ (n + 1))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.one_lt_coe_iff`：one_lt_coe_iff : 1 < (↑p : Real>=0∞) ↔ 1 < p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_zpow`：coe_zpow (hr : r != 0) (n : Int) : (↑(r ^ n) : Real>=0
∞) = (r : Real>=0∞) ^ n
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem exists_mem_Ioc_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) := by
    refine NNReal.exists_mem_Ioc_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
/-
**ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：Ioo_zero_top_eq_iUnion_Ico_zpow {y : Real>=0∞} (hy : 1 < y) (h'y : y != ⊤)
 : Ioo (0 : Real>=0∞) (∞ : Real>=0∞) = ⋃ n : Int, Ico (y ^ n) (y ^ (n + 1))
参数：hy : 1 < y；h'y : y != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.exists_mem_Ico_zpow`：exists_mem_Ico_zpow {x y : Real>=0∞} (hx : 
x != 0) (h'x : x != ∞) (hy : 1 < y) (h'y : y != ⊤) : exists n : Int, x in Ico (y
 ^ n) (y ^ (n + 1…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `ENNReal.zpow_pos`：zpow_pos (ha : a != 0) (h'a : a != ∞) (n : Int) : 0 < 
a ^ n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `ENNReal.zpow_lt_top`：zpow_lt_top (ha : a != 0) (h'a : a != ∞) (n : Int) 
: a ^ n < ∞
-/
theorem Ioo_zero_top_eq_iUnion_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
    Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]
/-
**ENNReal.zpow_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zpow_le_of_le {x : Real>=0∞} (hx : 1 <= x) {a b : Int} (h : a <= b) : x ^ 
a <= x ^ b
参数：hx : 1 <= x；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `pow_right_mono₀`：pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h 
: 1 <= a) : Monotone (a ^ ·)
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Int.le_of_ofNat_le_ofNat`：∀ {m n : ℕ}, ↑m ≤ ↑n → m ≤ n
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Int.negSucc_lt_zero`：∀ (n : ℕ), Int.negSucc n < 0
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_le_one`：∀ {a : ENNReal}, a⁻¹ ≤ 1 ↔ 1 ≤ a
· 使用定理 `one_le_pow_of_one_le'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preo
rder M] [MulLeftMono M] {a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  obtain a | a := a <;> obtain b | b := b
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.natCast_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_natCast, zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.natCast_add, Int.ofNat_one] using! h
/-
**ENNReal.monotone_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：monotone_zpow {x : Real>=0∞} (hx : 1 <= x) : Monotone ((x ^ ·) : Int -> Re
al>=0∞)
参数：hx : 1 <= x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.zpow_le_of_le`：zpow_le_of_le {x : Real>=0∞} (hx : 1 <= x) {a b :
 Int} (h : a <= b) : x ^ a <= x ^ b
-/
theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((x ^ ·) : ℤ → ℝ≥0∞) := fun _ _ h =>
  zpow_le_of_le hx h
/-
**ENNReal.zpow_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x ≠ 0 → x ≠ ⊤ → ∀ (m n : ℤ), x ^ (m + n) = x ^ m * x ^ n
参数：m n : ℤ；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_zpow`：coe_zpow (hr : r != 0) (n : Int) : (↑(r ^ n) : Real>=0
∞) = (r : Real>=0∞) ^ n
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
    x ^ (m + n) = x ^ m * x ^ n := by
  lift x to ℝ≥0 using h'x
  replace hx : x ≠ 0 := by simpa only [Ne, coe_eq_zero] using hx
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]
/-
**ENNReal.zpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : ENNReal) (m : ℤ), x ^ (-m) = (x ^ m)⁻¹
参数：x : ENNReal；m : ℤ；-m；x ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENNReal.zero_zpow_def`：zero_zpow_def (n : Int) : (0 : Real>=0∞) ^ n = if
 n = 0 then 1 else if 0 < n then 0 else ⊤
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用引理 `ENNReal.top_zpow_def`：top_zpow_def (n : Int) : (⊤ : Real>=0∞) ^ n = if n
 = 0 then 1 else if 0 < n then ⊤ else 0
· 使用定理 `ENNReal.eq_inv_of_mul_eq_one_left`：∀ {a b : ENNReal}, a * b = 1 → a = b⁻
¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.zpow_add`：∀ {x : ENNReal}, x ≠ 0 → x ≠ ⊤ → ∀ (m n : ℤ), x ^ (m +
 n) = x ^ m * x ^ n
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
protected theorem zpow_neg (x : ℝ≥0∞) (m : ℤ) : x ^ (-m) = (x ^ m)⁻¹ := by
  obtain hx₀ | hx₀ := eq_or_ne x 0
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [zero_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  obtain hx | hx := eq_or_ne x ⊤
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [top_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simp [← ENNReal.zpow_add hx₀ hx])
/-
**ENNReal.zpow_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal}, x ≠ 0 → x ≠ ⊤ → ∀ (m n : ℤ), x ^ (m - n) = x ^ m * (x ^ n
)⁻¹
参数：m n : ℤ；m - n；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ENNReal.zpow_add`：∀ {x : ENNReal}, x ≠ 0 → x ≠ ⊤ → ∀ (m n : ℤ), x ^ (m +
 n) = x ^ m * x ^ n
· 使用定理 `ENNReal.zpow_neg`：∀ (x : ENNReal) (m : ℤ), x ^ (-m) = (x ^ m)⁻¹
-/
protected theorem zpow_sub {x : ℝ≥0∞} (x_ne_zero : x ≠ 0) (x_ne_top : x ≠ ⊤) (m n : ℤ) :
    x ^ (m - n) = (x ^ m) * (x ^ n)⁻¹ := by
  rw [sub_eq_add_neg, ENNReal.zpow_add x_ne_zero x_ne_top, ENNReal.zpow_neg]
/-
**ENNReal.inv_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : ENNReal) (n : ℤ), x⁻¹ ^ n = (x ^ n)⁻¹
参数：x : ENNReal；n : ℤ；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
protected lemma inv_zpow (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  cases n <;> simp [ENNReal.inv_pow]
/-
**ENNReal.inv_zpow'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : ENNReal) (n : ℤ), x⁻¹ ^ n = x ^ (-n)
参数：x : ENNReal；n : ℤ；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zpow_neg`：∀ (x : ENNReal) (m : ℤ), x ^ (-m) = (x ^ m)⁻¹
· 使用定理 `ENNReal.inv_zpow`：∀ (x : ENNReal) (n : ℤ), x⁻¹ ^ n = (x ^ n)⁻¹
-/
protected lemma inv_zpow' (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = x ^ (-n) := by
  rw [ENNReal.zpow_neg, ENNReal.inv_zpow]
/-
**ENNReal.zpow_le_one_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：zpow_le_one_of_nonpos {n : Int} (hn : n <= 0) {x : Real>=0∞} (hx : 1 <= x)
 : x ^ n <= 1
参数：hn : n <= 0；hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_surjective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Surj
ective Neg.neg
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.inv_zpow'`：∀ (x : ENNReal) (n : ℤ), x⁻¹ ^ n = x ^ (-n)
· 使用定理 `ENNReal.inv_zpow`：∀ (x : ENNReal) (n : ℤ), x⁻¹ ^ n = (x ^ n)⁻¹
· 使用定理 `ENNReal.inv_le_one`：∀ {a : ENNReal}, a⁻¹ ≤ 1 ↔ 1 ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma zpow_le_one_of_nonpos {n : ℤ} (hn : n ≤ 0) {x : ℝ≥0∞} (hx : 1 ≤ x) : x ^ n ≤ 1 := by
  obtain ⟨m, rfl⟩ := neg_surjective n
  lift m to ℕ using by simpa using hn
  rw [← ENNReal.inv_zpow', ENNReal.inv_zpow, ENNReal.inv_le_one]
  exact mod_cast one_le_pow₀ hx
/-
**ENNReal.isUnit_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：isUnit_iff : IsUnit a ↔ a != 0 ∧ a != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
-/
lemma isUnit_iff : IsUnit a ↔ a ≠ 0 ∧ a ≠ ∞ := by
  refine ⟨fun ha ↦ ⟨ha.ne_zero, ?_⟩,
    fun ha ↦ ⟨⟨a, a⁻¹, ENNReal.mul_inv_cancel ha.1 ha.2, ENNReal.inv_mul_cancel ha.1 ha.2⟩, rfl⟩⟩
  obtain ⟨u, rfl⟩ := ha
  rintro hu
  have := congr($hu * u⁻¹)
  simp at this

/-- Left multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
/-
**ENNReal.mulLeftOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：mulLeftOrderIso (a : Real>=0∞) (ha : IsUnit a) : Real>=0∞ ≃o Real>=0∞ wher
e toEquiv
参数：a : Real>=0∞；ha : IsUnit a。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by a nonzero finite `a` as an order isomorphism.
-/
def mulLeftOrderIso (a : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulLeft
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_right, ha.ne_zero, (isUnit_iff.1 ha).2]

/-- Right multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
/-
**ENNReal.mulRightOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：mulRightOrderIso (a : Real>=0∞) (ha : IsUnit a) : Real>=0∞ ≃o Real>=0∞ whe
re toEquiv
参数：a : Real>=0∞；ha : IsUnit a。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication by a nonzero finite `a` as an order isomorphism.
-/
def mulRightOrderIso (a : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulRight
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_left, ha.ne_zero, (isUnit_iff.1 ha).2]

variable {ι κ : Sort*} {f g : ι → ℝ≥0∞} {s : Set ℝ≥0∞} {a : ℝ≥0∞}
/-
**ENNReal.mul_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i, f i = ⨆ i, a * f i
参数：a : Real>=0∞；f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ENNReal.iSup_eq_zero`：∀ {ι : Sort u_1} {f : ι → ENNReal}, ⨆ i, f i = 0 ↔
 ∀ (i : ι), f i = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
· 使用引理 `ENNReal.isUnit_iff`：isUnit_iff : IsUnit a ↔ a != 0 ∧ a != ∞
-/
lemma mul_iSup (a : ℝ≥0∞) (f : ι → ℝ≥0∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
  by_cases hf : ∀ i, f i = 0
  · simp [hf]
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ := not_forall.1 hf
    simpa [iSup_eq_zero.not.2 hf, eq_comm (a := ⊤)]
      using le_iSup_of_le (f := fun i => ⊤ * f i) i (top_mul hi).ge
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iSup _
/-
**ENNReal.iSup_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_mul (f : ι -> Real>=0∞) (a : Real>=0∞) : (⨆ i, f i) * a = ⨆ i, f i * 
a
参数：f : ι -> Real>=0∞；a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_mul (f : ι → ℝ≥0∞) (a : ℝ≥0∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp [mul_comm, mul_iSup]
/-
**ENNReal.mul_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_sSup {a : Real>=0∞} : a * sSup s = ⨆ b in s, a * b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_sSup {a : ℝ≥0∞} : a * sSup s = ⨆ b ∈ s, a * b := by
  simp only [sSup_eq_iSup, mul_iSup]
/-
**ENNReal.sSup_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：sSup_mul {a : Real>=0∞} : sSup s * a = ⨆ b in s, b * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `ENNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0∞) (a : Real>=0∞) : (⨆ i, f 
i) * a = ⨆ i, f i * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sSup_mul {a : ℝ≥0∞} : sSup s * a = ⨆ b ∈ s, b * a := by
  simp only [sSup_eq_iSup, iSup_mul]
/-
**ENNReal.iSup_div** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_div (f : ι -> Real>=0∞) (a : Real>=0∞) : iSup f / a = ⨆ i, f i / a
参数：f : ι -> Real>=0∞；a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0∞) (a : Real>=0∞) : (⨆ i, f 
i) * a = ⨆ i, f i * a
-/
lemma iSup_div (f : ι → ℝ≥0∞) (a : ℝ≥0∞) : iSup f / a = ⨆ i, f i / a := iSup_mul ..
/-
**ENNReal.sSup_div** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：sSup_div (s : Set Real>=0∞) (a : Real>=0∞) : sSup s / a = ⨆ b in s, b / a
参数：s : Set Real>=0∞；a : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.sSup_mul`：sSup_mul {a : Real>=0∞} : sSup s * a = ⨆ b in s, b * a
-/
lemma sSup_div (s : Set ℝ≥0∞) (a : ℝ≥0∞) : sSup s / a = ⨆ b ∈ s, b / a := sSup_mul ..

/-- Very general version for distributivity of multiplication over an infimum.

See `ENNReal.mul_iInf_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.mul_iInf` for the special case assuming `Nonempty ι`. -/
/-
**ENNReal.mul_iInf'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_iInf' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = 
0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i
参数：hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0；h₀ : a = 0 -> Nonempty ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInf_eq_bot`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLinearOrder
 α] {f : ι → α}, iInf f = ⊥ ↔ ∀ (b : α), ⊥ < b → ∃ i, f i < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.bot_eq_zero`：bot_eq_zero : (⊥ : Real>=0∞) = 0
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iInf_eq_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{s : ι → α}, iInf s = ⊤ ↔ ∀ (i : ι), s i = ⊤
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
· 使用引理 `ENNReal.isUnit_iff`：isUnit_iff : IsUnit a ↔ a != 0 ∧ a != ∞

--- 原说明 ---
Very general version for distributivity of multiplication over an infimum.

See `ENNReal.mul_iInf_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, 
and
`ENNReal.mul_iInf` for the special case assuming `Nonempty ι`.
-/
lemma mul_iInf' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [h₀ rfl]
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ | hf := em (∃ i, f i = 0)
    · rw [iInf_eq_bot.2, iInf_eq_bot.2, bot_eq_zero, mul_zero] <;>
        exact fun _ _ ↦ ⟨i, by simpa [hi]⟩
    · rw [top_mul (mt (hinfty rfl) hf), eq_comm, iInf_eq_top]
      exact fun i ↦ top_mul fun hi ↦ hf ⟨i, hi⟩
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iInf _

/-- Very general version for distributivity of multiplication over an infimum.

See `ENNReal.iInf_mul_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.iInf_mul` for the special case assuming `Nonempty ι`. -/
/-
**ENNReal.iInf_mul'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_mul' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = 
0 -> Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a
参数：hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0；h₀ : a = 0 -> Nonempty ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ENNReal.mul_iInf'`：mul_iInf' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = 0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i

--- 原说明 ---
Very general version for distributivity of multiplication over an infimum.

See `ENNReal.iInf_mul_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, 
and
`ENNReal.iInf_mul` for the special case assuming `Nonempty ι`.
-/
lemma iInf_mul' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    (⨅ i, f i) * a = ⨅ i, f i * a := by simpa only [mul_comm a] using mul_iInf' hinfty h₀

/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.

See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another special case that
assumes `Nonempty ι` but does not require `a ≠ 0`, and `ENNReal`. -/
/-
**ENNReal.mul_iInf_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_iInf_of_ne (ha₀ : a != 0) (ha : a != ∞) : a * ⨅ i, f i = ⨅ i, a * f i
参数：ha₀ : a != 0；ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.mul_iInf'`：mul_iInf' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = 0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum
.

See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another
 special case that
assumes `Nonempty ι` but does not require `a ≠ 0`, and `ENNReal`.
-/
lemma mul_iInf_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * ⨅ i, f i = ⨅ i, a * f i :=
  mul_iInf' (by simp [ha]) (by simp [ha₀])

/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.

See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul` for another special case that
assumes `Nonempty ι` but does not require `a ≠ 0`. -/
/-
**ENNReal.iInf_mul_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_mul_of_ne (ha₀ : a != 0) (ha : a != ∞) : (⨅ i, f i) * a = ⨅ i, f i * 
a
参数：ha₀ : a != 0；ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.iInf_mul'`：iInf_mul' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = 0 -> Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum
.

See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul` for another
 special case that
assumes `Nonempty ι` but does not require `a ≠ 0`.
-/
lemma iInf_mul_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  iInf_mul' (by simp [ha]) (by simp [ha₀])

/-- See `ENNReal.mul_iInf'` for the general case, and `ENNReal.mul_iInf_of_ne` for another special
case that assumes `a ≠ 0` but does not require `Nonempty ι`. -/
/-
**ENNReal.mul_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：mul_iInf [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0
) : a * ⨅ i, f i = ⨅ i, a * f i
参数：hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.mul_iInf'`：mul_iInf' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = 0 -> Nonempty ι) : a * ⨅ i, f i = ⨅ i, a * f i

--- 原说明 ---
See `ENNReal.mul_iInf'` for the general case, and `ENNReal.mul_iInf_of_ne` for a
nother special
case that assumes `a ≠ 0` but does not require `Nonempty ι`.
-/
lemma mul_iInf [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    a * ⨅ i, f i = ⨅ i, a * f i := mul_iInf' hinfty fun _ ↦ ‹Nonempty ι›

/-- See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul_of_ne` for another special
case that assumes `a ≠ 0` but does not require `Nonempty ι`. -/
/-
**ENNReal.iInf_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_mul [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0
) : (⨅ i, f i) * a = ⨅ i, f i * a
参数：hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i, f i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.iInf_mul'`：iInf_mul' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = 0 -> Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a

--- 原说明 ---
See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul_of_ne` for a
nother special
case that assumes `a ≠ 0` but does not require `Nonempty ι`.
-/
lemma iInf_mul [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) * a = ⨅ i, f i * a := iInf_mul' hinfty fun _ ↦ ‹Nonempty ι›

/-- Very general version for distributivity of division over an infimum.

See `ENNReal.iInf_div_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.iInf_div` for the special case assuming `Nonempty ι`. -/
/-
**ENNReal.iInf_div'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_div' (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0) (h₀ : a = 
∞ -> Nonempty ι) : (⨅ i, f i) / a = ⨅ i, f i / a
参数：hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0；h₀ : a = ∞ -> Nonempty ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.iInf_mul'`：iInf_mul' (hinfty : a = ∞ -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = 0 -> Nonempty ι) : (⨅ i, f i) * a = ⨅ i, f i * a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Very general version for distributivity of division over an infimum.

See `ENNReal.iInf_div_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, 
and
`ENNReal.iInf_div` for the special case assuming `Nonempty ι`.
-/
lemma iInf_div' (hinfty : a = 0 → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = ∞ → Nonempty ι) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_mul' (by simpa) (by simpa)

/-- If `a ≠ 0` and `a ≠ ∞`, then division by `a` maps infimum to infimum.

See `ENNReal.iInf_div'` for the general case, and `ENNReal.iInf_div` for another special case that
assumes `Nonempty ι` but does not require `a ≠ ∞`. -/
/-
**ENNReal.iInf_div_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_div_of_ne (ha₀ : a != 0) (ha : a != ∞) : (⨅ i, f i) / a = ⨅ i, f i / 
a
参数：ha₀ : a != 0；ha : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.iInf_div'`：iInf_div' (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = ∞ -> Nonempty ι) : (⨅ i, f i) / a = ⨅ i, f i / a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If `a ≠ 0` and `a ≠ ∞`, then division by `a` maps infimum to infimum.

See `ENNReal.iInf_div'` for the general case, and `ENNReal.iInf_div` for another
 special case that
assumes `Nonempty ι` but does not require `a ≠ ∞`.
-/
lemma iInf_div_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : (⨅ i, f i) / a = ⨅ i, f i / a :=
  iInf_div' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.iInf_div'` for the general case, and `ENNReal.iInf_div_of_ne` for another special
case that assumes `a ≠ ∞` but does not require `Nonempty ι`. -/
/-
**ENNReal.iInf_div** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_div [Nonempty ι] (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0
) : (⨅ i, f i) / a = ⨅ i, f i / a
参数：hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i, f i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.iInf_div'`：iInf_div' (hinfty : a = 0 -> ⨅ i, f i = 0 -> exists i
, f i = 0) (h₀ : a = ∞ -> Nonempty ι) : (⨅ i, f i) / a = ⨅ i, f i / a

--- 原说明 ---
See `ENNReal.iInf_div'` for the general case, and `ENNReal.iInf_div_of_ne` for a
nother special
case that assumes `a ≠ ∞` but does not require `Nonempty ι`.
-/
lemma iInf_div [Nonempty ι] (hinfty : a = 0 → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_div' hinfty fun _ ↦ ‹Nonempty ι›
/-
**ENNReal.inv_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：inv_iInf (f : ι -> Real>=0∞) : (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹
参数：f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
lemma inv_iInf (f : ι → ℝ≥0∞) : (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹ := OrderIso.invENNReal.map_iInf _
/-
**ENNReal.inv_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：inv_iSup (f : ι -> Real>=0∞) : (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹
参数：f : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
lemma inv_iSup (f : ι → ℝ≥0∞) : (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹ := OrderIso.invENNReal.map_iSup _
/-
**ENNReal.inv_sInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：inv_sInf (s : Set Real>=0∞) : (sInf s)⁻¹ = ⨆ a in s, a⁻¹
参数：s : Set Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用引理 `ENNReal.inv_iInf`：inv_iInf (f : ι -> Real>=0∞) : (⨅ i, f i)⁻¹ = ⨆ i, (f 
i)⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_sInf (s : Set ℝ≥0∞) : (sInf s)⁻¹ = ⨆ a ∈ s, a⁻¹ := by simp [sInf_eq_iInf, inv_iInf]
/-
**ENNReal.inv_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：inv_sSup (s : Set Real>=0∞) : (sSup s)⁻¹ = ⨅ a in s, a⁻¹
参数：s : Set Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用引理 `ENNReal.inv_iSup`：inv_iSup (f : ι -> Real>=0∞) : (⨆ i, f i)⁻¹ = ⨅ i, (f 
i)⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_sSup (s : Set ℝ≥0∞) : (sSup s)⁻¹ = ⨅ a ∈ s, a⁻¹ := by simp [sSup_eq_iSup, inv_iSup]
/-
**ENNReal.le_iInf_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：le_iInf_mul {ι : Type*} (u v : ι -> Real>=0∞) : (⨅ i, u i) * ⨅ i, v i <= ⨅
 i, u i * v i
参数：u v : ι -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma le_iInf_mul {ι : Type*} (u v : ι → ℝ≥0∞) :
    (⨅ i, u i) * ⨅ i, v i ≤ ⨅ i, u i * v i :=
  le_iInf fun i ↦ mul_le_mul' (iInf_le u i) (iInf_le v i)
/-
**ENNReal.iSup_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_mul_le {ι : Type*} {u v : ι -> Real>=0∞} : ⨆ i, u i * v i <= (⨆ i, u 
i) * ⨆ i, v i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma iSup_mul_le {ι : Type*} {u v : ι → ℝ≥0∞} :
    ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun i ↦ mul_le_mul' (le_iSup u i) (le_iSup v i)
/-
**ENNReal.le_iInf_mul_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：le_iInf_mul_iInf {g : κ -> Real>=0∞} (hf : exists i, f i != ∞) (hg : exist
s j, g j != ∞) (ha : forall i j, a <= f i * g j) : a <= (⨅ i, f i) * ⨅ j, g j
参数：hf : exists i, f i != ∞；hg : exists j, g j != ∞；ha : forall i j, a <= f i * g
 j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_ne_top_subtype`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLat
tice α] (f : ι → α), ⨅ i, f ↑i = ⨅ i, f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ENNReal.iInf_mul`：iInf_mul [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 
-> exists i, f i = 0) : (⨅ i, f i) * a = ⨅ i, f i * a
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用引理 `ENNReal.mul_iInf`：mul_iInf [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 
-> exists i, f i = 0) : a * ⨅ i, f i = ⨅ i, a * f i
-/
lemma le_iInf_mul_iInf {g : κ → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (ha : ∀ i j, a ≤ f i * g j) : a ≤ (⨅ i, f i) * ⨅ j, g j := by
  rw [← iInf_ne_top_subtype]
  have := nonempty_subtype.2 hf
  have := hg.nonempty
  replace hg : ⨅ j, g j ≠ ∞ := by simpa using hg
  rw [iInf_mul fun h ↦ (hg h).elim, le_iInf_iff]
  rintro ⟨i, hi⟩
  simpa [mul_iInf fun h ↦ (hi h).elim] using ha i
/-
**ENNReal.iInf_mul_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_mul_iInf {f g : ι -> Real>=0∞} (hf : exists i, f i != ∞) (hg : exists
 j, g j != ∞) (h : forall i j, exists k, f k * g k <= f i * g j) : (⨅ i, f i) * 
⨅ i, g i = ⨅ i, f i * g i
参数：hf : exists i, f i != ∞；hg : exists j, g j != ∞；h : forall i j, exists k, f k
 * g k <= f i * g j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用引理 `ENNReal.le_iInf_mul_iInf`：le_iInf_mul_iInf {g : κ -> Real>=0∞} (hf : exi
sts i, f i != ∞) (hg : exists j, g j != ∞) (ha : forall i j, a <= f i * g j) : a
 <= (⨅ i, f i)…
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
-/
lemma iInf_mul_iInf {f g : ι → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (h : ∀ i j, ∃ k, f k * g k ≤ f i * g j) : (⨅ i, f i) * ⨅ i, g i = ⨅ i, f i * g i := by
  refine le_antisymm (le_iInf fun i ↦ mul_le_mul' (iInf_le ..) (iInf_le ..))
    (le_iInf_mul_iInf hf hg fun i j ↦ ?_)
  obtain ⟨k, hk⟩ := h i j
  exact iInf_le_of_le k hk
/-
**ENNReal.smul_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：smul_iSup {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (f : ι
 -> Real>=0∞) (c : R) : c • ⨆ i, f i = ⨆ i, c • f i
参数：f : ι -> Real>=0∞；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用引理 `ENNReal.mul_iSup`：mul_iSup (a : Real>=0∞) (f : ι -> Real>=0∞) : a * ⨆ i,
 f i = ⨆ i, a * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_iSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (f : ι → ℝ≥0∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]
/-
**ENNReal.smul_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：smul_sSup {R} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (s : S
et Real>=0∞) (c : R) : c • sSup s = ⨆ a in s, c • a
参数：s : Set Real>=0∞；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用引理 `ENNReal.mul_sSup`：mul_sSup {a : Real>=0∞} : a * sSup s = ⨆ b in s, a * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_sSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (s : Set ℝ≥0∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a := by
  simp_rw [← smul_one_mul c (sSup s), ENNReal.mul_sSup, smul_one_mul]

@[simp]
/-
**ENNReal.ofReal_inv_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : ENNReal.ofReal x⁻¹ = (ENNReal.
ofReal x)⁻¹
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `Real.toNNReal_inv`：∀ {x : ℝ}, x⁻¹.toNNReal = x.toNNReal⁻¹
-/
theorem ofReal_inv_of_pos {x : ℝ} (hx : 0 < x) : ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹ := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_inj,
    ← Real.toNNReal_inv]
/-
**ENNReal.ofReal_inv_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_inv_le {x : Real} : ENNReal.ofReal x⁻¹ <= (ENNReal.ofReal x)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_inv_of_pos`：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : E
NNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
-/
theorem ofReal_inv_le {x : ℝ} : ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
  obtain hx | hx := lt_or_ge 0 x
  · simp [ofReal_inv_of_pos hx]
  · simp [ofReal_of_nonpos hx]
/-
**ENNReal.ofReal_div_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_div_le {x y : Real} (hy : 0 <= y) : ENNReal.ofReal (x / y) <= ENNRe
al.ofReal x / ENNReal.ofReal y
参数：hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_mul'`：ofReal_mul' {p q : Real} (hq : 0 <= q) : ENNReal.of
Real (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.ofReal_inv_le`：ofReal_inv_le {x : Real} : ENNReal.ofReal x⁻¹ <= 
(ENNReal.ofReal x)⁻¹
-/
theorem ofReal_div_le {x y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal (x / y) ≤ ENNReal.ofReal x / ENNReal.ofReal y := by
  simp_rw [div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy)]
  gcongr
  exact ofReal_inv_le
/-
**ENNReal.ofReal_div_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_div_of_pos {x y : Real} (hy : 0 < y) : ENNReal.ofReal (x / y) = ENN
Real.ofReal x / ENNReal.ofReal y
参数：hy : 0 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.ofReal_mul'`：ofReal_mul' {p q : Real} (hq : 0 <= q) : ENNReal.of
Real (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.ofReal_inv_of_pos`：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : E
NNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
-/
theorem ofReal_div_of_pos {x y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy.le), ofReal_inv_of_pos hy]
/-
**ENNReal.toNNReal_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : ENNReal), a⁻¹.toNNReal = a.toNNReal⁻¹
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
-/
@[simp] theorem toNNReal_inv (a : ℝ≥0∞) : a⁻¹.toNNReal = a.toNNReal⁻¹ := by
  cases a with
  | top => simp
  | coe a =>
    rcases eq_or_ne a 0 with (rfl | ha); · simp
    rw [← coe_inv ha, toNNReal_coe, toNNReal_coe]
/-
**ENNReal.toNNReal_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a b : ENNReal), (a / b).toNNReal = a.toNNReal / b.toNNReal
参数：a b : ENNReal；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.toNNReal_mul`：toNNReal_mul {a b : Real>=0∞} : (a * b).toNNReal =
 a.toNNReal * b.toNNReal
· 使用定理 `ENNReal.toNNReal_inv`：∀ (a : ENNReal), a⁻¹.toNNReal = a.toNNReal⁻¹
-/
@[simp] theorem toNNReal_div (a b : ℝ≥0∞) : (a / b).toNNReal = a.toNNReal / b.toNNReal := by
  rw [div_eq_mul_inv, toNNReal_mul, toNNReal_inv, div_eq_mul_inv]
/-
**ENNReal.toReal_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
参数：a : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_inv`：∀ (a : ENNReal), a⁻¹.toNNReal = a.toNNReal⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem toReal_inv (a : ℝ≥0∞) : a⁻¹.toReal = a.toReal⁻¹ := by
  simp only [ENNReal.toReal, toNNReal_inv, NNReal.coe_inv]
/-
**ENNReal.toReal_div** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toReal
参数：a b : ENNReal；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
-/
@[simp] theorem toReal_div (a b : ℝ≥0∞) : (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv, toReal_mul, toReal_inv, div_eq_mul_inv]

end Inv
end ENNReal

