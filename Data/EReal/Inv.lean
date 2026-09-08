/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Data.EReal.Operations
public import Mathlib.Data.Sign.Basic
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Absolute value, sign, inversion and division on extended real numbers

This file defines an absolute value and sign function on `EReal` and uses them to provide a
`CommMonoidWithZero` instance, based on the absolute value and sign characterising all `EReal`s.
Then it defines the inverse of an `EReal` as `⊤⁻¹ = ⊥⁻¹ = 0`, which leads to a
`DivInvMonoid` instance and division.
-/

@[expose] public section

open ENNReal Set SignType

noncomputable section

namespace EReal

/-! ### Absolute value -/

-- TODO: use `Real.nnabs` for the case `(x : ℝ)`
/-- The absolute value from `EReal` to `ℝ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a real `x` to `|x|`. -/
/-
**EReal.abs** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：EReal → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute value from `EReal` to `ℝ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a real `x` to `|x|`.
-/
protected def abs : EReal → ℝ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℝ) => ENNReal.ofReal |x|
/-
**EReal.abs_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊤.abs = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem abs_top : (⊤ : EReal).abs = ⊤ := rfl
/-
**EReal.abs_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：⊥.abs = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem abs_bot : (⊥ : EReal).abs = ⊤ := rfl
/-
**EReal.abs_def** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：abs_def (x : Real) : (x : EReal).abs = ENNReal.ofReal |x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abs_def (x : ℝ) : (x : EReal).abs = ENNReal.ofReal |x| := rfl
/-
**EReal.abs_coe_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：abs_coe_lt_top (x : Real) : (x : EReal).abs < ⊤
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
-/
theorem abs_coe_lt_top (x : ℝ) : (x : EReal).abs < ⊤ :=
  ENNReal.ofReal_lt_top

@[simp]
/-
**EReal.abs_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0 := by
  induction x
  · simp
  · simp only [abs_def, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]

@[simp]
/-
**EReal.abs_zero** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：abs_zero : (0 : EReal).abs = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.abs_eq_zero_iff`：abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0
-/
theorem abs_zero : (0 : EReal).abs = 0 := by rw [abs_eq_zero_iff]

@[simp]
/-
**EReal.coe_abs** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_abs (x : Real) : ((x : EReal).abs : EReal) = (|x| : Real)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.abs_def`：abs_def (x : Real) : (x : EReal).abs = ENNReal.ofReal |x|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_nnabs`：coe_nnabs (x : Real) : (nnabs x : Real) = |x|
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
-/
theorem coe_abs (x : ℝ) : ((x : EReal).abs : EReal) = (|x| : ℝ) := by
  rw [abs_def, ← Real.coe_nnabs, ENNReal.ofReal_coe_nnreal]; rfl

@[simp]
/-
**EReal.abs_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : EReal), (-x).abs = x.abs
参数：x : EReal；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.abs_def`：abs_def (x : Real) : (x : EReal).abs = ENNReal.ofReal |x|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
protected theorem abs_neg : ∀ x : EReal, (-x).abs = x.abs
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [abs_def, ← coe_neg, abs_def, abs_neg]

@[simp]
/-
**EReal.abs_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs
参数：x y : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.induction₂_symm_neg`：induction₂_symm_neg {P : EReal -> EReal -> Pr
op} (symm : forall {x y}, P x y -> P y x) (neg_left : forall {x y}, P x y -> P (
-x) y) (top_top…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `EReal.abs_neg`：∀ (x : EReal), (-x).abs = x.abs
· 使用引理 `EReal.top_mul_coe_of_pos`：top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤
 : EReal) * x = ⊤
· 使用定理 `EReal.abs_top`：⊤.abs = ⊤
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `EReal.abs_eq_zero_iff`：abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0
· 使用定理 `EReal.coe_eq_zero`：coe_eq_zero {x : Real} : (x : EReal) = 0 ↔ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `EReal.abs_zero`：abs_zero : (0 : EReal).abs = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, abs_top, ENNReal.top_mul]
    rw [Ne, abs_eq_zero_iff, coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, EReal.abs_neg, EReal.abs_neg]

/-! ### Sign -/

open SignType (sign)

/-
**EReal.sign_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sign_top : sign (⊤ : EReal) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sign_top : sign (⊤ : EReal) = 1 := rfl
/-
**EReal.sign_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sign_bot : sign (⊥ : EReal) = -1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sign_bot : sign (⊥ : EReal) = -1 := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**EReal.sign_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sign_coe (x : Real) : sign (x : EReal) = sign x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sign_coe (x : ℝ) : sign (x : EReal) = sign x := by
  simp only [sign, OrderHom.coe_mk, EReal.coe_pos, EReal.coe_neg']

@[simp, norm_cast]
/-
**EReal.coe_coe_sign** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_coe_sign (x : SignType) : ((x : Real) : EReal) = x
参数：x : SignType。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_coe_sign (x : SignType) : ((x : ℝ) : EReal) = x := by cases x <;> rfl
/-
**EReal.sign_neg** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : EReal), SignType.sign (-x) = -SignType.sign x
参数：x : EReal；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用定理 `EReal.sign_coe`：sign_coe (x : Real) : sign (x : EReal) = sign x
· 使用定理 `Left.sign_neg`：Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) =
 -sign a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
@[simp] theorem sign_neg : ∀ x : EReal, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [← coe_neg, sign_coe, sign_coe, Left.sign_neg]

@[simp]
/-
**EReal.sign_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sign_mul (x y : EReal) : sign (x * y) = sign x * sign y
参数：x y : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.induction₂_symm_neg`：induction₂_symm_neg {P : EReal -> EReal -> Pr
op} (symm : forall {x y}, P x y -> P y x) (neg_left : forall {x y}, P x y -> P (
-x) y) (top_top…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `EReal.sign_neg`：∀ (x : EReal), SignType.sign (-x) = -SignType.sign x
· 使用引理 `EReal.top_mul_coe_of_pos`：top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤
 : EReal) * x = ⊤
· 使用定理 `EReal.sign_top`：sign_top : sign (⊤ : EReal) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_pos`：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EReal.sign_coe`：sign_coe (x : Real) : sign (x : EReal) = sign x
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y
-/
theorem sign_mul (x y : EReal) : sign (x * y) = sign x * sign y := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, sign_top, one_mul, sign_pos (EReal.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]
/-
**EReal.sign_mul_abs** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : EReal), ↑(SignType.sign x) * ↑x.abs = x
参数：x : EReal；SignType.sign x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `EReal.sign_coe`：sign_coe (x : Real) : sign (x : EReal) = sign x
· 使用定理 `EReal.coe_abs`：coe_abs (x : Real) : ((x : EReal).abs : EReal) = (|x| : R
eal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_coe_sign`：coe_coe_sign (x : SignType) : ((x : Real) : EReal) =
 x
· 使用定理 `EReal.coe_mul`：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
· 使用定理 `sign_mul_abs`：∀ {α : Type u} [inst : Ring α] [inst_1 : LinearOrder α] [I
sStrictOrderedRing α] (x : α), ↑(SignType.sign x) * |x| = x
-/
@[simp] protected theorem sign_mul_abs : ∀ x : EReal, (sign x * x.abs : EReal) = x
  | ⊥ => by simp
  | ⊤ => by simp
  | (x : ℝ) => by rw [sign_coe, coe_abs, ← coe_coe_sign, ← coe_mul, sign_mul_abs]
/-
**EReal.abs_mul_sign** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (x : EReal), ↑x.abs * ↑(SignType.sign x) = x
参数：x : EReal；SignType.sign x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `EReal.sign_mul_abs`：∀ (x : EReal), ↑(SignType.sign x) * ↑x.abs = x
-/
@[simp] protected theorem abs_mul_sign (x : EReal) : (x.abs * sign x : EReal) = x := by
  rw [EReal.mul_comm, EReal.sign_mul_abs]
/-
**EReal.sign_eq_and_abs_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：sign_eq_and_abs_eq_iff_eq {x y : EReal} : x.abs = y.abs ∧ sign x = sign y 
↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.sign_mul_abs`：∀ (x : EReal), ↑(SignType.sign x) * ↑x.abs = x
-/
theorem sign_eq_and_abs_eq_iff_eq {x y : EReal} :
    x.abs = y.abs ∧ sign x = sign y ↔ x = y := by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩
/-
**EReal.le_iff_sign** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：le_iff_sign {x y : EReal} : x <= y ↔ sign x < sign y ∨ sign x = SignType.n
eg ∧ sign y = SignType.neg ∧ y.abs <= x.abs ∨ sign x = SignType.zero ∧ sign y = 
SignType.zero ∨ sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs <= y.abs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `EReal.sign_mul_abs`：∀ (x : EReal), ↑(SignType.sign x) * ↑x.abs = x
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem le_iff_sign {x y : EReal} :
    x ≤ y ↔ sign x < sign y ∨
      sign x = SignType.neg ∧ sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
        sign x = SignType.zero ∧ sign y = SignType.zero ∨
          sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs ≤ y.abs := by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoidWithZero EReal :=
  { (inferInstance : MulZeroOneClass EReal) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosMulMono EReal := posMulMono_iff_covariant_pos.2 <| .mk <| by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, EReal.sign_mul, sign_pos x0, one_mul, EReal.abs_mul] at h ⊢
  exact h.imp_right <| Or.imp (And.imp_right <| And.imp_right (mul_le_mul_right · _)) <|
    Or.imp_right <| And.imp_right <| And.imp_right (mul_le_mul_right · _)
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulPosMono EReal := posMulMono_iff_mulPosMono.1 inferInstance
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PosMulReflectLT EReal := PosMulMono.toPosMulReflectLT
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulPosReflectLT EReal := MulPosMono.toMulPosReflectLT
/-
**EReal.mul_le_mul_of_nonpos_right** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_le_mul_of_nonpos_right {a b c : EReal} (h : b <= a) (hc : c <= 0) : a 
* c <= b * c
参数：h : b <= a；hc : c <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用定理 `EReal.le_neg`：∀ {a b : EReal}, a ≤ -b ↔ b ≤ -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
lemma mul_le_mul_of_nonpos_right {a b c : EReal} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c, ← neg_le_neg_iff, ← neg_mul c b, ← neg_mul c a]
  rw [← neg_zero, EReal.le_neg] at hc
  gcongr

@[simp, norm_cast]
/-
**EReal.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_pow (x : Real) (n : Nat) : (↑(x ^ n) : EReal) = (x : EReal) ^ n
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `EReal.coe_one`：coe_one : ((1 : Real) : EReal) = 1
· 使用定理 `EReal.coe_mul`：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
-/
theorem coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : ℝ →* EReal) _ _

@[simp, norm_cast]
/-
**EReal.coe_ennreal_pow** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：coe_ennreal_pow (x : Real>=0∞) (n : Nat) : (↑(x ^ n) : EReal) = (x : EReal
) ^ n
参数：x : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `EReal.coe_ennreal_one`：coe_ennreal_one : ((1 : Real>=0∞) : EReal) = 1
· 使用定理 `EReal.coe_ennreal_mul`：∀ (x y : ENNReal), ↑(x * y) = ↑x * ↑y
-/
theorem coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_ennreal_one⟩, coe_ennreal_mul⟩ : ℝ≥0∞ →* EReal) _ _
/-
**EReal.exists_nat_ge_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：exists_nat_ge_mul {a : EReal} (ha : a != ⊤) (n : Nat) : exists m : Nat, a 
* n <= m
参数：ha : a != ⊤；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.irrefl`：∀ {α : Sort u} {a : α}, a ≠ a → False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.mul_nonpos_iff`：mul_nonpos_iff {a b : EReal} : a * b <= 0 ↔ 0 <= a
 ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用定理 `EReal.coe_mul`：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
· 使用定理 `EReal.coe_le_coe_iff`：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
-/
lemma exists_nat_ge_mul {a : EReal} (ha : a ≠ ⊤) (n : ℕ) :
    ∃ m : ℕ, a * n ≤ m :=
  match a with
  | ⊤ => ha.irrefl.rec
  | ⊥ => ⟨0, Nat.cast_zero (R := EReal) ▸ mul_nonpos_iff.2 (.inr ⟨bot_le, n.cast_nonneg'⟩)⟩
  | (a : ℝ) => by
    obtain ⟨m, an_m⟩ := exists_nat_ge (a * n)
    use m
    rwa [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, ← EReal.coe_mul, EReal.coe_le_coe_iff]

/-! ### Min and Max -/

/-
**EReal.min_neg_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：min_neg_neg (x y : EReal) : min (-x) (-y) = -max x y
参数：x y : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a

--- 原说明 ---
### Min and Max
-/
lemma min_neg_neg (x y : EReal) : min (-x) (-y) = -max x y := by
  rcases le_total x y with (h | h) <;> simp_all
/-
**EReal.max_neg_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：max_neg_neg (x y : EReal) : max (-x) (-y) = -min x y
参数：x y : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
lemma max_neg_neg (x y : EReal) : max (-x) (-y) = -min x y := by
  rcases le_total x y with (h | h) <;> simp_all

/-! ### Inverse -/

/-- Multiplicative inverse of an `EReal`. We choose `0⁻¹ = 0` to guarantee several good properties,
for instance `(a * b)⁻¹ = a⁻¹ * b⁻¹`. -/
/-
**EReal.inv** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：EReal → EReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative inverse of an `EReal`. We choose `0⁻¹ = 0` to guarantee several g
ood properties,
for instance `(a * b)⁻¹ = a⁻¹ * b⁻¹`.
-/
protected def inv : EReal → EReal
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => (x⁻¹ : ℝ)
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (EReal) := ⟨EReal.inv⟩
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DivInvMonoid EReal where inv := EReal.inv

@[simp]
/-
**EReal.inv_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_bot : (⊥ : EReal)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_bot : (⊥ : EReal)⁻¹ = 0 := rfl

@[simp]
/-
**EReal.inv_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_top : (⊤ : EReal)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_top : (⊤ : EReal)⁻¹ = 0 := rfl
/-
**EReal.coe_inv** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_inv (x : ℝ) : (x⁻¹ : ℝ) = (x : EReal)⁻¹ := rfl

@[simp]
/-
**EReal.inv_zero** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_zero : (0 : EReal)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
· 使用定理 `EReal.coe_zero`：coe_zero : ((0 : Real) : EReal) = 0
-/
lemma inv_zero : (0 : EReal)⁻¹ = 0 := by
  change (0 : ℝ)⁻¹ = (0 : EReal)
  rw [GroupWithZero.inv_zero, coe_zero]
/-
**EReal.** 是 Mathlib 中的一个实例，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DivInvOneMonoid EReal where
  inv_one := by nth_rw 1 [← coe_one, ← coe_inv 1, _root_.inv_one, coe_one]
/-
**EReal.inv_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_neg (a : EReal) : (-a)⁻¹ = -a⁻¹
参数：a : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.neg_bot`：neg_bot : -(⊥ : EReal) = ⊤
· 使用引理 `EReal.inv_top`：inv_top : (⊤ : EReal)⁻¹ = 0
· 使用引理 `EReal.inv_bot`：inv_bot : (⊥ : EReal)⁻¹ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_eq_coe_iff`：∀ {x y : ℝ}, ↑x = ↑y ↔ x = y
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `EReal.neg_top`：neg_top : -(⊤ : EReal) = ⊥
-/
lemma inv_neg (a : EReal) : (-a)⁻¹ = -a⁻¹ := by
  induction a
  · rw [neg_bot, inv_top, inv_bot, neg_zero]
  · rw [← coe_inv _, ← coe_neg _⁻¹, ← coe_neg _, ← coe_inv (-_)]
    exact EReal.coe_eq_coe_iff.2 _root_.inv_neg
  · rw [neg_top, inv_bot, inv_top, neg_zero]
/-
**EReal.inv_inv** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_inv {a : EReal} (h : a != ⊥) (h' : a != ⊤) : (a⁻¹)⁻¹ = a
参数：h : a != ⊥；h' : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_toReal`：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : 
(x.toReal : EReal) = x
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma inv_inv {a : EReal} (h : a ≠ ⊥) (h' : a ≠ ⊤) : (a⁻¹)⁻¹ = a := by
  rw [← coe_toReal h' h, ← coe_inv a.toReal, ← coe_inv a.toReal⁻¹, _root_.inv_inv a.toReal]
/-
**EReal.mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_inv (a b : EReal) : (a * b)⁻¹ = a⁻¹ * b⁻¹
参数：a b : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.induction₂_symm`：induction₂_symm {P : EReal -> EReal -> Prop} (sym
m : forall {x y}, P x y -> P y x) (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 
0 < x -> P …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `EReal.top_mul_of_pos`：top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_pos`：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
· 使用引理 `EReal.inv_top`：inv_top : (⊤ : EReal)⁻¹ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `EReal.inv_zero`：inv_zero : (0 : EReal)⁻¹ = 0
· 使用引理 `EReal.top_mul_of_neg`：top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥
· 使用定理 `EReal.coe_neg'`：∀ {x : ℝ}, ↑x < 0 ↔ x < 0
· 使用引理 `EReal.inv_bot`：inv_bot : (⊥ : EReal)⁻¹ = 0
· 使用定理 `EReal.mul_bot_of_pos`：∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_mul`：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EReal.mul_bot_of_neg`：∀ {x : EReal}, x < 0 → x * ⊥ = ⊤
-/
lemma mul_inv (a b : EReal) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction a, b using EReal.induction₂_symm with
  | top_top | top_zero | top_bot | zero_bot | bot_bot => simp
  | @symm a b h => rw [mul_comm b a, mul_comm b⁻¹ a⁻¹]; exact h
  | top_pos x x_pos => rw [top_mul_of_pos (EReal.coe_pos.2 x_pos), inv_top, zero_mul]
  | top_neg x x_neg => rw [top_mul_of_neg (EReal.coe_neg'.2 x_neg), inv_bot, inv_top, zero_mul]
  | pos_bot x x_pos => rw [mul_bot_of_pos (EReal.coe_pos.2 x_pos), inv_bot, mul_zero]
  | coe_coe x y => rw [← coe_mul, ← coe_inv, _root_.mul_inv, coe_mul, coe_inv, coe_inv]
  | neg_bot x x_neg => rw [mul_bot_of_neg (EReal.coe_neg'.2 x_neg), inv_top, inv_bot, mul_zero]

/-! #### Inversion and Absolute Value -/

/-
**EReal.sign_mul_inv_abs** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sign_mul_inv_abs (a : EReal) : (sign a) * (a.abs : EReal)⁻¹ = a⁻¹
参数：a : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `EReal.sign_coe`：sign_coe (x : Real) : sign (x : EReal) = sign x
· 使用定理 `SignType.coe_neg_one`：coe_neg_one : ↑(-1 : SignType) = (-1 : α)
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.inv_neg`：inv_neg (a : EReal) : (-a)⁻¹ = -a⁻¹
· 使用定理 `EReal.abs_def`：abs_def (x : Real) : (x : EReal).abs = ENNReal.ofReal |x|
· 使用定理 `EReal.coe_ennreal_ofReal`：coe_ennreal_ofReal {x : Real} : (ENNReal.ofRea
l x : EReal) = max x 0
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `EReal.abs_zero`：abs_zero : (0 : EReal).abs = 0
· 使用引理 `EReal.inv_zero`：inv_zero : (0 : EReal)⁻¹ = 0
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用定理 `SignType.coe_one`：coe_one : ↑(1 : SignType) = (1 : α)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a

--- 原说明 ---
#### Inversion and Absolute Value
-/
lemma sign_mul_inv_abs (a : EReal) : (sign a) * (a.abs : EReal)⁻¹ = a⁻¹ := by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, ← inv_neg, abs_def a,
        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul]
      simp only [abs_def a, coe_ennreal_ofReal, abs_nonneg, max_eq_left]
      congr
      exact abs_of_pos a_pos
/-
**EReal.sign_mul_inv_abs'** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：sign_mul_inv_abs' (a : EReal) : (sign a) * ((a.abs⁻¹ : Real>=0∞) : EReal) 
= a⁻¹
参数：a : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `EReal.sign_coe`：sign_coe (x : Real) : sign (x : EReal) = sign x
· 使用定理 `SignType.coe_neg_one`：coe_neg_one : ↑(-1 : SignType) = (-1 : α)
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `EReal.abs_def`：abs_def (x : Real) : (x : EReal).abs = ENNReal.ofReal |x|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_inv_of_pos`：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : E
NNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
· 使用定理 `abs_pos_of_neg`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrd
er α] [AddLeftMono α] {a : α}, a < 0 → 0 < |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `EReal.coe_ennreal_ofReal`：coe_ennreal_ofReal {x : Real} : (ENNReal.ofRea
l x : EReal) = max x 0
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
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
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `EReal.coe_neg`：∀ (x : ℝ), ↑(-x) = -↑x
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
（共 42 条，此处仅展示前 30 条）
-/
lemma sign_mul_inv_abs' (a : EReal) : (sign a) * ((a.abs⁻¹ : ℝ≥0∞) : EReal) = a⁻¹ := by
  induction a with
  | bot | top => simp
  | coe a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_neg a_neg), coe_ennreal_ofReal,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_pos a_pos), coe_ennreal_ofReal,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos

/-! #### Inversion and Positivity -/

/-
**EReal.bot_lt_inv** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：bot_lt_inv (x : EReal) : ⊥ < x⁻¹
参数：x : EReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.bot_lt_zero`：bot_lt_zero : (⊥ : EReal) < 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.inv_bot`：inv_bot : (⊥ : EReal)⁻¹ = 0
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用引理 `EReal.inv_top`：inv_top : (⊤ : EReal)⁻¹ = 0

--- 原说明 ---
#### Inversion and Positivity
-/
lemma bot_lt_inv (x : EReal) : ⊥ < x⁻¹ := by
  cases x with
  | bot => exact inv_bot ▸ bot_lt_zero
  | top => exact EReal.inv_top ▸ bot_lt_zero
  | coe x => exact (coe_inv x).symm ▸ bot_lt_coe (x⁻¹)
/-
**EReal.inv_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_lt_top (x : EReal) : x⁻¹ < ⊤
参数：x : EReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.zero_lt_top`：zero_lt_top : (0 : EReal) < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.inv_bot`：inv_bot : (⊥ : EReal)⁻¹ = 0
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用引理 `EReal.inv_top`：inv_top : (⊤ : EReal)⁻¹ = 0
-/
lemma inv_lt_top (x : EReal) : x⁻¹ < ⊤ := by
  cases x with
  | bot => exact inv_bot ▸ zero_lt_top
  | top => exact EReal.inv_top ▸ zero_lt_top
  | coe x => exact (coe_inv x).symm ▸ coe_lt_top (x⁻¹)
/-
**EReal.inv_nonneg_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_nonneg_of_nonneg {a : EReal} (h : 0 <= a) : 0 <= a⁻¹
参数：h : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `EReal.coe_nonneg`：∀ {x : ℝ}, 0 ≤ ↑x ↔ 0 ≤ x
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma inv_nonneg_of_nonneg {a : EReal} (h : 0 ≤ a) : 0 ≤ a⁻¹ := by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonneg, inv_nonneg]; exact EReal.coe_nonneg.1 h
/-
**EReal.inv_nonpos_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_nonpos_of_nonpos {a : EReal} (h : a <= 0) : a⁻¹ <= 0
参数：h : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `EReal.coe_nonpos`：∀ {x : ℝ}, ↑x ≤ 0 ↔ x ≤ 0
· 使用定理 `inv_nonpos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linear
Order G₀] {a : G₀} [PosMulMono G₀], a⁻¹ ≤ 0 ↔ a ≤ 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma inv_nonpos_of_nonpos {a : EReal} (h : a ≤ 0) : a⁻¹ ≤ 0 := by
  cases a with
  | bot | top => simp
  | coe a => rw [← coe_inv a, EReal.coe_nonpos, inv_nonpos]; exact EReal.coe_nonpos.1 h
/-
**EReal.inv_pos_of_pos_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_pos_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a != ⊤) : 0 < a⁻¹
参数：h : 0 < a；h' : a != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
lemma inv_pos_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : 0 < a⁻¹ := by
  lift a to ℝ using ⟨h', ne_bot_of_gt h⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_pos_of_pos h
/-
**EReal.inv_neg_of_neg_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_neg_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a != ⊥) : a⁻¹ < 0
参数：h : a < 0；h' : a != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linea
rOrder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma inv_neg_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : a⁻¹ < 0 := by
  lift a to ℝ using ⟨ne_top_of_lt h, h'⟩
  rw [← coe_inv a]; norm_cast at *; exact inv_lt_zero.2 h
/-
**EReal.inv_strictAntiOn** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：inv_strictAntiOn : StrictAntiOn (fun (x : EReal) => x⁻¹) (Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用引理 `EReal.inv_pos_of_pos_ne_top`：inv_pos_of_pos_ne_top {a : EReal} (h : 0 < 
a) (h' : a != ⊤) : 0 < a⁻¹
· 使用定理 `EReal.coe_ne_top`：coe_ne_top (x : Real) : (x : EReal) != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.inv_top`：inv_top : (⊤ : EReal)⁻¹ = 0
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.coe_inv`：coe_inv (x : Real) : (x⁻¹ : Real) = (x : EReal)⁻¹
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用定理 `inv_strictAntiOn`：inv_strictAntiOn : StrictAntiOn (fun x : α => x⁻¹) (Se
t.Ioi 0)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_pos`：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
-/
lemma inv_strictAntiOn : StrictAntiOn (fun (x : EReal) => x⁻¹) (Ioi 0) := by
  intro a a_0 b b_0 a_b
  push _ ∈ _ at *
  lift a to ℝ using ⟨ne_top_of_lt a_b, ne_bot_of_gt a_0⟩
  match b with
  | ⊤ => exact inv_top ▸ inv_pos_of_pos_ne_top a_0 (coe_ne_top a)
  | ⊥ => exact (not_lt_bot b_0).rec
  | (b : ℝ) =>
    rw [← coe_inv a, ← coe_inv b, EReal.coe_lt_coe_iff]
    exact _root_.inv_strictAntiOn (EReal.coe_pos.1 a_0) (EReal.coe_pos.1 b_0)
      (EReal.coe_lt_coe_iff.1 a_b)

/-! ### Division -/

/-
**EReal.div_eq_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ (a b : EReal), a / b = b⁻¹ * a
参数：a b : EReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x

--- 原说明 ---
### Division
-/
protected lemma div_eq_inv_mul (a b : EReal) : a / b = b⁻¹ * a := EReal.mul_comm a b⁻¹
/-
**EReal.coe_div** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：coe_div (a b : Real) : (a / b : Real) = (a : EReal) / (b : EReal)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_div (a b : ℝ) : (a / b : ℝ) = (a : EReal) / (b : EReal) := rfl
/-
**EReal.natCast_div_le** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：natCast_div_le (m n : Nat) : (m / n : Nat) <= (m : EReal) / (n : EReal)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用引理 `EReal.coe_div`：coe_div (a b : Real) : (a / b : Real) = (a : EReal) / (b 
: EReal)
· 使用定理 `EReal.coe_le_coe_iff`：∀ {x y : ℝ}, ↑x ≤ ↑y ↔ x ≤ y
· 使用定理 `Nat.cast_div_le`：cast_div_le {m n : Nat} : ((m / n : Nat) : α) <= m / n
-/
theorem natCast_div_le (m n : ℕ) :
    (m / n : ℕ) ≤ (m : EReal) / (n : EReal) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_div,
    EReal.coe_le_coe_iff]
  exact Nat.cast_div_le

@[simp]
/-
**EReal.div_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_bot {a : EReal} : a / ⊥ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `EReal.inv_bot`：inv_bot : (⊥ : EReal)⁻¹ = 0
-/
lemma div_bot {a : EReal} : a / ⊥ = 0 := inv_bot ▸ mul_zero a

@[simp]
/-
**EReal.div_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_top {a : EReal} : a / ⊤ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `EReal.inv_top`：inv_top : (⊤ : EReal)⁻¹ = 0
-/
lemma div_top {a : EReal} : a / ⊤ = 0 := inv_top ▸ mul_zero a

@[simp]
/-
**EReal.div_zero** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_zero {a : EReal} : a / 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.inv_zero`：inv_zero : (0 : EReal)⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma div_zero {a : EReal} : a / 0 = 0 := by
  change a * 0⁻¹ = 0
  rw [inv_zero, mul_zero a]

@[simp]
/-
**EReal.zero_div** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：zero_div {a : EReal} : 0 / a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma zero_div {a : EReal} : 0 / a = 0 := zero_mul a⁻¹
/-
**EReal.top_div_of_pos_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a != ⊤) : ⊤ / a = ⊤
参数：h : 0 < a；h' : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.top_mul_of_pos`：top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤
· 使用引理 `EReal.inv_pos_of_pos_ne_top`：inv_pos_of_pos_ne_top {a : EReal} (h : 0 < 
a) (h' : a != ⊤) : 0 < a⁻¹
-/
lemma top_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊤ / a = ⊤ :=
  top_mul_of_pos (inv_pos_of_pos_ne_top h h')
/-
**EReal.top_div_of_neg_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：top_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a != ⊥) : ⊤ / a = ⊥
参数：h : a < 0；h' : a != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.top_mul_of_neg`：top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥
· 使用引理 `EReal.inv_neg_of_neg_ne_bot`：inv_neg_of_neg_ne_bot {a : EReal} (h : a < 
0) (h' : a != ⊥) : a⁻¹ < 0
-/
lemma top_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊤ / a = ⊥ :=
  top_mul_of_neg (inv_neg_of_neg_ne_bot h h')
/-
**EReal.bot_div_of_pos_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：bot_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a != ⊤) : ⊥ / a = ⊥
参数：h : 0 < a；h' : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.bot_mul_of_pos`：bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥
· 使用引理 `EReal.inv_pos_of_pos_ne_top`：inv_pos_of_pos_ne_top {a : EReal} (h : 0 < 
a) (h' : a != ⊤) : 0 < a⁻¹
-/
lemma bot_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊥ / a = ⊥ :=
  bot_mul_of_pos (inv_pos_of_pos_ne_top h h')
/-
**EReal.bot_div_of_neg_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：bot_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a != ⊥) : ⊥ / a = ⊤
参数：h : a < 0；h' : a != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.bot_mul_of_neg`：bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤
· 使用引理 `EReal.inv_neg_of_neg_ne_bot`：inv_neg_of_neg_ne_bot {a : EReal} (h : a < 
0) (h' : a != ⊥) : a⁻¹ < 0
-/
lemma bot_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊥ / a = ⊤ :=
  bot_mul_of_neg (inv_neg_of_neg_ne_bot h h')

/-! #### Division and Multiplication -/

/-
**EReal.div_self** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_self {a : EReal} (h₁ : a != ⊥) (h₂ : a != ⊤) (h₃ : a != 0) : a / a = 1
参数：h₁ : a != ⊥；h₂ : a != ⊤；h₃ : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_toReal`：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : 
(x.toReal : EReal) = x
· 使用引理 `EReal.coe_div`：coe_div (a b : Real) : (a / b : Real) = (a : EReal) / (b 
: EReal)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.coe_ne_zero`：coe_ne_zero {x : Real} : (x : EReal) != 0 ↔ x != 0
· 使用定理 `EReal.coe_one`：coe_one : ((1 : Real) : EReal) = 1

--- 原说明 ---
#### Division and Multiplication
-/
lemma div_self {a : EReal} (h₁ : a ≠ ⊥) (h₂ : a ≠ ⊤) (h₃ : a ≠ 0) : a / a = 1 := by
  rw [← coe_toReal h₂ h₁] at h₃ ⊢
  rw [← coe_div, _root_.div_self (coe_ne_zero.1 h₃), coe_one]
/-
**EReal.mul_div** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
参数：a b c : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma mul_div (a b c : EReal) : a * (b / c) = (a * b) / c := by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]
/-
**EReal.mul_div_right** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_div_right (a b c : EReal) : a / b * c = a * c / b
参数：a b c : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
-/
lemma mul_div_right (a b c : EReal) : a / b * c = a * c / b := by
  rw [mul_comm, EReal.mul_div, mul_comm]
/-
**EReal.mul_div_left_comm** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_div_left_comm (a b c : EReal) : a * (b / c) = b * (a / c)
参数：a b c : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mul_div_left_comm (a b c : EReal) : a * (b / c) = b * (a / c) := by
  rw [mul_div a b c, mul_comm a b, ← mul_div b a c]
/-
**EReal.div_div** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_div (a b c : EReal) : a / b / c = a / (b * c)
参数：a b c : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `EReal.mul_inv`：mul_inv (a b : EReal) : (a * b)⁻¹ = a⁻¹ * b⁻¹
-/
lemma div_div (a b c : EReal) : a / b / c = a / (b * c) := by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  rw [mul_assoc a b⁻¹, mul_inv]
/-
**EReal.div_mul_div_comm** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_mul_div_comm (a b c d : EReal) : a / b * (c / d) = a * c / (b * d)
参数：a b c d : EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `EReal.div_div`：div_div (a b c : EReal) : a / b / c = a / (b * c)
· 使用引理 `EReal.mul_div_left_comm`：mul_div_left_comm (a b c : EReal) : a * (b / c)
 = b * (a / c)
-/
lemma div_mul_div_comm (a b c d : EReal) : a / b * (c / d) = a * c / (b * d) := by
  rw [← mul_div a, mul_comm b d, ← div_div c, ← mul_div_left_comm (c / d), mul_comm (a / b)]

variable {a b c : EReal}
/-
**EReal.div_mul_cancel** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_mul_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0) : a / b * b = a
参数：h₁ : b != ⊥；h₂ : b != ⊤；h₃ : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_left_comm`：mul_div_left_comm (a b c : EReal) : a * (b / c)
 = b * (a / c)
· 使用引理 `EReal.div_self`：div_self {a : EReal} (h₁ : a != ⊥) (h₂ : a != ⊤) (h₃ : a
 != 0) : a / a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma div_mul_cancel (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : a / b * b = a := by
  rw [mul_comm (a / b) b, ← mul_div_left_comm a b b, div_self h₁ h₂ h₃, mul_one]
/-
**EReal.mul_div_cancel** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b != 0) : b * (a / b) = a
参数：h₁ : b != ⊥；h₂ : b != ⊤；h₃ : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `EReal.div_mul_cancel`：div_mul_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : a / b * b = a
-/
lemma mul_div_cancel (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel h₁ h₂ h₃]
/-
**EReal.mul_div_mul_cancel** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_div_mul_cancel (h₁ : c != ⊥) (h₂ : c != ⊤) (h₃ : c != 0) : a * c / (b 
* c) = a / b
参数：h₁ : c != ⊥；h₂ : c != ⊤；h₃ : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_right`：mul_div_right (a b c : EReal) : a / b * c = a * c /
 b
· 使用引理 `EReal.div_div`：div_div (a b c : EReal) : a / b / c = a / (b * c)
· 使用引理 `EReal.div_mul_cancel`：div_mul_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : a / b * b = a
-/
lemma mul_div_mul_cancel (h₁ : c ≠ ⊥) (h₂ : c ≠ ⊤) (h₃ : c ≠ 0) : a * c / (b * c) = a / b := by
  rw [← mul_div_right a (b * c) c, ← div_div a b c, div_mul_cancel h₁ h₂ h₃]
/-
**EReal.div_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_eq_iff (hbot : b != ⊥) (htop : b != ⊤) (hzero : b != 0) : c / b = a ↔ 
c = a * b
参数：hbot : b != ⊥；htop : b != ⊤；hzero : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_cancel`：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : b * (a / b) = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
-/
lemma div_eq_iff (hbot : b ≠ ⊥) (htop : b ≠ ⊤) (hzero : b ≠ 0) : c / b = a ↔ c = a * b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← @mul_div_cancel c b hbot htop hzero, h, mul_comm a b]
  · rw [h, mul_comm a b, ← mul_div b a b, @mul_div_cancel a b hbot htop hzero]

/-! #### Division and Order -/

/-
**EReal.monotone_div_right_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：monotone_div_right_of_nonneg (h : 0 <= b) : Monotone fun a => a / b
参数：h : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `EReal.instMulPosMono`：MulPosMono EReal
· 使用引理 `EReal.inv_nonneg_of_nonneg`：inv_nonneg_of_nonneg {a : EReal} (h : 0 <= a
) : 0 <= a⁻¹

--- 原说明 ---
#### Division and Order
-/
lemma monotone_div_right_of_nonneg (h : 0 ≤ b) : Monotone fun a ↦ a / b :=
  fun _ _ h' ↦ mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg h)

@[gcongr]
/-
**EReal.div_le_div_right_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_le_div_right_of_nonneg (h : 0 <= c) (h' : a <= b) : a / c <= b / c
参数：h : 0 <= c；h' : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
-/
lemma div_le_div_right_of_nonneg (h : 0 ≤ c) (h' : a ≤ b) : a / c ≤ b / c :=
  monotone_div_right_of_nonneg h h'
/-
**EReal.strictMono_div_right_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：strictMono_div_right_of_pos (h : 0 < b) (h' : b != ⊤) : StrictMono fun a =
> a / b
参数：h : 0 < b；h' : b != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `EReal.div_le_div_right_of_nonneg`：div_le_div_right_of_nonneg (h : 0 <= c
) (h' : a <= b) : a / c <= b / c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_cancel`：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : b * (a / b) = a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma strictMono_div_right_of_pos (h : 0 < b) (h' : b ≠ ⊤) : StrictMono fun a ↦ a / b := by
  intro a a' a_lt_a'
  apply lt_of_le_of_ne <| div_le_div_right_of_nonneg (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b (ne_bot_of_gt h) h' h.ne', hyp,
    @EReal.mul_div_cancel a' b (ne_bot_of_gt h) h' h.ne']

@[gcongr]
/-
**EReal.div_lt_div_right_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_lt_div_right_of_pos (h₁ : 0 < c) (h₂ : c != ⊤) (h₃ : a < b) : a / c < 
b / c
参数：h₁ : 0 < c；h₂ : c != ⊤；h₃ : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.strictMono_div_right_of_pos`：strictMono_div_right_of_pos (h : 0 < 
b) (h' : b != ⊤) : StrictMono fun a => a / b
-/
lemma div_lt_div_right_of_pos (h₁ : 0 < c) (h₂ : c ≠ ⊤) (h₃ : a < b) : a / c < b / c :=
  strictMono_div_right_of_pos h₁ h₂ h₃
/-
**EReal.antitone_div_right_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：antitone_div_right_of_nonpos (h : b <= 0) : Antitone fun a => a / b
参数：h : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `EReal.neg_le_neg_iff`：∀ {a b : EReal}, -a ≤ -b ↔ b ≤ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `EReal.inv_neg`：inv_neg (a : EReal) : (-a)⁻¹ = -a⁻¹
· 使用定理 `EReal.le_neg_of_le_neg`：∀ {a b : EReal}, a ≤ -b → b ≤ -a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `EReal.div_le_div_right_of_nonneg`：div_le_div_right_of_nonneg (h : 0 <= c
) (h' : a <= b) : a / c <= b / c
-/
lemma antitone_div_right_of_nonpos (h : b ≤ 0) : Antitone fun a ↦ a / b := by
  intro a a' h'
  change a' * b⁻¹ ≤ a * b⁻¹
  rw [← neg_neg (a * b⁻¹), ← neg_neg (a' * b⁻¹), neg_le_neg_iff, mul_comm a b⁻¹, mul_comm a' b⁻¹,
    ← neg_mul b⁻¹ a, ← neg_mul b⁻¹ a', mul_comm (-b⁻¹) a, mul_comm (-b⁻¹) a', ← inv_neg b]
  have : 0 ≤ -b := by apply EReal.le_neg_of_le_neg; simp [h]
  exact div_le_div_right_of_nonneg this h'
/-
**EReal.div_le_div_right_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_le_div_right_of_nonpos (h : c <= 0) (h' : a <= b) : b / c <= a / c
参数：h : c <= 0；h' : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.antitone_div_right_of_nonpos`：antitone_div_right_of_nonpos (h : b 
<= 0) : Antitone fun a => a / b
-/
lemma div_le_div_right_of_nonpos (h : c ≤ 0) (h' : a ≤ b) : b / c ≤ a / c :=
  antitone_div_right_of_nonpos h h'
/-
**EReal.strictAnti_div_right_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：strictAnti_div_right_of_neg (h : b < 0) (h' : b != ⊥) : StrictAnti fun a =
> a / b
参数：h : b < 0；h' : b != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `EReal.div_le_div_right_of_nonpos`：div_le_div_right_of_nonpos (h : c <= 0
) (h' : a <= b) : b / c <= a / c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_cancel`：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : b * (a / b) = a
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
-/
lemma strictAnti_div_right_of_neg (h : b < 0) (h' : b ≠ ⊥) : StrictAnti fun a ↦ a / b := by
  intro a a' a_lt_a'
  simp only
  apply lt_of_le_of_ne <| div_le_div_right_of_nonpos (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b h' (ne_top_of_lt h) (ne_of_lt h), ← hyp,
    @EReal.mul_div_cancel a' b h' (ne_top_of_lt h) (ne_of_lt h)]
/-
**EReal.div_lt_div_right_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_lt_div_right_of_neg (h₁ : c < 0) (h₂ : c != ⊥) (h₃ : a < b) : b / c < 
a / c
参数：h₁ : c < 0；h₂ : c != ⊥；h₃ : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.strictAnti_div_right_of_neg`：strictAnti_div_right_of_neg (h : b < 
0) (h' : b != ⊥) : StrictAnti fun a => a / b
-/
lemma div_lt_div_right_of_neg (h₁ : c < 0) (h₂ : c ≠ ⊥) (h₃ : a < b) : b / c < a / c :=
  strictAnti_div_right_of_neg h₁ h₂ h₃
/-
**EReal.le_div_iff_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_div_iff_mul_le (h : b > 0) (h' : b != ⊤) : a <= c / b ↔ a * b <= c
参数：h : b > 0；h' : b != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_cancel`：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : b * (a / b) = a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `EReal.strictMono_div_right_of_pos`：strictMono_div_right_of_pos (h : 0 < 
b) (h' : b != ⊤) : StrictMono fun a => a / b
-/
lemma le_div_iff_mul_le (h : b > 0) (h' : b ≠ ⊤) : a ≤ c / b ↔ a * b ≤ c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b a b, mul_comm a b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')
/-
**EReal.div_le_iff_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_le_iff_le_mul (h : 0 < b) (h' : b != ⊤) : a / b <= c ↔ a <= b * c
参数：h : 0 < b；h' : b != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_cancel`：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : b * (a / b) = a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `EReal.strictMono_div_right_of_pos`：strictMono_div_right_of_pos (h : 0 < 
b) (h' : b != ⊤) : StrictMono fun a => a / b
-/
lemma div_le_iff_le_mul (h : 0 < b) (h' : b ≠ ⊤) : a / b ≤ c ↔ a ≤ b * c := by
  nth_rw 1 [← @mul_div_cancel c b (ne_bot_of_gt h) h' h.ne']
  rw [mul_div b c b, mul_comm b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')
/-
**EReal.lt_div_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：lt_div_iff (h : 0 < b) (h' : b != ⊤) : a < c / b ↔ a * b < c
参数：h : 0 < b；h' : b != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_cancel`：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : b * (a / b) = a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `EReal.strictMono_div_right_of_pos`：strictMono_div_right_of_pos (h : 0 < 
b) (h' : b != ⊤) : StrictMono fun a => a / b
-/
lemma lt_div_iff (h : 0 < b) (h' : b ≠ ⊤) : a < c / b ↔ a * b < c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div b a b, mul_comm a b]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt
/-
**EReal.div_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_lt_iff (h : 0 < c) (h' : c != ⊤) : b / c < a ↔ b < a * c
参数：h : 0 < c；h' : c != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.mul_div_cancel`：mul_div_cancel (h₁ : b != ⊥) (h₂ : b != ⊤) (h₃ : b
 != 0) : b * (a / b) = a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `EReal.mul_div`：mul_div (a b c : EReal) : a * (b / c) = (a * b) / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `EReal.strictMono_div_right_of_pos`：strictMono_div_right_of_pos (h : 0 < 
b) (h' : b != ⊤) : StrictMono fun a => a / b
-/
lemma div_lt_iff (h : 0 < c) (h' : c ≠ ⊤) : b / c < a ↔ b < a * c := by
  nth_rw 1 [← @mul_div_cancel a c (ne_bot_of_gt h) h' h.ne']
  rw [EReal.mul_div c a c, mul_comm a c]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt
/-
**EReal.div_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_nonneg (h : 0 <= a) (h' : 0 <= b) : 0 <= a / b
参数：h : 0 <= a；h' : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用引理 `EReal.inv_nonneg_of_nonneg`：inv_nonneg_of_nonneg {a : EReal} (h : 0 <= a
) : 0 <= a⁻¹
-/
lemma div_nonneg (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg h (inv_nonneg_of_nonneg h')
/-
**EReal.div_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_pos (ha : 0 < a) (hb : 0 < b) (hb' : b != ⊤) : 0 < a / b
参数：ha : 0 < a；hb : 0 < b；hb' : b != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.mul_pos`：∀ {a b : EReal}, 0 < a → 0 < b → 0 < a * b
· 使用引理 `EReal.inv_pos_of_pos_ne_top`：inv_pos_of_pos_ne_top {a : EReal} (h : 0 < 
a) (h' : a != ⊤) : 0 < a⁻¹
-/
lemma div_pos (ha : 0 < a) (hb : 0 < b) (hb' : b ≠ ⊤) : 0 < a / b :=
  EReal.mul_pos ha (inv_pos_of_pos_ne_top hb hb')
/-
**EReal.div_nonpos_of_nonpos_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_nonpos_of_nonpos_of_nonneg (h : a <= 0) (h' : 0 <= b) : a / b <= 0
参数：h : a <= 0；h' : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `EReal.instMulPosMono`：MulPosMono EReal
· 使用引理 `EReal.inv_nonneg_of_nonneg`：inv_nonneg_of_nonneg {a : EReal} (h : 0 <= a
) : 0 <= a⁻¹
-/
lemma div_nonpos_of_nonpos_of_nonneg (h : a ≤ 0) (h' : 0 ≤ b) : a / b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg h')
/-
**EReal.div_nonpos_of_nonneg_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_nonpos_of_nonneg_of_nonpos (h : 0 <= a) (h' : b <= 0) : a / b <= 0
参数：h : 0 <= a；h' : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonpos_of_nonneg_of_nonpos`：mul_nonpos_of_nonneg_of_nonpos [PosMulMo
no α] (ha : 0 <= a) (hb : b <= 0) : a * b <= 0
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用引理 `EReal.inv_nonpos_of_nonpos`：inv_nonpos_of_nonpos {a : EReal} (h : a <= 0
) : a⁻¹ <= 0
-/
lemma div_nonpos_of_nonneg_of_nonpos (h : 0 ≤ a) (h' : b ≤ 0) : a / b ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos h')
/-
**EReal.div_nonneg_of_nonpos_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_nonneg_of_nonpos_of_nonpos (h : a <= 0) (h' : b <= 0) : 0 <= a / b
参数：h : a <= 0；h' : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.zero_div`：zero_div {a : EReal} : 0 / a = 0
· 使用引理 `EReal.div_le_div_right_of_nonpos`：div_le_div_right_of_nonpos (h : c <= 0
) (h' : a <= b) : b / c <= a / c
-/
lemma div_nonneg_of_nonpos_of_nonpos (h : a ≤ 0) (h' : b ≤ 0) : 0 ≤ a / b :=
  le_of_eq_of_le zero_div.symm (div_le_div_right_of_nonpos h' h)
/-
**EReal.exists_lt_mul_left_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_mul_left_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ a' ∈ Ioo 0 a, c < a' * b := by
  rcases eq_or_ne b ⊤ with rfl | b_top
  · rcases eq_or_lt_of_le ha with rfl | ha
    · rw [zero_mul] at h
      exact (not_le_of_gt h hc).rec
    · obtain ⟨a', a0', aa'⟩ := exists_between ha
      use a', mem_Ioo.2 ⟨a0', aa'⟩
      rw [mul_top_of_pos ha] at h
      rwa [mul_top_of_pos a0']
  · have b0 : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
    obtain ⟨a', ha', aa'⟩ := exists_between ((div_lt_iff b0 b_top).2 h)
    exact ⟨a', ⟨(div_nonneg hc b0.le).trans_lt ha', aa'⟩, (div_lt_iff b0 b_top).1 ha'⟩
/-
**EReal.exists_lt_mul_right_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_lt_mul_right_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ b' ∈ Ioo 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h
/-
**EReal.exists_mul_left_lt** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_mul_left_lt (h₁ : a ≠ 0 ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ 0 < b) (hc : a * b < c) :
    ∃ a' ∈ Ioo a ⊤, a' * b < c := by
  rcases eq_top_or_lt_top a with rfl | a_top
  · rw [ne_self_iff_false, false_or] at h₂; rw [top_mul_of_pos h₂] at hc; exact (not_top_lt hc).rec
  rcases le_or_gt b 0 with b0 | b0
  · obtain ⟨a', aa', a_top'⟩ := exists_between a_top
    exact ⟨a', mem_Ioo.2 ⟨aa', a_top'⟩, lt_of_le_of_lt (mul_le_mul_of_nonpos_right aa'.le b0) hc⟩
  rcases eq_top_or_lt_top b with rfl | b_top
  · rcases lt_trichotomy a 0 with a0 | rfl | a0
    · obtain ⟨a', aa', a0'⟩ := exists_between a0
      rw [mul_top_of_neg a0] at hc
      refine ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt a0'⟩, mul_top_of_neg a0' ▸ hc⟩
    · rw [ne_self_iff_false, ne_self_iff_false, false_or] at h₁; exact h₁.rec
    · rw [mul_top_of_pos a0] at hc; exact (not_top_lt hc).rec
  · obtain ⟨a', aa', hc'⟩ := exists_between ((lt_div_iff b0 b_top.ne).2 hc)
    exact ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt hc'⟩, (lt_div_iff b0 b_top.ne).1 hc'⟩
/-
**EReal.exists_mul_right_lt** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_mul_right_lt (h₁ : 0 < a ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ 0) (hc : a * b < c) :
    ∃ b' ∈ Ioo b ⊤, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢
  exact exists_mul_left_lt h₂.symm h₁.symm hc
/-
**EReal.le_mul_of_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_mul_of_forall_lt (h₁ : 0 < a ∨ b != ⊤) (h₂ : a != ⊤ ∨ 0 < b) (h : foral
l a' > a, forall b' > b, c <= a' * b') : c <= a * b
参数：h₁ : 0 < a ∨ b != ⊤；h₂ : a != ⊤ ∨ 0 < b；h : forall a' > a, forall b' > b, c <
= a' * b'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_left_lt`：∀ {a b c : E
Real}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ 0 < b → a * b < c → ∃ a' ∈ Set.Ioo a ⊤, a' * b < 
c
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_right_lt`：∀ {a b c : 
EReal}, 0 < a ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → a * b < c → ∃ b' ∈ Set.Ioo b ⊤, a * b' <
 c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma le_mul_of_forall_lt (h₁ : 0 < a ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ 0 < b)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', aa', hd⟩ := exists_mul_left_lt (h₁.imp_left ne_of_gt) h₂ hd
  replace h₁ : 0 < a' ∨ b ≠ ⊤ := h₁.imp_left fun a0 ↦ a0.trans (mem_Ioo.1 aa').1
  replace h₂ : a' ≠ ⊤ ∨ b ≠ 0 := Or.inl (mem_Ioo.1 aa').2.ne
  obtain ⟨b', bb', hd⟩ := exists_mul_right_lt h₁ h₂ hd
  exact (h a' (mem_Ioo.1 aa').1 b' (mem_Ioo.1 bb').1).trans hd.le
/-
**EReal.mul_le_of_forall_lt_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：mul_le_of_forall_lt_of_nonneg (ha : 0 <= a) (hc : 0 <= c) (h : forall a' i
n Ioo 0 a, forall b' in Ioo 0 b, a' * b' <= c) : a * b <= c
参数：ha : 0 <= a；hc : 0 <= c；h : forall a' in Ioo 0 a, forall b' in Ioo 0 b, a' * 
b' <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_left_of_nonneg`：∀ 
{a b c : EReal}, 0 ≤ a → 0 ≤ c → c < a * b → ∃ a' ∈ Set.Ioo 0 a, c < a' * b
· 使用定理 `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_right_of_nonneg`：∀
 {a b c : EReal}, 0 ≤ a → 0 ≤ c → c < a * b → ∃ b' ∈ Set.Ioo 0 b, c < a * b'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma mul_le_of_forall_lt_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ a' ∈ Ioo 0 a, ∀ b' ∈ Ioo 0 b, a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d dab ↦ ?_
  rcases lt_or_ge d 0 with d0 | d0
  · exact d0.le.trans hc
  obtain ⟨a', aa', dab⟩ := exists_lt_mul_left_of_nonneg ha d0 dab
  obtain ⟨b', bb', dab⟩ := exists_lt_mul_right_of_nonneg aa'.1.le d0 dab
  exact dab.le.trans (h a' aa' b' bb')

/-! #### Division Distributivity -/

/-
**EReal.div_right_distrib_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：div_right_distrib_of_nonneg (h : 0 <= a) (h' : 0 <= b) : (a + b) / c = a /
 c + b / c
参数：h : 0 <= a；h' : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.right_distrib_of_nonneg`：right_distrib_of_nonneg {a b c : EReal} (
ha : 0 <= a) (hb : 0 <= b) : (a + b) * c = a * c + b * c

--- 原说明 ---
#### Division Distributivity
-/
lemma div_right_distrib_of_nonneg (h : 0 ≤ a) (h' : 0 ≤ b) :
    (a + b) / c = a / c + b / c :=
  EReal.right_distrib_of_nonneg h h'
/-
**EReal.add_div_of_nonneg_right** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_div_of_nonneg_right (h : 0 <= c) : (a + b) / c = a / c + b / c
参数：h : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.right_distrib_of_nonneg_of_ne_top`：right_distrib_of_nonneg_of_ne_t
op {x : EReal} (hx_nonneg : 0 <= x) (hx_ne_top : x != ⊤) (y z : EReal) : (y + z)
 * x = y * x + z * x
· 使用引理 `EReal.inv_nonneg_of_nonneg`：inv_nonneg_of_nonneg {a : EReal} (h : 0 <= a
) : 0 <= a⁻¹
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `EReal.inv_lt_top`：inv_lt_top (x : EReal) : x⁻¹ < ⊤
-/
lemma add_div_of_nonneg_right (h : 0 ≤ c) :
    (a + b) / c = a / c + b / c := by
  apply right_distrib_of_nonneg_of_ne_top (inv_nonneg_of_nonneg h) (inv_lt_top c).ne

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: inverse of an `EReal`. -/
@[positivity (_⁻¹ : EReal)]
meta def evalERealInv : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a⁻¹) =>
    assertInstancesCommute
    match (← core zα pα a).toNonneg with
    | some pa => pure (.nonnegative q(EReal.inv_nonneg_of_nonneg <| $pa))
    | none => pure .none
  | _, _, _ => throwError "not an inverse of an `EReal`"

/-- Extension for the `positivity` tactic: ratio of two `EReal`s. -/
@[positivity (_ / _ : EReal)]
meta def evalERealDiv : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a / $b) =>
    assertInstancesCommute
    match (← core zα pα a).toNonneg with
    | some pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.nonnegative q(EReal.div_nonneg $pa $pb))
      | none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a ratio of 2 `EReal`s"

end Mathlib.Meta.Positivity

