/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Square root of a real number

In this file we define

* `NNReal.sqrt` to be the square root of a nonnegative real number.
* `Real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `NNReal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `NNReal.sqrt x` exists. As a side
effect, `NNReal.sqrt` is a bundled `OrderIso`, so for `NNReal` numbers we get continuity as well as
theorems like `NNReal.sqrt x ≤ y ↔ x ≤ y * y` for free.

Then we define `Real.sqrt x` to be `NNReal.sqrt (Real.toNNReal x)`.

## Tags

square root
-/

@[expose] public section

open Set Filter
open scoped Filter NNReal Topology

namespace NNReal

variable {x y : ℝ≥0}

/-- Square root of a nonnegative real number. -/
@[pp_nodot]
/-
**NNReal.sqrt** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：sqrt : Real>=0 ≃o Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Square root of a nonnegative real number.
-/
noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
  OrderIso.symm <| powOrderIso 2 two_ne_zero
/-
**NNReal.sq_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
参数：x : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _
/-
**NNReal.sqrt_sq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), NNReal.sqrt (x ^ 2) = x
参数：x : NNReal；x ^ 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
@[simp] lemma sqrt_sq (x : ℝ≥0) : sqrt (x ^ 2) = x := sqrt.apply_symm_apply _
/-
**NNReal.mul_self_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), NNReal.sqrt x * NNReal.sqrt x = x
参数：x : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
-/
@[simp] lemma mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x := by rw [← sq, sq_sqrt]
/-
**NNReal.sqrt_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), NNReal.sqrt (x * x) = x
参数：x : NNReal；x * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `NNReal.sqrt_sq`：∀ (x : NNReal), NNReal.sqrt (x ^ 2) = x
-/
@[simp] lemma sqrt_mul_self (x : ℝ≥0) : sqrt (x * x) = x := by rw [← sq, sqrt_sq]
/-
**NNReal.sqrt_le_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sqrt_le_sqrt : sqrt x <= sqrt y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
lemma sqrt_le_sqrt : sqrt x ≤ sqrt y ↔ x ≤ y := sqrt.le_iff_le
/-
**NNReal.sqrt_lt_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sqrt_lt_sqrt : sqrt x < sqrt y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
-/
lemma sqrt_lt_sqrt : sqrt x < sqrt y ↔ x < y := sqrt.lt_iff_lt
/-
**NNReal.sqrt_eq_iff_eq_sq** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sqrt_eq_iff_eq_sq : sqrt x = y ↔ x = y ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
lemma sqrt_eq_iff_eq_sq : sqrt x = y ↔ x = y ^ 2 := sqrt.toEquiv.eq_symm_apply.symm
/-
**NNReal.sqrt_le_iff_le_sq** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sqrt_le_iff_le_sq : sqrt x <= y ↔ x <= y ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
lemma sqrt_le_iff_le_sq : sqrt x ≤ y ↔ x ≤ y ^ 2 := sqrt.to_galoisConnection _ _
/-
**NNReal.le_sqrt_iff_sq_le** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：le_sqrt_iff_sq_le : x <= sqrt y ↔ x ^ 2 <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
lemma le_sqrt_iff_sq_le : x ≤ sqrt y ↔ x ^ 2 ≤ y := (sqrt.symm.to_galoisConnection _ _).symm
/-
**NNReal.sqrt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x : NNReal}, NNReal.sqrt x = 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sqrt_eq_zero : sqrt x = 0 ↔ x = 0 := by simp [sqrt_eq_iff_eq_sq]
/-
**NNReal.sqrt_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x : NNReal}, NNReal.sqrt x = 1 ↔ x = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sqrt_eq_one : sqrt x = 1 ↔ x = 1 := by simp [sqrt_eq_iff_eq_sq]
/-
**NNReal.sqrt_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：NNReal.sqrt 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sqrt_zero : sqrt 0 = 0 := by simp
/-
**NNReal.sqrt_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：NNReal.sqrt 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sqrt_one : sqrt 1 = 1 := by simp
/-
**NNReal.sqrt_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x : NNReal}, NNReal.sqrt x ≤ 1 ↔ x ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.sqrt_one`：NNReal.sqrt 1 = 1
· 使用引理 `NNReal.sqrt_le_sqrt`：sqrt_le_sqrt : sqrt x <= sqrt y ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sqrt_le_one : sqrt x ≤ 1 ↔ x ≤ 1 := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
/-
**NNReal.one_le_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x : NNReal}, 1 ≤ NNReal.sqrt x ↔ 1 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.sqrt_one`：NNReal.sqrt 1 = 1
· 使用引理 `NNReal.sqrt_le_sqrt`：sqrt_le_sqrt : sqrt x <= sqrt y ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_le_sqrt : 1 ≤ sqrt x ↔ 1 ≤ x := by rw [← sqrt_one, sqrt_le_sqrt, sqrt_one]
/-
**NNReal.sqrt_mul_le_max** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sqrt_mul_le_max : sqrt (x * y) <= max x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.sqrt_le_iff_le_sq`：sqrt_le_iff_le_sq : sqrt x <= y ↔ x <= y ^ 2
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma sqrt_mul_le_max : sqrt (x * y) ≤ max x y := by
  rw [sqrt_le_iff_le_sq, sq]; gcongr <;> simp
/-
**NNReal.sqrt_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.sqrt_eq_iff_eq_sq`：sqrt_eq_iff_eq_sq : sqrt x = y ↔ x = y ^ 2
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
-/
theorem sqrt_mul (x y : ℝ≥0) : sqrt (x * y) = sqrt x * sqrt y := by
  rw [sqrt_eq_iff_eq_sq, mul_pow, sq_sqrt, sq_sqrt]

/-- `NNReal.sqrt` as a `MonoidWithZeroHom`. -/
/-
**NNReal.sqrtHom** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：sqrtHom : Real>=0 ->*₀ Real>=0
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `NNReal.sqrt_one`：NNReal.sqrt 1 = 1
· 使用定理 `NNReal.sqrt_mul`：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt
 y

--- 原说明 ---
`NNReal.sqrt` as a `MonoidWithZeroHom`.
-/
noncomputable def sqrtHom : ℝ≥0 →*₀ ℝ≥0 :=
  ⟨⟨sqrt, sqrt_zero⟩, sqrt_one, sqrt_mul⟩
/-
**NNReal.sqrt_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sqrt_inv (x : Real>=0) : sqrt x⁻¹ = (sqrt x)⁻¹
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
-/
theorem sqrt_inv (x : ℝ≥0) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
  map_inv₀ sqrtHom x
/-
**NNReal.sqrt_div** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sqrt_div (x y : Real>=0) : sqrt (x / y) = sqrt x / sqrt y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
-/
theorem sqrt_div (x y : ℝ≥0) : sqrt (x / y) = sqrt x / sqrt y :=
  map_div₀ sqrtHom x y

@[continuity, fun_prop]
/-
**NNReal.continuous_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：continuous_sqrt : Continuous sqrt
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpac
e β] [Ord…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
-/
theorem continuous_sqrt : Continuous sqrt := sqrt.continuous
/-
**NNReal.sqrt_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x : NNReal}, 0 < NNReal.sqrt x ↔ 0 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x := by simp [pos_iff_ne_zero]

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos

attribute [bound] sqrt_pos_of_pos
/-
**NNReal.isSquare** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (x : NNReal), IsSquare x
参数：x : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.mul_self_sqrt`：∀ (x : NNReal), NNReal.sqrt x * NNReal.sqrt x = x
-/
@[simp] theorem isSquare (x : ℝ≥0) : IsSquare x := ⟨_, mul_self_sqrt _ |>.symm⟩

end NNReal

namespace Real

/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
/-
**Real.sqrt** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：ℝ → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
-/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)

-- TODO: replace this with a typeclass
@[inherit_doc]
prefix:max "√" => Real.sqrt

variable {x y : ℝ}

@[simp, norm_cast]
/-
**Real.coe_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
theorem coe_sqrt {x : ℝ≥0} : (NNReal.sqrt x : ℝ) = √(x : ℝ) := by
  rw [Real.sqrt, Real.toNNReal_coe]

@[continuity, fun_prop]
/-
**Real.continuous_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_sqrt : Continuous (√· : Real -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `NNReal.continuous_sqrt`：continuous_sqrt : Continuous sqrt
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
-/
theorem continuous_sqrt : Continuous (√· : ℝ → ℝ) := by unfold sqrt; fun_prop

@[simp]
/-
**Real.map_sqrt_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：map_sqrt_atTop : map (√·) atTop = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.map_toNNReal_atTop`：Filter.map Real.toNNReal Filter.atTop = Filter.
atTop
· 使用定理 `OrderIso.map_atTop`：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = at
Top
· 使用定理 `NNReal.map_coe_atTop`：Filter.map NNReal.toReal Filter.atTop = Filter.atT
op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_sqrt_atTop : map (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← map_map]

@[simp]
/-
**Real.comap_sqrt_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：comap_sqrt_atTop : comap (√·) atTop = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.comap_coe_atTop`：comap_coe_atTop : comap toReal atTop = atTop
· 使用定理 `OrderIso.comap_atTop`：comap_atTop (e : α ≃o β) : comap e atTop = atTop
· 使用定理 `Real.comap_toNNReal_atTop`：Filter.comap Real.toNNReal Filter.atTop = Fil
ter.atTop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_sqrt_atTop : comap (√·) atTop = atTop := by
  unfold sqrt
  simp_rw [← Function.comp_def]
  simp [← comap_comap]
/-
**Real.tendsto_sqrt_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：tendsto_sqrt_atTop : Tendsto (√·) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Real.map_sqrt_atTop`：map_sqrt_atTop : map (√·) atTop = atTop
-/
lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := map_sqrt_atTop.le
/-
**Real.sqrt_eq_zero_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 0
参数：h : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.toNNReal_eq_zero`：toNNReal_eq_zero {r : Real} : Real.toNNReal r = 0
 ↔ r <= 0
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : √x = 0 := by simp [sqrt, Real.toNNReal_eq_zero.2 h]
/-
**Real.sqrt_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ (x : ℝ), 0 ≤ √x
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
@[simp] theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x := by
  unfold sqrt
  exact NNReal.coe_nonneg _

@[simp]
/-
**Real.mul_self_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mul_self_sqrt (h : 0 <= x) : √x * √x = x
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `NNReal.mul_self_sqrt`：∀ (x : NNReal), NNReal.sqrt x * NNReal.sqrt x = x
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
-/
theorem mul_self_sqrt (h : 0 ≤ x) : √x * √x = x := by
  rw [Real.sqrt, ← NNReal.coe_mul, NNReal.mul_self_sqrt, Real.coe_toNNReal _ h]

@[simp]
/-
**Real.sqrt_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_self_inj_of_nonneg`：mul_self_inj_of_nonneg {α : Type*} [CommRing α] 
[NoZeroDivisors α] [PartialOrder α] [IsStrictOrderedRing α] {a b : α} (a0 : 0 <=
 a) (b0 : 0 …
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem sqrt_mul_self (h : 0 ≤ x) : √(x * x) = x :=
  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))
/-
**Real.sqrt_eq_cases** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_cases : √x = y ↔ y * y = x ∧ 0 <= y ∨ x < 0 ∧ y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sqrt_eq_cases : √x = y ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 := by
  constructor
  · rintro rfl
    rcases le_or_gt 0 x with hle | hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts [sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]
/-
**Real.sqrt_eq_iff_mul_self_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_iff_mul_self_eq (hx : 0 <= x) (hy : 0 <= y) : √x = y ↔ x = y * y
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
-/
theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y * y :=
  ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [h, sqrt_mul_self hy]⟩
/-
**Real.sqrt_eq_iff_mul_self_eq_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : √x = y ↔ y * y = x
参数：h : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : √x = y ↔ y * y = x := by
  simp [sqrt_eq_cases, h.ne', h.le]

@[simp]
/-
**Real.sqrt_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_one : √x = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sqrt_eq_iff_mul_self_eq_of_pos`：sqrt_eq_iff_mul_self_eq_of_pos (h :
 0 < y) : √x = y ↔ y * y = x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_eq_one : √x = 1 ↔ x = 1 :=
  calc
    √x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]

@[simp]
/-
**Real.sq_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
-/
theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]

@[simp]
/-
**Real.sqrt_sq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
-/
theorem sqrt_sq (h : 0 ≤ x) : √(x ^ 2) = x := by rw [sq, sqrt_mul_self h]
/-
**Real.sqrt_eq_iff_eq_sq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_iff_eq_sq (hx : 0 <= x) (hy : 0 <= y) : √x = y ↔ x = y ^ 2
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.sqrt_eq_iff_mul_self_eq`：sqrt_eq_iff_mul_self_eq (hx : 0 <= x) (hy 
: 0 <= y) : √x = y ↔ x = y * y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_eq_iff_eq_sq (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = y ↔ x = y ^ 2 := by
  rw [sq, sqrt_eq_iff_mul_self_eq hx hy]
/-
**Real.sqrt_mul_self_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_mul_self_eq_abs (x : Real) : √(x * x) = |x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `Real.sqrt_mul_self`：sqrt_mul_self (h : 0 <= x) : √(x * x) = x
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem sqrt_mul_self_eq_abs (x : ℝ) : √(x * x) = |x| := by
  rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]
/-
**Real.sqrt_sq_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.sqrt_mul_self_eq_abs`：sqrt_mul_self_eq_abs (x : Real) : √(x * x) = 
|x|
-/
theorem sqrt_sq_eq_abs (x : ℝ) : √(x ^ 2) = |x| := by rw [sq, sqrt_mul_self_eq_abs]

@[simp, grind =]
/-
**Real.sqrt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_zero : √0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `Real.toNNReal_zero`：toNNReal_zero : Real.toNNReal 0 = 0
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sqrt_zero : √0 = 0 := by simp [Real.sqrt]

@[simp, grind =]
/-
**Real.sqrt_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_one : √1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `NNReal.sqrt_one`：NNReal.sqrt 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sqrt_one : √1 = 1 := by simp [Real.sqrt]

@[simp]
/-
**Real.sqrt_le_sqrt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= y
参数：hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用引理 `NNReal.sqrt_le_sqrt`：sqrt_le_sqrt : sqrt x <= sqrt y ↔ x <= y
· 使用定理 `Real.toNNReal_le_toNNReal_iff`：toNNReal_le_toNNReal_iff {r p : Real} (hp
 : 0 <= p) : toNNReal r <= toNNReal p ↔ r <= p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_le_sqrt_iff (hy : 0 ≤ y) : √x ≤ √y ↔ x ≤ y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt, toNNReal_le_toNNReal_iff hy]

@[simp]
/-
**Real.sqrt_lt_sqrt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_lt_sqrt_iff (hx : 0 <= x) : √x < √y ↔ x < y
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Real.sqrt_le_sqrt_iff`：sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= 
y
-/
theorem sqrt_lt_sqrt_iff (hx : 0 ≤ x) : √x < √y ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)
/-
**Real.sqrt_lt_sqrt_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x < √y ↔ x < y
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用引理 `NNReal.sqrt_lt_sqrt`：sqrt_lt_sqrt : sqrt x < sqrt y ↔ x < y
· 使用定理 `Real.toNNReal_lt_toNNReal_iff`：toNNReal_lt_toNNReal_iff {r p : Real} (h 
: 0 < p) : Real.toNNReal r < Real.toNNReal p ↔ r < p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x < √y ↔ x < y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_lt_coe, NNReal.sqrt_lt_sqrt, toNNReal_lt_toNNReal_iff hy]

@[bound]
/-
**Real.sqrt_le_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_le_sqrt (h : x <= y) : √x <= √y
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用引理 `NNReal.sqrt_le_sqrt`：sqrt_le_sqrt : sqrt x <= sqrt y ↔ x <= y
· 使用定理 `Real.toNNReal_le_toNNReal`：toNNReal_le_toNNReal {r p : Real} (h : r <= p
) : Real.toNNReal r <= Real.toNNReal p
-/
theorem sqrt_le_sqrt (h : x ≤ y) : √x ≤ √y := by
  rw [Real.sqrt, Real.sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt]
  exact toNNReal_le_toNNReal h

@[gcongr]
/-
**Real.sqrt_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_monotone : Monotone Real.sqrt
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sqrt_le_sqrt`：sqrt_le_sqrt (h : x <= y) : √x <= √y
-/
theorem sqrt_monotone : Monotone Real.sqrt :=
  fun _ _ ↦ sqrt_le_sqrt
/-
**Real.strictMonoOn_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_sqrt : StrictMonoOn sqrt (Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_lt_sqrt_iff`：sqrt_lt_sqrt_iff (hx : 0 <= x) : √x < √y ↔ x < y
-/
theorem strictMonoOn_sqrt : StrictMonoOn sqrt (Ici 0) :=
  fun _ ha _ _ h => (sqrt_lt_sqrt_iff ha).mpr h

@[gcongr, bound]
/-
**Real.sqrt_lt_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_lt_sqrt (hx : 0 <= x) (h : x < y) : √x < √y
参数：hx : 0 <= x；h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_lt_sqrt_iff`：sqrt_lt_sqrt_iff (hx : 0 <= x) : √x < √y ↔ x < y
-/
theorem sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y) : √x < √y :=
  (sqrt_lt_sqrt_iff hx).2 h
/-
**Real.sqrt_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_le_left (hy : 0 <= y) : √x <= y ↔ x <= y ^ 2
参数：hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.le_toNNReal_iff_coe_le`：le_toNNReal_iff_coe_le {r : Real>=0} {p : R
eal} (hp : 0 <= p) : r <= Real.toNNReal p ↔ ↑r <= p
· 使用引理 `NNReal.sqrt_le_iff_le_sq`：sqrt_le_iff_le_sq : sqrt x <= y ↔ x <= y ^ 2
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Real.toNNReal_mul`：toNNReal_mul {p q : Real} (hp : 0 <= p) : Real.toNNRe
al (p * q) = Real.toNNReal p * Real.toNNReal q
· 使用定理 `Real.toNNReal_le_toNNReal_iff`：toNNReal_le_toNNReal_iff {r p : Real} (hp
 : 0 <= p) : toNNReal r <= toNNReal p ↔ r <= p
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_le_left (hy : 0 ≤ y) : √x ≤ y ↔ x ≤ y ^ 2 := by
  rw [sqrt, ← Real.le_toNNReal_iff_coe_le hy, NNReal.sqrt_le_iff_le_sq, sq, ← Real.toNNReal_mul hy,
    Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y), sq]
/-
**Real.sqrt_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_le_iff : √x <= y ↔ 0 <= y ∧ x <= y ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Real.sqrt_le_left`：sqrt_le_left (hy : 0 <= y) : √x <= y ↔ x <= y ^ 2
-/
theorem sqrt_le_iff : √x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 := by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h, and_congr_right_iff]
  exact sqrt_le_left
/-
**Real.sqrt_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_lt (hx : 0 <= x) (hy : 0 <= y) : √x < y ↔ x < y ^ 2
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_lt_sqrt_iff`：sqrt_lt_sqrt_iff (hx : 0 <= x) : √x < √y ↔ x < y
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_lt (hx : 0 ≤ x) (hy : 0 ≤ y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff hx, sqrt_sq hy]
/-
**Real.sqrt_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y ^ 2
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_lt_sqrt_iff_of_pos`：sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x 
< √y ↔ x < y
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _), sqrt_sq hy.le]

/-- Note: if you want to conclude `x ≤ √y`, then use `Real.le_sqrt_of_sq_le`.
If you have `x > 0`, consider using `Real.le_sqrt'` -/
/-
**Real.le_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Real.sqrt_lt`：sqrt_lt (hx : 0 <= x) (hy : 0 <= y) : √x < y ↔ x < y ^ 2

--- 原说明 ---
Note: if you want to conclude `x ≤ √y`, then use `Real.le_sqrt_of_sq_le`.
If you have `x > 0`, consider using `Real.le_sqrt'`
-/
theorem le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt hy hx
/-
**Real.le_sqrt'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_sqrt' (hx : 0 < x) : x <= √y ↔ x ^ 2 <= y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Real.sqrt_lt'`：sqrt_lt' (hy : 0 < y) : √x < y ↔ x < y ^ 2
-/
theorem le_sqrt' (hx : 0 < x) : x ≤ √y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt' hx
/-
**Real.abs_le_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_le_sqrt (h : x ^ 2 <= y) : |x| <= √y
参数：h : x ^ 2 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_sq_eq_abs`：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
· 使用定理 `Real.sqrt_le_sqrt`：sqrt_le_sqrt (h : x <= y) : √x <= √y
-/
theorem abs_le_sqrt (h : x ^ 2 ≤ y) : |x| ≤ √y := by
  rw [← sqrt_sq_eq_abs]; exact sqrt_le_sqrt h
/-
**Real.sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sq_le (h : 0 <= y) : x ^ 2 <= y ↔ -√y <= x ∧ x <= √y
参数：h : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.abs_le_sqrt`：abs_le_sqrt (h : x ^ 2 <= y) : |x| <= √y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.le_sqrt`：le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem sq_le (h : 0 ≤ y) : x ^ 2 ≤ y ↔ -√y ≤ x ∧ x ≤ √y := by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp
/-
**Real.neg_sqrt_le_of_sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：neg_sqrt_le_of_sq_le (h : x ^ 2 <= y) : -√y <= x
参数：h : x ^ 2 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.sq_le`：sq_le (h : 0 <= y) : x ^ 2 <= y ↔ -√y <= x ∧ x <= √y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem neg_sqrt_le_of_sq_le (h : x ^ 2 ≤ y) : -√y ≤ x :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).1
/-
**Real.le_sqrt_of_sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：le_sqrt_of_sq_le (h : x ^ 2 <= y) : x <= √y
参数：h : x ^ 2 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.sq_le`：sq_le (h : 0 <= y) : x ^ 2 <= y ↔ -√y <= x ∧ x <= √y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ √y :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).2

@[simp]
/-
**Real.sqrt_inj** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_inj (hx : 0 <= x) (hy : 0 <= y) : √x = √y ↔ x = y
参数：hx : 0 <= x；hy : 0 <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : √x = √y ↔ x = y := by
  simp [le_antisymm_iff, hx, hy]

@[simp]
/-
**Real.sqrt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_zero (h : 0 <= x) : √x = 0 ↔ x = 0
参数：h : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `Real.sqrt_inj`：sqrt_inj (hx : 0 <= x) (hy : 0 <= y) : √x = √y ↔ x = y
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sqrt_eq_zero (h : 0 ≤ x) : √x = 0 ↔ x = 0 := by simpa using sqrt_inj h le_rfl
/-
**Real.sqrt_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_eq_zero' : √x = 0 ↔ x <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `NNReal.sqrt_eq_zero`：∀ {x : NNReal}, NNReal.sqrt x = 0 ↔ x = 0
· 使用定理 `Real.toNNReal_eq_zero`：toNNReal_eq_zero {r : Real} : Real.toNNReal r = 0
 ↔ r <= 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_eq_zero' : √x = 0 ↔ x ≤ 0 := by
  rw [sqrt, NNReal.coe_eq_zero, NNReal.sqrt_eq_zero, Real.toNNReal_eq_zero]
/-
**Real.sqrt_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_ne_zero (h : 0 <= x) : √x != 0 ↔ x != 0
参数：h : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Real.sqrt_eq_zero`：sqrt_eq_zero (h : 0 <= x) : √x = 0 ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_ne_zero (h : 0 ≤ x) : √x ≠ 0 ↔ x ≠ 0 := by rw [not_iff_not, sqrt_eq_zero h]
/-
**Real.sqrt_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_ne_zero' : √x != 0 ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Real.sqrt_eq_zero'`：sqrt_eq_zero' : √x = 0 ↔ x <= 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sqrt_ne_zero' : √x ≠ 0 ↔ 0 < x := by rw [← not_le, not_iff_not, sqrt_eq_zero']

/-- Variant of `sq_sqrt` without a non-negativity assumption on `x`. -/
/-
**Real.sq_sqrt'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sq_sqrt' : √x ^ 2 = max x 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a

--- 原说明 ---
Variant of `sq_sqrt` without a non-negativity assumption on `x`.
-/
theorem sq_sqrt' : √x ^ 2 = max x 0 := by
  rcases lt_trichotomy x 0 with _ | _ | _ <;> grind [sqrt_eq_zero', sq_sqrt]

-- Add the rule for `√x ^ 2` to the grind whiteboard whenever we see a real square root.
grind_pattern sq_sqrt' => √x

-- Check that `grind` can discharge non-zero goals for square roots of positive numerals.
/-
**Real.** 是 Mathlib 中的一个示例，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : √7 ≠ 0 := by grind

@[simp]
/-
**Real.sqrt_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_pos : 0 < √x ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Real.sqrt_eq_zero'`：sqrt_eq_zero' : √x = 0 ↔ x <= 0
-/
theorem sqrt_pos : 0 < √x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')

alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos
/-
**Real.sqrt_le_sqrt_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sqrt_le_sqrt_iff' (hx : 0 < x) : √x <= √y ↔ x <= y
参数：hx : 0 < x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sqrt_pos`：sqrt_pos : 0 < √x ↔ 0 < x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Real.sqrt_le_sqrt_iff`：sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= 
y
-/
lemma sqrt_le_sqrt_iff' (hx : 0 < x) : √x ≤ √y ↔ x ≤ y := by
  obtain hy | hy := le_total y 0
  · exact iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt <| sqrt_pos.2 hx).not_ge
      (hy.trans_lt hx).not_ge
  · exact sqrt_le_sqrt_iff hy
/-
**Real.one_le_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, 1 ≤ √x ↔ 1 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用引理 `Real.sqrt_le_sqrt_iff'`：sqrt_le_sqrt_iff' (hx : 0 < x) : √x <= √y ↔ x <=
 y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_le_sqrt : 1 ≤ √x ↔ 1 ≤ x := by
  rw [← sqrt_one, sqrt_le_sqrt_iff' zero_lt_one, sqrt_one]
/-
**Real.sqrt_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, √x ≤ 1 ↔ x ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用定理 `Real.sqrt_le_sqrt_iff`：sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= 
y
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma sqrt_le_one : √x ≤ 1 ↔ x ≤ 1 := by
  rw [← sqrt_one, sqrt_le_sqrt_iff zero_le_one, sqrt_one]
/-
**Real.isSquare_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, IsSquare x ↔ 0 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSquare.nonneg`：IsSquare.nonneg [Semiring R] [LinearOrder R] [ExistsAdd
OfLE R] [PosMulMono R] [AddLeftMono R] {x : R} (h : IsSquare x) : 0 <= x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
-/
@[simp] lemma isSquare_iff : IsSquare x ↔ 0 ≤ x :=
  ⟨(·.nonneg), (⟨√x, mul_self_sqrt · |>.symm⟩)⟩
/-
**Real.sqrt_le_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, √x ≤ x ↔ x = 0 ∨ 1 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_le_iff`：sqrt_le_iff : √x <= y ↔ 0 <= y ∧ x <= y ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_sub_one`：mul_sub_one (a b : α) : a * (b - 1) = a * b - a
-/
@[simp] lemma sqrt_le_self_iff : √x ≤ x ↔ x = 0 ∨ 1 ≤ x := by
  rw [sqrt_le_iff, ← sub_nonneg (a := x ^ 2), sq, ← mul_sub_one]
  grind [mul_nonneg_iff]
/-
**Real.le_sqrt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, x ≤ √x ↔ x ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Real.le_sqrt'`：le_sqrt' (hx : 0 < x) : x <= √y ↔ x ^ 2 <= y
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `mul_le_iff_le_one_left`：mul_le_iff_le_one_left [MulPosMono α] [MulPosRef
lectLE α] (b0 : 0 < b) : a * b <= b ↔ a <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma le_sqrt_self_iff : x ≤ √x ↔ x ≤ 1 := by
  obtain hx | hx := le_or_gt x 0
  · simp [hx.trans]
  · rw [le_sqrt' hx, sq, mul_le_iff_le_one_left hx]
/-
**Real.sqrt_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, √x < x ↔ 1 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sqrt_lt_self_iff : √x < x ↔ 1 < x := by simp [← not_le]
/-
**Real.lt_sqrt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {x : ℝ}, x < √x ↔ x ≠ 0 ∧ x < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma lt_sqrt_self_iff : x < √x ↔ x ≠ 0 ∧ x < 1 := by simp [← not_le]

end Real

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: a square root of a strictly positive nonnegative real is
positive. -/
@[positivity NNReal.sqrt _]
meta def evalNNRealSqrt : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(NNReal), ~q(NNReal.sqrt $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(NNReal.sqrt_pos_of_pos $pa))
    | _ => failure -- this case is dealt with by generic nonnegativity of nnreals
  | _, _, _ => throwError "not NNReal.sqrt"

/-- Extension for the `positivity` tactic: a square root is nonnegative, and is strictly positive if
its input is. -/
@[positivity √_]
meta def evalSqrt : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(√$a) =>
    assertInstancesCommute
    let ra ← catchNone <| core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure (.positive q(Real.sqrt_pos_of_pos $pa))
    | _ => pure (.nonnegative q(Real.sqrt_nonneg $a))
  | _, _, _ => throwError "not Real.sqrt"

end Mathlib.Meta.Positivity

namespace Real

/-
**Real.one_lt_sqrt_two** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：one_lt_sqrt_two : 1 < √2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_one`：sqrt_one : √1 = 1
· 使用定理 `Real.sqrt_lt_sqrt`：sqrt_lt_sqrt (hx : 0 <= x) (h : x < y) : √x < √y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma one_lt_sqrt_two : 1 < √2 := by rw [← Real.sqrt_one]; gcongr; simp
/-
**Real.sqrt_two_lt_three_halves** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sqrt_two_lt_three_halves : √2 < 3 / 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_lt_sq₀`：sq_lt_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 < b ^ 2 ↔ a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
-/
lemma sqrt_two_lt_three_halves : √2 < 3 / 2 := by
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  grind
/-
**Real.inv_sqrt_two_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：inv_sqrt_two_sub_one : (√2 - 1)⁻¹ = √2 + 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_sqrt_two_sub_one : (√2 - 1)⁻¹ = √2 + 1 := by
  grind

@[simp]
/-
**Real.sqrt_mul** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) = √x * √y
参数：hx : 0 <= x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.toNNReal_mul`：toNNReal_mul {p q : Real} (hp : 0 <= p) : Real.toNNRe
al (p * q) = Real.toNNReal p * Real.toNNReal q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.sqrt_mul`：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt
 y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sqrt_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x * y) = √x * √y := by
  simp_rw [Real.sqrt, ← NNReal.coe_mul, NNReal.coe_inj, Real.toNNReal_mul hx, NNReal.sqrt_mul]

@[simp]
/-
**Real.sqrt_mul'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_mul' (x) {y : Real} (hy : 0 <= y) : √(x * y) = √x * √y
参数：x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
-/
theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : √(x * y) = √x * √y := by
  rw [mul_comm, sqrt_mul hy, mul_comm]

@[simp]
/-
**Real.sqrt_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt.eq_1`：∀ (x : ℝ), √x = ↑(NNReal.sqrt x.toNNReal)
· 使用定理 `Real.toNNReal_inv`：∀ {x : ℝ}, x⁻¹.toNNReal = x.toNNReal⁻¹
· 使用定理 `NNReal.sqrt_inv`：sqrt_inv (x : Real>=0) : sqrt x⁻¹ = (sqrt x)⁻¹
· 使用定理 `NNReal.coe_inv`：∀ (r : NNReal), ↑r⁻¹ = (↑r)⁻¹
-/
theorem sqrt_inv (x : ℝ) : √x⁻¹ = (√x)⁻¹ := by
  rw [Real.sqrt, Real.toNNReal_inv, NNReal.sqrt_inv, NNReal.coe_inv, Real.sqrt]

@[simp]
/-
**Real.sqrt_div** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_div {x : Real} (hx : 0 <= x) (y : Real) : √(x / y) = √x / √y
参数：hx : 0 <= x；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
-/
theorem sqrt_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : √(x / y) = √x / √y := by
  rw [division_def, sqrt_mul hx, sqrt_inv, division_def]

@[simp]
/-
**Real.sqrt_div'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_div' (x) {y : Real} (hy : 0 <= y) : √(x / y) = √x / √y
参数：x；hy : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
· 使用定理 `Real.sqrt_mul'`：sqrt_mul' (x) {y : Real} (hy : 0 <= y) : √(x * y) = √x *
 √y
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
· 使用定理 `Real.sqrt_inv`：sqrt_inv (x : Real) : √x⁻¹ = (√x)⁻¹
-/
theorem sqrt_div' (x) {y : ℝ} (hy : 0 ≤ y) : √(x / y) = √x / √y := by
  rw [division_def, sqrt_mul' x (inv_nonneg.2 hy), sqrt_inv, division_def]

variable {x y : ℝ}

@[simp]
/-
**Real.div_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：div_sqrt : x / √x = √x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_sqrt : x / √x = √x := by
  grind
/-
**Real.sqrt_div_self'** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_div_self' : √x / x = 1 / √x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.div_sqrt`：div_sqrt : x / √x = √x
· 使用定理 `one_div_div`：one_div_div : 1 / (a / b) = b / a
-/
theorem sqrt_div_self' : √x / x = 1 / √x := by rw [← div_sqrt, one_div_div, div_sqrt]
/-
**Real.sqrt_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_div_self : √x / x = (√x)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_div_self'`：sqrt_div_self' : √x / x = 1 / √x
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem sqrt_div_self : √x / x = (√x)⁻¹ := by rw [sqrt_div_self', one_div]
/-
**Real.lt_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_sqrt (hx : 0 <= x) : x < √y ↔ x ^ 2 < y
参数：hx : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_lt_sqrt_iff`：sqrt_lt_sqrt_iff (hx : 0 <= x) : √x < √y ↔ x < y
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_sqrt (hx : 0 ≤ x) : x < √y ↔ x ^ 2 < y := by
  rw [← sqrt_lt_sqrt_iff (sq_nonneg _), sqrt_sq hx]
/-
**Real.sq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sq_lt : x ^ 2 < y ↔ -√y < x ∧ x < √y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `Real.lt_sqrt`：lt_sqrt (hx : 0 <= x) : x < √y ↔ x ^ 2 < y
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sq_lt : x ^ 2 < y ↔ -√y < x ∧ x < √y := by
  rw [← abs_lt, ← sq_abs, lt_sqrt (abs_nonneg _)]
/-
**Real.neg_sqrt_lt_of_sq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：neg_sqrt_lt_of_sq_lt (h : x ^ 2 < y) : -√y < x
参数：h : x ^ 2 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.sq_lt`：sq_lt : x ^ 2 < y ↔ -√y < x ∧ x < √y
-/
theorem neg_sqrt_lt_of_sq_lt (h : x ^ 2 < y) : -√y < x :=
  (sq_lt.mp h).1
/-
**Real.lt_sqrt_of_sq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < √y
参数：h : x ^ 2 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.sq_lt`：sq_lt : x ^ 2 < y ↔ -√y < x ∧ x < √y
-/
theorem lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < √y :=
  (sq_lt.mp h).2
/-
**Real.lt_sq_of_sqrt_lt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lt_sq_of_sqrt_lt (h : √x < y) : x < y ^ 2
参数：h : √x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_lt_sqrt_iff_of_pos`：sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : √x 
< √y ↔ x < y
· 使用引理 `sq_pos_of_pos`：sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a 
^ 2
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem lt_sq_of_sqrt_lt (h : √x < y) : x < y ^ 2 := by
  have hy := x.sqrt_nonneg.trans_lt h
  rwa [← sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le]

/-- The natural square root is at most the real square root -/
/-
**Real.nat_sqrt_le_real_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nat_sqrt_le_real_sqrt {a : Nat} : ↑(Nat.sqrt a) <= √(a : Real)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.le_sqrt`：le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Nat.sqrt_le'`：sqrt_le' (n : Nat) : sqrt n ^ 2 <= n

--- 原说明 ---
The natural square root is at most the real square root
-/
theorem nat_sqrt_le_real_sqrt {a : ℕ} : ↑(Nat.sqrt a) ≤ √(a : ℝ) := by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  norm_cast
  exact Nat.sqrt_le' a

/-- The real square root is less than the natural square root plus one -/
/-
**Real.real_sqrt_lt_nat_sqrt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：real_sqrt_lt_nat_sqrt_succ {a : Nat} : √(a : Real) < Nat.sqrt a + 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_lt`：sqrt_lt (hx : 0 <= x) (hy : 0 <= y) : √x < y ↔ x < y ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.lt_succ_sqrt'`：lt_succ_sqrt' (n : Nat) : n < succ (sqrt n) ^ 2

--- 原说明 ---
The real square root is less than the natural square root plus one
-/
theorem real_sqrt_lt_nat_sqrt_succ {a : ℕ} : √(a : ℝ) < Nat.sqrt a + 1 := by
  rw [sqrt_lt (by simp)] <;> norm_cast
  · exact Nat.lt_succ_sqrt' a
  · exact Nat.le_add_left 0 (Nat.sqrt a + 1)

/-- The real square root is at most the natural square root plus one -/
/-
**Real.real_sqrt_le_nat_sqrt_succ** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：real_sqrt_le_nat_sqrt_succ {a : Nat} : √(a : Real) <= Nat.sqrt a + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.real_sqrt_lt_nat_sqrt_succ`：real_sqrt_lt_nat_sqrt_succ {a : Nat} : 
√(a : Real) < Nat.sqrt a + 1

--- 原说明 ---
The real square root is at most the natural square root plus one
-/
theorem real_sqrt_le_nat_sqrt_succ {a : ℕ} : √(a : ℝ) ≤ Nat.sqrt a + 1 :=
  real_sqrt_lt_nat_sqrt_succ.le

/-- The floor of the real square root is the same as the natural square root. -/
@[simp]
/-
**Real.floor_real_sqrt_eq_nat_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：floor_real_sqrt_eq_nat_sqrt {a : Nat} : ⌊√(a : Real)⌋ = Nat.sqrt a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_eq_iff`：floor_eq_iff : ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
· 使用定理 `Real.nat_sqrt_le_real_sqrt`：nat_sqrt_le_real_sqrt {a : Nat} : ↑(Nat.sqrt
 a) <= √(a : Real)
· 使用定理 `Real.real_sqrt_lt_nat_sqrt_succ`：real_sqrt_lt_nat_sqrt_succ {a : Nat} : 
√(a : Real) < Nat.sqrt a + 1

--- 原说明 ---
The floor of the real square root is the same as the natural square root.
-/
theorem floor_real_sqrt_eq_nat_sqrt {a : ℕ} : ⌊√(a : ℝ)⌋ = Nat.sqrt a := by
  rw [Int.floor_eq_iff]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

/-- The natural floor of the real square root is the same as the natural square root. -/
@[simp]
/-
**Real.nat_floor_real_sqrt_eq_nat_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nat_floor_real_sqrt_eq_nat_sqrt {a : Nat} : ⌊√(a : Real)⌋₊ = Nat.sqrt a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.floor_eq_iff`：floor_eq_iff (ha : 0 <= a) : ⌊a⌋₊ = n ↔ ↑n <= a ∧ a < 
↑n + 1
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `Real.nat_sqrt_le_real_sqrt`：nat_sqrt_le_real_sqrt {a : Nat} : ↑(Nat.sqrt
 a) <= √(a : Real)
· 使用定理 `Real.real_sqrt_lt_nat_sqrt_succ`：real_sqrt_lt_nat_sqrt_succ {a : Nat} : 
√(a : Real) < Nat.sqrt a + 1

--- 原说明 ---
The natural floor of the real square root is the same as the natural square root
.
-/
theorem nat_floor_real_sqrt_eq_nat_sqrt {a : ℕ} : ⌊√(a : ℝ)⌋₊ = Nat.sqrt a := by
  rw [Nat.floor_eq_iff (sqrt_nonneg a)]
  exact ⟨nat_sqrt_le_real_sqrt, real_sqrt_lt_nat_sqrt_succ⟩

/-- Bernoulli's inequality for exponent `1 / 2`, stated using `sqrt`. -/
/-
**Real.sqrt_one_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_one_add_le (h : -1 <= x) : √(1 + x) <= 1 + x / 2
参数：h : -1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sqrt_le_iff`：sqrt_le_iff : √x <= y ↔ 0 <= y ∧ x <= y ^ 2
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 93 条，此处仅展示前 30 条）

--- 原说明 ---
Bernoulli's inequality for exponent `1 / 2`, stated using `sqrt`.
-/
theorem sqrt_one_add_le (h : -1 ≤ x) : √(1 + x) ≤ 1 + x / 2 := by
  refine sqrt_le_iff.mpr ⟨by linarith, ?_⟩
  calc 1 + x
    _ ≤ 1 + x + (x / 2) ^ 2 := le_add_of_nonneg_right <| sq_nonneg _
    _ = _ := by ring
/-
**Real.sqrt_prod** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrt_prod {ι : Type*} (s : Finset ι) {x : ι -> Real} (hx : forall i in s, 
0 <= x i) : √(∏ i in s, x i) = ∏ i in s, √(x i)
参数：s : Finset ι；hx : forall i in s, 0 <= x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.sqrt_zero`：NNReal.sqrt 0 = 0
· 使用定理 `NNReal.sqrt_one`：NNReal.sqrt 1 = 1
· 使用定理 `NNReal.sqrt_mul`：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt
 y
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `NNReal.coe_prod`：coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s
, f a) = ∏ a in s, (f a : Real)
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
theorem sqrt_prod {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ i ∈ s, 0 ≤ x i) :
    √(∏ i ∈ s, x i) = ∏ i ∈ s, √(x i) := by
  convert! congr_arg NNReal.toReal <| map_prod NNReal.sqrtHom (Real.toNNReal ∘ x) s <;>
    simp +contextual [-map_prod, NNReal.sqrtHom, hx]

end Real

open Real

variable {α : Type*}

/-
**Filter.Tendsto.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.sqrt {f : α -> Real} {l : Filter α} {x : Real} (h : Tendsto
 f l (𝓝 x)) : Tendsto (fun x => √(f x)) l (𝓝 (√x))
参数：h : Tendsto f l (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_sqrt`：continuous_sqrt : Continuous (√· : Real -> Real)
-/
theorem Filter.Tendsto.sqrt {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) :
    Tendsto (fun x => √(f x)) l (𝓝 (√x)) :=
  (continuous_sqrt.tendsto _).comp h

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

nonrec theorem ContinuousWithinAt.sqrt (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => √(f x)) s x :=
  h.sqrt

@[fun_prop]
nonrec theorem ContinuousAt.sqrt (h : ContinuousAt f x) : ContinuousAt (fun x => √(f x)) x :=
  h.sqrt

@[fun_prop]
/-
**ContinuousOn.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.sqrt (h : ContinuousOn f s) : ContinuousOn (fun x => √(f x)) 
s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.sqrt`：∀ {α : Type u_1} [inst : TopologicalSpace α] {f
 : α → ℝ} {s : Set α} {x : α},   ContinuousWithinAt f s x → ContinuousWithinAt (
fun x => √(f …
-/
theorem ContinuousOn.sqrt (h : ContinuousOn f s) : ContinuousOn (fun x => √(f x)) s :=
  fun x hx => (h x hx).sqrt

@[continuity, fun_prop]
/-
**Continuous.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.sqrt (h : Continuous f) : Continuous fun x => √(f x)
参数：h : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Real.continuous_sqrt`：continuous_sqrt : Continuous (√· : Real -> Real)
-/
theorem Continuous.sqrt (h : Continuous f) : Continuous fun x => √(f x) :=
  continuous_sqrt.comp h

namespace NNReal
variable {ι : Type*}
open Finset

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ≥0`. -/
/-
**NNReal.sum_mul_le_sqrt_mul_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι -> Real>=0) : ∑ i in s, f
 i * g i <= sqrt (∑ i in s, f i ^ 2) * sqrt (∑ i in s, g i ^ 2)
参数：s : Finset ι；f g : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `NNReal.le_sqrt_iff_sq_le`：le_sqrt_iff_sq_le : x <= sqrt y ↔ x ^ 2 <= y
· 使用引理 `Finset.sum_mul_sq_le_sq_mul_sq`：sum_mul_sq_le_sq_mul_sq [CommSemiring R]
 [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f g :
 ι -> R) : (∑ i in s…
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.sqrt_mul`：sqrt_mul (x y : Real>=0) : sqrt (x * y) = sqrt x * sqrt
 y

--- 原说明 ---
**Cauchy-Schwarz inequality** for finsets using square roots in `ℝ≥0`.
-/
lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, f i * g i ≤ sqrt (∑ i ∈ s, f i ^ 2) * sqrt (∑ i ∈ s, g i ^ 2) :=
  (le_sqrt_iff_sq_le.2 <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq <| sqrt_mul _ _

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ≥0`. -/
/-
**NNReal.sum_sqrt_mul_sqrt_le** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：sum_sqrt_mul_sqrt_le (s : Finset ι) (f g : ι -> Real>=0) : ∑ i in s, sqrt 
(f i) * sqrt (g i) <= sqrt (∑ i in s, f i) * sqrt (∑ i in s, g i)
参数：s : Finset ι；f g : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
· 使用引理 `NNReal.sum_mul_le_sqrt_mul_sqrt`：sum_mul_le_sqrt_mul_sqrt (s : Finset ι)
 (f g : ι -> Real>=0) : ∑ i in s, f i * g i <= sqrt (∑ i in s, f i ^ 2) * sqrt (
∑ i in s, g i ^ 2)

--- 原说明 ---
**Cauchy-Schwarz inequality** for finsets using square roots in `ℝ≥0`.
-/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, sqrt (f i) * sqrt (g i) ≤ sqrt (∑ i ∈ s, f i) * sqrt (∑ i ∈ s, g i) := by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x ↦ sqrt (f x)) (fun x ↦ sqrt (g x))

end NNReal

namespace Real
variable {ι : Type*} {f g : ι → ℝ}
open Finset

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ`. -/
/-
**Real.sum_mul_le_sqrt_mul_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι -> Real) : ∑ i in s, f i 
* g i <= √(∑ i in s, f i ^ 2) * √(∑ i in s, g i ^ 2)
参数：s : Finset ι；f g : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Real.le_sqrt_of_sq_le`：le_sqrt_of_sq_le (h : x ^ 2 <= y) : x <= √y
· 使用引理 `Finset.sum_mul_sq_le_sq_mul_sq`：sum_mul_sq_le_sq_mul_sq [CommSemiring R]
 [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f g :
 ι -> R) : (∑ i in s…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)

--- 原说明 ---
**Cauchy-Schwarz inequality** for finsets using square roots in `ℝ`.
-/
lemma sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, f i * g i ≤ √(∑ i ∈ s, f i ^ 2) * √(∑ i ∈ s, g i ^ 2) :=
  (le_sqrt_of_sq_le <| sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq <| sqrt_mul
    (sum_nonneg fun _ _ ↦ by positivity) _

/-- **Cauchy-Schwarz inequality** for finsets using square roots in `ℝ`. -/
/-
**Real.sum_sqrt_mul_sqrt_le** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：sum_sqrt_mul_sqrt_le (s : Finset ι) (hf : forall i, 0 <= f i) (hg : forall
 i, 0 <= g i) : ∑ i in s, √(f i) * √(g i) <= √(∑ i in s, f i) * √(∑ i in s, g i)
参数：s : Finset ι；hf : forall i, 0 <= f i；hg : forall i, 0 <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Real.sum_mul_le_sqrt_mul_sqrt`：sum_mul_le_sqrt_mul_sqrt (s : Finset ι) (
f g : ι -> Real) : ∑ i in s, f i * g i <= √(∑ i in s, f i ^ 2) * √(∑ i in s, g i
 ^ 2)

--- 原说明 ---
**Cauchy-Schwarz inequality** for finsets using square roots in `ℝ`.
-/
lemma sum_sqrt_mul_sqrt_le (s : Finset ι) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, √(f i) * √(g i) ≤ √(∑ i ∈ s, f i) * √(∑ i ∈ s, g i) := by
  simpa [*] using sum_mul_le_sqrt_mul_sqrt _ (fun x ↦ √(f x)) (fun x ↦ √(g x))

end Real

