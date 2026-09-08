/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Positivity.Core

/-!
# Absolute values

This file defines a bundled type of absolute values `AbsoluteValue R S`.

## Main definitions

* `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`.
* `AbsoluteValue.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
* `AbsoluteValue.toMonoidWithZeroHom`: absolute values mapping to a
  linear ordered field preserve `0`, `*` and `1`
* `IsAbsoluteValue`: a type class stating that `f : β → α` satisfies the axioms of an absolute
  value
-/

@[expose] public section

variable {ι α R S : Type*}

/-- `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy
the triangle inequality. -/
/-
**AbsoluteValue** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_5) → (S : Type u_6) → [Semiring R] → [Semiring S] → [PartialOr
der S] → Type (max u_5 u_6)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy
the triangle inequality.
-/
structure AbsoluteValue (R S : Type*) [Semiring R] [Semiring S] [PartialOrder S]
    extends R →ₙ* S where
  /-- The absolute value is nonnegative -/
  nonneg' : ∀ x, 0 ≤ toFun x
  /-- The absolute value is positive definitive -/
  eq_zero' : ∀ x, toFun x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  add_le' : ∀ x y, toFun (x + y) ≤ toFun x + toFun y

namespace AbsoluteValue

attribute [nolint docBlame] AbsoluteValue.toMulHom

section OrderedSemiring

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

/-
**AbsoluteValue.funLike** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
形式化陈述：funLike : FunLike (AbsoluteValue R S) R S where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (AbsoluteValue R S) R S where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
/-
**AbsoluteValue.zeroHomClass** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
形式化陈述：zeroHomClass : ZeroHomClass (AbsoluteValue R S) R S where map_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.eq_zero'`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (self : AbsoluteValue R S)
 (x : R), se…
-/
instance zeroHomClass : ZeroHomClass (AbsoluteValue R S) R S where
  map_zero f := (f.eq_zero' _).2 rfl
/-
**AbsoluteValue.mulHomClass** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
形式化陈述：mulHomClass : MulHomClass (AbsoluteValue R S) R S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…
-/
instance mulHomClass : MulHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_mul := fun f => f.map_mul' }
/-
**AbsoluteValue.nonnegHomClass** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
形式化陈述：nonnegHomClass : NonnegHomClass (AbsoluteValue R S) R S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.nonneg'`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (self : AbsoluteValue R S) 
(x : R), 0 …
-/
instance nonnegHomClass : NonnegHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with apply_nonneg := fun f => f.nonneg' }
/-
**AbsoluteValue.subadditiveHomClass** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
形式化陈述：subadditiveHomClass : SubadditiveHomClass (AbsoluteValue R S) R S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.add_le'`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (self : AbsoluteValue R S) 
(x y : R), …
-/
instance subadditiveHomClass : SubadditiveHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.zeroHomClass (R := R) (S := S) with map_add_le_add := fun f => f.add_le' }

@[simp]
/-
**AbsoluteValue.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：coe_mk (f : R ->ₙ* S) {h₁ h₂ h₃} : (AbsoluteValue.mk f h₁ h₂ h₃ : R -> S) 
= f
参数：f : R ->ₙ* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : R →ₙ* S) {h₁ h₂ h₃} : (AbsoluteValue.mk f h₁ h₂ h₃ : R → S) = f :=
  rfl

@[ext]
/-
**AbsoluteValue.ext** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：ext ⦃f g : AbsoluteValue R S⦄ : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : AbsoluteValue R S⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

/-- See Note [custom simps projection]. -/
/-
**AbsoluteValue.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue.Simps`。
形式化陈述：{R : Type u_5} →   {S : Type u_6} → [inst : Semiring R] → [inst_1 : Semiri
ng S] → [inst_2 : PartialOrder S] → AbsoluteValue R S → R → S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.apply (f : AbsoluteValue R S) : R → S :=
  f

initialize_simps_projections AbsoluteValue (toFun → apply)

@[simp]
/-
**AbsoluteValue.coe_toMulHom** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：coe_toMulHom : ⇑abv.toMulHom = abv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMulHom : ⇑abv.toMulHom = abv :=
  rfl

@[bound]
/-
**AbsoluteValue.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x : R), 0 ≤ abv x
参数：abv : AbsoluteValue R S；x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.nonneg'`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (self : AbsoluteValue R S) 
(x : R), 0 …
-/
protected theorem nonneg (x : R) : 0 ≤ abv x :=
  abv.nonneg' x

@[simp]
/-
**AbsoluteValue.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : R}, abv x = 0 ↔ x = 0
参数：abv : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.eq_zero'`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (self : AbsoluteValue R S)
 (x : R), se…
-/
protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 :=
  abv.eq_zero' x

@[bound]
/-
**AbsoluteValue.add_le** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x y : R), abv (x + y) ≤ a
bv x + abv y
参数：abv : AbsoluteValue R S；x y : R；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.add_le'`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (self : AbsoluteValue R S) 
(x y : R), …
-/
protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y :=
  abv.add_le' x y

/-- The triangle inequality for an `AbsoluteValue` applied to a list. -/
/-
**AbsoluteValue.listSum_le** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue`。
形式化陈述：listSum_le [AddLeftMono S] (l : List R) : abv l.sum <= (l.map abv).sum
参数：l : List R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c

--- 原说明 ---
The triangle inequality for an `AbsoluteValue` applied to a list.
-/
lemma listSum_le [AddLeftMono S] (l : List R) : abv l.sum ≤ (l.map abv).sum := by
  induction l with
  | nil => simp
  | cons head tail ih => exact (abv.add_le ..).trans <| add_le_add_right ih (abv head)

@[simp]
/-
**AbsoluteValue.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x y : R), abv (x * y) = a
bv x * abv y
参数：abv : AbsoluteValue R S；x y : R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…
-/
protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y :=
  abv.map_mul' x y
/-
**AbsoluteValue.ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : R}, abv x ≠ 0 ↔ x ≠ 0
参数：abv : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `AbsoluteValue.eq_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, abv…
-/
protected theorem ne_zero_iff {x : R} : abv x ≠ 0 ↔ x ≠ 0 :=
  abv.eq_zero.not
protected alias ⟨_, ne_zero⟩ := AbsoluteValue.ne_zero_iff

@[simp]
/-
**AbsoluteValue.pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : R}, 0 < abv x ↔ x ≠ 0
参数：abv : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `AbsoluteValue.ne_zero_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R 
S) {x : R}, abv…
-/
protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
  (abv.nonneg x).lt_iff_ne'.trans abv.ne_zero_iff
protected alias ⟨_, pos⟩ := AbsoluteValue.pos_iff

@[simp]
/-
**AbsoluteValue.nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : R}, abv x ≤ 0 ↔ x = 0
参数：abv : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsoluteValue.eq_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, abv…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem nonpos_iff {x : R} : abv x ≤ 0 ↔ x = 0 := by
  simp only [← abv.eq_zero, le_antisymm_iff, abv.nonneg, and_true]
/-
**AbsoluteValue.map_one_of_isLeftRegular** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValu
e`。
形式化陈述：map_one_of_isLeftRegular (h : IsLeftRegular (abv 1)) : abv 1 = 1
参数：h : IsLeftRegular (abv 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_one_of_isLeftRegular (h : IsLeftRegular (abv 1)) : abv 1 = 1 :=
  h <| by simp [← abv.map_mul]

@[simp]
/-
**AbsoluteValue.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S), abv 0 = 0
参数：abv : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.eq_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, abv…
-/
protected theorem map_zero : abv 0 = 0 :=
  abv.eq_zero.2 rfl

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

/-
**AbsoluteValue.sub_le** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Ring R] [inst_1 : Semiring S] [ins
t_2 : PartialOrder S]   (abv : AbsoluteValue R S) (a b c : R), abv (a - c) ≤ abv
 (a - b) + abv (b - c)
参数：abv : AbsoluteValue R S；a b c : R；a - c；a - b；b - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…
-/
protected theorem sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv.add_le (a - b) (b - c)

@[simp high] -- added `high` to apply it before `AbsoluteValue.eq_zero`
/-
**AbsoluteValue.map_sub_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b
参数：a b : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AbsoluteValue.eq_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, abv…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
theorem map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
  abv.eq_zero.trans sub_eq_zero

end Ring

section Semiring

section IsDomain

-- all of these are true for `NoZeroDivisors S`; but it doesn't work smoothly with the
-- `IsDomain`/`IsCancelMulZero` API
variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)
variable [IsDomain S] [Nontrivial R]

@[simp]
/-
**AbsoluteValue.map_one** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [IsDomain S] [Nontrivial R
], abv 1 = 1
参数：abv : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_one_of_isLeftRegular`：map_one_of_isLeftRegular (h : Is
LeftRegular (abv 1)) : abv 1 = 1
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `AbsoluteValue.ne_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, x ≠…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
protected theorem map_one : abv 1 = 1 :=
  abv.map_one_of_isLeftRegular (IsRegular.of_ne_zero <| abv.ne_zero one_ne_zero).left
/-
**AbsoluteValue.monoidWithZeroHomClass** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`
。
形式化陈述：monoidWithZeroHomClass : MonoidWithZeroHomClass (AbsoluteValue R S) R S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_one`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
-/
instance monoidWithZeroHomClass : MonoidWithZeroHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.mulHomClass with
    map_zero := fun f => f.map_zero
    map_one := fun f => f.map_one }

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*`, `0` and `1`. -/
/-
**AbsoluteValue.toMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：toMonoidWithZeroHom : R ->*₀ S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Absolute values from a nontrivial `R` to a linear ordered ring preserve `*`, `0`
 and `1`.
-/
def toMonoidWithZeroHom : R →*₀ S :=
  .ofClass abv

@[simp]
/-
**AbsoluteValue.coe_toMonoidWithZeroHom** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue
`。
形式化陈述：coe_toMonoidWithZeroHom : ⇑abv.toMonoidWithZeroHom = abv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMonoidWithZeroHom : ⇑abv.toMonoidWithZeroHom = abv :=
  rfl

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*` and `1`. -/
/-
**AbsoluteValue.toMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：toMonoidHom : R ->* S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Absolute values from a nontrivial `R` to a linear ordered ring preserve `*` and 
`1`.
-/
def toMonoidHom : R →* S :=
  abv

@[simp]
/-
**AbsoluteValue.coe_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：coe_toMonoidHom : ⇑abv.toMonoidHom = abv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMonoidHom : ⇑abv.toMonoidHom = abv :=
  rfl

@[simp]
/-
**AbsoluteValue.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S] 
[inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [IsDomain S] [Nontrivial R
] (a : R) (n : ℕ), abv (a ^ n) = abv a ^ n
参数：abv : AbsoluteValue R S；a : R；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
protected theorem map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
  abv.toMonoidHom.map_pow a n

omit [Nontrivial R] in
/-- An absolute value satisfies `f (n : R) ≤ n` for every `n : ℕ`. -/
/-
**AbsoluteValue.apply_nat_le_self** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue`。
形式化陈述：apply_nat_le_self [IsOrderedRing S] (n : Nat) : abv n <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `AbsoluteValue.map_one`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
An absolute value satisfies `f (n : R) ≤ n` for every `n : ℕ`.
-/
lemma apply_nat_le_self [IsOrderedRing S] (n : ℕ) : abv n ≤ n := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.eq_zero (α := R)]
  induction n with
  | zero => simp
  | succ n ih =>
  · grw [Nat.cast_succ, Nat.cast_succ, abv.add_le, abv.map_one, ih]

end IsDomain

end Semiring

end OrderedSemiring

section OrderedRing

section Ring

variable {R S : Type*} [Ring R] [Ring S] [PartialOrder S] [IsOrderedRing S]
  (abv : AbsoluteValue R S)

@[bound]
/-
**AbsoluteValue.le_sub** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : Ring R] [inst_1 : Ring S] [inst_2 
: PartialOrder S] [IsOrderedRing S]   (abv : AbsoluteValue R S) (a b : R), abv a
 - abv b ≤ abv (a - b)
参数：abv : AbsoluteValue R S；a b : R；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…
-/
protected theorem le_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  sub_le_iff_le_add.2 <| by simpa using abv.add_le (a - b) b

end Ring

end OrderedRing

section OrderedCommRing

variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [Ring R]
  (abv : AbsoluteValue R S) [NoZeroDivisors S]

/-
**AbsoluteValue.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing S] [inst_1 : PartialOrder
 S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : AbsoluteValue R S) [NoZeroDivis
ors S] (a : R), abv (-a) = abv a
参数：abv : AbsoluteValue R S；a : R；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_self_eq_mul_self_iff`：mul_self_eq_mul_self_iff [NonUnitalNonAssocCom
mRing R] [NoZeroDivisors R] {a b : R} : a * a = b * b ↔ a = b ∨ a = -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
-/
protected theorem map_neg (a : R) : abv (-a) = abv a := by
  by_cases ha : a = 0; · simp [ha]
  refine
    (mul_self_eq_mul_self_iff.mp (by rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right ?_
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'
/-
**AbsoluteValue.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing S] [inst_1 : PartialOrder
 S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : AbsoluteValue R S) [NoZeroDivis
ors S] (a b : R), abv (a - b) = abv (b - a)
参数：abv : AbsoluteValue R S；a b : R；a - b；b - a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `AbsoluteValue.map_neg`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
-/
protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) := by rw [← neg_sub, abv.map_neg]

/-- Bound `abv (a + b)` from below -/
@[bound]
/-
**AbsoluteValue.le_add** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing S] [inst_1 : PartialOrder
 S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : AbsoluteValue R S) [NoZeroDivis
ors S] (a b : R), abv a - abv b ≤ abv (a + b)
参数：abv : AbsoluteValue R S；a b : R；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `AbsoluteValue.map_neg`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…

--- 原说明 ---
Bound `abv (a + b)` from below
-/
protected theorem le_add (a b : R) : abv a - abv b ≤ abv (a + b) := by
  simpa only [tsub_le_iff_right, add_neg_cancel_right, abv.map_neg] using abv.add_le (a + b) (-b)

/-- Bound `abv (a - b)` from above -/
@[bound]
/-
**AbsoluteValue.sub_le_add** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue`。
形式化陈述：sub_le_add (a b : R) : abv (a - b) <= abv a + abv b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsoluteValue.map_neg`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…

--- 原说明 ---
Bound `abv (a - b)` from above
-/
lemma sub_le_add (a b : R) : abv (a - b) ≤ abv a + abv b := by
  simpa only [← sub_eq_add_neg, AbsoluteValue.map_neg] using abv.add_le a (-b)
/-
**AbsoluteValue.addGroupSeminormClass** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
形式化陈述：addGroupSeminormClass : AddGroupSeminormClass (AbsoluteValue R S) R S wher
e toSubadditiveHomClass
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `AbsoluteValue.map_neg`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
-/
instance addGroupSeminormClass : AddGroupSeminormClass (AbsoluteValue R S) R S where
  toSubadditiveHomClass := AbsoluteValue.subadditiveHomClass
  map_zero := AbsoluteValue.map_zero
  map_neg_eq_map f a := AbsoluteValue.map_neg f a
/-
**AbsoluteValue.** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] [IsDomain S] : MulRingNormClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.subadditiveHomClass,
    AbsoluteValue.monoidWithZeroHomClass with
    map_neg_eq_map := fun f => f.map_neg
    eq_zero_of_map_eq_zero := fun f _ => f.eq_zero.1 }

open Int in
/-
**AbsoluteValue.apply_natAbs_eq** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue`。
形式化陈述：apply_natAbs_eq (x : Int) : abv (natAbs x) = abv x
参数：x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
-/
lemma apply_natAbs_eq (x : ℤ) : abv (natAbs x) = abv x := by
  obtain ⟨_, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> simp

open Int in
/-- Values of an absolute value coincide on the image of `ℕ` in `R`
if and only if they coincide on the image of `ℤ` in `R`. -/
/-
**AbsoluteValue.eq_on_nat_iff_eq_on_int** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue
`。
形式化陈述：eq_on_nat_iff_eq_on_int {f g : AbsoluteValue R S} : (forall n : Nat, f n =
 g n) ↔ forall n : Int, f n = g n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…

--- 原说明 ---
Values of an absolute value coincide on the image of `ℕ` in `R`
if and only if they coincide on the image of `ℤ` in `R`.
-/
lemma eq_on_nat_iff_eq_on_int {f g : AbsoluteValue R S} :
    (∀ n : ℕ, f n = g n) ↔ ∀ n : ℤ, f n = g n := by
  refine ⟨fun h z ↦ ?_, fun a n ↦ mod_cast a n⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z <;> simp [h n]

end OrderedCommRing

section LinearOrderedRing

variable {R S : Type*} [Semiring R] [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
  (abv : AbsoluteValue R S)

/-- `AbsoluteValue.abs` is `abs` as a bundled `AbsoluteValue`. -/
@[simps]
/-
**AbsoluteValue.abs** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：{S : Type u_6} → [inst : Ring S] → [inst_1 : LinearOrder S] → [IsStrictOrd
eredRing S] → AbsoluteValue S S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AbsoluteValue.abs` is `abs` as a bundled `AbsoluteValue`.
-/
protected def abs : AbsoluteValue S S where
  toFun := abs
  nonneg' := abs_nonneg
  eq_zero' _ := abs_eq_zero
  add_le' := abs_add_le
  map_mul' := abs_mul
/-
**AbsoluteValue.** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (AbsoluteValue S S) :=
  ⟨AbsoluteValue.abs⟩

end LinearOrderedRing

section LinearOrderedCommRing

variable {R S : Type*} [Ring R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  (abv : AbsoluteValue R S)

@[bound]
/-
**AbsoluteValue.abs_abv_sub_le_abv_sub** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`
。
形式化陈述：abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) <= abv (a - b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AbsoluteValue.le_sub`：∀ {R : Type u_5} {S : Type u_6} [inst : Ring R] [i
nst_1 : Ring S] [inst_2 : PartialOrder S] [IsOrderedRing S]   (abv : AbsoluteVal
ue R S) (a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsoluteValue.map_sub`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  abs_sub_le_iff.2 ⟨abv.le_sub _ _, by rw [abv.map_sub]; apply abv.le_sub⟩

end LinearOrderedCommRing

section trivial

variable {R : Type*} [Semiring R] [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [Nontrivial S]

/-- The *trivial* absolute value takes the value `1` on all nonzero elements. -/
protected
/-
**AbsoluteValue.trivial** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：trivial : AbsoluteValue R S where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def trivial : AbsoluteValue R S where
  toFun x := if x = 0 then 0 else 1
  map_mul' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp [hx, hy]
  nonneg' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  eq_zero' x := by rcases eq_or_ne x 0 with hx | hx <;> simp [hx]
  add_le' x y := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    simp only [hx, ↓reduceIte, hy, one_add_one_eq_two]
    rcases eq_or_ne (x + y) 0 with hxy | hxy <;> simp [hxy, one_le_two]

@[simp]
/-
**AbsoluteValue.trivial_apply** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue`。
形式化陈述：trivial_apply {x : R} (hx : x != 0) : AbsoluteValue.trivial (S
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma trivial_apply {x : R} (hx : x ≠ 0) : AbsoluteValue.trivial (S := S) x = 1 :=
  if_neg hx

end trivial

section nontrivial

section OrderedSemiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

/-- An absolute value on a semiring `R` without zero divisors is *nontrivial* if it takes
a value `≠ 1` on a nonzero element.

This has the advantage over `v ≠ .trivial` that it does not require decidability
of `· = 0` in `R`. -/
/-
**AbsoluteValue.IsNontrivial** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：IsNontrivial (v : AbsoluteValue R S) : Prop
参数：v : AbsoluteValue R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute value on a semiring `R` without zero divisors is *nontrivial* if it 
takes
a value `≠ 1` on a nonzero element.

This has the advantage over `v ≠ .trivial` that it does not require decidability
of `· = 0` in `R`.
-/
def IsNontrivial (v : AbsoluteValue R S) : Prop :=
  ∃ x ≠ 0, v x ≠ 1
/-
**AbsoluteValue.isNontrivial_iff_ne_trivial** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteV
alue`。
形式化陈述：isNontrivial_iff_ne_trivial [DecidablePred fun x : R => x = 0] [NoZeroDivi
sors R] [Nontrivial S] (v : AbsoluteValue R S) : v.IsNontrivial ↔ v != .trivial
参数：v : AbsoluteValue R S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AbsoluteValue.trivial_apply`：trivial_apply {x : R} (hx : x != 0) : Absol
uteValue.trivial (S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `AbsoluteValue.ext`：ext ⦃f g : AbsoluteValue R S⦄ : (forall x, f x = g x)
 -> f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma isNontrivial_iff_ne_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [Nontrivial S] (v : AbsoluteValue R S) :
    v.IsNontrivial ↔ v ≠ .trivial := by
  refine ⟨fun ⟨x, hx₀, hx₁⟩ h ↦ hx₁ <| h.symm ▸ trivial_apply hx₀, fun H ↦ ?_⟩
  simp only [IsNontrivial]
  contrapose! H
  ext1 x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp [H, hx]

omit [IsOrderedRing S] in
/-
**AbsoluteValue.not_isNontrivial_iff** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue`。
形式化陈述：not_isNontrivial_iff (v : AbsoluteValue R S) : ¬ v.IsNontrivial ↔ forall x
 != 0, v x = 1
参数：v : AbsoluteValue R S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma not_isNontrivial_iff (v : AbsoluteValue R S) :
    ¬ v.IsNontrivial ↔ ∀ x ≠ 0, v x = 1 := by
  simp only [IsNontrivial]
  push Not
  rfl

omit [IsOrderedRing S] in
@[simp]
/-
**AbsoluteValue.not_isNontrivial_apply** 是 Mathlib 中的一个引理，位于命名空间 `AbsoluteValue`
。
形式化陈述：not_isNontrivial_apply {v : AbsoluteValue R S} (hv : ¬ v.IsNontrivial) {x 
: R} (hx : x != 0) : v x = 1
参数：hv : ¬ v.IsNontrivial；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AbsoluteValue.not_isNontrivial_iff`：not_isNontrivial_iff (v : AbsoluteVa
lue R S) : ¬ v.IsNontrivial ↔ forall x != 0, v x = 1
-/
lemma not_isNontrivial_apply {v : AbsoluteValue R S} (hv : ¬ v.IsNontrivial) {x : R} (hx : x ≠ 0) :
    v x = 1 :=
  v.not_isNontrivial_iff.mp hv _ hx

end OrderedSemiring

section LinearOrderedSemifield

variable [Field R] [Semifield S] [LinearOrder S] [IsStrictOrderedRing S] [ExistsAddOfLE S]
  {v : AbsoluteValue R S}

/-
**AbsoluteValue.IsNontrivial.exists_abv_gt_one** 是 Mathlib 中的一个定理，位于命名空间 `Absolu
teValue.IsNontrivial`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : Field R] [inst_1 : Semifield S] [i
nst_2 : LinearOrder S] [IsStrictOrderedRing S]   [ExistsAddOfLE S] {v : Absolute
Value R S}, v.IsNontrivial → ∃ x, 1 < v x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
-/
lemma IsNontrivial.exists_abv_gt_one (h : v.IsNontrivial) : ∃ x, 1 < v x := by
  obtain ⟨x, hx₀, hx₁⟩ := h
  rcases hx₁.lt_or_gt with h | h
  · refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀]
    exact (one_lt_inv₀ <| v.pos hx₀).mpr h
  · exact ⟨x, h⟩
/-
**AbsoluteValue.IsNontrivial.exists_abv_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Absolu
teValue.IsNontrivial`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : Field R] [inst_1 : Semifield S] [i
nst_2 : LinearOrder S] [IsStrictOrderedRing S]   [ExistsAddOfLE S] {v : Absolute
Value R S}, v.IsNontrivial → ∃ x, x ≠ 0 ∧ v x < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.IsNontrivial.exists_abv_gt_one`：∀ {R : Type u_3} {S : Type
 u_4} [inst : Field R] [inst_1 : Semifield S] [inst_2 : LinearOrder S] [IsStrict
OrderedRing S]   [ExistsAddOfLE S]…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AbsoluteValue.ne_zero_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R 
S) {x : R}, abv…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `inv_lt_one₀`：inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
-/
lemma IsNontrivial.exists_abv_lt_one (h : v.IsNontrivial) : ∃ x ≠ 0, v x < 1 := by
  obtain ⟨y, hy⟩ := h.exists_abv_gt_one
  have hy₀ := v.ne_zero_iff.mp <| (zero_lt_one.trans hy).ne'
  refine ⟨y⁻¹, inv_ne_zero hy₀, ?_⟩
  rw [map_inv₀]
  exact (inv_lt_one₀ <| v.pos hy₀).mpr hy

end LinearOrderedSemifield

end nontrivial

end AbsoluteValue

/-- A function `f` is an absolute value if it is nonnegative, zero only at 0, additive, and
multiplicative.

See also the type `AbsoluteValue` which represents a bundled version of absolute values.
-/
/-
**IsAbsoluteValue** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{S : Type u_5} → [Semiring S] → [PartialOrder S] → {R : Type u_6} → [Semir
ing R] → (R → S) → Prop
参数：R → S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is an absolute value if it is nonnegative, zero only at 0, additi
ve, and
multiplicative.

See also the type `AbsoluteValue` which represents a bundled version of absolute
 values.
-/
class IsAbsoluteValue {S} [Semiring S] [PartialOrder S] {R} [Semiring R] (f : R → S) : Prop where
  /-- The absolute value is nonnegative -/
  abv_nonneg' : ∀ x, 0 ≤ f x
  /-- The absolute value is positive definitive -/
  abv_eq_zero' : ∀ {x}, f x = 0 ↔ x = 0
  /-- The absolute value satisfies the triangle inequality -/
  abv_add' : ∀ x y, f (x + y) ≤ f x + f y
  /-- The absolute value is multiplicative -/
  abv_mul' : ∀ x y, f (x * y) = f x * f y

namespace IsAbsoluteValue

section OrderedSemiring

variable {S : Type*} [Semiring S] [PartialOrder S]
variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]

/-
**IsAbsoluteValue.abv_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_nonneg (x) : 0 <= abv x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAbsoluteValue.abv_nonneg'`：∀ {S : Type u_5} {inst : Semiring S} {inst_
1 : PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : I
sAbsoluteValue f]…
-/
lemma abv_nonneg (x) : 0 ≤ abv x := abv_nonneg' x

open Lean Meta Mathlib Meta Positivity Qq in
/-- The `positivity` extension which identifies expressions of the form `abv a`.
For performance reasons, we only attempt to apply this when `abv` is a variable.
If it is an explicit function, e.g. `|_|` or `‖_‖`, another extension should apply. -/
@[positivity _]
meta def Mathlib.Meta.Positivity.evalAbv : PositivityExt where eval {_ _α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  let (.app f a) ← whnfR e | throwError "not abv ·"
  if !f.getAppFn.isFVar then
    throwError "abv: function is not a variable"
  let pa' ← mkAppM ``abv_nonneg #[f, a]
  pure (.nonnegative pa')

/-
**IsAbsoluteValue.abv_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_eq_zero {x} : abv x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAbsoluteValue.abv_eq_zero'`：∀ {S : Type u_5} {inst : Semiring S} {inst
_1 : PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : 
IsAbsoluteValue f]…
-/
lemma abv_eq_zero {x} : abv x = 0 ↔ x = 0 := abv_eq_zero'
/-
**IsAbsoluteValue.abv_add** 是 Mathlib 中的一个引理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_add (x y) : abv (x + y) <= abv x + abv y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAbsoluteValue.abv_add'`：∀ {S : Type u_5} {inst : Semiring S} {inst_1 :
 PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : IsAb
soluteValue f]…
-/
lemma abv_add (x y) : abv (x + y) ≤ abv x + abv y := abv_add' x y
/-
**IsAbsoluteValue.abv_mul** 是 Mathlib 中的一个引理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_mul (x y) : abv (x * y) = abv x * abv y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAbsoluteValue.abv_mul'`：∀ {S : Type u_5} {inst : Semiring S} {inst_1 :
 PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : IsAb
soluteValue f]…
-/
lemma abv_mul (x y) : abv (x * y) = abv x * abv y := abv_mul' x y

/-- A bundled absolute value is an absolute value. -/
/-
**IsAbsoluteValue._root_.AbsoluteValue.isAbsoluteValue** 是 Mathlib 中的一个实例，位于命名空间
 `IsAbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled absolute value is an absolute value.
-/
instance _root_.AbsoluteValue.isAbsoluteValue (abv : AbsoluteValue R S) : IsAbsoluteValue abv where
  abv_nonneg' := abv.nonneg
  abv_eq_zero' := abv.eq_zero
  abv_add' := abv.add_le
  abv_mul' := abv.map_mul

/-- Convert an unbundled `IsAbsoluteValue` to a bundled `AbsoluteValue`. -/
@[simps]
/-
**IsAbsoluteValue.toAbsoluteValue** 是 Mathlib 中的一个定义，位于命名空间 `IsAbsoluteValue`。
形式化陈述：toAbsoluteValue : AbsoluteValue R S where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsAbsoluteValue.abv_mul'`：∀ {S : Type u_5} {inst : Semiring S} {inst_1 :
 PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : IsAb
soluteValue f]…
· 使用定理 `IsAbsoluteValue.abv_nonneg'`：∀ {S : Type u_5} {inst : Semiring S} {inst_
1 : PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : I
sAbsoluteValue f]…
· 使用定理 `IsAbsoluteValue.abv_eq_zero'`：∀ {S : Type u_5} {inst : Semiring S} {inst
_1 : PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : 
IsAbsoluteValue f]…
· 使用定理 `IsAbsoluteValue.abv_add'`：∀ {S : Type u_5} {inst : Semiring S} {inst_1 :
 PartialOrder S} {R : Type u_6} {inst_2 : Semiring R} {f : R → S}   [self : IsAb
soluteValue f]…

--- 原说明 ---
Convert an unbundled `IsAbsoluteValue` to a bundled `AbsoluteValue`.
-/
def toAbsoluteValue : AbsoluteValue R S where
  toFun := abv
  add_le' := abv_add'
  eq_zero' _ := abv_eq_zero'
  nonneg' := abv_nonneg'
  map_mul' := abv_mul'
/-
**IsAbsoluteValue.abv_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_zero : abv 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
-/
theorem abv_zero : abv 0 = 0 :=
  (toAbsoluteValue abv).map_zero
/-
**IsAbsoluteValue.abv_pos** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_pos {a : R} : 0 < abv a ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.pos_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, 0 <…
-/
theorem abv_pos {a : R} : 0 < abv a ↔ a ≠ 0 :=
  (toAbsoluteValue abv).pos_iff

end OrderedSemiring

section LinearOrderedRing

variable {S : Type*} [Ring S] [LinearOrder S] [IsStrictOrderedRing S]

/-
**IsAbsoluteValue.abs_isAbsoluteValue** 是 Mathlib 中的一个实例，位于命名空间 `IsAbsoluteValue
`。
形式化陈述：abs_isAbsoluteValue : IsAbsoluteValue (abs : S -> S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.isAbsoluteValue`：∀ {S : Type u_5} [inst : Semiring S] [ins
t_1 : PartialOrder S] {R : Type u_6} [inst_2 : Semiring R]   (abv : AbsoluteValu
e R S), IsAbsoluteV…
-/
instance abs_isAbsoluteValue : IsAbsoluteValue (abs : S → S) :=
  AbsoluteValue.abs.isAbsoluteValue

end LinearOrderedRing

section OrderedRing

variable {S : Type*} [Ring S] [PartialOrder S]

section Semiring

variable {R : Type*} [Semiring R] (abv : R → S) [IsAbsoluteValue abv]
variable [IsDomain S]

/-
**IsAbsoluteValue.abv_one** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_one [Nontrivial R] : abv 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_one`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
-/
theorem abv_one [Nontrivial R] : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one

/-- `abv` as a `MonoidWithZeroHom`. -/
/-
**IsAbsoluteValue.abvHom** 是 Mathlib 中的一个定义，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abvHom [Nontrivial R] : R ->*₀ S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`abv` as a `MonoidWithZeroHom`.
-/
def abvHom [Nontrivial R] : R →*₀ S :=
  (toAbsoluteValue abv).toMonoidWithZeroHom
/-
**IsAbsoluteValue.abv_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_pow [Nontrivial R] (abv : R -> S) [IsAbsoluteValue abv] (a : R) (n : N
at) : abv (a ^ n) = abv a ^ n
参数：abv : R -> S；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_pow`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
-/
theorem abv_pow [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv] (a : R) (n : ℕ) :
    abv (a ^ n) = abv a ^ n :=
  (toAbsoluteValue abv).map_pow a n

end Semiring

section Ring

variable {R : Type*} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

/-
**IsAbsoluteValue.abv_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_sub_le (a b c : R) : abv (a - c) <= abv (a - b) + abv (b - c)
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用引理 `IsAbsoluteValue.abv_add`：abv_add (x y) : abv (x + y) <= abv x + abv y
-/
theorem abv_sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assoc] using abv_add abv (a - b) (b - c)
/-
**IsAbsoluteValue.sub_abv_le_abv_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`
。
形式化陈述：sub_abv_le_abv_sub [IsOrderedRing S] (a b : R) : abv a - abv b <= abv (a -
 b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.le_sub`：∀ {R : Type u_5} {S : Type u_6} [inst : Ring R] [i
nst_1 : Ring S] [inst_2 : PartialOrder S] [IsOrderedRing S]   (abv : AbsoluteVal
ue R S) (a…
-/
theorem sub_abv_le_abv_sub [IsOrderedRing S] (a b : R) : abv a - abv b ≤ abv (a - b) :=
  (toAbsoluteValue abv).le_sub a b

end Ring

end OrderedRing

section OrderedCommRing
variable [CommRing S] [PartialOrder S] [IsOrderedRing S] [NoZeroDivisors S] [Ring R]
  (abv : R → S) [IsAbsoluteValue abv]

/-
**IsAbsoluteValue.abv_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_neg (a : R) : abv (-a) = abv a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_neg`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
-/
theorem abv_neg (a : R) : abv (-a) = abv a :=
  (toAbsoluteValue abv).map_neg a
/-
**IsAbsoluteValue.abv_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_sub (a b : R) : abv (a - b) = abv (b - a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_sub`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
-/
theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) :=
  (toAbsoluteValue abv).map_sub a b

end OrderedCommRing

section LinearOrderedCommRing

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

section Ring

variable {R : Type*} [Ring R] (abv : R → S) [IsAbsoluteValue abv]

/-
**IsAbsoluteValue.abs_abv_sub_le_abv_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteVa
lue`。
形式化陈述：abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) <= abv (a - b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.abs_abv_sub_le_abv_sub`：abs_abv_sub_le_abv_sub (a b : R) :
 abs (abv a - abv b) <= abv (a - b)
-/
theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  (toAbsoluteValue abv).abs_abv_sub_le_abv_sub a b

end Ring

end LinearOrderedCommRing

section IsCancelMulZero

variable {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S] [IsCancelMulZero S]

section Semiring

variable {R : Type*} [Semiring R] [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv]

omit [IsOrderedRing S] in
/-
**IsAbsoluteValue.abv_one'** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_one' : abv 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.map_one_of_isLeftRegular`：map_one_of_isLeftRegular (h : Is
LeftRegular (abv 1)) : abv 1 = 1
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
· 使用定理 `AbsoluteValue.ne_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, x ≠…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem abv_one' : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one_of_isLeftRegular <|
    (IsRegular.of_ne_zero <| (toAbsoluteValue abv).ne_zero one_ne_zero).left

/-- An absolute value as a monoid with zero homomorphism, assuming the target is a semifield. -/
/-
**IsAbsoluteValue.abvHom'** 是 Mathlib 中的一个定义，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abvHom' : R ->*₀ S where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsAbsoluteValue.abv_zero`：abv_zero : abv 0 = 0
· 使用定理 `IsAbsoluteValue.abv_one'`：abv_one' : abv 1 = 1
· 使用引理 `IsAbsoluteValue.abv_mul`：abv_mul (x y) : abv (x * y) = abv x * abv y

--- 原说明 ---
An absolute value as a monoid with zero homomorphism, assuming the target is a s
emifield.
-/
def abvHom' : R →*₀ S where
  toFun := abv; map_zero' := abv_zero abv; map_one' := abv_one' abv; map_mul' := abv_mul abv

end Semiring

end IsCancelMulZero

section LinearOrderedSemifield

variable {S : Type*} [Semifield S] [LinearOrder S]

section DivisionSemiring

variable {R : Type*} [DivisionSemiring R] (abv : R → S) [IsAbsoluteValue abv]

/-
**IsAbsoluteValue.abv_inv** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
  map_inv₀ (abvHom' abv) a
/-
**IsAbsoluteValue.abv_div** 是 Mathlib 中的一个定理，位于命名空间 `IsAbsoluteValue`。
形式化陈述：abv_div (a b : R) : abv (a / b) = abv a / abv b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem abv_div (a b : R) : abv (a / b) = abv a / abv b :=
  map_div₀ (abvHom' abv) a b

end DivisionSemiring

end LinearOrderedSemifield

end IsAbsoluteValue

