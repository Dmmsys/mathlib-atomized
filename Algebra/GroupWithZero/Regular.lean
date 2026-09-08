/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Tactic.Push

/-!
# Results about `IsRegular` and `0`
-/

public section

variable {R}

section MulZeroClass
variable [MulZeroClass R] {a b : R}

/-- The element `0` is left-regular if and only if `R` is trivial. -/
/-
**IsLeftRegular.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R
参数：h : IsLeftRegular (0 : R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The element `0` is left-regular if and only if `R` is trivial.
-/
theorem IsLeftRegular.subsingleton (h : IsLeftRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (zero_mul a) (zero_mul b).symm⟩

/-- The element `0` is right-regular if and only if `R` is trivial. -/
/-
**IsRightRegular.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R
参数：h : IsRightRegular (0 : R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The element `0` is right-regular if and only if `R` is trivial.
-/
theorem IsRightRegular.subsingleton (h : IsRightRegular (0 : R)) : Subsingleton R :=
  ⟨fun a b => h <| Eq.trans (mul_zero a) (mul_zero b).symm⟩

/-- The element `0` is regular if and only if `R` is trivial. -/
/-
**IsRegular.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R
参数：h : IsRegular (0 : R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.subsingleton`：IsLeftRegular.subsingleton (h : IsLeftRegula
r (0 : R)) : Subsingleton R
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c

--- 原说明 ---
The element `0` is regular if and only if `R` is trivial.
-/
theorem IsRegular.subsingleton (h : IsRegular (0 : R)) : Subsingleton R :=
  h.left.subsingleton

/-- The element `0` is left-regular if and only if `R` is trivial. -/
/-
**isLeftRegular_zero_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeftRegular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton
 R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.subsingleton`：IsLeftRegular.subsingleton (h : IsLeftRegula
r (0 : R)) : Subsingleton R
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
The element `0` is left-regular if and only if `R` is trivial.
-/
theorem isLeftRegular_zero_iff_subsingleton : IsLeftRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- In a non-trivial `MulZeroClass`, the `0` element is not left-regular. -/
/-
**not_isLeftRegular_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isLeftRegular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `isLeftRegular_zero_iff_subsingleton`：isLeftRegular_zero_iff_subsingleton
 : IsLeftRegular (0 : R) ↔ Subsingleton R
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In a non-trivial `MulZeroClass`, the `0` element is not left-regular.
-/
theorem not_isLeftRegular_zero_iff : ¬IsLeftRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isLeftRegular_zero_iff_subsingleton, subsingleton_iff]
  push Not
  exact Iff.rfl

/-- The element `0` is right-regular if and only if `R` is trivial. -/
/-
**isRightRegular_zero_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsinglet
on R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightRegular.subsingleton`：IsRightRegular.subsingleton (h : IsRightReg
ular (0 : R)) : Subsingleton R
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
The element `0` is right-regular if and only if `R` is trivial.
-/
theorem isRightRegular_zero_iff_subsingleton : IsRightRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.subsingleton, fun H a b _ => @Subsingleton.elim _ H a b⟩

/-- In a non-trivial `MulZeroClass`, the `0` element is not right-regular. -/
/-
**not_isRightRegular_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isRightRegular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nontrivial_iff`：nontrivial_iff : Nontrivial α ↔ exists x y : α, x != y
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `isRightRegular_zero_iff_subsingleton`：isRightRegular_zero_iff_subsinglet
on : IsRightRegular (0 : R) ↔ Subsingleton R
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In a non-trivial `MulZeroClass`, the `0` element is not right-regular.
-/
theorem not_isRightRegular_zero_iff : ¬IsRightRegular (0 : R) ↔ Nontrivial R := by
  rw [nontrivial_iff, not_iff_comm, isRightRegular_zero_iff_subsingleton, subsingleton_iff]
  push Not
  exact Iff.rfl

/-- The element `0` is regular if and only if `R` is trivial. -/
/-
**isRegular_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.subsingleton`：IsLeftRegular.subsingleton (h : IsLeftRegula
r (0 : R)) : Subsingleton R
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLeftRegular_zero_iff_subsingleton`：isLeftRegular_zero_iff_subsingleton
 : IsLeftRegular (0 : R) ↔ Subsingleton R
· 使用定理 `isRightRegular_zero_iff_subsingleton`：isRightRegular_zero_iff_subsinglet
on : IsRightRegular (0 : R) ↔ Subsingleton R

--- 原说明 ---
The element `0` is regular if and only if `R` is trivial.
-/
theorem isRegular_iff_subsingleton : IsRegular (0 : R) ↔ Subsingleton R :=
  ⟨fun h => h.left.subsingleton, fun h =>
    ⟨isLeftRegular_zero_iff_subsingleton.mpr h, isRightRegular_zero_iff_subsingleton.mpr h⟩⟩

/-- A left-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
/-
**IsLeftRegular.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a != 0
参数：la : IsLeftRegular a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A left-regular element of a `Nontrivial` `MulZeroClass` is non-zero.
-/
theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la ?_)
  simp

/-- A right-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
/-
**IsRightRegular.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a != 0
参数：ra : IsRightRegular a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A right-regular element of a `Nontrivial` `MulZeroClass` is non-zero.
-/
theorem IsRightRegular.ne_zero [Nontrivial R] (ra : IsRightRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (ra ?_)
  simp

/-- A regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
/-
**IsRegular.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a != 0
参数：la : IsRegular a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.ne_zero`：IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeft
Regular a) : a != 0
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c

--- 原说明 ---
A regular element of a `Nontrivial` `MulZeroClass` is non-zero.
-/
theorem IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) : a ≠ 0 :=
  la.left.ne_zero

/-- In a non-trivial ring, the element `0` is not left-regular -- with typeclasses. -/
/-
**not_isLeftRegular_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isLeftRegular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isLeftRegular_zero_iff`：not_isLeftRegular_zero_iff : ¬IsLeftRegular 
(0 : R) ↔ Nontrivial R

--- 原说明 ---
In a non-trivial ring, the element `0` is not left-regular -- with typeclasses.
-/
theorem not_isLeftRegular_zero [nR : Nontrivial R] : ¬IsLeftRegular (0 : R) :=
  not_isLeftRegular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not right-regular -- with typeclasses. -/
/-
**not_isRightRegular_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isRightRegular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isRightRegular_zero_iff`：not_isRightRegular_zero_iff : ¬IsRightRegul
ar (0 : R) ↔ Nontrivial R

--- 原说明 ---
In a non-trivial ring, the element `0` is not right-regular -- with typeclasses.
-/
theorem not_isRightRegular_zero [nR : Nontrivial R] : ¬IsRightRegular (0 : R) :=
  not_isRightRegular_zero_iff.mpr nR

/-- In a non-trivial ring, the element `0` is not regular -- with typeclasses. -/
/-
**not_isRegular_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isRegular_zero [Nontrivial R] : ¬IsRegular (0 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.ne_zero`：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) :
 a != 0

--- 原说明 ---
In a non-trivial ring, the element `0` is not regular -- with typeclasses.
-/
theorem not_isRegular_zero [Nontrivial R] : ¬IsRegular (0 : R) := fun h => IsRegular.ne_zero h rfl
/-
**IsLeftRegular.mul_left_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLeftRegular`。
形式化陈述：∀ {R : Type u_1} [inst : MulZeroClass R] {a b : R}, IsLeftRegular b → (b *
 a = 0 ↔ a = 0)
参数：b * a = 0 ↔ a = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
@[simp] lemma IsLeftRegular.mul_left_eq_zero_iff (hb : IsLeftRegular b) : b * a = 0 ↔ a = 0 := by
  conv_lhs => rw [← mul_zero b]
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha]⟩
/-
**IsRightRegular.mul_right_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRightRegular
`。
形式化陈述：∀ {R : Type u_1} [inst : MulZeroClass R] {a b : R}, IsRightRegular b → (a 
* b = 0 ↔ a = 0)
参数：a * b = 0 ↔ a = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
@[simp] lemma IsRightRegular.mul_right_eq_zero_iff (hb : IsRightRegular b) : a * b = 0 ↔ a = 0 := by
  conv_lhs => rw [← zero_mul b]
  exact ⟨fun h ↦ hb h, fun ha ↦ by rw [ha]⟩

end MulZeroClass

section CancelMonoidWithZero
variable [MulZeroClass R] [IsCancelMulZero R] {a : R}

/-- Non-zero elements of an integral domain are regular. -/
/-
**IsRegular.of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
参数：a0 : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀

--- 原说明 ---
Non-zero elements of an integral domain are regular.
-/
theorem IsRegular.of_ne_zero (a0 : a ≠ 0) : IsRegular a :=
  ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero := IsRegular.of_ne_zero

/-- In a non-trivial integral domain, an element is regular iff it is non-zero. -/
/-
**isRegular_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.ne_zero`：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) :
 a != 0
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a

--- 原说明 ---
In a non-trivial integral domain, an element is regular iff it is non-zero.
-/
theorem isRegular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a ≠ 0 :=
  ⟨IsRegular.ne_zero, .of_ne_zero⟩

end CancelMonoidWithZero

