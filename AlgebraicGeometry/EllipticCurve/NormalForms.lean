/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Algebra.CharP.Defs

/-!

# Some normal forms of elliptic curves

This file defines some normal forms of Weierstrass equations of elliptic curves.

## Main definitions and results

The following normal forms are in [silverman2009], section III.1, page 42.

- `WeierstrassCurve.IsCharNeTwoNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₄X + a₆`. It is the normal form of characteristic ≠ 2.

  If 2 is invertible in the ring (for example, if it is a field of characteristic ≠ 2),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharNeTwoNF`).
  See also `WeierstrassCurve.toCharNeTwoNF` and `WeierstrassCurve.toCharNeTwoNF_spec`.

The following normal forms are in [silverman2009], Appendix A, Proposition 1.1.

- `WeierstrassCurve.IsShortNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₄X + a₆`. It is the normal form of characteristic ≠ 2 or 3, and
  also the normal form of characteristic = 3 and j = 0.

  If 2 and 3 are invertible in the ring (for example, if it is a field of characteristic ≠ 2 or 3),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isShortNF`).
  See also `WeierstrassCurve.toShortNF` and `WeierstrassCurve.toShortNF_spec`.

  If the ring is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toShortNFOfCharThree`
  and `WeierstrassCurve.toShortNFOfCharThree_spec`).

- `WeierstrassCurve.IsCharThreeJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₆`. It is the normal form of characteristic = 3 and j ≠ 0.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharThreeNF`
  and `WeierstrassCurve.toCharThreeNF_spec_of_b₂_ne_zero`).

- `WeierstrassCurve.IsCharThreeNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² = X³ + a₂X² + a₆` or `Y² = X³ + a₄X + a₆`.
  It is the normal form of characteristic = 3.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharThreeNF`).
  See also `WeierstrassCurve.toCharThreeNF` and `WeierstrassCurve.toCharThreeNF_spec`.

- `WeierstrassCurve.IsCharTwoJEqZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2 and j = 0.

  If the ring is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJEqZeroNF`
  and `WeierstrassCurve.toCharTwoJEqZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + XY = X³ + a₂X² + a₆`. It is the normal form of characteristic = 2 and j ≠ 0.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJNeZeroNF`
  and `WeierstrassCurve.toCharTwoJNeZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² + XY = X³ + a₂X² + a₆` or
  `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharTwoNF`).
  See also `WeierstrassCurve.toCharTwoNF` and `WeierstrassCurve.toCharTwoNF_spec`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, normal form

-/

@[expose] public section

variable {R : Type*} [CommRing R] {F : Type*} [Field F] (W : WeierstrassCurve R)

namespace WeierstrassCurve

/-! ## Normal forms of characteristic ≠ 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its `a₁, a₃ = 0`.
In other words it is `Y² = X³ + a₂X² + a₄X + a₆`. -/
@[mk_iff]
/-
**WeierstrassCurve.IsCharNeTwoNF** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurve`。
形式化陈述：{R : Type u_1} → [CommRing R] → WeierstrassCurve R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its `a₁, a₃ = 0
`.
In other words it is `Y² = X³ + a₂X² + a₄X + a₆`.
-/
class IsCharNeTwoNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsCharNeTwoNF]

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₁_of_isCharNeTwoNF : W.a₁ = 0 := IsCharNeTwoNF.a₁

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₃_of_isCharNeTwoNF : W.a₃ = 0 := IsCharNeTwoNF.a₃

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₂_of_isCharNeTwoNF : W.b₂ = 4 * W.a₂ := by
  rw [b₂, a₁_of_isCharNeTwoNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₄_of_isCharNeTwoNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄, a₃_of_isCharNeTwoNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₆_of_isCharNeTwoNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆, a₃_of_isCharNeTwoNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isCharNeTwoNF : W.b₈ = 4 * W.a₂ * W.a₆ - W.a₄ ^ 2 := by
  rw [b₈, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring1

@[simp]
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isCharNeTwoNF : W.c₄ = 16 * W.a₂ ^ 2 - 48 * W.a₄ := by
  rw [c₄, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF]
  ring1

@[simp]
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isCharNeTwoNF : W.c₆ = -64 * W.a₂ ^ 3 + 288 * W.a₂ * W.a₄ - 864 * W.a₆ := by
  rw [c₆, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF, b₆_of_isCharNeTwoNF]
  ring1

@[simp]
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isCharNeTwoNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3
    - 432 * W.a₆ ^ 2 + 288 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Δ, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF, b₆_of_isCharNeTwoNF, b₈_of_isCharNeTwoNF]
  ring1

end Quantity

section VariableChange

variable [Invertible (2 : R)]

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2, provided that 2 is invertible in the ring. -/
@[simps]
/-
**WeierstrassCurve.toCharNeTwoNF** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：toCharNeTwoNF : VariableChange R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2, provided that 2 is invertible in the ring.
-/
def toCharNeTwoNF : VariableChange R := ⟨1, 0, ⅟2 * -W.a₁, ⅟2 * -W.a₃⟩
/-
**WeierstrassCurve.toCharNeTwoNF_spec** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurv
e`。
形式化陈述：toCharNeTwoNF_spec : (W.toCharNeTwoNF • W).IsCharNeTwoNF
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WeierstrassCurve.toCharNeTwoNF_u`：∀ {R : Type u_1} [inst : CommRing R] (
W : WeierstrassCurve R) [inst_1 : Invertible 2], W.toCharNeTwoNF.u = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `WeierstrassCurve.toCharNeTwoNF_s`：∀ {R : Type u_1} [inst : CommRing R] (
W : WeierstrassCurve R) [inst_1 : Invertible 2], W.toCharNeTwoNF.s = ⅟2 * -W.a₁
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_invOf_cancel_left'`：mul_invOf_cancel_left' {_ : Invertible a} : a * 
(⅟a * b) = b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `WeierstrassCurve.toCharNeTwoNF_r`：∀ {R : Type u_1} [inst : CommRing R] (
W : WeierstrassCurve R) [inst_1 : Invertible 2], W.toCharNeTwoNF.r = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `WeierstrassCurve.toCharNeTwoNF_t`：∀ {R : Type u_1} [inst : CommRing R] (
W : WeierstrassCurve R) [inst_1 : Invertible 2], W.toCharNeTwoNF.t = ⅟2 * -W.a₃
-/
instance toCharNeTwoNF_spec : (W.toCharNeTwoNF • W).IsCharNeTwoNF := by
  constructor <;> simp [variableChange_a₁, variableChange_a₃]
/-
**WeierstrassCurve.exists_variableChange_isCharNeTwoNF** 是 Mathlib 中的一个定理，位于命名空间
 `WeierstrassCurve`。
形式化陈述：exists_variableChange_isCharNeTwoNF : exists C : VariableChange R, (C • W)
.IsCharNeTwoNF
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem exists_variableChange_isCharNeTwoNF : ∃ C : VariableChange R, (C • W).IsCharNeTwoNF :=
  ⟨_, W.toCharNeTwoNF_spec⟩

end VariableChange

/-! ## Short normal form -/

/-- A `WeierstrassCurve` is in short normal form, if its `a₁, a₂, a₃ = 0`.
In other words it is `Y² = X³ + a₄X + a₆`.

This is the normal form of characteristic ≠ 2 or 3, and
also the normal form of characteristic = 3 and j = 0. -/
@[mk_iff]
/-
**WeierstrassCurve.IsShortNF** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCurve`。
形式化陈述：{R : Type u_1} → [CommRing R] → WeierstrassCurve R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeierstrassCurve` is in short normal form, if its `a₁, a₂, a₃ = 0`.
In other words it is `Y² = X³ + a₄X + a₆`.

This is the normal form of characteristic ≠ 2 or 3, and
also the normal form of characteristic = 3 and j = 0.
-/
class IsShortNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsShortNF]

/-
**WeierstrassCurve.isCharNeTwoNF_of_isShortNF** 是 Mathlib 中的一个实例，位于命名空间 `Weierst
rassCurve`。
形式化陈述：isCharNeTwoNF_of_isShortNF : W.IsCharNeTwoNF
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.IsShortNF.a₁`：∀ {R : Type u_1} {inst : CommRing R} {W :
 WeierstrassCurve R} [self : W.IsShortNF], W.a₁ = 0
· 使用定理 `WeierstrassCurve.IsShortNF.a₃`：∀ {R : Type u_1} {inst : CommRing R} {W :
 WeierstrassCurve R} [self : W.IsShortNF], W.a₃ = 0
-/
instance isCharNeTwoNF_of_isShortNF : W.IsCharNeTwoNF := ⟨IsShortNF.a₁, IsShortNF.a₃⟩
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₁_of_isShortNF : W.a₁ = 0 := IsShortNF.a₁

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₂_of_isShortNF : W.a₂ = 0 := IsShortNF.a₂
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₃_of_isShortNF : W.a₃ = 0 := IsShortNF.a₃
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₂_of_isShortNF : W.b₂ = 0 := by
  simp
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₄_of_isShortNF : W.b₄ = 2 * W.a₄ := W.b₄_of_isCharNeTwoNF
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₆_of_isShortNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isShortNF : W.b₈ = -W.a₄ ^ 2 := by
  simp
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isShortNF : W.c₄ = -48 * W.a₄ := by
  simp
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isShortNF : W.c₆ = -864 * W.a₆ := by
  simp
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isShortNF : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  rw [Δ_of_isCharNeTwoNF, a₂_of_isShortNF]
  ring1

variable [CharP R 3]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₄_of_isShortNF_of_char_three : W.b₄ = -W.a₄ := by
  rw [b₄_of_isShortNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₆_of_isShortNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isShortNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isShortNF_of_char_three : W.c₄ = 0 := by
  rw [c₄_of_isShortNF]
  linear_combination -16 * W.a₄ * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isShortNF_of_char_three : W.c₆ = 0 := by
  rw [c₆_of_isShortNF]
  linear_combination -288 * W.a₆ * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isShortNF_of_char_three : W.Δ = -W.a₄ ^ 3 := by
  rw [Δ_of_isShortNF]
  linear_combination (-21 * W.a₄ ^ 3 - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]
/-
**WeierstrassCurve.j_of_isShortNF** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
形式化陈述：j_of_isShortNF : W.j = 6912 * W.a₄ ^ 3 / (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
· 使用定理 `WeierstrassCurve.c₄_of_isShortNF`：c₄_of_isShortNF : W.c₄ = -48 * W.a₄
· 使用定理 `WeierstrassCurve.Δ_of_isShortNF`：Δ_of_isShortNF : W.Δ = -16 * (4 * W.a₄ 
^ 3 + 27 * W.a₆ ^ 2)
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 54 条，此处仅展示前 30 条）
-/
theorem j_of_isShortNF : W.j = 6912 * W.a₄ ^ 3 / (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isShortNF] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isShortNF, Δ_of_isShortNF, div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

@[simp]
/-
**WeierstrassCurve.j_of_isShortNF_of_char_three** 是 Mathlib 中的一个定理，位于命名空间 `Weier
strassCurve`。
形式化陈述：j_of_isShortNF_of_char_three [CharP F 3] : W.j = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `WeierstrassCurve.c₄_of_isShortNF_of_char_three`：c₄_of_isShortNF_of_char_
three : W.c₄ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `WeierstrassCurve.Δ_of_isCharNeTwoNF`：Δ_of_isCharNeTwoNF : W.Δ = -64 * W.
a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3 - 432 * W.a₆ ^ 2 + 288 
* W.a₂ * W.a₄ * W.a₆
· 使用定理 `WeierstrassCurve.a₂_of_isShortNF`：a₂_of_isShortNF : W.a₂ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem j_of_isShortNF_of_char_three [CharP F 3] : W.j = 0 := by
  rw [j, c₄_of_isShortNF_of_char_three]; simp

end Quantity

section VariableChange

variable [Invertible (2 : R)] [Invertible (3 : R)]

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a short normal form, provided that 2 and 3 are invertible in the ring.
It is the composition of an explicit change of variables with `WeierstrassCurve.toCharNeTwoNF`. -/
/-
**WeierstrassCurve.toShortNF** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：toShortNF : VariableChange R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is an explicit change of variables of a `WeierstrassCurve` to
a short normal form, provided that 2 and 3 are invertible in the ring.
It is the composition of an explicit change of variables with `WeierstrassCurve.
toCharNeTwoNF`.
-/
def toShortNF : VariableChange R :=
  ⟨1, ⅟3 * -(W.toCharNeTwoNF • W).a₂, 0, 0⟩ * W.toCharNeTwoNF
/-
**WeierstrassCurve.toShortNF_spec** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`。
形式化陈述：toShortNF_spec : (W.toShortNF • W).IsShortNF
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.toShortNF.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (W
 : WeierstrassCurve R) [inst_1 : Invertible 2] [inst_2 : Invertible 3],   W.toSh
ortNF = { u := 1, r :…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WeierstrassCurve.toCharNeTwoNF_u`：∀ {R : Type u_1} [inst : CommRing R] (
W : WeierstrassCurve R) [inst_1 : Invertible 2], W.toCharNeTwoNF.u = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `WeierstrassCurve.toCharNeTwoNF_s`：∀ {R : Type u_1} [inst : CommRing R] (
W : WeierstrassCurve R) [inst_1 : Invertible 2], W.toCharNeTwoNF.s = ⅟2 * -W.a₁
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `WeierstrassCurve.toCharNeTwoNF_r`：∀ {R : Type u_1} [inst : CommRing R] (
W : WeierstrassCurve R) [inst_1 : Invertible 2], W.toCharNeTwoNF.r = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `WeierstrassCurve.a₁_of_isCharNeTwoNF`：a₁_of_isCharNeTwoNF : W.a₁ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_invOf_cancel_left'`：mul_invOf_cancel_left' {_ : Invertible a} : a * 
(⅟a * b) = b
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 31 条，此处仅展示前 30 条）
-/
instance toShortNF_spec : (W.toShortNF • W).IsShortNF := by
  rw [toShortNF, mul_smul]
  constructor <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃]
/-
**WeierstrassCurve.exists_variableChange_isShortNF** 是 Mathlib 中的一个定理，位于命名空间 `We
ierstrassCurve`。
形式化陈述：exists_variableChange_isShortNF : exists C : VariableChange R, (C • W).IsS
hortNF
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem exists_variableChange_isShortNF : ∃ C : VariableChange R, (C • W).IsShortNF :=
  ⟨_, W.toShortNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 3 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3 and j ≠ 0, if its
`a₁, a₃, a₄ = 0`. In other words it is `Y² = X³ + a₂X² + a₆`. -/
@[mk_iff]
/-
**WeierstrassCurve.IsCharThreeJNeZeroNF** 是 Mathlib 中的一个归纳类型，位于命名空间 `Weierstrass
Curve`。
形式化陈述：{R : Type u_1} → [CommRing R] → WeierstrassCurve R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeierstrassCurve` is in normal form of characteristic = 3 and j ≠ 0, if its
`a₁, a₃, a₄ = 0`. In other words it is `Y² = X³ + a₂X² + a₆`.
-/
class IsCharThreeJNeZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharThreeJNeZeroNF]

/-
**WeierstrassCurve.isCharNeTwoNF_of_isCharThreeJNeZeroNF** 是 Mathlib 中的一个实例，位于命名
空间 `WeierstrassCurve`。
形式化陈述：isCharNeTwoNF_of_isCharThreeJNeZeroNF : W.IsCharNeTwoNF
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.IsCharThreeJNeZeroNF.a₁`：∀ {R : Type u_1} {inst : CommR
ing R} {W : WeierstrassCurve R} [self : W.IsCharThreeJNeZeroNF], W.a₁ = 0
· 使用定理 `WeierstrassCurve.IsCharThreeJNeZeroNF.a₃`：∀ {R : Type u_1} {inst : CommR
ing R} {W : WeierstrassCurve R} [self : W.IsCharThreeJNeZeroNF], W.a₃ = 0
-/
instance isCharNeTwoNF_of_isCharThreeJNeZeroNF : W.IsCharNeTwoNF :=
  ⟨IsCharThreeJNeZeroNF.a₁, IsCharThreeJNeZeroNF.a₃⟩
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₁_of_isCharThreeJNeZeroNF : W.a₁ = 0 := IsCharThreeJNeZeroNF.a₁
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₃_of_isCharThreeJNeZeroNF : W.a₃ = 0 := IsCharThreeJNeZeroNF.a₃

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₄_of_isCharThreeJNeZeroNF : W.a₄ = 0 := IsCharThreeJNeZeroNF.a₄
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₂_of_isCharThreeJNeZeroNF : W.b₂ = 4 * W.a₂ := W.b₂_of_isCharNeTwoNF
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₄_of_isCharThreeJNeZeroNF : W.b₄ = 0 := by
  simp
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₆_of_isCharThreeJNeZeroNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isCharThreeJNeZeroNF : W.b₈ = 4 * W.a₂ * W.a₆ := by
  simp
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isCharThreeJNeZeroNF : W.c₄ = 16 * W.a₂ ^ 2 := by
  simp
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isCharThreeJNeZeroNF : W.c₆ = -64 * W.a₂ ^ 3 - 864 * W.a₆ := by
  simp
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isCharThreeJNeZeroNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ - 432 * W.a₆ ^ 2 := by
  simp

variable [CharP R 3]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₂_of_isCharThreeJNeZeroNF_of_char_three : W.b₂ = W.a₂ := by
  rw [b₂_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₆_of_isCharThreeJNeZeroNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isCharThreeJNeZeroNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isCharThreeJNeZeroNF_of_char_three : W.b₈ = W.a₂ * W.a₆ := by
  rw [b₈_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isCharThreeJNeZeroNF_of_char_three : W.c₄ = W.a₂ ^ 2 := by
  rw [c₄_of_isCharThreeJNeZeroNF]
  linear_combination 5 * W.a₂ ^ 2 * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isCharThreeJNeZeroNF_of_char_three : W.c₆ = -W.a₂ ^ 3 := by
  rw [c₆_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 - 288 * W.a₆) * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isCharThreeJNeZeroNF_of_char_three : W.Δ = -W.a₂ ^ 3 * W.a₆ := by
  rw [Δ_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharThreeJNeZeroNF] [CharP F 3]

@[simp]
/-
**WeierstrassCurve.j_of_isCharThreeJNeZeroNF_of_char_three** 是 Mathlib 中的一个定理，位于
命名空间 `WeierstrassCurve`。
形式化陈述：j_of_isCharThreeJNeZeroNF_of_char_three : W.j = -W.a₂ ^ 3 / W.a₆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
· 使用定理 `WeierstrassCurve.c₄_of_isCharThreeJNeZeroNF_of_char_three`：c₄_of_isCharT
hreeJNeZeroNF_of_char_three : W.c₄ = W.a₂ ^ 2
· 使用定理 `WeierstrassCurve.Δ_of_isCharThreeJNeZeroNF_of_char_three`：Δ_of_isCharThr
eeJNeZeroNF_of_char_three : W.Δ = -W.a₂ ^ 3 * W.a₆
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 45 条，此处仅展示前 30 条）
-/
theorem j_of_isCharThreeJNeZeroNF_of_char_three : W.j = -W.a₂ ^ 3 / W.a₆ := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharThreeJNeZeroNF_of_char_three, Δ_of_isCharThreeJNeZeroNF_of_char_three,
    div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1
/-
**WeierstrassCurve.j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three** 是 Mathlib 中
的一个定理，位于命名空间 `WeierstrassCurve`。
形式化陈述：j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three : W.j != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j_of_isCharThreeJNeZeroNF_of_char_three`：j_of_isCharThr
eeJNeZeroNF_of_char_three : W.j = -W.a₂ ^ 3 / W.a₆
· 使用定理 `div_ne_zero_iff`：div_ne_zero_iff : a / b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `WeierstrassCurve.Δ_of_isCharThreeJNeZeroNF_of_char_three`：Δ_of_isCharThr
eeJNeZeroNF_of_char_three : W.Δ = -W.a₂ ^ 3 * W.a₆
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
-/
theorem j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three : W.j ≠ 0 := by
  rw [j_of_isCharThreeJNeZeroNF_of_char_three, div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rwa [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff] at h

end Quantity

/-! ## Normal forms of characteristic = 3 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3, if it is
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`). -/
/-
**WeierstrassCurve.inductive** 是 Mathlib 中的一个类，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeierstrassCurve` is in normal form of characteristic = 3, if it is
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`).
-/
class inductive IsCharThreeNF : Prop
| of_j_ne_zero [W.IsCharThreeJNeZeroNF] : IsCharThreeNF
| of_j_eq_zero [W.IsShortNF] : IsCharThreeNF
/-
**WeierstrassCurve.isCharThreeNF_of_isCharThreeJNeZeroNF** 是 Mathlib 中的一个实例，位于命名
空间 `WeierstrassCurve`。
形式化陈述：isCharThreeNF_of_isCharThreeJNeZeroNF [W.IsCharThreeJNeZeroNF] : W.IsCharT
hreeNF
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCharThreeNF_of_isCharThreeJNeZeroNF [W.IsCharThreeJNeZeroNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_ne_zero
/-
**WeierstrassCurve.isCharThreeNF_of_isShortNF** 是 Mathlib 中的一个实例，位于命名空间 `Weierst
rassCurve`。
形式化陈述：isCharThreeNF_of_isShortNF [W.IsShortNF] : W.IsCharThreeNF
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCharThreeNF_of_isShortNF [W.IsShortNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_eq_zero
/-
**WeierstrassCurve.isCharNeTwoNF_of_isCharThreeNF** 是 Mathlib 中的一个实例，位于命名空间 `Wei
erstrassCurve`。
形式化陈述：isCharNeTwoNF_of_isCharThreeNF [W.IsCharThreeNF] : W.IsCharNeTwoNF
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCharNeTwoNF_of_isCharThreeNF [W.IsCharThreeNF] : W.IsCharNeTwoNF := by
  cases ‹W.IsCharThreeNF› <;> infer_instance

section VariableChange

variable [CharP R 3] [CharP F 3]

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 3,
there is an explicit change of variables of it to `Y² = X³ + a₄X + a₆`
(`WeierstrassCurve.IsShortNF`) if its j = 0.
This is in fact given by `WeierstrassCurve.toCharNeTwoNF`. -/
/-
**WeierstrassCurve.toShortNFOfCharThree** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCu
rve`。
形式化陈述：toShortNFOfCharThree : VariableChange R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `WeierstrassCurve` defined over a ring of characteristic = 3,
there is an explicit change of variables of it to `Y² = X³ + a₄X + a₆`
(`WeierstrassCurve.IsShortNF`) if its j = 0.
This is in fact given by `WeierstrassCurve.toCharNeTwoNF`.
-/
def toShortNFOfCharThree : VariableChange R :=
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.toCharNeTwoNF
/-
**WeierstrassCurve.toShortNFOfCharThree_a** 是 Mathlib 中的一个引理，位于命名空间 `Weierstrass
Curve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toShortNFOfCharThree_a₂ : (W.toShortNFOfCharThree • W).a₂ = W.b₂ := by
  simp_rw [toShortNFOfCharThree, toCharNeTwoNF, variableChange_a₂, inv_one, Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3
/-
**WeierstrassCurve.toShortNFOfCharThree_spec** 是 Mathlib 中的一个定理，位于命名空间 `Weierstr
assCurve`。
形式化陈述：toShortNFOfCharThree_spec (hb₂ : W.b₂ = 0) : (W.toShortNFOfCharThree • W).
IsShortNF
参数：hb₂ : W.b₂ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
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
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 41 条，此处仅展示前 30 条）
-/
theorem toShortNFOfCharThree_spec (hb₂ : W.b₂ = 0) : (W.toShortNFOfCharThree • W).IsShortNF := by
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  let : Invertible (2 : R) := ⟨2, h, h⟩
  have H := W.toCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.toShortNFOfCharThree_a₂, H.a₃⟩

variable (W : WeierstrassCurve F)

/-- For a `WeierstrassCurve` defined over a field of characteristic = 3,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharThreeNF`, that is,
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`).
It is the composition of an explicit change of variables with
`WeierstrassCurve.toShortNFOfCharThree`. -/
/-
**WeierstrassCurve.toCharThreeNF** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：toCharThreeNF : VariableChange F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `WeierstrassCurve` defined over a field of characteristic = 3,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharThreeN
F`, that is,
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`).
It is the composition of an explicit change of variables with
`WeierstrassCurve.toShortNFOfCharThree`.
-/
def toCharThreeNF : VariableChange F :=
  ⟨1, (W.toShortNFOfCharThree • W).a₄ /
    (W.toShortNFOfCharThree • W).a₂, 0, 0⟩ * W.toShortNFOfCharThree
/-
**WeierstrassCurve.toCharThreeNF_spec_of_b** 是 Mathlib 中的一个定理，位于命名空间 `Weierstras
sCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCharThreeNF_spec_of_b₂_ne_zero (hb₂ : W.b₂ ≠ 0) :
    (W.toCharThreeNF • W).IsCharThreeJNeZeroNF := by
  have h : (2 : F) * 2 = 1 := by linear_combination CharP.cast_eq_zero F 3
  let : Invertible (2 : F) := ⟨2, h, h⟩
  rw [toCharThreeNF, mul_smul]
  set W' := W.toShortNFOfCharThree • W
  have : W'.IsCharNeTwoNF := W.toCharNeTwoNF_spec
  constructor
  · simp [variableChange_a₁]
  · simp [variableChange_a₃]
  · have ha₂ : W'.a₂ ≠ 0 := W.toShortNFOfCharThree_a₂ ▸ hb₂
    simp [field, variableChange_a₄, -mul_eq_zero]
    linear_combination (W'.a₄ * W'.a₂ ^ 2 + W'.a₄ ^ 2) * CharP.cast_eq_zero F 3
/-
**WeierstrassCurve.toCharThreeNF_spec_of_b** 是 Mathlib 中的一个定理，位于命名空间 `Weierstras
sCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCharThreeNF_spec_of_b₂_eq_zero (hb₂ : W.b₂ = 0) : (W.toCharThreeNF • W).IsShortNF := by
  rw [toCharThreeNF, toShortNFOfCharThree_a₂, hb₂, div_zero, ← VariableChange.one_def, one_mul]
  exact W.toShortNFOfCharThree_spec hb₂
/-
**WeierstrassCurve.toCharThreeNF_spec** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurv
e`。
形式化陈述：toCharThreeNF_spec : (W.toCharThreeNF • W).IsCharThreeNF
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WeierstrassCurve.toCharThreeNF_spec_of_b₂_eq_zero`：toCharThreeNF_spec_of
_b₂_eq_zero (hb₂ : W.b₂ = 0) : (W.toCharThreeNF • W).IsShortNF
· 使用定理 `WeierstrassCurve.toCharThreeNF_spec_of_b₂_ne_zero`：toCharThreeNF_spec_of
_b₂_ne_zero (hb₂ : W.b₂ != 0) : (W.toCharThreeNF • W).IsCharThreeJNeZeroNF
-/
instance toCharThreeNF_spec : (W.toCharThreeNF • W).IsCharThreeNF := by
  by_cases hb₂ : W.b₂ = 0
  · have := W.toCharThreeNF_spec_of_b₂_eq_zero hb₂
    infer_instance
  · have := W.toCharThreeNF_spec_of_b₂_ne_zero hb₂
    infer_instance
/-
**WeierstrassCurve.exists_variableChange_isCharThreeNF** 是 Mathlib 中的一个定理，位于命名空间
 `WeierstrassCurve`。
形式化陈述：exists_variableChange_isCharThreeNF : exists C : VariableChange F, (C • W)
.IsCharThreeNF
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_variableChange_isCharThreeNF : ∃ C : VariableChange F, (C • W).IsCharThreeNF :=
  ⟨_, W.toCharThreeNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 2 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j ≠ 0, if its `a₁ = 1` and
`a₃, a₄ = 0`. In other words it is `Y² + XY = X³ + a₂X² + a₆`. -/
@[mk_iff]
/-
**WeierstrassCurve.IsCharTwoJNeZeroNF** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCu
rve`。
形式化陈述：{R : Type u_1} → [CommRing R] → WeierstrassCurve R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeierstrassCurve` is in normal form of characteristic = 2 and j ≠ 0, if its `
a₁ = 1` and
`a₃, a₄ = 0`. In other words it is `Y² + XY = X³ + a₂X² + a₆`.
-/
class IsCharTwoJNeZeroNF : Prop where
  a₁ : W.a₁ = 1
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharTwoJNeZeroNF]

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₁_of_isCharTwoJNeZeroNF : W.a₁ = 1 := IsCharTwoJNeZeroNF.a₁

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₃_of_isCharTwoJNeZeroNF : W.a₃ = 0 := IsCharTwoJNeZeroNF.a₃

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₄_of_isCharTwoJNeZeroNF : W.a₄ = 0 := IsCharTwoJNeZeroNF.a₄

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₂_of_isCharTwoJNeZeroNF : W.b₂ = 1 + 4 * W.a₂ := by
  rw [b₂, a₁_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₄_of_isCharTwoJNeZeroNF : W.b₄ = 0 := by
  rw [b₄, a₃_of_isCharTwoJNeZeroNF, a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₆_of_isCharTwoJNeZeroNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆, a₃_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isCharTwoJNeZeroNF : W.b₈ = W.a₆ + 4 * W.a₂ * W.a₆ := by
  rw [b₈, a₁_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF, a₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isCharTwoJNeZeroNF : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄, b₄_of_isCharTwoJNeZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isCharTwoJNeZeroNF : W.c₆ = -W.b₂ ^ 3 - 864 * W.a₆ := by
  rw [c₆, b₄_of_isCharTwoJNeZeroNF, b₆_of_isCharTwoJNeZeroNF]
  ring1

variable [CharP R 2]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₂_of_isCharTwoJNeZeroNF_of_char_two : W.b₂ = 1 := by
  rw [b₂_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₆_of_isCharTwoJNeZeroNF_of_char_two : W.b₆ = 0 := by
  rw [b₆_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isCharTwoJNeZeroNF_of_char_two : W.b₈ = W.a₆ := by
  rw [b₈_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * W.a₆ * CharP.cast_eq_zero R 2
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isCharTwoJNeZeroNF_of_char_two : W.c₄ = 1 := by
  rw [c₄_of_isCharTwoJNeZeroNF, b₂_of_isCharTwoJNeZeroNF_of_char_two]
  ring1
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isCharTwoJNeZeroNF_of_char_two : W.c₆ = 1 := by
  rw [c₆_of_isCharTwoJNeZeroNF, b₂_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination (-1 - 432 * W.a₆) * CharP.cast_eq_zero R 2

@[simp]
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isCharTwoJNeZeroNF_of_char_two : W.Δ = W.a₆ := by
  rw [Δ, b₂_of_isCharTwoJNeZeroNF_of_char_two, b₄_of_isCharTwoJNeZeroNF,
    b₆_of_isCharTwoJNeZeroNF_of_char_two, b₈_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination -W.a₆ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] [CharP F 2]

@[simp]
/-
**WeierstrassCurve.j_of_isCharTwoJNeZeroNF_of_char_two** 是 Mathlib 中的一个定理，位于命名空间
 `WeierstrassCurve`。
形式化陈述：j_of_isCharTwoJNeZeroNF_of_char_two : W.j = 1 / W.a₆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
· 使用定理 `WeierstrassCurve.c₄_of_isCharTwoJNeZeroNF_of_char_two`：c₄_of_isCharTwoJN
eZeroNF_of_char_two : W.c₄ = 1
· 使用定理 `WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two`：Δ_of_isCharTwoJNeZ
eroNF_of_char_two : W.Δ = W.a₆
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem j_of_isCharTwoJNeZeroNF_of_char_two : W.j = 1 / W.a₆ := by
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharTwoJNeZeroNF_of_char_two, Δ_of_isCharTwoJNeZeroNF_of_char_two, one_pow]
/-
**WeierstrassCurve.j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two** 是 Mathlib 中的一个定
理，位于命名空间 `WeierstrassCurve`。
形式化陈述：j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two : W.j != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j_of_isCharTwoJNeZeroNF_of_char_two`：j_of_isCharTwoJNeZ
eroNF_of_char_two : W.j = 1 / W.a₆
· 使用定理 `div_ne_zero_iff`：div_ne_zero_iff : a / b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two`：Δ_of_isCharTwoJNeZ
eroNF_of_char_two : W.Δ = W.a₆
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
-/
theorem j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two : W.j ≠ 0 := by
  rw [j_of_isCharTwoJNeZeroNF_of_char_two, div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact ⟨one_ne_zero, h⟩

end Quantity

/-! ## Normal forms of characteristic = 2 and j = 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j = 0, if its `a₁, a₂ = 0`.
In other words it is `Y² + a₃Y = X³ + a₄X + a₆`. -/
@[mk_iff]
/-
**WeierstrassCurve.IsCharTwoJEqZeroNF** 是 Mathlib 中的一个归纳类型，位于命名空间 `WeierstrassCu
rve`。
形式化陈述：{R : Type u_1} → [CommRing R] → WeierstrassCurve R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeierstrassCurve` is in normal form of characteristic = 2 and j = 0, if its `
a₁, a₂ = 0`.
In other words it is `Y² + a₃Y = X³ + a₄X + a₆`.
-/
class IsCharTwoJEqZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0

section Quantity

variable [W.IsCharTwoJEqZeroNF]

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₁_of_isCharTwoJEqZeroNF : W.a₁ = 0 := IsCharTwoJEqZeroNF.a₁

@[simp]
/-
**WeierstrassCurve.a** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem a₂_of_isCharTwoJEqZeroNF : W.a₂ = 0 := IsCharTwoJEqZeroNF.a₂

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₂_of_isCharTwoJEqZeroNF : W.b₂ = 0 := by
  rw [b₂, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₄_of_isCharTwoJEqZeroNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄, a₁_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isCharTwoJEqZeroNF : W.b₈ = -W.a₄ ^ 2 := by
  rw [b₈, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isCharTwoJEqZeroNF : W.c₄ = -48 * W.a₄ := by
  rw [c₄, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isCharTwoJEqZeroNF : W.c₆ = -216 * W.b₆ := by
  rw [c₆, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

@[simp]
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isCharTwoJEqZeroNF : W.Δ = -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  rw [Δ, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

variable [CharP R 2]
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₄_of_isCharTwoJEqZeroNF_of_char_two : W.b₄ = 0 := by
  rw [b₄_of_isCharTwoJEqZeroNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2
/-
**WeierstrassCurve.b** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem b₈_of_isCharTwoJEqZeroNF_of_char_two : W.b₈ = W.a₄ ^ 2 := by
  rw [b₈_of_isCharTwoJEqZeroNF]
  linear_combination -W.a₄ ^ 2 * CharP.cast_eq_zero R 2
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₄_of_isCharTwoJEqZeroNF_of_char_two : W.c₄ = 0 := by
  rw [c₄_of_isCharTwoJEqZeroNF]
  linear_combination -24 * W.a₄ * CharP.cast_eq_zero R 2
/-
**WeierstrassCurve.c** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem c₆_of_isCharTwoJEqZeroNF_of_char_two : W.c₆ = 0 := by
  rw [c₆_of_isCharTwoJEqZeroNF]
  linear_combination -108 * W.b₆ * CharP.cast_eq_zero R 2
/-
**WeierstrassCurve.** 是 Mathlib 中的一个定理，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Δ_of_isCharTwoJEqZeroNF_of_char_two : W.Δ = W.a₃ ^ 4 := by
  rw [Δ_of_isCharTwoJEqZeroNF, b₆_of_char_two]
  linear_combination (-32 * W.a₄ ^ 3 - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
/-
**WeierstrassCurve.j_of_isCharTwoJEqZeroNF** 是 Mathlib 中的一个定理，位于命名空间 `Weierstras
sCurve`。
形式化陈述：j_of_isCharTwoJEqZeroNF : W.j = 110592 * W.a₄ ^ 3 / (64 * W.a₄ ^ 3 + 27 * 
W.b₆ ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `WeierstrassCurve.coe_Δ'`：coe_Δ' : W.Δ' = W.Δ
· 使用定理 `WeierstrassCurve.c₄_of_isCharTwoJEqZeroNF`：c₄_of_isCharTwoJEqZeroNF : W.
c₄ = -48 * W.a₄
· 使用定理 `WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF`：Δ_of_isCharTwoJEqZeroNF : W.Δ 
= -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2)
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 56 条，此处仅展示前 30 条）
-/
theorem j_of_isCharTwoJEqZeroNF : W.j = 110592 * W.a₄ ^ 3 / (64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharTwoJEqZeroNF] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharTwoJEqZeroNF, Δ_of_isCharTwoJEqZeroNF, div_eq_div_iff h (neg_ne_zero.1 h)]
  ring1

@[simp]
/-
**WeierstrassCurve.j_of_isCharTwoJEqZeroNF_of_char_two** 是 Mathlib 中的一个定理，位于命名空间
 `WeierstrassCurve`。
形式化陈述：j_of_isCharTwoJEqZeroNF_of_char_two [CharP F 2] : W.j = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.j.eq_1`：∀ {R : Type u} [inst : CommRing R] (W : Weierst
rassCurve R) [inst_1 : W.IsElliptic], W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3
· 使用定理 `WeierstrassCurve.c₄_of_isCharTwoJEqZeroNF_of_char_two`：c₄_of_isCharTwoJE
qZeroNF_of_char_two : W.c₄ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF`：Δ_of_isCharTwoJEqZeroNF : W.Δ 
= -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem j_of_isCharTwoJEqZeroNF_of_char_two [CharP F 2] : W.j = 0 := by
  rw [j, c₄_of_isCharTwoJEqZeroNF_of_char_two]; simp

end Quantity

/-! ## Normal forms of characteristic = 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2, if it is
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`). -/
/-
**WeierstrassCurve.inductive** 是 Mathlib 中的一个类，位于命名空间 `WeierstrassCurve`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `WeierstrassCurve` is in normal form of characteristic = 2, if it is
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`).
-/
class inductive IsCharTwoNF : Prop
| of_j_ne_zero [W.IsCharTwoJNeZeroNF] : IsCharTwoNF
| of_j_eq_zero [W.IsCharTwoJEqZeroNF] : IsCharTwoNF
/-
**WeierstrassCurve.isCharTwoNF_of_isCharTwoJNeZeroNF** 是 Mathlib 中的一个实例，位于命名空间 `
WeierstrassCurve`。
形式化陈述：isCharTwoNF_of_isCharTwoJNeZeroNF [W.IsCharTwoJNeZeroNF] : W.IsCharTwoNF
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCharTwoNF_of_isCharTwoJNeZeroNF [W.IsCharTwoJNeZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_ne_zero
/-
**WeierstrassCurve.isCharTwoNF_of_isCharTwoJEqZeroNF** 是 Mathlib 中的一个实例，位于命名空间 `
WeierstrassCurve`。
形式化陈述：isCharTwoNF_of_isCharTwoJEqZeroNF [W.IsCharTwoJEqZeroNF] : W.IsCharTwoNF
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCharTwoNF_of_isCharTwoJEqZeroNF [W.IsCharTwoJEqZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_eq_zero

section VariableChange

variable [CharP R 2] [CharP F 2]

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 2,
there is an explicit change of variables of it to `Y² + a₃Y = X³ + a₄X + a₆`
(`WeierstrassCurve.IsCharTwoJEqZeroNF`) if its j = 0. -/
/-
**WeierstrassCurve.toCharTwoJEqZeroNF** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e`。
形式化陈述：toCharTwoJEqZeroNF : VariableChange R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `WeierstrassCurve` defined over a ring of characteristic = 2,
there is an explicit change of variables of it to `Y² + a₃Y = X³ + a₄X + a₆`
(`WeierstrassCurve.IsCharTwoJEqZeroNF`) if its j = 0.
-/
def toCharTwoJEqZeroNF : VariableChange R := ⟨1, W.a₂, 0, 0⟩
/-
**WeierstrassCurve.toCharTwoJEqZeroNF_spec** 是 Mathlib 中的一个定理，位于命名空间 `Weierstras
sCurve`。
形式化陈述：toCharTwoJEqZeroNF_spec (ha₁ : W.a₁ = 0) : (W.toCharTwoJEqZeroNF • W).IsCh
arTwoJEqZeroNF
参数：ha₁ : W.a₁ = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 62 条，此处仅展示前 30 条）
-/
theorem toCharTwoJEqZeroNF_spec (ha₁ : W.a₁ = 0) :
    (W.toCharTwoJEqZeroNF • W).IsCharTwoJEqZeroNF := by
  constructor
  · simp [toCharTwoJEqZeroNF, ha₁, variableChange_a₁]
  · simp_rw [toCharTwoJEqZeroNF, variableChange_a₂, inv_one, Units.val_one]
    linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F)

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `Y² + XY = X³ + a₂X² + a₆`
(`WeierstrassCurve.IsCharTwoJNeZeroNF`) if its j ≠ 0. -/
/-
**WeierstrassCurve.toCharTwoJNeZeroNF** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurv
e`。
形式化陈述：toCharTwoJNeZeroNF (W : WeierstrassCurve F) (ha₁ : W.a₁ != 0) : VariableCh
ange F
参数：W : WeierstrassCurve F；ha₁ : W.a₁ != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `Y² + XY = X³ + a₂X² + a₆`
(`WeierstrassCurve.IsCharTwoJNeZeroNF`) if its j ≠ 0.
-/
def toCharTwoJNeZeroNF (W : WeierstrassCurve F) (ha₁ : W.a₁ ≠ 0) : VariableChange F :=
  ⟨Units.mk0 _ ha₁, W.a₃ / W.a₁, 0, (W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) / W.a₁ ^ 3⟩
/-
**WeierstrassCurve.toCharTwoJNeZeroNF_spec** 是 Mathlib 中的一个定理，位于命名空间 `Weierstras
sCurve`。
形式化陈述：toCharTwoJNeZeroNF_spec (ha₁ : W.a₁ != 0) : (W.toCharTwoJNeZeroNF ha₁ • W)
.IsCharTwoJNeZeroNF
参数：ha₁ : W.a₁ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 106 条，此处仅展示前 30 条）
-/
theorem toCharTwoJNeZeroNF_spec (ha₁ : W.a₁ ≠ 0) :
    (W.toCharTwoJNeZeroNF ha₁ • W).IsCharTwoJNeZeroNF := by
  constructor
  · simp [toCharTwoJNeZeroNF, ha₁, variableChange_a₁]
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₃, -mul_eq_zero]
    linear_combination (W.a₃ * W.a₁ ^ 3 + W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) * CharP.cast_eq_zero F 2
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₄, -mul_eq_zero]
    linear_combination (W.a₃ ^ 2 + W.a₁ * W.a₃ * W.a₂) * CharP.cast_eq_zero F 2

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharTwoNF`, that is,
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`). -/
/-
**WeierstrassCurve.toCharTwoNF** 是 Mathlib 中的一个定义，位于命名空间 `WeierstrassCurve`。
形式化陈述：toCharTwoNF [DecidableEq F] : VariableChange F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharTwoNF`
, that is,
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`).
-/
def toCharTwoNF [DecidableEq F] : VariableChange F :=
  if ha₁ : W.a₁ = 0 then W.toCharTwoJEqZeroNF else W.toCharTwoJNeZeroNF ha₁
/-
**WeierstrassCurve.toCharTwoNF_spec** 是 Mathlib 中的一个实例，位于命名空间 `WeierstrassCurve`
。
形式化陈述：toCharTwoNF_spec [DecidableEq F] : (W.toCharTwoNF • W).IsCharTwoNF
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeierstrassCurve.toCharTwoNF.eq_1`：∀ {F : Type u_2} [inst : Field F] (W 
: WeierstrassCurve F) [inst_1 : DecidableEq F],   W.toCharTwoNF = if ha₁ : W.a₁ 
= 0 then W.toCharTwoJEq…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `WeierstrassCurve.toCharTwoJEqZeroNF_spec`：toCharTwoJEqZeroNF_spec (ha₁ :
 W.a₁ = 0) : (W.toCharTwoJEqZeroNF • W).IsCharTwoJEqZeroNF
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `WeierstrassCurve.toCharTwoJNeZeroNF_spec`：toCharTwoJNeZeroNF_spec (ha₁ :
 W.a₁ != 0) : (W.toCharTwoJNeZeroNF ha₁ • W).IsCharTwoJNeZeroNF
-/
instance toCharTwoNF_spec [DecidableEq F] : (W.toCharTwoNF • W).IsCharTwoNF := by
  by_cases ha₁ : W.a₁ = 0
  · rw [toCharTwoNF, dif_pos ha₁]
    have := W.toCharTwoJEqZeroNF_spec ha₁
    infer_instance
  · rw [toCharTwoNF, dif_neg ha₁]
    have := W.toCharTwoJNeZeroNF_spec ha₁
    infer_instance
/-
**WeierstrassCurve.exists_variableChange_isCharTwoNF** 是 Mathlib 中的一个定理，位于命名空间 `
WeierstrassCurve`。
形式化陈述：exists_variableChange_isCharTwoNF : exists C : VariableChange F, (C • W).I
sCharTwoNF
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_variableChange_isCharTwoNF : ∃ C : VariableChange F, (C • W).IsCharTwoNF := by
  classical
  exact ⟨_, W.toCharTwoNF_spec⟩

end VariableChange

end WeierstrassCurve

