/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Torsors of group actions

This file defines torsors of additive and multiplicative group actions.

## Notation

The group elements are referred to as acting on points.  This file
uses the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element, as well as `•` and `/ₛ` for the
corresponding operations in multiplicative torsors.

## Implementation notes

Affine spaces are a motivating example of additive torsors. Additional simply transitive
actions which give rise to torsors include the action of the Weyl group on Weyl chambers, the
action of non-zero scalars on the non-vanishing elements of the top exterior power of a
finite-dimensional vector space, the action of the general linear group of a vector space on the
bases of that space, and the monodromy action of the fundamental group of a space on a fibre of its
universal cover. Both the additive and multiplicative notation will be useful to formalise
such examples.

## Notation

* `v +ᵥ p` is a notation for `VAdd.vadd`, the left action of an additive monoid;
* `p₁ -ᵥ p₂` is a notation for `VSub.vsub`, the difference between two points in an additive torsor
  as an element of the corresponding additive group;
* `v • p` is a notation for `SMul.smul`, the left action of a multiplicative monoid;
* `p₁ /ₛ p₂` is a notation for `SDiv.sdiv`, the quotient of two points in a multiplicative
  torsor as an element of the corresponding multiplicative group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

@[expose] public section

assert_not_exists MonoidWithZero

/-- An `AddTorsor G P` gives a structure to the nonempty type `P`,
acted on by an `AddGroup G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
/-
**AddTorsor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : outParam (Type u_1)) → Type u_2 → [AddGroup G] → Type (max u_1 u_2)
参数：Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AddTorsor G P` gives a structure to the nonempty type `P`,
acted on by an `AddGroup G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space.
-/
class AddTorsor (G : outParam Type*) (P : Type*) [AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

/-- A `Torsor G P` gives a structure to the nonempty type `P`,
acted on by a `Group G` with a transitive and free action given
by the `•` operation and a corresponding division given by the
`/ₛ` operation. -/
@[to_additive existing]
/-
**Torsor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : outParam (Type u_1)) → Type u_2 → [Group G] → Type (max u_1 u_2)
参数：Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Torsor G P` gives a structure to the nonempty type `P`,
acted on by a `Group G` with a transitive and free action given
by the `•` operation and a corresponding division given by the
`/ₛ` operation.
-/
class Torsor (G : outParam Type*) (P : Type*) [Group G] extends MulAction G P, SDiv G P where
  [nonempty : Nonempty P]
  /-- Scalar division and multiplication with the same element cancels out. -/
  sdiv_smul' : ∀ p₁ p₂ : P, (p₁ /ₛ p₂ : G) • p₂ = p₁
  /-- Scalar multiplication and division with the same element cancels out. -/
  smul_sdiv' : ∀ (g : G) (p : P), (g • p) /ₛ p = g

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed `nolint instance_priority`; lint not ported yet
attribute [instance 100] AddTorsor.nonempty
attribute [instance 100] Torsor.nonempty

/-- A `Group G` is a torsor for itself. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): linter not ported yet
--@[nolint instance_priority]
@[to_additive /-- An `AddGroup G` is a torsor for itself.-/]
/-
**Group.instTorsor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Group.instTorsor (G : Type*) [Group G] : Torsor G G where sdiv
参数：G : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `mul_div_cancel_right`：mul_div_cancel_right (a b : G) : a * b / b = a
-/
instance Group.instTorsor (G : Type*) [Group G] : Torsor G G where
  sdiv := Div.div
  sdiv_smul' := div_mul_cancel
  smul_sdiv' := mul_div_cancel_right

@[deprecated (since := "2026-05-04")] alias addGroupIsAddTorsor := AddGroup.instAddTorsor

/-- Simplify division for a torsor for a `Group G` over itself. -/
@[to_additive (attr := simp) /-- Simplify subtraction for a torsor for an `AddGroup G` over
itself.-/]
/-
**sdiv_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_eq_div {G : Type*} [Group G] (g₁ g₂ : G) : g₁ /ₛ g₂ = g₁ / g₂
参数：g₁ g₂ : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sdiv_eq_div {G : Type*} [Group G] (g₁ g₂ : G) : g₁ /ₛ g₂ = g₁ / g₂ :=
  rfl

section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

/-- Scalar multiplying the result of dividing another point produces that point. -/
@[to_additive (attr := simp) /-- Adding the result of subtracting from another point produces that
point. -/]
/-
**sdiv_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Torsor.sdiv_smul'`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Gr
oup G} [self : Torsor G P] (p₁ p₂ : P), (p₁ /ₛ p₂) • p₂ = p₁
-/
theorem sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁ :=
  Torsor.sdiv_smul' p₁ p₂

/-- Multiplying by a group element then dividing by the original point
produces that group element. -/
@[to_additive (attr := simp) /-- Adding a group element then subtracting the original point
produces that group element. -/]
/-
**smul_sdiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g
参数：g : G；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Torsor.smul_sdiv'`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Gr
oup G} [self : Torsor G P] (g : G) (p : P), g • p /ₛ p = g
-/
theorem smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g :=
  Torsor.smul_sdiv' g p

/-- If the same point multiplied with two group elements produces equal
results, those group elements are equal. -/
@[to_additive /-- If the same point added to two group elements produces equal
results, those group elements are equal. -/]
/-
**smul_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g₂ • p) : g₁ = g₂
参数：p : P；h : g₁ • p = g₂ • p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sdiv`：smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g
-/
theorem smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g₂ • p) : g₁ = g₂ := by
  rw [← smul_sdiv g₁ p, h, smul_sdiv]

@[to_additive (attr := simp)]
/-
**smul_right_cancel_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ • p = g₂ • p ↔ g₁ = g₂
参数：p : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_right_cancel`：smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g
₂ • p) : g₁ = g₂
-/
theorem smul_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ • p = g₂ • p ↔ g₁ = g₂ :=
  ⟨smul_right_cancel p, fun h => h ▸ rfl⟩

/-- Multiplying a group element with the point `p` is an injective function. -/
@[to_additive vadd_right_injective /-- Adding a group element to the point `p` is an injective
function. -/]
/-
**smul_right_injective'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_right_injective' (p : P) : Function.Injective ((· • p) : G -> P)
参数：p : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_right_cancel`：smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g
₂ • p) : g₁ = g₂
-/
theorem smul_right_injective' (p : P) : Function.Injective ((· • p) : G → P) := fun _ _ =>
  smul_right_cancel p

/-- Multiplying a group element with a point, then dividing by another point,
produces the same result as dividing the points then multiplying the group element. -/
@[to_additive /-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the group element. -/]
/-
**smul_sdiv_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂)
参数：g : G；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_right_cancel`：smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g
₂ • p) : g₁ = g₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiv_smul`：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂) := by
  apply smul_right_cancel p₂
  rw [sdiv_smul, mul_smul, sdiv_smul]

/-- Dividing a point by itself produces 1. -/
@[to_additive (attr := simp) /-- Subtracting a point from itself produces 0. -/]
/-
**sdiv_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_self (p : P) : p /ₛ p = (1 : G)
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `smul_sdiv_assoc`：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = 
g * (p₁ /ₛ p₂)
· 使用定理 `smul_sdiv`：smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g

--- 原说明 ---
Dividing a point by itself produces 1.
-/
theorem sdiv_self (p : P) : p /ₛ p = (1 : G) := by
  rw [← one_mul (p /ₛ p), ← smul_sdiv_assoc, smul_sdiv]

/-- If dividing two points produces 1, they are equal. -/
@[to_additive /-- If subtracting two points produces 0, they are equal. -/]
/-
**eq_of_sdiv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_sdiv_eq_one {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G)) : p₁ = p₂
参数：h : p₁ /ₛ p₂ = (1 : G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiv_smul`：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
If dividing two points produces 1, they are equal.
-/
theorem eq_of_sdiv_eq_one {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G)) : p₁ = p₂ := by
  rw [← sdiv_smul p₁ p₂, h, one_smul]

/-- Dividing two points produces 1 if and only if they are equal. -/
@[to_additive (attr := simp) /-- Subtracting two points produces 0 if and only if they are
equal. -/]
/-
**sdiv_eq_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) ↔ p₁ = p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_sdiv_eq_one`：eq_of_sdiv_eq_one {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G)
) : p₁ = p₂
· 使用定理 `sdiv_self`：sdiv_self (p : P) : p /ₛ p = (1 : G)
-/
theorem sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) ↔ p₁ = p₂ :=
  Iff.intro eq_of_sdiv_eq_one fun h => h ▸ sdiv_self _

@[to_additive]
/-
**sdiv_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_ne_one {p q : P} : p /ₛ q != (1 : G) ↔ p != q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sdiv_eq_one_iff_eq`：sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) 
↔ p₁ = p₂
-/
theorem sdiv_ne_one {p q : P} : p /ₛ q ≠ (1 : G) ↔ p ≠ q :=
  not_congr sdiv_eq_one_iff_eq

/-- Cancellation multiplying the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation adding the results of two subtractions. -/]
/-
**sdiv_mul_sdiv_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_right_cancel`：smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g
₂ • p) : g₁ = g₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `sdiv_smul`：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁

--- 原说明 ---
Cancellation multiplying the results of two divisions.
-/
theorem sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃ := by
  apply smul_right_cancel p₃
  rw [mul_smul, sdiv_smul, sdiv_smul, sdiv_smul]

/-- Dividing two points in the reverse order produces the inverse of dividing them. -/
@[to_additive (attr := simp) /-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/]
/-
**inv_sdiv_eq_sdiv_rev** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `smul_right_cancel`：smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g
₂ • p) : g₁ = g₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiv_mul_sdiv_cancel`：sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) *
 (p₂ /ₛ p₃) = p₁ /ₛ p₃
· 使用定理 `sdiv_self`：sdiv_self (p : P) : p /ₛ p = (1 : G)
-/
theorem inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁ := by
  refine inv_eq_of_mul_eq_one_right (smul_right_cancel p₁ ?_)
  rw [sdiv_mul_sdiv_cancel, sdiv_self]

@[to_additive]
/-
**smul_sdiv_eq_div_sdiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sdiv_eq_div_sdiv (g : G) (p q : P) : (g • p) /ₛ q = g / (q /ₛ p)
参数：g : G；p q : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sdiv_assoc`：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = 
g * (p₁ /ₛ p₂)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_sdiv_eq_sdiv_rev`：inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = 
p₂ /ₛ p₁
-/
theorem smul_sdiv_eq_div_sdiv (g : G) (p q : P) : (g • p) /ₛ q = g / (q /ₛ p) := by
  rw [smul_sdiv_assoc, div_eq_mul_inv, inv_sdiv_eq_sdiv_rev]

/-- Dividing by the result of multiplying with a group element produces the same result
as dividing the points and dividing by that group element. -/
@[to_additive /-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/]
/-
**sdiv_smul_eq_sdiv_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ (g • p₂) = (p₁ /ₛ p₂) / 
g
参数：p₁ p₂ : P；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `sdiv_mul_sdiv_cancel`：sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) *
 (p₂ /ₛ p₃) = p₁ /ₛ p₃
· 使用定理 `inv_sdiv_eq_sdiv_rev`：inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = 
p₂ /ₛ p₁
· 使用定理 `smul_sdiv`：smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ (g • p₂) = (p₁ /ₛ p₂) / g := by
  rw [← mul_right_inj (p₂ /ₛ p₁ : G), sdiv_mul_sdiv_cancel, ← inv_sdiv_eq_sdiv_rev, smul_sdiv, ←
    mul_div_assoc, ← inv_sdiv_eq_sdiv_rev, inv_mul_cancel, one_div]

/-- Cancellation dividing the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation subtracting the results of two subtractions. -/]
/-
**sdiv_div_sdiv_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sdiv_div_sdiv_cancel_right (p₁ p₂ p₃ : P) : (p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /
ₛ p₂
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiv_smul_eq_sdiv_div`：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ
 (g • p₂) = (p₁ /ₛ p₂) / g
· 使用定理 `sdiv_smul`：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁

--- 原说明 ---
Cancellation dividing the results of two divisions.
-/
theorem sdiv_div_sdiv_cancel_right (p₁ p₂ p₃ : P) : (p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /ₛ p₂ := by
  rw [← sdiv_smul_eq_sdiv_div, sdiv_smul]

/-- Convert between an equality with multiplying a group element with a point
and an equality of a division of two points with a group element. -/
@[to_additive /-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group element. -/]
/-
**eq_smul_iff_sdiv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_smul_iff_sdiv_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g • p₂ ↔ p₁ /ₛ p₂ = g
参数：p₁ : P；g : G；p₂ : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_sdiv`：smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sdiv_smul`：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁
-/
theorem eq_smul_iff_sdiv_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g • p₂ ↔ p₁ /ₛ p₂ = g :=
  ⟨fun h => h.symm ▸ smul_sdiv _ _, fun h => h ▸ (sdiv_smul _ _).symm⟩

@[to_additive]
/-
**smul_eq_smul_iff_inv_mul_eq_sdiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_eq_smul_iff_inv_mul_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} : v₁ • p₁ = v₂ • 
p₂ ↔ v₁⁻¹ * v₂ = p₁ /ₛ p₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_smul_iff_sdiv_eq`：eq_smul_iff_sdiv_eq (p₁ : P) (g : G) (p₂ : P) : p₁ 
= g • p₂ ↔ p₁ /ₛ p₂ = g
· 使用定理 `smul_sdiv_assoc`：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = 
g * (p₁ /ₛ p₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_eq_smul_iff_inv_mul_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₁⁻¹ * v₂ = p₁ /ₛ p₂ := by
  rw [eq_smul_iff_sdiv_eq, smul_sdiv_assoc, ← mul_right_inj v₁⁻¹, inv_mul_cancel_left, eq_comm]

@[to_additive (attr := simp)]
/-
**smul_sdiv_smul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_sdiv_smul_cancel_right (v₁ v₂ : G) (p : P) : (v₁ • p) /ₛ (v₂ • p) = v
₁ / v₂
参数：v₁ v₂ : G；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiv_smul_eq_sdiv_div`：sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ
 (g • p₂) = (p₁ /ₛ p₂) / g
· 使用定理 `smul_sdiv_assoc`：smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = 
g * (p₁ /ₛ p₂)
· 使用定理 `sdiv_self`：sdiv_self (p : P) : p /ₛ p = (1 : G)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_sdiv_smul_cancel_right (v₁ v₂ : G) (p : P) : (v₁ • p) /ₛ (v₂ • p) = v₁ / v₂ := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, sdiv_self, mul_one]

end General

namespace Equiv

variable {G : Type*} {P : Type*} [Group G] [Torsor G P]

/-- `v ↦ v • p` as an equivalence. -/
@[to_additive /-- `v ↦ v +ᵥ p` as an equivalence. -/]
/-
**Equiv.smulConst** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：smulConst (p : P) : G ≃ P where toFun v
参数：p : P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `smul_sdiv`：smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g
· 使用定理 `sdiv_smul`：sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁

--- 原说明 ---
`v ↦ v • p` as an equivalence.
-/
def smulConst (p : P) : G ≃ P where
  toFun v := v • p
  invFun p' := p' /ₛ p
  left_inv _ := smul_sdiv _ _
  right_inv _ := sdiv_smul _ _

@[to_additive (attr := simp)]
/-
**Equiv.coe_smulConst** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_smulConst (p : P) : ⇑(smulConst p) = fun v => v • p
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smulConst (p : P) : ⇑(smulConst p) = fun v => v • p :=
  rfl

@[to_additive (attr := simp)]
/-
**Equiv.coe_smulConst_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_smulConst_symm (p : P) : ⇑(smulConst p).symm = fun p' => p' /ₛ p
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_smulConst_symm (p : P) : ⇑(smulConst p).symm = fun p' => p' /ₛ p :=
  rfl

/-- `p' ↦ p /ₛ p'` as an equivalence. -/
@[to_additive /-- `p' ↦ p -ᵥ p'` as an equivalence. -/]
/-
**Equiv.constSDiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：constSDiv (p : P) : P ≃ G where toFun
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p' ↦ p /ₛ p'` as an equivalence.
-/
def constSDiv (p : P) : P ≃ G where
  toFun := (p /ₛ ·)
  invFun := (·⁻¹ • p)
  left_inv p' := by simp
  right_inv v := by simp [sdiv_smul_eq_sdiv_div]

@[to_additive (attr := simp)]
/-
**Equiv.coe_constSDiv** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：coe_constSDiv (p : P) : ⇑(constSDiv p) = (p /ₛ ·)
参数：p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_constSDiv (p : P) : ⇑(constSDiv p) = (p /ₛ ·) := rfl

@[to_additive (attr := simp)]
/-
**Equiv.coe_constSDiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_constSDiv_symm (p : P) : ⇑(constSDiv p).symm = fun (v : G) => v⁻¹ • p
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_constSDiv_symm (p : P) : ⇑(constSDiv p).symm = fun (v : G) => v⁻¹ • p :=
  rfl

variable (P)

/-- The permutation given by `p ↦ v • p`. -/
@[to_additive /-- The permutation given by `p ↦ v +ᵥ p`. -/]
/-
**Equiv.constSMul** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：constSMul (v : G) : Equiv.Perm P where toFun
参数：v : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The permutation given by `p ↦ v • p`.
-/
def constSMul (v : G) : Equiv.Perm P where
  toFun := (v • ·)
  invFun := (v⁻¹ • ·)
  left_inv p := by simp [smul_smul]
  right_inv p := by simp [smul_smul]

@[to_additive (attr := simp)]
/-
**Equiv.coe_constSMul** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：coe_constSMul (v : G) : ⇑(constSMul P v) = (v • ·)
参数：v : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_constSMul (v : G) : ⇑(constSMul P v) = (v • ·) := rfl

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

open Function

/-- Point reflection in `x` as a permutation. -/
/-
**Equiv.pointReflection** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：pointReflection (x : P) : Perm P
参数：x : P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Point reflection in `x` as a permutation.
-/
def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)
/-
**Equiv.pointReflection_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：pointReflection_apply (x y : P) : pointReflection x y = (x -ᵥ y) +ᵥ x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointReflection_apply (x y : P) : pointReflection x y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
/-
**Equiv.pointReflection_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：pointReflection_vsub_left (x y : P) : pointReflection x y -ᵥ x = x -ᵥ y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
-/
theorem pointReflection_vsub_left (x y : P) : pointReflection x y -ᵥ x = x -ᵥ y :=
  vadd_vsub ..

@[simp]
/-
**Equiv.pointReflection_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：pointReflection_vsub_right (x y : P) : pointReflection x y -ᵥ y = 2 • (x -
ᵥ y)
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pointReflection_vsub_right (x y : P) : pointReflection x y -ᵥ y = 2 • (x -ᵥ y) := by
  simp [pointReflection, two_nsmul, vadd_vsub_assoc]

@[simp]
/-
**Equiv.pointReflection_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection 
x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection x :=
  ext <| by simp [pointReflection]

@[simp]
/-
**Equiv.pointReflection_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：pointReflection_self (x : P) : pointReflection x x = x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
-/
theorem pointReflection_self (x : P) : pointReflection x x = x :=
  vsub_vadd _ _
/-
**Equiv.pointReflection_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：pointReflection_involutive (x : P) : Involutive (pointReflection x : P -> 
P)
参数：x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.pointReflection_symm`：pointReflection_symm (x : P) : (pointReflect
ion x).symm = pointReflection x
-/
theorem pointReflection_involutive (x : P) : Involutive (pointReflection x : P → P) := fun y =>
  (Equiv.eq_symm_apply _).1 <| by rw [pointReflection_symm]

end Equiv

@[to_additive]
/-
**Torsor.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Torsor.subsingleton_iff (G P : Type*) [Group G] [Torsor G P] : Subsingleto
n G ↔ Subsingleton P
参数：G P : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
-/
theorem Torsor.subsingleton_iff (G P : Type*) [Group G] [Torsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.smulConst default).subsingleton_congr
