/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Ordered scalar multiplication and vector addition

This file defines ordered scalar multiplication and vector addition, and proves some properties.
In the additive case, a motivating example is given by the additive action of `ℤ` on subsets of
reals that are closed under integer translation. The order compatibility allows for a treatment of
the `R((z))`-module structure on `(z ^ s) V((z))` for an `R`-module `V`, using the formalism of Hahn
series. In the multiplicative case, a standard example is the action of non-negative rationals on
an ordered field.

## Implementation notes
* Because these classes mix the algebra and order hierarchies, we write them as `Prop`-valued
  mixins.
* Despite the file name, Ordered AddTorsors are not defined as a separate class. To implement them,
  combine `[AddTorsor G P]` with `[IsOrderedCancelVAdd G P]`

## Definitions
* IsOrderedSMul : inequalities are preserved by scalar multiplication.
* IsOrderedVAdd : inequalities are preserved by translation.
* IsCancelSMul : the scalar multiplication version of cancellative multiplication
* IsCancelVAdd : the vector addition version of cancellative addition
* IsOrderedCancelSMul : inequalities are preserved and reflected by scalar multiplication.
* IsOrderedCancelVAdd : inequalities are preserved and reflected by translation.

## Instances
* `IsOrderedMonoid.toIsOrderedSMul`
* `IsOrderedAddMonoid.toIsOrderedVAdd`
* `IsOrderedSMul.toCovariantClassLeft`
* `IsOrderedVAdd.toCovariantClassLeft`
* `IsOrderedCancelSMul.toCancelSMul`
* `IsOrderedCancelVAdd.toCancelVAdd`
* `IsOrderedCancelMonoid.toIsOrderedCancelSMul`
* `IsOrderedCancelAddMonoid.toIsOrderedCancelVAdd`
* `IsOrderedCancelSMul.toContravariantClassLeft`
* `IsOrderedCancelVAdd.toContravariantClassLeft`

## TODO
* (lex) prod instances
* Pi instances
* WithTop (in a different file?)
-/

public section

open Function

variable {G P : Type*}

/--
Definition of `IsOrderedVAdd` / `IsOrderedVAdd` 的定义

English:
class IsOrderedVAdd
  parameters: (G P : Type*) [LE G] [LE P] [VAdd G P]
  axioms and operations (2):
    - vadd_le_vadd_left : forall a b : P, a <= b -> forall c : G, c +ᵥ a <= c +ᵥ b
    - vadd_le_vadd_right : forall c d : G, c <= d -> forall a : P, c +ᵥ a <= d +ᵥ a

中文:
类 是OrderedVAdd
  参数: (G P : 类型) [LE G] [LE P] [向量加法 G P]
  公理与运算 (2 个):
    - vadd_le_vadd_left : 对任意 a b : P, a <= b -> 对任意 c : G, c +ᵥ a <= c +ᵥ b
    - vadd_le_vadd_right : 对任意 c d : G, c <= d -> 对任意 a : P, c +ᵥ a <= d +ᵥ a
-/
class IsOrderedVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop where
  protected vadd_le_vadd_left : forall a b : P, a <= b -> forall c : G, c +ᵥ a <= c +ᵥ b
  protected vadd_le_vadd_right : forall c d : G, c <= d -> forall a : P, c +ᵥ a <= d +ᵥ a

/-- An ordered scalar multiplication is a bi-monotone scalar multiplication. Note that this is
different from `IsOrderedModule` whose defining conditions are restricted to nonnegative elements.
-/
@[to_additive]
/--
Definition of `IsOrderedSMul` / `IsOrderedSMul` 的定义

English:
class IsOrderedSMul
  parameters: (G P : Type*) [LE G] [LE P] [SMul G P]
  axioms and operations (2):
    - smul_le_smul_left : forall a b : P, a <= b -> forall c : G, c • a <= c • b
    - smul_le_smul_right : forall c d : G, c <= d -> forall a : P, c • a <= d • a

中文:
类 是OrderedSMul
  参数: (G P : 类型) [LE G] [LE P] [标量乘法 G P]
  公理与运算 (2 个):
    - smul_le_smul_left : 对任意 a b : P, a <= b -> 对任意 c : G, c • a <= c • b
    - smul_le_smul_right : 对任意 c d : G, c <= d -> 对任意 a : P, c • a <= d • a
-/
class IsOrderedSMul (G P : Type*) [LE G] [LE P] [SMul G P] : Prop where
  protected smul_le_smul_left : forall a b : P, a <= b -> forall c : G, c • a <= c • b
  protected smul_le_smul_right : forall c d : G, c <= d -> forall a : P, c • a <= d • a

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: G] [LE P] [SMul G P] [IsOrderedSMul G P] : CovariantClass G P (· • ·) (· <= ·) where
  body: fun a _ _ bc => IsOrderedSMul.smul_le_smul_left _ _ bc a

@[to_additive]

中文:
实例 [LE
  签名: G] [LE P] [标量乘法 G P] [是OrderedSMul G P] : 协变类 G P (· • ·) (· <= ·) where
  定义体: fun a _ _ bc => IsOrderedSMul.smul_le_smul_left _ _ bc a

@[to_additive]

Depends on / 依赖: IsOrderedSMul, IsOrderedSMul.smul_le_smul_left, smul_le_smul_left
-/
instance [LE G] [LE P] [SMul G P] [IsOrderedSMul G P] : CovariantClass G P (· • ·) (· <= ·) where
  elim := fun a _ _ bc => IsOrderedSMul.smul_le_smul_left _ _ bc a

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: G] [Preorder G] [IsOrderedMonoid G] : IsOrderedSMul G G where
  body: mul_le_mul_right
  smul_le_smul_right _ _ := mul_le_mul_left

@[to_additive (attr := gcongr)]

中文:
实例 [交换幺半群
  签名: G] [预序 G] [是Ordered幺半群 G] : 是OrderedSMul G G where
  定义体: mul_le_mul_right
  smul_le_smul_right _ _ := mul_le_mul_left

@[to_additive (attr := gcongr)]

Depends on / 依赖: mul_le_mul_right
-/
instance [CommMonoid G] [Preorder G] [IsOrderedMonoid G] : IsOrderedSMul G G where
  smul_le_smul_left _ _ := mul_le_mul_right
  smul_le_smul_right _ _ := mul_le_mul_left

@[to_additive (attr := gcongr)]
/--
theorem `IsOrderedSMul.smul_le_smul` / 定理 `IsOrderedSMul.smul_le_smul`

English:
theorem IsOrderedSMul.smul_le_smul
  statement: [LE G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
  proof: (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)

@[to_additive]

中文:
定理 是OrderedSMul.smul_le_smul
  结论: [LE G] [预序 P] [标量乘法 G P] [是OrderedSMul G P]
  证明: (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)

@[to_additive]

Depends on / 依赖: IsOrderedSMul, IsOrderedSMul.smul_le_smul_left, IsOrderedSMul.smul_le_smul_right, smul_le_smul_left, smul_le_smul_right
-/
theorem IsOrderedSMul.smul_le_smul [LE G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {a b : G} {c d : P} (hab : a <= b) (hcd : c <= d) : a • c <= b • d :=
  (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)

@[to_additive]
/--
theorem `Monotone.smul` / 定理 `Monotone.smul`

English:
theorem Monotone.smul
  statement: {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
  proof: fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)

中文:
定理 递增.smul
  结论: {γ : 类型} [预序 G] [预序 P] [预序 γ] [标量乘法 G P]
  证明: fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)

Depends on / 依赖: IsOrderedSMul, IsOrderedSMul.smul_le_smul_left, IsOrderedSMul.smul_le_smul_right, smul_le_smul_left, smul_le_smul_right
-/
theorem Monotone.smul {γ : Type*} [Preorder G] [Preorder P] [Preorder γ] [SMul G P]
    [IsOrderedSMul G P] {f : γ -> G} {g : γ -> P} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x • g x :=
  fun _ _ hab => (IsOrderedSMul.smul_le_smul_left _ _ (hg hab) _).trans
    (IsOrderedSMul.smul_le_smul_right _ _ (hf hab) _)

/--
Definition of `IsOrderedCancelVAdd` / `IsOrderedCancelVAdd` 的定义

English:
class IsOrderedCancelVAdd
  parameters: (G P : Type*) [LE G] [LE P] [VAdd G P]
  extends: IsOrderedVAdd G P
  axioms and operations (2):
    - le_of_vadd_le_vadd_left : forall (a : G) (b c : P), a +ᵥ b <= a +ᵥ c -> b <= c
    - le_of_vadd_le_vadd_right : forall (a b : G) (c : P), a +ᵥ c <= b +ᵥ c -> a <= b

中文:
类 是OrderedCancelVAdd
  参数: (G P : 类型) [LE G] [LE P] [向量加法 G P]
  继承: 是OrderedVAdd G P
  公理与运算 (2 个):
    - le_of_vadd_le_vadd_left : 对任意 (a : G) (b c : P), a +ᵥ b <= a +ᵥ c -> b <= c
    - le_of_vadd_le_vadd_right : 对任意 (a b : G) (c : P), a +ᵥ c <= b +ᵥ c -> a <= b
-/
class IsOrderedCancelVAdd (G P : Type*) [LE G] [LE P] [VAdd G P] : Prop
    extends IsOrderedVAdd G P where
  protected le_of_vadd_le_vadd_left : forall (a : G) (b c : P), a +ᵥ b <= a +ᵥ c -> b <= c
  protected le_of_vadd_le_vadd_right : forall (a b : G) (c : P), a +ᵥ c <= b +ᵥ c -> a <= b

/-- An ordered cancellative scalar multiplication is an ordered scalar multiplication that is
  cancellative. -/
@[to_additive]
/--
Definition of `IsOrderedCancelSMul` / `IsOrderedCancelSMul` 的定义

English:
class IsOrderedCancelSMul
  parameters: (G P : Type*) [LE G] [LE P] [SMul G P]
  extends: IsOrderedSMul G P
  axioms and operations (2):
    - le_of_smul_le_smul_left : forall (a : G) (b c : P), a • b <= a • c -> b <= c
    - le_of_smul_le_smul_right : forall (a b : G) (c : P), a • c <= b • c -> a <= b

中文:
类 是OrderedCancelSMul
  参数: (G P : 类型) [LE G] [LE P] [标量乘法 G P]
  继承: 是OrderedSMul G P
  公理与运算 (2 个):
    - le_of_smul_le_smul_left : 对任意 (a : G) (b c : P), a • b <= a • c -> b <= c
    - le_of_smul_le_smul_right : 对任意 (a b : G) (c : P), a • c <= b • c -> a <= b
-/
class IsOrderedCancelSMul (G P : Type*) [LE G] [LE P] [SMul G P] : Prop
    extends IsOrderedSMul G P where
  protected le_of_smul_le_smul_left : forall (a : G) (b c : P), a • b <= a • c -> b <= c
  protected le_of_smul_le_smul_right : forall (a b : G) (c : P), a • c <= b • c -> a <= b

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] :
  body: (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_left a c b h.ge)
  right_cancel' a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_right b a c h.ge)

@[to_additive]

中文:
实例 [偏序
  签名: G] [偏序 P] [标量乘法 G P] [是OrderedCancelSMul G P] :
  定义体: (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_left a c b h.ge)
  right_cancel' a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_right b a c h.ge)

@[to_additive]

Depends on / 依赖: IsOrderedCancelSMul, IsOrderedCancelSMul.le_of_smul_le_smul_left, antisymm, h.le, le_of_smul_le_smul_left
-/
instance [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] :
    IsCancelSMul G P where
  left_cancel' a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_left a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_left a c b h.ge)
  right_cancel' a b c h := (IsOrderedCancelSMul.le_of_smul_le_smul_right a b c h.le).antisymm
    (IsOrderedCancelSMul.le_of_smul_le_smul_right b a c h.ge)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: G] [Preorder G] [IsOrderedCancelMonoid G] : IsOrderedCancelSMul G G where
  body: le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

@[to_additive]

中文:
实例 [交换幺半群
  签名: G] [预序 G] [是OrderedCancel幺半群 G] : 是OrderedCancelSMul G G where
  定义体: le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

@[to_additive]

Depends on / 依赖: le_of_mul_le_mul_left
-/
instance [CommMonoid G] [Preorder G] [IsOrderedCancelMonoid G] : IsOrderedCancelSMul G G where
  le_of_smul_le_smul_left _ _ _ := le_of_mul_le_mul_left'
  le_of_smul_le_smul_right _ _ _ := le_of_mul_le_mul_right'

@[to_additive]
instance (priority := 200) [LE G] [LE P] [SMul G P] [IsOrderedCancelSMul G P] :
    ContravariantClass G P (· • ·) (· <= ·) :=
  ⟨IsOrderedCancelSMul.le_of_smul_le_smul_left⟩

namespace SMul

@[to_additive]
/--
theorem `smul_lt_smul_of_le_of_lt` / 定理 `smul_lt_smul_of_le_of_lt`

English:
theorem smul_lt_smul_of_le_of_lt
  statement: [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
  proof: by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d <= c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_ge] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]

中文:
定理 smul_lt_smul_of_le_of_lt
  结论: [LE G] [预序 P] [标量乘法 G P] [是OrderedCancelSMul G P]
  证明: by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d <= c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_ge] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]

Depends on / 依赖: IsOrderedCancelSMul, IsOrderedCancelSMul.le_of_smul_le_smul_left, IsOrderedSMul, IsOrderedSMul.smul_le_smul_left, IsOrderedSMul.smul_le_smul_right, and_false, le_of_lt, le_of_smul_le_smul_left, lt_iff_le_not_ge, lt_of_le_not_ge, lt_of_le_of_lt, not_true_eq_false, smul_le_smul_left, smul_le_smul_right
-/
theorem smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a <= b) (h₂ : c < d) :
    a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d <= c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_ge] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
/--
theorem `smul_lt_smul_of_lt_of_le` / 定理 `smul_lt_smul_of_lt_of_le`

English:
theorem smul_lt_smul_of_lt_of_le
  statement: [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
  proof: by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b <= a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_ge] at h₁
  simp_all only [not_true_eq_false, and_false]

中文:
定理 smul_lt_smul_of_lt_of_le
  结论: [预序 G] [预序 P] [标量乘法 G P] [是OrderedCancelSMul G P]
  证明: by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b <= a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_ge] at h₁
  simp_all only [not_true_eq_false, and_false]

Depends on / 依赖: IsOrderedCancelSMul, IsOrderedCancelSMul.le_of_smul_le_smul_right, IsOrderedSMul, IsOrderedSMul.smul_le_smul_left, IsOrderedSMul.smul_le_smul_right, and_false, le_of_lt, le_of_smul_le_smul_right, lt_iff_le_not_ge, lt_of_le_not_ge, lt_of_le_of_lt, not_true_eq_false, smul_le_smul_left, smul_le_smul_right
-/
theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c <= d) : a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b <= a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_ge] at h₁
  simp_all only [not_true_eq_false, and_false]

end SMul
