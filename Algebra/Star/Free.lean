/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.FreeAlgebra

/-!
# A \*-algebra structure on the free algebra.

Reversing words gives a \*-structure on the free monoid or on the free algebra on a type.

## Implementation note
We have this in a separate file, rather than in `Algebra.FreeMonoid` and `Algebra.FreeAlgebra`,
to avoid importing `Algebra.Star.Basic` into the entire hierarchy.
-/

@[expose] public section


namespace FreeMonoid

variable {α : Type*}

/-
**FreeMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `FreeMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (FreeMonoid α) where
  star := List.reverse
  star_involutive := List.reverse_reverse
  star_mul := fun _ _ => List.reverse_append

@[simp]
/-
**FreeMonoid.star_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：star_of (x : α) : star (of x) = of x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_of (x : α) : star (of x) = of x :=
  rfl

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp]
/-
**FreeMonoid.star_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：star_one : star (1 : FreeMonoid α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that `star_one` is already a global simp lemma, but this one works with dsi
mp too
-/
theorem star_one : star (1 : FreeMonoid α) = 1 :=
  rfl

end FreeMonoid

namespace FreeAlgebra

variable {R : Type*} [CommSemiring R] {X : Type*}

/-- The star ring formed by reversing the elements of products -/
/-
**FreeAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The star ring formed by reversing the elements of products
-/
instance : StarRing (FreeAlgebra R X) where
  star := MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive x := by
    simp only [Function.comp_apply]
    let y := lift R (X := X) (MulOpposite.op ∘ ι R)
    refine induction (motive := fun x ↦ (y (y x).unop).unop = x) _ _ ?_ ?_ ?_ ?_ x
    · intros
      simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
    · intros
      simp only [y, lift_ι_apply, Function.comp_apply, MulOpposite.unop_op]
    · intros
      simp only [*, map_mul, MulOpposite.unop_mul]
    · intros
      simp only [*, map_add, MulOpposite.unop_add]
  star_mul a b := by simp only [Function.comp_apply, map_mul, MulOpposite.unop_mul]
  star_add a b := by simp only [Function.comp_apply, map_add, MulOpposite.unop_add]

@[simp]
/-
**FreeAlgebra.star_** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_ι (x : X) : star (ι R x) = ι R x := by simp [star, Star.star]

@[simp]
/-
**FreeAlgebra.star_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `FreeAlgebra`。
形式化陈述：star_algebraMap (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebr
aMap R _ r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_algebraMap (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r := by
  simp [star, Star.star]

/-- `star` as an `AlgEquiv` -/
/-
**FreeAlgebra.starHom** 是 Mathlib 中的一个定义，位于命名空间 `FreeAlgebra`。
形式化陈述：starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`star` as an `AlgEquiv`
-/
def starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ :=
  { starRingEquiv with commutes' := fun r => by simp [star_algebraMap] }

end FreeAlgebra

