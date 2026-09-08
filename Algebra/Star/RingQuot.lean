/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.RingQuot
public import Mathlib.Algebra.Star.Basic

/-!
# The \*-ring structure on suitable quotients of a \*-ring.
-/

public section

namespace RingQuot

universe u

variable {R : Type u} [Semiring R] (r : R → R → Prop)

section StarRing

variable [StarRing R]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**RingQuot.Rel.star** 是 Mathlib 中的一个定理，位于命名空间 `RingQuot.Rel`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] (r : R → R → Prop) [inst_1 : StarRing R
],   (∀ (a b : R), r a b → r (star a) (star b)) → ∀ ⦃a b : R⦄, RingQuot.Rel r a 
b → RingQuot.Rel r (star a) (star b)
参数：r : R → R → Prop；∀ (a b : R), r a b → r (star a) (star b)。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
-/
theorem Rel.star (hr : ∀ a b, r a b → r (star a) (star b))
    ⦃a b : R⦄ (h : Rel r a b) : Rel r (star a) (star b) := by
  induction h with
  | of h          => exact Rel.of (hr _ _ h)
  | add_left _ h  => rw [star_add, star_add]
                     exact Rel.add_left h
  | mul_left _ h  => rw [star_mul, star_mul]
                     exact Rel.mul_right h
  | mul_right _ h => rw [star_mul, star_mul]
                     exact Rel.mul_left h
/-
**RingQuot.star'** 是 Mathlib 中的一个定义，位于命名空间 `RingQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def star' (hr : ∀ a b, r a b → r (star a) (star b)) : RingQuot r → RingQuot r
  | ⟨a⟩ => ⟨Quot.map (star : R → R) (Rel.star r hr) a⟩
/-
**RingQuot.star'_quot** 是 Mathlib 中的一个定理，位于命名空间 `RingQuot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem star'_quot (hr : ∀ a b, r a b → r (star a) (star b)) {a} :
    (star' r hr ⟨Quot.mk _ a⟩ : RingQuot r) = ⟨Quot.mk _ (star a)⟩ := rfl

/-- Transfer a `StarRing` instance through a quotient, if the quotient is invariant to `star` -/
@[instance_reducible]
/-
**RingQuot.starRing** 是 Mathlib 中的一个定义，位于命名空间 `RingQuot`。
形式化陈述：starRing {R : Type u} [Semiring R] [StarRing R] (r : R -> R -> Prop) (hr :
 forall a b, r a b -> r (star a) (star b)) : StarRing (RingQuot r) where star
参数：r : R -> R -> Prop；hr : forall a b, r a b -> r (star a) (star b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a `StarRing` instance through a quotient, if the quotient is invariant 
to `star`
-/
def starRing {R : Type u} [Semiring R] [StarRing R] (r : R → R → Prop)
    (hr : ∀ a b, r a b → r (star a) (star b)) : StarRing (RingQuot r) where
  star := star' r hr
  star_involutive := by
    rintro ⟨⟨⟩⟩
    simp [star'_quot]
  star_mul := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, mul_quot, star_mul]
  star_add := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, add_quot, star_add]

end StarRing

end RingQuot

