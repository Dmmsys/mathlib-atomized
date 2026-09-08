/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.Algebra.Star.Basic

/-!
# Helpers for working with star operators on quotients.

TODO: consider defining `Star` versions of `RingCon`.
-/

@[expose] public section

section Ring
variable {R : Type*} [NonUnitalNonAssocSemiring R] [StarRing R] {r : R → R → Prop}

/-
**RingConGen.Rel.star** 是 Mathlib 中的一个定理，位于命名空间 `RingConGen.Rel`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring R] [inst_1 : StarRing R
] {r : R → R → Prop},   (∀ (a b : R), r a b → r (star a) (star b)) → ∀ ⦃a b : R⦄
, RingConGen.Rel r a b → RingConGen.Rel r (star a) (star b)
参数：∀ (a b : R), r a b → r (star a) (star b)。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingConGen.Rel.brecOn`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] 
{r : R → R → Prop}   {motive : (a a_1 : R) → RingConGen.Rel r a a_1 → Prop} {a a
_1 : R} (t …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
-/
theorem RingConGen.Rel.star (hr : ∀ a b, r a b → r (star a) (star b))
    ⦃a b : R⦄ : Rel r a b → Rel r (star a) (star b)
  | refl _ => .refl _
  | symm h => .symm <| h.star hr
  | trans h1 h2 => .trans  (h1.star hr) (h2.star hr)
  | of _ _ h => .of _ _ (hr _ _ h)
  | mul h1 h2 => by
    rw [star_mul, star_mul]
    exact (h2.star hr).mul (h1.star hr)
  | add h1 h2 => by
    rw [star_add, star_add]
    exact (h1.star hr).add (h2.star hr)
/-
**ringConGen_star** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ringConGen_star (hr : forall a b, r a b -> r (star a) (star b)) ⦃a b : R⦄ 
: ringConGen r a b -> ringConGen r (star a) (star b)
参数：hr : forall a b, r a b -> r (star a) (star b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingConGen.Rel.star`：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring 
R] [inst_1 : StarRing R] {r : R → R → Prop},   (∀ (a b : R), r a b → r (star a) 
(star b))…
-/
theorem ringConGen_star (hr : ∀ a b, r a b → r (star a) (star b)) ⦃a b : R⦄ :
    ringConGen r a b → ringConGen r (star a) (star b) := (RingConGen.Rel.star hr ·)

end Ring

