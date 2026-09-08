/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Hom.Ring

/-!
### Uniqueness of ring homomorphisms to archimedean fields.

There is at most one ordered ring homomorphism from a linear ordered field to an archimedean linear
ordered field. Reciprocally, such an ordered ring homomorphism exists when the codomain is further
conditionally complete.
-/

public section

assert_not_exists Finset

variable {α β : Type*} [Field α] [LinearOrder α] [Field β] [LinearOrder β]

/-- There is at most one ordered ring homomorphism from a linear ordered field to an archimedean
linear ordered field. -/
/-
**OrderRingHom.subsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderRingHom.subsingleton [IsStrictOrderedRing β] [Archimedean β] : Subsin
gleton (α ->+*o β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.ext`：ext {f g : α ->+*o β} (h : forall a, f a = g a) : f = 
g
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `OrderRingHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : 
NonAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_
3 : Preorder β], Ord…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a

--- 原说明 ---
There is at most one ordered ring homomorphism from a linear ordered field to an
 archimedean
linear ordered field.
-/
instance OrderRingHom.subsingleton [IsStrictOrderedRing β] [Archimedean β] :
    Subsingleton (α →+*o β) :=
  ⟨fun f g => by
    ext x
    by_contra h' : f x ≠ g x
    wlog h : f x < g x with h₂
    · exact h₂ g f x (Ne.symm h') (h'.lt_or_gt.resolve_left h)
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    rw [← map_ratCast f] at hf
    rw [← map_ratCast g] at hg
    exact
      (lt_asymm ((OrderHomClass.mono g).reflect_lt hg) <|
          (OrderHomClass.mono f).reflect_lt hf).elim⟩

/-- There is at most one ordered ring isomorphism between a linear ordered field and an archimedean
linear ordered field. -/
/-
**OrderRingIso.subsingleton_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderRingIso.subsingleton_right [IsStrictOrderedRing β] [Archimedean β] : 
Subsingleton (α ≃+*o β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `OrderRingIso.toOrderRingHom_injective`：toOrderRingHom_injective : Inject
ive (toOrderRingHom : α ≃+*o β -> α ->+*o β)

--- 原说明 ---
There is at most one ordered ring isomorphism between a linear ordered field and
 an archimedean
linear ordered field.
-/
instance OrderRingIso.subsingleton_right [IsStrictOrderedRing β] [Archimedean β] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.toOrderRingHom_injective.subsingleton

/-- There is at most one ordered ring isomorphism between an archimedean linear ordered field and a
linear ordered field. -/
/-
**OrderRingIso.subsingleton_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderRingIso.subsingleton_left [IsStrictOrderedRing α] [Archimedean α] : S
ubsingleton (α ≃+*o β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `OrderRingIso.symm_bijective`：symm_bijective : Bijective (OrderRingIso.sy
mm : (α ≃+*o β) -> β ≃+*o α)

--- 原说明 ---
There is at most one ordered ring isomorphism between an archimedean linear orde
red field and a
linear ordered field.
-/
instance OrderRingIso.subsingleton_left [IsStrictOrderedRing α] [Archimedean α] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.symm_bijective.injective.subsingleton
/-
**OrderRingHom.eq_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderRingHom.eq_id [IsStrictOrderedRing α] [Archimedean α] (f : α ->+*o α)
 : f = .id _
参数：f : α ->+*o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem OrderRingHom.eq_id [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) : f = .id _ :=
  Subsingleton.elim ..
/-
**OrderRingIso.eq_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderRingIso.eq_refl [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α
) : f = .refl _
参数：f : α ≃+*o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem OrderRingIso.eq_refl [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) : f = .refl _ :=
  Subsingleton.elim ..
/-
**OrderRingHom.apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderRingHom.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α 
->+*o α) (x : α) : f x = x
参数：f : α ->+*o α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderRingHom.eq_id`：OrderRingHom.eq_id [IsStrictOrderedRing α] [Archimed
ean α] (f : α ->+*o α) : f = .id _
-/
theorem OrderRingHom.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) (x : α) :
    f x = x := by
  rw [f.eq_id]; rfl
/-
**OrderRingIso.apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderRingIso.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α 
≃+*o α) (x : α) : f x = x
参数：f : α ≃+*o α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingHom.apply_eq_self`：OrderRingHom.apply_eq_self [IsStrictOrderedR
ing α] [Archimedean α] (f : α ->+*o α) (x : α) : f x = x
-/
theorem OrderRingIso.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) (x : α) :
    f x = x :=
  f.toOrderRingHom.apply_eq_self x
