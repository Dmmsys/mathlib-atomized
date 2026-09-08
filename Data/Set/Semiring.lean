/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, an alias of `Set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/

@[expose] public section


open Function Set

open scoped Pointwise

variable {α β : Type*}

/-- An alias for `Set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
/-
**SetSemiring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SetSemiring (α : Type*) : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alias for `Set α`, which has a semiring structure given by `∪` as "addition" 
and pointwise
  multiplication `*` as "multiplication".
-/
def SetSemiring (α : Type*) : Type _ :=
  Set α
deriving Inhabited, PartialOrder, OrderBot

/-- The identity function `Set α → SetSemiring α`. -/
/-
**Set.up** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_1} → Set α ≃ SetSemiring α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity function `Set α → SetSemiring α`.
-/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _

namespace SetSemiring

/-- The identity function `SetSemiring α → Set α`. -/
/-
**SetSemiring.down** 是 Mathlib 中的一个定义，位于命名空间 `SetSemiring`。
形式化陈述：{α : Type u_1} → SetSemiring α ≃ Set α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity function `SetSemiring α → Set α`.
-/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _

open SetSemiring (down)
open Set (up)

@[simp]
/-
**SetSemiring.down_up** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：∀ {α : Type u_1} (s : Set α), SetSemiring.down (Set.up s) = s
参数：s : Set α；Set.up s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem down_up (s : Set α) : s.up.down = s :=
  rfl

@[simp]
/-
**SetSemiring.up_down** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：∀ {α : Type u_1} (s : SetSemiring α), Set.up (SetSemiring.down s) = s
参数：s : SetSemiring α；SetSemiring.down s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem up_down (s : SetSemiring α) : s.down.up = s :=
  rfl

-- TODO: These lemmas should be tagged `simp`
/-
**SetSemiring.up_le_up** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：up_le_up {s t : Set α} : s.up <= t.up ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem up_le_up {s t : Set α} : s.up ≤ t.up ↔ s ⊆ t :=
  Iff.rfl
/-
**SetSemiring.up_lt_up** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t :=
  Iff.rfl

@[simp]
/-
**SetSemiring.down_subset_down** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：down_subset_down {s t : SetSemiring α} : s.down subseteq t.down ↔ s <= t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem down_subset_down {s t : SetSemiring α} : s.down ⊆ t.down ↔ s ≤ t :=
  Iff.rfl

@[simp]
/-
**SetSemiring.down_ssubset_down** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (SetSemiring α) where zero := (∅ : Set α).up
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (SetSemiring α) where add s t := (s.down ∪ t.down).up
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (SetSemiring α) where
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  nsmul := nsmulRec
/-
**SetSemiring.zero_def** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：zero_def : (0 : SetSemiring α) = Set.up ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_def : (0 : SetSemiring α) = Set.up ∅ :=
  rfl

@[simp]
/-
**SetSemiring.down_zero** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：down_zero : (0 : SetSemiring α).down = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_zero : (0 : SetSemiring α).down = ∅ :=
  rfl

@[simp]
/-
**SetSemiring._root_.Set.up_empty** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.up_empty : (∅ : Set α).up = 0 :=
  rfl
/-
**SetSemiring.add_def** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：add_def (s t : SetSemiring α) : s + t = (s.down union t.down).up
参数：s t : SetSemiring α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_def (s t : SetSemiring α) : s + t = (s.down ∪ t.down).up :=
  rfl

@[simp]
/-
**SetSemiring.down_add** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：down_add (s t : SetSemiring α) : (s + t).down = s.down union t.down
参数：s t : SetSemiring α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_add (s t : SetSemiring α) : (s + t).down = s.down ∪ t.down :=
  rfl

@[simp]
/-
**SetSemiring._root_.Set.up_union** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.up_union (s t : Set α) : (s ∪ t).up = s.up + t.up :=
  rfl

/-- Since addition on `SetSemiring` is commutative (it is set union), there is no need
to also have the instance `AddRightMono (SetSemiring α)`. -/
/-
**SetSemiring.addLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
形式化陈述：addLeftMono : AddLeftMono (SetSemiring α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂

--- 原说明 ---
Since addition on `SetSemiring` is commutative (it is set union), there is no ne
ed
to also have the instance `AddRightMono (SetSemiring α)`.
-/
instance addLeftMono : AddLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => union_subset_union_right _⟩

section Mul

variable [Mul α]

/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalNonAssocSemiring (SetSemiring α) where
  mul := fun s t => (image2 (· * ·) s.down t.down).up
  zero_mul := fun _ => empty_mul
  mul_zero := fun _ => mul_empty
  left_distrib := fun _ _ _ => mul_union
  right_distrib := fun _ _ _ => union_mul
/-
**SetSemiring.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：mul_def (s t : SetSemiring α) : s * t = (s.down * t.down).up
参数：s t : SetSemiring α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (s t : SetSemiring α) : s * t = (s.down * t.down).up :=
  rfl

@[simp]
/-
**SetSemiring.down_mul** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：down_mul (s t : SetSemiring α) : (s * t).down = s.down * t.down
参数：s t : SetSemiring α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_mul (s t : SetSemiring α) : (s * t).down = s.down * t.down :=
  rfl

@[simp]
/-
**SetSemiring._root_.Set.up_mul** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.up_mul (s t : Set α) : (s * t).up = s.up * t.up :=
  rfl
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun {a b} ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩
/-
**SetSemiring.mulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
形式化陈述：mulLeftMono : MulLeftMono (SetSemiring α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
-/
instance mulLeftMono : MulLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_left⟩
/-
**SetSemiring.mulRightMono** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
形式化陈述：mulRightMono : MulRightMono (SetSemiring α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mul_subset_mul_right`：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * 
t subseteq s₂ * t
-/
instance mulRightMono : MulRightMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_right⟩

end Mul


section One

variable [One α]

/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (SetSemiring α) where one := (1 : Set α).up
/-
**SetSemiring.one_def** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：one_def : (1 : SetSemiring α) = Set.up 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : SetSemiring α) = Set.up 1 :=
  rfl

@[simp]
/-
**SetSemiring.down_one** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
形式化陈述：down_one : (1 : SetSemiring α).down = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_one : (1 : SetSemiring α).down = 1 :=
  rfl

@[simp]
/-
**SetSemiring._root_.Set.up_one** 是 Mathlib 中的一个定理，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.up_one : (1 : Set α).up = 1 :=
  rfl

end One

/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass α] : MulOneClass (SetSemiring α) :=
  inferInstanceAs <| MulOneClass (Set α)
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) where
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup α] : Semigroup (SetSemiring α) :=
  inferInstanceAs <| Semigroup (Set α)
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) where
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteBooleanAlgebra (SetSemiring α) :=
  inferInstanceAs <| CompleteBooleanAlgebra (Set α)
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [Monoid α] : IdemSemiring (SetSemiring α) :=
  { (inferInstance : NonAssocSemiring (SetSemiring α)),
    (inferInstance : NonUnitalSemiring (SetSemiring α)),
    (inferInstance : CompleteBooleanAlgebra (SetSemiring α)) with }
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemigroup α] : CommSemigroup (SetSemiring α) :=
  inferInstanceAs <| CommSemigroup (Set α)
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) where
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CommMonoid α] : CommMonoid (SetSemiring α) :=
  inferInstanceAs <| CommMonoid (Set α)
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) where
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanonicallyOrderedAdd (SetSemiring α) where
  exists_add_of_le {_ b} ab := ⟨b, (union_eq_right.2 ab).symm⟩
  le_add_self _ _ := subset_union_right
  le_self_add _ _ := subset_union_left
/-
**SetSemiring.** 是 Mathlib 中的一个实例，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CommMonoid α] : IsOrderedRing (SetSemiring α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/-- If `α` is a monoid, the map that sends `a : α` to
the singleton set `{a}` is a monoid homomorphism. -/
/-
**SetSemiring.singletonMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `SetSemiring`。
形式化陈述：singletonMonoidHom [Monoid α] : α ->* SetSemiring α where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a monoid, the map that sends `a : α` to
the singleton set `{a}` is a monoid homomorphism.
-/
noncomputable def singletonMonoidHom [Monoid α] : α →* SetSemiring α where
  toFun a := up {a}
  map_one' := rfl
  map_mul' _ _ := image2_singleton.symm

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
/-
**SetSemiring.imageHom** 是 Mathlib 中的一个定义，位于命名空间 `SetSemiring`。
形式化陈述：imageHom [MulOneClass α] [MulOneClass β] (f : α ->* β) : SetSemiring α ->+
* SetSemiring β where toFun s
参数：f : α ->* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets.
-/
noncomputable def imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) :
    SetSemiring α →+* SetSemiring β where
  toFun s := (image f s.down).up
  map_zero' := image_empty _
  map_one' := by
    rw [down_one, image_one, map_one, singleton_one, up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f
/-
**SetSemiring.imageHom_def** 是 Mathlib 中的一个引理，位于命名空间 `SetSemiring`。
形式化陈述：imageHom_def [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemirin
g α) : imageHom f s = (image f s.down).up
参数：f : α ->* β；s : SetSemiring α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma imageHom_def [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    imageHom f s = (image f s.down).up :=
  rfl

@[simp]
/-
**SetSemiring.down_imageHom** 是 Mathlib 中的一个引理，位于命名空间 `SetSemiring`。
形式化陈述：down_imageHom [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemiri
ng α) : (imageHom f s).down = f '' s.down
参数：f : α ->* β；s : SetSemiring α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma down_imageHom [MulOneClass α] [MulOneClass β] (f : α →* β) (s : SetSemiring α) :
    (imageHom f s).down = f '' s.down :=
  rfl

@[simp]
/-
**SetSemiring._root_.Set.up_image** 是 Mathlib 中的一个引理，位于命名空间 `SetSemiring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.up_image [MulOneClass α] [MulOneClass β] (f : α →* β) (s : Set α) :
    (f '' s).up = imageHom f s.up :=
  rfl

end SetSemiring

