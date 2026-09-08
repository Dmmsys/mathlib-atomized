/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Order.Hom.Basic
/-!
# Lemmas about subtraction in unbundled canonically ordered monoids
-/

public section


variable {α β : Type*}

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α]

/-
**AddHom.le_map_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom
 α β) (hf : Monotone f) (a b : α) : f a - f b <= f (a - b)
参数：f : AddHom α β；hf : Monotone f；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 :
 Add N] (f : M →ₙ+ N) (a b : M), f (a + b) = f a + f b
· 使用定理 `le_tsub_add`：le_tsub_add : b <= b - a + a
-/
theorem AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom α β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) := by
  rw [tsub_le_iff_right, ← f.map_add]
  exact hf le_tsub_add
/-
**le_mul_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_tsub {R : Type*} [Distrib R] [Preorder R] [Sub R] [OrderedSub R] [M
ulLeftMono R] {a b c : R} : a * b - a * c <= a * (b - c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddHom.le_map_tsub`：AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [Ord
eredSub β] (f : AddHom α β) (hf : Monotone f) (a b : α) : f a - f b <= f (a - b)
· 使用定理 `Monotone.const_mul'`：Monotone.const_mul' [MulLeftMono α] (hf : Monotone 
f) (a : α) : Monotone fun x => a * f x
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem le_mul_tsub {R : Type*} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * b - a * c ≤ a * (b - c) :=
  (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _
/-
**le_tsub_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_tsub_mul {R : Type*} [NonUnitalCommSemiring R] [Preorder R] [Sub R] [Or
deredSub R] [MulLeftMono R] {a b c : R} : a * c - b * c <= (a - b) * c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `le_mul_tsub`：le_mul_tsub {R : Type*} [Distrib R] [Preorder R] [Sub R] [O
rderedSub R] [MulLeftMono R] {a b c : R} : a * b - a * c <= a * (b - c)
-/
theorem le_tsub_mul {R : Type*} [NonUnitalCommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * c - b * c ≤ (a - b) * c := by
  simpa only [mul_comm _ c] using le_mul_tsub

end Add

/-
**map_tsub_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_tsub_of_le {F : Type*} [PartialOrder α] [AddCommSemigroup α] [ExistsAd
dOfLE α] [AddLeftMono α] [Sub α] [OrderedSub α] [PartialOrder β] [AddCommSemigro
up β] [Sub β] [OrderedSub β] [AddLeftReflectLE β] [FunLike F α β] [AddHomClass F
 α β] (f : F) (a b : α) (h : b <= a) : f a - f b = f (a - b)
参数：f : F；a b : α；h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
-/
theorem map_tsub_of_le {F : Type*} [PartialOrder α] [AddCommSemigroup α] [ExistsAddOfLE α]
    [AddLeftMono α] [Sub α] [OrderedSub α] [PartialOrder β] [AddCommSemigroup β] [Sub β]
    [OrderedSub β] [AddLeftReflectLE β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : α) (h : b ≤ a) : f a - f b = f (a - b) := by
  conv => lhs; rw [← tsub_add_cancel_of_le h]
  rw [map_add, add_tsub_cancel_right]

/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
/-
**OrderIso.map_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_tsub {M N : Type*} [Preorder M] [Add M] [Sub M] [OrderedSub M
] [PartialOrder N] [Add N] [Sub N] [OrderedSub N] (e : M ≃o N) (h_add : forall a
 b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b
参数：e : M ≃o N；h_add : forall a b, e (a + b) = e a + e b；a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
· 使用定理 `AddHom.le_map_tsub`：AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [Ord
eredSub β] (f : AddHom α β) (hf : Monotone f) (a b : α) : f a - f b <= f (a - b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x

--- 原说明 ---
An order isomorphism between types with ordered subtraction preserves subtractio
n provided that
it preserves addition.
-/
theorem OrderIso.map_tsub {M N : Type*} [Preorder M] [Add M] [Sub M] [OrderedSub M]
    [PartialOrder N] [Add N] [Sub N] [OrderedSub N] (e : M ≃o N)
    (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b := by
  let e_add : M ≃+ N := { e with map_add' := h_add }
  refine le_antisymm ?_ (e_add.toAddHom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)) by simpa
  exact e.monotone (e_add.symm.toAddHom.le_map_tsub e.symm.monotone _ _)

/-! ### Preorder -/


section Preorder

variable [Preorder α]
variable [AddCommMonoid α] [Sub α] [OrderedSub α]

/-
**AddMonoidHom.le_map_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.le_map_tsub [Preorder β] [AddZeroClass β] [Sub β] [OrderedSub
 β] (f : α ->+ β) (hf : Monotone f) (a b : α) : f a - f b <= f (a - b)
参数：f : α ->+ β；hf : Monotone f；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddHom.le_map_tsub`：AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [Ord
eredSub β] (f : AddHom α β) (hf : Monotone f) (a b : α) : f a - f b <= f (a - b)
-/
theorem AddMonoidHom.le_map_tsub [Preorder β] [AddZeroClass β] [Sub β] [OrderedSub β] (f : α →+ β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) :=
  f.toAddHom.le_map_tsub hf a b

end Preorder

