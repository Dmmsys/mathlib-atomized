/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Pointwise operations of sets in a ring

This file proves properties of pointwise operations of sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

assert_not_exists IsOrderedMonoid Field

open Function
open scoped Pointwise

variable {α β : Type*}

namespace Set

section DistribSMul
variable [AddGroup β] [DistribSMul α β] (a : α) (s : Set α) (t : Set β)

@[simp]
/-
**Set.smul_set_neg** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_neg : a • -t = -(a • t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, smul_neg]

@[simp]
/-
**Set.smul_neg** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : AddGroup β] [inst_1 : DistribSMul 
α β] (s : Set α) (t : Set β),   s • -t = -(s • t)
参数：s : Set α；t : Set β；s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image2_right_comm`：image_image2_right_comm {f : α -> β' -> γ} 
{g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ} (h_right_comm : forall a b, f a (
g b) = g' (f' a b…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
protected lemma smul_neg : s • -t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image_image2_right_comm smul_neg

end DistribSMul

section Semiring
variable [Semiring α] [AddCommMonoid β] [Module α β]

/-
**Set.add_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：add_smul_subset (a b : α) (s : Set β) : (a + b) • s subseteq a • s + b • s
参数：a b : α；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
lemma add_smul_subset (a b : α) (s : Set β) : (a + b) • s ⊆ a • s + b • s := by
  rintro _ ⟨x, hx, rfl⟩
  simpa only [add_smul] using add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hx)

variable [IsDomain α] [Module.IsTorsionFree α β] {a : α} {s : Set α} {t : Set β}
/-
**Set.zero_mem_smul_set_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：zero_mem_smul_set_iff (ha : a != 0) : (0 : β) in a • t ↔ (0 : β) in t
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Set.zero_mem_smul_set`：zero_mem_smul_set (h : (0 : β) in t) : (0 : β) in
 a • t
-/
lemma zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t := by
  refine ⟨?_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(smul_eq_zero.1 h).resolve_left ha] at hb
/-
**Set.zero_mem_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：zero_mem_smul_iff : 0 in s • t ↔ 0 in s ∧ t.Nonempty ∨ 0 in t ∧ s.Nonempty
 where mp | ⟨a, ha, b, hb, h⟩ => by obtain rfl | rfl
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma zero_mem_smul_iff : 0 ∈ s • t ↔ 0 ∈ s ∧ t.Nonempty ∨ 0 ∈ t ∧ s.Nonempty where
  mp | ⟨a, ha, b, hb, h⟩ => by
      obtain rfl | rfl := smul_eq_zero.1 h; exacts [.inl ⟨ha, b, hb⟩, .inr ⟨hb, a, ha⟩]
  mpr
  | .inl ⟨hs, b, hb⟩ => ⟨0, hs, b, hb, zero_smul _ _⟩
  | .inr ⟨ht, a, ha⟩ => ⟨a, ha, 0, ht, smul_zero _⟩

end Semiring

section Ring
variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

@[simp]
/-
**Set.neg_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：neg_smul_set : -a • t = -(a • t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg_eq_neg, image_image, neg_smul]

@[simp]
/-
**Set.neg_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Ring α] [inst_1 : AddCommGroup β] 
[inst_2 : _root_.Module α β] (s : Set α)   (t : Set β), -s • t = -(s • t)
参数：s : Set α；t : Set β；s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image2_image_left_comm`：image2_image_left_comm {f : α' -> β -> γ} {g
 : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ} (h_left_comm : forall a b, f (g a) 
b = g' (f' a b))…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
-/
protected lemma neg_smul : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image2_image_left_comm neg_smul

end Ring
end Set

