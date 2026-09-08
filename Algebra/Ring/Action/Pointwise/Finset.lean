/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.Action.Pointwise.Set

/-!
# Pointwise actions on sets in a ring

This file proves properties of pointwise actions on sets in a ring.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

open Module
open scoped Pointwise

variable {R G M : Type*}

namespace Finset
section Semiring
variable [Semiring R] [IsDomain R] [AddCommMonoid M] [DecidableEq M] [Module R M]
  [IsTorsionFree R M] {s : Finset R} {t : Finset M} {r : R} {m : M}

/-
**Finset.zero_mem_smul_finset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：zero_mem_smul_finset_iff (hr : r != 0) : 0 in r • t ↔ 0 in t
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用引理 `Set.zero_mem_smul_set_iff`：zero_mem_smul_set_iff (ha : a != 0) : (0 : β)
 in a • t ↔ (0 : β) in t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma zero_mem_smul_finset_iff (hr : r ≠ 0) : 0 ∈ r • t ↔ 0 ∈ t := by
  rw [← mem_coe, coe_smul_finset, Set.zero_mem_smul_set_iff hr, mem_coe]
/-
**Finset.zero_mem_smul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：zero_mem_smul_iff : (0 : M) in s • t ↔ 0 in s ∧ t.Nonempty ∨ 0 in t ∧ s.No
nempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用引理 `Finset.coe_smul`：coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s 
: Set α) • (t : Set β)
· 使用引理 `Set.zero_mem_smul_iff`：zero_mem_smul_iff : 0 in s • t ↔ 0 in s ∧ t.Nonem
pty ∨ 0 in t ∧ s.Nonempty where mp | ⟨a, ha, b, hb, h⟩ => by obtain rfl | rfl
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma zero_mem_smul_iff : (0 : M) ∈ s • t ↔ 0 ∈ s ∧ t.Nonempty ∨ 0 ∈ t ∧ s.Nonempty := by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]; rfl

end Semiring

variable [Ring R] [AddCommGroup G] [Module R G] [DecidableEq G] {s : Finset R} {t : Finset G}
  {a : R}

/-
**Finset.neg_smul_finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {R : Type u_1} {G : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup G] 
[inst_2 : _root_.Module R G]   [inst_3 : DecidableEq G] {t : Finset G} {a : R}, 
-a • t = -(a • t)
参数：a • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg_eq_neg, image_image, neg_smul, Function.comp_def]
/-
**Finset.neg_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {R : Type u_1} {G : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup G] 
[inst_2 : _root_.Module R G]   [inst_3 : DecidableEq G] {s : Finset R} {t : Fins
et G} [inst_4 : DecidableEq R], -s • t = -(s • t)
参数：s • t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_image_left_comm`：image₂_image_left_comm {f : α' -> β -> γ}
 {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ} (h_left_comm : forall a b, f (g 
a) b = g' (f' a b))…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
-/
@[simp] protected lemma neg_smul [DecidableEq R] : -s • t = -(s • t) := by
  simp_rw [← image_neg_eq_neg]
  exact image₂_image_left_comm neg_smul

end Finset

