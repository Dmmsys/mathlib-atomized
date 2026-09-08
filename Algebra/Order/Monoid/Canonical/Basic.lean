/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# Extra lemmas about canonically ordered monoids
-/

public section

namespace Set
variable {α : Type*} [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {β : Type*} {f : α → β} {k : α}

/-
**Set.range_add_eq_image_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_add_eq_image_Ici : range (fun x => f (x + k)) = f '' Ici k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
-/
theorem range_add_eq_image_Ici : range (fun x ↦ f (x + k)) = f '' Ici k :=
  Set.ext fun x ↦ ⟨fun ⟨y, hfy⟩ ↦ ⟨y + k, self_le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ ↦ ⟨y - k, by simpa [tsub_add_cancel_of_le hy] using hfy⟩⟩

end Set

section LinearOrder
variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

section Add
variable [Add α] [CanonicallyOrderedAdd α]

/-
**lt_add_iff_lt_left_or_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_add_iff_lt_left_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
 a < b + c ↔ a < b ∨ exists d < c, a = b + d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `addLeftStrictMono_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : Add N] [
inst_1 : LinearOrder N] [AddLeftReflectLE N], AddLeftStrictMono N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lt_add_iff_lt_left_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < b ∨ ∃ d < c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp
/-
**forall_lt_add_iff_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] : (fora
ll a < b + c, P a) ↔ (forall a < b, P a) ∧ (forall d < c, P (b + d))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem forall_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∀ a < b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ d < c, P (b + d)) := by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop
/-
**exists_lt_add_iff_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] : (exis
ts a < b + c, P a) ↔ (exists a < b, P a) ∨ (exists d < c, P (b + d))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem exists_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∃ a < b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ d < c, P (b + d)) := by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop
/-
**le_add_iff_lt_left_or_exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_add_iff_lt_left_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] : a <=
 b + c ↔ a < b ∨ exists d <= c, a = b + d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_add_iff_lt_left_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] :
    a ≤ b + c ↔ a < b ∨ ∃ d ≤ c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a ≤ b + c := h.le.trans (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp
/-
**forall_le_add_iff_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] : (forall a 
<= b + c, P a) ↔ (forall a < b, P a) ∧ (forall d <= c, P (b + d))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem forall_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] :
    (∀ a ≤ b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ d ≤ c, P (b + d)) := by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop
/-
**exists_le_add_iff_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] : (exists a 
<= b + c, P a) ↔ (exists a < b, P a) ∨ (exists d <= c, P (b + d))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem exists_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] :
    (∃ a ≤ b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ d ≤ c, P (b + d)) := by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

end Add

section AddCommMagma
variable [AddCommMagma α] [CanonicallyOrderedAdd α]

/-
**lt_add_iff_lt_right_or_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_add_iff_lt_right_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] 
: a < b + c ↔ a < c ∨ exists d < b, a = d + c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `lt_add_iff_lt_left_or_exists_lt`：lt_add_iff_lt_left_or_exists_lt [AddLef
tReflectLT α] [IsLeftCancelAdd α] : a < b + c ↔ a < b ∨ exists d < c, a = b + d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_add_iff_lt_right_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < c ∨ ∃ d < b, a = d + c := by
  rw [add_comm, lt_add_iff_lt_left_or_exists_lt]
  simp_rw [add_comm]
/-
**forall_lt_add_iff_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] : (for
all a < b + c, P a) ↔ (forall a < c, P a) ∧ (forall d < b, P (d + c))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem forall_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∀ a < b + c, P a) ↔ (∀ a < c, P a) ∧ (∀ d < b, P (d + c)) := by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop
/-
**exists_lt_add_iff_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] : (exi
sts a < b + c, P a) ↔ (exists a < c, P a) ∨ (exists d < b, P (d + c))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem exists_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∃ a < b + c, P a) ↔ (∃ a < c, P a) ∨ (∃ d < b, P (d + c)) := by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop
/-
**le_add_iff_lt_right_or_exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_add_iff_lt_right_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] : a <
= b + c ↔ a < c ∨ exists d <= b, a = d + c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `le_add_iff_lt_left_or_exists_le`：le_add_iff_lt_left_or_exists_le [AddLef
tMono α] [IsLeftCancelAdd α] : a <= b + c ↔ a < b ∨ exists d <= c, a = b + d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_add_iff_lt_right_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] :
    a ≤ b + c ↔ a < c ∨ ∃ d ≤ b, a = d + c := by
  rw [add_comm, le_add_iff_lt_left_or_exists_le]
  simp_rw [add_comm]
/-
**forall_le_add_iff_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：forall_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] : (forall a
 <= b + c, P a) ↔ (forall a < c, P a) ∧ (forall d <= b, P (d + c))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem forall_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] :
    (∀ a ≤ b + c, P a) ↔ (∀ a < c, P a) ∧ (∀ d ≤ b, P (d + c)) := by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop
/-
**exists_le_add_iff_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] : (exists a
 <= b + c, P a) ↔ (exists a < c, P a) ∨ (exists d <= b, P (d + c))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem exists_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] :
    (∃ a ≤ b + c, P a) ↔ (∃ a < c, P a) ∨ (∃ d ≤ b, P (d + c)) := by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

end AddCommMagma
end LinearOrder

