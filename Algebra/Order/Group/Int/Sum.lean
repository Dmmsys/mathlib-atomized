/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval

/-!
# Sharp bounds for sums of bounded finsets of integers

The sum of a finset of integers with cardinality `s` where all elements are at most `c` can be given
a sharper upper bound than `#s * c`, because the elements are distinct.

This file provides these sharp bounds, both in the upper-bounded and analogous lower-bounded cases.
-/

public section


namespace Finset

/-- Sharp upper bound for the sum of a finset of integers that is bounded above, `Ioc` version. -/
/-
**Finset.sum_le_sum_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_le_sum_Ioc {s : Finset Int} {c : Int} (hs : forall x in s, x <= c) : ∑
 x in s, x <= ∑ x in Ioc (c - #s) c, x
参数：hs : forall x in s, x <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_inter_add_sum_sdiff`：∀ {ι : Type u_1} {M : Type u_3} [inst : 
AddCommMonoid M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   ∑ x ∈ 
s ∩ t, f x + ∑ x ∈ s…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.card_sdiff_comm`：∀ {α : Type u_1} {s t : Finset α} [inst : Decida
bleEq α], s.card = t.card → (s \ t).card = (t \ s).card
· 使用定理 `Int.card_Ioc`：card_Ioc : #(Ioc a b) = (b - a).toNat
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
· 使用定理 `Finset.card_nsmul_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t

--- 原说明 ---
Sharp upper bound for the sum of a finset of integers that is bounded above, `Io
c` version.
-/
lemma sum_le_sum_Ioc {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, x ≤ c) :
    ∑ x ∈ s, x ≤ ∑ x ∈ Ioc (c - #s) c, x := by
  set r := Ioc (c - #s) c
  calc
    _ ≤ ∑ x ∈ s ∩ r, x + #(s \ r) • (c - #s) := by
      rw [← sum_inter_add_sum_sdiff s r _]
      gcongr
      apply sum_le_card_nsmul
      grind
    _ = ∑ x ∈ r ∩ s, x + #(r \ s) • (c - #s) := by
      rw [inter_comm, card_sdiff_comm]
      rw [Int.card_Ioc, sub_sub_cancel, Int.toNat_natCast]
    _ ≤ _ := by
      rw [← sum_inter_add_sum_sdiff r s _]
      gcongr
      refine card_nsmul_le_sum _ _ _ fun x mx ↦ ?_
      rw [mem_sdiff, mem_Ioc] at mx; exact mx.1.1.le

/-- Sharp upper bound for the sum of a finset of integers that is bounded above, `range` version. -/
/-
**Finset.sum_le_sum_range** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_le_sum_range {s : Finset Int} {c : Int} (hs : forall x in s, x <= c) :
 ∑ x in s, x <= ∑ n in range #s, (c - n)
参数：hs : forall x in s, x <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用引理 `Finset.sum_le_sum_Ioc`：sum_le_sum_Ioc {s : Finset Int} {c : Int} (hs : f
orall x in s, x <= c) : ∑ x in s, x <= ∑ x in Ioc (c - #s) c, x

--- 原说明 ---
Sharp upper bound for the sum of a finset of integers that is bounded above, `ra
nge` version.
-/
lemma sum_le_sum_range {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, x ≤ c) :
    ∑ x ∈ s, x ≤ ∑ n ∈ range #s, (c - n) := by
  convert! sum_le_sum_Ioc hs
  refine sum_nbij (c - ·) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro x mx; rw [mem_Ioc]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c - x = c - y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe, mem_Ioc] at mx
    use (c - x).toNat; grind

/-- Sharp lower bound for the sum of a finset of integers that is bounded below, `Ico` version. -/
/-
**Finset.sum_Ico_le_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_Ico_le_sum {s : Finset Int} {c : Int} (hs : forall x in s, c <= x) : ∑
 x in Ico c (c + #s), x <= ∑ x in s, x
参数：hs : forall x in s, c <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_inter_add_sum_sdiff`：∀ {ι : Type u_1} {M : Type u_3} [inst : 
AddCommMonoid M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   ∑ x ∈ 
s ∩ t, f x + ∑ x ∈ s…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.card_sdiff_comm`：∀ {α : Type u_1} {s t : Finset α} [inst : Decida
bleEq α], s.card = t.card → (s \ t).card = (t \ s).card
· 使用定理 `Int.card_Ico`：card_Ico : #(Ico a b) = (b - a).toNat
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
· 使用定理 `Finset.card_nsmul_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …

--- 原说明 ---
Sharp lower bound for the sum of a finset of integers that is bounded below, `Ic
o` version.
-/
lemma sum_Ico_le_sum {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, c ≤ x) :
    ∑ x ∈ Ico c (c + #s), x ≤ ∑ x ∈ s, x := by
  set r := Ico c (c + #s)
  calc
    _ ≤ ∑ x ∈ r ∩ s, x + #(r \ s) • (c + #s) := by
      grw [← sum_inter_add_sum_sdiff r s, ← sum_le_card_nsmul _ _ _ fun x mx ↦ ?_]
      rw [mem_sdiff, mem_Ico] at mx; exact mx.1.2.le
    _ = ∑ x ∈ s ∩ r, x + #(s \ r) • (c + #s) := by
      rw [inter_comm, card_sdiff_comm]
      rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]
    _ ≤ _ := by
      grw [← sum_inter_add_sum_sdiff s r, card_nsmul_le_sum _ _ _ fun x mx ↦ ?_]
      grind

/-- Sharp lower bound for the sum of a finset of integers that is bounded below, `range` version. -/
/-
**Finset.sum_range_le_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_range_le_sum {s : Finset Int} {c : Int} (hs : forall x in s, c <= x) :
 ∑ n in range #s, (c + n) <= ∑ x in s, x
参数：hs : forall x in s, c <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用引理 `Finset.sum_Ico_le_sum`：sum_Ico_le_sum {s : Finset Int} {c : Int} (hs : f
orall x in s, c <= x) : ∑ x in Ico c (c + #s), x <= ∑ x in s, x

--- 原说明 ---
Sharp lower bound for the sum of a finset of integers that is bounded below, `ra
nge` version.
-/
lemma sum_range_le_sum {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, c ≤ x) :
    ∑ n ∈ range #s, (c + n) ≤ ∑ x ∈ s, x := by
  convert! sum_Ico_le_sum hs
  refine sum_nbij (c + ·) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro x mx; rw [mem_Ico]; rw [mem_range] at mx; lia
  · intro x mx y my (h : c + x = c + y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe, mem_Ico] at mx
    use (x - c).toNat; grind

end Finset

