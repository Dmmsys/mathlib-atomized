/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Big operators on a finset in the natural numbers

This file contains the results concerning the interaction of finset big operators with natural
numbers.
-/

public section

variable {ι : Type*}

namespace Finset

/-
**Finset.even_sum_iff_even_card_odd** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：even_sum_iff_even_card_odd {s : Finset ι} (f : ι -> Nat) : Even (∑ i in s,
 f i) ↔ Even #{x in s | Odd (f x)}
参数：f : ι -> Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `Nat.even_add`：∀ {m n : ℕ}, Even (m + n) ↔ (Even m ↔ Even n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用引理 `Nat.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
· 使用定理 `Finset.sum_nat_mod`：sum_nat_mod (s : Finset ι) (n : Nat) (f : ι -> Nat) 
: (∑ i in s, f i) % n = (∑ i in s, f i % n) % n
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma even_sum_iff_even_card_odd {s : Finset ι} (f : ι → ℕ) :
    Even (∑ i ∈ s, f i) ↔ Even #{x ∈ s | Odd (f x)} := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x ↦ Even (f x)), Nat.even_add]
  simp only [Finset.mem_filter, and_imp, imp_self, implies_true, Finset.even_sum, true_iff]
  rw [Nat.even_iff, Finset.sum_nat_mod, Finset.sum_filter]
  simp +contextual only [Nat.not_even_iff_odd, Nat.odd_iff.mp]
  simp_rw [← Finset.sum_filter, ← Nat.even_iff, Finset.card_eq_sum_ones]
/-
**Finset.odd_sum_iff_odd_card_odd** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：odd_sum_iff_odd_card_odd {s : Finset ι} (f : ι -> Nat) : Odd (∑ i in s, f 
i) ↔ Odd #{x in s | Odd (f x)}
参数：f : ι -> Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma odd_sum_iff_odd_card_odd {s : Finset ι} (f : ι → ℕ) :
    Odd (∑ i ∈ s, f i) ↔ Odd #{x ∈ s | Odd (f x)} := by
  simp only [← Nat.not_even_iff_odd, even_sum_iff_even_card_odd]
/-
**Finset.card_preimage_eq_sum_card_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_preimage_eq_sum_card_image_eq {M : Type*} {f : ι -> M} {s : Finset M}
 (hb : forall b in s, Set.Finite {a | f a = b}) : Nat.card (f ⁻¹' s) = ∑ b in s,
 Nat.card {a // f a = b}
参数：hb : forall b in s, Set.Finite {a | f a = b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinite_toFinset`：toFinite_toFinset (s : Set α) [Fintype s] : s.toF
inite.toFinset = s.toFinset
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.card_of_isEmpty`：∀ {α : Type u_1} [IsEmpty α], Nat.card α = 0
· 使用定理 `Set.Finite.preimage'`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β
}, s.Finite → (∀ b ∈ s, (f ⁻¹' {b}).Finite) → (f ⁻¹' s).Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用引理 `Nat.card_eq_card_finite_toFinset`：card_eq_card_finite_toFinset {s : Set 
α} (hs : s.Finite) : Nat.card s = hs.toFinset.card
· 使用定理 `Finset.card_eq_sum_card_image`：card_eq_sum_card_image [DecidableEq M] (f
 : ι -> M) (s : Finset ι) : #s = ∑ b in s.image f, #{a in s | f a = b}
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 33 条，此处仅展示前 30 条）
-/
theorem card_preimage_eq_sum_card_image_eq {M : Type*} {f : ι → M} {s : Finset M}
    (hb : ∀ b ∈ s, Set.Finite {a | f a = b}) :
    Nat.card (f ⁻¹' s) = ∑ b ∈ s, Nat.card {a // f a = b} := by
  classical
  -- `t = s ∩ Set.range f` as a `Finset`
  let t := (Set.finite_coe_iff.mp (Finite.Set.finite_inter_of_left ↑s (Set.range f))).toFinset
  rw [show Nat.card (f ⁻¹' s) = Nat.card (f ⁻¹' t) by simp [t]]
  rw [show ∑ b ∈ s, Nat.card {a //f a = b} = ∑ b ∈ t, Nat.card {a | f a = b} by
    exact (Finset.sum_subset (by simp [t]) (by aesop)).symm]
  have ht : Set.Finite (f ⁻¹' t) := Set.Finite.preimage' (finite_toSet t) (by aesop)
  rw [Nat.card_eq_card_finite_toFinset ht, Finset.card_eq_sum_card_image (f := f)]
  refine Finset.sum_congr ?_ fun m hm ↦ ?_
  · simpa [← Finset.coe_inj, t] using Set.image_preimage_eq_inter_range
  · rw [Nat.card_eq_card_finite_toFinset (hb _ (by aesop))]
    suffices {a | f a = m} ⊆ ht.toFinset from
      congr_arg (Finset.card ·) (Finset.ext_iff.mpr fun a ↦ by simpa using fun h ↦ this h)
    intro _ h
    simp_all

end Finset

