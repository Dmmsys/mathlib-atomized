/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Setoid.Partition

/-! # Cardinality of parts of partitions

* `Setoid.IsPartition.ncard_eq_finsum` on an ambient finite type,
  the cardinal of a set is the sum of the cardinalities of its trace on the parts of the partition

-/

public section

section Finite

/-- Given a partition of the ambient type, the cardinal of a finite set
  is the `finsum` of the cardinalities of its traces on the parts of the partition -/
/-
**Setoid.IsPartition.ncard_eq_finsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Setoid.IsPartition.ncard_eq_finsum {α : Type*} {P : Set (Set α)} (hP : Set
oid.IsPartition P) (s : Set α) (hs : s.Finite
参数：Set α；hP : Setoid.IsPartition P；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用引理 `Nat.card_eq_card_finite_toFinset`：card_eq_card_finite_toFinset {s : Set 
α} (hs : s.Finite) : Nat.card s = hs.toFinset.card
· 使用定理 `Set.nonempty_of_ncard_ne_zero`：nonempty_of_ncard_ne_zero (hs : s.ncard !
= 0) : s.Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_def`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] (f 
: α → M) [inst_1 : Decidable (Function.HasFiniteSupport f)],   ∑ᶠ (i : α), f i =
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_sigma`：card_sigma {σ : α -> Type*} (s : Finset α) (t : foral
l a, Finset (σ a)) : #(s.sigma t) = ∑ a in s, #(t a)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Finset.card_nbij'`：card_nbij' (i : α -> β) (j : β -> α) (hi : Set.MapsTo
 i s t) (hj : Set.MapsTo j t s) (left_inv : Set.LeftInvOn j i s) (right_inv : Se
t.Right…
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_sigma`：coe_sigma (s : Finset ι) (t : forall i, Finset (α i)) 
: (s.sigma t : Set (Σ i, α i)) = (s : Set ι).sigma fun i => (t i : Set (α i))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Given a partition of the ambient type, the cardinal of a finite set
  is the `finsum` of the cardinalities of its traces on the parts of the partiti
on
-/
theorem Setoid.IsPartition.ncard_eq_finsum {α : Type*} {P : Set (Set α)}
    (hP : Setoid.IsPartition P) (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = finsum fun t : P => (s ∩ t).ncard := by
  classical
  have hst (t : Set α) : (s ∩ t).Finite := hs.inter_of_left t
  have hst' (t : Set α) : Nat.card ↑(s ∩ t) = (hst t).toFinset.card :=
    Nat.card_eq_card_finite_toFinset (hst t)
  suffices hs' : _ by
    rw [finsum_def, dif_pos hs']
    simp only [← Nat.card_coe_set_eq, Nat.card_eq_card_finite_toFinset hs]
    rw [Finset.sum_congr rfl (fun t ht ↦ by exact hst' ↑t)]
    rw [← Finset.card_sigma, eq_comm]
    apply Finset.card_nbij' (fun ⟨t, x⟩ ↦ x)
      (fun x ↦ ⟨⟨(hP.2 x).exists.choose, (hP.2 x).exists.choose_spec.1⟩, x⟩)
    · rintro ⟨t, x⟩
      simp +contextual
    · intro x
      simp only [Set.Finite.mem_toFinset, Finset.mem_sigma, Function.mem_support, Set.mem_inter_iff,
        Finset.mem_coe]
      intro hx
      refine ⟨Nat.card_ne_zero.mpr ⟨?_, hst (hP.right x).exists.choose⟩,
        hx, (hP.2 x).exists.choose_spec.2⟩
      simp only [nonempty_subtype, Set.mem_inter_iff]
      use x, hx, (hP.2 x).exists.choose_spec.2
    · rintro ⟨t, x⟩
      simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Function.mem_support, Nat.card_ne_zero,
        Set.mem_inter_iff, Sigma.mk.inj_iff, heq_eq_eq, and_true, and_imp, Finset.mem_coe]
      simp only [nonempty_subtype, Set.mem_inter_iff, forall_exists_index, and_imp]
      intro y hy hyt _ hxs hxt
      rw [← Subtype.coe_inj]
      exact (hP.2 x).unique (hP.2 x).exists.choose_spec ⟨t.prop, hxt⟩
    · intro t
      simp only [implies_true]
  let f : Function.support (fun (t : P) ↦ (s ∩ (t : Set α)).ncard) → s := fun ⟨t, ht⟩ ↦
    ⟨(Set.nonempty_of_ncard_ne_zero ht).choose, (Set.nonempty_of_ncard_ne_zero ht).choose_spec.1⟩
  have hf (t : Function.support (fun (t : P) ↦ (s ∩ (t : Set α)).ncard)) :
      ↑↑t ∈ P ∧ (f t : α) ∈ (t : Set α) :=
    ⟨(↑t : P).prop, (Set.nonempty_of_ncard_ne_zero t.prop).choose_spec.2⟩
  have : Finite ↑s := hs
  apply Finite.of_injective f
  intro t t' h
  simp only [← Subtype.coe_inj]
  exact (hP.2 (f t)).unique (hf t) (h ▸ hf t')

end Finite

