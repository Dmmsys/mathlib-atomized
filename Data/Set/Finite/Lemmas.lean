/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Embedding.Set

/-!
# Lemmas on finiteness of sets

This file should contain lemmas that prove some result under the *assumption* of `Set.Finite`.
If your proof has as *result* `Set.Finite`, then it should go to a more specific file.

## Tags

finite sets
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Properties -/

/-
**Set.Finite.fin_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∃ n f, Set.range ⇑f = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.asEmbedding_range`：Equiv.asEmbedding_range {α β : Sort _} {p : β -
> Prop} (e : α ≃ Subtype p) : Set.range e.asEmbedding = Set.ofPred p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Properties
-/
theorem Finite.fin_embedding {s : Set α} (h : s.Finite) :
    ∃ (n : ℕ) (f : Fin n ↪ α), range f = s :=
  ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by
    simp only [Finset.coe_sort_coe, Equiv.asEmbedding_range, Finite.coe_toFinset, ofPred_mem_eq]⟩
/-
**Set.Finite.fin_param** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {s : Set α}, s.Finite → ∃ n f, Function.Injective f ∧ Set.r
ange f = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.fin_embedding`：∀ {α : Type u} {s : Set α}, s.Finite → ∃ n f, 
Set.range ⇑f = s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem Finite.fin_param {s : Set α} (h : s.Finite) :
    ∃ (n : ℕ) (f : Fin n → α), Injective f ∧ range f = s :=
  let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.injective, hf⟩

/-- Induction up to a finite set `S`. -/
/-
**Set.Finite.induction_to** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} {C : Set α → Prop} {S : Set α},   S.Finite → ∀ S0 ⊆ S, C S0
 → (∀ s ⊂ S, C s → ∃ a ∈ S \ s, C (insert a s)) → C S
参数：∀ s ⊂ S, C s → ∃ a ∈ S \ s, C (insert a s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `WellFounded.induction_bot'`：WellFounded.induction_bot' {α β} {r : α -> α
 -> Prop} (hwf : WellFounded r) {a bot : α} {C : β -> Prop} {f : α -> β} (ih : f
orall b, f b != …
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `ssubset_of_ne_of_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [i
nst : PartialOrder α] {a b : α}, a ≠ b → a ⊆ b → a ⊂ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Set.ssubset_insert`：ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂
 insert a s

--- 原说明 ---
Induction up to a finite set `S`.
-/
theorem Finite.induction_to {C : Set α → Prop} {S : Set α} (h : S.Finite)
    (S0 : Set α) (hS0 : S0 ⊆ S) (H0 : C S0) (H1 : ∀ s ⊂ S, C s → ∃ a ∈ S \ s, C (insert a s)) :
    C S := by
  have : Finite S := Finite.to_subtype h
  have : Finite {T : Set α // T ⊆ S} := Finite.of_equiv (Set S) (Equiv.Set.powerset S).symm
  rw [← Subtype.coe_mk (p := (· ⊆ S)) _ le_rfl]
  rw [← Subtype.coe_mk (p := (· ⊆ S)) _ hS0] at H0
  refine Finite.to_wellFoundedGT.wf.induction_bot' (fun s hs hs' ↦ ?_) H0
  obtain ⟨a, ⟨ha1, ha2⟩, ha'⟩ := H1 s (ssubset_of_ne_of_subset hs s.2) hs'
  exact ⟨⟨insert a s.1, insert_subset ha1 s.2⟩, Set.ssubset_insert ha2, ha'⟩

/-- Induction up to `univ`. -/
/-
**Set.Finite.induction_to_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u} [Finite α] {C : Set α → Prop} (S0 : Set α),   C S0 → (∀ (S 
: Set α), S ≠ Set.univ → C S → ∃ a ∉ S, C (insert a S)) → C Set.univ
参数：S0 : Set α；∀ (S : Set α), S ≠ Set.univ → C S → ∃ a ∉ S, C (insert a S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_to`：∀ {α : Type u} {C : Set α → Prop} {S : Set α}, 
  S.Finite → ∀ S0 ⊆ S, C S0 → (∀ s ⊂ S, C s → ∃ a ∈ S \ s, C (insert a s)) → C S
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
Induction up to `univ`.
-/
theorem Finite.induction_to_univ [Finite α] {C : Set α → Prop} (S0 : Set α)
    (H0 : C S0) (H1 : ∀ S ≠ univ, C S → ∃ a ∉ S, C (insert a S)) : C univ :=
  finite_univ.induction_to S0 (subset_univ S0) H0 (by simpa [ssubset_univ_iff])
/-
**Set.sUnion_finite_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：sUnion_finite_eq_univ {X : Type*} : ⋃₀ {(s : Set X) | Set.Finite s} = Set.
univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sUnion_eq_univ_iff`：sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀ c = un
iv ↔ forall a, exists b in c, a in b
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem sUnion_finite_eq_univ {X : Type*} : ⋃₀ {(s : Set X) | Set.Finite s} = Set.univ :=
  sUnion_eq_univ_iff.mpr fun x ↦ ⟨{x}, finite_singleton x, rfl⟩

/-! ### Infinite sets -/

variable {s t : Set α}

/-! ### Order properties -/

/-
**Set.exists_min_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : LinearOrder β] (s : Set α) (f : α → β)
,   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
参数：s : Set α；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.exists_min_image`：exists_min_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x <= f x'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s

--- 原说明 ---
### Order properties
-/
theorem exists_min_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_min_image f ⟨x, h1.mem_toFinset.2 hx⟩
/-
**Set.exists_max_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : LinearOrder β] (s : Set α) (f : α → β)
,   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
参数：s : Set α；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.exists_max_image`：exists_max_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x' <= f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem exists_max_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, Finite.mem_toFinset] using
      h1.toFinset.exists_max_image f ⟨x, h1.mem_toFinset.2 hx⟩
/-
**Set.exists_lower_bound_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_lower_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α -
> β) (h : s.Finite) : exists a : α, forall b in s, f a <= f b
参数：s : Set α；f : α -> β；h : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.exists_min_image`：∀ {α : Type u} {β : Type v} [inst : LinearOrder β]
 (s : Set α) (f : α → β),   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
-/
theorem exists_lower_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f a ≤ f b := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ‹Nonempty α›.elim fun a => ⟨a, fun _ => False.elim⟩
  · rcases Set.exists_min_image s f h hs with ⟨x₀, _, hx₀⟩
    exact ⟨x₀, fun x hx => hx₀ x hx⟩
/-
**Set.exists_upper_bound_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_upper_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α -
> β) (h : s.Finite) : exists a : α, forall b in s, f b <= f a
参数：s : Set α；f : α -> β；h : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_lower_bound_image`：exists_lower_bound_image [Nonempty α] [Lin
earOrder β] (s : Set α) (f : α -> β) (h : s.Finite) : exists a : α, forall b in 
s, f a <= f b
-/
theorem exists_upper_bound_image [Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f b ≤ f a :=
  exists_lower_bound_image (β := βᵒᵈ) s f h

end Set

