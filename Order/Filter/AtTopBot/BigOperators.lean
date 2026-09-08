/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Preimage
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Two lemmas about limit of `Π b ∈ s, f b` along

In this file we prove two auxiliary lemmas
about `Filter.atTop : Filter (Finset _)` and `∏ b ∈ s, f b`.
These lemmas are useful to build the theory of absolutely convergent series.
-/

public section

open Filter Finset

variable {α β M : Type*} [CommMonoid M]

/-- Let `f` and `g` be two maps to the same commutative monoid. This lemma gives a sufficient
condition for comparison of the filter `atTop.map (fun s ↦ ∏ b ∈ s, f b)` with
`atTop.map (fun s ↦ ∏ b ∈ s, g b)`. This is useful to compare the set of limit points of
`Π b in s, f b` as `s → atTop` with the similar set for `g`. -/
@[to_additive /-- Let `f` and `g` be two maps to the same commutative additive monoid. This lemma
gives a sufficient condition for comparison of the filter `atTop.map (fun s ↦ ∑ b ∈ s, f b)` with
`atTop.map (fun s ↦ ∑ b ∈ s, g b)`. This is useful to compare the set of limit points of
`∑ b ∈ s, f b` as `s → atTop` with the similar set for `g`. -/]
/-
**Filter.map_atTop_finsetProd_le_of_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_atTop_finsetProd_le_of_prod_eq {f : α -> M} {g : β -> M} (h_eq 
: forall u : Finset β, exists v : Finset α, forall v', v subseteq v' -> exists u
', u subseteq u' ∧ ∏ x in u', g x = ∏ b in v', f b) : (atTop.map fun s : Finset 
α => ∏ b in s, f b) <= atTop.map fun s : Finset β => ∏ x in s, g x
参数：h_eq : forall u : Finset β, exists v : Finset α, forall v', v subseteq v' -> 
exists u', u subseteq u' ∧ ∏ x in u', g x = ∏ b in v', f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `trivial`：True
-/
theorem Filter.map_atTop_finsetProd_le_of_prod_eq {f : α → M} {g : β → M}
    (h_eq : ∀ u : Finset β,
      ∃ v : Finset α, ∀ v', v ⊆ v' → ∃ u', u ⊆ u' ∧ ∏ x ∈ u', g x = ∏ b ∈ v', f b) :
    (atTop.map fun s : Finset α => ∏ b ∈ s, f b) ≤
      atTop.map fun s : Finset β => ∏ x ∈ s, g x := by
  refine ((atTop_basis.map _).le_basis_iff (atTop_basis.map _)).2 fun b _ => ?_
  let ⟨v, hv⟩ := h_eq b
  refine ⟨v, trivial, ?_⟩
  simpa [Finset.image_subset_iff] using! hv

@[deprecated (since := "2026-04-08")]
alias Filter.map_atTop_finset_sum_le_of_sum_eq := Filter.map_atTop_finsetSum_le_of_sum_eq

@[to_additive existing, deprecated (since := "2026-04-08")]
alias Filter.map_atTop_finset_prod_le_of_prod_eq := Filter.map_atTop_finsetProd_le_of_prod_eq

/-- Let `g : γ → β` be an injective function and `f : β → α` be a function from the codomain of `g`
to a commutative monoid. Suppose that `f x = 1` outside of the range of `g`. Then the filters
`atTop.map (fun s ↦ ∏ i ∈ s, f (g i))` and `atTop.map (fun s ↦ ∏ i ∈ s, f i)` coincide.

The additive version of this lemma is used to prove the equality `∑' x, f (g x) = ∑' y, f y` under
the same assumptions. -/
@[to_additive]
/-
**Function.Injective.map_atTop_finsetProd_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.map_atTop_finsetProd_eq {g : α -> β} (hg : Function.Inj
ective g) {f : β -> M} (hf : forall x, x ∉ Set.range g -> f x = 1) : map (fun s 
=> ∏ i in s, f (g i)) atTop = map (fun s => ∏ i in s, f i) atTop
参数：hg : Function.Injective g；hf : forall x, x ∉ Set.range g -> f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Filter.map_atTop_finsetProd_le_of_prod_eq`：Filter.map_atTop_finsetProd_l
e_of_prod_eq {f : α -> M} {g : β -> M} (h_eq : forall u : Finset β, exists v : F
inset α, forall v', v subseteq …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.prod_preimage`：prod_preimage (f : ι -> κ) (s : Finset κ) (hf) (g 
: κ -> β) (hg : forall x in s, x ∉ Set.range f -> g x = 1) : ∏ x in s.preimage f
 hf, g (f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.image_subset_iff_subset_preimage`：image_subset_iff_subset_preimag
e [DecidableEq β] {f : α -> β} {s : Finset α} {t : Finset β} (hf : Set.InjOn f (
f ⁻¹' ↑t)) : s.image f subset…

--- 原说明 ---
Let `g : γ → β` be an injective function and `f : β → α` be a function from the 
codomain of `g`
to a commutative monoid. Suppose that `f x = 1` outside of the range of `g`. The
n the filters
`atTop.map (fun s ↦ ∏ i ∈ s, f (g i))` and `atTop.map (fun s ↦ ∏ i ∈ s, f i)` co
incide.

The additive version of this lemma is used to prove the equality `∑' x, f (g x) 
= ∑' y, f y` under
the same assumptions.
-/
theorem Function.Injective.map_atTop_finsetProd_eq {g : α → β}
    (hg : Function.Injective g) {f : β → M} (hf : ∀ x, x ∉ Set.range g → f x = 1) :
    map (fun s => ∏ i ∈ s, f (g i)) atTop = map (fun s => ∏ i ∈ s, f i) atTop := by
  have := Classical.decEq β
  apply le_antisymm <;> refine map_atTop_finsetProd_le_of_prod_eq fun s => ?_
  · refine ⟨s.preimage g hg.injOn, fun t ht => ?_⟩
    refine ⟨t.image g ∪ s, Finset.subset_union_right, ?_⟩
    rw [← Finset.prod_image hg.injOn]
    refine (prod_subset subset_union_left ?_).symm
    simp only [Finset.mem_union, Finset.mem_image]
    refine fun y hy hyt => hf y (mt ?_ hyt)
    rintro ⟨x, rfl⟩
    exact ⟨x, ht (Finset.mem_preimage.2 <| hy.resolve_left hyt), rfl⟩
  · refine ⟨s.image g, fun t ht => ?_⟩
    simp only [← prod_preimage _ _ hg.injOn _ fun x _ => hf x]
    exact ⟨_, (image_subset_iff_subset_preimage _).1 ht, rfl⟩

@[deprecated (since := "2026-04-08")]
alias Function.Injective.map_atTop_finset_sum_eq := Function.Injective.map_atTop_finsetSum_eq

@[to_additive existing, deprecated (since := "2026-04-08")]
alias Function.Injective.map_atTop_finset_prod_eq := Function.Injective.map_atTop_finsetProd_eq

/-- Let `g : γ → β` be an injective function and `f : β → α` be a function from the codomain of `g`
to an additive commutative monoid. Suppose that `f x = 0` outside of the range of `g`. Then the
filters `atTop.map (fun s ↦ ∑ i ∈ s, f (g i))` and `atTop.map (fun s ↦ ∑ i ∈ s, f i)` coincide.

This lemma is used to prove the equality `∑' x, f (g x) = ∑' y, f y` under
the same assumptions. -/
add_decl_doc Function.Injective.map_atTop_finsetSum_eq

