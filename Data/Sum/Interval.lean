/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite intervals in a disjoint union

This file provides the `LocallyFiniteOrder` instance for the disjoint sum and linear sum of two
orders and calculates the cardinality of their finite intervals.
-/

@[expose] public section


open Function Sum

namespace Finset

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}

section SumLift₂

variable (f f₁ g₁ : α₁ -> β₁ -> Finset γ₁) (g f₂ g₂ : α₂ -> β₂ -> Finset γ₂)

/-- Lifts maps `α₁ → β₁ → Finset γ₁` and `α₂ → β₂ → Finset γ₂` to a map
`α₁ ⊕ α₂ → β₁ ⊕ β₂ → Finset (γ₁ ⊕ γ₂)`. Could be generalized to `Alternative` functors if we can
make sure to keep computability and universe polymorphism. -/
@[simp]
/--
Definition of `sumLift₂` / `sumLift₂` 的定义

English:
definition sumLift₂
  signature: : forall (_ : α₁ oplus α₂) (_ : β₁ oplus β₂), Finset (γ₁ oplus γ₂)

中文:
定义 sumLift₂
  签名: : 对任意 (_ : α₁ oplus α₂) (_ : β₁ oplus β₂), Finset (γ₁ oplus γ₂)
-/
def sumLift₂ : forall (_ : α₁ oplus α₂) (_ : β₁ oplus β₂), Finset (γ₁ oplus γ₂)
  | inl a, inl b => (f a b).map Embedding.inl
  | inl _, inr _ => ∅
  | inr _, inl _ => ∅
  | inr a, inr b => (g a b).map Embedding.inr

variable {f f₁ g₁ g f₂ g₂} {a : α₁ oplus α₂} {b : β₁ oplus β₂} {c : γ₁ oplus γ₂}

/--
theorem `mem_sumLift₂` / 定理 `mem_sumLift₂`

English:
theorem mem_sumLift₂
  proof: by
  constructor
  · rcases a with a | a <;> rcases b with b | b
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h => (notMem_empty _ h).elim
    · refine fun h => (notMem_empty _ h).elim
    · rw [sumLift₂, mem_map]
      rintr

中文:
定理 mem_sumLift₂
  证明: by
  constructor
  · rcases a with a | a <;> rcases b with b | b
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h => (notMem_empty _ h).elim
    · refine fun h => (notMem_empty _ h).elim
    · rw [sumLift₂, mem_map]
      rintr

Depends on / 依赖: Or.inl, Or.inr, mem_map, mem_map_of_mem, notMem_empty
-/
theorem mem_sumLift₂ :
    c in sumLift₂ f g a b ↔
      (exists a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ in f a₁ b₁) ∨
        exists a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ in g a₂ b₂ := by
  constructor
  · rcases a with a | a <;> rcases b with b | b
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h => (notMem_empty _ h).elim
    · refine fun h => (notMem_empty _ h).elim
    · rw [sumLift₂, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr ⟨a, b, c, rfl, rfl, rfl, hc⟩
  · rintro (⟨a, b, c, rfl, rfl, rfl, h⟩ | ⟨a, b, c, rfl, rfl, rfl, h⟩) <;> exact mem_map_of_mem _ h

/--
theorem `inl_mem_sumLift₂` / 定理 `inl_mem_sumLift₂`

English:
theorem inl_mem_sumLift₂
  given: {c₁ : γ₁}
  proof: by
  rw [mem_sumLift₂]; rw [or_iff_left]
  · simp only [inl.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inl_ne_inr h

中文:
定理 inl_mem_sumLift₂
  条件: {c₁ : γ₁}
  证明: by
  rw [mem_sumLift₂]; rw [or_iff_left]
  · simp only [inl.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inl_ne_inr h

Depends on / 依赖: exists_and_left, exists_eq_left, inl.injEq, inl_ne_inr, or_iff_left
-/
theorem inl_mem_sumLift₂ {c₁ : γ₁} :
    inl c₁ in sumLift₂ f g a b ↔ exists a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ in f a₁ b₁ := by
  rw [mem_sumLift₂]; rw [or_iff_left]
  · simp only [inl.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inl_ne_inr h

/--
theorem `inr_mem_sumLift₂` / 定理 `inr_mem_sumLift₂`

English:
theorem inr_mem_sumLift₂
  given: {c₂ : γ₂}
  proof: by
  rw [mem_sumLift₂]; rw [or_iff_right]
  · simp only [inr.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inr_ne_inl h

中文:
定理 inr_mem_sumLift₂
  条件: {c₂ : γ₂}
  证明: by
  rw [mem_sumLift₂]; rw [or_iff_right]
  · simp only [inr.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inr_ne_inl h

Depends on / 依赖: exists_and_left, exists_eq_left, inr.injEq, inr_ne_inl, or_iff_right
-/
theorem inr_mem_sumLift₂ {c₂ : γ₂} :
    inr c₂ in sumLift₂ f g a b ↔ exists a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ in g a₂ b₂ := by
  rw [mem_sumLift₂]; rw [or_iff_right]
  · simp only [inr.injEq, exists_and_left, exists_eq_left']
  rintro ⟨_, _, c₂, _, _, h, _⟩
  exact inr_ne_inl h

/--
theorem `sumLift₂_eq_empty` / 定理 `sumLift₂_eq_empty`

English:
theorem sumLift₂_eq_empty
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · constructor <;>
    · rintro a b rfl rfl
      exact map_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · rfl
  · rfl
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)

中文:
定理 sumLift₂_eq_empty
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · constructor <;>
    · rintro a b rfl rfl
      exact map_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · rfl
  · rfl
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)

Depends on / 依赖: map_eq_empty
-/
theorem sumLift₂_eq_empty :
    sumLift₂ f g a b = ∅ ↔
      (forall a₁ b₁, a = inl a₁ -> b = inl b₁ -> f a₁ b₁ = ∅) ∧
        forall a₂ b₂, a = inr a₂ -> b = inr b₂ -> g a₂ b₂ = ∅ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · constructor <;>
    · rintro a b rfl rfl
      exact map_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · rfl
  · rfl
  · exact map_eq_empty.2 (h.2 _ _ rfl rfl)

/--
theorem `sumLift₂_nonempty` / 定理 `sumLift₂_nonempty`

English:
theorem sumLift₂_nonempty
  proof: by
  simp only [nonempty_iff_ne_empty, Ne, sumLift₂_eq_empty, not_and_or, not_forall, exists_prop]

中文:
定理 sumLift₂_nonempty
  证明: by
  simp only [nonempty_iff_ne_empty, Ne, sumLift₂_eq_empty, not_and_or, not_forall, exists_prop]

Depends on / 依赖: exists_prop, nonempty_iff_ne_empty, not_and_or, not_forall
-/
theorem sumLift₂_nonempty :
    (sumLift₂ f g a b).Nonempty ↔
      (exists a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f a₁ b₁).Nonempty) ∨
        exists a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (g a₂ b₂).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, sumLift₂_eq_empty, not_and_or, not_forall, exists_prop]

/--
theorem `sumLift₂_mono` / 定理 `sumLift₂_mono`

English:
theorem sumLift₂_mono
  given: (h₁ : forall a b, f₁ a b subseteq g₁ a b) (h₂ : forall a b, f₂ a b subseteq g₂ a b)

中文:
定理 sumLift₂_mono
  条件: (h₁ : 对任意 a b, f₁ a b subseteq g₁ a b) (h₂ : 对任意 a b, f₂ a b subseteq g₂ a b)
-/
theorem sumLift₂_mono (h₁ : forall a b, f₁ a b subseteq g₁ a b) (h₂ : forall a b, f₂ a b subseteq g₂ a b) :
    forall a b, sumLift₂ f₁ f₂ a b subseteq sumLift₂ g₁ g₂ a b
  | inl _, inl _ => map_subset_map.2 (h₁ _ _)
  | inl _, inr _ => Subset.rfl
  | inr _, inl _ => Subset.rfl
  | inr _, inr _ => map_subset_map.2 (h₂ _ _)

end SumLift₂

section SumLexLift
variable (f₁ f₁' : α₁ -> β₁ -> Finset γ₁) (f₂ f₂' : α₂ -> β₂ -> Finset γ₂)
  (g₁ g₁' : α₁ -> β₂ -> Finset γ₁) (g₂ g₂' : α₁ -> β₂ -> Finset γ₂)

/--
Definition of `sumLexLift` / `sumLexLift` 的定义

English:
definition sumLexLift
  signature: : α₁ oplus α₂ -> β₁ oplus β₂ -> Finset (γ₁ oplus γ₂)

中文:
定义 sumLexLift
  签名: : α₁ oplus α₂ -> β₁ oplus β₂ -> Finset (γ₁ oplus γ₂)
-/
def sumLexLift : α₁ oplus α₂ -> β₁ oplus β₂ -> Finset (γ₁ oplus γ₂)
  | inl a, inl b => (f₁ a b).map Embedding.inl
  | inl a, inr b => (g₁ a b).disjSum (g₂ a b)
  | inr _, inl _ => ∅
  | inr a, inr b => (f₂ a b).map ⟨_, inr_injective⟩

@[simp]
/--
lemma `sumLexLift_inl_inl` / 引理 `sumLexLift_inl_inl`

English:
lemma sumLexLift_inl_inl
  given: (a : α₁) (b : β₁)
  proof: rfl

@[simp]

中文:
引理 sumLexLift_inl_inl
  条件: (a : α₁) (b : β₁)
  证明: rfl

@[simp]
-/
lemma sumLexLift_inl_inl (a : α₁) (b : β₁) :
    sumLexLift f₁ f₂ g₁ g₂ (inl a) (inl b) = (f₁ a b).map Embedding.inl := rfl

@[simp]
/--
lemma `sumLexLift_inl_inr` / 引理 `sumLexLift_inl_inr`

English:
lemma sumLexLift_inl_inr
  given: (a : α₁) (b : β₂)
  proof: rfl

@[simp]

中文:
引理 sumLexLift_inl_inr
  条件: (a : α₁) (b : β₂)
  证明: rfl

@[simp]
-/
lemma sumLexLift_inl_inr (a : α₁) (b : β₂) :
    sumLexLift f₁ f₂ g₁ g₂ (inl a) (inr b) = (g₁ a b).disjSum (g₂ a b) := rfl

@[simp]
/--
lemma `sumLexLift_inr_inl` / 引理 `sumLexLift_inr_inl`

English:
lemma sumLexLift_inr_inl
  given: (a : α₂) (b : β₁)
  statement: sumLexLift f₁ f₂ g₁ g₂ (inr a) (inl b) = ∅
  proof: rfl

@[simp]

中文:
引理 sumLexLift_inr_inl
  条件: (a : α₂) (b : β₁)
  结论: sumLexLift f₁ f₂ g₁ g₂ (inr a) (inl b) = ∅
  证明: rfl

@[simp]
-/
lemma sumLexLift_inr_inl (a : α₂) (b : β₁) : sumLexLift f₁ f₂ g₁ g₂ (inr a) (inl b) = ∅ := rfl

@[simp]
/--
lemma `sumLexLift_inr_inr` / 引理 `sumLexLift_inr_inr`

English:
lemma sumLexLift_inr_inr
  given: (a : α₂) (b : β₂)
  proof: rfl

中文:
引理 sumLexLift_inr_inr
  条件: (a : α₂) (b : β₂)
  证明: rfl
-/
lemma sumLexLift_inr_inr (a : α₂) (b : β₂) :
    sumLexLift f₁ f₂ g₁ g₂ (inr a) (inr b) = (f₂ a b).map ⟨_, inr_injective⟩ := rfl

variable {f₁ g₁ f₂ g₂ f₁' g₁' f₂' g₂'} {a : α₁ oplus α₂} {b : β₁ oplus β₂} {c : γ₁ oplus γ₂}

/--
lemma `mem_sumLexLift` / 引理 `mem_sumLexLift`

English:
lemma mem_sumLexLift
  proof: by
  constructor
  · obtain a | a := a <;> obtain b | b := b
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h => (mem_disjSum.1 h).elim ?_ ?_
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inl ⟨a, b, c, rfl, rfl, rfl, h

中文:
引理 mem_sumLexLift
  证明: by
  constructor
  · obtain a | a := a <;> obtain b | b := b
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h => (mem_disjSum.1 h).elim ?_ ?_
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inl ⟨a, b, c, rfl, rfl, rfl, h

Depends on / 依赖: Or.inl, Or.inr, mem_disjSum, mem_map, notMem_empty, sumLexLift
-/
lemma mem_sumLexLift :
    c in sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (exists a₁ b₁ c₁, a = inl a₁ ∧ b = inl b₁ ∧ c = inl c₁ ∧ c₁ in f₁ a₁ b₁) ∨
        (exists a₁ b₂ c₁, a = inl a₁ ∧ b = inr b₂ ∧ c = inl c₁ ∧ c₁ in g₁ a₁ b₂) ∨
          (exists a₁ b₂ c₂, a = inl a₁ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ in g₂ a₁ b₂) ∨
            exists a₂ b₂ c₂, a = inr a₂ ∧ b = inr b₂ ∧ c = inr c₂ ∧ c₂ in f₂ a₂ b₂ := by
  constructor
  · obtain a | a := a <;> obtain b | b := b
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩
    · refine fun h => (mem_disjSum.1 h).elim ?_ ?_
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩)
      · rintro ⟨c, hc, rfl⟩
        exact Or.inr (Or.inr <| Or.inl ⟨a, b, c, rfl, rfl, rfl, hc⟩)
    · exact fun h => (notMem_empty _ h).elim
    · rw [sumLexLift, mem_map]
      rintro ⟨c, hc, rfl⟩
      exact Or.inr (Or.inr <| Or.inr <| ⟨a, b, c, rfl, rfl, rfl, hc⟩)
  · rintro (⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩ |
      ⟨a, b, c, rfl, rfl, rfl, hc⟩ | ⟨a, b, c, rfl, rfl, rfl, hc⟩)
    · exact mem_map_of_mem _ hc
    · exact inl_mem_disjSum.2 hc
    · exact inr_mem_disjSum.2 hc
    · exact mem_map_of_mem _ hc

/--
lemma `inl_mem_sumLexLift` / 引理 `inl_mem_sumLexLift`

English:
lemma inl_mem_sumLexLift
  given: {c₁ : γ₁}
  proof: by
  simp [mem_sumLexLift]

中文:
引理 inl_mem_sumLexLift
  条件: {c₁ : γ₁}
  证明: by
  simp [mem_sumLexLift]

Depends on / 依赖: mem_sumLexLift
-/
lemma inl_mem_sumLexLift {c₁ : γ₁} :
    inl c₁ in sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (exists a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ c₁ in f₁ a₁ b₁) ∨
        exists a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₁ in g₁ a₁ b₂ := by
  simp [mem_sumLexLift]

/--
lemma `inr_mem_sumLexLift` / 引理 `inr_mem_sumLexLift`

English:
lemma inr_mem_sumLexLift
  given: {c₂ : γ₂}
  proof: by
  simp [mem_sumLexLift]

中文:
引理 inr_mem_sumLexLift
  条件: {c₂ : γ₂}
  证明: by
  simp [mem_sumLexLift]

Depends on / 依赖: mem_sumLexLift
-/
lemma inr_mem_sumLexLift {c₂ : γ₂} :
    inr c₂ in sumLexLift f₁ f₂ g₁ g₂ a b ↔
      (exists a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ c₂ in g₂ a₁ b₂) ∨
        exists a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ c₂ in f₂ a₂ b₂ := by
  simp [mem_sumLexLift]

/--
lemma `sumLexLift_mono` / 引理 `sumLexLift_mono`

English:
lemma sumLexLift_mono
  statement: (hf₁ : forall a b, f₁ a b subseteq f₁' a b) (hf₂ : forall a b, f₂ a b subseteq f₂' a b)
  proof: by
  cases a <;> cases b
  exacts [map_subset_map.2 (hf₁ _ _), disjSum_mono (hg₁ _ _) (hg₂ _ _), Subset.rfl,
    map_subset_map.2 (hf₂ _ _)]

中文:
引理 sumLexLift_mono
  结论: (hf₁ : 对任意 a b, f₁ a b subseteq f₁' a b) (hf₂ : 对任意 a b, f₂ a b subseteq f₂' a b)
  证明: by
  cases a <;> cases b
  exacts [map_subset_map.2 (hf₁ _ _), disjSum_mono (hg₁ _ _) (hg₂ _ _), Subset.rfl,
    map_subset_map.2 (hf₂ _ _)]

Depends on / 依赖: Subset, Subset.rfl, disjSum_mono, exacts, map_subset_map
-/
lemma sumLexLift_mono (hf₁ : forall a b, f₁ a b subseteq f₁' a b) (hf₂ : forall a b, f₂ a b subseteq f₂' a b)
    (hg₁ : forall a b, g₁ a b subseteq g₁' a b) (hg₂ : forall a b, g₂ a b subseteq g₂' a b) (a : α₁ oplus α₂)
    (b : β₁ oplus β₂) : sumLexLift f₁ f₂ g₁ g₂ a b subseteq sumLexLift f₁' f₂' g₁' g₂' a b := by
  cases a <;> cases b
  exacts [map_subset_map.2 (hf₁ _ _), disjSum_mono (hg₁ _ _) (hg₂ _ _), Subset.rfl,
    map_subset_map.2 (hf₂ _ _)]

/--
lemma `sumLexLift_eq_empty` / 引理 `sumLexLift_eq_empty`

English:
lemma sumLexLift_eq_empty
  proof: by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
  any_goals rintro a b rfl rfl; exact map_eq_empty.1 h
  · rintro a b rfl rfl; exact disjSum_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · simp [h.2.1 _ _ rfl rfl]
  · rfl
  · exact map_eq_empty.2 (h.2.2 _ _ rfl rfl

中文:
引理 sumLexLift_eq_empty
  证明: by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
  any_goals rintro a b rfl rfl; exact map_eq_empty.1 h
  · rintro a b rfl rfl; exact disjSum_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · simp [h.2.1 _ _ rfl rfl]
  · rfl
  · exact map_eq_empty.2 (h.2.2 _ _ rfl rfl

Depends on / 依赖: any_goals, disjSum_eq_empty, map_eq_empty
-/
lemma sumLexLift_eq_empty :
    sumLexLift f₁ f₂ g₁ g₂ a b = ∅ ↔
      (forall a₁ b₁, a = inl a₁ -> b = inl b₁ -> f₁ a₁ b₁ = ∅) ∧
        (forall a₁ b₂, a = inl a₁ -> b = inr b₂ -> g₁ a₁ b₂ = ∅ ∧ g₂ a₁ b₂ = ∅) ∧
          forall a₂ b₂, a = inr a₂ -> b = inr b₂ -> f₂ a₂ b₂ = ∅ := by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
  any_goals rintro a b rfl rfl; exact map_eq_empty.1 h
  · rintro a b rfl rfl; exact disjSum_eq_empty.1 h
  cases a <;> cases b
  · exact map_eq_empty.2 (h.1 _ _ rfl rfl)
  · simp [h.2.1 _ _ rfl rfl]
  · rfl
  · exact map_eq_empty.2 (h.2.2 _ _ rfl rfl)

/--
lemma `sumLexLift_nonempty` / 引理 `sumLexLift_nonempty`

English:
lemma sumLexLift_nonempty
  proof: by
  simp only [nonempty_iff_ne_empty, Ne, sumLexLift_eq_empty, not_and_or, exists_prop, not_forall]

中文:
引理 sumLexLift_nonempty
  证明: by
  simp only [nonempty_iff_ne_empty, Ne, sumLexLift_eq_empty, not_and_or, exists_prop, not_forall]

Depends on / 依赖: exists_prop, nonempty_iff_ne_empty, not_and_or, not_forall, sumLexLift_eq_empty
-/
lemma sumLexLift_nonempty :
    (sumLexLift f₁ f₂ g₁ g₂ a b).Nonempty ↔
      (exists a₁ b₁, a = inl a₁ ∧ b = inl b₁ ∧ (f₁ a₁ b₁).Nonempty) ∨
        (exists a₁ b₂, a = inl a₁ ∧ b = inr b₂ ∧ ((g₁ a₁ b₂).Nonempty ∨ (g₂ a₁ b₂).Nonempty)) ∨
          exists a₂ b₂, a = inr a₂ ∧ b = inr b₂ ∧ (f₂ a₂ b₂).Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, sumLexLift_eq_empty, not_and_or, exists_prop, not_forall]

end SumLexLift
end Finset

open Finset

namespace Sum

variable {α β : Type*}

/-! ### Disjoint sum of orders -/


section Disjoint

section LocallyFiniteOrder
variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder (α oplus β) where
  body: sumLift₂ Icc Icc
  finsetIco := sumLift₂ Ico Ico
  finsetIoc := sumLift₂ Ioc Ioc
  finsetIoo := sumLift₂ Ioo Ioo
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

中文:
实例 instLocallyFiniteOrder
  签名: : LocallyFiniteOrder (α oplus β) where
  定义体: sumLift₂ Icc Icc
  finsetIco := sumLift₂ Ico Ico
  finsetIoc := sumLift₂ Ioc Ioc
  finsetIoo := sumLift₂ Ioo Ioo
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (α oplus β) where
  finsetIcc := sumLift₂ Icc Icc
  finsetIco := sumLift₂ Ico Ico
  finsetIoc := sumLift₂ Ioc Ioc
  finsetIoo := sumLift₂ Ioo Ioo
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

variable (a₁ a₂ : α) (b₁ b₂ : β)

/--
theorem `Icc_inl_inl` / 定理 `Icc_inl_inl`

English:
theorem Icc_inl_inl
  statement: Icc (inl a₁ : α oplus β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl
  proof: rfl

中文:
定理 Icc_inl_inl
  结论: Icc (inl a₁ : α oplus β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl
  证明: rfl
-/
theorem Icc_inl_inl : Icc (inl a₁ : α oplus β) (inl a₂) = (Icc a₁ a₂).map Embedding.inl :=
  rfl

/--
theorem `Ico_inl_inl` / 定理 `Ico_inl_inl`

English:
theorem Ico_inl_inl
  statement: Ico (inl a₁ : α oplus β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl
  proof: rfl

中文:
定理 Ico_inl_inl
  结论: Ico (inl a₁ : α oplus β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl
  证明: rfl
-/
theorem Ico_inl_inl : Ico (inl a₁ : α oplus β) (inl a₂) = (Ico a₁ a₂).map Embedding.inl :=
  rfl

/--
theorem `Ioc_inl_inl` / 定理 `Ioc_inl_inl`

English:
theorem Ioc_inl_inl
  statement: Ioc (inl a₁ : α oplus β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl
  proof: rfl

中文:
定理 Ioc_inl_inl
  结论: Ioc (inl a₁ : α oplus β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl
  证明: rfl
-/
theorem Ioc_inl_inl : Ioc (inl a₁ : α oplus β) (inl a₂) = (Ioc a₁ a₂).map Embedding.inl :=
  rfl

/--
theorem `Ioo_inl_inl` / 定理 `Ioo_inl_inl`

English:
theorem Ioo_inl_inl
  statement: Ioo (inl a₁ : α oplus β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl
  proof: rfl

@[simp]

中文:
定理 Ioo_inl_inl
  结论: Ioo (inl a₁ : α oplus β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl
  证明: rfl

@[simp]
-/
theorem Ioo_inl_inl : Ioo (inl a₁ : α oplus β) (inl a₂) = (Ioo a₁ a₂).map Embedding.inl :=
  rfl

@[simp]
/--
theorem `Icc_inl_inr` / 定理 `Icc_inl_inr`

English:
theorem Icc_inl_inr
  statement: Icc (inl a₁) (inr b₂) = ∅
  proof: rfl

@[simp]

中文:
定理 Icc_inl_inr
  结论: Icc (inl a₁) (inr b₂) = ∅
  证明: rfl

@[simp]
-/
theorem Icc_inl_inr : Icc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/--
theorem `Ico_inl_inr` / 定理 `Ico_inl_inr`

English:
theorem Ico_inl_inr
  statement: Ico (inl a₁) (inr b₂) = ∅
  proof: rfl

@[simp]

中文:
定理 Ico_inl_inr
  结论: Ico (inl a₁) (inr b₂) = ∅
  证明: rfl

@[simp]
-/
theorem Ico_inl_inr : Ico (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/--
theorem `Ioc_inl_inr` / 定理 `Ioc_inl_inr`

English:
theorem Ioc_inl_inr
  statement: Ioc (inl a₁) (inr b₂) = ∅
  proof: rfl

@[simp]

中文:
定理 Ioc_inl_inr
  结论: Ioc (inl a₁) (inr b₂) = ∅
  证明: rfl

@[simp]
-/
theorem Ioc_inl_inr : Ioc (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/--
theorem `Ioo_inl_inr` / 定理 `Ioo_inl_inr`

English:
theorem Ioo_inl_inr
  statement: Ioo (inl a₁) (inr b₂) = ∅
  proof: rfl

@[simp]

中文:
定理 Ioo_inl_inr
  结论: Ioo (inl a₁) (inr b₂) = ∅
  证明: rfl

@[simp]
-/
theorem Ioo_inl_inr : Ioo (inl a₁) (inr b₂) = ∅ :=
  rfl

@[simp]
/--
theorem `Icc_inr_inl` / 定理 `Icc_inr_inl`

English:
theorem Icc_inr_inl
  statement: Icc (inr b₁) (inl a₂) = ∅
  proof: rfl

@[simp]

中文:
定理 Icc_inr_inl
  结论: Icc (inr b₁) (inl a₂) = ∅
  证明: rfl

@[simp]
-/
theorem Icc_inr_inl : Icc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
/--
theorem `Ico_inr_inl` / 定理 `Ico_inr_inl`

English:
theorem Ico_inr_inl
  statement: Ico (inr b₁) (inl a₂) = ∅
  proof: rfl

@[simp]

中文:
定理 Ico_inr_inl
  结论: Ico (inr b₁) (inl a₂) = ∅
  证明: rfl

@[simp]
-/
theorem Ico_inr_inl : Ico (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
/--
theorem `Ioc_inr_inl` / 定理 `Ioc_inr_inl`

English:
theorem Ioc_inr_inl
  statement: Ioc (inr b₁) (inl a₂) = ∅
  proof: rfl

@[simp]

中文:
定理 Ioc_inr_inl
  结论: Ioc (inr b₁) (inl a₂) = ∅
  证明: rfl

@[simp]
-/
theorem Ioc_inr_inl : Ioc (inr b₁) (inl a₂) = ∅ :=
  rfl

@[simp]
/--
theorem `Ioo_inr_inl` / 定理 `Ioo_inr_inl`

English:
theorem Ioo_inr_inl
  statement: Ioo (inr b₁) (inl a₂) = ∅
  proof: rfl

中文:
定理 Ioo_inr_inl
  结论: Ioo (inr b₁) (inl a₂) = ∅
  证明: rfl
-/
theorem Ioo_inr_inl : Ioo (inr b₁) (inl a₂) = ∅ :=
  rfl

/--
theorem `Icc_inr_inr` / 定理 `Icc_inr_inr`

English:
theorem Icc_inr_inr
  statement: Icc (inr b₁ : α oplus β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr
  proof: rfl

中文:
定理 Icc_inr_inr
  结论: Icc (inr b₁ : α oplus β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr
  证明: rfl
-/
theorem Icc_inr_inr : Icc (inr b₁ : α oplus β) (inr b₂) = (Icc b₁ b₂).map Embedding.inr :=
  rfl

/--
theorem `Ico_inr_inr` / 定理 `Ico_inr_inr`

English:
theorem Ico_inr_inr
  statement: Ico (inr b₁ : α oplus β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr
  proof: rfl

中文:
定理 Ico_inr_inr
  结论: Ico (inr b₁ : α oplus β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr
  证明: rfl
-/
theorem Ico_inr_inr : Ico (inr b₁ : α oplus β) (inr b₂) = (Ico b₁ b₂).map Embedding.inr :=
  rfl

/--
theorem `Ioc_inr_inr` / 定理 `Ioc_inr_inr`

English:
theorem Ioc_inr_inr
  statement: Ioc (inr b₁ : α oplus β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr
  proof: rfl

中文:
定理 Ioc_inr_inr
  结论: Ioc (inr b₁ : α oplus β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr
  证明: rfl
-/
theorem Ioc_inr_inr : Ioc (inr b₁ : α oplus β) (inr b₂) = (Ioc b₁ b₂).map Embedding.inr :=
  rfl

/--
theorem `Ioo_inr_inr` / 定理 `Ioo_inr_inr`

English:
theorem Ioo_inr_inr
  statement: Ioo (inr b₁ : α oplus β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr
  proof: rfl

中文:
定理 Ioo_inr_inr
  结论: Ioo (inr b₁ : α oplus β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr
  证明: rfl
-/
theorem Ioo_inr_inr : Ioo (inr b₁ : α oplus β) (inr b₂) = (Ioo b₁ b₂).map Embedding.inr :=
  rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [Preorder α] [Preorder β] [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyFiniteOrderBot (α oplus β)
  body: Sum.elim (Iic · |>.map .inl) (Iic · |>.map .inr)
  finsetIio := Sum.elim (Iio · |>.map .inl) (Iio · |>.map .inr)
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

中文:
实例 :
  签名: LocallyFiniteOrderBot (α oplus β)
  定义体: Sum.elim (Iic · |>.map .inl) (Iic · |>.map .inr)
  finsetIio := Sum.elim (Iio · |>.map .inl) (Iio · |>.map .inr)
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

Depends on / 依赖: Sum.elim
-/
instance : LocallyFiniteOrderBot (α oplus β) where
  finsetIic := Sum.elim (Iic · |>.map .inl) (Iic · |>.map .inr)
  finsetIio := Sum.elim (Iio · |>.map .inl) (Iio · |>.map .inr)
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

variable (a : α) (b : β)

/--
theorem `Iic_inl` / 定理 `Iic_inl`

English:
theorem Iic_inl
  statement: Iic (inl a : α oplus β) = (Iic a).map Embedding.inl
  proof: rfl

中文:
定理 Iic_inl
  结论: Iic (inl a : α oplus β) = (Iic a).map Embedding.inl
  证明: rfl
-/
theorem Iic_inl : Iic (inl a : α oplus β) = (Iic a).map Embedding.inl := rfl
/--
theorem `Iic_inr` / 定理 `Iic_inr`

English:
theorem Iic_inr
  statement: Iic (inr b : α oplus β) = (Iic b).map Embedding.inr
  proof: rfl

中文:
定理 Iic_inr
  结论: Iic (inr b : α oplus β) = (Iic b).map Embedding.inr
  证明: rfl
-/
theorem Iic_inr : Iic (inr b : α oplus β) = (Iic b).map Embedding.inr := rfl
/--
theorem `Iio_inl` / 定理 `Iio_inl`

English:
theorem Iio_inl
  statement: Iio (inl a : α oplus β) = (Iio a).map Embedding.inl
  proof: rfl

中文:
定理 Iio_inl
  结论: Iio (inl a : α oplus β) = (Iio a).map Embedding.inl
  证明: rfl
-/
theorem Iio_inl : Iio (inl a : α oplus β) = (Iio a).map Embedding.inl := rfl
/--
theorem `Iio_inr` / 定理 `Iio_inr`

English:
theorem Iio_inr
  statement: Iio (inr b : α oplus β) = (Iio b).map Embedding.inr
  proof: rfl

中文:
定理 Iio_inr
  结论: Iio (inr b : α oplus β) = (Iio b).map Embedding.inr
  证明: rfl
-/
theorem Iio_inr : Iio (inr b : α oplus β) = (Iio b).map Embedding.inr := rfl

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [Preorder α] [Preorder β] [LocallyFiniteOrderTop α] [LocallyFiniteOrderTop β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyFiniteOrderTop (α oplus β)
  body: Sum.elim (Ici · |>.map .inl) (Ici · |>.map .inr)
  finsetIoi := Sum.elim (Ioi · |>.map .inl) (Ioi · |>.map .inr)
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

中文:
实例 :
  签名: LocallyFiniteOrderTop (α oplus β)
  定义体: Sum.elim (Ici · |>.map .inl) (Ici · |>.map .inr)
  finsetIoi := Sum.elim (Ioi · |>.map .inl) (Ioi · |>.map .inr)
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

Depends on / 依赖: Sum.elim
-/
instance : LocallyFiniteOrderTop (α oplus β) where
  finsetIci := Sum.elim (Ici · |>.map .inl) (Ici · |>.map .inr)
  finsetIoi := Sum.elim (Ioi · |>.map .inl) (Ioi · |>.map .inr)
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

variable (a : α) (b : β)

/--
theorem `Ici_inl` / 定理 `Ici_inl`

English:
theorem Ici_inl
  statement: Ici (inl a : α oplus β) = (Ici a).map Embedding.inl
  proof: rfl

中文:
定理 Ici_inl
  结论: Ici (inl a : α oplus β) = (Ici a).map Embedding.inl
  证明: rfl
-/
theorem Ici_inl : Ici (inl a : α oplus β) = (Ici a).map Embedding.inl := rfl
/--
theorem `Ici_inr` / 定理 `Ici_inr`

English:
theorem Ici_inr
  statement: Ici (inr b : α oplus β) = (Ici b).map Embedding.inr
  proof: rfl

中文:
定理 Ici_inr
  结论: Ici (inr b : α oplus β) = (Ici b).map Embedding.inr
  证明: rfl
-/
theorem Ici_inr : Ici (inr b : α oplus β) = (Ici b).map Embedding.inr := rfl
/--
theorem `Ioi_inl` / 定理 `Ioi_inl`

English:
theorem Ioi_inl
  statement: Ioi (inl a : α oplus β) = (Ioi a).map Embedding.inl
  proof: rfl

中文:
定理 Ioi_inl
  结论: Ioi (inl a : α oplus β) = (Ioi a).map Embedding.inl
  证明: rfl
-/
theorem Ioi_inl : Ioi (inl a : α oplus β) = (Ioi a).map Embedding.inl := rfl
/--
theorem `Ioi_inr` / 定理 `Ioi_inr`

English:
theorem Ioi_inr
  statement: Ioi (inr b : α oplus β) = (Ioi b).map Embedding.inr
  proof: rfl

中文:
定理 Ioi_inr
  结论: Ioi (inr b : α oplus β) = (Ioi b).map Embedding.inr
  证明: rfl
-/
theorem Ioi_inr : Ioi (inr b : α oplus β) = (Ioi b).map Embedding.inr := rfl

end LocallyFiniteOrderTop

end Disjoint

/-! ### Lexicographical sum of orders -/

namespace Lex

section LocallyFiniteOrder
variable [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot β]

/--
Instance `locallyFiniteOrder` / 实例 `locallyFiniteOrder`

English:
instance locallyFiniteOrder
  signature: : LocallyFiniteOrder (α oplusₗ β) where
  body: (sumLexLift Icc Icc (fun a _ => Ici a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIco a b :=
    (sumLexLift Ico Ico (fun a _ => Ici a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoc a b :=
    (sumLexLift Ioc Ioc (fun a _ => Ioi a) (fun _ => Iic) (ofLex

中文:
实例 locallyFiniteOrder
  签名: : LocallyFiniteOrder (α oplusₗ β) where
  定义体: (sumLexLift Icc Icc (fun a _ => Ici a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIco a b :=
    (sumLexLift Ico Ico (fun a _ => Ici a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoc a b :=
    (sumLexLift Ioc Ioc (fun a _ => Ioi a) (fun _ => Iic) (ofLex

Depends on / 依赖: finsetIco, finsetIoc, finsetIoo, finset_me, finset_mem_Icc, finset_mem_Ico, sumLexLift, toEmbedding, toLex.toEmbedding
-/
instance locallyFiniteOrder : LocallyFiniteOrder (α oplusₗ β) where
  finsetIcc a b :=
    (sumLexLift Icc Icc (fun a _ => Ici a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIco a b :=
    (sumLexLift Ico Ico (fun a _ => Ici a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoc a b :=
    (sumLexLift Ioc Ioc (fun a _ => Ioi a) (fun _ => Iic) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finsetIoo a b :=
    (sumLexLift Ioo Ioo (fun a _ => Ioi a) (fun _ => Iio) (ofLex a) (ofLex b)).map toLex.toEmbedding
  finset_mem_Icc := by simp
  finset_mem_Ico := by simp
  finset_mem_Ioc := by simp
  finset_mem_Ioo := by simp

variable (a a₁ a₂ : α) (b b₁ b₂ : β)

/--
lemma `Icc_inl_inl` / 引理 `Icc_inl_inl`

English:
lemma Icc_inl_inl
  proof: by
  rw [← Finset.map_map]; rfl

中文:
引理 Icc_inl_inl
  证明: by
  rw [← Finset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Icc_inl_inl :
    Icc (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Icc a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

/--
lemma `Ico_inl_inl` / 引理 `Ico_inl_inl`

English:
lemma Ico_inl_inl
  proof: by
  rw [← Finset.map_map]; rfl

中文:
引理 Ico_inl_inl
  证明: by
  rw [← Finset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Ico_inl_inl :
    Ico (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Ico a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

/--
lemma `Ioc_inl_inl` / 引理 `Ioc_inl_inl`

English:
lemma Ioc_inl_inl
  proof: by
  rw [← Finset.map_map]; rfl

中文:
引理 Ioc_inl_inl
  证明: by
  rw [← Finset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Ioc_inl_inl :
    Ioc (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Ioc a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

/--
lemma `Ioo_inl_inl` / 引理 `Ioo_inl_inl`

English:
lemma Ioo_inl_inl
  proof: by
  rw [← Finset.map_map]; rfl

@[simp]

中文:
引理 Ioo_inl_inl
  证明: by
  rw [← Finset.map_map]; rfl

@[simp]

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Ioo_inl_inl :
    Ioo (inlₗ a₁ : α oplusₗ β) (inlₗ a₂) = (Ioo a₁ a₂).map (Embedding.inl.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

@[simp]
/--
lemma `Icc_inl_inr` / 引理 `Icc_inl_inr`

English:
lemma Icc_inl_inr
  statement: Icc (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iic b)).map toLex.toEmbedding
  proof: rfl

@[simp]

中文:
引理 Icc_inl_inr
  结论: Icc (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iic b)).map toLex.toEmbedding
  证明: rfl

@[simp]
-/
lemma Icc_inl_inr : Icc (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iic b)).map toLex.toEmbedding := rfl

@[simp]
/--
lemma `Ico_inl_inr` / 引理 `Ico_inl_inr`

English:
lemma Ico_inl_inr
  statement: Ico (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iio b)).map toLex.toEmbedding
  proof: rfl

@[simp]

中文:
引理 Ico_inl_inr
  结论: Ico (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iio b)).map toLex.toEmbedding
  证明: rfl

@[simp]
-/
lemma Ico_inl_inr : Ico (inlₗ a) (inrₗ b) = ((Ici a).disjSum (Iio b)).map toLex.toEmbedding := rfl

@[simp]
/--
lemma `Ioc_inl_inr` / 引理 `Ioc_inl_inr`

English:
lemma Ioc_inl_inr
  statement: Ioc (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iic b)).map toLex.toEmbedding
  proof: rfl

@[simp]

中文:
引理 Ioc_inl_inr
  结论: Ioc (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iic b)).map toLex.toEmbedding
  证明: rfl

@[simp]
-/
lemma Ioc_inl_inr : Ioc (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iic b)).map toLex.toEmbedding := rfl

@[simp]
/--
lemma `Ioo_inl_inr` / 引理 `Ioo_inl_inr`

English:
lemma Ioo_inl_inr
  statement: Ioo (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iio b)).map toLex.toEmbedding
  proof: rfl

@[simp]

中文:
引理 Ioo_inl_inr
  结论: Ioo (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iio b)).map toLex.toEmbedding
  证明: rfl

@[simp]
-/
lemma Ioo_inl_inr : Ioo (inlₗ a) (inrₗ b) = ((Ioi a).disjSum (Iio b)).map toLex.toEmbedding := rfl

@[simp]
/--
lemma `Icc_inr_inl` / 引理 `Icc_inr_inl`

English:
lemma Icc_inr_inl
  statement: Icc (inrₗ b) (inlₗ a) = ∅
  proof: rfl

@[simp]

中文:
引理 Icc_inr_inl
  结论: Icc (inrₗ b) (inlₗ a) = ∅
  证明: rfl

@[simp]
-/
lemma Icc_inr_inl : Icc (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
/--
lemma `Ico_inr_inl` / 引理 `Ico_inr_inl`

English:
lemma Ico_inr_inl
  statement: Ico (inrₗ b) (inlₗ a) = ∅
  proof: rfl

@[simp]

中文:
引理 Ico_inr_inl
  结论: Ico (inrₗ b) (inlₗ a) = ∅
  证明: rfl

@[simp]
-/
lemma Ico_inr_inl : Ico (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
/--
lemma `Ioc_inr_inl` / 引理 `Ioc_inr_inl`

English:
lemma Ioc_inr_inl
  statement: Ioc (inrₗ b) (inlₗ a) = ∅
  proof: rfl

@[simp]

中文:
引理 Ioc_inr_inl
  结论: Ioc (inrₗ b) (inlₗ a) = ∅
  证明: rfl

@[simp]
-/
lemma Ioc_inr_inl : Ioc (inrₗ b) (inlₗ a) = ∅ := rfl

@[simp]
/--
lemma `Ioo_inr_inl` / 引理 `Ioo_inr_inl`

English:
lemma Ioo_inr_inl
  statement: Ioo (inrₗ b) (inlₗ a) = ∅
  proof: rfl

中文:
引理 Ioo_inr_inl
  结论: Ioo (inrₗ b) (inlₗ a) = ∅
  证明: rfl
-/
lemma Ioo_inr_inl : Ioo (inrₗ b) (inlₗ a) = ∅ := rfl

/--
lemma `Icc_inr_inr` / 引理 `Icc_inr_inr`

English:
lemma Icc_inr_inr
  proof: by
  rw [← Finset.map_map]; rfl

中文:
引理 Icc_inr_inr
  证明: by
  rw [← Finset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Icc_inr_inr :
    Icc (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Icc b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

/--
lemma `Ico_inr_inr` / 引理 `Ico_inr_inr`

English:
lemma Ico_inr_inr
  proof: by
  rw [← Finset.map_map]; rfl

中文:
引理 Ico_inr_inr
  证明: by
  rw [← Finset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Ico_inr_inr :
    Ico (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Ico b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

/--
lemma `Ioc_inr_inr` / 引理 `Ioc_inr_inr`

English:
lemma Ioc_inr_inr
  proof: by
  rw [← Finset.map_map]; rfl

中文:
引理 Ioc_inr_inr
  证明: by
  rw [← Finset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Ioc_inr_inr :
    Ioc (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Ioc b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

/--
lemma `Ioo_inr_inr` / 引理 `Ioo_inr_inr`

English:
lemma Ioo_inr_inr
  proof: by
  rw [← Finset.map_map]; rfl

中文:
引理 Ioo_inr_inr
  证明: by
  rw [← Finset.map_map]; rfl

Depends on / 依赖: Finset, Finset.map_map, map_map
-/
lemma Ioo_inr_inr :
    Ioo (inrₗ b₁ : α oplusₗ β) (inrₗ b₂) = (Ioo b₁ b₂).map (Embedding.inr.trans toLex.toEmbedding) := by
  rw [← Finset.map_map]; rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [Preorder α] [Preorder β] [Fintype α] [LocallyFiniteOrderBot α] [LocallyFiniteOrderBot β]

/--
Instance `instLocallyFiniteOrderBot` / 实例 `instLocallyFiniteOrderBot`

English:
instance instLocallyFiniteOrderBot
  signature: : LocallyFiniteOrderBot (α oplusₗ β) where
  body: Sum.elim
    (Iic · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iic x) |>.map toLex.toEmbedding) ∘ ofLex
  finsetIio := Sum.elim
    (Iio · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iio x) |>.map toLex.toEmbedding) ∘ ofLex
  finset_mem_

中文:
实例 instLocallyFiniteOrderBot
  签名: : LocallyFiniteOrderBot (α oplusₗ β) where
  定义体: Sum.elim
    (Iic · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iic x) |>.map toLex.toEmbedding) ∘ ofLex
  finsetIio := Sum.elim
    (Iio · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iio x) |>.map toLex.toEmbedding) ∘ ofLex
  finset_mem_

Depends on / 依赖: Sum.elim
-/
instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (α oplusₗ β) where
  finsetIic := Sum.elim
    (Iic · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iic x) |>.map toLex.toEmbedding) ∘ ofLex
  finsetIio := Sum.elim
    (Iio · |>.map (.trans .inl toLex.toEmbedding))
    (fun x => Finset.univ.disjSum (Iio x) |>.map toLex.toEmbedding) ∘ ofLex
  finset_mem_Iic := by simp
  finset_mem_Iio := by simp

variable (a : α) (b : β)

/--
lemma `Iic_inl` / 引理 `Iic_inl`

English:
lemma Iic_inl
  statement: Iic (inlₗ a : α oplusₗ β) = (Iic a).map (Embedding.inl.trans toLex.toEmbedding)
  proof: rfl

中文:
引理 Iic_inl
  结论: Iic (inlₗ a : α oplusₗ β) = (Iic a).map (Embedding.inl.trans toLex.toEmbedding)
  证明: rfl
-/
lemma Iic_inl : Iic (inlₗ a : α oplusₗ β) = (Iic a).map (Embedding.inl.trans toLex.toEmbedding) := rfl
/--
lemma `Iic_inr` / 引理 `Iic_inr`

English:
lemma Iic_inr
  statement: Iic (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iic b)).map toLex.toEmbedding
  proof: rfl

中文:
引理 Iic_inr
  结论: Iic (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iic b)).map toLex.toEmbedding
  证明: rfl
-/
lemma Iic_inr : Iic (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iic b)).map toLex.toEmbedding := rfl

/--
lemma `Iio_inl` / 引理 `Iio_inl`

English:
lemma Iio_inl
  statement: Iio (inlₗ a : α oplusₗ β) = (Iio a).map (Embedding.inl.trans toLex.toEmbedding)
  proof: rfl

中文:
引理 Iio_inl
  结论: Iio (inlₗ a : α oplusₗ β) = (Iio a).map (Embedding.inl.trans toLex.toEmbedding)
  证明: rfl
-/
lemma Iio_inl : Iio (inlₗ a : α oplusₗ β) = (Iio a).map (Embedding.inl.trans toLex.toEmbedding) := rfl
/--
lemma `Iio_inr` / 引理 `Iio_inr`

English:
lemma Iio_inr
  statement: Iio (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iio b)).map toLex.toEmbedding
  proof: rfl

中文:
引理 Iio_inr
  结论: Iio (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iio b)).map toLex.toEmbedding
  证明: rfl

Depends on / 依赖: NormalWord, fstIdx_ne
-/
lemma Iio_inr : Iio (inrₗ b : α oplusₗ β) = (Finset.univ.disjSum (Iio b)).map toLex.toEmbedding := rfl

end LocallyFiniteOrderBot

/-- TODO: `LocallyFiniteOrder.toLocallyFiniteOrderBot` is probably a bad instance, as it forms
a diamond with this instance, and constructs data from data. We should consider removing it. -/
example [Fintype α] [Preorder α] [Preorder β] [OrderBot α] [OrderBot β] [OrderTop α]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] :
    LocallyFiniteOrder.toLocallyFiniteOrderBot = instLocallyFiniteOrderBot (α := α) (β := β) := by
  try with_reducible_and_instances rfl -- fails
  try rfl -- fails
  exact Subsingleton.elim _ _

section LocallyFiniteOrderTop
variable [Preorder α] [Preorder β] [LocallyFiniteOrderTop α] [Fintype β] [LocallyFiniteOrderTop β]

/--
Instance `instLocallyFiniteOrderTop` / 实例 `instLocallyFiniteOrderTop`

English:
instance instLocallyFiniteOrderTop
  signature: : LocallyFiniteOrderTop (α oplusₗ β) where
  body: Sum.elim
    (fun x => (Ici x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ici · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finsetIoi := Sum.elim
    (fun x => (Ioi x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ioi · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finset_mem_

中文:
实例 instLocallyFiniteOrderTop
  签名: : LocallyFiniteOrderTop (α oplusₗ β) where
  定义体: Sum.elim
    (fun x => (Ici x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ici · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finsetIoi := Sum.elim
    (fun x => (Ioi x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ioi · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finset_mem_

Depends on / 依赖: Sum.elim
-/
instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (α oplusₗ β) where
  finsetIci := Sum.elim
    (fun x => (Ici x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ici · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finsetIoi := Sum.elim
    (fun x => (Ioi x).disjSum Finset.univ |>.map toLex.toEmbedding)
    (Ioi · |>.map (.trans .inr toLex.toEmbedding)) ∘ ofLex
  finset_mem_Ici := by simp
  finset_mem_Ioi := by simp

variable (a : α) (b : β)

/--
lemma `Ici_inl` / 引理 `Ici_inl`

English:
lemma Ici_inl
  statement: Ici (inlₗ a : α oplusₗ β) = ((Ici a).disjSum Finset.univ).map toLex.toEmbedding
  proof: rfl

中文:
引理 Ici_inl
  结论: Ici (inlₗ a : α oplusₗ β) = ((Ici a).disjSum Finset.univ).map toLex.toEmbedding
  证明: rfl
-/
lemma Ici_inl : Ici (inlₗ a : α oplusₗ β) = ((Ici a).disjSum Finset.univ).map toLex.toEmbedding := rfl
/--
lemma `Ici_inr` / 引理 `Ici_inr`

English:
lemma Ici_inr
  statement: Ici (inrₗ b : α oplusₗ β) = (Ici b).map (Embedding.inr.trans toLex.toEmbedding)
  proof: rfl

中文:
引理 Ici_inr
  结论: Ici (inrₗ b : α oplusₗ β) = (Ici b).map (Embedding.inr.trans toLex.toEmbedding)
  证明: rfl
-/
lemma Ici_inr : Ici (inrₗ b : α oplusₗ β) = (Ici b).map (Embedding.inr.trans toLex.toEmbedding) := rfl

/--
lemma `Ioi_inl` / 引理 `Ioi_inl`

English:
lemma Ioi_inl
  statement: Ioi (inlₗ a : α oplusₗ β) = ((Ioi a).disjSum Finset.univ).map toLex.toEmbedding
  proof: rfl

中文:
引理 Ioi_inl
  结论: Ioi (inlₗ a : α oplusₗ β) = ((Ioi a).disjSum Finset.univ).map toLex.toEmbedding
  证明: rfl
-/
lemma Ioi_inl : Ioi (inlₗ a : α oplusₗ β) = ((Ioi a).disjSum Finset.univ).map toLex.toEmbedding := rfl
/--
lemma `Ioi_inr` / 引理 `Ioi_inr`

English:
lemma Ioi_inr
  statement: Ioi (inrₗ b : α oplusₗ β) = (Ioi b).map (Embedding.inr.trans toLex.toEmbedding)
  proof: rfl

中文:
引理 Ioi_inr
  结论: Ioi (inrₗ b : α oplusₗ β) = (Ioi b).map (Embedding.inr.trans toLex.toEmbedding)
  证明: rfl
-/
lemma Ioi_inr : Ioi (inrₗ b : α oplusₗ β) = (Ioi b).map (Embedding.inr.trans toLex.toEmbedding) := rfl

end LocallyFiniteOrderTop

end Lex
end Sum
