/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.UpperLower.Basic

/-!
# Harris-Kleitman inequality

This file proves the Harris-Kleitman inequality. This relates `#𝒜 * #ℬ` and
`2 ^ card α * #(𝒜 ∩ ℬ)` where `𝒜` and `ℬ` are upward- or downcard-closed finite families of
finsets. This can be interpreted as saying that any two lower sets (resp. any two upper sets)
correlate in the uniform measure.

## Main declarations

* `IsLowerSet.le_card_inter_finset`: One form of the Harris-Kleitman inequality.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

public section


open Finset

variable {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s : Finset α} {a : α}

/--
theorem `IsLowerSet.nonMemberSubfamily` / 定理 `IsLowerSet.nonMemberSubfamily`

English:
theorem IsLowerSet.nonMemberSubfamily
  given: (h : IsLowerSet (𝒜 : Set (Finset α)))
  proof: fun s t hts => by
  simp_rw [mem_coe, mem_nonMemberSubfamily]
  exact And.imp (h hts) (mt <| @hts _)

中文:
定理 是下集.nonMemberSubfamily
  条件: (h : 是下集 (𝒜 : 集合 (有限集 α)))
  证明: fun s t hts => by
  simp_rw [mem_coe, mem_nonMemberSubfamily]
  exact And.imp (h hts) (mt <| @hts _)

Depends on / 依赖: And.imp, mem_coe, mem_nonMemberSubfamily, simp_rw
-/
theorem IsLowerSet.nonMemberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.nonMemberSubfamily a : Set (Finset α)) := fun s t hts => by
  simp_rw [mem_coe, mem_nonMemberSubfamily]
  exact And.imp (h hts) (mt <| @hts _)

/--
theorem `IsLowerSet.memberSubfamily` / 定理 `IsLowerSet.memberSubfamily`

English:
theorem IsLowerSet.memberSubfamily
  given: (h : IsLowerSet (𝒜 : Set (Finset α)))
  proof: by
  rintro s t hts
  simp_rw [mem_coe, mem_memberSubfamily]
  exact And.imp (h <| insert_subset_insert _ hts) (mt <| @hts _)

中文:
定理 是下集.memberSubfamily
  条件: (h : 是下集 (𝒜 : 集合 (有限集 α)))
  证明: by
  rintro s t hts
  simp_rw [mem_coe, mem_memberSubfamily]
  exact And.imp (h <| insert_subset_insert _ hts) (mt <| @hts _)

Depends on / 依赖: And.imp, insert_subset_insert, mem_coe, mem_memberSubfamily, simp_rw
-/
theorem IsLowerSet.memberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    IsLowerSet (𝒜.memberSubfamily a : Set (Finset α)) := by
  rintro s t hts
  simp_rw [mem_coe, mem_memberSubfamily]
  exact And.imp (h <| insert_subset_insert _ hts) (mt <| @hts _)

/--
theorem `IsLowerSet.memberSubfamily_subset_nonMemberSubfamily` / 定理 `IsLowerSet.memberSubfamily_subset_nonMemberSubfamily`

English:
theorem IsLowerSet.memberSubfamily_subset_nonMemberSubfamily
  given: (h : IsLowerSet (𝒜 : Set (Finset α)))
  proof: fun s => by
  rw [mem_memberSubfamily]; rw [mem_nonMemberSubfamily]
  exact And.imp_left (h <| subset_insert _ _)

中文:
定理 是下集.memberSubfamily_subset_nonMemberSubfamily
  条件: (h : 是下集 (𝒜 : 集合 (有限集 α)))
  证明: fun s => by
  rw [mem_memberSubfamily]; rw [mem_nonMemberSubfamily]
  exact And.imp_left (h <| subset_insert _ _)

Depends on / 依赖: And.imp_left, imp_left, mem_memberSubfamily, mem_nonMemberSubfamily, subset_insert
-/
theorem IsLowerSet.memberSubfamily_subset_nonMemberSubfamily (h : IsLowerSet (𝒜 : Set (Finset α))) :
    𝒜.memberSubfamily a subseteq 𝒜.nonMemberSubfamily a := fun s => by
  rw [mem_memberSubfamily]; rw [mem_nonMemberSubfamily]
  exact And.imp_left (h <| subset_insert _ _)

/--
theorem `IsLowerSet.le_card_inter_finset'` / 定理 `IsLowerSet.le_card_inter_finset'`

English:
theorem IsLowerSet.le_card_inter_finset'
  statement: (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  proof: by
  induction s using Finset.induction generalizing 𝒜 ℬ with
  | empty =>
    simp_rw [subset_empty, ← subset_singleton_iff', subset_singleton_iff] at h𝒜s hℬs
    obtain rfl | rfl := h𝒜s
    · simp only [card_empty, zero_mul, empty_inter, mul_zero, le_refl]
    obtain rfl | rfl := hℬs
    · simp
    · simp only [card_empty, pow_zero, inter_singleton_of_mem, mem_singleton, card_singleton,
        le_refl]
  | insert a s hs ih =>
  rw [card_insert_of_notMem hs]; rw [← card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜]; rw [←
    card_memberSubfamily_add_card_nonMemberSubfamily a ℬ]; rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [add_comm (_ * _)]; rw [add_add_add_comm]
  grw [mul_add_mul_le_mul_add_mul
(card_le_card h𝒜.memberSubfamily_subset_nonMemberSubfamily)
      card_le_card hℬ.memberSubfamily_subset_nonMemberSubfamily, ← two_mul, pow_succ', mul_assoc]
  have h₀ : forall 𝒞 : Finset (Finset α), (forall t in 𝒞, t subseteq insert a s) ->
      forall t in 𝒞.nonMemberSubfamily a, t subseteq s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_nonMemberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 (h𝒞 _ ht.1)
  have h₁ : forall 𝒞 : Finset (Finset α), (forall t in 𝒞, t subseteq insert a s) ->
      forall t in 𝒞.memberSubfamily a, t subseteq s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_memberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 ((subset_insert _ _).trans <| h𝒞 _ ht.1)
  gcongr
  refine (add_le_add (ih h𝒜.memberSubfamily hℬ.memberSubfamily (h₁ _ h𝒜s) <| h₁ _ hℬs) <|
ih h𝒜.nonMemberSubfamily hℬ.nonMemberSubfamily (h₀ _ h𝒜s) h₀ _ hℬs).trans_eq ?_
  rw [← mul_add]; rw [← memberSubfamily_inter]; rw [← nonMemberSubfamily_inter]; rw [card_memberSubfamily_add_card_nonMemberSubfamily]

中文:
定理 是下集.le_card_inter_finset'
  结论: (h𝒜 : 是下集 (𝒜 : 集合 (有限集 α)))
  证明: by
  induction s using Finset.induction generalizing 𝒜 ℬ with
  | empty =>
    simp_rw [subset_empty, ← subset_singleton_iff', subset_singleton_iff] at h𝒜s hℬs
    obtain rfl | rfl := h𝒜s
    · simp only [card_empty, zero_mul, empty_inter, mul_zero, le_refl]
    obtain rfl | rfl := hℬs
    · simp
    · simp only [card_empty, pow_zero, inter_singleton_of_mem, mem_singleton, card_singleton,
        le_refl]
  | insert a s hs ih =>
  rw [card_insert_of_notMem hs]; rw [← card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜]; rw [←
    card_memberSubfamily_add_card_nonMemberSubfamily a ℬ]; rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [add_comm (_ * _)]; rw [add_add_add_comm]
  grw [mul_add_mul_le_mul_add_mul
(card_le_card h𝒜.memberSubfamily_subset_nonMemberSubfamily)
      card_le_card hℬ.memberSubfamily_subset_nonMemberSubfamily, ← two_mul, pow_succ', mul_assoc]
  have h₀ : forall 𝒞 : Finset (Finset α), (forall t in 𝒞, t subseteq insert a s) ->
      forall t in 𝒞.nonMemberSubfamily a, t subseteq s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_nonMemberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 (h𝒞 _ ht.1)
  have h₁ : forall 𝒞 : Finset (Finset α), (forall t in 𝒞, t subseteq insert a s) ->
      forall t in 𝒞.memberSubfamily a, t subseteq s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_memberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 ((subset_insert _ _).trans <| h𝒞 _ ht.1)
  gcongr
  refine (add_le_add (ih h𝒜.memberSubfamily hℬ.memberSubfamily (h₁ _ h𝒜s) <| h₁ _ hℬs) <|
ih h𝒜.nonMemberSubfamily hℬ.nonMemberSubfamily (h₀ _ h𝒜s) h₀ _ hℬs).trans_eq ?_
  rw [← mul_add]; rw [← memberSubfamily_inter]; rw [← nonMemberSubfamily_inter]; rw [card_memberSubfamily_add_card_nonMemberSubfamily]

Depends on / 依赖: Finset, Finset.induction, card_empty, card_insert_of_notMem, card_me, card_memberSubfamily_add_card_nonMemberSubfamily, card_singleton, empty_inter, generalizing, insert, inter_singleton_of_mem, le_refl, mem_singleton, mul_zero, pow_zero, simp_rw, subset_empty, subset_singleton_iff, zero_mul
-/
theorem IsLowerSet.le_card_inter_finset' (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) (h𝒜s : forall t in 𝒜, t subseteq s) (hℬs : forall t in ℬ, t subseteq s) :
    #𝒜 * #ℬ <= 2 ^ #s * #(𝒜 inter ℬ) := by
  induction s using Finset.induction generalizing 𝒜 ℬ with
  | empty =>
    simp_rw [subset_empty, ← subset_singleton_iff', subset_singleton_iff] at h𝒜s hℬs
    obtain rfl | rfl := h𝒜s
    · simp only [card_empty, zero_mul, empty_inter, mul_zero, le_refl]
    obtain rfl | rfl := hℬs
    · simp
    · simp only [card_empty, pow_zero, inter_singleton_of_mem, mem_singleton, card_singleton,
        le_refl]
  | insert a s hs ih =>
  rw [card_insert_of_notMem hs]; rw [← card_memberSubfamily_add_card_nonMemberSubfamily a 𝒜]; rw [←
    card_memberSubfamily_add_card_nonMemberSubfamily a ℬ]; rw [add_mul]; rw [mul_add]; rw [mul_add]; rw [add_comm (_ * _)]; rw [add_add_add_comm]
  grw [mul_add_mul_le_mul_add_mul
(card_le_card h𝒜.memberSubfamily_subset_nonMemberSubfamily)
      card_le_card hℬ.memberSubfamily_subset_nonMemberSubfamily, ← two_mul, pow_succ', mul_assoc]
  have h₀ : forall 𝒞 : Finset (Finset α), (forall t in 𝒞, t subseteq insert a s) ->
      forall t in 𝒞.nonMemberSubfamily a, t subseteq s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_nonMemberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 (h𝒞 _ ht.1)
  have h₁ : forall 𝒞 : Finset (Finset α), (forall t in 𝒞, t subseteq insert a s) ->
      forall t in 𝒞.memberSubfamily a, t subseteq s := by
    rintro 𝒞 h𝒞 t ht
    rw [mem_memberSubfamily] at ht
    exact (subset_insert_iff_of_notMem ht.2).1 ((subset_insert _ _).trans <| h𝒞 _ ht.1)
  gcongr
  refine (add_le_add (ih h𝒜.memberSubfamily hℬ.memberSubfamily (h₁ _ h𝒜s) <| h₁ _ hℬs) <|
ih h𝒜.nonMemberSubfamily hℬ.nonMemberSubfamily (h₀ _ h𝒜s) h₀ _ hℬs).trans_eq ?_
  rw [← mul_add]; rw [← memberSubfamily_inter]; rw [← nonMemberSubfamily_inter]; rw [card_memberSubfamily_add_card_nonMemberSubfamily]

variable [Fintype α]

/--
theorem `IsLowerSet.le_card_inter_finset` / 定理 `IsLowerSet.le_card_inter_finset`

English:
theorem IsLowerSet.le_card_inter_finset
  statement: (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  proof: h𝒜.le_card_inter_finset' hℬ (fun _ _ => subset_univ _) fun _ _ => subset_univ _

中文:
定理 是下集.le_card_inter_finset
  结论: (h𝒜 : 是下集 (𝒜 : 集合 (有限集 α)))
  证明: h𝒜.le_card_inter_finset' hℬ (fun _ _ => subset_univ _) fun _ _ => subset_univ _

Depends on / 依赖: le_card_inter_finset, subset_univ
-/
theorem IsLowerSet.le_card_inter_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) : #𝒜 * #ℬ <= 2 ^ Fintype.card α * #(𝒜 inter ℬ) :=
h𝒜.le_card_inter_finset' hℬ (fun _ _ => subset_univ _) fun _ _ => subset_univ _

/--
theorem `IsUpperSet.card_inter_le_finset` / 定理 `IsUpperSet.card_inter_le_finset`

English:
theorem IsUpperSet.card_inter_le_finset
  statement: (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  proof: by
  rw [← isLowerSet_compl]; rw [← coe_compl] at h𝒜
  have := h𝒜.le_card_inter_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this

中文:
定理 是上集.card_inter_le_finset
  结论: (h𝒜 : 是上集 (𝒜 : 集合 (有限集 α)))
  证明: by
  rw [← isLowerSet_compl]; rw [← coe_compl] at h𝒜
  have := h𝒜.le_card_inter_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this

Depends on / 依赖: Fintype, Fintype.card_finset, _root_, _root_.inf_comm, card_compl, card_finset, card_sdiff_of_subset, coe_compl, inf_comm, inter_subset_right, isLowerSet_compl, le_card_inter_finset, mul_tsub, sdiff_compl, sdiff_inter_self_right, tsub_le_iff_tsub_le, tsub_mul
-/
theorem IsUpperSet.card_inter_le_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * #(𝒜 inter ℬ) <= #𝒜 * #ℬ := by
  rw [← isLowerSet_compl]; rw [← coe_compl] at h𝒜
  have := h𝒜.le_card_inter_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, tsub_le_iff_tsub_le, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this

/--
theorem `IsLowerSet.card_inter_le_finset` / 定理 `IsLowerSet.card_inter_le_finset`

English:
theorem IsLowerSet.card_inter_le_finset
  statement: (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
  proof: by
  rw [inter_comm]; rw [mul_comm #𝒜]
  exact hℬ.card_inter_le_finset h𝒜

中文:
定理 是下集.card_inter_le_finset
  结论: (h𝒜 : 是下集 (𝒜 : 集合 (有限集 α)))
  证明: by
  rw [inter_comm]; rw [mul_comm #𝒜]
  exact hℬ.card_inter_le_finset h𝒜

Depends on / 依赖: card_inter_le_finset, inter_comm, mul_comm
-/
theorem IsLowerSet.card_inter_le_finset (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    2 ^ Fintype.card α * #(𝒜 inter ℬ) <= #𝒜 * #ℬ := by
  rw [inter_comm]; rw [mul_comm #𝒜]
  exact hℬ.card_inter_le_finset h𝒜

/--
theorem `IsUpperSet.le_card_inter_finset` / 定理 `IsUpperSet.le_card_inter_finset`

English:
theorem IsUpperSet.le_card_inter_finset
  statement: (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
  proof: by
  rw [← isLowerSet_compl]; rw [← coe_compl] at h𝒜
  have := h𝒜.card_inter_le_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this
  · grw [inter_subset_right]
  · grw [← Fintype.card_finset, card_le_univ]

中文:
定理 是上集.le_card_inter_finset
  结论: (h𝒜 : 是上集 (𝒜 : 集合 (有限集 α)))
  证明: by
  rw [← isLowerSet_compl]; rw [← coe_compl] at h𝒜
  have := h𝒜.card_inter_le_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this
  · grw [inter_subset_right]
  · grw [← Fintype.card_finset, card_le_univ]

Depends on / 依赖: Fintype, Fintype.card_finset, _root_, _root_.inf_comm, card_compl, card_finset, card_inter_le_finset, card_le_univ, card_sdiff_of_subset, coe_compl, inf_comm, inter_subset_right, isLowerSet_compl, le_tsub_iff_le_tsub, mul_tsub, sdiff_compl, sdiff_inter_self_right, tsub_mul
-/
theorem IsUpperSet.le_card_inter_finset (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ <= 2 ^ Fintype.card α * #(𝒜 inter ℬ) := by
  rw [← isLowerSet_compl]; rw [← coe_compl] at h𝒜
  have := h𝒜.card_inter_le_finset hℬ
  rwa [card_compl, Fintype.card_finset, tsub_mul, le_tsub_iff_le_tsub, ← mul_tsub, ←
    card_sdiff_of_subset inter_subset_right, sdiff_inter_self_right, sdiff_compl,
    _root_.inf_comm] at this
  · grw [inter_subset_right]
  · grw [← Fintype.card_finset, card_le_univ]
