/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Lee
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Order.Filter.AtTopBot.BigOperators

import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Lemmas on infinite sums and products in topological monoids

This file contains many simple lemmas on `tsum`, `HasSum` etc, which are placed here in order to
keep the basic file of definitions as short as possible.

Results requiring a group (rather than monoid) structure on the target should go in `Group.lean`.

-/

public section

noncomputable section

open Filter Finset Function Topology SummationFilter

variable {α β γ : Type*}

section HasProd

variable [CommMonoid α] [TopologicalSpace α]
variable {f g : β -> α} {a b : α} {L : SummationFilter β}

/-- Constant one function has product `1` -/
@[to_additive (attr := simp) /-- Constant zero function has sum `0` -/]
/--
theorem `hasProd_one` / 定理 `hasProd_one`

English:
theorem hasProd_one
  statement: HasProd (fun _ => 1 : β -> α) 1 L
  proof: by simp [HasProd, tendsto_const_nhds]

@[to_additive (attr := simp)]

中文:
定理 hasProd_one
  结论: 有积类型 (fun _ => 1 : β -> α) 1 L
  证明: by simp [HasProd, tendsto_const_nhds]

@[to_additive (attr := simp)]

Depends on / 依赖: HasProd, tendsto_const_nhds
-/
theorem hasProd_one : HasProd (fun _ => 1 : β -> α) 1 L := by simp [HasProd, tendsto_const_nhds]

@[to_additive (attr := simp)]
/--
theorem `hasProd_empty` / 定理 `hasProd_empty`

English:
theorem hasProd_empty
  given: [IsEmpty β]
  statement: HasProd f 1 L
  proof: by
  convert! hasProd_one

@[to_additive (attr := nontriviality)]

中文:
定理 hasProd_empty
  条件: [是空 β]
  结论: 有积类型 f 1 L
  证明: by
  convert! hasProd_one

@[to_additive (attr := nontriviality)]

Depends on / 依赖: convert, hasProd_one
-/
theorem hasProd_empty [IsEmpty β] : HasProd f 1 L := by
  convert! hasProd_one

@[to_additive (attr := nontriviality)]
/--
theorem `HasProd.of_subsingleton_cod` / 定理 `HasProd.of_subsingleton_cod`

English:
theorem HasProd.of_subsingleton_cod
  given: [Subsingleton α]
  statement: HasProd f 1 L
  proof: by
  convert! hasProd_one

@[to_additive (attr := simp)]

中文:
定理 有积类型.of_subsingleton_cod
  条件: [子单例 α]
  结论: 有积类型 f 1 L
  证明: by
  convert! hasProd_one

@[to_additive (attr := simp)]

Depends on / 依赖: convert, hasProd_one
-/
theorem HasProd.of_subsingleton_cod [Subsingleton α] : HasProd f 1 L := by
  convert! hasProd_one

@[to_additive (attr := simp)]
/--
theorem `multipliable_one` / 定理 `multipliable_one`

English:
theorem multipliable_one
  statement: Multipliable (fun _ => 1 : β -> α) L
  proof: hasProd_one.multipliable

@[to_additive (attr := simp)]

中文:
定理 multipliable_one
  结论: Multipliable (fun _ => 1 : β -> α) L
  证明: hasProd_one.multipliable

@[to_additive (attr := simp)]

Depends on / 依赖: hasProd_one, hasProd_one.multipliable, multipliable
-/
theorem multipliable_one : Multipliable (fun _ => 1 : β -> α) L :=
  hasProd_one.multipliable

@[to_additive (attr := simp)]
/--
theorem `multipliable_empty` / 定理 `multipliable_empty`

English:
theorem multipliable_empty
  given: [IsEmpty β]
  statement: Multipliable f L
  proof: hasProd_empty.multipliable

@[to_additive (attr := nontriviality)]

中文:
定理 multipliable_empty
  条件: [是空 β]
  结论: Multipliable f L
  证明: hasProd_empty.multipliable

@[to_additive (attr := nontriviality)]

Depends on / 依赖: hasProd_empty, hasProd_empty.multipliable, multipliable
-/
theorem multipliable_empty [IsEmpty β] : Multipliable f L :=
  hasProd_empty.multipliable

@[to_additive (attr := nontriviality)]
/--
theorem `Multipliable.of_subsingleton_cod` / 定理 `Multipliable.of_subsingleton_cod`

English:
theorem Multipliable.of_subsingleton_cod
  given: [Subsingleton α]
  statement: Multipliable f L
  proof: HasProd.of_subsingleton_cod.multipliable

中文:
定理 Multipliable.of_subsingleton_cod
  条件: [子单例 α]
  结论: Multipliable f L
  证明: HasProd.of_subsingleton_cod.multipliable

Depends on / 依赖: HasProd, HasProd.of_subsingleton_cod.multipliable, multipliable, of_subsingleton_cod
-/
theorem Multipliable.of_subsingleton_cod [Subsingleton α] : Multipliable f L :=
  HasProd.of_subsingleton_cod.multipliable

/-- See `multipliable_congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/
@[to_additive /-- See `summable_congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/]
/--
theorem `multipliable_congr` / 定理 `multipliable_congr`

English:
theorem multipliable_congr
  given: (hfg : forall b, f b = g b)
  statement: Multipliable f L ↔ Multipliable g L
  proof: iff_of_eq (congr_arg (Multipliable · L) <| funext hfg)

中文:
定理 multipliable_congr
  条件: (hfg : 对任意 b, f b = g b)
  结论: Multipliable f L ↔ Multipliable g L
  证明: iff_of_eq (congr_arg (Multipliable · L) <| funext hfg)

Depends on / 依赖: Multipliable, congr_arg, iff_of_eq
-/
theorem multipliable_congr (hfg : forall b, f b = g b) : Multipliable f L ↔ Multipliable g L :=
  iff_of_eq (congr_arg (Multipliable · L) <| funext hfg)

/-- See `Multipliable.congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/
@[to_additive /-- See `Summable.congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/]
/--
theorem `Multipliable.congr` / 定理 `Multipliable.congr`

English:
theorem Multipliable.congr
  given: (hf : Multipliable f L) (hfg : forall b, f b = g b)
  statement: Multipliable g L
  proof: (multipliable_congr hfg).mp hf

@[to_additive]

中文:
定理 Multipliable.congr
  条件: (hf : Multipliable f L) (hfg : 对任意 b, f b = g b)
  结论: Multipliable g L
  证明: (multipliable_congr hfg).mp hf

@[to_additive]

Depends on / 依赖: multipliable_congr
-/
theorem Multipliable.congr (hf : Multipliable f L) (hfg : forall b, f b = g b) : Multipliable g L :=
  (multipliable_congr hfg).mp hf

@[to_additive]
/--
lemma `HasProd.congr_fun` / 引理 `HasProd.congr_fun`

English:
lemma HasProd.congr_fun
  given: (hf : HasProd f a L) (h : forall x : β, g x = f x)
  statement: HasProd g a L
  proof: (funext h : g = f) ▸ hf

@[to_additive]

中文:
引理 有积类型.congr_fun
  条件: (hf : 有积类型 f a L) (h : 对任意 x : β, g x = f x)
  结论: 有积类型 g a L
  证明: (funext h : g = f) ▸ hf

@[to_additive]
-/
lemma HasProd.congr_fun (hf : HasProd f a L) (h : forall x : β, g x = f x) : HasProd g a L :=
  (funext h : g = f) ▸ hf

@[to_additive]
/--
theorem `HasProd.hasProd_of_prod_eq` / 定理 `HasProd.hasProd_of_prod_eq`

English:
theorem HasProd.hasProd_of_prod_eq
  statement: {g : γ -> α}
  proof: le_trans (map_atTop_finsetProd_le_of_prod_eq h_eq) hf

@[to_additive]

中文:
定理 有积类型.hasProd_of_prod_eq
  结论: {g : γ -> α}
  证明: le_trans (map_atTop_finsetProd_le_of_prod_eq h_eq) hf

@[to_additive]

Depends on / 依赖: h_eq, le_trans, map_atTop_finsetProd_le_of_prod_eq
-/
theorem HasProd.hasProd_of_prod_eq {g : γ -> α}
    (h_eq : forall u : Finset γ, exists v : Finset β, forall v', v subseteq v' ->
      exists u', u subseteq u' ∧ ∏ x in u', g x = ∏ b in v', f b)
    (hf : HasProd g a) : HasProd f a :=
  le_trans (map_atTop_finsetProd_le_of_prod_eq h_eq) hf

@[to_additive]
/--
theorem `hasProd_iff_hasProd` / 定理 `hasProd_iff_hasProd`

English:
theorem hasProd_iff_hasProd
  statement: {g : γ -> α}
  proof: ⟨HasProd.hasProd_of_prod_eq h₂, HasProd.hasProd_of_prod_eq h₁⟩

@[to_additive]

中文:
定理 hasProd_iff_hasProd
  结论: {g : γ -> α}
  证明: ⟨HasProd.hasProd_of_prod_eq h₂, HasProd.hasProd_of_prod_eq h₁⟩

@[to_additive]

Depends on / 依赖: HasProd, HasProd.hasProd_of_prod_eq, hasProd_of_prod_eq
-/
theorem hasProd_iff_hasProd {g : γ -> α}
    (h₁ : forall u : Finset γ, exists v : Finset β, forall v', v subseteq v' ->
      exists u', u subseteq u' ∧ ∏ x in u', g x = ∏ b in v', f b)
    (h₂ : forall v : Finset β, exists u : Finset γ, forall u', u subseteq u' ->
      exists v', v subseteq v' ∧ ∏ b in v', f b = ∏ x in u', g x) :
    HasProd f a ↔ HasProd g a :=
  ⟨HasProd.hasProd_of_prod_eq h₂, HasProd.hasProd_of_prod_eq h₁⟩

@[to_additive]
/--
theorem `Function.Injective.multipliable_iff` / 定理 `Function.Injective.multipliable_iff`

English:
theorem Function.Injective.multipliable_iff
  statement: {g : γ -> β} (hg : Injective g)
  proof: exists_congr fun _ => hg.hasProd_iff hf

中文:
定理 函数.单射.multipliable_iff
  结论: {g : γ -> β} (hg : 单射 g)
  证明: exists_congr fun _ => hg.hasProd_iff hf

Depends on / 依赖: exists_congr, hasProd_iff, hg.hasProd_iff
-/
theorem Function.Injective.multipliable_iff {g : γ -> β} (hg : Injective g)
    (hf : forall x ∉ Set.range g, f x = 1) : Multipliable (f ∘ g) ↔ Multipliable f :=
  exists_congr fun _ => hg.hasProd_iff hf

/--
theorem `hasProd_extend_one` / 定理 `hasProd_extend_one`

English:
theorem hasProd_extend_one
  given: {g : β -> γ} (hg : Injective g)
  proof: by
  rw [← hg.hasProd_iff]; rw [extend_comp hg]
  exact extend_apply' _ _

中文:
定理 hasProd_extend_one
  条件: {g : β -> γ} (hg : 单射 g)
  证明: by
  rw [← hg.hasProd_iff]; rw [extend_comp hg]
  exact extend_apply' _ _
-/
@[to_additive (attr := simp)] theorem hasProd_extend_one {g : β -> γ} (hg : Injective g) :
    HasProd (extend g f 1) a ↔ HasProd f a := by
  rw [← hg.hasProd_iff]; rw [extend_comp hg]
  exact extend_apply' _ _

/--
theorem `multipliable_extend_one` / 定理 `multipliable_extend_one`

English:
theorem multipliable_extend_one
  given: {g : β -> γ} (hg : Injective g)
  proof: exists_congr fun _ => hasProd_extend_one hg

@[to_additive]

中文:
定理 multipliable_extend_one
  条件: {g : β -> γ} (hg : 单射 g)
  证明: exists_congr fun _ => hasProd_extend_one hg

@[to_additive]
-/
@[to_additive (attr := simp)] theorem multipliable_extend_one {g : β -> γ} (hg : Injective g) :
    Multipliable (extend g f 1) ↔ Multipliable f :=
  exists_congr fun _ => hasProd_extend_one hg

@[to_additive]
/--
theorem `hasProd_subtype_iff_mulIndicator` / 定理 `hasProd_subtype_iff_mulIndicator`

English:
theorem hasProd_subtype_iff_mulIndicator
  given: {s : Set β}
  proof: by
  rw [← Set.mulIndicator_range_comp]; rw [Subtype.range_coe]; rw [hasProd_subtype_iff_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]

@[to_additive]

中文:
定理 hasProd_subtype_iff_mulIndicator
  条件: {s : 集合 β}
  证明: by
  rw [← Set.mulIndicator_range_comp]; rw [Subtype.range_coe]; rw [hasProd_subtype_iff_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]

@[to_additive]

Depends on / 依赖: Set.mulIndicator_range_comp, Set.mulSupport_mulIndicator_subset, Subtype, Subtype.range_coe, hasProd_subtype_iff_of_mulSupport_subset, mulIndicator_range_comp, mulSupport_mulIndicator_subset, range_coe
-/
theorem hasProd_subtype_iff_mulIndicator {s : Set β} :
    HasProd (f ∘ (↑) : s -> α) a ↔ HasProd (s.mulIndicator f) a := by
  rw [← Set.mulIndicator_range_comp]; rw [Subtype.range_coe]; rw [hasProd_subtype_iff_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]

@[to_additive]
/--
theorem `multipliable_subtype_iff_mulIndicator` / 定理 `multipliable_subtype_iff_mulIndicator`

English:
theorem multipliable_subtype_iff_mulIndicator
  given: {s : Set β}
  proof: exists_congr fun _ => hasProd_subtype_iff_mulIndicator

@[to_additive (attr := simp)]

中文:
定理 multipliable_subtype_iff_mulIndicator
  条件: {s : 集合 β}
  证明: exists_congr fun _ => hasProd_subtype_iff_mulIndicator

@[to_additive (attr := simp)]

Depends on / 依赖: exists_congr, hasProd_subtype_iff_mulIndicator
-/
theorem multipliable_subtype_iff_mulIndicator {s : Set β} :
    Multipliable (f ∘ (↑) : s -> α) ↔ Multipliable (s.mulIndicator f) :=
  exists_congr fun _ => hasProd_subtype_iff_mulIndicator

@[to_additive (attr := simp)]
/--
theorem `hasProd_subtype_mulSupport` / 定理 `hasProd_subtype_mulSupport`

English:
theorem hasProd_subtype_mulSupport
  statement: HasProd (f ∘ (↑) : mulSupport f -> α) a ↔ HasProd f a
  proof: hasProd_subtype_iff_of_mulSupport_subset Set.Subset.refl _

@[to_additive]

中文:
定理 hasProd_subtype_mulSupport
  结论: 有积类型 (f ∘ (↑) : mulSupport f -> α) a ↔ 有积类型 f a
  证明: hasProd_subtype_iff_of_mulSupport_subset Set.Subset.refl _

@[to_additive]

Depends on / 依赖: Set.Subset.refl, Subset, hasProd_subtype_iff_of_mulSupport_subset
-/
theorem hasProd_subtype_mulSupport : HasProd (f ∘ (↑) : mulSupport f -> α) a ↔ HasProd f a :=
hasProd_subtype_iff_of_mulSupport_subset Set.Subset.refl _

@[to_additive]
/--
theorem `Finset.multipliable` / 定理 `Finset.multipliable`

English:
theorem Finset.multipliable
  given: (s : Finset β) (f : β -> α)
  proof: (s.hasProd f).multipliable

@[to_additive]

中文:
定理 有限集.multipliable
  条件: (s : 有限集 β) (f : β -> α)
  证明: (s.hasProd f).multipliable

@[to_additive]
-/
protected theorem Finset.multipliable (s : Finset β) (f : β -> α) :
    Multipliable (f ∘ (↑) : (↑s : Set β) -> α) :=
  (s.hasProd f).multipliable

@[to_additive]
/--
theorem `Set.Finite.multipliable` / 定理 `Set.Finite.multipliable`

English:
theorem Set.Finite.multipliable
  given: {s : Set β} (hs : s.Finite) (f : β -> α)
  proof: by
  have := hs.toFinset.multipliable f
  rwa [hs.coe_toFinset] at this

中文:
定理 集合.有限.multipliable
  条件: {s : 集合 β} (hs : s.有限) (f : β -> α)
  证明: by
  have := hs.toFinset.multipliable f
  rwa [hs.coe_toFinset] at this
-/
protected theorem Set.Finite.multipliable {s : Set β} (hs : s.Finite) (f : β -> α) :
    Multipliable (f ∘ (↑) : s -> α) := by
  have := hs.toFinset.multipliable f
  rwa [hs.coe_toFinset] at this

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `multipliable_of_hasFiniteMulSupport` / 定理 `multipliable_of_hasFiniteMulSupport`

English:
theorem multipliable_of_hasFiniteMulSupport
  given: [L.HasSupport] (h : HasFiniteMulSupport f)
  proof: by
  apply multipliable_of_ne_finset_one (s := h.toFinset); simp

@[deprecated (since := "2026-03-03")] alias
  multipliable_of_finite_mulSupport := multipliable_of_hasFiniteMulSupport

@[deprecated (since := "2026-03-03")] alias
  summable_of_finite_support := summable_of_hasFiniteSupport

@[to_add

中文:
定理 multipliable_of_hasFiniteMulSupport
  条件: [L.有Support] (h : HasFiniteMulSupport f)
  证明: by
  apply multipliable_of_ne_finset_one (s := h.toFinset); simp

@[deprecated (since := "2026-03-03")] alias
  multipliable_of_finite_mulSupport := multipliable_of_hasFiniteMulSupport

@[deprecated (since := "2026-03-03")] alias
  summable_of_finite_support := summable_of_hasFiniteSupport

@[to_add

Depends on / 依赖: h.toFinset, multipliable_of_ne_finset_one, toFinset
-/
theorem multipliable_of_hasFiniteMulSupport [L.HasSupport] (h : HasFiniteMulSupport f) :
    Multipliable f L := by
  apply multipliable_of_ne_finset_one (s := h.toFinset); simp

@[deprecated (since := "2026-03-03")] alias
  multipliable_of_finite_mulSupport := multipliable_of_hasFiniteMulSupport

@[deprecated (since := "2026-03-03")] alias
  summable_of_finite_support := summable_of_hasFiniteSupport

@[to_additive]
/--
lemma `Multipliable.of_finite` / 引理 `Multipliable.of_finite`

English:
lemma Multipliable.of_finite
  given: [Finite β] [L.HasSupport] {f : β -> α}
  statement: Multipliable f L
  proof: multipliable_of_hasFiniteMulSupport Set.finite_univ.subset (Set.subset_univ _)

@[to_additive]

中文:
引理 Multipliable.of_finite
  条件: [有限 β] [L.有Support] {f : β -> α}
  结论: Multipliable f L
  证明: multipliable_of_hasFiniteMulSupport Set.finite_univ.subset (Set.subset_univ _)

@[to_additive]

Depends on / 依赖: Set.finite_univ.subset, Set.subset_univ, finite_univ, multipliable_of_hasFiniteMulSupport, subset, subset_univ
-/
lemma Multipliable.of_finite [Finite β] [L.HasSupport] {f : β -> α} : Multipliable f L :=
multipliable_of_hasFiniteMulSupport Set.finite_univ.subset (Set.subset_univ _)

@[to_additive]
/--
theorem `hasProd_single` / 定理 `hasProd_single`

English:
theorem hasProd_single
  statement: {f : β -> α} (b : β) (hf : forall (b') (_ : b' != b), f b' = 1)
  proof: suffices HasProd f (∏ b' in {b}, f b') L by simpa using this
hasProd_prod_of_ne_finset_one by simpa [hf]

@[to_additive (attr := simp)]

中文:
定理 hasProd_single
  结论: {f : β -> α} (b : β) (hf : 对任意 (b') (_ : b' != b), f b' = 1)
  证明: suffices HasProd f (∏ b' in {b}, f b') L by simpa using this
hasProd_prod_of_ne_finset_one by simpa [hf]

@[to_additive (attr := simp)]

Depends on / 依赖: HasProd, L.LeAtTop, LeAtTop, unconditional
-/
theorem hasProd_single {f : β -> α} (b : β) (hf : forall (b') (_ : b' != b), f b' = 1)
    (L := unconditional β) [L.LeAtTop] : HasProd f (f b) L :=
  suffices HasProd f (∏ b' in {b}, f b') L by simpa using this
hasProd_prod_of_ne_finset_one by simpa [hf]

@[to_additive (attr := simp)]
/--
lemma `hasProd_unique` / 引理 `hasProd_unique`

English:
lemma hasProd_unique
  given: [Unique β] (f : β -> α) (L := unconditional β) [L.LeAtTop]
  proof: hasProd_single default (fun _ hb => False.elim <| hb <| Unique.uniq ..) L

@[to_additive (attr := simp)]

中文:
引理 hasProd_unique
  条件: [唯一 β] (f : β -> α) (L := unconditional β) [L.LeAtTop]
  证明: hasProd_single default (fun _ hb => False.elim <| hb <| Unique.uniq ..) L

@[to_additive (attr := simp)]

Depends on / 依赖: L.LeAtTop, LeAtTop, unconditional
-/
lemma hasProd_unique [Unique β] (f : β -> α) (L := unconditional β) [L.LeAtTop] :
    HasProd f (f default) L :=
  hasProd_single default (fun _ hb => False.elim <| hb <| Unique.uniq ..) L

@[to_additive (attr := simp)]
/--
lemma `hasProd_singleton` / 引理 `hasProd_singleton`

English:
lemma hasProd_singleton
  given: (m : β) (f : β -> α)
  statement: HasProd (({m} : Set β).domRestrict f) (f m)
  proof: hasProd_unique (Set.domRestrict {m} f)

@[to_additive]

中文:
引理 hasProd_singleton
  条件: (m : β) (f : β -> α)
  结论: 有积类型 (({m} : 集合 β).domRestrict f) (f m)
  证明: hasProd_unique (Set.domRestrict {m} f)

@[to_additive]

Depends on / 依赖: Set.domRestrict, domRestrict, hasProd_unique
-/
lemma hasProd_singleton (m : β) (f : β -> α) : HasProd (({m} : Set β).domRestrict f) (f m) :=
  hasProd_unique (Set.domRestrict {m} f)

@[to_additive]
/--
theorem `hasProd_ite_eq` / 定理 `hasProd_ite_eq`

English:
theorem hasProd_ite_eq
  given: (b : β) [DecidablePred (· = b)] (a : α) (L := unconditional β) [L.LeAtTop]
  proof: suffices HasProd (fun b' => if b' = b then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' => if_neg hb') (L := L)

@[to_additive]

中文:
定理 hasProd_ite_eq
  条件: (b : β) [DecidablePred (· = b)] (a : α) (L := unconditional β) [L.LeAtTop]
  证明: suffices HasProd (fun b' => if b' = b then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' => if_neg hb') (L := L)

@[to_additive]

Depends on / 依赖: L.LeAtTop, LeAtTop, unconditional
-/
theorem hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) (L := unconditional β) [L.LeAtTop] :
    HasProd (fun b' => if b' = b then a else 1) a L :=
  suffices HasProd (fun b' => if b' = b then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' => if_neg hb') (L := L)

@[to_additive]
/--
theorem `hasProd_ite_eq'` / 定理 `hasProd_ite_eq'`

English:
theorem hasProd_ite_eq'
  given: (b : β) [DecidablePred (b = ·)] (a : α) (L := unconditional β) [L.LeAtTop]
  proof: suffices HasProd (fun b' => if b = b' then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' => if_neg hb'.symm) (L := L)

@[to_additive]

中文:
定理 hasProd_ite_eq'
  条件: (b : β) [DecidablePred (b = ·)] (a : α) (L := unconditional β) [L.LeAtTop]
  证明: suffices HasProd (fun b' => if b = b' then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' => if_neg hb'.symm) (L := L)

@[to_additive]

Depends on / 依赖: L.LeAtTop, LeAtTop, unconditional
-/
theorem hasProd_ite_eq' (b : β) [DecidablePred (b = ·)] (a : α) (L := unconditional β) [L.LeAtTop] :
    HasProd (fun b' => if b = b' then a else 1) a L :=
  suffices HasProd (fun b' => if b = b' then a else 1) (if b = b then a else 1) L by simpa
  hasProd_single b (hf := fun b' hb' => if_neg hb'.symm) (L := L)

@[to_additive]
/--
theorem `Equiv.hasProd_iff` / 定理 `Equiv.hasProd_iff`

English:
theorem Equiv.hasProd_iff
  given: (e : γ ≃ β)
  statement: HasProd (f ∘ e) a ↔ HasProd f a
  proof: e.injective.hasProd_iff by simp

@[to_additive]

中文:
定理 等价.hasProd_iff
  条件: (e : γ ≃ β)
  结论: 有积类型 (f ∘ e) a ↔ 有积类型 f a
  证明: e.injective.hasProd_iff by simp

@[to_additive]

Depends on / 依赖: e.injective.hasProd_iff, hasProd_iff, injective
-/
theorem Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ HasProd f a :=
e.injective.hasProd_iff by simp

@[to_additive]
/--
theorem `Function.Injective.hasProd_range_iff` / 定理 `Function.Injective.hasProd_range_iff`

English:
theorem Function.Injective.hasProd_range_iff
  given: {g : γ -> β} (hg : Injective g)
  proof: (Equiv.ofInjective g hg).hasProd_iff.symm

@[to_additive]

中文:
定理 函数.单射.hasProd_range_iff
  条件: {g : γ -> β} (hg : 单射 g)
  证明: (Equiv.ofInjective g hg).hasProd_iff.symm

@[to_additive]

Depends on / 依赖: Equiv.ofInjective, hasProd_iff, hasProd_iff.symm, ofInjective
-/
theorem Function.Injective.hasProd_range_iff {g : γ -> β} (hg : Injective g) :
    HasProd (fun x : Set.range g => f x) a ↔ HasProd (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasProd_iff.symm

@[to_additive]
/--
theorem `Equiv.multipliable_iff` / 定理 `Equiv.multipliable_iff`

English:
theorem Equiv.multipliable_iff
  given: (e : γ ≃ β)
  statement: Multipliable (f ∘ e) ↔ Multipliable f
  proof: exists_congr fun _ => e.hasProd_iff

@[to_additive]

中文:
定理 等价.multipliable_iff
  条件: (e : γ ≃ β)
  结论: Multipliable (f ∘ e) ↔ Multipliable f
  证明: exists_congr fun _ => e.hasProd_iff

@[to_additive]

Depends on / 依赖: e.hasProd_iff, exists_congr, hasProd_iff
-/
theorem Equiv.multipliable_iff (e : γ ≃ β) : Multipliable (f ∘ e) ↔ Multipliable f :=
  exists_congr fun _ => e.hasProd_iff

@[to_additive]
/--
theorem `Equiv.hasProd_iff_of_mulSupport` / 定理 `Equiv.hasProd_iff_of_mulSupport`

English:
theorem Equiv.hasProd_iff_of_mulSupport
  statement: {g : γ -> α} (e : mulSupport f ≃ mulSupport g)
  proof: by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  rw [← hasProd_subtype_mulSupport]; rw [← this]; rw [e.hasProd_iff]; rw [hasProd_subtype_mulSupport]

@[to_additive]

中文:
定理 等价.hasProd_iff_of_mulSupport
  结论: {g : γ -> α} (e : mulSupport f ≃ mulSupport g)
  证明: by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  rw [← hasProd_subtype_mulSupport]; rw [← this]; rw [e.hasProd_iff]; rw [hasProd_subtype_mulSupport]

@[to_additive]

Depends on / 依赖: e.hasProd_iff, hasProd_iff, hasProd_subtype_mulSupport
-/
theorem Equiv.hasProd_iff_of_mulSupport {g : γ -> α} (e : mulSupport f ≃ mulSupport g)
    (he : forall x : mulSupport f, g (e x) = f x) : HasProd f a ↔ HasProd g a := by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  rw [← hasProd_subtype_mulSupport]; rw [← this]; rw [e.hasProd_iff]; rw [hasProd_subtype_mulSupport]

@[to_additive]
/--
theorem `hasProd_iff_hasProd_of_ne_one_bij` / 定理 `hasProd_iff_hasProd_of_ne_one_bij`

English:
theorem hasProd_iff_hasProd_of_ne_one_bij
  statement: {g : γ -> α} (i : mulSupport g -> β)
  proof: Iff.symm
    Equiv.hasProd_iff_of_mulSupport
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
⟨fun _ _ h => hi Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun _ hx => Subtype.ext hx⟩)
      hfg

@[to_additive]

中文:
定理 hasProd_iff_hasProd_of_ne_one_bij
  结论: {g : γ -> α} (i : mulSupport g -> β)
  证明: Iff.symm
    Equiv.hasProd_iff_of_mulSupport
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
⟨fun _ _ h => hi Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun _ hx => Subtype.ext hx⟩)
      hfg

@[to_additive]

Depends on / 依赖: Equiv.hasProd_iff_of_mulSupport, Equiv.ofBijective, Iff.symm, Subtype, Subtype.ext, Subtype.ext_iff, coe_prop, ext_iff, hasProd_iff_of_mulSupport, ofBijective, x.coe_prop, y.coe_prop
-/
theorem hasProd_iff_hasProd_of_ne_one_bij {g : γ -> α} (i : mulSupport g -> β)
    (hi : Injective i) (hf : mulSupport f subseteq Set.range i)
    (hfg : forall x, f (i x) = g x) : HasProd f a ↔ HasProd g a :=
Iff.symm
    Equiv.hasProd_iff_of_mulSupport
      (Equiv.ofBijective (fun x => ⟨i x, fun hx => x.coe_prop <| hfg x ▸ hx⟩)
⟨fun _ _ h => hi Subtype.ext_iff.1 h, fun y =>
          (hf y.coe_prop).imp fun _ hx => Subtype.ext hx⟩)
      hfg

@[to_additive]
/--
theorem `Equiv.multipliable_iff_of_mulSupport` / 定理 `Equiv.multipliable_iff_of_mulSupport`

English:
theorem Equiv.multipliable_iff_of_mulSupport
  statement: {g : γ -> α} (e : mulSupport f ≃ mulSupport g)
  proof: exists_congr fun _ => e.hasProd_iff_of_mulSupport he

@[to_additive]

中文:
定理 等价.multipliable_iff_of_mulSupport
  结论: {g : γ -> α} (e : mulSupport f ≃ mulSupport g)
  证明: exists_congr fun _ => e.hasProd_iff_of_mulSupport he

@[to_additive]

Depends on / 依赖: e.hasProd_iff_of_mulSupport, exists_congr, hasProd_iff_of_mulSupport
-/
theorem Equiv.multipliable_iff_of_mulSupport {g : γ -> α} (e : mulSupport f ≃ mulSupport g)
    (he : forall x : mulSupport f, g (e x) = f x) : Multipliable f ↔ Multipliable g :=
  exists_congr fun _ => e.hasProd_iff_of_mulSupport he

@[to_additive]
/--
theorem `HasProd.map` / 定理 `HasProd.map`

English:
theorem HasProd.map
  statement: [CommMonoid γ] [TopologicalSpace γ] (hf : HasProd f a L) {G}
  proof: by
  have : (g ∘ fun s : Finset β => ∏ b in s, f b) = fun s : Finset β => ∏ b in s, (g ∘ f) b :=
funext map_prod g _
  unfold HasProd
  rw [← this]
  exact (hg.tendsto a).comp hf

@[to_additive]

中文:
定理 有积类型.map
  结论: [交换幺半群 γ] [拓扑空间 γ] (hf : 有积类型 f a L) {G}
  证明: by
  have : (g ∘ fun s : Finset β => ∏ b in s, f b) = fun s : Finset β => ∏ b in s, (g ∘ f) b :=
funext map_prod g _
  unfold HasProd
  rw [← this]
  exact (hg.tendsto a).comp hf

@[to_additive]
-/
protected theorem HasProd.map [CommMonoid γ] [TopologicalSpace γ] (hf : HasProd f a L) {G}
    [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    HasProd (g ∘ f) (g a) L := by
  have : (g ∘ fun s : Finset β => ∏ b in s, f b) = fun s : Finset β => ∏ b in s, (g ∘ f) b :=
funext map_prod g _
  unfold HasProd
  rw [← this]
  exact (hg.tendsto a).comp hf

@[to_additive]
/--
theorem `Topology.IsInducing.hasProd_iff` / 定理 `Topology.IsInducing.hasProd_iff`

English:
theorem Topology.IsInducing.hasProd_iff
  statement: [CommMonoid γ] [TopologicalSpace γ] {G}
  proof: by
  simp_rw [HasProd, comp_apply, ← _root_.map_prod]
  exact hg.tendsto_nhds_iff.symm

@[to_additive]

中文:
定理 拓扑.是Inducing.hasProd_iff
  结论: [交换幺半群 γ] [拓扑空间 γ] {G}
  证明: by
  simp_rw [HasProd, comp_apply, ← _root_.map_prod]
  exact hg.tendsto_nhds_iff.symm

@[to_additive]
-/
protected theorem Topology.IsInducing.hasProd_iff [CommMonoid γ] [TopologicalSpace γ] {G}
    [FunLike G α γ] [MonoidHomClass G α γ] {g : G} (hg : IsInducing g) (f : β -> α) (a : α) :
    HasProd (g ∘ f) (g a) L ↔ HasProd f a L := by
  simp_rw [HasProd, comp_apply, ← _root_.map_prod]
  exact hg.tendsto_nhds_iff.symm

@[to_additive]
/--
theorem `Multipliable.map` / 定理 `Multipliable.map`

English:
theorem Multipliable.map
  statement: [CommMonoid γ] [TopologicalSpace γ]
  proof: (hf.hasProd.map g hg).multipliable

@[to_additive]

中文:
定理 Multipliable.map
  结论: [交换幺半群 γ] [拓扑空间 γ]
  证明: (hf.hasProd.map g hg).multipliable

@[to_additive]
-/
protected theorem Multipliable.map [CommMonoid γ] [TopologicalSpace γ]
    (hf : Multipliable f L) {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    Multipliable (g ∘ f) L :=
  (hf.hasProd.map g hg).multipliable

@[to_additive]
/--
theorem `Multipliable.map_iff_of_leftInverse` / 定理 `Multipliable.map_iff_of_leftInverse`

English:
theorem Multipliable.map_iff_of_leftInverse
  statement: [CommMonoid γ]
  proof: ⟨fun h => by
    have := h.map _ hg'
    rwa [← Function.comp_assoc, hinv.id] at this, fun h => h.map _ hg⟩

@[to_additive]

中文:
定理 Multipliable.map_iff_of_leftInverse
  结论: [交换幺半群 γ]
  证明: ⟨fun h => by
    have := h.map _ hg'
    rwa [← Function.comp_assoc, hinv.id] at this, fun h => h.map _ hg⟩

@[to_additive]
-/
protected theorem Multipliable.map_iff_of_leftInverse [CommMonoid γ]
    [TopologicalSpace γ] {G G'}
    [FunLike G α γ] [MonoidHomClass G α γ] [FunLike G' γ α] [MonoidHomClass G' γ α]
    (g : G) (g' : G') (hg : Continuous g) (hg' : Continuous g') (hinv : Function.LeftInverse g' g) :
    Multipliable (g ∘ f) L ↔ Multipliable f L :=
  ⟨fun h => by
    have := h.map _ hg'
    rwa [← Function.comp_assoc, hinv.id] at this, fun h => h.map _ hg⟩

@[to_additive]
/--
theorem `Multipliable.map_tprod` / 定理 `Multipliable.map_tprod`

English:
theorem Multipliable.map_tprod
  statement: [L.NeBot] [CommMonoid γ] [TopologicalSpace γ] [T2Space γ]
  proof: (HasProd.tprod_eq (HasProd.map hf.hasProd g hg)).symm

@[to_additive]

中文:
定理 Multipliable.map_tprod
  结论: [L.NeBot] [交换幺半群 γ] [拓扑空间 γ] [T2空间 γ]
  证明: (HasProd.tprod_eq (HasProd.map hf.hasProd g hg)).symm

@[to_additive]

Depends on / 依赖: HasProd, HasProd.map, HasProd.tprod_eq, hasProd, hf.hasProd, tprod_eq
-/
theorem Multipliable.map_tprod [L.NeBot] [CommMonoid γ] [TopologicalSpace γ] [T2Space γ]
    (hf : Multipliable f L) {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    g (∏'[L] i, f i) = ∏'[L] i, g (f i) :=
  (HasProd.tprod_eq (HasProd.map hf.hasProd g hg)).symm

@[to_additive]
/--
lemma `Topology.IsClosedEmbedding.map_tprod` / 引理 `Topology.IsClosedEmbedding.map_tprod`

English:
lemma Topology.IsClosedEmbedding.map_tprod
  statement: {ι α α' G : Type*}
  proof: by
  by_cases hL : L.NeBot
  · by_cases h : Multipliable f L
    · exact h.map_tprod g hge.continuous
    · rw [tprod_eq_one_of_not_multipliable h, tprod_eq_one_of_not_multipliable, map_one]
      contrapose h
      -- need to show `g ∘ f` multipliable implies `g` multipliable
      simp only [Multi

中文:
引理 拓扑.是闭嵌入.map_tprod
  结论: {ι α α' G : 类型}
  证明: by
  by_cases hL : L.NeBot
  · by_cases h : Multipliable f L
    · exact h.map_tprod g hge.continuous
    · rw [tprod_eq_one_of_not_multipliable h, tprod_eq_one_of_not_multipliable, map_one]
      contrapose h
      -- need to show `g ∘ f` multipliable implies `g` multipliable
      simp only [Multi

Depends on / 依赖: L.NeBot, Multipliable, continuous, contrapose, h.map_tprod, hge.continuous, map_one, map_tprod, tprod_eq_one_of_not_multipliable
-/
lemma Topology.IsClosedEmbedding.map_tprod {ι α α' G : Type*}
    [CommMonoid α] [CommMonoid α'] [TopologicalSpace α] [TopologicalSpace α'] [T2Space α']
    (f : ι -> α) {L : SummationFilter ι} {g : G} [FunLike G α α'] [MonoidHomClass G α α']
    (hge : Topology.IsClosedEmbedding g) :
    g (∏'[L] i, f i) = ∏'[L] i, g (f i) := by
  by_cases hL : L.NeBot
  · by_cases h : Multipliable f L
    · exact h.map_tprod g hge.continuous
    · rw [tprod_eq_one_of_not_multipliable h, tprod_eq_one_of_not_multipliable, map_one]
      contrapose h
      -- need to show `g ∘ f` multipliable implies `g` multipliable
      simp only [Multipliable, HasProd] at h ⊢
      obtain ⟨b, hb⟩ := h
      obtain ⟨a, ha⟩ : b in Set.range g :=
        hge.isClosed_range.mem_of_tendsto hb (.of_forall <| by simp [← _root_.map_prod])
      use a
      simp [hge.tendsto_nhds_iff, Function.comp_def, ha, hb]
  · simpa [tprod_bot hL] using
      (MonoidHomClass.toMonoidHom g).map_finprod_of_injective hge.injective _

/-- Special case of `Topology.IsClosedEmbedding.map_tprod`, logically weaker but possibly easier
to apply in practice. -/
@[to_additive /-- Special case of `Topology.IsClosedEmbedding.map_tsum`, logically weaker but
possibly easier to apply in practice. -/]
/--
lemma `Function.LeftInverse.map_tprod` / 引理 `Function.LeftInverse.map_tprod`

English:
lemma Function.LeftInverse.map_tprod
  statement: {G : Type*} (f : β -> α) [CommMonoid γ] [TopologicalSpace γ]
  proof: (hgg'.isClosedEmbedding hg' hg).map_tprod _

@[to_additive]

中文:
引理 函数.左逆.map_tprod
  结论: {G : 类型} (f : β -> α) [交换幺半群 γ] [拓扑空间 γ]
  证明: (hgg'.isClosedEmbedding hg' hg).map_tprod _

@[to_additive]

Depends on / 依赖: isClosedEmbedding, map_tprod
-/
lemma Function.LeftInverse.map_tprod {G : Type*} (f : β -> α) [CommMonoid γ] [TopologicalSpace γ]
    [T2Space γ] {g : G} [FunLike G α γ] [MonoidHomClass G α γ] (hg : Continuous g)
    {g' : γ -> α} (hg' : Continuous g') (hgg' : LeftInverse g' g) :
    g (∏'[L] b, f b) = ∏'[L] b, g (f b) :=
  (hgg'.isClosedEmbedding hg' hg).map_tprod _

@[to_additive]
/--
lemma `Topology.IsInducing.multipliable_iff_tprod_comp_mem_range` / 引理 `Topology.IsInducing.multipliable_iff_tprod_comp_mem_range`

English:
lemma Topology.IsInducing.multipliable_iff_tprod_comp_mem_range
  statement: [CommMonoid γ] [TopologicalSpace γ]
  proof: by
  constructor
  · intro hf
    constructor
    · exact hf.map g hg.continuous
    · by_cases hL : L.NeBot
      · exact ⟨_, hf.map_tprod g hg.continuous⟩
      · by_cases hfs : (mulSupport fun x => g (f x)).Finite
        · simp [tprod_bot hL, finprod_eq_prod _ hfs, ← _root_.map_prod]
        · e

中文:
引理 拓扑.是Inducing.multipliable_iff_tprod_comp_mem_range
  结论: [交换幺半群 γ] [拓扑空间 γ]
  证明: by
  constructor
  · intro hf
    constructor
    · exact hf.map g hg.continuous
    · by_cases hL : L.NeBot
      · exact ⟨_, hf.map_tprod g hg.continuous⟩
      · by_cases hfs : (mulSupport fun x => g (f x)).Finite
        · simp [tprod_bot hL, finprod_eq_prod _ hfs, ← _root_.map_prod]
        · e

Depends on / 依赖: Finite, L.NeBot, _root_, _root_.map_prod, comp_apply, continuous, finprod_eq_prod, finprod_of_infinite_mulSupport, hasProd, hasProd_iff, hf.map, hf.map_tprod, hg.continuous, hg.hasProd_iff, hgf.hasProd, map_prod, map_tprod, mulSupport, simp_rw, tprod_bot
-/
lemma Topology.IsInducing.multipliable_iff_tprod_comp_mem_range [CommMonoid γ] [TopologicalSpace γ]
    [T2Space γ] {G} [FunLike G α γ] [MonoidHomClass G α γ] {g : G} (hg : IsInducing g) (f : β -> α) :
    Multipliable f L ↔ Multipliable (g ∘ f) L ∧ ∏'[L] i, g (f i) in Set.range g := by
  constructor
  · intro hf
    constructor
    · exact hf.map g hg.continuous
    · by_cases hL : L.NeBot
      · exact ⟨_, hf.map_tprod g hg.continuous⟩
      · by_cases hfs : (mulSupport fun x => g (f x)).Finite
        · simp [tprod_bot hL, finprod_eq_prod _ hfs, ← _root_.map_prod]
        · exact ⟨1, by simp [tprod_bot hL, finprod_of_infinite_mulSupport hfs]⟩
  · rintro ⟨hgf, a, ha⟩
    use a
    have := hgf.hasProd
    simp_rw [comp_apply, ← ha] at this
    exact (hg.hasProd_iff f a).mp this

/-- "A special case of `Multipliable.map_iff_of_leftInverse` for convenience" -/
@[to_additive /-- A special case of `Summable.map_iff_of_leftInverse` for convenience -/]
/--
theorem `Multipliable.map_iff_of_equiv` / 定理 `Multipliable.map_iff_of_equiv`

English:
theorem Multipliable.map_iff_of_equiv
  statement: [CommMonoid γ] [TopologicalSpace γ] {G}
  proof: Multipliable.map_iff_of_leftInverse g (g : α ≃* γ).symm hg hg' (EquivLike.left_inv g)

@[to_additive]

中文:
定理 Multipliable.map_iff_of_equiv
  结论: [交换幺半群 γ] [拓扑空间 γ] {G}
  证明: Multipliable.map_iff_of_leftInverse g (g : α ≃* γ).symm hg hg' (EquivLike.left_inv g)

@[to_additive]
-/
protected theorem Multipliable.map_iff_of_equiv [CommMonoid γ] [TopologicalSpace γ] {G}
    [EquivLike G α γ] [MulEquivClass G α γ] (g : G) (hg : Continuous g)
    (hg' : Continuous (EquivLike.inv g : γ -> α)) :
    Multipliable (g ∘ f) L ↔ Multipliable f L :=
  Multipliable.map_iff_of_leftInverse g (g : α ≃* γ).symm hg hg' (EquivLike.left_inv g)

@[to_additive]
/--
theorem `Function.Surjective.multipliable_iff_of_hasProd_iff` / 定理 `Function.Surjective.multipliable_iff_of_hasProd_iff`

English:
theorem Function.Surjective.multipliable_iff_of_hasProd_iff
  statement: {α' : Type*} [CommMonoid α']
  proof: hes.exists.trans exists_congr @he

中文:
定理 函数.满射.multipliable_iff_of_hasProd_iff
  结论: {α' : 类型} [交换幺半群 α']
  证明: hes.exists.trans exists_congr @he

Depends on / 依赖: exists_congr, hes.exists.trans
-/
theorem Function.Surjective.multipliable_iff_of_hasProd_iff {α' : Type*} [CommMonoid α']
    [TopologicalSpace α'] {e : α' -> α} (hes : Function.Surjective e) {f : β -> α} {g : γ -> α'}
    (he : forall {a}, HasProd f (e a) ↔ HasProd g a) : Multipliable f ↔ Multipliable g :=
hes.exists.trans exists_congr @he

variable [ContinuousMul α]

@[to_additive]
/--
theorem `HasProd.mul` / 定理 `HasProd.mul`

English:
theorem HasProd.mul
  given: (hf : HasProd f a L) (hg : HasProd g b L)
  proof: by
  dsimp only [HasProd] at hf hg ⊢
  simp_rw [prod_mul_distrib]
  exact hf.mul hg

@[to_additive]

中文:
定理 有积类型.mul
  条件: (hf : 有积类型 f a L) (hg : 有积类型 g b L)
  证明: by
  dsimp only [HasProd] at hf hg ⊢
  simp_rw [prod_mul_distrib]
  exact hf.mul hg

@[to_additive]

Depends on / 依赖: HasProd, hf.mul, prod_mul_distrib, simp_rw
-/
theorem HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) :
    HasProd (fun b => f b * g b) (a * b) L := by
  dsimp only [HasProd] at hf hg ⊢
  simp_rw [prod_mul_distrib]
  exact hf.mul hg

@[to_additive]
/--
theorem `Multipliable.mul` / 定理 `Multipliable.mul`

English:
theorem Multipliable.mul
  given: (hf : Multipliable f L) (hg : Multipliable g L)
  proof: (hf.hasProd.mul hg.hasProd).multipliable

@[to_additive]

中文:
定理 Multipliable.mul
  条件: (hf : Multipliable f L) (hg : Multipliable g L)
  证明: (hf.hasProd.mul hg.hasProd).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hf.hasProd.mul, hg.hasProd, multipliable
-/
theorem Multipliable.mul (hf : Multipliable f L) (hg : Multipliable g L) :
    Multipliable (fun b => f b * g b) L :=
  (hf.hasProd.mul hg.hasProd).multipliable

@[to_additive]
/--
lemma `HasProd.pow` / 引理 `HasProd.pow`

English:
lemma HasProd.pow
  given: (hf : HasProd f a L) (n : Nat)
  statement: HasProd (f · ^ n) (a ^ n) L
  proof: by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

@[to_additive]

中文:
引理 有积类型.pow
  条件: (hf : 有积类型 f a L) (n : 自然数)
  结论: 有积类型 (f · ^ n) (a ^ n) L
  证明: by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

@[to_additive]

Depends on / 依赖: hn.mul, pow_succ
-/
lemma HasProd.pow (hf : HasProd f a L) (n : Nat) : HasProd (f · ^ n) (a ^ n) L := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

@[to_additive]
/--
lemma `Multipliable.pow` / 引理 `Multipliable.pow`

English:
lemma Multipliable.pow
  given: (hf : Multipliable f L) (n : Nat)
  statement: Multipliable (f · ^ n) L
  proof: (hf.hasProd.pow n).multipliable

@[to_additive]

中文:
引理 Multipliable.pow
  条件: (hf : Multipliable f L) (n : 自然数)
  结论: Multipliable (f · ^ n) L
  证明: (hf.hasProd.pow n).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hf.hasProd.pow, multipliable
-/
lemma Multipliable.pow (hf : Multipliable f L) (n : Nat) : Multipliable (f · ^ n) L :=
  (hf.hasProd.pow n).multipliable

@[to_additive]
/--
theorem `hasProd_prod` / 定理 `hasProd_prod`

English:
theorem hasProd_prod
  given: {f : γ -> β -> α} {a : γ -> α} {s : Finset γ}
  proof: by
  classical
exact Finset.induction_on s (by simp) by
    simp +contextual only [mem_insert, forall_eq_or_imp, not_false_iff,
      prod_insert, and_imp]
    exact fun x s _ IH hx h => hx.mul (IH h)

@[to_additive]

中文:
定理 hasProd_prod
  条件: {f : γ -> β -> α} {a : γ -> α} {s : 有限集 γ}
  证明: by
  classical
exact Finset.induction_on s (by simp) by
    simp +contextual only [mem_insert, forall_eq_or_imp, not_false_iff,
      prod_insert, and_imp]
    exact fun x s _ IH hx h => hx.mul (IH h)

@[to_additive]

Depends on / 依赖: Finset, Finset.induction_on, and_imp, classical, contextual, forall_eq_or_imp, hx.mul, induction_on, mem_insert, not_false_iff, prod_insert
-/
theorem hasProd_prod {f : γ -> β -> α} {a : γ -> α} {s : Finset γ} :
    (forall i in s, HasProd (f i) (a i) L) -> HasProd (fun b => ∏ i in s, f i b) (∏ i in s, a i) L := by
  classical
exact Finset.induction_on s (by simp) by
    simp +contextual only [mem_insert, forall_eq_or_imp, not_false_iff,
      prod_insert, and_imp]
    exact fun x s _ IH hx h => hx.mul (IH h)

@[to_additive]
/--
theorem `multipliable_prod` / 定理 `multipliable_prod`

English:
theorem multipliable_prod
  statement: {f : γ -> β -> α} {s : Finset γ}
  proof: (hasProd_prod fun i hi => (hf i hi).hasProd).multipliable

@[to_additive]

中文:
定理 multipliable_prod
  结论: {f : γ -> β -> α} {s : 有限集 γ}
  证明: (hasProd_prod fun i hi => (hf i hi).hasProd).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hasProd_prod, multipliable
-/
theorem multipliable_prod {f : γ -> β -> α} {s : Finset γ}
    (hf : forall i in s, Multipliable (f i) L) : Multipliable (fun b => ∏ i in s, f i b) L :=
  (hasProd_prod fun i hi => (hf i hi).hasProd).multipliable

@[to_additive]
/--
theorem `HasProd.mul_disjoint` / 定理 `HasProd.mul_disjoint`

English:
theorem HasProd.mul_disjoint
  statement: {s t : Set β} (hs : Disjoint s t) (ha : HasProd (f ∘ (↑) : s -> α) a)
  proof: by
  rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Set.mulIndicator_union_of_disjoint hs]
  exact ha.mul hb

@[to_additive]

中文:
定理 有积类型.mul_disjoint
  结论: {s t : 集合 β} (hs : Disjoint s t) (ha : 有积类型 (f ∘ (↑) : s -> α) a)
  证明: by
  rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Set.mulIndicator_union_of_disjoint hs]
  exact ha.mul hb

@[to_additive]

Depends on / 依赖: Set.mulIndicator_union_of_disjoint, ha.mul, hasProd_subtype_iff_mulIndicator, mulIndicator_union_of_disjoint
-/
theorem HasProd.mul_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasProd (f ∘ (↑) : s -> α) a)
    (hb : HasProd (f ∘ (↑) : t -> α) b) : HasProd (f ∘ (↑) : (s union t : Set β) -> α) (a * b) := by
  rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Set.mulIndicator_union_of_disjoint hs]
  exact ha.mul hb

@[to_additive]
/--
theorem `hasProd_prod_disjoint` / 定理 `hasProd_prod_disjoint`

English:
theorem hasProd_prod_disjoint
  statement: {ι} (s : Finset ι) {t : ι -> Set β} {a : ι -> α}
  proof: by
  simp_rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Finset.mulIndicator_biUnion _ _ hs]
  exact hasProd_prod hf

@[to_additive]

中文:
定理 hasProd_prod_disjoint
  结论: {ι} (s : 有限集 ι) {t : ι -> 集合 β} {a : ι -> α}
  证明: by
  simp_rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Finset.mulIndicator_biUnion _ _ hs]
  exact hasProd_prod hf

@[to_additive]

Depends on / 依赖: Finset, Finset.mulIndicator_biUnion, hasProd_prod, hasProd_subtype_iff_mulIndicator, mulIndicator_biUnion, simp_rw
-/
theorem hasProd_prod_disjoint {ι} (s : Finset ι) {t : ι -> Set β} {a : ι -> α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : forall i in s, HasProd (f ∘ (↑) : t i -> α) (a i)) :
    HasProd (f ∘ (↑) : (⋃ i in s, t i) -> α) (∏ i in s, a i) := by
  simp_rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Finset.mulIndicator_biUnion _ _ hs]
  exact hasProd_prod hf

@[to_additive]
/--
theorem `HasProd.mul_isCompl` / 定理 `HasProd.mul_isCompl`

English:
theorem HasProd.mul_isCompl
  statement: {s t : Set β} (hs : IsCompl s t) (ha : HasProd (f ∘ (↑) : s -> α) a)
  proof: by
  simpa [← hs.compl_eq] using
    (hasProd_subtype_iff_mulIndicator.1 ha).mul (hasProd_subtype_iff_mulIndicator.1 hb)

@[to_additive]

中文:
定理 有积类型.mul_isCompl
  结论: {s t : 集合 β} (hs : 是补集 s t) (ha : 有积类型 (f ∘ (↑) : s -> α) a)
  证明: by
  simpa [← hs.compl_eq] using
    (hasProd_subtype_iff_mulIndicator.1 ha).mul (hasProd_subtype_iff_mulIndicator.1 hb)

@[to_additive]

Depends on / 依赖: compl_eq, hasProd_subtype_iff_mulIndicator, hs.compl_eq
-/
theorem HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasProd (f ∘ (↑) : s -> α) a)
    (hb : HasProd (f ∘ (↑) : t -> α) b) : HasProd f (a * b) := by
  simpa [← hs.compl_eq] using
    (hasProd_subtype_iff_mulIndicator.1 ha).mul (hasProd_subtype_iff_mulIndicator.1 hb)

@[to_additive]
/--
theorem `HasProd.mul_compl` / 定理 `HasProd.mul_compl`

English:
theorem HasProd.mul_compl
  statement: {s : Set β} (ha : HasProd (f ∘ (↑) : s -> α) a)
  proof: ha.mul_isCompl isCompl_compl hb

@[to_additive]

中文:
定理 有积类型.mul_compl
  结论: {s : 集合 β} (ha : 有积类型 (f ∘ (↑) : s -> α) a)
  证明: ha.mul_isCompl isCompl_compl hb

@[to_additive]

Depends on / 依赖: ha.mul_isCompl, isCompl_compl, mul_isCompl
-/
theorem HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) : s -> α) a)
    (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl hb

@[to_additive]
/--
theorem `Multipliable.mul_compl` / 定理 `Multipliable.mul_compl`

English:
theorem Multipliable.mul_compl
  statement: {s : Set β} (hs : Multipliable (f ∘ (↑) : s -> α))
  proof: (hs.hasProd.mul_compl hsc.hasProd).multipliable

@[to_additive]

中文:
定理 Multipliable.mul_compl
  结论: {s : 集合 β} (hs : Multipliable (f ∘ (↑) : s -> α))
  证明: (hs.hasProd.mul_compl hsc.hasProd).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hs.hasProd.mul_compl, hsc.hasProd, mul_compl, multipliable
-/
theorem Multipliable.mul_compl {s : Set β} (hs : Multipliable (f ∘ (↑) : s -> α))
    (hsc : Multipliable (f ∘ (↑) : (sᶜ : Set β) -> α)) : Multipliable f :=
  (hs.hasProd.mul_compl hsc.hasProd).multipliable

@[to_additive]
/--
theorem `HasProd.compl_mul` / 定理 `HasProd.compl_mul`

English:
theorem HasProd.compl_mul
  statement: {s : Set β} (ha : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) a)
  proof: ha.mul_isCompl isCompl_compl.symm hb

@[to_additive]

中文:
定理 有积类型.compl_mul
  结论: {s : 集合 β} (ha : 有积类型 (f ∘ (↑) : (sᶜ : 集合 β) -> α) a)
  证明: ha.mul_isCompl isCompl_compl.symm hb

@[to_additive]

Depends on / 依赖: ha.mul_isCompl, isCompl_compl, isCompl_compl.symm, mul_isCompl
-/
theorem HasProd.compl_mul {s : Set β} (ha : HasProd (f ∘ (↑) : (sᶜ : Set β) -> α) a)
    (hb : HasProd (f ∘ (↑) : s -> α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl.symm hb

@[to_additive]
/--
theorem `Multipliable.compl_add` / 定理 `Multipliable.compl_add`

English:
theorem Multipliable.compl_add
  statement: {s : Set β} (hs : Multipliable (f ∘ (↑) : (sᶜ : Set β) -> α))
  proof: (hs.hasProd.compl_mul hsc.hasProd).multipliable

中文:
定理 Multipliable.compl_add
  结论: {s : 集合 β} (hs : Multipliable (f ∘ (↑) : (sᶜ : 集合 β) -> α))
  证明: (hs.hasProd.compl_mul hsc.hasProd).multipliable

Depends on / 依赖: compl_mul, hasProd, hs.hasProd.compl_mul, hsc.hasProd, multipliable
-/
theorem Multipliable.compl_add {s : Set β} (hs : Multipliable (f ∘ (↑) : (sᶜ : Set β) -> α))
    (hsc : Multipliable (f ∘ (↑) : s -> α)) : Multipliable f :=
  (hs.hasProd.compl_mul hsc.hasProd).multipliable

/-- Version of `HasProd.update` for `CommMonoid` rather than `CommGroup`.
Rather than showing that `f.update` has a specific product in terms of `HasProd`,
it gives a relationship between the products of `f` and `f.update` given that both exist. -/
@[to_additive /-- Version of `HasSum.update` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that `f.update` has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/]
/--
theorem `HasProd.update'` / 定理 `HasProd.update'`

English:
theorem HasProd.update'
  statement: [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
  proof: by
  have : forall b', f b' * ite (b' = b) x 1 = update f b x b' * ite (b' = b) (f b) 1 := by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using! mul_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.mul (hasProd

中文:
定理 有积类型.update'
  结论: [L.LeAtTop] [L.NeBot] {α : 类型} [拓扑空间 α] [交换幺半群 α]
  证明: by
  have : forall b', f b' * ite (b' = b) x 1 = update f b x b' * ite (b' = b) (f b) 1 := by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using! mul_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.mul (hasProd

Depends on / 依赖: Function, Function.update_apply, HasProd, HasProd.unique, eq_self_iff_true, hasProd_ite_eq, hf.mul, if_false, mul_comm, simp_rw, split_ifs, unique, update, update_apply
-/
theorem HasProd.update' [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
    [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β -> α} {a a' : α} (hf : HasProd f a L)
    (b : β) (x : α) (hf' : HasProd (update f b x) a' L) :
    a * x = a' * f b := by
  have : forall b', f b' * ite (b' = b) x 1 = update f b x b' * ite (b' = b) (f b) 1 := by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using! mul_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.mul (hasProd_ite_eq b x L)
  simp_rw [this] at h
  exact HasProd.unique h (hf'.mul (hasProd_ite_eq b (f b) L))

/-- Version of `hasProd_ite_div_hasProd` for `CommMonoid` rather than `CommGroup`.
Rather than showing that the `ite` expression has a specific product in terms of `HasProd`, it gives
a relationship between the products of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
@[to_additive /-- Version of `hasSum_ite_sub_hasSum` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that the `ite` expression has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/]
/--
theorem `eq_mul_of_hasProd_ite` / 定理 `eq_mul_of_hasProd_ite`

English:
theorem eq_mul_of_hasProd_ite
  statement: [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
  proof: by
  refine (mul_one a).symm.trans (hf.update' b 1 ?_)
  convert! hf'
  apply update_apply

中文:
定理 eq_mul_of_hasProd_ite
  结论: [L.LeAtTop] [L.NeBot] {α : 类型} [拓扑空间 α] [交换幺半群 α]
  证明: by
  refine (mul_one a).symm.trans (hf.update' b 1 ?_)
  convert! hf'
  apply update_apply

Depends on / 依赖: convert, hf.update, mul_one, symm.trans, update, update_apply
-/
theorem eq_mul_of_hasProd_ite [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
    [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β -> α} {a : α} (hf : HasProd f a L) (b : β)
    (a' : α) (hf' : HasProd (fun n => ite (n = b) 1 (f n)) a' L) : a = a' * f b := by
  refine (mul_one a).symm.trans (hf.update' b 1 ?_)
  convert! hf'
  apply update_apply

end HasProd

section tprod

variable [CommMonoid α] [TopologicalSpace α] {f g : β -> α} {L : SummationFilter β}

@[to_additive]
/--
theorem `tprod_congr_set_coe` / 定理 `tprod_congr_set_coe`

English:
theorem tprod_congr_set_coe
  given: (f : β -> α) {s t : Set β} (h : s = t)
  proof: by rw [h]

@[to_additive]

中文:
定理 tprod_congr_set_coe
  条件: (f : β -> α) {s t : 集合 β} (h : s = t)
  证明: by rw [h]

@[to_additive]
-/
theorem tprod_congr_set_coe (f : β -> α) {s t : Set β} (h : s = t) :
    ∏' x : s, f x = ∏' x : t, f x := by rw [h]

@[to_additive]
/--
theorem `tprod_congr_subtype` / 定理 `tprod_congr_subtype`

English:
theorem tprod_congr_subtype
  given: (f : β -> α) {P Q : β -> Prop} (h : forall x, P x ↔ Q x)
  proof: tprod_congr_set_coe f Set.ext h

@[to_additive]

中文:
定理 tprod_congr_subtype
  条件: (f : β -> α) {P Q : β -> 命题} (h : 对任意 x, P x ↔ Q x)
  证明: tprod_congr_set_coe f Set.ext h

@[to_additive]

Depends on / 依赖: Set.ext, tprod_congr_set_coe
-/
theorem tprod_congr_subtype (f : β -> α) {P Q : β -> Prop} (h : forall x, P x ↔ Q x) :
    ∏' x : {x // P x}, f x = ∏' x : {x // Q x}, f x :=
tprod_congr_set_coe f Set.ext h

@[to_additive]
/--
theorem `tprod_eq_finprod` / 定理 `tprod_eq_finprod`

English:
theorem tprod_eq_finprod
  given: [L.LeAtTop] (hf : HasFiniteMulSupport f)
  proof: by
  simp [tprod_def, multipliable_of_hasFiniteMulSupport hf, show Set.Finite _ from hf,
    show L.HasSupport by infer_instance]

@[to_additive]

中文:
定理 tprod_eq_finprod
  条件: [L.LeAtTop] (hf : HasFiniteMulSupport f)
  证明: by
  simp [tprod_def, multipliable_of_hasFiniteMulSupport hf, show Set.Finite _ from hf,
    show L.HasSupport by infer_instance]

@[to_additive]

Depends on / 依赖: Finite, HasSupport, L.HasSupport, Set.Finite, infer_instance, multipliable_of_hasFiniteMulSupport, tprod_def
-/
theorem tprod_eq_finprod [L.LeAtTop] (hf : HasFiniteMulSupport f) :
    ∏'[L] b, f b = ∏ᶠ b, f b := by
  simp [tprod_def, multipliable_of_hasFiniteMulSupport hf, show Set.Finite _ from hf,
    show L.HasSupport by infer_instance]

@[to_additive]
/--
theorem `tprod_eq_prod'` / 定理 `tprod_eq_prod'`

English:
theorem tprod_eq_prod'
  given: [L.LeAtTop] {s : Finset β} (hf : mulSupport f subseteq s)
  proof: by
  rw [tprod_eq_finprod (s.finite_toSet.subset hf)]; rw [finprod_eq_prod_of_mulSupport_subset _ hf]

@[to_additive]

中文:
定理 tprod_eq_prod'
  条件: [L.LeAtTop] {s : 有限集 β} (hf : mulSupport f subseteq s)
  证明: by
  rw [tprod_eq_finprod (s.finite_toSet.subset hf)]; rw [finprod_eq_prod_of_mulSupport_subset _ hf]

@[to_additive]

Depends on / 依赖: finite_toSet, finprod_eq_prod_of_mulSupport_subset, s.finite_toSet.subset, subset, tprod_eq_finprod
-/
theorem tprod_eq_prod' [L.LeAtTop] {s : Finset β} (hf : mulSupport f subseteq s) :
    ∏'[L] b, f b = ∏ b in s, f b := by
  rw [tprod_eq_finprod (s.finite_toSet.subset hf)]; rw [finprod_eq_prod_of_mulSupport_subset _ hf]

@[to_additive]
/--
theorem `tprod_eq_prod` / 定理 `tprod_eq_prod`

English:
theorem tprod_eq_prod
  given: [L.LeAtTop] {s : Finset β} (hf : forall b ∉ s, f b = 1)
  proof: tprod_eq_prod' mulSupport_subset_iff'.2 hf

@[to_additive (attr := simp)]

中文:
定理 tprod_eq_prod
  条件: [L.LeAtTop] {s : 有限集 β} (hf : 对任意 b ∉ s, f b = 1)
  证明: tprod_eq_prod' mulSupport_subset_iff'.2 hf

@[to_additive (attr := simp)]

Depends on / 依赖: mulSupport_subset_iff, tprod_eq_prod
-/
theorem tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : forall b ∉ s, f b = 1) :
    ∏'[L] b, f b = ∏ b in s, f b :=
tprod_eq_prod' mulSupport_subset_iff'.2 hf

@[to_additive (attr := simp)]
/--
theorem `tprod_one` / 定理 `tprod_one`

English:
theorem tprod_one
  statement: ∏'[L] _, (1 : α) = 1
  proof: by
  rw [tprod_def]; rw [dif_pos multipliable_one]; rw [mulSupport_fun_one]; rw [Set.empty_inter]; rw [Set.mulIndicator_one]; rw [finprod_one]; rw [eq_true_intro hasProd_one]; rw [if_true]; rw [ite_self]

@[to_additive (attr := simp)]

中文:
定理 tprod_one
  结论: ∏'[L] _, (1 : α) = 1
  证明: by
  rw [tprod_def]; rw [dif_pos multipliable_one]; rw [mulSupport_fun_one]; rw [Set.empty_inter]; rw [Set.mulIndicator_one]; rw [finprod_one]; rw [eq_true_intro hasProd_one]; rw [if_true]; rw [ite_self]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.empty_inter, Set.mulIndicator_one, dif_pos, empty_inter, eq_true_intro, finprod_one, hasProd_one, if_true, ite_self, mulIndicator_one, mulSupport_fun_one, multipliable_one, tprod_def
-/
theorem tprod_one : ∏'[L] _, (1 : α) = 1 := by
  rw [tprod_def]; rw [dif_pos multipliable_one]; rw [mulSupport_fun_one]; rw [Set.empty_inter]; rw [Set.mulIndicator_one]; rw [finprod_one]; rw [eq_true_intro hasProd_one]; rw [if_true]; rw [ite_self]

@[to_additive (attr := simp)]
/--
theorem `tprod_empty` / 定理 `tprod_empty`

English:
theorem tprod_empty
  given: [IsEmpty β]
  statement: ∏'[L] b, f b = 1
  proof: by
  convert! tprod_one (L := L)

@[to_additive]

中文:
定理 tprod_empty
  条件: [是空 β]
  结论: ∏'[L] b, f b = 1
  证明: by
  convert! tprod_one (L := L)

@[to_additive]

Depends on / 依赖: convert, tprod_one
-/
theorem tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1 := by
  convert! tprod_one (L := L)

@[to_additive]
/--
theorem `tprod_congr` / 定理 `tprod_congr`

English:
theorem tprod_congr
  statement: {f g : β -> α}
  proof: congr_arg (tprod · L) (funext hfg)

@[to_additive]

中文:
定理 tprod_congr
  结论: {f g : β -> α}
  证明: congr_arg (tprod · L) (funext hfg)

@[to_additive]

Depends on / 依赖: congr_arg
-/
theorem tprod_congr {f g : β -> α}
    (hfg : forall b, f b = g b) : ∏'[L] b, f b = ∏'[L] b, g b :=
  congr_arg (tprod · L) (funext hfg)

@[to_additive]
/--
theorem `tprod_congr₂` / 定理 `tprod_congr₂`

English:
theorem tprod_congr₂
  statement: {f g : β -> γ -> α} {M : SummationFilter γ}
  proof: tprod_congr fun b => tprod_congr fun c => hfg b c

@[to_additive (attr := simp)]

中文:
定理 tprod_congr₂
  结论: {f g : β -> γ -> α} {M : SummationFilter γ}
  证明: tprod_congr fun b => tprod_congr fun c => hfg b c

@[to_additive (attr := simp)]

Depends on / 依赖: tprod_congr
-/
theorem tprod_congr₂ {f g : β -> γ -> α} {M : SummationFilter γ}
    (hfg : forall b c, f b c = g b c) : ∏'[L] b, ∏'[M] c, f b c = ∏'[L] b, ∏'[M] c, g b c :=
  tprod_congr fun b => tprod_congr fun c => hfg b c

@[to_additive (attr := simp)]
/--
theorem `tprod_fintype` / 定理 `tprod_fintype`

English:
theorem tprod_fintype
  given: [L.LeAtTop] [Fintype β] (f : β -> α)
  statement: ∏'[L] b, f b = ∏ b, f b
  proof: by
  apply tprod_eq_prod; simp

@[to_additive]

中文:
定理 tprod_fintype
  条件: [L.LeAtTop] [有限类型 β] (f : β -> α)
  结论: ∏'[L] b, f b = ∏ b, f b
  证明: by
  apply tprod_eq_prod; simp

@[to_additive]

Depends on / 依赖: tprod_eq_prod
-/
theorem tprod_fintype [L.LeAtTop] [Fintype β] (f : β -> α) : ∏'[L] b, f b = ∏ b, f b := by
  apply tprod_eq_prod; simp

@[to_additive]
/--
theorem `prod_eq_tprod_mulIndicator` / 定理 `prod_eq_tprod_mulIndicator`

English:
theorem prod_eq_tprod_mulIndicator
  given: (f : β -> α) (s : Finset β) (L := unconditional β) [L.LeAtTop]
  proof: by
  rw [tprod_eq_prod' (Set.mulSupport_mulIndicator_subset)]; rw [Finset.prod_mulIndicator_subset _ Finset.Subset.rfl]

@[to_additive]

中文:
定理 prod_eq_tprod_mulIndicator
  条件: (f : β -> α) (s : 有限集 β) (L := unconditional β) [L.LeAtTop]
  证明: by
  rw [tprod_eq_prod' (Set.mulSupport_mulIndicator_subset)]; rw [Finset.prod_mulIndicator_subset _ Finset.Subset.rfl]

@[to_additive]

Depends on / 依赖: L.LeAtTop, LeAtTop, unconditional
-/
theorem prod_eq_tprod_mulIndicator (f : β -> α) (s : Finset β) (L := unconditional β) [L.LeAtTop] :
    ∏ x in s, f x = ∏'[L] x, Set.mulIndicator (↑s) f x := by
  rw [tprod_eq_prod' (Set.mulSupport_mulIndicator_subset)]; rw [Finset.prod_mulIndicator_subset _ Finset.Subset.rfl]

@[to_additive]
/--
theorem `tprod_bool` / 定理 `tprod_bool`

English:
theorem tprod_bool
  given: (f : Bool -> α)
  statement: ∏' i : Bool, f i = f false * f true
  proof: by
  rw [tprod_fintype]; rw [Fintype.prod_bool]; rw [mul_comm]

@[to_additive]

中文:
定理 tprod_bool
  条件: (f : 布尔值 -> α)
  结论: ∏' i : 布尔值, f i = f false * f true
  证明: by
  rw [tprod_fintype]; rw [Fintype.prod_bool]; rw [mul_comm]

@[to_additive]

Depends on / 依赖: Fintype, Fintype.prod_bool, mul_comm, prod_bool, tprod_fintype
-/
theorem tprod_bool (f : Bool -> α) : ∏' i : Bool, f i = f false * f true := by
  rw [tprod_fintype]; rw [Fintype.prod_bool]; rw [mul_comm]

@[to_additive]
/--
theorem `tprod_eq_mulSingle` / 定理 `tprod_eq_mulSingle`

English:
theorem tprod_eq_mulSingle
  given: [L.LeAtTop] {f : β -> α} (b : β) (hf : forall b' != b, f b' = 1)
  proof: by
  rw [tprod_eq_prod (s := {b})]; rw [prod_singleton]
  exact fun b' hb' => hf b' (by simpa using hb')

@[to_additive]

中文:
定理 tprod_eq_mulSingle
  条件: [L.LeAtTop] {f : β -> α} (b : β) (hf : 对任意 b' != b, f b' = 1)
  证明: by
  rw [tprod_eq_prod (s := {b})]; rw [prod_singleton]
  exact fun b' hb' => hf b' (by simpa using hb')

@[to_additive]

Depends on / 依赖: prod_singleton, tprod_eq_prod
-/
theorem tprod_eq_mulSingle [L.LeAtTop] {f : β -> α} (b : β) (hf : forall b' != b, f b' = 1) :
    ∏'[L] b, f b = f b := by
  rw [tprod_eq_prod (s := {b})]; rw [prod_singleton]
  exact fun b' hb' => hf b' (by simpa using hb')

@[to_additive]
/--
theorem `tprod_tprod_eq_mulSingle` / 定理 `tprod_tprod_eq_mulSingle`

English:
theorem tprod_tprod_eq_mulSingle
  proof: calc
    ∏' (b') (c'), f b' c' = ∏' b', f b' c := tprod_congr fun b' => tprod_eq_mulSingle _ (hfc b')
    _ = f b c := tprod_eq_mulSingle _ hfb

@[to_additive (attr := simp)]

中文:
定理 tprod_tprod_eq_mulSingle
  证明: calc
    ∏' (b') (c'), f b' c' = ∏' b', f b' c := tprod_congr fun b' => tprod_eq_mulSingle _ (hfc b')
    _ = f b c := tprod_eq_mulSingle _ hfb

@[to_additive (attr := simp)]

Depends on / 依赖: tprod_congr, tprod_eq_mulSingle
-/
theorem tprod_tprod_eq_mulSingle
    (f : β -> γ -> α) (b : β) (c : γ) (hfb : forall b' != b, f b' c = 1)
    (hfc : forall b', forall c' != c, f b' c' = 1) : ∏' (b') (c'), f b' c' = f b c :=
  calc
    ∏' (b') (c'), f b' c' = ∏' b', f b' c := tprod_congr fun b' => tprod_eq_mulSingle _ (hfc b')
    _ = f b c := tprod_eq_mulSingle _ hfb

@[to_additive (attr := simp)]
/--
theorem `tprod_ite_eq` / 定理 `tprod_ite_eq`

English:
theorem tprod_ite_eq
  statement: (b : β) [DecidablePred (· = b)] (a : β -> α)
  proof: by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive (attr := simp)]

中文:
定理 tprod_ite_eq
  结论: (b : β) [DecidablePred (· = b)] (a : β -> α)
  证明: by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive (attr := simp)]

Depends on / 依赖: L.LeAtTop, LeAtTop, fast_instance, unconditional
-/
theorem tprod_ite_eq (b : β) [DecidablePred (· = b)] (a : β -> α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b' = b then a b' else 1) = a b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive (attr := simp)]
/--
theorem `tprod_ite_eq'` / 定理 `tprod_ite_eq'`

English:
theorem tprod_ite_eq'
  statement: (b : β) [DecidablePred (b = ·)] (a : β -> α)
  proof: by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

@[to_additive]

中文:
定理 tprod_ite_eq'
  结论: (b : β) [DecidablePred (b = ·)] (a : β -> α)
  证明: by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

@[to_additive]

Depends on / 依赖: L.LeAtTop, LeAtTop, unconditional
-/
theorem tprod_ite_eq' (b : β) [DecidablePred (b = ·)] (a : β -> α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b = b' then a b' else 1) = a b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb'.symm]

@[to_additive]
/--
theorem `Finset.tprod_subtype` / 定理 `Finset.tprod_subtype`

English:
theorem Finset.tprod_subtype
  given: (s : Finset β) (f : β -> α)
  proof: by
  rw [← prod_attach]; exact tprod_fintype _

@[to_additive]

中文:
定理 有限集.tprod_subtype
  条件: (s : 有限集 β) (f : β -> α)
  证明: by
  rw [← prod_attach]; exact tprod_fintype _

@[to_additive]

Depends on / 依赖: g.toRiemannianMetric, prod_attach, toRiemannianMetric, tprod_fintype
-/
theorem Finset.tprod_subtype (s : Finset β) (f : β -> α) :
    ∏' x : { x // x in s }, f x = ∏ x in s, f x := by
  rw [← prod_attach]; exact tprod_fintype _

@[to_additive]
/--
theorem `Finset.tprod_subtype'` / 定理 `Finset.tprod_subtype'`

English:
theorem Finset.tprod_subtype'
  given: (s : Finset β) (f : β -> α)
  proof: by
  simp [prod_attach]

@[to_additive]

中文:
定理 有限集.tprod_subtype'
  条件: (s : 有限集 β) (f : β -> α)
  证明: by
  simp [prod_attach]

@[to_additive]

Depends on / 依赖: prod_attach
-/
theorem Finset.tprod_subtype' (s : Finset β) (f : β -> α) :
    ∏' x : (s : Set β), f x = ∏ x in s, f x := by
  simp [prod_attach]

@[to_additive]
/--
theorem `tprod_singleton` / 定理 `tprod_singleton`

English:
theorem tprod_singleton
  given: (b : β) (f : β -> α)
  statement: ∏' x : ({b} : Set β), f x = f b
  proof: by simp

中文:
定理 tprod_singleton
  条件: (b : β) (f : β -> α)
  结论: ∏' x : ({b} : 集合 β), f x = f b
  证明: by simp
-/
theorem tprod_singleton (b : β) (f : β -> α) : ∏' x : ({b} : Set β), f x = f b := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `Function.Injective.tprod_eq` / 定理 `Function.Injective.tprod_eq`

English:
theorem Function.Injective.tprod_eq
  statement: {g : γ -> β} (hg : Injective g) {f : β -> α}
  proof: by
  classical
  have : mulSupport f = g '' mulSupport (f ∘ g) := by
    rw [mulSupport_comp_eq_preimage]; rw [Set.image_preimage_eq_iff.2 hf]
  rw [← Function.comp_def]
  by_cases hf_fin : (mulSupport f).Finite
  · have hfg_fin : (mulSupport (f ∘ g)).Finite := hf_fin.preimage hg.injOn
    lift g to

中文:
定理 函数.单射.tprod_eq
  结论: {g : γ -> β} (hg : 单射 g) {f : β -> α}
  证明: by
  classical
  have : mulSupport f = g '' mulSupport (f ∘ g) := by
    rw [mulSupport_comp_eq_preimage]; rw [Set.image_preimage_eq_iff.2 hf]
  rw [← Function.comp_def]
  by_cases hf_fin : (mulSupport f).Finite
  · have hfg_fin : (mulSupport (f ∘ g)).Finite := hf_fin.preimage hg.injOn
    lift g to

Depends on / 依赖: Finite, Finset, Finset.coe_injective, Finset.prod_congr, Finset.prod_map, Function, Function.comp_def, Set.image_preimage_eq_iff, classical, coe_injective, coe_toFinset, comp_apply, comp_def, hf_fin, hf_fin.coe_toFinset.ge, hf_fin.preimage, hfg_fin, hfg_fin.coe_toFinset.ge, hg.injOn, image_preimage_eq_iff
-/
theorem Function.Injective.tprod_eq {g : γ -> β} (hg : Injective g) {f : β -> α}
    (hf : mulSupport f subseteq Set.range g) : ∏' c, f (g c) = ∏' b, f b := by
  classical
  have : mulSupport f = g '' mulSupport (f ∘ g) := by
    rw [mulSupport_comp_eq_preimage]; rw [Set.image_preimage_eq_iff.2 hf]
  rw [← Function.comp_def]
  by_cases hf_fin : (mulSupport f).Finite
  · have hfg_fin : (mulSupport (f ∘ g)).Finite := hf_fin.preimage hg.injOn
    lift g to γ ↪ β using hg
    simp_rw [tprod_eq_prod' hf_fin.coe_toFinset.ge, tprod_eq_prod' hfg_fin.coe_toFinset.ge,
      comp_apply, ← Finset.prod_map]
    refine Finset.prod_congr (Finset.coe_injective ?_) fun _ _ => rfl
    simp [this]
  · have hf_fin' : ¬ Set.Finite (mulSupport (f ∘ g)) := by
      rwa [this, Set.finite_image_iff hg.injOn] at hf_fin
    simp_rw [tprod_def, SummationFilter.support_eq_univ, Set.inter_univ,
      show (unconditional β).HasSupport by infer_instance,
      show (unconditional γ).HasSupport by infer_instance, true_and,
      if_neg hf_fin, if_neg hf_fin', Multipliable]
    simp [hg.hasProd_iff (mulSupport_subset_iff'.1 hf)]

@[to_additive]
/--
theorem `Equiv.tprod_eq` / 定理 `Equiv.tprod_eq`

English:
theorem Equiv.tprod_eq
  given: (e : γ ≃ β) (f : β -> α)
  statement: ∏' c, f (e c) = ∏' b, f b
  proof: e.injective.tprod_eq by simp

@[to_additive (attr := simp)]

中文:
定理 等价.tprod_eq
  条件: (e : γ ≃ β) (f : β -> α)
  结论: ∏' c, f (e c) = ∏' b, f b
  证明: e.injective.tprod_eq by simp

@[to_additive (attr := simp)]

Depends on / 依赖: e.injective.tprod_eq, injective, tprod_eq
-/
theorem Equiv.tprod_eq (e : γ ≃ β) (f : β -> α) : ∏' c, f (e c) = ∏' b, f b :=
e.injective.tprod_eq by simp

@[to_additive (attr := simp)]
/--
theorem `tprod_comp_neg` / 定理 `tprod_comp_neg`

English:
theorem tprod_comp_neg
  given: {β : Type*} [InvolutiveNeg β] (f : β -> α)
  proof: (Equiv.neg β).tprod_eq f

@[to_additive]

中文:
定理 tprod_comp_neg
  条件: {β : 类型} [InvolutiveNeg β] (f : β -> α)
  证明: (Equiv.neg β).tprod_eq f

@[to_additive]

Depends on / 依赖: Equiv.neg, tprod_eq
-/
theorem tprod_comp_neg {β : Type*} [InvolutiveNeg β] (f : β -> α) :
    ∏' d, f (-d) = ∏' d, f d :=
  (Equiv.neg β).tprod_eq f

@[to_additive]
/--
theorem `tprod_mem` / 定理 `tprod_mem`

English:
theorem tprod_mem
  statement: {ι S : Type*} {s : S} [SetLike S α] [SubmonoidClass S α]
  proof: by
  by_cases hf : Multipliable f
· exact h_closed.mem_of_tendsto hf.hasProd .of_forall fun _ => prod_mem fun i _ => h i
  · simp [tprod_eq_one_of_not_multipliable hf, one_mem]

中文:
定理 tprod_mem
  结论: {ι S : 类型} {s : S} [集合状 S α] [子幺半群类 S α]
  证明: by
  by_cases hf : Multipliable f
· exact h_closed.mem_of_tendsto hf.hasProd .of_forall fun _ => prod_mem fun i _ => h i
  · simp [tprod_eq_one_of_not_multipliable hf, one_mem]

Depends on / 依赖: Multipliable, h_closed, h_closed.mem_of_tendsto, hasProd, hf.hasProd, mem_of_tendsto, of_forall, one_mem, prod_mem, tprod_eq_one_of_not_multipliable
-/
theorem tprod_mem {ι S : Type*} {s : S} [SetLike S α] [SubmonoidClass S α]
    (h_closed : IsClosed (s : Set α)) {f : ι -> α} (h : forall i, f i in s) :
    ∏' i, f i in s := by
  by_cases hf : Multipliable f
· exact h_closed.mem_of_tendsto hf.hasProd .of_forall fun _ => prod_mem fun i _ => h i
  · simp [tprod_eq_one_of_not_multipliable hf, one_mem]

/-! ### `tprod` on subsets - part 1 -/

@[to_additive]
/--
theorem `tprod_subtype_eq_of_mulSupport_subset` / 定理 `tprod_subtype_eq_of_mulSupport_subset`

English:
theorem tprod_subtype_eq_of_mulSupport_subset
  given: {f : β -> α} {s : Set β} (hs : mulSupport f subseteq s)
  proof: Subtype.val_injective.tprod_eq by simpa

@[to_additive]

中文:
定理 tprod_subtype_eq_of_mulSupport_subset
  条件: {f : β -> α} {s : 集合 β} (hs : mulSupport f subseteq s)
  证明: Subtype.val_injective.tprod_eq by simpa

@[to_additive]

Depends on / 依赖: Subtype, Subtype.val_injective.tprod_eq, tprod_eq, val_injective
-/
theorem tprod_subtype_eq_of_mulSupport_subset {f : β -> α} {s : Set β} (hs : mulSupport f subseteq s) :
    ∏' x : s, f x = ∏' x, f x :=
Subtype.val_injective.tprod_eq by simpa

@[to_additive]
/--
theorem `tprod_subtype_mulSupport` / 定理 `tprod_subtype_mulSupport`

English:
theorem tprod_subtype_mulSupport
  given: (f : β -> α)
  statement: ∏' x : mulSupport f, f x = ∏' x, f x
  proof: tprod_subtype_eq_of_mulSupport_subset Set.Subset.rfl

@[to_additive]

中文:
定理 tprod_subtype_mulSupport
  条件: (f : β -> α)
  结论: ∏' x : mulSupport f, f x = ∏' x, f x
  证明: tprod_subtype_eq_of_mulSupport_subset Set.Subset.rfl

@[to_additive]

Depends on / 依赖: Set.Subset.rfl, Subset, tprod_subtype_eq_of_mulSupport_subset
-/
theorem tprod_subtype_mulSupport (f : β -> α) : ∏' x : mulSupport f, f x = ∏' x, f x :=
  tprod_subtype_eq_of_mulSupport_subset Set.Subset.rfl

@[to_additive]
/--
theorem `tprod_subtype` / 定理 `tprod_subtype`

English:
theorem tprod_subtype
  given: (s : Set β) (f : β -> α)
  statement: ∏' x : s, f x = ∏' x, s.mulIndicator f x
  proof: by
  rw [← tprod_subtype_eq_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]; rw [tprod_congr]
  simp

@[to_additive (attr := simp)]

中文:
定理 tprod_subtype
  条件: (s : 集合 β) (f : β -> α)
  结论: ∏' x : s, f x = ∏' x, s.mulIndicator f x
  证明: by
  rw [← tprod_subtype_eq_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]; rw [tprod_congr]
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: Set.mulSupport_mulIndicator_subset, mulSupport_mulIndicator_subset, tprod_congr, tprod_subtype_eq_of_mulSupport_subset
-/
theorem tprod_subtype (s : Set β) (f : β -> α) : ∏' x : s, f x = ∏' x, s.mulIndicator f x := by
  rw [← tprod_subtype_eq_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]; rw [tprod_congr]
  simp

@[to_additive (attr := simp)]
/--
theorem `tprod_univ` / 定理 `tprod_univ`

English:
theorem tprod_univ
  given: (f : β -> α)
  statement: ∏' x : (Set.univ : Set β), f x = ∏' x, f x
  proof: tprod_subtype_eq_of_mulSupport_subset Set.subset_univ _

@[to_additive]

中文:
定理 tprod_univ
  条件: (f : β -> α)
  结论: ∏' x : (集合.univ : 集合 β), f x = ∏' x, f x
  证明: tprod_subtype_eq_of_mulSupport_subset Set.subset_univ _

@[to_additive]

Depends on / 依赖: Set.subset_univ, subset_univ, tprod_subtype_eq_of_mulSupport_subset
-/
theorem tprod_univ (f : β -> α) : ∏' x : (Set.univ : Set β), f x = ∏' x, f x :=
tprod_subtype_eq_of_mulSupport_subset Set.subset_univ _

@[to_additive]
/--
theorem `tprod_image` / 定理 `tprod_image`

English:
theorem tprod_image
  given: {g : γ -> β} (f : β -> α) {s : Set γ} (hg : Set.InjOn g s)
  proof: ((Equiv.Set.imageOfInjOn _ _ hg).tprod_eq fun x => f x).symm

@[to_additive]

中文:
定理 tprod_image
  条件: {g : γ -> β} (f : β -> α) {s : 集合 γ} (hg : 集合.单射限制 g s)
  证明: ((Equiv.Set.imageOfInjOn _ _ hg).tprod_eq fun x => f x).symm

@[to_additive]

Depends on / 依赖: Equiv.Set.imageOfInjOn, imageOfInjOn, tprod_eq
-/
theorem tprod_image {g : γ -> β} (f : β -> α) {s : Set γ} (hg : Set.InjOn g s) :
    ∏' x : g '' s, f x = ∏' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tprod_eq fun x => f x).symm

@[to_additive]
/--
theorem `tprod_range` / 定理 `tprod_range`

English:
theorem tprod_range
  given: {g : γ -> β} (f : β -> α) (hg : Injective g)
  proof: by
  rw [← Set.image_univ]; rw [tprod_image f hg.injOn]
  simp_rw [← comp_apply (g := g), tprod_univ (f ∘ g)]

中文:
定理 tprod_range
  条件: {g : γ -> β} (f : β -> α) (hg : 单射 g)
  证明: by
  rw [← Set.image_univ]; rw [tprod_image f hg.injOn]
  simp_rw [← comp_apply (g := g), tprod_univ (f ∘ g)]

Depends on / 依赖: Set.image_univ, comp_apply, hg.injOn, image_univ, simp_rw, tprod_image, tprod_univ
-/
theorem tprod_range {g : γ -> β} (f : β -> α) (hg : Injective g) :
    ∏' x : Set.range g, f x = ∏' x, f (g x) := by
  rw [← Set.image_univ]; rw [tprod_image f hg.injOn]
  simp_rw [← comp_apply (g := g), tprod_univ (f ∘ g)]

/-- If `f b = 1` for all `b ∈ t`, then the product of `f a` with `a ∈ s` is the same as the
product of `f a` with `a ∈ s ∖ t`. -/
@[to_additive /-- If `f b = 0` for all `b ∈ t`, then the sum of `f a` with `a ∈ s` is the same as
the sum of `f a` with `a ∈ s ∖ t`. -/]
/--
lemma `tprod_setElem_eq_tprod_setElem_sdiff` / 引理 `tprod_setElem_eq_tprod_setElem_sdiff`

English:
lemma tprod_setElem_eq_tprod_setElem_sdiff
  statement: {f : β -> α} (s t : Set β)
  proof: .symm (Set.inclusion_injective (t := s) Set.sdiff_subset).tprod_eq (f := f ∘ (↑))
mulSupport_subset_iff'.2 fun b hb => hf₀ b by simpa using hb

@[deprecated (since := "2026-06-03")]
alias tprod_setElem_eq_tprod_setElem_diff := tprod_setElem_eq_tprod_setElem_sdiff

中文:
引理 tprod_setElem_eq_tprod_setElem_sdiff
  结论: {f : β -> α} (s t : 集合 β)
  证明: .symm (Set.inclusion_injective (t := s) Set.sdiff_subset).tprod_eq (f := f ∘ (↑))
mulSupport_subset_iff'.2 fun b hb => hf₀ b by simpa using hb

@[deprecated (since := "2026-06-03")]
alias tprod_setElem_eq_tprod_setElem_diff := tprod_setElem_eq_tprod_setElem_sdiff

Depends on / 依赖: Set.inclusion_injective, Set.sdiff_subset, inclusion_injective, mulSupport_subset_iff, sdiff_subset, tprod_eq
-/
lemma tprod_setElem_eq_tprod_setElem_sdiff {f : β -> α} (s t : Set β)
    (hf₀ : forall b in t, f b = 1) :
    ∏' a : s, f a = ∏' a : (s \ t : Set β), f a :=
.symm (Set.inclusion_injective (t := s) Set.sdiff_subset).tprod_eq (f := f ∘ (↑))
mulSupport_subset_iff'.2 fun b hb => hf₀ b by simpa using hb

@[deprecated (since := "2026-06-03")]
alias tprod_setElem_eq_tprod_setElem_diff := tprod_setElem_eq_tprod_setElem_sdiff

/-- If `f b = 1`, then the product of `f a` with `a ∈ s` is the same as the product of `f a` for
`a ∈ s ∖ {b}`. -/
@[to_additive /-- If `f b = 0`, then the sum of `f a` with `a ∈ s` is the same as the sum of `f a`
for `a ∈ s ∖ {b}`. -/]
/--
lemma `tprod_eq_tprod_sdiff_singleton` / 引理 `tprod_eq_tprod_sdiff_singleton`

English:
lemma tprod_eq_tprod_sdiff_singleton
  given: {f : β -> α} (s : Set β) {b : β} (hf₀ : f b = 1)
  proof: tprod_setElem_eq_tprod_setElem_sdiff s {b} fun _ ha => ha ▸ hf₀

@[deprecated (since := "2026-06-03")]
alias tprod_eq_tprod_diff_singleton := tprod_eq_tprod_sdiff_singleton

@[to_additive]

中文:
引理 tprod_eq_tprod_sdiff_singleton
  条件: {f : β -> α} (s : 集合 β) {b : β} (hf₀ : f b = 1)
  证明: tprod_setElem_eq_tprod_setElem_sdiff s {b} fun _ ha => ha ▸ hf₀

@[deprecated (since := "2026-06-03")]
alias tprod_eq_tprod_diff_singleton := tprod_eq_tprod_sdiff_singleton

@[to_additive]

Depends on / 依赖: tprod_setElem_eq_tprod_setElem_sdiff
-/
lemma tprod_eq_tprod_sdiff_singleton {f : β -> α} (s : Set β) {b : β} (hf₀ : f b = 1) :
    ∏' a : s, f a = ∏' a : (s \ {b} : Set β), f a :=
  tprod_setElem_eq_tprod_setElem_sdiff s {b} fun _ ha => ha ▸ hf₀

@[deprecated (since := "2026-06-03")]
alias tprod_eq_tprod_diff_singleton := tprod_eq_tprod_sdiff_singleton

@[to_additive]
/--
theorem `tprod_eq_tprod_of_ne_one_bij` / 定理 `tprod_eq_tprod_of_ne_one_bij`

English:
theorem tprod_eq_tprod_of_ne_one_bij
  statement: {g : γ -> α} (i : mulSupport g -> β) (hi : Injective i)
  proof: by
  rw [← tprod_subtype_mulSupport g]; rw [← hi.tprod_eq hf]
  simp only [hfg]

@[to_additive]

中文:
定理 tprod_eq_tprod_of_ne_one_bij
  结论: {g : γ -> α} (i : mulSupport g -> β) (hi : 单射 i)
  证明: by
  rw [← tprod_subtype_mulSupport g]; rw [← hi.tprod_eq hf]
  simp only [hfg]

@[to_additive]

Depends on / 依赖: hi.tprod_eq, tprod_eq, tprod_subtype_mulSupport
-/
theorem tprod_eq_tprod_of_ne_one_bij {g : γ -> α} (i : mulSupport g -> β) (hi : Injective i)
    (hf : mulSupport f subseteq Set.range i) (hfg : forall x, f (i x) = g x) : ∏' x, f x = ∏' y, g y := by
  rw [← tprod_subtype_mulSupport g]; rw [← hi.tprod_eq hf]
  simp only [hfg]

@[to_additive]
/--
theorem `Equiv.tprod_eq_tprod_of_mulSupport` / 定理 `Equiv.tprod_eq_tprod_of_mulSupport`

English:
theorem Equiv.tprod_eq_tprod_of_mulSupport
  statement: {f : β -> α} {g : γ -> α}
  proof: .symm tprod_eq_tprod_of_ne_one_bij _ (Subtype.val_injective.comp e.injective) (by simp) he

@[to_additive]

中文:
定理 等价.tprod_eq_tprod_of_mulSupport
  结论: {f : β -> α} {g : γ -> α}
  证明: .symm tprod_eq_tprod_of_ne_one_bij _ (Subtype.val_injective.comp e.injective) (by simp) he

@[to_additive]

Depends on / 依赖: Subtype, Subtype.val_injective.comp, e.injective, injective, tprod_eq_tprod_of_ne_one_bij, val_injective
-/
theorem Equiv.tprod_eq_tprod_of_mulSupport {f : β -> α} {g : γ -> α}
    (e : mulSupport f ≃ mulSupport g) (he : forall x, g (e x) = f x) :
    ∏' x, f x = ∏' y, g y :=
.symm tprod_eq_tprod_of_ne_one_bij _ (Subtype.val_injective.comp e.injective) (by simp) he

@[to_additive]
/--
theorem `tprod_dite_right` / 定理 `tprod_dite_right`

English:
theorem tprod_dite_right
  given: (P : Prop) [Decidable P] (x : β -> ¬P -> α)
  proof: by
  by_cases hP : P <;> simp [hP]

@[to_additive]

中文:
定理 tprod_dite_right
  条件: (P : 命题) [可判定 P] (x : β -> ¬P -> α)
  证明: by
  by_cases hP : P <;> simp [hP]

@[to_additive]
-/
theorem tprod_dite_right (P : Prop) [Decidable P] (x : β -> ¬P -> α) :
    ∏'[L] b, (if h : P then 1 else x b h) = if h : P then 1 else ∏'[L] b, x b h := by
  by_cases hP : P <;> simp [hP]

@[to_additive]
/--
theorem `tprod_dite_left` / 定理 `tprod_dite_left`

English:
theorem tprod_dite_left
  given: (P : Prop) [Decidable P] (x : β -> P -> α)
  proof: by
  by_cases hP : P <;> simp [hP]

@[to_additive (attr := simp)]

中文:
定理 tprod_dite_left
  条件: (P : 命题) [可判定 P] (x : β -> P -> α)
  证明: by
  by_cases hP : P <;> simp [hP]

@[to_additive (attr := simp)]
-/
theorem tprod_dite_left (P : Prop) [Decidable P] (x : β -> P -> α) :
    ∏'[L] b, (if h : P then x b h else 1) = if h : P then ∏'[L] b, x b h else 1 := by
  by_cases hP : P <;> simp [hP]

@[to_additive (attr := simp)]
/--
lemma `tprod_extend_one` / 引理 `tprod_extend_one`

English:
lemma tprod_extend_one
  given: {γ : Type*} {g : γ -> β} (hg : Injective g) (f : γ -> α)
  proof: by
have : mulSupport (extend g f 1) subseteq Set.range g := mulSupport_subset_iff'.2 extend_apply' _ _
  simp_rw [← hg.tprod_eq this, hg.extend_apply]

@[to_additive]

中文:
引理 tprod_extend_one
  条件: {γ : 类型} {g : γ -> β} (hg : 单射 g) (f : γ -> α)
  证明: by
have : mulSupport (extend g f 1) subseteq Set.range g := mulSupport_subset_iff'.2 extend_apply' _ _
  simp_rw [← hg.tprod_eq this, hg.extend_apply]

@[to_additive]

Depends on / 依赖: Set.range, extend, extend_apply, hg.extend_apply, hg.tprod_eq, mulSupport, mulSupport_subset_iff, simp_rw, subseteq, tprod_eq
-/
lemma tprod_extend_one {γ : Type*} {g : γ -> β} (hg : Injective g) (f : γ -> α) :
    ∏' y, extend g f 1 y = ∏' x, f x := by
have : mulSupport (extend g f 1) subseteq Set.range g := mulSupport_subset_iff'.2 extend_apply' _ _
  simp_rw [← hg.tprod_eq this, hg.extend_apply]

@[to_additive]
/--
lemma `tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem` / 引理 `tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem`

English:
lemma tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem
  statement: (s : γ -> Set β) (f : β -> α)
  proof: by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {j})]
  · aesop
  · exact Set.mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f hs i j hj

@[to_additive]

中文:
引理 tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem
  结论: (s : γ -> 集合 β) (f : β -> α)
  证明: by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {j})]
  · aesop
  · exact Set.mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f hs i j hj

@[to_additive]

Depends on / 依赖: Set.mem_iUnion.mp, Set.mulSupport_subset_subsingleton_of_disjoint_on_mulSupport, mem_iUnion, mulSupport_subset_subsingleton_of_disjoint_on_mulSupport, tprod_subtype_eq_of_mulSupport_subset
-/
lemma tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem (s : γ -> Set β) (f : β -> α)
    (i : β) (hi : i in ⋃ d, s d) (hs : Pairwise (Disjoint on (fun j => s j inter f.mulSupport))) :
    ∏' d, (s d).mulIndicator f i = f i := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
  rw [← tprod_subtype_eq_of_mulSupport_subset (s := {j})]
  · aesop
  · exact Set.mulSupport_subset_subsingleton_of_disjoint_on_mulSupport f hs i j hj

@[to_additive]
/--
lemma `tprod_mulIndicator_of_mem_union_disjoint` / 引理 `tprod_mulIndicator_of_mem_union_disjoint`

English:
lemma tprod_mulIndicator_of_mem_union_disjoint
  statement: (s : γ -> Set β) (f : β -> α)
  proof: tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem s f i hi (pairwise_disjoint_mono hs
 fun _ _ hi => hi.1)

@[to_additive]

中文:
引理 tprod_mulIndicator_of_mem_union_disjoint
  结论: (s : γ -> 集合 β) (f : β -> α)
  证明: tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem s f i hi (pairwise_disjoint_mono hs
 fun _ _ hi => hi.1)

@[to_additive]

Depends on / 依赖: pairwise_disjoint_mono, tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem
-/
lemma tprod_mulIndicator_of_mem_union_disjoint (s : γ -> Set β) (f : β -> α)
    (hs : Pairwise (Disjoint on s)) (i : β) (hi : i in ⋃ d, s d) :
    ∏' d, (s d).mulIndicator f i = f i :=
  tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem s f i hi (pairwise_disjoint_mono hs
 fun _ _ hi => hi.1)

@[to_additive]
/--
lemma `tprod_mulIndicator_of_notMem` / 引理 `tprod_mulIndicator_of_notMem`

English:
lemma tprod_mulIndicator_of_notMem
  given: (s : γ -> Set β) (f : β -> α) (i : β) (hi : forall d, i ∉ s d)
  proof: by
  aesop

@[to_additive]

中文:
引理 tprod_mulIndicator_of_notMem
  条件: (s : γ -> 集合 β) (f : β -> α) (i : β) (hi : 对任意 d, i ∉ s d)
  证明: by
  aesop

@[to_additive]
-/
lemma tprod_mulIndicator_of_notMem (s : γ -> Set β) (f : β -> α) (i : β) (hi : forall d, i ∉ s d) :
    ∏' d, (s d).mulIndicator f i = 1 := by
  aesop

@[to_additive]
/--
lemma `mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport` / 引理 `mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport`

English:
lemma mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport
  statement: (s : γ -> Set β) (f : β -> α)
  proof: by
  by_cases h₀ : i in ⋃ d, s d
  · simp only [h₀, hs, Set.mulIndicator_of_mem, tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem]
  · aesop

@[to_additive]

中文:
引理 mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport
  结论: (s : γ -> 集合 β) (f : β -> α)
  证明: by
  by_cases h₀ : i in ⋃ d, s d
  · simp only [h₀, hs, Set.mulIndicator_of_mem, tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem]
  · aesop

@[to_additive]

Depends on / 依赖: Set.mulIndicator_of_mem, mulIndicator_of_mem, tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem
-/
lemma mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport (s : γ -> Set β) (f : β -> α)
    (hs : Pairwise (Disjoint on (fun j => s j inter f.mulSupport))) (i : β) :
    (⋃ d, s d).mulIndicator f i = ∏' d, (s d).mulIndicator f i := by
  by_cases h₀ : i in ⋃ d, s d
  · simp only [h₀, hs, Set.mulIndicator_of_mem, tprod_mulIndicator_of_disjoint_on_mulSupport_of_mem]
  · aesop

@[to_additive]
/--
lemma `mulIndicator_iUnion_of_pairwise_disjoint` / 引理 `mulIndicator_iUnion_of_pairwise_disjoint`

English:
lemma mulIndicator_iUnion_of_pairwise_disjoint
  statement: (s : γ -> Set β) (hs : Pairwise (Disjoint on s))
  proof: by
  ext i
  exact mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport s f (pairwise_disjoint_mono hs
 fun _ _ hi => hi.1) i

中文:
引理 mulIndicator_iUnion_of_pairwise_disjoint
  结论: (s : γ -> 集合 β) (hs : 两两 (Disjoint on s))
  证明: by
  ext i
  exact mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport s f (pairwise_disjoint_mono hs
 fun _ _ hi => hi.1) i

Depends on / 依赖: mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport, pairwise_disjoint_mono
-/
lemma mulIndicator_iUnion_of_pairwise_disjoint (s : γ -> Set β) (hs : Pairwise (Disjoint on s))
    (f : β -> α) : (⋃ d, s d).mulIndicator f = fun i => ∏' d, (s d).mulIndicator f i := by
  ext i
  exact mulIndicator_iUnion_of_pairwise_disjoint_on_mulSupport s f (pairwise_disjoint_mono hs
 fun _ _ hi => hi.1) i

variable [T2Space α]

@[to_additive]
/--
theorem `Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd` / 定理 `Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd`

English:
theorem Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd
  statement: {α' : Type*} [CommMonoid α']
  proof: by_cases (fun x => (h.mpr x.hasProd).tprod_eq) fun hg : ¬Multipliable g => by
    have hf : ¬Multipliable f := mt (hes.multipliable_iff_of_hasProd_iff @h).1 hg
    simp [tprod_def, hf, hg, h1]

@[to_additive]

中文:
定理 函数.满射.tprod_eq_tprod_of_hasProd_iff_hasProd
  结论: {α' : 类型} [交换幺半群 α']
  证明: by_cases (fun x => (h.mpr x.hasProd).tprod_eq) fun hg : ¬Multipliable g => by
    have hf : ¬Multipliable f := mt (hes.multipliable_iff_of_hasProd_iff @h).1 hg
    simp [tprod_def, hf, hg, h1]

@[to_additive]

Depends on / 依赖: Multipliable, h.mpr, hasProd, hes.multipliable_iff_of_hasProd_iff, multipliable_iff_of_hasProd_iff, tprod_def, tprod_eq, x.hasProd
-/
theorem Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd {α' : Type*} [CommMonoid α']
    [TopologicalSpace α'] {e : α' -> α} (hes : Function.Surjective e) (h1 : e 1 = 1) {f : β -> α}
    {g : γ -> α'} (h : forall {a}, HasProd f (e a) ↔ HasProd g a) : ∏' b, f b = e (∏' c, g c) :=
  by_cases (fun x => (h.mpr x.hasProd).tprod_eq) fun hg : ¬Multipliable g => by
    have hf : ¬Multipliable f := mt (hes.multipliable_iff_of_hasProd_iff @h).1 hg
    simp [tprod_def, hf, hg, h1]

@[to_additive]
/--
theorem `tprod_eq_tprod_of_hasProd_iff_hasProd` / 定理 `tprod_eq_tprod_of_hasProd_iff_hasProd`

English:
theorem tprod_eq_tprod_of_hasProd_iff_hasProd
  statement: {f : β -> α} {g : γ -> α}
  proof: surjective_id.tprod_eq_tprod_of_hasProd_iff_hasProd rfl @h

中文:
定理 tprod_eq_tprod_of_hasProd_iff_hasProd
  结论: {f : β -> α} {g : γ -> α}
  证明: surjective_id.tprod_eq_tprod_of_hasProd_iff_hasProd rfl @h

Depends on / 依赖: surjective_id, surjective_id.tprod_eq_tprod_of_hasProd_iff_hasProd, tprod_eq_tprod_of_hasProd_iff_hasProd
-/
theorem tprod_eq_tprod_of_hasProd_iff_hasProd {f : β -> α} {g : γ -> α}
    (h : forall {a}, HasProd f a ↔ HasProd g a) : ∏' b, f b = ∏' c, g c :=
  surjective_id.tprod_eq_tprod_of_hasProd_iff_hasProd rfl @h

section ContinuousMul

variable [ContinuousMul α]

@[to_additive]
/--
theorem `Multipliable.tprod_mul` / 定理 `Multipliable.tprod_mul`

English:
theorem Multipliable.tprod_mul
  statement: [L.NeBot]
  proof: (hf.hasProd.mul hg.hasProd).tprod_eq

@[to_additive]

中文:
定理 Multipliable.tprod_mul
  结论: [L.NeBot]
  证明: (hf.hasProd.mul hg.hasProd).tprod_eq

@[to_additive]
-/
protected theorem Multipliable.tprod_mul [L.NeBot]
    (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] b, (f b * g b) = (∏'[L] b, f b) * ∏'[L] b, g b :=
  (hf.hasProd.mul hg.hasProd).tprod_eq

@[to_additive]
/--
lemma `Multipliable.tprod_pow` / 引理 `Multipliable.tprod_pow`

English:
lemma Multipliable.tprod_pow
  given: [L.NeBot] (hf : Multipliable f L) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, (hf.pow n).tprod_mul hf, hn]

@[to_additive]

中文:
引理 Multipliable.tprod_pow
  条件: [L.NeBot] (hf : Multipliable f L) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, (hf.pow n).tprod_mul hf, hn]

@[to_additive]

Depends on / 依赖: hf.pow, pow_succ, tprod_mul
-/
lemma Multipliable.tprod_pow [L.NeBot] (hf : Multipliable f L) (n : Nat) :
    ∏'[L] b, (f b) ^ n = (∏'[L] b, f b) ^ n := by
  induction n with
  | zero => simp
  | succ n hn => simp [pow_succ, (hf.pow n).tprod_mul hf, hn]

@[to_additive]
/--
theorem `Multipliable.tprod_finsetProd` / 定理 `Multipliable.tprod_finsetProd`

English:
theorem Multipliable.tprod_finsetProd
  statement: [L.NeBot] {f : γ -> β -> α} {s : Finset γ}
  proof: (hasProd_prod fun i hi => (hf i hi).hasProd).tprod_eq

中文:
定理 Multipliable.tprod_finsetProd
  结论: [L.NeBot] {f : γ -> β -> α} {s : 有限集 γ}
  证明: (hasProd_prod fun i hi => (hf i hi).hasProd).tprod_eq
-/
protected theorem Multipliable.tprod_finsetProd [L.NeBot] {f : γ -> β -> α} {s : Finset γ}
    (hf : forall i in s, Multipliable (f i) L) : ∏'[L] b, ∏ i in s, f i b = ∏ i in s, ∏'[L] b, f i b :=
  (hasProd_prod fun i hi => (hf i hi).hasProd).tprod_eq

/-- Version of `tprod_eq_mul_tprod_ite` for `CommMonoid` rather than `CommGroup`.
Requires a different convergence assumption involving `Function.update`. -/
@[to_additive /-- Version of `tsum_eq_add_tsum_ite` for `AddCommMonoid` rather than `AddCommGroup`.
Requires a different convergence assumption involving `Function.update`. -/]
/--
theorem `Multipliable.tprod_eq_mul_tprod_ite'` / 定理 `Multipliable.tprod_eq_mul_tprod_ite'`

English:
theorem Multipliable.tprod_eq_mul_tprod_ite'
  statement: [DecidableEq β] [L.LeAtTop] [L.NeBot]
  proof: calc
    ∏'[L] x, f x = ∏'[L] x, (ite (x = b) (f x) 1 * update f b 1 x) :=
      tprod_congr fun n => by split_ifs with h <;> simp [h]
    _ = (∏'[L] x, ite (x = b) (f x) 1) * ∏'[L] x, update f b 1 x :=
      Multipliable.tprod_mul ⟨ite (b = b) (f b) 1, hasProd_single b (fun _ hb => if_neg hb) L⟩ hf

中文:
定理 Multipliable.tprod_eq_mul_tprod_ite'
  结论: [DecidableEq β] [L.LeAtTop] [L.NeBot]
  证明: calc
    ∏'[L] x, f x = ∏'[L] x, (ite (x = b) (f x) 1 * update f b 1 x) :=
      tprod_congr fun n => by split_ifs with h <;> simp [h]
    _ = (∏'[L] x, ite (x = b) (f x) 1) * ∏'[L] x, update f b 1 x :=
      Multipliable.tprod_mul ⟨ite (b = b) (f b) 1, hasProd_single b (fun _ hb => if_neg hb) L⟩ hf
-/
protected theorem Multipliable.tprod_eq_mul_tprod_ite' [DecidableEq β] [L.LeAtTop] [L.NeBot]
    {f : β -> α} (b : β) (hf : Multipliable (update f b 1) L) :
    ∏'[L] x, f x = f b * ∏'[L] x, ite (x = b) 1 (f x) :=
  calc
    ∏'[L] x, f x = ∏'[L] x, (ite (x = b) (f x) 1 * update f b 1 x) :=
      tprod_congr fun n => by split_ifs with h <;> simp [h]
    _ = (∏'[L] x, ite (x = b) (f x) 1) * ∏'[L] x, update f b 1 x :=
      Multipliable.tprod_mul ⟨ite (b = b) (f b) 1, hasProd_single b (fun _ hb => if_neg hb) L⟩ hf
    _ = ite (b = b) (f b) 1 * ∏'[L] x, update f b 1 x := by
      congr
      exact tprod_eq_mulSingle b fun b' hb' => if_neg hb'
    _ = f b * ∏'[L] x, ite (x = b) 1 (f x) := by
      simp only [update, if_true, eq_rec_constant, dite_eq_ite]

@[to_additive]
/--
theorem `Multipliable.tprod_mul_tprod_compl` / 定理 `Multipliable.tprod_mul_tprod_compl`

English:
theorem Multipliable.tprod_mul_tprod_compl
  statement: {s : Set β}
  proof: (hs.hasProd.mul_compl hsc.hasProd).tprod_eq.symm

@[to_additive]

中文:
定理 Multipliable.tprod_mul_tprod_compl
  结论: {s : 集合 β}
  证明: (hs.hasProd.mul_compl hsc.hasProd).tprod_eq.symm

@[to_additive]
-/
protected theorem Multipliable.tprod_mul_tprod_compl {s : Set β}
    (hs : Multipliable (f ∘ (↑) : s -> α)) (hsc : Multipliable (f ∘ (↑) : ↑sᶜ -> α)) :
    (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  (hs.hasProd.mul_compl hsc.hasProd).tprod_eq.symm

@[to_additive]
/--
theorem `Multipliable.tprod_union_disjoint` / 定理 `Multipliable.tprod_union_disjoint`

English:
theorem Multipliable.tprod_union_disjoint
  statement: {s t : Set β} (hd : Disjoint s t)
  proof: (hs.hasProd.mul_disjoint hd ht.hasProd).tprod_eq

@[to_additive]

中文:
定理 Multipliable.tprod_union_disjoint
  结论: {s t : 集合 β} (hd : Disjoint s t)
  证明: (hs.hasProd.mul_disjoint hd ht.hasProd).tprod_eq

@[to_additive]
-/
protected theorem Multipliable.tprod_union_disjoint {s t : Set β} (hd : Disjoint s t)
    (hs : Multipliable (f ∘ (↑) : s -> α)) (ht : Multipliable (f ∘ (↑) : t -> α)) :
    ∏' x : ↑(s union t), f x = (∏' x : s, f x) * ∏' x : t, f x :=
  (hs.hasProd.mul_disjoint hd ht.hasProd).tprod_eq

@[to_additive]
/--
theorem `Multipliable.tprod_finset_bUnion_disjoint` / 定理 `Multipliable.tprod_finset_bUnion_disjoint`

English:
theorem Multipliable.tprod_finset_bUnion_disjoint
  statement: {ι} {s : Finset ι} {t : ι -> Set β}
  proof: (hasProd_prod_disjoint _ hd fun i hi => (hf i hi).hasProd).tprod_eq

中文:
定理 Multipliable.tprod_finset_bUnion_disjoint
  结论: {ι} {s : 有限集 ι} {t : ι -> 集合 β}
  证明: (hasProd_prod_disjoint _ hd fun i hi => (hf i hi).hasProd).tprod_eq
-/
protected theorem Multipliable.tprod_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι -> Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : forall i in s, Multipliable (f ∘ (↑) : t i -> α)) :
    ∏' x : ⋃ i in s, t i, f x = ∏ i in s, ∏' x : t i, f x :=
  (hasProd_prod_disjoint _ hd fun i hi => (hf i hi).hasProd).tprod_eq

end ContinuousMul

end tprod

section CommMonoidWithZero
variable [CommMonoidWithZero α] [TopologicalSpace α] {f : β -> α} {L : SummationFilter β}

/--
lemma `hasProd_zero_of_exists_eq_zero` / 引理 `hasProd_zero_of_exists_eq_zero`

English:
lemma hasProd_zero_of_exists_eq_zero
  given: (hf : exists b, f b = 0) [L.LeAtTop]
  statement: HasProd f 0 L
  proof: by
  obtain ⟨b, hb⟩ := hf
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_ge_atTop {b}).filter_mono L.le_atTop] with s hs
  exact (Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) hb).symm

中文:
引理 hasProd_zero_of_存在_eq_zero
  条件: (hf : 存在 b, f b = 0) [L.LeAtTop]
  结论: 有积类型 f 0 L
  证明: by
  obtain ⟨b, hb⟩ := hf
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_ge_atTop {b}).filter_mono L.le_atTop] with s hs
  exact (Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) hb).symm

Depends on / 依赖: Finset, Finset.prod_eq_zero, Finset.singleton_subset_iff.mp, L.le_atTop, eventually_ge_atTop, filter_mono, filter_upwards, le_atTop, prod_eq_zero, singleton_subset_iff, tendsto_const_nhds, tendsto_const_nhds.congr
-/
lemma hasProd_zero_of_exists_eq_zero (hf : exists b, f b = 0) [L.LeAtTop] : HasProd f 0 L := by
  obtain ⟨b, hb⟩ := hf
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_ge_atTop {b}).filter_mono L.le_atTop] with s hs
  exact (Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) hb).symm

/--
lemma `hasProd_zero_zero` / 引理 `hasProd_zero_zero`

English:
lemma hasProd_zero_zero
  given: [Nonempty β] [L.LeAtTop]
  statement: HasProd (fun _ => 0 : β -> α) 0 L
  proof: by
  obtain ⟨b⟩ := ‹Nonempty β›
  exact hasProd_zero_of_exists_eq_zero ⟨b, by simp⟩

中文:
引理 hasProd_zero_zero
  条件: [非空 β] [L.LeAtTop]
  结论: 有积类型 (fun _ => 0 : β -> α) 0 L
  证明: by
  obtain ⟨b⟩ := ‹Nonempty β›
  exact hasProd_zero_of_exists_eq_zero ⟨b, by simp⟩

Depends on / 依赖: Nonempty, hasProd_zero_of_exists_eq_zero
-/
lemma hasProd_zero_zero [Nonempty β] [L.LeAtTop] : HasProd (fun _ => 0 : β -> α) 0 L := by
  obtain ⟨b⟩ := ‹Nonempty β›
  exact hasProd_zero_of_exists_eq_zero ⟨b, by simp⟩

/--
lemma `multipliable_of_exists_eq_zero` / 引理 `multipliable_of_exists_eq_zero`

English:
lemma multipliable_of_exists_eq_zero
  given: (hf : exists b, f b = 0) [L.LeAtTop]
  statement: Multipliable f L
  proof: ⟨0, hasProd_zero_of_exists_eq_zero hf⟩

中文:
引理 multipliable_of_存在_eq_zero
  条件: (hf : 存在 b, f b = 0) [L.LeAtTop]
  结论: Multipliable f L
  证明: ⟨0, hasProd_zero_of_exists_eq_zero hf⟩

Depends on / 依赖: hasProd_zero_of_exists_eq_zero
-/
lemma multipliable_of_exists_eq_zero (hf : exists b, f b = 0) [L.LeAtTop] : Multipliable f L :=
  ⟨0, hasProd_zero_of_exists_eq_zero hf⟩

/--
lemma `multipliable_zero` / 引理 `multipliable_zero`

English:
lemma multipliable_zero
  given: [L.LeAtTop]
  statement: Multipliable (fun _ => 0 : β -> α) L
  proof: by
  obtain hβ | hβ := isEmpty_or_nonempty β
  · simp
  · exact ⟨0, hasProd_zero_zero⟩

中文:
引理 multipliable_zero
  条件: [L.LeAtTop]
  结论: Multipliable (fun _ => 0 : β -> α) L
  证明: by
  obtain hβ | hβ := isEmpty_or_nonempty β
  · simp
  · exact ⟨0, hasProd_zero_zero⟩

Depends on / 依赖: hasProd_zero_zero, isEmpty_or_nonempty
-/
lemma multipliable_zero [L.LeAtTop] : Multipliable (fun _ => 0 : β -> α) L := by
  obtain hβ | hβ := isEmpty_or_nonempty β
  · simp
  · exact ⟨0, hasProd_zero_zero⟩

/--
lemma `tprod_of_exists_eq_zero` / 引理 `tprod_of_exists_eq_zero`

English:
lemma tprod_of_exists_eq_zero
  given: [T2Space α] [L.NeBot] [L.LeAtTop] (hf : exists b, f b = 0)
  proof: (hasProd_zero_of_exists_eq_zero hf).tprod_eq

中文:
引理 tprod_of_存在_eq_zero
  条件: [T2空间 α] [L.NeBot] [L.LeAtTop] (hf : 存在 b, f b = 0)
  证明: (hasProd_zero_of_exists_eq_zero hf).tprod_eq

Depends on / 依赖: hasProd_zero_of_exists_eq_zero, tprod_eq
-/
lemma tprod_of_exists_eq_zero [T2Space α] [L.NeBot] [L.LeAtTop] (hf : exists b, f b = 0) :
    ∏'[L] b, f b = 0 :=
  (hasProd_zero_of_exists_eq_zero hf).tprod_eq

/--
lemma `tprod_zero` / 引理 `tprod_zero`

English:
lemma tprod_zero
  given: [T2Space α] [Nonempty β] [L.NeBot] [L.LeAtTop]
  proof: hasProd_zero_zero.tprod_eq

中文:
引理 tprod_zero
  条件: [T2空间 α] [非空 β] [L.NeBot] [L.LeAtTop]
  证明: hasProd_zero_zero.tprod_eq
-/
@[simp] lemma tprod_zero [T2Space α] [Nonempty β] [L.NeBot] [L.LeAtTop] :
    ∏'[L] _, (0 : α) = 0 :=
  hasProd_zero_zero.tprod_eq

end CommMonoidWithZero
