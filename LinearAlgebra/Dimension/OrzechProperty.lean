/-
Copyright (c) 2018 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Noetherian.Orzech

/-! # Bases of modules and the Orzech property

It is shown in this file that any spanning set of a module over a ring satisfying the Orzech
property of cardinality not exceeding the rank of the module must be linearly independent,
and therefore is a basis.
-/

@[expose] public section

section Basis

open Module Submodule

variable {R M : Type*} [Semiring R] [OrzechProperty R] [AddCommMonoid M] [Module R M]

/--
theorem `linearIndependent_of_top_le_span_of_card_le_finrank` / 定理 `linearIndependent_of_top_le_span_of_card_le_finrank`

English:
theorem linearIndependent_of_top_le_span_of_card_le_finrank
  statement: {ι : Type*} [Fintype ι] {b : ι -> M}
  proof: by
  rw [← Finsupp.range_linearCombination]; rw [top_le_iff]; rw [LinearMap.range_eq_top] at spans
  have := Module.Finite.of_surjective _ spans
  have ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank card_le
  exact OrzechProperty.injective_of_surjective_of_injective
    _ _ (hf.comp _ (Fintype.eq

中文:
定理 linearIndependent_of_top_le_span_of_card_le_finrank
  结论: {ι : 类型} [有限类型 ι] {b : ι -> M}
  证明: by
  rw [← Finsupp.range_linearCombination]; rw [top_le_iff]; rw [LinearMap.range_eq_top] at spans
  have := Module.Finite.of_surjective _ spans
  have ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank card_le
  exact OrzechProperty.injective_of_surjective_of_injective
    _ _ (hf.comp _ (Fintype.eq

Depends on / 依赖: Finite, Finsupp, Finsupp.range_linearCombination, Fintype, Fintype.equivFin, LinearMap, LinearMap.range_eq_top, Module, Module.Finite.of_surjective, OrzechProperty, OrzechProperty.injective_of_surjective_of_injective, card_le, equivFin, exists_linearIndependent_of_le_finrank, hf.comp, injective, injective_of_surjective_of_injective, of_surjective, range_eq_top, range_linearCombination
-/
theorem linearIndependent_of_top_le_span_of_card_le_finrank {ι : Type*} [Fintype ι] {b : ι -> M}
    (spans : ⊤ <= span R (Set.range b)) (card_le : Fintype.card ι <= finrank R M) :
    LinearIndependent R b := by
  rw [← Finsupp.range_linearCombination]; rw [top_le_iff]; rw [LinearMap.range_eq_top] at spans
  have := Module.Finite.of_surjective _ spans
  have ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank card_le
  exact OrzechProperty.injective_of_surjective_of_injective
    _ _ (hf.comp _ (Fintype.equivFin _).injective) spans

/--
theorem `linearIndependent_of_top_le_span_of_card_eq_finrank` / 定理 `linearIndependent_of_top_le_span_of_card_eq_finrank`

English:
theorem linearIndependent_of_top_le_span_of_card_eq_finrank
  statement: {ι : Type*} [Fintype ι] {b : ι -> M}
  proof: linearIndependent_of_top_le_span_of_card_le_finrank spans card_eq.le

中文:
定理 linearIndependent_of_top_le_span_of_card_eq_finrank
  结论: {ι : 类型} [有限类型 ι] {b : ι -> M}
  证明: linearIndependent_of_top_le_span_of_card_le_finrank spans card_eq.le

Depends on / 依赖: card_eq, card_eq.le, linearIndependent_of_top_le_span_of_card_le_finrank
-/
theorem linearIndependent_of_top_le_span_of_card_eq_finrank {ι : Type*} [Fintype ι] {b : ι -> M}
    (spans : ⊤ <= span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    LinearIndependent R b :=
  linearIndependent_of_top_le_span_of_card_le_finrank spans card_eq.le

/--
theorem `linearIndependent_iff_card_eq_finrank_span` / 定理 `linearIndependent_iff_card_eq_finrank_span`

English:
theorem linearIndependent_iff_card_eq_finrank_span
  given: [Nontrivial R] {ι} [Fintype ι] {b : ι -> M}
  proof: (finrank_span_eq_card h).symm
  mpr hc := by
refine (LinearMap.linearIndependent_iff_of_injOn _ (subtype_injective _).injOn).mpr
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := fun i => ⟨b i, subset_span ⟨i, rfl⟩⟩)
        (fun ⟨_, _⟩ _ => (subtype_injective _).mem_set_image.mp ?_) h

中文:
定理 linearIndependent_iff_card_eq_finrank_span
  条件: [非平凡 R] {ι} [有限类型 ι] {b : ι -> M}
  证明: (finrank_span_eq_card h).symm
  mpr hc := by
refine (LinearMap.linearIndependent_iff_of_injOn _ (subtype_injective _).injOn).mpr
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := fun i => ⟨b i, subset_span ⟨i, rfl⟩⟩)
        (fun ⟨_, _⟩ _ => (subtype_injective _).mem_set_image.mp ?_) h

Depends on / 依赖: finrank_span_eq_card
-/
theorem linearIndependent_iff_card_eq_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι -> M} :
    LinearIndependent R b ↔ Fintype.card ι = (Set.range b).finrank R where
  mp h := (finrank_span_eq_card h).symm
  mpr hc := by
refine (LinearMap.linearIndependent_iff_of_injOn _ (subtype_injective _).injOn).mpr
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := fun i => ⟨b i, subset_span ⟨i, rfl⟩⟩)
        (fun ⟨_, _⟩ _ => (subtype_injective _).mem_set_image.mp ?_) hc
    rwa [← map_coe, ← span_image, ← Set.range_comp]

/--
theorem `linearIndependent_iff_card_le_finrank_span` / 定理 `linearIndependent_iff_card_le_finrank_span`

English:
theorem linearIndependent_iff_card_le_finrank_span
  given: [Nontrivial R] {ι} [Fintype ι] {b : ι -> M}
  proof: by
  rw [linearIndependent_iff_card_eq_finrank_span]; rw [(finrank_range_le_card _).ge_iff_eq']

中文:
定理 linearIndependent_iff_card_le_finrank_span
  条件: [非平凡 R] {ι} [有限类型 ι] {b : ι -> M}
  证明: by
  rw [linearIndependent_iff_card_eq_finrank_span]; rw [(finrank_range_le_card _).ge_iff_eq']

Depends on / 依赖: finrank_range_le_card, ge_iff_eq, linearIndependent_iff_card_eq_finrank_span
-/
theorem linearIndependent_iff_card_le_finrank_span [Nontrivial R] {ι} [Fintype ι] {b : ι -> M} :
    LinearIndependent R b ↔ Fintype.card ι <= (Set.range b).finrank R := by
  rw [linearIndependent_iff_card_eq_finrank_span]; rw [(finrank_range_le_card _).ge_iff_eq']

/--
Definition of `basisOfTopLeSpanOfCardEqFinrank` / `basisOfTopLeSpanOfCardEqFinrank` 的定义

English:
definition basisOfTopLeSpanOfCardEqFinrank
  signature: {ι : Type*} [Fintype ι] (b : ι -> M)
  body: Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp]

中文:
定义 basisOfTopLeSpanOfCardEqFinrank
  签名: {ι : 类型} [有限类型 ι] (b : ι -> M)
  定义体: Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp]

Depends on / 依赖: Basis.mk, card_eq, le_span, linearIndependent_of_top_le_span_of_card_eq_finrank
-/
noncomputable def basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι -> M)
    (le_span : ⊤ <= span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) : Basis ι R M :=
  Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank le_span card_eq) le_span

@[simp]
/--
theorem `coe_basisOfTopLeSpanOfCardEqFinrank` / 定理 `coe_basisOfTopLeSpanOfCardEqFinrank`

English:
theorem coe_basisOfTopLeSpanOfCardEqFinrank
  statement: {ι : Type*} [Fintype ι] (b : ι -> M)
  proof: Basis.coe_mk _ _

中文:
定理 coe_basisOfTopLeSpanOfCardEqFinrank
  结论: {ι : 类型} [有限类型 ι] (b : ι -> M)
  证明: Basis.coe_mk _ _

Depends on / 依赖: Basis.coe_mk, coe_mk
-/
theorem coe_basisOfTopLeSpanOfCardEqFinrank {ι : Type*} [Fintype ι] (b : ι -> M)
    (le_span : ⊤ <= span R (Set.range b)) (card_eq : Fintype.card ι = finrank R M) :
    ⇑(basisOfTopLeSpanOfCardEqFinrank b le_span card_eq) = b :=
  Basis.coe_mk _ _

/-- A finset of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
@[simps! repr_apply]
/--
Definition of `finsetBasisOfTopLeSpanOfCardEqFinrank` / `finsetBasisOfTopLeSpanOfCardEqFinrank` 的定义

English:
definition finsetBasisOfTopLeSpanOfCardEqFinrank
  signature: {s : Finset M}
  body: basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set M) -> M)
    ((@Subtype.range_coe_subtype _ fun x => x in s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)

中文:
定义 finsetBasisOfTopLeSpanOfCardEqFinrank
  签名: {s : 有限集 M}
  定义体: basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set M) -> M)
    ((@Subtype.range_coe_subtype _ fun x => x in s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)

Depends on / 依赖: Fintype, Fintype.card_coe, Subtype, Subtype.range_coe_subtype, _root_, _root_.trans, basisOfTopLeSpanOfCardEqFinrank, card_coe, card_eq, le_span, range_coe_subtype
-/
noncomputable def finsetBasisOfTopLeSpanOfCardEqFinrank {s : Finset M}
    (le_span : ⊤ <= span R (s : Set M)) (card_eq : s.card = finrank R M) : Basis {x // x in s} R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : ↥(s : Set M) -> M)
    ((@Subtype.range_coe_subtype _ fun x => x in s).symm ▸ le_span)
    (_root_.trans (Fintype.card_coe _) card_eq)

/-- A set of `finrank R M` vectors forms a basis if they span the whole space,
provided `R` satisfies the Orzech property. -/
@[simps! repr_apply]
/--
Definition of `setBasisOfTopLeSpanOfCardEqFinrank` / `setBasisOfTopLeSpanOfCardEqFinrank` 的定义

English:
definition setBasisOfTopLeSpanOfCardEqFinrank
  signature: {s : Set M} [Fintype s]
  body: basisOfTopLeSpanOfCardEqFinrank ((↑) : s -> M) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)

中文:
定义 setBasisOfTopLeSpanOfCardEqFinrank
  签名: {s : 集合 M} [有限类型 s]
  定义体: basisOfTopLeSpanOfCardEqFinrank ((↑) : s -> M) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, _root_, _root_.trans, basisOfTopLeSpanOfCardEqFinrank, card_eq, le_span, range_coe_subtype, s.toFinset_card.symm, toFinset_card
-/
noncomputable def setBasisOfTopLeSpanOfCardEqFinrank {s : Set M} [Fintype s]
    (le_span : ⊤ <= span R s) (card_eq : s.toFinset.card = finrank R M) : Basis s R M :=
  basisOfTopLeSpanOfCardEqFinrank ((↑) : s -> M) ((@Subtype.range_coe_subtype _ s).symm ▸ le_span)
    (_root_.trans s.toFinset_card.symm card_eq)

end Basis
