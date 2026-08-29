/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.BaseChange

/-!

# Locality of `Algebra.FiniteType`

In this file we show that finite-type is local on the source and the target.

## Main results

- `Algebra.FiniteType.of_span_eq_top_source`: finite-type is local on the (algebraic) source
- `Algebra.FiniteType.of_span_eq_top_target`: finite-type is local on the (algebraic) target

-/

public section

section Algebra

open scoped Pointwise TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

variable {S'} in
open scoped Classical in
/--
theorem `IsLocalization.exists_smul_mem_of_mem_adjoin` / 定理 `IsLocalization.exists_smul_mem_of_mem_adjoin`

English:
theorem IsLocalization.exists_smul_mem_of_mem_adjoin
  statement: [Algebra R S']
  proof: by
  let g : S ->ₐ[R] S' := IsScalarTower.toAlgHom R S S'
  let y := IsLocalization.commonDenomOfFinset M s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨n, hn⟩ :=
    Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s :

中文:
定理 IsLocalization.exists_smul_mem_of_mem_adjoin
  结论: [Algebra R S']
  证明: by
  let g : S ->ₐ[R] S' := IsScalarTower.toAlgHom R S S'
  let y := IsLocalization.commonDenomOfFinset M s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨n, hn⟩ :=
    Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s :

Depends on / 依赖: A.map, Algebra, Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin, Algebra.smul_def, IsLocal, IsLocalization, IsLocalization.commonDenomOfFinset, IsLocalization.finsetIntegerMultiple_image, IsScalarTower, IsScalarTower.toAlgHom, Set.image_mono, Set.mem_image_of_mem, commonDenomOfFinset, finsetIntegerMultiple_image, image_mono, le_of_eq, map_mul, mem_image_of_mem, pow_smul_mem_of_smul_subset_of_mem_adjoin, smul_def
-/
theorem IsLocalization.exists_smul_mem_of_mem_adjoin [Algebra R S']
    [IsScalarTower R S S'] (M : Submonoid S) [IsLocalization M S'] (x : S) (s : Finset S')
    (A : Subalgebra R S) (hA₁ : (IsLocalization.finsetIntegerMultiple M s : Set S) subseteq A)
    (hA₂ : M <= A.toSubmonoid) (hx : algebraMap S S' x in Algebra.adjoin R (s : Set S')) :
    exists m : M, m • x in A := by
  let g : S ->ₐ[R] S' := IsScalarTower.toAlgHom R S S'
  let y := IsLocalization.commonDenomOfFinset M s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨n, hn⟩ :=
    Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s : Set S') (A.map g)
      (by rw [hx₁]; exact Set.image_mono hA₁) hx (Set.mem_image_of_mem _ (hA₂ y.2))
  obtain ⟨x', hx', hx''⟩ := hn n (le_of_eq rfl)
  rw [Algebra.smul_def]; rw [← map_mul] at hx''
  obtain ⟨a, ha₂⟩ := (IsLocalization.eq_iff_exists M S').mp hx''
  use a * y ^ n
  convert! A.mul_mem hx' (hA₂ a.prop) using 1
  rw [Submonoid.smul_def]; rw [smul_eq_mul]; rw [Submonoid.coe_mul]; rw [SubmonoidClass.coe_pow]; rw [mul_assoc]; rw [← ha₂]; rw [mul_comm]

variable {S'} in
open scoped Classical in
/--
theorem `IsLocalization.lift_mem_adjoin_finsetIntegerMultiple` / 定理 `IsLocalization.lift_mem_adjoin_finsetIntegerMultiple`

English:
theorem IsLocalization.lift_mem_adjoin_finsetIntegerMultiple
  statement: [Algebra R S']
  proof: by
  obtain ⟨⟨_, a, ha, rfl⟩, e⟩ :=
    IsLocalization.exists_smul_mem_of_mem_adjoin (M.map (algebraMap R S)) x s (Algebra.adjoin R _)
      Algebra.subset_adjoin (by rintro _ ⟨a, _, rfl⟩; exact Subalgebra.algebraMap_mem _ a) hx
  refine ⟨⟨a, ha⟩, ?_⟩
  simpa only [Submonoid.smul_def, algebraMap_smu

中文:
定理 IsLocalization.lift_mem_adjoin_finsetIntegerMultiple
  结论: [Algebra R S']
  证明: by
  obtain ⟨⟨_, a, ha, rfl⟩, e⟩ :=
    IsLocalization.exists_smul_mem_of_mem_adjoin (M.map (algebraMap R S)) x s (Algebra.adjoin R _)
      Algebra.subset_adjoin (by rintro _ ⟨a, _, rfl⟩; exact Subalgebra.algebraMap_mem _ a) hx
  refine ⟨⟨a, ha⟩, ?_⟩
  simpa only [Submonoid.smul_def, algebraMap_smu

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, IsLocalization, IsLocalization.exists_smul_mem_of_mem_adjoin, M.map, Subalgebra, Subalgebra.algebraMap_mem, Submonoid, Submonoid.smul_def, adjoin, algebraMap, algebraMap_mem, algebraMap_smul, exists_smul_mem_of_mem_adjoin, smul_def, subset_adjoin
-/
theorem IsLocalization.lift_mem_adjoin_finsetIntegerMultiple [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x in Algebra.adjoin R (s : Set S')) :
    exists m : M, m • x in
      Algebra.adjoin R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  obtain ⟨⟨_, a, ha, rfl⟩, e⟩ :=
    IsLocalization.exists_smul_mem_of_mem_adjoin (M.map (algebraMap R S)) x s (Algebra.adjoin R _)
      Algebra.subset_adjoin (by rintro _ ⟨a, _, rfl⟩; exact Subalgebra.algebraMap_mem _ a) hx
  refine ⟨⟨a, ha⟩, ?_⟩
  simpa only [Submonoid.smul_def, algebraMap_smul] using e

/--
lemma `Algebra.FiniteType.of_span_eq_top_target` / 引理 `Algebra.FiniteType.of_span_eq_top_target`

English:
lemma Algebra.FiniteType.of_span_eq_top_target
  statement: (s : Set S) (hs : Ideal.span (s : Set S) = ⊤)
  proof: by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FiniteType R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  -- Suppose `s : Finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
  -- Say `t r : Finset Sᵣ` generates

中文:
引理 Algebra.FiniteType.of_span_eq_top_target
  结论: (s : Set S) (hs : Ideal.span (s : Set S) = ⊤)
  证明: by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FiniteType R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  -- Suppose `s : Finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
  -- Say `t r : Finset Sᵣ` generates

Depends on / 依赖: Algebra, Algebra.FiniteType, FiniteType, Ideal.span_eq_top_iff_finite, Localization, Localization.Away, classical, i.property, i.val, property, replace, span_eq_top_iff_finite
-/
lemma Algebra.FiniteType.of_span_eq_top_target (s : Set S) (hs : Ideal.span (s : Set S) = ⊤)
    (h : forall x in s, Algebra.FiniteType R (Localization.Away x)) :
    Algebra.FiniteType R S := by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FiniteType R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  -- Suppose `s : Finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
  -- Say `t r : Finset Sᵣ` generates `Sᵣ`. By assumption, we may find `lᵢ` such that
  -- `∑ lᵢ * sᵢ = 1`. I claim that all `s` and `l` and the numerators of `t` and generates `S`.
  replace h := fun r => (h r).1
  choose t ht using h
  obtain ⟨l, hl⟩ :=
    (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) in Ideal.span (s : Set S) by rw [hs]; trivial)
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (x : S)) (t x)
  use s.attach.biUnion sf union s union l.support.image l
  rw [_root_.eq_top_iff]
  -- We need to show that every `x` falls in the subalgebra generated by those elements.
  -- Since all `s` and `l` are in the subalgebra, it suffices to check that `sᵢ ^ nᵢ • x` falls in
  -- the algebra for each `sᵢ` and some `nᵢ`.
  rintro x -
  apply Subalgebra.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set S) l hl _ _ x _
  · intro x hx
    apply Algebra.subset_adjoin
    rw [Finset.coe_union]; rw [Finset.coe_union]
    exact Or.inl (Or.inr hx)
  · intro i
    by_cases h : l i = 0; · rw [h]; exact zero_mem _
    apply Algebra.subset_adjoin
    rw [Finset.coe_union]; rw [Finset.coe_image]
    exact Or.inr (Set.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr h))
  · intro r
    rw [Finset.coe_union]; rw [Finset.coe_union]; rw [Finset.coe_biUnion]
    -- Since all `sᵢ` and numerators of `t r` are in the algebra, it suffices to show that the
    -- image of `x` in `Sᵣ` falls in the `R`-adjoin of `t r`, which is of course true.
    -- Porting note: The following `obtain` fails because Lean wants to know right away what the
    -- placeholders are, so we need to provide a little more guidance
    -- obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalization.exists_smul_mem_of_mem_adjoin
    -- (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) _ _ _
    rw [show forall A : Set S]; rw [(exists n]; rw [(r : S) ^ n • x in Algebra.adjoin R A) ↔
      (exists m : (Submonoid.powers (r : S))]; rw [(m : S) • x in Algebra.adjoin R A) by
      { exact fun _ => by simp [Submonoid.mem_powers_iff] }]
    refine IsLocalization.exists_smul_mem_of_mem_adjoin
      (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) ?_ ?_ ?_
    · intro x hx
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inl ⟨_, ⟨r, rfl⟩, _, ⟨s.mem_attach r, rfl⟩, hx⟩)
    · rw [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff]
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inr r.2)
    · rw [ht]; trivial

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `Algebra.FiniteType.of_span_eq_top_source` / 引理 `Algebra.FiniteType.of_span_eq_top_source`

English:
lemma Algebra.FiniteType.of_span_eq_top_source
  statement: (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
  proof: by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) := h i.val (h₁ i.property)
  classical
  let := fun r : s => (Localization.awayMap (algebraMap R S) r).toAlgebra
  set f := algebraMap R S
  constructor
  replace H := fun r => (h r).1
  choose s₁ s₂ using H
  let 

中文:
引理 Algebra.FiniteType.of_span_eq_top_source
  结论: (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
  证明: by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) := h i.val (h₁ i.property)
  classical
  let := fun r : s => (Localization.awayMap (algebraMap R S) r).toAlgebra
  set f := algebraMap R S
  constructor
  replace H := fun r => (h r).1
  choose s₁ s₂ using H
  let 

Depends on / 依赖: Algebra, Algebra.adjoin_attach_biUnion, Ideal.span_eq_top_iff_finite, IsLocalization, IsLocalization.finsetIntegerMultiple, Localization, Localization.awayMap, Submonoid, Submonoid.powers, adjoin_attach_biUnion, algebraMap, attach, awayMap, biUnion, classical, convert, eq_top_iff, finsetIntegerMultiple, i.property, i.val
-/
lemma Algebra.FiniteType.of_span_eq_top_source (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : forall i in s, Algebra.FiniteType (Localization.Away i) (Localization.Away i otimes[R] S)) :
    Algebra.FiniteType R S := by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) := h i.val (h₁ i.property)
  classical
  let := fun r : s => (Localization.awayMap (algebraMap R S) r).toAlgebra
  set f := algebraMap R S
  constructor
  replace H := fun r => (h r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  convert! (Algebra.adjoin_attach_biUnion (R := R) sf).trans _
  rw [eq_top_iff]
  rintro x -
  apply (⨆ x : s, Algebra.adjoin R (sf x : Set S)).toSubmodule.mem_of_span_eq_top_of_smul_pow_mem
    _ hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away r.val otimes[R] S))
      (algebraMap S _ x) (by rw [s₂ r]; trivial)
  rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R S]; rw [← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.lift_mem_adjoin_finsetIntegerMultiple (Submonoid.powers (r : R)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def]; rw [← Algebra.smul_def]; rw [smul_smul]; rw [← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Algebra.adjoin R (sf x : Set S)) r hn₂

end Algebra
