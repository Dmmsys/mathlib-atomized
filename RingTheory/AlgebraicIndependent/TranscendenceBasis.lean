/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Rank.Cardinal
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Transcendence basis

This file defines the transcendence basis as a maximal algebraically independent subset.

## Main results

* `exists_isTranscendenceBasis`: a ring extension has a transcendence basis
* `IsTranscendenceBasis.lift_cardinalMk_eq_trdeg`: any transcendence basis of a domain has
  cardinality equal to transcendental degree.
* `IsTranscendenceBasis.lift_cardinalMk_eq`: any two transcendence bases of a domain have the
  same cardinality.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence basis, transcendence degree, transcendence

-/

@[expose] public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u u' v w

variable {ι : Type u} {ι' : Type u'} (R : Type*) {S : Type v} {A : Type w}
variable {x : ι -> A} {y : ι' -> A}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open AlgebraicIndependent

variable {R} in
/--
theorem `exists_isTranscendenceBasis_superset` / 定理 `exists_isTranscendenceBasis_superset`

English:
theorem exists_isTranscendenceBasis_superset
  statement: {s : Set A}
  proof: by
  simpa [← isTranscendenceBasis_iff_maximal]
    using exists_maximal_algebraicIndependent s _ (subset_univ _) hs

中文:
定理 存在_isTranscendenceBasis_superset
  结论: {s : 集合 A}
  证明: by
  simpa [← isTranscendenceBasis_iff_maximal]
    using exists_maximal_algebraicIndependent s _ (subset_univ _) hs

Depends on / 依赖: exists_maximal_algebraicIndependent, isTranscendenceBasis_iff_maximal, subset_univ
-/
theorem exists_isTranscendenceBasis_superset {s : Set A}
    (hs : AlgebraicIndepOn R id s) :
    exists t, s subseteq t ∧ IsTranscendenceBasis R ((↑) : t -> A) := by
  simpa [← isTranscendenceBasis_iff_maximal]
    using exists_maximal_algebraicIndependent s _ (subset_univ _) hs

variable (A)
/--
theorem `exists_isTranscendenceBasis` / 定理 `exists_isTranscendenceBasis`

English:
theorem exists_isTranscendenceBasis
  given: [FaithfulSMul R A]
  proof: by
  simpa using exists_isTranscendenceBasis_superset
    ((algebraicIndependent_empty_iff R A).mpr (FaithfulSMul.algebraMap_injective R A))

中文:
定理 存在_isTranscendenceBasis
  条件: [忠实标量乘法 R A]
  证明: by
  simpa using exists_isTranscendenceBasis_superset
    ((algebraicIndependent_empty_iff R A).mpr (FaithfulSMul.algebraMap_injective R A))

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraicIndependent_empty_iff, exists_isTranscendenceBasis_superset
-/
theorem exists_isTranscendenceBasis [FaithfulSMul R A] :
    exists s : Set A, IsTranscendenceBasis R ((↑) : s -> A) := by
  simpa using exists_isTranscendenceBasis_superset
    ((algebraicIndependent_empty_iff R A).mpr (FaithfulSMul.algebraMap_injective R A))

/--
theorem `exists_isTranscendenceBasis'` / 定理 `exists_isTranscendenceBasis'`

English:
theorem exists_isTranscendenceBasis'
  given: [FaithfulSMul R A]
  proof: have ⟨s, h⟩ := exists_isTranscendenceBasis R A
  ⟨s, Subtype.val, h⟩

中文:
定理 存在_isTranscendenceBasis'
  条件: [忠实标量乘法 R A]
  证明: have ⟨s, h⟩ := exists_isTranscendenceBasis R A
  ⟨s, Subtype.val, h⟩

Depends on / 依赖: Subtype, Subtype.val, exists_isTranscendenceBasis
-/
theorem exists_isTranscendenceBasis' [FaithfulSMul R A] :
    exists (ι : Type w) (x : ι -> A), IsTranscendenceBasis R x :=
  have ⟨s, h⟩ := exists_isTranscendenceBasis R A
  ⟨s, Subtype.val, h⟩

variable {A}

open Cardinal in
/--
theorem `trdeg_eq_iSup_cardinalMk_isTranscendenceBasis` / 定理 `trdeg_eq_iSup_cardinalMk_isTranscendenceBasis`

English:
theorem trdeg_eq_iSup_cardinalMk_isTranscendenceBasis
  proof: by
  refine (ciSup_le' fun s => ?_).antisymm
    (ciSup_le' fun s => le_ciSup_of_le bddAbove_of_small ⟨s, s.2.1⟩ le_rfl)
  choose t ht using exists_isTranscendenceBasis_superset s.2
  exact le_ciSup_of_le bddAbove_of_small ⟨t, ht.2⟩ (mk_le_mk_of_subset ht.1)

中文:
定理 trdeg_eq_iSup_cardinalMk_isTranscendenceBasis
  证明: by
  refine (ciSup_le' fun s => ?_).antisymm
    (ciSup_le' fun s => le_ciSup_of_le bddAbove_of_small ⟨s, s.2.1⟩ le_rfl)
  choose t ht using exists_isTranscendenceBasis_superset s.2
  exact le_ciSup_of_le bddAbove_of_small ⟨t, ht.2⟩ (mk_le_mk_of_subset ht.1)

Depends on / 依赖: antisymm, bddAbove_of_small, ciSup_le, exists_isTranscendenceBasis_superset, le_ciSup_of_le, le_rfl, mk_le_mk_of_subset
-/
theorem trdeg_eq_iSup_cardinalMk_isTranscendenceBasis :
    trdeg R A = ⨆ ι : { s : Set A // IsTranscendenceBasis R ((↑) : s -> A) }, #ι.1 := by
  refine (ciSup_le' fun s => ?_).antisymm
    (ciSup_le' fun s => le_ciSup_of_le bddAbove_of_small ⟨s, s.2.1⟩ le_rfl)
  choose t ht using exists_isTranscendenceBasis_superset s.2
  exact le_ciSup_of_le bddAbove_of_small ⟨t, ht.2⟩ (mk_le_mk_of_subset ht.1)

variable {R}

/--
theorem `AlgebraicIndependent.isTranscendenceBasis_iff` / 定理 `AlgebraicIndependent.isTranscendenceBasis_iff`

English:
theorem AlgebraicIndependent.isTranscendenceBasis_iff
  statement: [Nontrivial R]
  proof: by
  fconstructor
  · rintro p κ w i' j rfl
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp]; rw [← @image_univ _ _ w] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w -> 

中文:
定理 AlgebraicIndependent.isTranscendenceBasis_iff
  结论: [非平凡 R]
  证明: by
  fconstructor
  · rintro p κ w i' j rfl
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp]; rw [← @image_univ _ _ w] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w -> 

Depends on / 依赖: coe_range, congr_arg, fconstructor, image_image, image_injective, image_injective.mpr, image_univ, injective, p.range_eq, range_comp, range_comp_subset_range, range_eq, range_eq_univ, range_eq_univ.mp, range_subset_iff, range_subset_iff.mp, specialize
-/
theorem AlgebraicIndependent.isTranscendenceBasis_iff [Nontrivial R]
    (i : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔
      forall (κ : Type w) (w : κ -> A) (_ : AlgebraicIndependent R w) (j : ι -> κ) (_ : w ∘ j = x),
        Surjective j := by
  fconstructor
  · rintro p κ w i' j rfl
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _)
    rw [range_comp]; rw [← @image_univ _ _ w] at p
    exact range_eq_univ.mp (image_injective.mpr i'.injective p)
  · intro p
    use i
    intro w i' h
    specialize p w ((↑) : w -> A) i' (fun i => ⟨x i, range_subset_iff.mp h i⟩) (by ext; simp)
    have q := congr_arg (fun s => ((↑) : w -> A) '' s) p.range_eq
    rw [← image_univ]; rw [image_image] at q
    simpa using q

/--
theorem `IsTranscendenceBasis.isAlgebraic` / 定理 `IsTranscendenceBasis.isAlgebraic`

English:
theorem IsTranscendenceBasis.isAlgebraic
  given: [Nontrivial R] (hx : IsTranscendenceBasis R x)
  proof: by
  constructor
  intro a
  rw [← not_iff_comm.1 (hx.1.option_iff_transcendental _).symm]
  intro ai
  have h₁ : range x subseteq range fun o : Option ι => o.elim a x := by
    rintro x ⟨y, rfl⟩
    exact ⟨some y, rfl⟩
  have h₂ : range x != range fun o : Option ι => o.elim a x := by
    intro h
  

中文:
定理 IsTranscendenceBasis.isAlgebraic
  条件: [非平凡 R] (hx : IsTranscendenceBasis R x)
  证明: by
  constructor
  intro a
  rw [← not_iff_comm.1 (hx.1.option_iff_transcendental _).symm]
  intro ai
  have h₁ : range x subseteq range fun o : Option ι => o.elim a x := by
    rintro x ⟨y, rfl⟩
    exact ⟨some y, rfl⟩
  have h₂ : range x != range fun o : Option ι => o.elim a x := by
    intro h
  

Depends on / 依赖: Set.range, ai.inje, ai.injective, algebraicIndependent_subtype_range, injective, not_iff_comm, o.elim, option_iff_transcendental, subseteq
-/
theorem IsTranscendenceBasis.isAlgebraic [Nontrivial R] (hx : IsTranscendenceBasis R x) :
    Algebra.IsAlgebraic (adjoin R (range x)) A := by
  constructor
  intro a
  rw [← not_iff_comm.1 (hx.1.option_iff_transcendental _).symm]
  intro ai
  have h₁ : range x subseteq range fun o : Option ι => o.elim a x := by
    rintro x ⟨y, rfl⟩
    exact ⟨some y, rfl⟩
  have h₂ : range x != range fun o : Option ι => o.elim a x := by
    intro h
    have : a in range x := by
      rw [h]
      exact ⟨none, rfl⟩
    rcases this with ⟨b, rfl⟩
    have : some b = none := ai.injective rfl
    simpa
  exact h₂ (hx.2 (Set.range fun o : Option ι => o.elim a x)
    ((algebraicIndependent_subtype_range ai.injective).2 ai) h₁)

/--
theorem `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic` / 定理 `AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic`

English:
theorem AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
  proof: by
  refine ⟨(·.isAlgebraic), fun alg => ⟨ind, fun s ind_s hxs => of_not_not fun hxs' => ?_⟩⟩
  have : ¬ s subseteq range x := (hxs' <| hxs.antisymm ·)
  have ⟨a, has, hax⟩ := not_subset.mp this
  rw [show range x = Subtype.val '' range (Set.inclusion hxs) by
    rw [← range_comp]; rw [val_comp_incl

中文:
定理 AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
  证明: by
  refine ⟨(·.isAlgebraic), fun alg => ⟨ind, fun s ind_s hxs => of_not_not fun hxs' => ?_⟩⟩
  have : ¬ s subseteq range x := (hxs' <| hxs.antisymm ·)
  have ⟨a, has, hax⟩ := not_subset.mp this
  rw [show range x = Subtype.val '' range (Set.inclusion hxs) by
    rw [← range_comp]; rw [val_comp_incl

Depends on / 依赖: Set.inclusion, Subtype, Subtype.range_val, Subtype.val, antisymm, hxs.antisymm, inclusion, ind_s, ind_s.transcendental_adjoin, isAlgebraic, not_subset, not_subset.mp, of_not_not, range_comp, range_val, subseteq, transcendental_adjoin, val_comp_inclusion
-/
theorem AlgebraicIndependent.isTranscendenceBasis_iff_isAlgebraic
    [Nontrivial R] (ind : AlgebraicIndependent R x) :
    IsTranscendenceBasis R x ↔ Algebra.IsAlgebraic (adjoin R (range x)) A := by
  refine ⟨(·.isAlgebraic), fun alg => ⟨ind, fun s ind_s hxs => of_not_not fun hxs' => ?_⟩⟩
  have : ¬ s subseteq range x := (hxs' <| hxs.antisymm ·)
  have ⟨a, has, hax⟩ := not_subset.mp this
  rw [show range x = Subtype.val '' range (Set.inclusion hxs) by
    rw [← range_comp]; rw [val_comp_inclusion]; rw [Subtype.range_val]] at alg
  refine ind_s.transcendental_adjoin (s := range (inclusion hxs)) (i := ⟨a, has⟩) ?_ (alg.1 _)
  simpa using hax

/--
theorem `isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic` / 定理 `isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic`

English:
theorem isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic
  given: [Nontrivial R]
  proof: ⟨fun h => ⟨h.1, h.1.isTranscendenceBasis_iff_isAlgebraic.mp h⟩,
    fun ⟨ind, alg⟩ => ind.isTranscendenceBasis_iff_isAlgebraic.mpr alg⟩

中文:
定理 isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic
  条件: [非平凡 R]
  证明: ⟨fun h => ⟨h.1, h.1.isTranscendenceBasis_iff_isAlgebraic.mp h⟩,
    fun ⟨ind, alg⟩ => ind.isTranscendenceBasis_iff_isAlgebraic.mpr alg⟩

Depends on / 依赖: ind.isTranscendenceBasis_iff_isAlgebraic.mpr, isTranscendenceBasis_iff_isAlgebraic, isTranscendenceBasis_iff_isAlgebraic.mp
-/
theorem isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic [Nontrivial R] :
    IsTranscendenceBasis R x ↔
      AlgebraicIndependent R x ∧ Algebra.IsAlgebraic (adjoin R (range x)) A :=
  ⟨fun h => ⟨h.1, h.1.isTranscendenceBasis_iff_isAlgebraic.mp h⟩,
    fun ⟨ind, alg⟩ => ind.isTranscendenceBasis_iff_isAlgebraic.mpr alg⟩

/--
lemma `IsTranscendenceBasis.algebraMap_comp` / 引理 `IsTranscendenceBasis.algebraMap_comp`

English:
lemma IsTranscendenceBasis.algebraMap_comp
  proof: by
  let f := IsScalarTower.toAlgHom R S A
  refine hx.1.map (f := f) (FaithfulSMul.algebraMap_injective S A).injOn
.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_comp]; rw [← AlgHom.map_adjoin]
  set Rx := adjoin R (range x)
  let e := Rx.equivMapOfInjective f (FaithfulSMul.algebraMap

中文:
引理 IsTranscendenceBasis.algebraMap_comp
  证明: by
  let f := IsScalarTower.toAlgHom R S A
  refine hx.1.map (f := f) (FaithfulSMul.algebraMap_injective S A).injOn
.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_comp]; rw [← AlgHom.map_adjoin]
  set Rx := adjoin R (range x)
  let e := Rx.equivMapOfInjective f (FaithfulSMul.algebraMap

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, Algebra, Algebra.IsAlgebraic, FaithfulSMul, FaithfulSMul.algebraMap_injective, IsAlgebraic, IsScalarTower, IsScalarTower.toAlgHom, Rx.equivMapOfInjective, Rx.map, Set.range_comp, adjoin, algebraMap_injective, e.toRingHom.toAlgebra, equivMapOfInjective, hx.isAlgebraic, isAlgebraic, isTranscendenceBasis_iff_isAlgebraic, isTranscendenceBasis_iff_isAlgebraic.mpr
-/
lemma IsTranscendenceBasis.algebraMap_comp
    [Nontrivial R] [NoZeroDivisors S] [Algebra.IsAlgebraic S A] [FaithfulSMul S A]
    {x : ι -> S} (hx : IsTranscendenceBasis R x) : IsTranscendenceBasis R (algebraMap S A ∘ x) := by
  let f := IsScalarTower.toAlgHom R S A
  refine hx.1.map (f := f) (FaithfulSMul.algebraMap_injective S A).injOn
.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  rw [Set.range_comp]; rw [← AlgHom.map_adjoin]
  set Rx := adjoin R (range x)
  let e := Rx.equivMapOfInjective f (FaithfulSMul.algebraMap_injective S A)
  let := e.toRingHom.toAlgebra
  have : IsScalarTower Rx (Rx.map f) A := .of_algebraMap_eq fun x => rfl
  have : Algebra.IsAlgebraic Rx S := hx.isAlgebraic
  have : Algebra.IsAlgebraic Rx A := .trans _ S _
  exact .extendScalars e.injective

/--
lemma `IsTranscendenceBasis.isAlgebraic_iff` / 引理 `IsTranscendenceBasis.isAlgebraic_iff`

English:
lemma IsTranscendenceBasis.isAlgebraic_iff
  statement: [IsDomain S] [NoZeroDivisors A]
  proof: by
  refine ⟨fun _ i => Algebra.IsAlgebraic.isAlgebraic (v i), fun H => ?_⟩
  let Rv := adjoin R (range v)
  let Sv := adjoin S (range v)
  have : Algebra.IsAlgebraic S Sv := by
    simpa [Sv, ← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
  have le : Rv <= Sv.restrictScalars R := by
    rw [

中文:
引理 IsTranscendenceBasis.isAlgebraic_iff
  结论: [是整环 S] [无零因子 A]
  证明: by
  refine ⟨fun _ i => Algebra.IsAlgebraic.isAlgebraic (v i), fun H => ?_⟩
  let Rv := adjoin R (range v)
  let Sv := adjoin S (range v)
  have : Algebra.IsAlgebraic S Sv := by
    simpa [Sv, ← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
  have le : Rv <= Sv.restrictScalars R := by
    rw [

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, IsScalarTower, Subalgebra, Subalgebra.inclusion, Subalgebra.isAlgebraic_iff, Subalgebra.restrictScalars_adjoin, Sv.restrictScalars, adjoin, algebraMap, domain_nontrivia, inclusion, isAlgebraic, isAlgebraic_adjoin_iff, isAlgebraic_iff, le_sup_right, of_algebraMap_eq, restrictScalars
-/
lemma IsTranscendenceBasis.isAlgebraic_iff [IsDomain S] [NoZeroDivisors A]
    {ι : Type*} {v : ι -> A} (hv : IsTranscendenceBasis R v) :
    Algebra.IsAlgebraic S A ↔ forall i, IsAlgebraic S (v i) := by
  refine ⟨fun _ i => Algebra.IsAlgebraic.isAlgebraic (v i), fun H => ?_⟩
  let Rv := adjoin R (range v)
  let Sv := adjoin S (range v)
  have : Algebra.IsAlgebraic S Sv := by
    simpa [Sv, ← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
  have le : Rv <= Sv.restrictScalars R := by
    rw [Subalgebra.restrictScalars_adjoin]; exact le_sup_right
  let : Algebra Rv Sv := (Subalgebra.inclusion le).toAlgebra
  have : IsScalarTower Rv Sv A := .of_algebraMap_eq fun x => rfl
  have := (algebraMap R S).domain_nontrivial
  have := hv.isAlgebraic
  have : Algebra.IsAlgebraic Sv A := .extendScalars (Subalgebra.inclusion_injective le)
  exact .trans _ Sv _

variable (ι R)

/--
theorem `IsTranscendenceBasis.mvPolynomial` / 定理 `IsTranscendenceBasis.mvPolynomial`

English:
theorem IsTranscendenceBasis.mvPolynomial
  given: [Nontrivial R]
  proof: by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨algebraicIndependent_X .., ?_⟩
  rw [adjoin_range_X]
  set A := MvPolynomial ι R
  have := Algebra.isIntegral_of_surjective (R := (⊤ : Subalgebra R A)) (B := A) (⟨⟨·, ⟨⟩⟩, rfl⟩)
  infer_instance

中文:
定理 IsTranscendenceBasis.mvPolynomial
  条件: [非平凡 R]
  证明: by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨algebraicIndependent_X .., ?_⟩
  rw [adjoin_range_X]
  set A := MvPolynomial ι R
  have := Algebra.isIntegral_of_surjective (R := (⊤ : Subalgebra R A)) (B := A) (⟨⟨·, ⟨⟩⟩, rfl⟩)
  infer_instance

Depends on / 依赖: Algebra, Algebra.isIntegral_of_surjective, MvPolynomial, Subalgebra, adjoin_range_X, algebraicIndependent_X, infer_instance, isIntegral_of_surjective, isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic
-/
theorem IsTranscendenceBasis.mvPolynomial [Nontrivial R] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by
  refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨algebraicIndependent_X .., ?_⟩
  rw [adjoin_range_X]
  set A := MvPolynomial ι R
  have := Algebra.isIntegral_of_surjective (R := (⊤ : Subalgebra R A)) (B := A) (⟨⟨·, ⟨⟩⟩, rfl⟩)
  infer_instance

/--
theorem `IsTranscendenceBasis.mvPolynomial'` / 定理 `IsTranscendenceBasis.mvPolynomial'`

English:
theorem IsTranscendenceBasis.mvPolynomial'
  given: [Nonempty ι]
  proof: by nontriviality R; exact .mvPolynomial ι R

中文:
定理 IsTranscendenceBasis.mvPolynomial'
  条件: [非空 ι]
  证明: by nontriviality R; exact .mvPolynomial ι R

Depends on / 依赖: mvPolynomial, nontriviality
-/
theorem IsTranscendenceBasis.mvPolynomial' [Nonempty ι] :
    IsTranscendenceBasis R (X (R := R) (σ := ι)) := by nontriviality R; exact .mvPolynomial ι R

/--
theorem `IsTranscendenceBasis.polynomial` / 定理 `IsTranscendenceBasis.polynomial`

English:
theorem IsTranscendenceBasis.polynomial
  given: [Nonempty ι] [Subsingleton ι]
  proof: by
  nontriviality R
  have := (nonempty_unique ι).some
refine (isTranscendenceBasis_equiv (Equiv.equivPUnit.{_, 1} _).symm).mp
    (MvPolynomial.uniqueAlgEquiv R PUnit).symm.isTranscendenceBasis_iff.mp ?_
  convert! IsTranscendenceBasis.mvPolynomial PUnit R
  ext; simp

中文:
定理 IsTranscendenceBasis.polynomial
  条件: [非空 ι] [子单例 ι]
  证明: by
  nontriviality R
  have := (nonempty_unique ι).some
refine (isTranscendenceBasis_equiv (Equiv.equivPUnit.{_, 1} _).symm).mp
    (MvPolynomial.uniqueAlgEquiv R PUnit).symm.isTranscendenceBasis_iff.mp ?_
  convert! IsTranscendenceBasis.mvPolynomial PUnit R
  ext; simp

Depends on / 依赖: Equiv.equivPUnit, IsTranscendenceBasis, IsTranscendenceBasis.mvPolynomial, MvPolynomial, MvPolynomial.uniqueAlgEquiv, convert, equivPUnit, isTranscendenceBasis_equiv, isTranscendenceBasis_iff, mvPolynomial, nonempty_unique, nontriviality, symm.isTranscendenceBasis_iff.mp, uniqueAlgEquiv
-/
theorem IsTranscendenceBasis.polynomial [Nonempty ι] [Subsingleton ι] :
    IsTranscendenceBasis R fun _ : ι => (.X : Polynomial R) := by
  nontriviality R
  have := (nonempty_unique ι).some
refine (isTranscendenceBasis_equiv (Equiv.equivPUnit.{_, 1} _).symm).mp
    (MvPolynomial.uniqueAlgEquiv R PUnit).symm.isTranscendenceBasis_iff.mp ?_
  convert! IsTranscendenceBasis.mvPolynomial PUnit R
  ext; simp

variable {ι R}

/--
theorem `IsTranscendenceBasis.sumElim_comp` / 定理 `IsTranscendenceBasis.sumElim_comp`

English:
theorem IsTranscendenceBasis.sumElim_comp
  statement: [NoZeroDivisors A] {x : ι -> S} {y : ι' -> A}
  proof: by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  rw [(hx.1.sumElim_comp hy.1).isTranscendenceBasis_iff_isAlgebraic]
  set Rx := adjoin R (range x)
  let Rxy := adjoin Rx (range y)
  rw [show adjoin R (range <| Sum.elim y (algebraMap 

中文:
定理 IsTranscendenceBasis.sumElim_comp
  结论: [无零因子 A] {x : ι -> S} {y : ι' -> A}
  证明: by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  rw [(hx.1.sumElim_comp hy.1).isTranscendenceBasis_iff_isAlgebraic]
  set Rx := adjoin R (range x)
  let Rxy := adjoin Rx (range y)
  rw [show adjoin R (range <| Sum.elim y (algebraMap 

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, IsAlgebraic, Rxy.restrictScalars, Sum.elim, Sum.elim_range, adjoin, adjoin_algebraMap_image_union_eq_adjoin_adjoin, algebraMap, algebraMap_injectiv, elim_range, infer_instance, isTranscendenceBasis_iff_isAlgebraic, isTranscendenceBasis_iff_of_subsingleton, range_comp, restrictScalars, subsingleton_or_nontrivial, sumElim_comp, union_comm
-/
theorem IsTranscendenceBasis.sumElim_comp [NoZeroDivisors A] {x : ι -> S} {y : ι' -> A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis S y) :
    IsTranscendenceBasis R (Sum.elim y (algebraMap S A ∘ x)) := by
  cases subsingleton_or_nontrivial R
  · rw [isTranscendenceBasis_iff_of_subsingleton] at hx ⊢; infer_instance
  rw [(hx.1.sumElim_comp hy.1).isTranscendenceBasis_iff_isAlgebraic]
  set Rx := adjoin R (range x)
  let Rxy := adjoin Rx (range y)
  rw [show adjoin R (range <| Sum.elim y (algebraMap S A ∘ x)) = Rxy.restrictScalars R by
    rw [← adjoin_algebraMap_image_union_eq_adjoin_adjoin]; rw [Sum.elim_range]; rw [union_comm]; rw [range_comp]]
  change Algebra.IsAlgebraic Rxy A
  have := hx.1.algebraMap_injective.nontrivial
  have := hy.1.algebraMap_injective.nontrivial
  have := hy.isAlgebraic
  set Sy := adjoin S (range y)
  let _ : Algebra Rxy Sy := by
    refine (Subalgebra.inclusion (T := Sy.restrictScalars Rx) <| adjoin_le ?_).toAlgebra
    rintro _ ⟨i, rfl⟩; exact subset_adjoin (s := range y) ⟨i, rfl⟩
  have : IsScalarTower Rxy Sy A := .of_algebraMap_eq fun ⟨a, _⟩ => show a = _ from rfl
  have : IsScalarTower Rx Rxy Sy := .of_algebraMap_eq fun ⟨a, _⟩ => Subtype.ext rfl
  have : Algebra.IsAlgebraic Rxy Sy := by
    refine ⟨fun ⟨a, ha⟩ => adjoin_induction ?_ (fun _ => .extendScalars (R := Rx) ?_ ?_)
      (fun _ _ _ _ => .add) (fun _ _ _ _ => .mul) ha⟩
    · rintro _ ⟨i, rfl⟩; exact isAlgebraic_algebraMap (⟨y i, subset_adjoin ⟨i, rfl⟩⟩ : Rxy)
    · exact fun _ _ => (Subtype.ext <| hy.1.algebraMap_injective <| Subtype.ext_iff.mp ·)
    · exact (hx.isAlgebraic.1 _).algHom (IsScalarTower.toAlgHom Rx S Sy)
  exact .trans _ Sy _

/--
theorem `IsTranscendenceBasis.isEmpty_iff_isAlgebraic` / 定理 `IsTranscendenceBasis.isEmpty_iff_isAlgebraic`

English:
theorem IsTranscendenceBasis.isEmpty_iff_isAlgebraic
  statement: [Nontrivial R]
  proof: by
  refine ⟨fun _ => ?_, fun _ => hx.1.isEmpty_of_isAlgebraic⟩
  have := hx.isAlgebraic
  rw [Set.range_eq_empty x]; rw [adjoin_empty] at this
  exact algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left R A

中文:
定理 IsTranscendenceBasis.isEmpty_iff_isAlgebraic
  结论: [非平凡 R]
  证明: by
  refine ⟨fun _ => ?_, fun _ => hx.1.isEmpty_of_isAlgebraic⟩
  have := hx.isAlgebraic
  rw [Set.range_eq_empty x]; rw [adjoin_empty] at this
  exact algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left R A

Depends on / 依赖: Set.range_eq_empty, adjoin_empty, algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left, hx.isAlgebraic, isAlgebraic, isEmpty_of_isAlgebraic, range_eq_empty
-/
theorem IsTranscendenceBasis.isEmpty_iff_isAlgebraic [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    IsEmpty ι ↔ Algebra.IsAlgebraic R A := by
  refine ⟨fun _ => ?_, fun _ => hx.1.isEmpty_of_isAlgebraic⟩
  have := hx.isAlgebraic
  rw [Set.range_eq_empty x]; rw [adjoin_empty] at this
  exact algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left R A

/--
theorem `IsTranscendenceBasis.nonempty_iff_transcendental` / 定理 `IsTranscendenceBasis.nonempty_iff_transcendental`

English:
theorem IsTranscendenceBasis.nonempty_iff_transcendental
  statement: [Nontrivial R]
  proof: by
  rw [← not_isEmpty_iff]; rw [Algebra.transcendental_iff_not_isAlgebraic]; rw [hx.isEmpty_iff_isAlgebraic]

中文:
定理 IsTranscendenceBasis.nonempty_iff_transcendental
  结论: [非平凡 R]
  证明: by
  rw [← not_isEmpty_iff]; rw [Algebra.transcendental_iff_not_isAlgebraic]; rw [hx.isEmpty_iff_isAlgebraic]

Depends on / 依赖: Algebra, Algebra.transcendental_iff_not_isAlgebraic, hx.isEmpty_iff_isAlgebraic, isEmpty_iff_isAlgebraic, not_isEmpty_iff, transcendental_iff_not_isAlgebraic
-/
theorem IsTranscendenceBasis.nonempty_iff_transcendental [Nontrivial R]
    (hx : IsTranscendenceBasis R x) :
    Nonempty ι ↔ Algebra.Transcendental R A := by
  rw [← not_isEmpty_iff]; rw [Algebra.transcendental_iff_not_isAlgebraic]; rw [hx.isEmpty_iff_isAlgebraic]

/--
theorem `IsTranscendenceBasis.isAlgebraic_field` / 定理 `IsTranscendenceBasis.isAlgebraic_field`

English:
theorem IsTranscendenceBasis.isAlgebraic_field
  statement: {F E : Type*} {x : ι -> E}
  proof: by
  have := hx.isAlgebraic
  set S := range x
  let : Algebra (adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  have : IsScalarTower (adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_a

中文:
定理 IsTranscendenceBasis.isAlgebraic_field
  结论: {F E : 类型} {x : ι -> E}
  证明: by
  have := hx.isAlgebraic
  set S := range x
  let : Algebra (adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  have : IsScalarTower (adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_a

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.extendScalars, IntermediateField, IntermediateField.adjoin, IntermediateField.algebra_adjoin_le_adjoin, IsAlgebraic, IsScalarTower, IsScalarTower.of_algebraMap_eq, Subalgebra, Subalgebra.inclusion, Subalgebra.inclusion_injective, adjoin, algebra_adjoin_le_adjoin, extendScalars, hx.isAlgebraic, inclusion, inclusion_injective, isAlgebraic, of_algebraMap_eq, toAlgebra
-/
theorem IsTranscendenceBasis.isAlgebraic_field {F E : Type*} {x : ι -> E}
    [Field F] [Field E] [Algebra F E] (hx : IsTranscendenceBasis F x) :
    Algebra.IsAlgebraic (IntermediateField.adjoin F (range x)) E := by
  have := hx.isAlgebraic
  set S := range x
  let : Algebra (adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  have : IsScalarTower (adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact Algebra.IsAlgebraic.extendScalars (R := adjoin F S) (Subalgebra.inclusion_injective _)

namespace AlgebraicIndependent

variable (R A) [FaithfulSMul R A]

section

variable [NoZeroDivisors A]

set_option backward.privateInPublic true in
/--
Definition of `indepMatroid` / `indepMatroid` 的定义

English:
definition indepMatroid
  signature: : IndepMatroid A where
  body: univ
  Indep := AlgebraicIndepOn R id
  indep_empty := (algebraicIndependent_empty_iff ..).mpr (FaithfulSMul.algebraMap_injective R A)
  indep_subset _ _ := (·.mono)
  indep_aug I B I_ind h B_base := by
    contrapose! h
    rw [← isTranscendenceBasis_iff_maximal] at B_base ⊢
    cases subsingleton_

中文:
定义 indepMatroid
  签名: : 独立拟阵 A where
  定义体: univ
  Indep := AlgebraicIndepOn R id
  indep_empty := (algebraicIndependent_empty_iff ..).mpr (FaithfulSMul.algebraMap_injective R A)
  indep_subset _ _ := (·.mono)
  indep_aug I B I_ind h B_base := by
    contrapose! h
    rw [← isTranscendenceBasis_iff_maximal] at B_base ⊢
    cases subsingleton_
-/
private def indepMatroid : IndepMatroid A where
  E := univ
  Indep := AlgebraicIndepOn R id
  indep_empty := (algebraicIndependent_empty_iff ..).mpr (FaithfulSMul.algebraMap_injective R A)
  indep_subset _ _ := (·.mono)
  indep_aug I B I_ind h B_base := by
    contrapose! h
    rw [← isTranscendenceBasis_iff_maximal] at B_base ⊢
    cases subsingleton_or_nontrivial R
    · rw [isTranscendenceBasis_iff_of_subsingleton] at B_base ⊢
      by_contra this
      have ⟨b, hb⟩ := B_base
      exact h b ⟨hb, fun hbI => this ⟨b, hbI⟩⟩ .of_subsingleton
    apply I_ind.isTranscendenceBasis_iff_isAlgebraic.mpr
    replace B_base := B_base.isAlgebraic
    simp_rw +instances [id_eq]
    rw [Subtype.range_val] at B_base ⊢
    refine ⟨fun a => (B_base.1 a).adjoin_of_forall_isAlgebraic fun x hx => ?_⟩
    contrapose! h
exact ⟨x, hx, I_ind.insert by rwa [image_id]⟩
  indep_maximal X _ I ind hIX := exists_maximal_algebraicIndependent I X hIX ind
  subset_ground _ _ := subset_univ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `matroid` / `matroid` 的定义

English:
definition matroid
  signature: : Matroid A
  body: (indepMatroid R A).matroid.copyBase univ
  (fun s => IsTranscendenceBasis R ((↑) : s -> A)) rfl
  (fun B => by simp_rw [Matroid.isBase_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl)

中文:
定义 matroid
  签名: : 拟阵 A
  定义体: (indepMatroid R A).matroid.copyBase univ
  (fun s => IsTranscendenceBasis R ((↑) : s -> A)) rfl
  (fun B => by simp_rw [Matroid.isBase_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl)

Depends on / 依赖: copyBase, indepMatroid, matroid, matroid.copyBase
-/
def matroid : Matroid A := (indepMatroid R A).matroid.copyBase univ
  (fun s => IsTranscendenceBasis R ((↑) : s -> A)) rfl
  (fun B => by simp_rw [Matroid.isBase_iff_maximal_indep, isTranscendenceBasis_iff_maximal]; rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (matroid R A).Finitary
  body: algebraicIndependent_of_finite

中文:
实例 :
  签名: (matroid R A).Finitary
  定义体: algebraicIndependent_of_finite

Depends on / 依赖: algebraicIndependent_of_finite
-/
instance : (matroid R A).Finitary where
  indep_of_forall_finite := algebraicIndependent_of_finite

/--
theorem `matroid_e` / 定理 `matroid_e`

English:
theorem matroid_e
  statement: (matroid R A).E = univ
  proof: rfl

中文:
定理 matroid_e
  结论: (matroid R A).E = univ
  证明: rfl
-/
@[simp] theorem matroid_e : (matroid R A).E = univ := rfl

/--
theorem `matroid_cRank_eq` / 定理 `matroid_cRank_eq`

English:
theorem matroid_cRank_eq
  statement: (matroid R A).cRank = trdeg R A
  proof: (trdeg_eq_iSup_cardinalMk_isTranscendenceBasis _).symm

中文:
定理 matroid_cRank_eq
  结论: (matroid R A).cRank = trdeg R A
  证明: (trdeg_eq_iSup_cardinalMk_isTranscendenceBasis _).symm

Depends on / 依赖: trdeg_eq_iSup_cardinalMk_isTranscendenceBasis
-/
theorem matroid_cRank_eq : (matroid R A).cRank = trdeg R A :=
  (trdeg_eq_iSup_cardinalMk_isTranscendenceBasis _).symm

variable {R A}

/--
theorem `matroid_indep_iff` / 定理 `matroid_indep_iff`

English:
theorem matroid_indep_iff
  given: {s : Set A}
  proof: Iff.rfl

中文:
定理 matroid_indep_iff
  条件: {s : 集合 A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem matroid_indep_iff {s : Set A} :
    (matroid R A).Indep s ↔ AlgebraicIndepOn R id s := Iff.rfl

/--
theorem `matroid_isBase_iff` / 定理 `matroid_isBase_iff`

English:
theorem matroid_isBase_iff
  given: {s : Set A}
  proof: Iff.rfl

中文:
定理 matroid_isBase_iff
  条件: {s : 集合 A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem matroid_isBase_iff {s : Set A} :
    (matroid R A).IsBase s ↔ IsTranscendenceBasis R ((↑) : s -> A) := Iff.rfl

end

variable {R A}

/--
theorem `matroid_isBasis_iff` / 定理 `matroid_isBasis_iff`

English:
theorem matroid_isBasis_iff
  given: [IsDomain A] {s t : Set A}
  statement: (matroid R A).IsBasis s t ↔
  proof: by
  rw [Matroid.IsBasis]; rw [maximal_iff_forall_insert fun s t h hst => ⟨h.1.subset hst]; rw [hst.trans h.2⟩]
  simp_rw [matroid_indep_iff, ← and_assoc, matroid_e, subset_univ, and_true]
  exact and_congr_right fun h => ⟨fun max a ha => of_not_not fun tr => max _
    (fun ha => tr (isAlgebraic_alg

中文:
定理 matroid_isBasis_iff
  条件: [是整环 A] {s t : 集合 A}
  结论: (matroid R A).是基 s t ↔
  证明: by
  rw [Matroid.IsBasis]; rw [maximal_iff_forall_insert fun s t h hst => ⟨h.1.subset hst]; rw [hst.trans h.2⟩]
  simp_rw [matroid_indep_iff, ← and_assoc, matroid_e, subset_univ, and_true]
  exact and_congr_right fun h => ⟨fun max a ha => of_not_not fun tr => max _
    (fun ha => tr (isAlgebraic_alg

Depends on / 依赖: AlgebraicIndepOn, AlgebraicIndepOn.insert_iff, IsBasis, Matroid, Matroid.IsBasis, adjoin, and_assoc, and_congr_right, and_true, hst.trans, image_id, insert, insert_iff, insert_subset, isAlgebraic_algebraMap, matroid_e, matroid_indep_iff, maximal_iff_forall_insert, mem_insert, of_not_not
-/
theorem matroid_isBasis_iff [IsDomain A] {s t : Set A} : (matroid R A).IsBasis s t ↔
    AlgebraicIndepOn R id s ∧ s subseteq t ∧ forall a in t, IsAlgebraic (adjoin R s) a := by
  rw [Matroid.IsBasis]; rw [maximal_iff_forall_insert fun s t h hst => ⟨h.1.subset hst]; rw [hst.trans h.2⟩]
  simp_rw [matroid_indep_iff, ← and_assoc, matroid_e, subset_univ, and_true]
  exact and_congr_right fun h => ⟨fun max a ha => of_not_not fun tr => max _
    (fun ha => tr (isAlgebraic_algebraMap (⟨a, subset_adjoin ha⟩ : adjoin R s)))
      ⟨.insert h.1 (by rwa [image_id]), insert_subset ha h.2⟩,
fun alg a ha h => ((AlgebraicIndepOn.insert_iff ha).mp h.1).2 by
rw [image_id]; exact alg _ h.2 mem_insert ..⟩

open Subsingleton in
/--
theorem `matroid_isBasis_iff_of_subsingleton` / 定理 `matroid_isBasis_iff_of_subsingleton`

English:
theorem matroid_isBasis_iff_of_subsingleton
  given: [Subsingleton A] {s t : Set A}
  proof: by
  have := (FaithfulSMul.algebraMap_injective R A).subsingleton
  simp_rw [Matroid.IsBasis, matroid_indep_iff, of_subsingleton, true_and,
    matroid_e, subset_univ, and_true, maximal_le_iff]

中文:
定理 matroid_isBasis_iff_of_subsingleton
  条件: [子单例 A] {s t : 集合 A}
  证明: by
  have := (FaithfulSMul.algebraMap_injective R A).subsingleton
  simp_rw [Matroid.IsBasis, matroid_indep_iff, of_subsingleton, true_and,
    matroid_e, subset_univ, and_true, maximal_le_iff]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsBasis, Matroid, Matroid.IsBasis, algebraMap_injective, and_true, matroid_e, matroid_indep_iff, maximal_le_iff, of_subsingleton, simp_rw, subset_univ, subsingleton, true_and
-/
theorem matroid_isBasis_iff_of_subsingleton [Subsingleton A] {s t : Set A} :
    (matroid R A).IsBasis s t ↔ s = t := by
  have := (FaithfulSMul.algebraMap_injective R A).subsingleton
  simp_rw [Matroid.IsBasis, matroid_indep_iff, of_subsingleton, true_and,
    matroid_e, subset_univ, and_true, maximal_le_iff]

/--
theorem `isAlgebraic_adjoin_iff_of_matroid_isBasis` / 定理 `isAlgebraic_adjoin_iff_of_matroid_isBasis`

English:
theorem isAlgebraic_adjoin_iff_of_matroid_isBasis
  statement: [NoZeroDivisors A] {s t : Set A} {a : A}
  proof: by
  cases subsingleton_or_nontrivial A
  · apply iff_of_false <;> apply is_transcendental_of_subsingleton
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨(·.adjoin_of_forall_isAlgebraic fun x hx => (hx.2 <| h.1.1.2 hx.1).elim),
    (·.adjoin_of_f

中文:
定理 isAlgebraic_adjoin_iff_of_matroid_isBasis
  结论: [无零因子 A] {s t : 集合 A} {a : A}
  证明: by
  cases subsingleton_or_nontrivial A
  · apply iff_of_false <;> apply is_transcendental_of_subsingleton
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨(·.adjoin_of_forall_isAlgebraic fun x hx => (hx.2 <| h.1.1.2 hx.1).elim),
    (·.adjoin_of_f

Depends on / 依赖: adjoin_of_forall_isAlgebraic, iff_of_false, isDomain_iff_noZeroDivisors_and_nontrivial, is_transcendental_of_subsingleton, matroid_isBasis_iff, matroid_isBasis_iff.mp, subsingleton_or_nontrivial
-/
theorem isAlgebraic_adjoin_iff_of_matroid_isBasis [NoZeroDivisors A] {s t : Set A} {a : A}
    (h : (matroid R A).IsBasis s t) : IsAlgebraic (adjoin R s) a ↔ IsAlgebraic (adjoin R t) a := by
  cases subsingleton_or_nontrivial A
  · apply iff_of_false <;> apply is_transcendental_of_subsingleton
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  exact ⟨(·.adjoin_of_forall_isAlgebraic fun x hx => (hx.2 <| h.1.1.2 hx.1).elim),
    (·.adjoin_of_forall_isAlgebraic fun x hx => (matroid_isBasis_iff.mp h).2.2 _ hx.1)⟩

/--
theorem `matroid_closure_eq` / 定理 `matroid_closure_eq`

English:
theorem matroid_closure_eq
  given: [IsDomain A] {s : Set A}
  proof: by
  have ⟨B, hB⟩ := (matroid R A).exists_isBasis s
  simp_rw [← hB.closure_eq_closure, hB.1.1.1.closure_eq_setOfPred_isBasis_insert, Set.ext_iff,
    mem_ofPred, matroid_isBasis_iff, ← matroid_indep_iff, hB.1.1.1, subset_insert, true_and,
    SetLike.mem_coe, mem_algebraicClosure, ← isAlgebraic_adj

中文:
定理 matroid_closure_eq
  条件: [是整环 A] {s : 集合 A}
  证明: by
  have ⟨B, hB⟩ := (matroid R A).exists_isBasis s
  simp_rw [← hB.closure_eq_closure, hB.1.1.1.closure_eq_setOfPred_isBasis_insert, Set.ext_iff,
    mem_ofPred, matroid_isBasis_iff, ← matroid_indep_iff, hB.1.1.1, subset_insert, true_and,
    SetLike.mem_coe, mem_algebraicClosure, ← isAlgebraic_adj

Depends on / 依赖: Set.ext_iff, SetLike, SetLike.mem_coe, adjoin, and_iff_left, closure_eq_closure, closure_eq_setOfPred_isBasis_insert, exists_isBasis, ext_iff, forall_mem_insert, hB.closure_eq_closure, isAlgebraic_adjoin_iff_of_matroid_isBasis, isAlgebraic_algebraMap, matroid, matroid_indep_iff, matroid_isBasis_iff, mem_algebraicClosure, mem_coe, mem_ofPred, simp_rw
-/
theorem matroid_closure_eq [IsDomain A] {s : Set A} :
    (matroid R A).closure s = algebraicClosure (adjoin R s) A := by
  have ⟨B, hB⟩ := (matroid R A).exists_isBasis s
  simp_rw [← hB.closure_eq_closure, hB.1.1.1.closure_eq_setOfPred_isBasis_insert, Set.ext_iff,
    mem_ofPred, matroid_isBasis_iff, ← matroid_indep_iff, hB.1.1.1, subset_insert, true_and,
    SetLike.mem_coe, mem_algebraicClosure, ← isAlgebraic_adjoin_iff_of_matroid_isBasis hB,
    forall_mem_insert]
  exact fun _ => and_iff_left fun x hx => isAlgebraic_algebraMap (⟨x, subset_adjoin hx⟩ : adjoin R B)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `matroid_isFlat_iff` / 定理 `matroid_isFlat_iff`

English:
theorem matroid_isFlat_iff
  given: [IsDomain A] {s : Set A}
  proof: by
  rw [Matroid.isFlat_iff_closure_eq]; rw [matroid_closure_eq]
  set S := algebraicClosure (adjoin R s) A
  refine ⟨fun eq => ⟨S.restrictScalars R, eq, fun a (h : IsAlgebraic S _) => ?_⟩, ?_⟩
  · rw [← eq]; exact h.restrictScalars (adjoin R s)
  rintro ⟨s, rfl, hs⟩
  refine Set.ext fun a => ⟨(hs _

中文:
定理 matroid_isFlat_iff
  条件: [是整环 A] {s : 集合 A}
  证明: by
  rw [Matroid.isFlat_iff_closure_eq]; rw [matroid_closure_eq]
  set S := algebraicClosure (adjoin R s) A
  refine ⟨fun eq => ⟨S.restrictScalars R, eq, fun a (h : IsAlgebraic S _) => ?_⟩, ?_⟩
  · rw [← eq]; exact h.restrictScalars (adjoin R s)
  rintro ⟨s, rfl, hs⟩
  refine Set.ext fun a => ⟨(hs _

Depends on / 依赖: IsAlgebraic, Matroid, Matroid.isFlat_iff_closure_eq, S.restrictScalars, Set.ext, adjoin, adjoin_eq, algebraicClosure, h.restrictScalars, isAlgebraic_algebraMap, isFlat_iff_closure_eq, matroid_closure_eq, restrictScalars, subset_adjoin
-/
theorem matroid_isFlat_iff [IsDomain A] {s : Set A} :
    (matroid R A).IsFlat s ↔ exists S : Subalgebra R A, S = s ∧ forall a : A, IsAlgebraic S a -> a in s := by
  rw [Matroid.isFlat_iff_closure_eq]; rw [matroid_closure_eq]
  set S := algebraicClosure (adjoin R s) A
  refine ⟨fun eq => ⟨S.restrictScalars R, eq, fun a (h : IsAlgebraic S _) => ?_⟩, ?_⟩
  · rw [← eq]; exact h.restrictScalars (adjoin R s)
  rintro ⟨s, rfl, hs⟩
  refine Set.ext fun a => ⟨(hs _ <| adjoin_eq s ▸ ·), fun h => ?_⟩
  exact isAlgebraic_algebraMap (A := A) (by exact (⟨a, subset_adjoin h⟩ : adjoin R s))

/--
theorem `matroid_spanning_iff` / 定理 `matroid_spanning_iff`

English:
theorem matroid_spanning_iff
  given: [IsDomain A] {s : Set A}
  proof: by
  simp_rw [Matroid.spanning_iff, matroid_e, subset_univ, and_true, eq_univ_iff_forall,
    matroid_closure_eq, SetLike.mem_coe, mem_algebraicClosure, Algebra.isAlgebraic_def]

中文:
定理 matroid_spanning_iff
  条件: [是整环 A] {s : 集合 A}
  证明: by
  simp_rw [Matroid.spanning_iff, matroid_e, subset_univ, and_true, eq_univ_iff_forall,
    matroid_closure_eq, SetLike.mem_coe, mem_algebraicClosure, Algebra.isAlgebraic_def]

Depends on / 依赖: Algebra, Algebra.isAlgebraic_def, Matroid, Matroid.spanning_iff, SetLike, SetLike.mem_coe, and_true, eq_univ_iff_forall, isAlgebraic_def, matroid_closure_eq, matroid_e, mem_algebraicClosure, mem_coe, simp_rw, spanning_iff, subset_univ
-/
theorem matroid_spanning_iff [IsDomain A] {s : Set A} :
    (matroid R A).Spanning s ↔ Algebra.IsAlgebraic (adjoin R s) A := by
  simp_rw [Matroid.spanning_iff, matroid_e, subset_univ, and_true, eq_univ_iff_forall,
    matroid_closure_eq, SetLike.mem_coe, mem_algebraicClosure, Algebra.isAlgebraic_def]

open Subsingleton -- brings the Subsingleton.to_noZeroDivisors instance into scope

/--
theorem `matroid_isFlat_of_subsingleton` / 定理 `matroid_isFlat_of_subsingleton`

English:
theorem matroid_isFlat_of_subsingleton
  given: [Subsingleton A] (s : Set A)
  statement: (matroid R A).IsFlat s
  proof: by
  simp_rw [Matroid.isFlat_iff, matroid_e, subset_univ,
    and_true, matroid_isBasis_iff_of_subsingleton]
  exact fun I X hIs hIX => (hIX.symm.trans hIs).subset

中文:
定理 matroid_isFlat_of_subsingleton
  条件: [子单例 A] (s : 集合 A)
  结论: (matroid R A).是平坦 s
  证明: by
  simp_rw [Matroid.isFlat_iff, matroid_e, subset_univ,
    and_true, matroid_isBasis_iff_of_subsingleton]
  exact fun I X hIs hIX => (hIX.symm.trans hIs).subset

Depends on / 依赖: Matroid, Matroid.isFlat_iff, and_true, hIX.symm.trans, isFlat_iff, matroid_e, matroid_isBasis_iff_of_subsingleton, simp_rw, subset, subset_univ
-/
theorem matroid_isFlat_of_subsingleton [Subsingleton A] (s : Set A) : (matroid R A).IsFlat s := by
  simp_rw [Matroid.isFlat_iff, matroid_e, subset_univ,
    and_true, matroid_isBasis_iff_of_subsingleton]
  exact fun I X hIs hIX => (hIX.symm.trans hIs).subset

/--
theorem `matroid_closure_of_subsingleton` / 定理 `matroid_closure_of_subsingleton`

English:
theorem matroid_closure_of_subsingleton
  given: [Subsingleton A] (s : Set A)
  proof: by
  simp_rw [Matroid.closure, matroid_isFlat_of_subsingleton, true_and, matroid_e, inter_univ]
  exact subset_antisymm (sInter_subset_of_mem <| subset_refl s) (subset_sInter fun _ => id)

中文:
定理 matroid_closure_of_subsingleton
  条件: [子单例 A] (s : 集合 A)
  证明: by
  simp_rw [Matroid.closure, matroid_isFlat_of_subsingleton, true_and, matroid_e, inter_univ]
  exact subset_antisymm (sInter_subset_of_mem <| subset_refl s) (subset_sInter fun _ => id)

Depends on / 依赖: Matroid, Matroid.closure, closure, inter_univ, matroid_e, matroid_isFlat_of_subsingleton, sInter_subset_of_mem, simp_rw, subset_antisymm, subset_refl, subset_sInter, true_and
-/
theorem matroid_closure_of_subsingleton [Subsingleton A] (s : Set A) :
    (matroid R A).closure s = s := by
  simp_rw [Matroid.closure, matroid_isFlat_of_subsingleton, true_and, matroid_e, inter_univ]
  exact subset_antisymm (sInter_subset_of_mem <| subset_refl s) (subset_sInter fun _ => id)

/--
theorem `matroid_spanning_iff_of_subsingleton` / 定理 `matroid_spanning_iff_of_subsingleton`

English:
theorem matroid_spanning_iff_of_subsingleton
  given: [Subsingleton A] {s : Set A}
  proof: by
  simp_rw [Matroid.spanning_iff, matroid_closure_of_subsingleton, matroid_e, subset_univ, and_true]

中文:
定理 matroid_spanning_iff_of_subsingleton
  条件: [子单例 A] {s : 集合 A}
  证明: by
  simp_rw [Matroid.spanning_iff, matroid_closure_of_subsingleton, matroid_e, subset_univ, and_true]

Depends on / 依赖: Matroid, Matroid.spanning_iff, and_true, matroid_closure_of_subsingleton, matroid_e, simp_rw, spanning_iff, subset_univ
-/
theorem matroid_spanning_iff_of_subsingleton [Subsingleton A] {s : Set A} :
    (matroid R A).Spanning s ↔ s = univ := by
  simp_rw [Matroid.spanning_iff, matroid_closure_of_subsingleton, matroid_e, subset_univ, and_true]

end AlgebraicIndependent

/--
theorem `exists_isTranscendenceBasis_between` / 定理 `exists_isTranscendenceBasis_between`

English:
theorem exists_isTranscendenceBasis_between
  statement: [NoZeroDivisors A] (s t : Set A) (hst : s subseteq t)
  proof: by
  have := ht.nontrivial
  have := Subtype.val_injective (p := (· in adjoin R t)).nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hs.algebraMap_injective
  rw [← matroid_spanning_iff] a

中文:
定理 存在_isTranscendenceBasis_between
  结论: [无零因子 A] (s t : 集合 A) (hst : s subseteq t)
  证明: by
  have := ht.nontrivial
  have := Subtype.val_injective (p := (· in adjoin R t)).nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hs.algebraMap_injective
  rw [← matroid_spanning_iff] a

Depends on / 依赖: Subtype, Subtype.val_injective, adjoin, algebraMap_injective, exists_isBase_subset_spanning, faithfulSMul_iff_algebraMap_injective, hs.algebraMap_injective, hs.exists_isBase_subset_spanning, ht.nontrivial, isDomain_iff_noZeroDivisors_and_nontrivial, matroid_indep_iff, matroid_spanning_iff, nontrivial, val_injective
-/
theorem exists_isTranscendenceBasis_between [NoZeroDivisors A] (s t : Set A) (hst : s subseteq t)
    (hs : AlgebraicIndepOn R id s) [ht : Algebra.IsAlgebraic (adjoin R t) A] :
    exists u, s subseteq u ∧ u subseteq t ∧ IsTranscendenceBasis R ((↑) : u -> A) := by
  have := ht.nontrivial
  have := Subtype.val_injective (p := (· in adjoin R t)).nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hs.algebraMap_injective
  rw [← matroid_spanning_iff] at ht
  rw [← matroid_indep_iff] at hs
  have ⟨B, base, hsB, hBt⟩ := hs.exists_isBase_subset_spanning ht hst
  exact ⟨B, hsB, hBt, base⟩

/--
theorem `exists_isTranscendenceBasis_subset` / 定理 `exists_isTranscendenceBasis_subset`

English:
theorem exists_isTranscendenceBasis_subset
  statement: [NoZeroDivisors A] [FaithfulSMul R A]
  proof: by
  have ⟨t, _, ht⟩ := exists_isTranscendenceBasis_between ∅ s (empty_subset _)
    ((algebraicIndependent_empty_iff ..).mpr <| FaithfulSMul.algebraMap_injective R A)
  exact ⟨t, ht⟩

中文:
定理 存在_isTranscendenceBasis_subset
  结论: [无零因子 A] [忠实标量乘法 R A]
  证明: by
  have ⟨t, _, ht⟩ := exists_isTranscendenceBasis_between ∅ s (empty_subset _)
    ((algebraicIndependent_empty_iff ..).mpr <| FaithfulSMul.algebraMap_injective R A)
  exact ⟨t, ht⟩

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraicIndependent_empty_iff, empty_subset, exists_isTranscendenceBasis_between
-/
theorem exists_isTranscendenceBasis_subset [NoZeroDivisors A] [FaithfulSMul R A]
    (s : Set A) [Algebra.IsAlgebraic (adjoin R s) A] :
    exists t, t subseteq s ∧ IsTranscendenceBasis R ((↑) : t -> A) := by
  have ⟨t, _, ht⟩ := exists_isTranscendenceBasis_between ∅ s (empty_subset _)
    ((algebraicIndependent_empty_iff ..).mpr <| FaithfulSMul.algebraMap_injective R A)
  exact ⟨t, ht⟩

/--
theorem `isAlgebraic_iff_exists_isTranscendenceBasis_subset` / 定理 `isAlgebraic_iff_exists_isTranscendenceBasis_subset`

English:
theorem isAlgebraic_iff_exists_isTranscendenceBasis_subset
  proof: by
  simp_rw [← matroid_spanning_iff, ← matroid_isBase_iff, and_comm (a := _ subseteq s)]
  exact Matroid.spanning_iff_exists_isBase_subset (subset_univ _)

中文:
定理 isAlgebraic_iff_存在_isTranscendenceBasis_subset
  证明: by
  simp_rw [← matroid_spanning_iff, ← matroid_isBase_iff, and_comm (a := _ subseteq s)]
  exact Matroid.spanning_iff_exists_isBase_subset (subset_univ _)

Depends on / 依赖: Matroid, Matroid.spanning_iff_exists_isBase_subset, and_comm, matroid_isBase_iff, matroid_spanning_iff, simp_rw, spanning_iff_exists_isBase_subset, subset_univ, subseteq
-/
theorem isAlgebraic_iff_exists_isTranscendenceBasis_subset
    [IsDomain A] [FaithfulSMul R A] {s : Set A} :
    Algebra.IsAlgebraic (adjoin R s) A ↔ exists t, t subseteq s ∧ IsTranscendenceBasis R ((↑) : t -> A) := by
  simp_rw [← matroid_spanning_iff, ← matroid_isBase_iff, and_comm (a := _ subseteq s)]
  exact Matroid.spanning_iff_exists_isBase_subset (subset_univ _)

open Cardinal AlgebraicIndependent

namespace IsTranscendenceBasis

variable [Nontrivial R] [NoZeroDivisors A]

/--
theorem `lift_cardinalMk_eq_trdeg` / 定理 `lift_cardinalMk_eq_trdeg`

English:
theorem lift_cardinalMk_eq_trdeg
  given: (hx : IsTranscendenceBasis R x)
  proof: by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.1.algebraMap_injective
  rw [← matroid_cRank_eq]; rw [← (matroid_isBase_iff.mpr hx.to_subtype_range).cardinalMk_eq_cRank]; rw [lift_mk_eq'.mpr ⟨.ofInjective _ hx.1.injective⟩]

中文:
定理 lift_cardinalMk_eq_trdeg
  条件: (hx : IsTranscendenceBasis R x)
  证明: by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.1.algebraMap_injective
  rw [← matroid_cRank_eq]; rw [← (matroid_isBase_iff.mpr hx.to_subtype_range).cardinalMk_eq_cRank]; rw [lift_mk_eq'.mpr ⟨.ofInjective _ hx.1.injective⟩]

Depends on / 依赖: algebraMap_injective, cardinalMk_eq_cRank, faithfulSMul_iff_algebraMap_injective, hx.to_subtype_range, injective, lift_mk_eq, matroid_cRank_eq, matroid_isBase_iff, matroid_isBase_iff.mpr, ofInjective, to_subtype_range
-/
theorem lift_cardinalMk_eq_trdeg (hx : IsTranscendenceBasis R x) :
    lift.{w} #ι = lift.{u} (trdeg R A) := by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.1.algebraMap_injective
  rw [← matroid_cRank_eq]; rw [← (matroid_isBase_iff.mpr hx.to_subtype_range).cardinalMk_eq_cRank]; rw [lift_mk_eq'.mpr ⟨.ofInjective _ hx.1.injective⟩]

/--
theorem `cardinalMk_eq_trdeg` / 定理 `cardinalMk_eq_trdeg`

English:
theorem cardinalMk_eq_trdeg
  given: {ι : Type w} {x : ι -> A} (hx : IsTranscendenceBasis R x)
  proof: by
  rw [← lift_id #ι]; rw [lift_cardinalMk_eq_trdeg hx]; rw [lift_id]

中文:
定理 cardinalMk_eq_trdeg
  条件: {ι : 类型 w} {x : ι -> A} (hx : IsTranscendenceBasis R x)
  证明: by
  rw [← lift_id #ι]; rw [lift_cardinalMk_eq_trdeg hx]; rw [lift_id]

Depends on / 依赖: lift_cardinalMk_eq_trdeg, lift_id
-/
theorem cardinalMk_eq_trdeg {ι : Type w} {x : ι -> A} (hx : IsTranscendenceBasis R x) :
    #ι = trdeg R A := by
  rw [← lift_id #ι]; rw [lift_cardinalMk_eq_trdeg hx]; rw [lift_id]

/-- Any two transcendence bases of a domain `A` have the same cardinality.
May fail if `A` is not a domain; see https://mathoverflow.net/a/144580. -/
@[stacks 030F]
/--
theorem `lift_cardinalMk_eq` / 定理 `lift_cardinalMk_eq`

English:
theorem lift_cardinalMk_eq
  given: (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y)
  proof: by
  rw [← lift_inj.{_]; rw [w}]; rw [lift_lift]; rw [lift_lift]; rw [← lift_lift.{w]; rw [u'}]; rw [hx.lift_cardinalMk_eq_trdeg]; rw [← lift_lift.{w]; rw [u}]; rw [hy.lift_cardinalMk_eq_trdeg]; rw [lift_lift]; rw [lift_lift]

中文:
定理 lift_cardinalMk_eq
  条件: (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y)
  证明: by
  rw [← lift_inj.{_]; rw [w}]; rw [lift_lift]; rw [lift_lift]; rw [← lift_lift.{w]; rw [u'}]; rw [hx.lift_cardinalMk_eq_trdeg]; rw [← lift_lift.{w]; rw [u}]; rw [hy.lift_cardinalMk_eq_trdeg]; rw [lift_lift]; rw [lift_lift]

Depends on / 依赖: hx.lift_cardinalMk_eq_trdeg, hy.lift_cardinalMk_eq_trdeg, lift_cardinalMk_eq_trdeg, lift_inj, lift_lift
-/
theorem lift_cardinalMk_eq (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    lift.{u'} #ι = lift.{u} #ι' := by
  rw [← lift_inj.{_]; rw [w}]; rw [lift_lift]; rw [lift_lift]; rw [← lift_lift.{w]; rw [u'}]; rw [hx.lift_cardinalMk_eq_trdeg]; rw [← lift_lift.{w]; rw [u}]; rw [hy.lift_cardinalMk_eq_trdeg]; rw [lift_lift]; rw [lift_lift]

/--
theorem `cardinalMk_eq` / 定理 `cardinalMk_eq`

English:
theorem cardinalMk_eq
  statement: {ι' : Type u} {y : ι' -> A}
  proof: by
  rw [← lift_id #ι]; rw [lift_cardinalMk_eq hx hy]; rw [lift_id]

中文:
定理 cardinalMk_eq
  结论: {ι' : 类型u} {y : ι' -> A}
  证明: by
  rw [← lift_id #ι]; rw [lift_cardinalMk_eq hx hy]; rw [lift_id]
-/
@[stacks 030F] theorem cardinalMk_eq {ι' : Type u} {y : ι' -> A}
    (hx : IsTranscendenceBasis R x) (hy : IsTranscendenceBasis R y) :
    #ι = #ι' := by
  rw [← lift_id #ι]; rw [lift_cardinalMk_eq hx hy]; rw [lift_id]

end IsTranscendenceBasis

-- TODO: generalize to Nontrivial S
@[simp]
/--
theorem `MvPolynomial.trdeg_of_isDomain` / 定理 `MvPolynomial.trdeg_of_isDomain`

English:
theorem MvPolynomial.trdeg_of_isDomain
  given: [IsDomain S]
  statement: trdeg S (MvPolynomial ι S) = lift.{v} #ι
  proof: by
  have := (IsTranscendenceBasis.mvPolynomial ι S).lift_cardinalMk_eq_trdeg.symm
  rwa [lift_id', ← lift_lift.{u}, lift_id] at this

中文:
定理 多元多项式.trdeg_of_isDomain
  条件: [是整环 S]
  结论: trdeg S (多元多项式 ι S) = lift.{v} #ι
  证明: by
  have := (IsTranscendenceBasis.mvPolynomial ι S).lift_cardinalMk_eq_trdeg.symm
  rwa [lift_id', ← lift_lift.{u}, lift_id] at this

Depends on / 依赖: IsTranscendenceBasis, IsTranscendenceBasis.mvPolynomial, lift_cardinalMk_eq_trdeg, lift_cardinalMk_eq_trdeg.symm, lift_id, lift_lift, mvPolynomial
-/
theorem MvPolynomial.trdeg_of_isDomain [IsDomain S] : trdeg S (MvPolynomial ι S) = lift.{v} #ι := by
  have := (IsTranscendenceBasis.mvPolynomial ι S).lift_cardinalMk_eq_trdeg.symm
  rwa [lift_id', ← lift_lift.{u}, lift_id] at this

-- TODO: generalize to Nontrivial R
@[simp]
/--
theorem `Polynomial.trdeg_of_isDomain` / 定理 `Polynomial.trdeg_of_isDomain`

English:
theorem Polynomial.trdeg_of_isDomain
  given: [IsDomain R]
  statement: trdeg R (Polynomial R) = 1
  proof: by
  simpa using (IsTranscendenceBasis.polynomial Unit R).lift_cardinalMk_eq_trdeg.symm

中文:
定理 多项式.trdeg_of_isDomain
  条件: [是整环 R]
  结论: trdeg R (多项式 R) = 1
  证明: by
  simpa using (IsTranscendenceBasis.polynomial Unit R).lift_cardinalMk_eq_trdeg.symm

Depends on / 依赖: IsTranscendenceBasis, IsTranscendenceBasis.polynomial, lift_cardinalMk_eq_trdeg, lift_cardinalMk_eq_trdeg.symm, polynomial
-/
theorem Polynomial.trdeg_of_isDomain [IsDomain R] : trdeg R (Polynomial R) = 1 := by
  simpa using (IsTranscendenceBasis.polynomial Unit R).lift_cardinalMk_eq_trdeg.symm

-- TODO: generalize to Nontrivial S
/--
theorem `trdeg_lt_aleph0_of_finiteType` / 定理 `trdeg_lt_aleph0_of_finiteType`

English:
theorem trdeg_lt_aleph0_of_finiteType
  given: [IsDomain R] [fin : FiniteType R S]
  statement: trdeg R S < ℵ₀
  proof: have ⟨n, f, surj⟩ := FiniteType.iff_quotient_mvPolynomial''.mp fin
lift_lt.mp (lift_trdeg_le_of_surjective f surj).trans_lt by simp

中文:
定理 trdeg_lt_aleph0_of_finiteType
  条件: [是整环 R] [fin : 有限型 R S]
  结论: trdeg R S < ℵ₀
  证明: have ⟨n, f, surj⟩ := FiniteType.iff_quotient_mvPolynomial''.mp fin
lift_lt.mp (lift_trdeg_le_of_surjective f surj).trans_lt by simp

Depends on / 依赖: FiniteType, FiniteType.iff_quotient_mvPolynomial, iff_quotient_mvPolynomial, lift_lt, lift_lt.mp, lift_trdeg_le_of_surjective, trans_lt
-/
theorem trdeg_lt_aleph0_of_finiteType [IsDomain R] [fin : FiniteType R S] : trdeg R S < ℵ₀ :=
  have ⟨n, f, surj⟩ := FiniteType.iff_quotient_mvPolynomial''.mp fin
lift_lt.mp (lift_trdeg_le_of_surjective f surj).trans_lt by simp

namespace Algebra.IsAlgebraic

variable (R x) (s : Set A)

variable [NoZeroDivisors A]

/--
lemma `isDomain_of_adjoin_range` / 引理 `isDomain_of_adjoin_range`

English:
lemma isDomain_of_adjoin_range
  given: [Algebra.IsAlgebraic (adjoin R s) A]
  statement: IsDomain A
  proof: have := Algebra.IsAlgebraic.nontrivial (adjoin R s) A
  (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    ⟨‹_›, (Subtype.val_injective (p := (· in adjoin R s))).nontrivial⟩

中文:
引理 isDomain_of_adjoin_range
  条件: [代数.是代数 (adjoin R s) A]
  结论: 是整环 A
  证明: have := Algebra.IsAlgebraic.nontrivial (adjoin R s) A
  (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    ⟨‹_›, (Subtype.val_injective (p := (· in adjoin R s))).nontrivial⟩

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.nontrivial, IsAlgebraic, Subtype, Subtype.val_injective, adjoin, isDomain_iff_noZeroDivisors_and_nontrivial, nontrivial, val_injective
-/
lemma isDomain_of_adjoin_range [Algebra.IsAlgebraic (adjoin R s) A] : IsDomain A :=
  have := Algebra.IsAlgebraic.nontrivial (adjoin R s) A
  (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr
    ⟨‹_›, (Subtype.val_injective (p := (· in adjoin R s))).nontrivial⟩

/--
theorem `trdeg_le_cardinalMk` / 定理 `trdeg_le_cardinalMk`

English:
theorem trdeg_le_cardinalMk
  given: [alg : Algebra.IsAlgebraic (adjoin R s) A]
  statement: trdeg R A <= #s
  proof: by
  by_cases h : Injective (algebraMap R A)
  on_goal 2 => simp [trdeg_eq_zero_of_not_injective h]
  have := isDomain_of_adjoin_range R s
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr h
  rw [← matroid_spanning_iff]; rw [← matroid_cRank_eq] at *
  exact alg.cRank_le_cardinalMk

中文:
定理 trdeg_le_cardinalMk
  条件: [alg : 代数.是代数 (adjoin R s) A]
  结论: trdeg R A <= #s
  证明: by
  by_cases h : Injective (algebraMap R A)
  on_goal 2 => simp [trdeg_eq_zero_of_not_injective h]
  have := isDomain_of_adjoin_range R s
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr h
  rw [← matroid_spanning_iff]; rw [← matroid_cRank_eq] at *
  exact alg.cRank_le_cardinalMk

Depends on / 依赖: Injective, alg.cRank_le_cardinalMk, algebraMap, cRank_le_cardinalMk, faithfulSMul_iff_algebraMap_injective, isDomain_of_adjoin_range, matroid_cRank_eq, matroid_spanning_iff, on_goal, trdeg_eq_zero_of_not_injective
-/
theorem trdeg_le_cardinalMk [alg : Algebra.IsAlgebraic (adjoin R s) A] : trdeg R A <= #s := by
  by_cases h : Injective (algebraMap R A)
  on_goal 2 => simp [trdeg_eq_zero_of_not_injective h]
  have := isDomain_of_adjoin_range R s
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr h
  rw [← matroid_spanning_iff]; rw [← matroid_cRank_eq] at *
  exact alg.cRank_le_cardinalMk

variable [FaithfulSMul R A]

/--
theorem `isTranscendenceBasis_of_lift_le_trdeg_of_finite` / 定理 `isTranscendenceBasis_of_lift_le_trdeg_of_finite`

English:
theorem isTranscendenceBasis_of_lift_le_trdeg_of_finite
  proof: by
  have ⟨_, h⟩ := lift_mk_le'.mp (le.trans <| lift_le.mpr <| trdeg_le_cardinalMk R (range x))
  have := rangeFactorization_surjective.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ h)
  refine .of_subtype_range (fun _ _ => (this.1 <| Subtype.ext ·)) ?_
  have := isDomain_of_adjoin_range

中文:
定理 isTranscendenceBasis_of_lift_le_trdeg_of_finite
  证明: by
  have ⟨_, h⟩ := lift_mk_le'.mp (le.trans <| lift_le.mpr <| trdeg_le_cardinalMk R (range x))
  have := rangeFactorization_surjective.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ h)
  refine .of_subtype_range (fun _ _ => (this.1 <| Subtype.ext ·)) ?_
  have := isDomain_of_adjoin_range

Depends on / 依赖: Nat.card_le_card_of_injective, Subtype, Subtype.ext, alg.isBase_of_le_cRank_of_finite, bijective_of_nat_card_le, card_le_card_of_injective, finite_range, isBase_of_le_cRank_of_finite, isDomain_of_adjoin_range, le.trans, lift_le, lift_le.mp, lift_le.mpr, lift_mk_le, matroid_cRank_eq, matroid_spanning_iff, mk_range_le_lift, mk_range_le_lift.trans, of_subtype_range, rangeFactorization_surjective
-/
theorem isTranscendenceBasis_of_lift_le_trdeg_of_finite
    [Finite ι] [alg : Algebra.IsAlgebraic (adjoin R (range x)) A]
    (le : lift.{w} #ι <= lift.{u} (trdeg R A)) : IsTranscendenceBasis R x := by
  have ⟨_, h⟩ := lift_mk_le'.mp (le.trans <| lift_le.mpr <| trdeg_le_cardinalMk R (range x))
  have := rangeFactorization_surjective.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ h)
  refine .of_subtype_range (fun _ _ => (this.1 <| Subtype.ext ·)) ?_
  have := isDomain_of_adjoin_range R (range x)
  rw [← matroid_spanning_iff]; rw [← matroid_cRank_eq] at *
  exact alg.isBase_of_le_cRank_of_finite (lift_le.mp <| mk_range_le_lift.trans le) (finite_range x)

/--
theorem `isTranscendenceBasis_of_le_trdeg_of_finite` / 定理 `isTranscendenceBasis_of_le_trdeg_of_finite`

English:
theorem isTranscendenceBasis_of_le_trdeg_of_finite
  statement: {ι : Type w} [Finite ι] (x : ι -> A)
  proof: isTranscendenceBasis_of_lift_le_trdeg_of_finite R x (by rwa [lift_id, lift_id])

中文:
定理 isTranscendenceBasis_of_le_trdeg_of_finite
  结论: {ι : 类型 w} [有限 ι] (x : ι -> A)
  证明: isTranscendenceBasis_of_lift_le_trdeg_of_finite R x (by rwa [lift_id, lift_id])

Depends on / 依赖: isTranscendenceBasis_of_lift_le_trdeg_of_finite, lift_id
-/
theorem isTranscendenceBasis_of_le_trdeg_of_finite {ι : Type w} [Finite ι] (x : ι -> A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] (le : #ι <= trdeg R A) :
    IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x (by rwa [lift_id, lift_id])

/--
theorem `isTranscendenceBasis_of_lift_le_trdeg` / 定理 `isTranscendenceBasis_of_lift_le_trdeg`

English:
theorem isTranscendenceBasis_of_lift_le_trdeg
  statement: [Algebra.IsAlgebraic (adjoin R (range x)) A]
  proof: have := mk_lt_aleph0_iff.mp (lift_lt.mp <| le.trans_lt <| (lift_lt.mpr fin).trans_eq <| by simp)
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x le

中文:
定理 isTranscendenceBasis_of_lift_le_trdeg
  结论: [代数.是代数 (adjoin R (range x)) A]
  证明: have := mk_lt_aleph0_iff.mp (lift_lt.mp <| le.trans_lt <| (lift_lt.mpr fin).trans_eq <| by simp)
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x le

Depends on / 依赖: isTranscendenceBasis_of_lift_le_trdeg_of_finite, le.trans_lt, lift_lt, lift_lt.mp, lift_lt.mpr, mk_lt_aleph0_iff, mk_lt_aleph0_iff.mp, trans_eq, trans_lt
-/
theorem isTranscendenceBasis_of_lift_le_trdeg [Algebra.IsAlgebraic (adjoin R (range x)) A]
    (fin : trdeg R A < ℵ₀) (le : lift.{w} #ι <= lift.{u} (trdeg R A)) :
    IsTranscendenceBasis R x :=
  have := mk_lt_aleph0_iff.mp (lift_lt.mp <| le.trans_lt <| (lift_lt.mpr fin).trans_eq <| by simp)
  isTranscendenceBasis_of_lift_le_trdeg_of_finite R x le

/--
theorem `isTranscendenceBasis_of_le_trdeg` / 定理 `isTranscendenceBasis_of_le_trdeg`

English:
theorem isTranscendenceBasis_of_le_trdeg
  statement: {ι : Type w} (x : ι -> A)
  proof: isTranscendenceBasis_of_lift_le_trdeg R x fin (by rwa [lift_id, lift_id])

中文:
定理 isTranscendenceBasis_of_le_trdeg
  结论: {ι : 类型 w} (x : ι -> A)
  证明: isTranscendenceBasis_of_lift_le_trdeg R x fin (by rwa [lift_id, lift_id])

Depends on / 依赖: isTranscendenceBasis_of_lift_le_trdeg, lift_id
-/
theorem isTranscendenceBasis_of_le_trdeg {ι : Type w} (x : ι -> A)
    [Algebra.IsAlgebraic (adjoin R (range x)) A] (fin : trdeg R A < ℵ₀)
    (le : #ι <= trdeg R A) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_le_trdeg R x fin (by rwa [lift_id, lift_id])

end Algebra.IsAlgebraic

namespace AlgebraicIndependent

variable [Nontrivial R] [NoZeroDivisors A]

/--
theorem `isTranscendenceBasis_of_lift_trdeg_le` / 定理 `isTranscendenceBasis_of_lift_trdeg_le`

English:
theorem isTranscendenceBasis_of_lift_trdeg_le
  statement: (hx : AlgebraicIndependent R x)
  proof: by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.algebraMap_injective
  rw [← matroid_cRank_eq]; rw [← Matroid.rankFinite_iff_cRank_lt_aleph0] at fin
exact .of_subtype_range hx.injective matroid_indep_iff.mpr hx.to_subtype_range
.isBase_of_cRank_le lift_le.mp (matroid_cRank_eq R A ▸ l

中文:
定理 isTranscendenceBasis_of_lift_trdeg_le
  结论: (hx : AlgebraicIndependent R x)
  证明: by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.algebraMap_injective
  rw [← matroid_cRank_eq]; rw [← Matroid.rankFinite_iff_cRank_lt_aleph0] at fin
exact .of_subtype_range hx.injective matroid_indep_iff.mpr hx.to_subtype_range
.isBase_of_cRank_le lift_le.mp (matroid_cRank_eq R A ▸ l

Depends on / 依赖: Matroid, Matroid.rankFinite_iff_cRank_lt_aleph0, algebraMap_injective, faithfulSMul_iff_algebraMap_injective, hx.algebraMap_injective, hx.injective, hx.to_subtype_range, injective, isBase_of_cRank_le, lift_le, lift_le.mp, matroid_cRank_eq, matroid_indep_iff, matroid_indep_iff.mpr, mk_range_eq_of_injective, of_subtype_range, rankFinite_iff_cRank_lt_aleph0, to_subtype_range, trans_eq
-/
theorem isTranscendenceBasis_of_lift_trdeg_le (hx : AlgebraicIndependent R x)
    (fin : trdeg R A < ℵ₀) (le : lift.{u} (trdeg R A) <= lift.{w} #ι) :
    IsTranscendenceBasis R x := by
  have := (faithfulSMul_iff_algebraMap_injective R A).mpr hx.algebraMap_injective
  rw [← matroid_cRank_eq]; rw [← Matroid.rankFinite_iff_cRank_lt_aleph0] at fin
exact .of_subtype_range hx.injective matroid_indep_iff.mpr hx.to_subtype_range
.isBase_of_cRank_le lift_le.mp (matroid_cRank_eq R A ▸ le).trans_eq
      (mk_range_eq_of_injective hx.injective).symm

/--
theorem `isTranscendenceBasis_of_trdeg_le` / 定理 `isTranscendenceBasis_of_trdeg_le`

English:
theorem isTranscendenceBasis_of_trdeg_le
  statement: {ι : Type w} {x : ι -> A} (hx : AlgebraicIndependent R x)
  proof: isTranscendenceBasis_of_lift_trdeg_le hx fin (by rwa [lift_id, lift_id])

中文:
定理 isTranscendenceBasis_of_trdeg_le
  结论: {ι : 类型 w} {x : ι -> A} (hx : AlgebraicIndependent R x)
  证明: isTranscendenceBasis_of_lift_trdeg_le hx fin (by rwa [lift_id, lift_id])

Depends on / 依赖: isTranscendenceBasis_of_lift_trdeg_le, lift_id
-/
theorem isTranscendenceBasis_of_trdeg_le {ι : Type w} {x : ι -> A} (hx : AlgebraicIndependent R x)
    (fin : trdeg R A < ℵ₀) (le : trdeg R A <= #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le hx fin (by rwa [lift_id, lift_id])

/--
theorem `isTranscendenceBasis_of_lift_trdeg_le_of_finite` / 定理 `isTranscendenceBasis_of_lift_trdeg_le_of_finite`

English:
theorem isTranscendenceBasis_of_lift_trdeg_le_of_finite
  statement: [Finite ι] (hx : AlgebraicIndependent R x)
  proof: isTranscendenceBasis_of_lift_trdeg_le hx
    (lift_lt.mp <| le.trans_lt <| by simp) le

中文:
定理 isTranscendenceBasis_of_lift_trdeg_le_of_finite
  结论: [有限 ι] (hx : AlgebraicIndependent R x)
  证明: isTranscendenceBasis_of_lift_trdeg_le hx
    (lift_lt.mp <| le.trans_lt <| by simp) le

Depends on / 依赖: isTranscendenceBasis_of_lift_trdeg_le, le.trans_lt, lift_lt, lift_lt.mp, trans_lt
-/
theorem isTranscendenceBasis_of_lift_trdeg_le_of_finite [Finite ι] (hx : AlgebraicIndependent R x)
    (le : lift.{u} (trdeg R A) <= lift.{w} #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le hx
    (lift_lt.mp <| le.trans_lt <| by simp) le

/--
theorem `isTranscendenceBasis_of_trdeg_le_of_finite` / 定理 `isTranscendenceBasis_of_trdeg_le_of_finite`

English:
theorem isTranscendenceBasis_of_trdeg_le_of_finite
  statement: {ι : Type w} [Finite ι] {x : ι -> A}
  proof: isTranscendenceBasis_of_lift_trdeg_le_of_finite hx (by rwa [lift_id, lift_id])

中文:
定理 isTranscendenceBasis_of_trdeg_le_of_finite
  结论: {ι : 类型 w} [有限 ι] {x : ι -> A}
  证明: isTranscendenceBasis_of_lift_trdeg_le_of_finite hx (by rwa [lift_id, lift_id])

Depends on / 依赖: isTranscendenceBasis_of_lift_trdeg_le_of_finite, lift_id
-/
theorem isTranscendenceBasis_of_trdeg_le_of_finite {ι : Type w} [Finite ι] {x : ι -> A}
    (hx : AlgebraicIndependent R x) (le : trdeg R A <= #ι) : IsTranscendenceBasis R x :=
  isTranscendenceBasis_of_lift_trdeg_le_of_finite hx (by rwa [lift_id, lift_id])

end AlgebraicIndependent

variable (R S A)

/--
theorem `lift_trdeg_add_eq` / 定理 `lift_trdeg_add_eq`

English:
theorem lift_trdeg_add_eq
  statement: [Nontrivial R] [NoZeroDivisors A] [FaithfulSMul R S]
  proof: by
  have ⟨s, hs⟩ := exists_isTranscendenceBasis R S
  have ⟨t, ht⟩ := exists_isTranscendenceBasis S A
  have := (FaithfulSMul.algebraMap_injective S A).noZeroDivisors _ (map_zero _) (map_mul _)
  have := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← hs.cardinalMk_eq_trdeg]; rw [← ht.ca

中文:
定理 lift_trdeg_add_eq
  结论: [非平凡 R] [无零因子 A] [忠实标量乘法 R S]
  证明: by
  have ⟨s, hs⟩ := exists_isTranscendenceBasis R S
  have ⟨t, ht⟩ := exists_isTranscendenceBasis S A
  have := (FaithfulSMul.algebraMap_injective S A).noZeroDivisors _ (map_zero _) (map_mul _)
  have := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← hs.cardinalMk_eq_trdeg]; rw [← ht.ca
-/
@[stacks 030H] theorem lift_trdeg_add_eq [Nontrivial R] [NoZeroDivisors A] [FaithfulSMul R S]
    [FaithfulSMul S A] : lift.{w} (trdeg R S) + lift.{v} (trdeg S A) = lift.{v} (trdeg R A) := by
  have ⟨s, hs⟩ := exists_isTranscendenceBasis R S
  have ⟨t, ht⟩ := exists_isTranscendenceBasis S A
  have := (FaithfulSMul.algebraMap_injective S A).noZeroDivisors _ (map_zero _) (map_mul _)
  have := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← hs.cardinalMk_eq_trdeg]; rw [← ht.cardinalMk_eq_trdeg]; rw [← lift_umax.{w}]; rw [add_comm]; rw [← (hs.sumElim_comp ht).lift_cardinalMk_eq_trdeg]; rw [mk_sum]; rw [lift_add]; rw [lift_lift]; rw [lift_lift]

/--
theorem `trdeg_add_eq` / 定理 `trdeg_add_eq`

English:
theorem trdeg_add_eq
  statement: [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
  proof: by
  rw [← (trdeg R S).lift_id]; rw [← (trdeg S A).lift_id]; rw [← (trdeg R A).lift_id]
  exact lift_trdeg_add_eq R S A

中文:
定理 trdeg_add_eq
  结论: [非平凡 R] {A : 类型v} [交换环 A] [无零因子 A]
  证明: by
  rw [← (trdeg R S).lift_id]; rw [← (trdeg S A).lift_id]; rw [← (trdeg R A).lift_id]
  exact lift_trdeg_add_eq R S A
-/
@[stacks 030H] theorem trdeg_add_eq [Nontrivial R] {A : Type v} [CommRing A] [NoZeroDivisors A]
    [Algebra R A] [Algebra S A] [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
    trdeg R S + trdeg S A = trdeg R A := by
  rw [← (trdeg R S).lift_id]; rw [← (trdeg S A).lift_id]; rw [← (trdeg R A).lift_id]
  exact lift_trdeg_add_eq R S A

namespace IsTranscendenceBasis

variable {R S} [FaithfulSMul R S] [NoZeroDivisors S] (s : Set ι) (i j : ι) (v : ι -> S)

/--
lemma `of_isAlgebraic_adjoin_insert_sdiff` / 引理 `of_isAlgebraic_adjoin_insert_sdiff`

English:
lemma of_isAlgebraic_adjoin_insert_sdiff
  statement: (hj : j in insert i s)
  proof: by
  have := H₂.nontrivial
  have := (adjoin R (v '' (insert i s \ {j}))).subtype_injective.nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial S).mpr ⟨‹_›, ‹_›⟩
  have := Module.nontrivial R S
  rw [← mem_algebraicClosure]; rw [← SetLike.mem_coe]; rw [← matroid_closure_eq] at H₂
  have

中文:
引理 of_isAlgebraic_adjoin_insert_sdiff
  结论: (hj : j in insert i s)
  证明: by
  have := H₂.nontrivial
  have := (adjoin R (v '' (insert i s \ {j}))).subtype_injective.nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial S).mpr ⟨‹_›, ‹_›⟩
  have := Module.nontrivial R S
  rw [← mem_algebraicClosure]; rw [← SetLike.mem_coe]; rw [← matroid_closure_eq] at H₂
  have

Depends on / 依赖: Module, Module.nontrivial, SetLike, SetLike.mem_coe, adjoin, hj.resolve_right, image_eq_range, injOn_iff_injective, injOn_iff_injective.mpr, injective, insert, insert_sdiff_self_, isDomain_iff_noZeroDivisors_and_nontrivial, matroid_closure_eq, matroid_isBase_iff, matroid_isBase_iff.mpr, mem_algebraicClosure, mem_coe, nontrivial, resolve_right
-/
lemma of_isAlgebraic_adjoin_insert_sdiff (hj : j in insert i s)
    (H₁ : IsTranscendenceBasis R fun x : s => v x)
    (H₂ : IsAlgebraic (Algebra.adjoin R (v '' (insert i s \ {j}))) (v j)) :
    IsTranscendenceBasis R fun x : ↥(insert i s \ {j}) => v x := by
  have := H₂.nontrivial
  have := (adjoin R (v '' (insert i s \ {j}))).subtype_injective.nontrivial
  have := (isDomain_iff_noZeroDivisors_and_nontrivial S).mpr ⟨‹_›, ‹_›⟩
  have := Module.nontrivial R S
  rw [← mem_algebraicClosure]; rw [← SetLike.mem_coe]; rw [← matroid_closure_eq] at H₂
  have inj := injOn_iff_injective.mpr H₁.1.injective
  have H' := image_eq_range .. ▸ matroid_isBase_iff.mpr H₁.to_subtype_range
  obtain hj' | hj := (em (j in s)).symm
  · cases hj.resolve_right hj'; rwa [insert_sdiff_self_of_notMem hj']
  have Hj := H'.indep.notMem_closure_sdiff_of_mem ⟨j, hj, rfl⟩
have hi : i ∉ s := fun hi => Hj by
    rw [← image_singleton]; rw [← inj.image_sdiff_subset (singleton_subset_iff.mpr hj)]
    rwa [insert_eq_of_mem hi] at H₂
  obtain eq | ne := eq_or_ne (v i) (v j)
  · classical
    convert!
H₁.comp_equiv
.symm
((Equiv.swap j i).image s).trans
.setCongr Equiv.image_swap_of_mem_of_notMem hj hi with
      ⟨x, rfl | hxi, hxj⟩
    · simp [eq]
    · simp [Equiv.swap_apply_of_ne_of_ne hxj (ne_of_mem_of_not_mem hxi hi)]
have hi' : v i ∉ v '' s := fun his => Hj by
    refine Matroid.closure_subset_closure _ ?_ H₂
    rintro x ⟨k, ⟨rfl | hks, hkj⟩, rfl⟩
    · exact ⟨his, ne⟩
    · exact ⟨⟨k, hks, rfl⟩, inj.ne hks hj hkj⟩
  have : (insert i s).InjOn v := (injOn_insert hi).mpr ⟨inj, hi'⟩
  rw [← isTranscendenceBasis_subtype_range
    (by exact injOn_iff_injective.1 (this.mono sdiff_subset))]; rw [← matroid_isBase_iff]; rw [← image_eq_range]
  rw [this.image_sdiff_subset (singleton_subset_iff.mpr (.inr hj))]; rw [image_singleton]; rw [image_insert_eq] at H₂ ⊢
  exact H'.isBase_insert_sdiff_of_mem_closure H₂ (.inr ⟨j, hj, rfl⟩)

@[deprecated (since := "2026-06-03")]
alias of_isAlgebraic_adjoin_insert_diff := of_isAlgebraic_adjoin_insert_sdiff

/--
lemma `of_isAlgebraic_adjoin_image_compl` / 引理 `of_isAlgebraic_adjoin_image_compl`

English:
lemma of_isAlgebraic_adjoin_image_compl
  proof: by
  obtain rfl | ne := eq_or_ne j i
  · exact H₁
  have := H₁.of_isAlgebraic_adjoin_insert_sdiff {i}ᶜ i j v (.inr ne)
  rw [compl_eq_univ_sdiff]; rw [insert_sdiff_self_of_mem (mem_univ _)]; rw [← compl_eq_univ_sdiff] at this
  exact this H₂

中文:
引理 of_isAlgebraic_adjoin_image_compl
  证明: by
  obtain rfl | ne := eq_or_ne j i
  · exact H₁
  have := H₁.of_isAlgebraic_adjoin_insert_sdiff {i}ᶜ i j v (.inr ne)
  rw [compl_eq_univ_sdiff]; rw [insert_sdiff_self_of_mem (mem_univ _)]; rw [← compl_eq_univ_sdiff] at this
  exact this H₂

Depends on / 依赖: compl_eq_univ_sdiff, eq_or_ne, insert_sdiff_self_of_mem, mem_univ, of_isAlgebraic_adjoin_insert_sdiff
-/
lemma of_isAlgebraic_adjoin_image_compl
    (H₁ : IsTranscendenceBasis R fun x : {x // x != i} => v x)
    (H₂ : IsAlgebraic (Algebra.adjoin R (v '' {j}ᶜ)) (v j)) :
    IsTranscendenceBasis R fun x : {x // x != j} => v x := by
  obtain rfl | ne := eq_or_ne j i
  · exact H₁
  have := H₁.of_isAlgebraic_adjoin_insert_sdiff {i}ᶜ i j v (.inr ne)
  rw [compl_eq_univ_sdiff]; rw [insert_sdiff_self_of_mem (mem_univ _)]; rw [← compl_eq_univ_sdiff] at this
  exact this H₂

end IsTranscendenceBasis
