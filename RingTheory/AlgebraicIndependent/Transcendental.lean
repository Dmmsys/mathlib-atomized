/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.RingTheory.Algebraic.MvPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebraic Independence

This file relates algebraic independence and transcendence (or algebraicity) of elements.

## References

* [Stacks: Transcendence](https://stacks.math.columbia.edu/tag/030D)

## Tags
transcendence

-/

public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

universe u v

variable {ι ι' R : Type*} {S : Type u} {A : Type v} {x : ι -> A}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

/-- A one-element family `x` is algebraically independent if and only if
its element is transcendental. -/
@[simp]
/--
theorem `algebraicIndependent_unique_type_iff` / 定理 `algebraicIndependent_unique_type_iff`

English:
theorem algebraicIndependent_unique_type_iff
  given: [Unique ι]
  proof: by
  rw [transcendental_iff_injective]; rw [algebraicIndependent_iff_injective_aeval]
  let i := uniqueAlgEquiv R ι
  have key : aeval (R := R) x = (Polynomial.aeval (R := R) (x default)).comp i := by
    ext y
    simp [i, Subsingleton.elim y default]
  simp [key]

中文:
定理 algebraicIndependent_unique_type_iff
  条件: [Unique ι]
  证明: by
  rw [transcendental_iff_injective]; rw [algebraicIndependent_iff_injective_aeval]
  let i := uniqueAlgEquiv R ι
  have key : aeval (R := R) x = (Polynomial.aeval (R := R) (x default)).comp i := by
    ext y
    simp [i, Subsingleton.elim y default]
  simp [key]

Depends on / 依赖: Polynomial, Polynomial.aeval, Subsingleton, Subsingleton.elim, algebraicIndependent_iff_injective_aeval, transcendental_iff_injective, uniqueAlgEquiv
-/
theorem algebraicIndependent_unique_type_iff [Unique ι] :
    AlgebraicIndependent R x ↔ Transcendental R (x default) := by
  rw [transcendental_iff_injective]; rw [algebraicIndependent_iff_injective_aeval]
  let i := uniqueAlgEquiv R ι
  have key : aeval (R := R) x = (Polynomial.aeval (R := R) (x default)).comp i := by
    ext y
    simp [i, Subsingleton.elim y default]
  simp [key]

/--
theorem `algebraicIndependent_singleton_iff` / 定理 `algebraicIndependent_singleton_iff`

English:
theorem algebraicIndependent_singleton_iff
  given: [Subsingleton ι] (i : ι)
  proof: letI := uniqueOfSubsingleton i
  algebraicIndependent_unique_type_iff

中文:
定理 algebraicIndependent_singleton_iff
  条件: [Subsingleton ι] (i : ι)
  证明: letI := uniqueOfSubsingleton i
  algebraicIndependent_unique_type_iff

Depends on / 依赖: algebraicIndependent_unique_type_iff, uniqueOfSubsingleton
-/
theorem algebraicIndependent_singleton_iff [Subsingleton ι] (i : ι) :
    AlgebraicIndependent R x ↔ Transcendental R (x i) :=
  letI := uniqueOfSubsingleton i
  algebraicIndependent_unique_type_iff

/--
theorem `algebraicIndependent_iff_transcendental` / 定理 `algebraicIndependent_iff_transcendental`

English:
theorem algebraicIndependent_iff_transcendental
  given: {x : A}
  proof: by
  simp

中文:
定理 algebraicIndependent_iff_transcendental
  条件: {x : A}
  证明: by
  simp
-/
theorem algebraicIndependent_iff_transcendental {x : A} :
    AlgebraicIndependent R ![x] ↔ Transcendental R x := by
  simp

namespace AlgebraicIndependent

variable (hx : AlgebraicIndependent R x)
include hx

/--
theorem `transcendental` / 定理 `transcendental`

English:
theorem transcendental
  given: (i : ι)
  statement: Transcendental R (x i)
  proof: by
  have := hx.comp ![i] (Function.injective_of_subsingleton _)
  have : AlgebraicIndependent R ![x i] := by rwa [← FinVec.map_eq] at this
  rwa [← algebraicIndependent_iff_transcendental]

中文:
定理 transcendental
  条件: (i : ι)
  结论: Transcendental R (x i)
  证明: by
  have := hx.comp ![i] (Function.injective_of_subsingleton _)
  have : AlgebraicIndependent R ![x i] := by rwa [← FinVec.map_eq] at this
  rwa [← algebraicIndependent_iff_transcendental]

Depends on / 依赖: AlgebraicIndependent, FinVec, FinVec.map_eq, Function, Function.injective_of_subsingleton, algebraicIndependent_iff_transcendental, hx.comp, injective_of_subsingleton, map_eq
-/
theorem transcendental (i : ι) : Transcendental R (x i) := by
  have := hx.comp ![i] (Function.injective_of_subsingleton _)
  have : AlgebraicIndependent R ![x i] := by rwa [← FinVec.map_eq] at this
  rwa [← algebraicIndependent_iff_transcendental]

/--
theorem `isEmpty_of_isAlgebraic` / 定理 `isEmpty_of_isAlgebraic`

English:
theorem isEmpty_of_isAlgebraic
  given: [Algebra.IsAlgebraic R A]
  statement: IsEmpty ι
  proof: by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
  · exact h
  exact False.elim (hx.transcendental i (Algebra.IsAlgebraic.isAlgebraic _))

中文:
定理 isEmpty_of_isAlgebraic
  条件: [Algebra.IsAlgebraic R A]
  结论: IsEmpty ι
  证明: by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
  · exact h
  exact False.elim (hx.transcendental i (Algebra.IsAlgebraic.isAlgebraic _))

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, False.elim, IsAlgebraic, hx.transcendental, isAlgebraic, isEmpty_or_nonempty, transcendental
-/
theorem isEmpty_of_isAlgebraic [Algebra.IsAlgebraic R A] : IsEmpty ι := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i⟩⟩
  · exact h
  exact False.elim (hx.transcendental i (Algebra.IsAlgebraic.isAlgebraic _))

end AlgebraicIndependent

/--
theorem `trdeg_eq_zero` / 定理 `trdeg_eq_zero`

English:
theorem trdeg_eq_zero
  given: [Algebra.IsAlgebraic R A]
  statement: trdeg R A = 0
  proof: bot_unique ciSup_le' fun s => have := s.2.isEmpty_of_isAlgebraic; (Cardinal.mk_eq_zero _).le

中文:
定理 trdeg_eq_zero
  条件: [Algebra.IsAlgebraic R A]
  结论: trdeg R A = 0
  证明: bot_unique ciSup_le' fun s => have := s.2.isEmpty_of_isAlgebraic; (Cardinal.mk_eq_zero _).le

Depends on / 依赖: Cardinal, Cardinal.mk_eq_zero, bot_unique, ciSup_le, isEmpty_of_isAlgebraic, mk_eq_zero
-/
theorem trdeg_eq_zero [Algebra.IsAlgebraic R A] : trdeg R A = 0 :=
bot_unique ciSup_le' fun s => have := s.2.isEmpty_of_isAlgebraic; (Cardinal.mk_eq_zero _).le

variable (R A) in
/--
theorem `trdeg_pos` / 定理 `trdeg_pos`

English:
theorem trdeg_pos
  given: [Algebra.Transcendental R A]
  statement: 0 < trdeg R A
  proof: have ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := R) (A := A)
zero_lt_one.trans_le le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨{x}, algebraicIndependent_unique_type_iff.mpr hx⟩ (by simp)

中文:
定理 trdeg_pos
  条件: [Algebra.Transcendental R A]
  结论: 0 < trdeg R A
  证明: have ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := R) (A := A)
zero_lt_one.trans_le le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨{x}, algebraicIndependent_unique_type_iff.mpr hx⟩ (by simp)

Depends on / 依赖: Algebra, Algebra.Transcendental.transcendental, Cardinal, Cardinal.bddAbove_of_small, Transcendental, algebraicIndependent_unique_type_iff, algebraicIndependent_unique_type_iff.mpr, bddAbove_of_small, le_ciSup_of_le, trans_le, transcendental, zero_lt_one, zero_lt_one.trans_le
-/
theorem trdeg_pos [Algebra.Transcendental R A] : 0 < trdeg R A :=
  have ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := R) (A := A)
zero_lt_one.trans_le le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨{x}, algebraicIndependent_unique_type_iff.mpr hx⟩ (by simp)

/--
theorem `trdeg_eq_zero_iff` / 定理 `trdeg_eq_zero_iff`

English:
theorem trdeg_eq_zero_iff
  statement: trdeg R A = 0 ↔ Algebra.IsAlgebraic R A
  proof: by
  by_cases h : Algebra.IsAlgebraic R A
  · exact iff_of_true trdeg_eq_zero h
  rw [← not_iff_not]
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at h ⊢
  exact iff_of_true (trdeg_pos R A).ne' h

中文:
定理 trdeg_eq_zero_iff
  结论: trdeg R A = 0 ↔ Algebra.IsAlgebraic R A
  证明: by
  by_cases h : Algebra.IsAlgebraic R A
  · exact iff_of_true trdeg_eq_zero h
  rw [← not_iff_not]
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at h ⊢
  exact iff_of_true (trdeg_pos R A).ne' h

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.transcendental_iff_not_isAlgebraic, IsAlgebraic, iff_of_true, not_iff_not, transcendental_iff_not_isAlgebraic, trdeg_eq_zero, trdeg_pos
-/
theorem trdeg_eq_zero_iff : trdeg R A = 0 ↔ Algebra.IsAlgebraic R A := by
  by_cases h : Algebra.IsAlgebraic R A
  · exact iff_of_true trdeg_eq_zero h
  rw [← not_iff_not]
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at h ⊢
  exact iff_of_true (trdeg_pos R A).ne' h

/--
theorem `trdeg_ne_zero_iff` / 定理 `trdeg_ne_zero_iff`

English:
theorem trdeg_ne_zero_iff
  statement: trdeg R A != 0 ↔ Algebra.Transcendental R A
  proof: by
  rw [Algebra.transcendental_iff_not_isAlgebraic]; rw [Ne]; rw [trdeg_eq_zero_iff]

中文:
定理 trdeg_ne_zero_iff
  结论: trdeg R A != 0 ↔ Algebra.Transcendental R A
  证明: by
  rw [Algebra.transcendental_iff_not_isAlgebraic]; rw [Ne]; rw [trdeg_eq_zero_iff]

Depends on / 依赖: Algebra, Algebra.transcendental_iff_not_isAlgebraic, transcendental_iff_not_isAlgebraic, trdeg_eq_zero_iff
-/
theorem trdeg_ne_zero_iff : trdeg R A != 0 ↔ Algebra.Transcendental R A := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]; rw [Ne]; rw [trdeg_eq_zero_iff]

open AlgebraicIndependent

/--
theorem `AlgebraicIndependent.option_iff_transcendental` / 定理 `AlgebraicIndependent.option_iff_transcendental`

English:
theorem AlgebraicIndependent.option_iff_transcendental
  given: (hx : AlgebraicIndependent R x) (a : A)
  proof: by
  rw [algebraicIndependent_iff_injective_aeval]; rw [transcendental_iff_injective]; rw [← AlgHom.coe_toRingHom]; rw [← hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin]; rw [RingHom.coe_comp]
  exact Injective.of_comp_iff' (Polynomial.aeval a)
    (mvPolynomialOptionEquivPolynomialAdjoin hx)

中文:
定理 AlgebraicIndependent.option_iff_transcendental
  条件: (hx : AlgebraicIndependent R x) (a : A)
  证明: by
  rw [algebraicIndependent_iff_injective_aeval]; rw [transcendental_iff_injective]; rw [← AlgHom.coe_toRingHom]; rw [← hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin]; rw [RingHom.coe_comp]
  exact Injective.of_comp_iff' (Polynomial.aeval a)
    (mvPolynomialOptionEquivPolynomialAdjoin hx)

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, Injective, Injective.of_comp_iff, Polynomial, Polynomial.aeval, RingHom, RingHom.coe_comp, aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin, algebraicIndependent_iff_injective_aeval, bijective, coe_comp, coe_toRingHom, hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin, mvPolynomialOptionEquivPolynomialAdjoin, of_comp_iff, transcendental_iff_injective
-/
theorem AlgebraicIndependent.option_iff_transcendental (hx : AlgebraicIndependent R x) (a : A) :
    AlgebraicIndependent R (fun o : Option ι => o.elim a x) ↔
      Transcendental (adjoin R (range x)) a := by
  rw [algebraicIndependent_iff_injective_aeval]; rw [transcendental_iff_injective]; rw [← AlgHom.coe_toRingHom]; rw [← hx.aeval_comp_mvPolynomialOptionEquivPolynomialAdjoin]; rw [RingHom.coe_comp]
  exact Injective.of_comp_iff' (Polynomial.aeval a)
    (mvPolynomialOptionEquivPolynomialAdjoin hx).bijective

/--
theorem `AlgebraicIndependent.option_iff` / 定理 `AlgebraicIndependent.option_iff`

English:
theorem AlgebraicIndependent.option_iff
  given: {a : A}
  proof: ⟨fun h => have := h.comp _ (Option.some_injective _); ⟨this,
    (this.option_iff_transcendental _).mp h⟩, fun h => (h.1.option_iff_transcendental _).mpr h.2⟩

中文:
定理 AlgebraicIndependent.option_iff
  条件: {a : A}
  证明: ⟨fun h => have := h.comp _ (Option.some_injective _); ⟨this,
    (this.option_iff_transcendental _).mp h⟩, fun h => (h.1.option_iff_transcendental _).mpr h.2⟩

Depends on / 依赖: Option.some_injective, h.comp, option_iff_transcendental, some_injective, this.option_iff_transcendental
-/
theorem AlgebraicIndependent.option_iff {a : A} :
    AlgebraicIndependent R (fun o : Option ι => o.elim a x) ↔
      AlgebraicIndependent R x ∧ Transcendental (adjoin R (range x)) a :=
  ⟨fun h => have := h.comp _ (Option.some_injective _); ⟨this,
    (this.option_iff_transcendental _).mp h⟩, fun h => (h.1.option_iff_transcendental _).mpr h.2⟩

/--
theorem `AlgebraicIndepOn.insert_iff` / 定理 `AlgebraicIndepOn.insert_iff`

English:
theorem AlgebraicIndepOn.insert_iff
  given: {s : Set ι} {i : ι} (h : i ∉ s)
  proof: by
  classical simp_rw [← algebraicIndependent_equiv (subtypeInsertEquivOption h).symm,
    AlgebraicIndepOn]
  convert! option_iff (x := fun i : s => x i) (a := x i) using 2
  · ext (_ | _) <;> rfl
  · rw [Set.image_eq_range]

中文:
定理 AlgebraicIndepOn.insert_iff
  条件: {s : Set ι} {i : ι} (h : i ∉ s)
  证明: by
  classical simp_rw [← algebraicIndependent_equiv (subtypeInsertEquivOption h).symm,
    AlgebraicIndepOn]
  convert! option_iff (x := fun i : s => x i) (a := x i) using 2
  · ext (_ | _) <;> rfl
  · rw [Set.image_eq_range]

Depends on / 依赖: AlgebraicIndepOn, Set.image_eq_range, algebraicIndependent_equiv, classical, convert, image_eq_range, option_iff, simp_rw, subtypeInsertEquivOption
-/
theorem AlgebraicIndepOn.insert_iff {s : Set ι} {i : ι} (h : i ∉ s) :
    AlgebraicIndepOn R x (insert i s) ↔
      AlgebraicIndepOn R x s ∧ Transcendental (adjoin R (x '' s)) (x i) := by
  classical simp_rw [← algebraicIndependent_equiv (subtypeInsertEquivOption h).symm,
    AlgebraicIndepOn]
  convert! option_iff (x := fun i : s => x i) (a := x i) using 2
  · ext (_ | _) <;> rfl
  · rw [Set.image_eq_range]

/--
theorem `AlgebraicIndepOn.insert` / 定理 `AlgebraicIndepOn.insert`

English:
theorem AlgebraicIndepOn.insert
  statement: {s : Set ι} {i : ι} (hs : AlgebraicIndepOn R x s)
  proof: by
  nontriviality R
  have := hs.algebraMap_injective.nontrivial
  exact (insert_iff fun h => hi <| isAlgebraic_algebraMap
    (⟨_, subset_adjoin ⟨i, h, rfl⟩⟩ : adjoin R (x '' s))).mpr ⟨hs, hi⟩

中文:
定理 AlgebraicIndepOn.insert
  结论: {s : Set ι} {i : ι} (hs : AlgebraicIndepOn R x s)
  证明: by
  nontriviality R
  have := hs.algebraMap_injective.nontrivial
  exact (insert_iff fun h => hi <| isAlgebraic_algebraMap
    (⟨_, subset_adjoin ⟨i, h, rfl⟩⟩ : adjoin R (x '' s))).mpr ⟨hs, hi⟩
-/
protected theorem AlgebraicIndepOn.insert {s : Set ι} {i : ι} (hs : AlgebraicIndepOn R x s)
    (hi : Transcendental (adjoin R (x '' s)) (x i)) : AlgebraicIndepOn R x (insert i s) := by
  nontriviality R
  have := hs.algebraMap_injective.nontrivial
  exact (insert_iff fun h => hi <| isAlgebraic_algebraMap
    (⟨_, subset_adjoin ⟨i, h, rfl⟩⟩ : adjoin R (x '' s))).mpr ⟨hs, hi⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `algebraicIndependent_of_set_of_finite` / 定理 `algebraicIndependent_of_set_of_finite`

English:
theorem algebraicIndependent_of_set_of_finite
  statement: (s : Set ι)
  proof: by
  classical
  refine algebraicIndependent_of_finite_type fun t hfin => ?_
  suffices AlgebraicIndependent R fun i : ↥(t inter s union t \ s) => x i from
    this.comp (Equiv.setCongr (t.inter_union_sdiff s).symm) (Equiv.injective _)
  refine hfin.sdiff.induction_on_subset _ (ind.comp (inclusion <

中文:
定理 algebraicIndependent_of_set_of_finite
  结论: (s : Set ι)
  证明: by
  classical
  refine algebraicIndependent_of_finite_type fun t hfin => ?_
  suffices AlgebraicIndependent R fun i : ↥(t inter s union t \ s) => x i from
    this.comp (Equiv.setCongr (t.inter_union_sdiff s).symm) (Equiv.injective _)
  refine hfin.sdiff.induction_on_subset _ (ind.comp (inclusion <

Depends on / 依赖: AlgebraicIndependent, Equiv.injective, Equiv.setCongr, algebraicIndependent_of_finite_type, classical, convert, h.option_iff_transcendental, hfin.sdiff.induction_on_subset, hfin.subset, image_eq_range, inclusion, inclusion_injective, ind.comp, induction_on_subset, injective, inter_union_sdiff, option_iff_transcendental, setCongr, subset, t.inter_union_sdiff
-/
theorem algebraicIndependent_of_set_of_finite (s : Set ι)
    (ind : AlgebraicIndependent R fun i : s => x i)
    (H : forall t : Set ι, t.Finite -> AlgebraicIndependent R (fun i : t => x i) ->
      forall i ∉ s, i ∉ t -> Transcendental (adjoin R (x '' t)) (x i)) :
    AlgebraicIndependent R x := by
  classical
  refine algebraicIndependent_of_finite_type fun t hfin => ?_
  suffices AlgebraicIndependent R fun i : ↥(t inter s union t \ s) => x i from
    this.comp (Equiv.setCongr (t.inter_union_sdiff s).symm) (Equiv.injective _)
  refine hfin.sdiff.induction_on_subset _ (ind.comp (inclusion <| by simp) (inclusion_injective _))
    fun {a u} ha hu ha' h => ?_
  have : a ∉ t inter s union u := (·.elim (ha.2 ·.2) ha')
  convert!
    (((image_eq_range .. ▸ h.option_iff_transcendental <| x a).2 <|
              H _ (hfin.subset (union_subset inter_subset_left <| hu.trans sdiff_subset)) h a ha.2
                this).comp
          _ (subtypeInsertEquivOption this).injective).comp
      (Equiv.setCongr union_insert) (Equiv.injective _) with
    x
  by_cases h : ↑x = a <;> simp [h, Set.subtypeInsertEquivOption]

/--
theorem `algebraicIndependent_of_finite_type'` / 定理 `algebraicIndependent_of_finite_type'`

English:
theorem algebraicIndependent_of_finite_type'
  proof: algebraicIndependent_of_set_of_finite ∅ (algebraicIndependent_empty_type_iff.mpr hinj)
    fun t ht ind i _ => H t ht ind i

中文:
定理 algebraicIndependent_of_finite_type'
  证明: algebraicIndependent_of_set_of_finite ∅ (algebraicIndependent_empty_type_iff.mpr hinj)
    fun t ht ind i _ => H t ht ind i

Depends on / 依赖: algebraicIndependent_empty_type_iff, algebraicIndependent_empty_type_iff.mpr, algebraicIndependent_of_set_of_finite
-/
theorem algebraicIndependent_of_finite_type'
    (hinj : Injective (algebraMap R A))
    (H : forall t : Set ι, t.Finite -> AlgebraicIndependent R (fun i : t => x i) ->
      forall i ∉ t, Transcendental (adjoin R (x '' t)) (x i)) :
    AlgebraicIndependent R x :=
  algebraicIndependent_of_set_of_finite ∅ (algebraicIndependent_empty_type_iff.mpr hinj)
    fun t ht ind i _ => H t ht ind i

/--
theorem `algebraicIndependent_of_finite'` / 定理 `algebraicIndependent_of_finite'`

English:
theorem algebraicIndependent_of_finite'
  statement: (s : Set A)
  proof: algebraicIndependent_of_finite_type' hinj fun t hfin h i hi => H _
    (by rintro _ ⟨x, _, rfl⟩; exact x.2) (hfin.image _) h.image _ i.2
    (mt Subtype.val_injective.mem_set_image.mp hi)

中文:
定理 algebraicIndependent_of_finite'
  结论: (s : Set A)
  证明: algebraicIndependent_of_finite_type' hinj fun t hfin h i hi => H _
    (by rintro _ ⟨x, _, rfl⟩; exact x.2) (hfin.image _) h.image _ i.2
    (mt Subtype.val_injective.mem_set_image.mp hi)

Depends on / 依赖: Subtype, Subtype.val_injective.mem_set_image.mp, algebraicIndependent_of_finite_type, h.image, hfin.image, mem_set_image, val_injective
-/
theorem algebraicIndependent_of_finite' (s : Set A)
    (hinj : Injective (algebraMap R A))
    (H : forall t subseteq s, t.Finite -> AlgebraicIndependent R ((↑) : t -> A) ->
      forall a in s, a ∉ t -> Transcendental (adjoin R t) a) :
    AlgebraicIndependent R ((↑) : s -> A) :=
  algebraicIndependent_of_finite_type' hinj fun t hfin h i hi => H _
    (by rintro _ ⟨x, _, rfl⟩; exact x.2) (hfin.image _) h.image _ i.2
    (mt Subtype.val_injective.mem_set_image.mp hi)

namespace AlgebraicIndependent

/--
theorem `sumElim_iff` / 定理 `sumElim_iff`

English:
theorem sumElim_iff
  given: {ι'} {y : ι' -> A}
  statement: AlgebraicIndependent R (Sum.elim y x) ↔
  proof: by
  by_cases hx : AlgebraicIndependent R x; swap
  · exact ⟨fun h => (hx <| by apply h.comp _ Sum.inr_injective).elim, fun h => (hx h.1).elim⟩
  let e := (sumAlgEquiv R ι' ι).trans (mapAlgEquiv _ hx.aevalEquiv)
  have : aeval (Sum.elim y x) = ((aeval y).restrictScalars R).comp e.toAlgHom := by
    

中文:
定理 sumElim_iff
  条件: {ι'} {y : ι' -> A}
  结论: AlgebraicIndependent R (Sum.elim y x) ↔
  证明: by
  by_cases hx : AlgebraicIndependent R x; swap
  · exact ⟨fun h => (hx <| by apply h.comp _ Sum.inr_injective).elim, fun h => (hx h.1).elim⟩
  let e := (sumAlgEquiv R ι' ι).trans (mapAlgEquiv _ hx.aevalEquiv)
  have : aeval (Sum.elim y x) = ((aeval y).restrictScalars R).comp e.toAlgHom := by
    

Depends on / 依赖: AlgebraicIndependent, Sum.elim, Sum.inr_injective, aevalEquiv, e.toAlgHom, h.comp, hx.aevalEquiv, inr_injective, mapAlgEquiv, restrictScalars, simp_rw, sumAlgEquiv, toAlgHom
-/
theorem sumElim_iff {ι'} {y : ι' -> A} : AlgebraicIndependent R (Sum.elim y x) ↔
    AlgebraicIndependent R x ∧ AlgebraicIndependent (adjoin R (range x)) y := by
  by_cases hx : AlgebraicIndependent R x; swap
  · exact ⟨fun h => (hx <| by apply h.comp _ Sum.inr_injective).elim, fun h => (hx h.1).elim⟩
  let e := (sumAlgEquiv R ι' ι).trans (mapAlgEquiv _ hx.aevalEquiv)
  have : aeval (Sum.elim y x) = ((aeval y).restrictScalars R).comp e.toAlgHom := by
    ext (_ | _) <;> simp [e]
  simp_rw [hx, AlgebraicIndependent, this]; simp

/--
theorem `iff_adjoin_image` / 定理 `iff_adjoin_image`

English:
theorem iff_adjoin_image
  given: (s : Set ι)
  proof: by
  rw [show x '' s = range fun i : s => x i by ext; simp]
  convert! ← sumElim_iff
  classical apply algebraicIndependent_equiv' ((Equiv.sumComm ..).trans (Equiv.Set.sumCompl ..))
  ext (_ | _) <;> rfl

中文:
定理 iff_adjoin_image
  条件: (s : Set ι)
  证明: by
  rw [show x '' s = range fun i : s => x i by ext; simp]
  convert! ← sumElim_iff
  classical apply algebraicIndependent_equiv' ((Equiv.sumComm ..).trans (Equiv.Set.sumCompl ..))
  ext (_ | _) <;> rfl

Depends on / 依赖: Equiv.Set.sumCompl, Equiv.sumComm, algebraicIndependent_equiv, classical, convert, sumComm, sumCompl, sumElim_iff
-/
theorem iff_adjoin_image (s : Set ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun i : s => x i) ∧
      AlgebraicIndepOn (adjoin R (x '' s)) x sᶜ := by
  rw [show x '' s = range fun i : s => x i by ext; simp]
  convert! ← sumElim_iff
  classical apply algebraicIndependent_equiv' ((Equiv.sumComm ..).trans (Equiv.Set.sumCompl ..))
  ext (_ | _) <;> rfl

/--
theorem `iff_adjoin_image_compl` / 定理 `iff_adjoin_image_compl`

English:
theorem iff_adjoin_image_compl
  given: (s : Set ι)
  proof: by
  convert! ← iff_adjoin_image _; apply compl_compl

中文:
定理 iff_adjoin_image_compl
  条件: (s : Set ι)
  证明: by
  convert! ← iff_adjoin_image _; apply compl_compl

Depends on / 依赖: compl_compl, convert, iff_adjoin_image
-/
theorem iff_adjoin_image_compl (s : Set ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun i : ↥sᶜ => x i) ∧
      AlgebraicIndepOn (adjoin R (x '' sᶜ)) x s := by
  convert! ← iff_adjoin_image _; apply compl_compl

/--
theorem `iff_transcendental_adjoin_image` / 定理 `iff_transcendental_adjoin_image`

English:
theorem iff_transcendental_adjoin_image
  given: (i : ι)
  proof: (iff_adjoin_image_compl _).trans and_congr_right
    fun _ => algebraicIndependent_unique_type_iff (ι := {j // j = i})

中文:
定理 iff_transcendental_adjoin_image
  条件: (i : ι)
  证明: (iff_adjoin_image_compl _).trans and_congr_right
    fun _ => algebraicIndependent_unique_type_iff (ι := {j // j = i})

Depends on / 依赖: algebraicIndependent_unique_type_iff, and_congr_right, iff_adjoin_image_compl
-/
theorem iff_transcendental_adjoin_image (i : ι) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R (fun j : {j // j != i} => x j) ∧
      Transcendental (adjoin R (x '' {i}ᶜ)) (x i) :=
(iff_adjoin_image_compl _).trans and_congr_right
    fun _ => algebraicIndependent_unique_type_iff (ι := {j // j = i})

variable (hx : AlgebraicIndependent R x)
include hx

/--
theorem `sumElim` / 定理 `sumElim`

English:
theorem sumElim
  given: {ι'} {y : ι' -> A} (hy : AlgebraicIndependent (adjoin R (range x)) y)
  proof: sumElim_iff.mpr ⟨hx, hy⟩

中文:
定理 sumElim
  条件: {ι'} {y : ι' -> A} (hy : AlgebraicIndependent (adjoin R (range x)) y)
  证明: sumElim_iff.mpr ⟨hx, hy⟩

Depends on / 依赖: sumElim_iff, sumElim_iff.mpr
-/
theorem sumElim {ι'} {y : ι' -> A} (hy : AlgebraicIndependent (adjoin R (range x)) y) :
    AlgebraicIndependent R (Sum.elim y x) :=
  sumElim_iff.mpr ⟨hx, hy⟩

/--
theorem `sumElim_of_tower` / 定理 `sumElim_of_tower`

English:
theorem sumElim_of_tower
  statement: {ι'} {y : ι' -> A} (hxS : range x subseteq range (algebraMap S A))
  proof: by
  let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R S A) hy.algebraMap_injective
  set Rx := adjoin R (range x)
  let _ : Algebra Rx S :=
    (e.symm.toAlgHom.comp <| Subalgebra.inclusion <| adjoin_le hxS).toAlgebra
  have : IsScalarTower Rx S A := .of_algebraMap_eq fun x => show _ = (e (e.

中文:
定理 sumElim_of_tower
  结论: {ι'} {y : ι' -> A} (hxS : range x subseteq range (algebraMap S A))
  证明: by
  let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R S A) hy.algebraMap_injective
  set Rx := adjoin R (range x)
  let _ : Algebra Rx S :=
    (e.symm.toAlgHom.comp <| Subalgebra.inclusion <| adjoin_le hxS).toAlgebra
  have : IsScalarTower Rx S A := .of_algebraMap_eq fun x => show _ = (e (e.

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, AlgHom, AlgHom.coe_toRingHom, Algebra, IsScalarTower, IsScalarTower.toAlgHom, Subalgebra, Subalgebra.inclusion, Subalgebra.inclusion_injective, adjoin, adjoin_le, algebraMap_injective, coe_toRingHom, e.symm, e.symm.injective.comp, e.symm.toAlgHom.comp, hx.sumElim, hy.algebraMap_injective, hy.restrictScalars
-/
theorem sumElim_of_tower {ι'} {y : ι' -> A} (hxS : range x subseteq range (algebraMap S A))
    (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y x) := by
  let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R S A) hy.algebraMap_injective
  set Rx := adjoin R (range x)
  let _ : Algebra Rx S :=
    (e.symm.toAlgHom.comp <| Subalgebra.inclusion <| adjoin_le hxS).toAlgebra
  have : IsScalarTower Rx S A := .of_algebraMap_eq fun x => show _ = (e (e.symm _)).1 by simp
  refine hx.sumElim (hy.restrictScalars (e.symm.injective.comp ?_))
  simpa only [AlgHom.coe_toRingHom] using Subalgebra.inclusion_injective _

omit hx in
/--
theorem `sumElim_comp` / 定理 `sumElim_comp`

English:
theorem sumElim_comp
  statement: {ι'} {x : ι -> S} {y : ι' -> A} (hx : AlgebraicIndependent R x)
  proof: (hx.map' (f := IsScalarTower.toAlgHom R S A) hy.algebraMap_injective).sumElim_of_tower
    (range_comp_subset_range ..) hy

中文:
定理 sumElim_comp
  结论: {ι'} {x : ι -> S} {y : ι' -> A} (hx : AlgebraicIndependent R x)
  证明: (hx.map' (f := IsScalarTower.toAlgHom R S A) hy.algebraMap_injective).sumElim_of_tower
    (range_comp_subset_range ..) hy

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, algebraMap_injective, hx.map, hy.algebraMap_injective, range_comp_subset_range, sumElim_of_tower, toAlgHom
-/
theorem sumElim_comp {ι'} {x : ι -> S} {y : ι' -> A} (hx : AlgebraicIndependent R x)
    (hy : AlgebraicIndependent S y) : AlgebraicIndependent R (Sum.elim y (algebraMap S A ∘ x)) :=
  (hx.map' (f := IsScalarTower.toAlgHom R S A) hy.algebraMap_injective).sumElim_of_tower
    (range_comp_subset_range ..) hy

/--
theorem `adjoin_of_disjoint` / 定理 `adjoin_of_disjoint`

English:
theorem adjoin_of_disjoint
  given: {s t : Set ι} (h : Disjoint s t)
  proof: ((iff_adjoin_image s).mp hx).2.comp (inclusion _) (inclusion_injective h.subset_compl_left)

中文:
定理 adjoin_of_disjoint
  条件: {s t : Set ι} (h : Disjoint s t)
  证明: ((iff_adjoin_image s).mp hx).2.comp (inclusion _) (inclusion_injective h.subset_compl_left)

Depends on / 依赖: h.subset_compl_left, iff_adjoin_image, inclusion, inclusion_injective, subset_compl_left
-/
theorem adjoin_of_disjoint {s t : Set ι} (h : Disjoint s t) :
    AlgebraicIndependent (adjoin R (x '' s)) fun i : t => x i :=
  ((iff_adjoin_image s).mp hx).2.comp (inclusion _) (inclusion_injective h.subset_compl_left)

/--
theorem `adjoin_iff_disjoint` / 定理 `adjoin_iff_disjoint`

English:
theorem adjoin_iff_disjoint
  given: [Nontrivial A] {s t : Set ι}
  proof: by
  refine ⟨fun ind => of_not_not fun ndisj => ?_, adjoin_of_disjoint hx⟩
  have ⟨i, hs, ht⟩ := Set.not_disjoint_iff.mp ndisj
  refine ind.transcendental ⟨i, ht⟩ (isAlgebraic_algebraMap (⟨_, subset_adjoin ?_⟩ : adjoin R _))
  exact ⟨i, hs, rfl⟩

中文:
定理 adjoin_iff_disjoint
  条件: [Nontrivial A] {s t : Set ι}
  证明: by
  refine ⟨fun ind => of_not_not fun ndisj => ?_, adjoin_of_disjoint hx⟩
  have ⟨i, hs, ht⟩ := Set.not_disjoint_iff.mp ndisj
  refine ind.transcendental ⟨i, ht⟩ (isAlgebraic_algebraMap (⟨_, subset_adjoin ?_⟩ : adjoin R _))
  exact ⟨i, hs, rfl⟩

Depends on / 依赖: Set.not_disjoint_iff.mp, adjoin, adjoin_of_disjoint, ind.transcendental, isAlgebraic_algebraMap, not_disjoint_iff, of_not_not, subset_adjoin, transcendental
-/
theorem adjoin_iff_disjoint [Nontrivial A] {s t : Set ι} :
    (AlgebraicIndependent (adjoin R (x '' s)) fun i : t => x i) ↔ Disjoint s t := by
  refine ⟨fun ind => of_not_not fun ndisj => ?_, adjoin_of_disjoint hx⟩
  have ⟨i, hs, ht⟩ := Set.not_disjoint_iff.mp ndisj
  refine ind.transcendental ⟨i, ht⟩ (isAlgebraic_algebraMap (⟨_, subset_adjoin ?_⟩ : adjoin R _))
  exact ⟨i, hs, rfl⟩

/--
theorem `transcendental_adjoin` / 定理 `transcendental_adjoin`

English:
theorem transcendental_adjoin
  given: {s : Set ι} {i : ι} (hi : i ∉ s)
  proof: by
  convert! ← hx.adjoin_of_disjoint (Set.disjoint_singleton_right.mpr hi)
  rw [algebraicIndependent_singleton_iff ⟨i]; rw [rfl⟩]

中文:
定理 transcendental_adjoin
  条件: {s : Set ι} {i : ι} (hi : i ∉ s)
  证明: by
  convert! ← hx.adjoin_of_disjoint (Set.disjoint_singleton_right.mpr hi)
  rw [algebraicIndependent_singleton_iff ⟨i]; rw [rfl⟩]

Depends on / 依赖: Set.disjoint_singleton_right.mpr, adjoin_of_disjoint, algebraicIndependent_singleton_iff, convert, disjoint_singleton_right, hx.adjoin_of_disjoint
-/
theorem transcendental_adjoin {s : Set ι} {i : ι} (hi : i ∉ s) :
    Transcendental (adjoin R (x '' s)) (x i) := by
  convert! ← hx.adjoin_of_disjoint (Set.disjoint_singleton_right.mpr hi)
  rw [algebraicIndependent_singleton_iff ⟨i]; rw [rfl⟩]

/--
theorem `transcendental_adjoin_iff` / 定理 `transcendental_adjoin_iff`

English:
theorem transcendental_adjoin_iff
  given: [Nontrivial A] {s : Set ι} {i : ι}
  proof: by
  rw [← Set.disjoint_singleton_right]
  convert! ← hx.adjoin_iff_disjoint (t := { i })
  rw [algebraicIndependent_singleton_iff ⟨i]; rw [rfl⟩]

中文:
定理 transcendental_adjoin_iff
  条件: [Nontrivial A] {s : Set ι} {i : ι}
  证明: by
  rw [← Set.disjoint_singleton_right]
  convert! ← hx.adjoin_iff_disjoint (t := { i })
  rw [algebraicIndependent_singleton_iff ⟨i]; rw [rfl⟩]

Depends on / 依赖: Set.disjoint_singleton_right, adjoin_iff_disjoint, algebraicIndependent_singleton_iff, convert, disjoint_singleton_right, hx.adjoin_iff_disjoint
-/
theorem transcendental_adjoin_iff [Nontrivial A] {s : Set ι} {i : ι} :
    Transcendental (adjoin R (x '' s)) (x i) ↔ i ∉ s := by
  rw [← Set.disjoint_singleton_right]
  convert! ← hx.adjoin_iff_disjoint (t := { i })
  rw [algebraicIndependent_singleton_iff ⟨i]; rw [rfl⟩]

end AlgebraicIndependent

open Cardinal in
/--
theorem `lift_trdeg_add_le` / 定理 `lift_trdeg_add_le`

English:
theorem lift_trdeg_add_le
  given: [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A]
  proof: by
  simp_rw [trdeg, lift_iSup bddAbove_of_small]
  simp_rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small,
    add_comm (lift.{v, u} _), ← mk_sum]
  refine ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ => ?_
  have := hs.sumElim_comp ht
  refine le_ciSup_of_le bddAbove_of_small ⟨_

中文:
定理 lift_trdeg_add_le
  条件: [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A]
  证明: by
  simp_rw [trdeg, lift_iSup bddAbove_of_small]
  simp_rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small,
    add_comm (lift.{v, u} _), ← mk_sum]
  refine ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ => ?_
  have := hs.sumElim_comp ht
  refine le_ciSup_of_le bddAbove_of_small ⟨_

Depends on / 依赖: Cardinal, Cardinal.ciSup_add_ciSup, add_comm, bddAbove_of_small, ciSup_add_ciSup, ciSup_le, hs.sumElim_comp, injective, le_ciSup_of_le, lift_iSup, lift_id, lift_umax, mk_range_eq_of_injective, mk_sum, simp_rw, sumElim_comp, this.injective, this.to_subtype_range, to_subtype_range
-/
theorem lift_trdeg_add_le [Nontrivial R] [FaithfulSMul R S] [FaithfulSMul S A] :
    lift.{v} (trdeg R S) + lift.{u} (trdeg S A) <= lift.{u} (trdeg R A) := by
  simp_rw [trdeg, lift_iSup bddAbove_of_small]
  simp_rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small,
    add_comm (lift.{v, u} _), ← mk_sum]
  refine ciSup_le fun ⟨s, hs⟩ => ciSup_le fun ⟨t, ht⟩ => ?_
  have := hs.sumElim_comp ht
  refine le_ciSup_of_le bddAbove_of_small ⟨_, this.to_subtype_range⟩ ?_
  rw [← lift_umax]; rw [mk_range_eq_of_injective this.injective]; rw [lift_id']

/--
theorem `trdeg_add_le` / 定理 `trdeg_add_le`

English:
theorem trdeg_add_le
  statement: [Nontrivial R] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A]
  proof: by
  rw [← (trdeg R S).lift_id]; rw [← (trdeg S A).lift_id]; rw [← (trdeg R A).lift_id]
  exact lift_trdeg_add_le

中文:
定理 trdeg_add_le
  结论: [Nontrivial R] {A : 类型u} [CommRing A] [Algebra R A] [Algebra S A]
  证明: by
  rw [← (trdeg R S).lift_id]; rw [← (trdeg S A).lift_id]; rw [← (trdeg R A).lift_id]
  exact lift_trdeg_add_le

Depends on / 依赖: lift_id, lift_trdeg_add_le
-/
theorem trdeg_add_le [Nontrivial R] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A]
    [FaithfulSMul R S] [FaithfulSMul S A] [IsScalarTower R S A] :
    trdeg R S + trdeg S A <= trdeg R A := by
  rw [← (trdeg R S).lift_id]; rw [← (trdeg S A).lift_id]; rw [← (trdeg R A).lift_id]
  exact lift_trdeg_add_le

/--
theorem `MvPolynomial.algebraicIndependent_polynomial_aeval_X` / 定理 `MvPolynomial.algebraicIndependent_polynomial_aeval_X`

English:
theorem MvPolynomial.algebraicIndependent_polynomial_aeval_X
  proof: by
  set x := fun i => Polynomial.aeval (X i : MvPolynomial ι R) (f i)
  refine algebraicIndependent_of_finite_type' (C_injective _ _) fun t _ _ i hi => ?_
  have hle : adjoin R (x '' t) <= supported R t := by
    rw [Algebra.adjoin_le_iff]; rw [Set.image_subset_iff]
    intro _ h
    rw [Set.mem_pr

中文:
定理 MvPolynomial.algebraicIndependent_polynomial_aeval_X
  证明: by
  set x := fun i => Polynomial.aeval (X i : MvPolynomial ι R) (f i)
  refine algebraicIndependent_of_finite_type' (C_injective _ _) fun t _ _ i hi => ?_
  have hle : adjoin R (x '' t) <= supported R t := by
    rw [Algebra.adjoin_le_iff]; rw [Set.image_subset_iff]
    intro _ h
    rw [Set.mem_pr

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Algebra.adjoin_mono, C_injective, MvPolynomial, Polynomial, Polynomial.aeval, Polynomial.aeval_mem_adjoin_singleton, Set.image_subset_iff, Set.mem_image_of_mem, Set.mem_preimage, adjoin, adjoin_le_iff, adjoin_mono, aeval_mem_adjoin_singleton, algebraicIndependent_of_finite_type, image_subset_iff, mem_image_of_mem, mem_preimage, of_tower_top_of
-/
theorem MvPolynomial.algebraicIndependent_polynomial_aeval_X
    (f : ι -> Polynomial R) (hf : forall i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i => Polynomial.aeval (X i : MvPolynomial ι R) (f i) := by
  set x := fun i => Polynomial.aeval (X i : MvPolynomial ι R) (f i)
  refine algebraicIndependent_of_finite_type' (C_injective _ _) fun t _ _ i hi => ?_
  have hle : adjoin R (x '' t) <= supported R t := by
    rw [Algebra.adjoin_le_iff]; rw [Set.image_subset_iff]
    intro _ h
    rw [Set.mem_preimage]
    refine Algebra.adjoin_mono ?_ (Polynomial.aeval_mem_adjoin_singleton R _)
    simp_rw [singleton_subset_iff, Set.mem_image_of_mem _ h]
  exact (transcendental_supported_polynomial_aeval_X R hi (hf i)).of_tower_top_of_subalgebra_le hle

/--
theorem `AlgebraicIndependent.polynomial_aeval_of_transcendental` / 定理 `AlgebraicIndependent.polynomial_aeval_of_transcendental`

English:
theorem AlgebraicIndependent.polynomial_aeval_of_transcendental
  proof: by
  convert! aeval_of_algebraicIndependent hx (algebraicIndependent_polynomial_aeval_X _ hf)
  rw [← AlgHom.comp_apply]
  congr 1; ext1; simp

中文:
定理 AlgebraicIndependent.polynomial_aeval_of_transcendental
  证明: by
  convert! aeval_of_algebraicIndependent hx (algebraicIndependent_polynomial_aeval_X _ hf)
  rw [← AlgHom.comp_apply]
  congr 1; ext1; simp

Depends on / 依赖: AlgHom, AlgHom.comp_apply, aeval_of_algebraicIndependent, algebraicIndependent_polynomial_aeval_X, comp_apply, convert
-/
theorem AlgebraicIndependent.polynomial_aeval_of_transcendental
    (hx : AlgebraicIndependent R x)
    {f : ι -> Polynomial R} (hf : forall i, Transcendental R (f i)) :
    AlgebraicIndependent R fun i => Polynomial.aeval (x i) (f i) := by
  convert! aeval_of_algebraicIndependent hx (algebraicIndependent_polynomial_aeval_X _ hf)
  rw [← AlgHom.comp_apply]
  congr 1; ext1; simp
