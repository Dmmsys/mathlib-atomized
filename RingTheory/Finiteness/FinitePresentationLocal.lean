/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!

# `Algebra.FinitePresentation` is local

In this file we show that being a finitely presented algebra is local.

## Main results

- `Algebra.FinitePresentation.of_span_eq_top_target`: finite presentation is local on the
  (algebraic) target

-/

public section

open scoped Pointwise TensorProduct

namespace Algebra.FinitePresentation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/--
lemma `of_span_eq_top_target_aux` / 引理 `of_span_eq_top_target_aux`

English:
lemma of_span_eq_top_target_aux
  statement: {A : Type*} [CommRing A] [Algebra R A]
  proof: by
  apply Algebra.FinitePresentation.of_surjective hf
  apply RingHom.ker_fg_of_localizationSpan t ht
  intro g
  let f' : Localization.Away g.val ->ₐ[R] Localization.Away (f g) :=
    Localization.awayMapₐ f g.val
  have (g : t) : Algebra.FinitePresentation R (Localization.Away g.val) :=
    haveI : Algebra.FinitePresentation A (Localization.Away g.val) :=
      IsLocalization.Away.finitePresentation g.val
    Algebra.FinitePresentation.trans R A (Localization.Away g.val)
  apply Algebra.FinitePresentation.ker_fG_of_surjective f'
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _ hf

universe u

中文:
引理 of_span_eq_top_target_aux
  结论: {A : 类型} [交换环 A] [代数 R A]
  证明: by
  apply Algebra.FinitePresentation.of_surjective hf
  apply RingHom.ker_fg_of_localizationSpan t ht
  intro g
  let f' : Localization.Away g.val ->ₐ[R] Localization.Away (f g) :=
    Localization.awayMapₐ f g.val
  have (g : t) : Algebra.FinitePresentation R (Localization.Away g.val) :=
    haveI : Algebra.FinitePresentation A (Localization.Away g.val) :=
      IsLocalization.Away.finitePresentation g.val
    Algebra.FinitePresentation.trans R A (Localization.Away g.val)
  apply Algebra.FinitePresentation.ker_fG_of_surjective f'
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _ hf

universe u

Depends on / 依赖: Algebra, Algebra.FinitePresentation, Algebra.FinitePresentation.ker_fG_of_surjec, Algebra.FinitePresentation.of_surjective, Algebra.FinitePresentation.trans, FinitePresentation, IsLocalization, IsLocalization.Away.finitePresentation, Localization, Localization.Away, Localization.awayMap, RingHom, RingHom.ker_fg_of_localizationSpan, finitePresentation, g.val, ker_fG_of_surjec, ker_fg_of_localizationSpan, of_surjective
-/
lemma of_span_eq_top_target_aux {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (f : A ->ₐ[R] S) (hf : Function.Surjective f)
    (t : Finset A) (ht : Ideal.span (t : Set A) = ⊤)
    (H : forall g : t, Algebra.FinitePresentation R (Localization.Away (f g))) :
    Algebra.FinitePresentation R S := by
  apply Algebra.FinitePresentation.of_surjective hf
  apply RingHom.ker_fg_of_localizationSpan t ht
  intro g
  let f' : Localization.Away g.val ->ₐ[R] Localization.Away (f g) :=
    Localization.awayMapₐ f g.val
  have (g : t) : Algebra.FinitePresentation R (Localization.Away g.val) :=
    haveI : Algebra.FinitePresentation A (Localization.Away g.val) :=
      IsLocalization.Away.finitePresentation g.val
    Algebra.FinitePresentation.trans R A (Localization.Away g.val)
  apply Algebra.FinitePresentation.ker_fG_of_surjective f'
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _ hf

universe u

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `of_span_eq_top_target` / 引理 `of_span_eq_top_target`

English:
lemma of_span_eq_top_target
  statement: (s : Set S) (hs : Ideal.span (s : Set S) = ⊤)
  proof: by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FinitePresentation R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  /-
  We already know that `S` is of finite type over `R`, so we have a surjection
  `MvPolynomial (Fin n) R →ₐ[R] S`. To reason about the kernel, we want to check it on the stalks
  of preimages of `s`. But the preimages do not necessarily span `MvPolynomial (Fin n) R`, so
  we quotient out by an ideal and apply `finitePresentation_ofLocalizationSpanTarget_aux`.
  -/
  have hfintype : Algebra.FiniteType R S := by
    apply Algebra.FiniteType.of_span_eq_top_target s hs
    intro x hx
    have := h ⟨x, hx⟩
    infer_instance
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfintype
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) in Ideal.span (s : Set S) by rw [hs]; trivial)
  choose g' hg' using (fun g : s => hf g)
  choose h' hh' using (fun g : s => hf (l g))
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span { ∑ g : s, g' g * h' g - 1 }
  let A := MvPolynomial (Fin n) R ⧸ I
  have hfI : forall a in I, f a = 0 := by
    intro p hp
    simp only [Finset.univ_eq_attach, I, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul, map_sub, map_sum, map_one, hg', hh']
    rw [Finsupp.linearCombination_apply_of_mem_supported (α := (s : Set S)) S (s := s.attach)] at hl
    · rw [← hl]
      simp only [Finset.coe_sort_coe, smul_eq_mul, mul_comm, sub_self, zero_mul]
    · rintro a -
      simp
  let f' : A ->ₐ[R] S := Ideal.Quotient.liftₐ I f hfI
  have hf' : Function.Surjective f' :=
    Ideal.Quotient.lift_surjective_of_surjective I hfI hf
  let t : Finset A := Finset.image (fun g => g' g) Finset.univ
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : ∑ g : { x // x in s }, g' g * h' g = (1 : A) := by
      apply eq_of_sub_eq_zero
      rw [← map_one (Ideal.Quotient.mk I)]; rw [← map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.subset_span
      simp
    simp_rw [← this, Finset.univ_eq_attach, map_sum, map_mul]
    refine Ideal.sum_mem _ (fun g _ => Ideal.mul_mem_right _ _ <| Ideal.subset_span ?_)
    simp [t]
  have : Algebra.FinitePresentation R A := by
    apply Algebra.FinitePresentation.quotient
    simp only [Finset.univ_eq_attach, I]
    exact ⟨{∑ g in s.attach, g' g * h' g - 1}, by simp⟩
  have Ht (g : t) : Algebra.FinitePresentation R (Localization.Away (f' g)) := by
    have : exists (a : S) (hb : a in s), (Ideal.Quotient.mk I) (g' ⟨a, hb⟩) = g.val := by
      obtain ⟨g, hg⟩ := g
      convert! hg
      simp [A, t]
    obtain ⟨r, hr, hrr⟩ := this
    simp only [f']
    rw [← hrr]; rw [Ideal.Quotient.liftₐ_apply]; rw [Ideal.Quotient.lift_mk]
    simp_rw +instances [RingHom.coe_coe]
    rw [hg']
    apply h
  exact of_span_eq_top_target_aux f' hf' t ht Ht

中文:
引理 of_span_eq_top_target
  结论: (s : 集合 S) (hs : 理想.span (s : 集合 S) = ⊤)
  证明: by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FinitePresentation R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  /-
  We already know that `S` is of finite type over `R`, so we have a surjection
  `MvPolynomial (Fin n) R →ₐ[R] S`. To reason about the kernel, we want to check it on the stalks
  of preimages of `s`. But the preimages do not necessarily span `MvPolynomial (Fin n) R`, so
  we quotient out by an ideal and apply `finitePresentation_ofLocalizationSpanTarget_aux`.
  -/
  have hfintype : Algebra.FiniteType R S := by
    apply Algebra.FiniteType.of_span_eq_top_target s hs
    intro x hx
    have := h ⟨x, hx⟩
    infer_instance
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfintype
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) in Ideal.span (s : Set S) by rw [hs]; trivial)
  choose g' hg' using (fun g : s => hf g)
  choose h' hh' using (fun g : s => hf (l g))
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span { ∑ g : s, g' g * h' g - 1 }
  let A := MvPolynomial (Fin n) R ⧸ I
  have hfI : forall a in I, f a = 0 := by
    intro p hp
    simp only [Finset.univ_eq_attach, I, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul, map_sub, map_sum, map_one, hg', hh']
    rw [Finsupp.linearCombination_apply_of_mem_supported (α := (s : Set S)) S (s := s.attach)] at hl
    · rw [← hl]
      simp only [Finset.coe_sort_coe, smul_eq_mul, mul_comm, sub_self, zero_mul]
    · rintro a -
      simp
  let f' : A ->ₐ[R] S := Ideal.Quotient.liftₐ I f hfI
  have hf' : Function.Surjective f' :=
    Ideal.Quotient.lift_surjective_of_surjective I hfI hf
  let t : Finset A := Finset.image (fun g => g' g) Finset.univ
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : ∑ g : { x // x in s }, g' g * h' g = (1 : A) := by
      apply eq_of_sub_eq_zero
      rw [← map_one (Ideal.Quotient.mk I)]; rw [← map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.subset_span
      simp
    simp_rw [← this, Finset.univ_eq_attach, map_sum, map_mul]
    refine Ideal.sum_mem _ (fun g _ => Ideal.mul_mem_right _ _ <| Ideal.subset_span ?_)
    simp [t]
  have : Algebra.FinitePresentation R A := by
    apply Algebra.FinitePresentation.quotient
    simp only [Finset.univ_eq_attach, I]
    exact ⟨{∑ g in s.attach, g' g * h' g - 1}, by simp⟩
  have Ht (g : t) : Algebra.FinitePresentation R (Localization.Away (f' g)) := by
    have : exists (a : S) (hb : a in s), (Ideal.Quotient.mk I) (g' ⟨a, hb⟩) = g.val := by
      obtain ⟨g, hg⟩ := g
      convert! hg
      simp [A, t]
    obtain ⟨r, hr, hrr⟩ := this
    simp only [f']
    rw [← hrr]; rw [Ideal.Quotient.liftₐ_apply]; rw [Ideal.Quotient.lift_mk]
    simp_rw +instances [RingHom.coe_coe]
    rw [hg']
    apply h
  exact of_span_eq_top_target_aux f' hf' t ht Ht

Depends on / 依赖: Algebra, Algebra.FinitePresentation, FinitePresentation, Ideal.span_eq_top_iff_finite, Localization, Localization.Away, classical, i.property, i.val, property, replace, span_eq_top_iff_finite
-/
lemma of_span_eq_top_target (s : Set S) (hs : Ideal.span (s : Set S) = ⊤)
    (h : forall i in s, Algebra.FinitePresentation R (Localization.Away i)) :
    Algebra.FinitePresentation R S := by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FinitePresentation R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  /-
  We already know that `S` is of finite type over `R`, so we have a surjection
  `MvPolynomial (Fin n) R →ₐ[R] S`. To reason about the kernel, we want to check it on the stalks
  of preimages of `s`. But the preimages do not necessarily span `MvPolynomial (Fin n) R`, so
  we quotient out by an ideal and apply `finitePresentation_ofLocalizationSpanTarget_aux`.
  -/
  have hfintype : Algebra.FiniteType R S := by
    apply Algebra.FiniteType.of_span_eq_top_target s hs
    intro x hx
    have := h ⟨x, hx⟩
    infer_instance
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfintype
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) in Ideal.span (s : Set S) by rw [hs]; trivial)
  choose g' hg' using (fun g : s => hf g)
  choose h' hh' using (fun g : s => hf (l g))
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span { ∑ g : s, g' g * h' g - 1 }
  let A := MvPolynomial (Fin n) R ⧸ I
  have hfI : forall a in I, f a = 0 := by
    intro p hp
    simp only [Finset.univ_eq_attach, I, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    simp only [map_mul, map_sub, map_sum, map_one, hg', hh']
    rw [Finsupp.linearCombination_apply_of_mem_supported (α := (s : Set S)) S (s := s.attach)] at hl
    · rw [← hl]
      simp only [Finset.coe_sort_coe, smul_eq_mul, mul_comm, sub_self, zero_mul]
    · rintro a -
      simp
  let f' : A ->ₐ[R] S := Ideal.Quotient.liftₐ I f hfI
  have hf' : Function.Surjective f' :=
    Ideal.Quotient.lift_surjective_of_surjective I hfI hf
  let t : Finset A := Finset.image (fun g => g' g) Finset.univ
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : ∑ g : { x // x in s }, g' g * h' g = (1 : A) := by
      apply eq_of_sub_eq_zero
      rw [← map_one (Ideal.Quotient.mk I)]; rw [← map_sub]; rw [Ideal.Quotient.eq_zero_iff_mem]
      apply Ideal.subset_span
      simp
    simp_rw [← this, Finset.univ_eq_attach, map_sum, map_mul]
    refine Ideal.sum_mem _ (fun g _ => Ideal.mul_mem_right _ _ <| Ideal.subset_span ?_)
    simp [t]
  have : Algebra.FinitePresentation R A := by
    apply Algebra.FinitePresentation.quotient
    simp only [Finset.univ_eq_attach, I]
    exact ⟨{∑ g in s.attach, g' g * h' g - 1}, by simp⟩
  have Ht (g : t) : Algebra.FinitePresentation R (Localization.Away (f' g)) := by
    have : exists (a : S) (hb : a in s), (Ideal.Quotient.mk I) (g' ⟨a, hb⟩) = g.val := by
      obtain ⟨g, hg⟩ := g
      convert! hg
      simp [A, t]
    obtain ⟨r, hr, hrr⟩ := this
    simp only [f']
    rw [← hrr]; rw [Ideal.Quotient.liftₐ_apply]; rw [Ideal.Quotient.lift_mk]
    simp_rw +instances [RingHom.coe_coe]
    rw [hg']
    apply h
  exact of_span_eq_top_target_aux f' hf' t ht Ht

/--
lemma `of_span_eq_top_target_of_isLocalizationAway` / 引理 `of_span_eq_top_target_of_isLocalizationAway`

English:
lemma of_span_eq_top_target_of_isLocalizationAway
  statement: {ι : Type*} (s : ι -> S)
  proof: by
  apply of_span_eq_top_target _ hs
  rintro - ⟨i, rfl⟩
exact .equiv .restrictScalars R (IsLocalization.algEquiv (.powers <| s i) _ (T i)).symm

中文:
引理 of_span_eq_top_target_of_isLocalizationAway
  结论: {ι : 类型} (s : ι -> S)
  证明: by
  apply of_span_eq_top_target _ hs
  rintro - ⟨i, rfl⟩
exact .equiv .restrictScalars R (IsLocalization.algEquiv (.powers <| s i) _ (T i)).symm

Depends on / 依赖: IsLocalization, IsLocalization.algEquiv, algEquiv, of_span_eq_top_target, powers, restrictScalars
-/
lemma of_span_eq_top_target_of_isLocalizationAway {ι : Type*} (s : ι -> S)
    (hs : Ideal.span (Set.range s) = ⊤) (T : ι -> Type*) [forall i, CommRing (T i)] [forall i, Algebra R (T i)]
    [forall i, Algebra S (T i)] [forall i, IsScalarTower R S (T i)] [forall i, IsLocalization.Away (s i) (T i)]
    [forall i, Algebra.FinitePresentation R (T i)] :
    Algebra.FinitePresentation R S := by
  apply of_span_eq_top_target _ hs
  rintro - ⟨i, rfl⟩
exact .equiv .restrictScalars R (IsLocalization.algEquiv (.powers <| s i) _ (T i)).symm

/--
Instance `pi` / 实例 `pi`

English:
instance pi
  signature: {ι : Type*} [Finite ι] (S : ι -> Type*) [forall i, CommRing (S i)] [forall i, Algebra R (S i)]
  body: by
  classical
  let (i : ι) : Algebra (Π a, S a) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : forall a, S a) (S i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  exact Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway
    _ (Ideal.span_single_eq_top S) (fun i => S i)

中文:
实例 pi
  签名: {ι : 类型} [有限 ι] (S : ι -> 类型) [对任意 i, 交换环 (S i)] [对任意 i, 代数 R (S i)]
  定义体: by
  classical
  let (i : ι) : Algebra (Π a, S a) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : forall a, S a) (S i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  exact Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway
    _ (Ideal.span_single_eq_top S) (fun i => S i)

Depends on / 依赖: Algebra, Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway, FinitePresentation, Ideal.span_single_eq_top, IsIdempotentElem, IsLocalization, IsLocalization.Away, IsLocalization.away_of_isIdempotentElem, Pi.evalAlgHom, Pi.evalRingHom, Pi.single, Pi.single_mul_left, RingHom, RingHom.ker_evalRingHom, away_of_isIdempotentElem, classical, evalAlgHom, evalRingHom, ker_evalRingHom, of_span_eq_top_target_of_isLocalizationAway
-/
instance pi {ι : Type*} [Finite ι] (S : ι -> Type*) [forall i, CommRing (S i)] [forall i, Algebra R (S i)]
    [forall i, Algebra.FinitePresentation R (S i)] :
    Algebra.FinitePresentation R (forall a, S a) := by
  classical
  let (i : ι) : Algebra (Π a, S a) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : forall a, S a) (S i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  exact Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway
    _ (Ideal.span_single_eq_top S) (fun i => S i)

end Algebra.FinitePresentation
