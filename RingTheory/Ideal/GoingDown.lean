/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Going down

In this file we define a predicate `Algebra.HasGoingDown`: An `R`-algebra `S` satisfies
`Algebra.HasGoingDown R S` if for every pair of prime ideals `p ≤ q` of `R` with `Q` a prime
of `S` lying above `q`, there exists a prime `P ≤ Q` of `S` lying above `p`.

## Main results

- `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`: going down is equivalent
  to generalizations lifting along `Spec S → Spec R`.
- `Algebra.HasGoingDown.of_flat`: flat algebras satisfy going down.

## Note

- For the fact that an integral extension of domains with normal base satisfies going down,
  see `Mathlib/RingTheory/IntegralClosure/GoingDown.lean`.

-/

@[expose] public section

/--
An `R`-algebra `S` satisfies `Algebra.HasGoingDown R S` if for every pair of
prime ideals `p ≤ q` of `R` with `Q` a prime of `S` lying above `q`, there exists a
prime `P ≤ Q` of `S` lying above `p`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_le_liesOver_of_le` for applying it.
-/
@[stacks 00HV "(2)"]
/--
Definition of `Algebra.HasGoingDown` / `Algebra.HasGoingDown` 的定义

English:
class Algebra.HasGoingDown
  parameters: (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  axioms and operations (1):
    - exists_ideal_le_liesOver_of_lt({p : Ideal R} [p.IsPrime] (Q : Ideal S) [Q.IsPrime]) : p < Q.under R -> exists P <= Q, P.IsPrime ∧ P.LiesOver p

中文:
类 Algebra.HasGoingDown
  参数: (R S : 类型) [CommRing R] [CommRing S] [Algebra R S]
  公理与运算 (1 个):
    - exists_ideal_le_liesOver_of_lt({p : Ideal R} [p.IsPrime] (Q : Ideal S) [Q.IsPrime]) : p < Q.under R -> 存在 P <= Q, P.IsPrime ∧ P.LiesOver p
-/
class Algebra.HasGoingDown (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_ideal_le_liesOver_of_lt {p : Ideal R} [p.IsPrime] (Q : Ideal S) [Q.IsPrime] :
    p < Q.under R -> exists P <= Q, P.IsPrime ∧ P.LiesOver p

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/--
lemma `Ideal.exists_ideal_le_liesOver_of_le` / 引理 `Ideal.exists_ideal_le_liesOver_of_le`

English:
lemma Ideal.exists_ideal_le_liesOver_of_le
  statement: [Algebra.HasGoingDown R S]
  proof: by
  by_cases h : p = q
  · subst h
    use Q
  · have := Q.over_def q
    subst this
    exact Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q (lt_of_le_of_ne hle h)

中文:
引理 Ideal.exists_ideal_le_liesOver_of_le
  结论: [Algebra.HasGoingDown R S]
  证明: by
  by_cases h : p = q
  · subst h
    use Q
  · have := Q.over_def q
    subst this
    exact Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q (lt_of_le_of_ne hle h)

Depends on / 依赖: Algebra, Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt, HasGoingDown, Q.over_def, exists_ideal_le_liesOver_of_lt, lt_of_le_of_ne, over_def
-/
lemma Ideal.exists_ideal_le_liesOver_of_le [Algebra.HasGoingDown R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q]
    (hle : p <= q) :
    exists P <= Q, P.IsPrime ∧ P.LiesOver p := by
  by_cases h : p = q
  · subst h
    use Q
  · have := Q.over_def q
    subst this
    exact Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q (lt_of_le_of_ne hle h)

/--
lemma `Ideal.exists_ideal_lt_liesOver_of_lt` / 引理 `Ideal.exists_ideal_lt_liesOver_of_lt`

English:
lemma Ideal.exists_ideal_lt_liesOver_of_lt
  statement: [Algebra.HasGoingDown R S]
  proof: by
  obtain ⟨P, hPQ, _, _⟩ := Q.exists_ideal_le_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨P, ?_, inferInstance, inferInstance⟩
  by_contra hc
  have : P = Q := eq_of_le_of_not_lt hPQ hc
  subst this
  simp [P.over_def p, P.over_def q] at hpq

中文:
引理 Ideal.exists_ideal_lt_liesOver_of_lt
  结论: [Algebra.HasGoingDown R S]
  证明: by
  obtain ⟨P, hPQ, _, _⟩ := Q.exists_ideal_le_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨P, ?_, inferInstance, inferInstance⟩
  by_contra hc
  have : P = Q := eq_of_le_of_not_lt hPQ hc
  subst this
  simp [P.over_def p, P.over_def q] at hpq

Depends on / 依赖: P.over_def, Q.exists_ideal_le_liesOver_of_le, eq_of_le_of_not_lt, exists_ideal_le_liesOver_of_le, hpq.le, over_def
-/
lemma Ideal.exists_ideal_lt_liesOver_of_lt [Algebra.HasGoingDown R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver q]
    (hpq : p < q) : exists P < Q, P.IsPrime ∧ P.LiesOver p := by
  obtain ⟨P, hPQ, _, _⟩ := Q.exists_ideal_le_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨P, ?_, inferInstance, inferInstance⟩
  by_contra hc
  have : P = Q := eq_of_le_of_not_lt hPQ hc
  subst this
  simp [P.over_def p, P.over_def q] at hpq

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Ideal.exists_ltSeries_of_hasGoingDown` / 引理 `Ideal.exists_ltSeries_of_hasGoingDown`

English:
lemma Ideal.exists_ltSeries_of_hasGoingDown
  statement: [Algebra.HasGoingDown R S]
  proof: by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    use RelSeries.singleton _ ⟨P, inferInstance⟩
    simp only [RelSeries.singleton_length, RelSeries.last_singleton, RelSeries.toList_singleton,
      List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and

中文:
引理 Ideal.exists_ltSeries_of_hasGoingDown
  结论: [Algebra.HasGoingDown R S]
  证明: by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    use RelSeries.singleton _ ⟨P, inferInstance⟩
    simp only [RelSeries.singleton_length, RelSeries.last_singleton, RelSeries.toList_singleton,
      List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and

Depends on / 依赖: L.head.asIdeal.LiesOver, L.toList_getElem_ze, LiesOver, List.cons.injEq, List.map_cons, List.map_nil, RelSeries, RelSeries.inductionOn, RelSeries.last_cons, RelSeries.last_singleton, RelSeries.singleton, RelSeries.singleton_length, RelSeries.toList_singleton, and_true, asIdeal, generalizing, inductionOn, l.head.asIdeal, last_cons, last_singleton
-/
lemma Ideal.exists_ltSeries_of_hasGoingDown [Algebra.HasGoingDown R S]
    (l : LTSeries (PrimeSpectrum R)) (P : Ideal S) [P.IsPrime] [lo : P.LiesOver l.last.asIdeal] :
    exists (L : LTSeries (PrimeSpectrum S)),
      L.length = l.length ∧
      L.last = ⟨P, inferInstance⟩ ∧
      List.map (PrimeSpectrum.comap (algebraMap R S)) L.toList = l.toList := by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    use RelSeries.singleton _ ⟨P, inferInstance⟩
    simp only [RelSeries.singleton_length, RelSeries.last_singleton, RelSeries.toList_singleton,
      List.map_cons, List.map_nil, List.cons.injEq, and_true, true_and]
    ext : 1
    simpa using lo.over.symm
  | cons l q lt ih =>
    simp only [RelSeries.last_cons] at lo
    obtain ⟨L, len, last, spec⟩ := ih P
    have : L.head.asIdeal.LiesOver l.head.asIdeal := by
      constructor
      rw [← L.toList_getElem_zero_eq_head]; rw [← l.toList_getElem_zero_eq_head]; rw [Ideal.under_def]
      have : l.toList[0] = (PrimeSpectrum.comap (algebraMap R S)) L.toList[0] := by
        rw [List.getElem_map_rev (PrimeSpectrum.comap (algebraMap R S))]; rw [List.getElem_of_eq spec.symm _]
      rwa [PrimeSpectrum.ext_iff] at this
    obtain ⟨Q, Qlt, hQ, Qlo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt L.head.asIdeal lt
    use L.cons ⟨Q, hQ⟩ Qlt
    simp only [RelSeries.cons_length, add_left_inj, RelSeries.last_cons]
    exact ⟨len, last, by simpa [spec] using PrimeSpectrum.ext_iff.mpr Qlo.over.symm⟩

namespace Algebra.HasGoingDown

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` has the going down property if and only if generalizations lift
along `Spec S → Spec R`. -/
@[stacks 00HW "(1)"]
/--
lemma `iff_generalizingMap_primeSpectrumComap` / 引理 `iff_generalizingMap_primeSpectrumComap`

English:
lemma iff_generalizingMap_primeSpectrumComap
  proof: by
  refine ⟨?_, fun h => ⟨fun {p} hp Q hQ hlt => ?_⟩⟩
  · intro h Q p hp
    rw [← PrimeSpectrum.le_iff_specializes] at hp
    obtain ⟨P, hle, hP, h⟩ := Q.asIdeal.exists_ideal_le_liesOver_of_le (p := p.asIdeal)
      (q := Q.asIdeal.under R) hp
    refine ⟨⟨P, hP⟩, (PrimeSpectrum.le_iff_specializes

中文:
引理 iff_generalizingMap_primeSpectrumComap
  证明: by
  refine ⟨?_, fun h => ⟨fun {p} hp Q hQ hlt => ?_⟩⟩
  · intro h Q p hp
    rw [← PrimeSpectrum.le_iff_specializes] at hp
    obtain ⟨P, hle, hP, h⟩ := Q.asIdeal.exists_ideal_le_liesOver_of_le (p := p.asIdeal)
      (q := Q.asIdeal.under R) hp
    refine ⟨⟨P, hP⟩, (PrimeSpectrum.le_iff_specializes

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.le_iff_specializes, Q.asIdeal.exists_ideal_le_liesOver_of_le, Q.asIdeal.under, algebraMap, asIdeal, exists_ideal_le_liesOver_of_le, h.over.symm, hlt.le, le_iff_specializes, p.asIdeal
-/
lemma iff_generalizingMap_primeSpectrumComap :
    Algebra.HasGoingDown R S ↔
      GeneralizingMap (PrimeSpectrum.comap (algebraMap R S)) := by
  refine ⟨?_, fun h => ⟨fun {p} hp Q hQ hlt => ?_⟩⟩
  · intro h Q p hp
    rw [← PrimeSpectrum.le_iff_specializes] at hp
    obtain ⟨P, hle, hP, h⟩ := Q.asIdeal.exists_ideal_le_liesOver_of_le (p := p.asIdeal)
      (q := Q.asIdeal.under R) hp
    refine ⟨⟨P, hP⟩, (PrimeSpectrum.le_iff_specializes _ Q).mp hle, ?_⟩
    ext : 1
    exact h.over.symm
  · have : (⟨p, hp⟩ : PrimeSpectrum R) ⤳ (PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQ⟩) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hlt.le
    obtain ⟨P, hs, heq⟩ := h this
    refine ⟨P.asIdeal, (PrimeSpectrum.le_iff_specializes _ _).mpr hs, P.2, ⟨?_⟩⟩
    simpa [PrimeSpectrum.ext_iff] using heq.symm

variable (R S) in
@[stacks 00HX]
/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  proof: by
  rw [iff_generalizingMap_primeSpectrumComap]; rw [IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply GeneralizingMap.comp
  · rwa [← iff_generalizingMap_primeSpectrumComap]
  · rwa [← iff_generalizingMap_primeSpectrumComap]

中文:
引理 trans
  结论: (T : 类型) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  证明: by
  rw [iff_generalizingMap_primeSpectrumComap]; rw [IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply GeneralizingMap.comp
  · rwa [← iff_generalizingMap_primeSpectrumComap]
  · rwa [← iff_generalizingMap_primeSpectrumComap]

Depends on / 依赖: GeneralizingMap, GeneralizingMap.comp, IsScalarTower, IsScalarTower.algebraMap_eq, PrimeSpectrum, PrimeSpectrum.comap_comp, algebraMap_eq, comap_comp, iff_generalizingMap_primeSpectrumComap
-/
lemma trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.HasGoingDown R S] [Algebra.HasGoingDown S T] :
    Algebra.HasGoingDown R T := by
  rw [iff_generalizingMap_primeSpectrumComap]; rw [IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply GeneralizingMap.comp
  · rwa [← iff_generalizingMap_primeSpectrumComap]
  · rwa [← iff_generalizingMap_primeSpectrumComap]

/--
lemma `of_comap_localRingHom_surjective` / 引理 `of_comap_localRingHom_surjective`

English:
lemma of_comap_localRingHom_surjective
  proof: by
    let pl : Ideal (Localization.AtPrime <| Q.under R) := p.map (algebraMap R _)
    have : pl.IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime (Q.under R) hlt.le
    obtain ⟨⟨Pl, _⟩, hl⟩ := H Q ⟨pl, inferInstance⟩
    refine ⟨Pl.under S, ?_, Ideal.IsPrime.under S Pl, ⟨?_⟩⟩
    · exact

中文:
引理 of_comap_localRingHom_surjective
  证明: by
    let pl : Ideal (Localization.AtPrime <| Q.under R) := p.map (algebraMap R _)
    have : pl.IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime (Q.under R) hlt.le
    obtain ⟨⟨Pl, _⟩, hl⟩ := H Q ⟨pl, inferInstance⟩
    refine ⟨Pl.under S, ?_, Ideal.IsPrime.under S Pl, ⟨?_⟩⟩
    · exact

Depends on / 依赖: AtPrime, Ideal.IsPrime.under, Ideal.isPrime_map_of_isLocalizationAtPrime, Ideal.under_und, IsLocalization, IsLocalization.AtPrime.orderIsoOfPrime, IsPrime, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, Pl.under, PrimeSpectrum, PrimeSpectrum.ext_iff, Q.under, algebraMap, algebraOfLiesOver, ext_iff, hlt.le, isPrime_map_of_isLocalizationAtPrime, orderIsoOfPrime
-/
lemma of_comap_localRingHom_surjective
    (H : forall (P : Ideal S) [P.IsPrime], Function.Surjective
      (PrimeSpectrum.comap <| Localization.localRingHom (P.under R) P (algebraMap R S) rfl)) :
    Algebra.HasGoingDown R S where
  exists_ideal_le_liesOver_of_lt {p} _ Q _ hlt := by
    let pl : Ideal (Localization.AtPrime <| Q.under R) := p.map (algebraMap R _)
    have : pl.IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime (Q.under R) hlt.le
    obtain ⟨⟨Pl, _⟩, hl⟩ := H Q ⟨pl, inferInstance⟩
    refine ⟨Pl.under S, ?_, Ideal.IsPrime.under S Pl, ⟨?_⟩⟩
    · exact (IsLocalization.AtPrime.orderIsoOfPrime _ Q ⟨Pl, inferInstance⟩).2.2
    · let := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
      replace hl : Pl.under _ = pl := by simpa [PrimeSpectrum.ext_iff] using! hl
      rw [Ideal.under_under]; rw [← Ideal.under_under (B := (Localization.AtPrime <| Q.under R)) Pl]; rw [hl]; rw [Ideal.under_map_of_isLocalizationAtPrime (Q.under R) hlt.le]

/-- Flat algebras satisfy the going down property. -/
@[stacks 00HS]
/--
Instance `of_flat` / 实例 `of_flat`

English:
instance of_flat
  signature: [Module.Flat R S]
  body: by
  apply of_comap_localRingHom_surjective
  intro P hP
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : IsLocalHom (algebraMap (Localization.AtPrime <| P.under R) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRing

中文:
实例 of_flat
  签名: [Module.Flat R S]
  定义体: by
  apply of_comap_localRingHom_surjective
  intro P hP
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : IsLocalHom (algebraMap (Localization.AtPrime <| P.under R) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRing

Depends on / 依赖: AtPrime, FaithfullyFlat, Ideal.LiesOver.over, IsLocalHom, LiesOver, Localization, Localization.AtPrime, Localization.AtPrime.algebraOfLiesOver, Localization.isLocalHom_localRingHom, Module, Module.FaithfullyFlat, Module.FaithfullyFlat.of_flat_of_isLocalHom, P.under, PrimeSpectrum, PrimeSpectrum.comap, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_toAlgebra, algebraOfLiesOver
-/
instance of_flat [Module.Flat R S] : Algebra.HasGoingDown R S := by
  apply of_comap_localRingHom_surjective
  intro P hP
  let := Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have : IsLocalHom (algebraMap (Localization.AtPrime <| P.under R) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom (P.under R) P (algebraMap R S) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime (P.under R)) (Localization.AtPrime P) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply PrimeSpectrum.comap_surjective_of_faithfullyFlat

end Algebra.HasGoingDown
