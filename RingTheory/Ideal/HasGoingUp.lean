/-
Copyright (c) 2026 Robert Shlyakhtenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Shlyakhtenko
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Going up

In this file we define a predicate `Algebra.HasGoingUp`: An `R`-algebra `S` satisfies
`Algebra.HasGoingUp R S` if for every pair of prime ideals `p ≤ q` of `R` with
`P` a prime of `S` lying above `p`, there exists a prime `P ≤ Q` of `S` lying above `q`.

This file closely mirrors `Mathlib.RingTheory.Ideal.GoingDown`.

## Main results

- `Algebra.HasGoingUp.iff_specializingMap_primeSpectrumComap`: going up is equivalent
  to specializations lifting along `Spec S → Spec R`.
- `Algebra.HasGoingUp.of_isIntegral`: integral algebras satisfy going up.
-/

@[expose] public section

/--
An `R`-algebra `S` satisfies `Algebra.HasGoingUp R S` if for every pair of
prime ideals `p ≤ q` of `R` with `P` a prime of `S` lying above `p`, there exists a
prime `P ≤ Q` of `S` lying above `q`.

The condition only asks for `<` which is easier to prove, use
`Ideal.exists_ideal_ge_liesOver_of_le` for applying it. -/
@[stacks 00HV "(1)"]
/--
Definition of `Algebra.HasGoingUp` / `Algebra.HasGoingUp` 的定义

English:
class Algebra.HasGoingUp
  axioms and operations (1):
    - exists_ideal_ge_liesOver_of_lt({q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime]) : P.under R < q -> exists Q, P <= Q ∧ Q.IsPrime ∧ Q.LiesOver q

中文:
类 Algebra.HasGoingUp
  公理与运算 (1 个):
    - exists_ideal_ge_liesOver_of_lt({q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime]) : P.under R < q -> 存在 Q, P <= Q ∧ Q.IsPrime ∧ Q.LiesOver q
-/
class Algebra.HasGoingUp
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_ideal_ge_liesOver_of_lt {q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] :
    P.under R < q -> exists Q, P <= Q ∧ Q.IsPrime ∧ Q.LiesOver q

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Ideal

/--
lemma `exists_ideal_ge_liesOver_of_le` / 引理 `exists_ideal_ge_liesOver_of_le`

English:
lemma exists_ideal_ge_liesOver_of_le
  statement: [Algebra.HasGoingUp R S]
  proof: by
  rcases eq_or_ne p q with rfl | h
  · use P
  · rw [P.over_def p] at hle h
    exact Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt P (lt_of_le_of_ne hle h)

中文:
引理 exists_ideal_ge_liesOver_of_le
  结论: [Algebra.HasGoingUp R S]
  证明: by
  rcases eq_or_ne p q with rfl | h
  · use P
  · rw [P.over_def p] at hle h
    exact Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt P (lt_of_le_of_ne hle h)

Depends on / 依赖: Algebra, Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt, HasGoingUp, P.over_def, eq_or_ne, exists_ideal_ge_liesOver_of_lt, lt_of_le_of_ne, over_def
-/
lemma exists_ideal_ge_liesOver_of_le [Algebra.HasGoingUp R S]
    {p q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hle : p <= q) :
    exists Q, P <= Q ∧ Q.IsPrime ∧ Q.LiesOver q := by
  rcases eq_or_ne p q with rfl | h
  · use P
  · rw [P.over_def p] at hle h
    exact Algebra.HasGoingUp.exists_ideal_ge_liesOver_of_lt P (lt_of_le_of_ne hle h)

/--
lemma `exists_ideal_gt_liesOver_of_lt` / 引理 `exists_ideal_gt_liesOver_of_lt`

English:
lemma exists_ideal_gt_liesOver_of_lt
  statement: [Algebra.HasGoingUp R S]
  proof: by
  obtain ⟨Q, hPQ, hQ, hQq⟩ := P.exists_ideal_ge_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨Q, lt_of_le_of_ne hPQ fun h => ?_, hQ, hQq⟩
  subst Q
  simp [P.over_def p, P.over_def q] at hpq

中文:
引理 exists_ideal_gt_liesOver_of_lt
  结论: [Algebra.HasGoingUp R S]
  证明: by
  obtain ⟨Q, hPQ, hQ, hQq⟩ := P.exists_ideal_ge_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨Q, lt_of_le_of_ne hPQ fun h => ?_, hQ, hQq⟩
  subst Q
  simp [P.over_def p, P.over_def q] at hpq

Depends on / 依赖: P.exists_ideal_ge_liesOver_of_le, P.over_def, exists_ideal_ge_liesOver_of_le, hpq.le, lt_of_le_of_ne, over_def
-/
lemma exists_ideal_gt_liesOver_of_lt [Algebra.HasGoingUp R S]
    {p q : Ideal R} [q.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hpq : p < q) :
    exists Q, P < Q ∧ Q.IsPrime ∧ Q.LiesOver q := by
  obtain ⟨Q, hPQ, hQ, hQq⟩ := P.exists_ideal_ge_liesOver_of_le (p := p) (q := q) hpq.le
  refine ⟨Q, lt_of_le_of_ne hPQ fun h => ?_, hQ, hQq⟩
  subst Q
  simp [P.over_def p, P.over_def q] at hpq

/--
lemma `exists_ltSeries_of_hasGoingUp` / 引理 `exists_ltSeries_of_hasGoingUp`

English:
lemma exists_ltSeries_of_hasGoingUp
  statement: [Algebra.HasGoingUp R S]
  proof: by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    refine ⟨RelSeries.singleton _ ⟨P, inferInstance⟩, rfl, rfl, ?_⟩
    simpa [PrimeSpectrum.ext_iff] using lo.over.symm
  | cons l q lt ih =>
    simp only [RelSeries.head_cons] at lo
    obtain ⟨Q, PQlt, hQ, Qlo⟩ :

中文:
引理 exists_ltSeries_of_hasGoingUp
  结论: [Algebra.HasGoingUp R S]
  证明: by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    refine ⟨RelSeries.singleton _ ⟨P, inferInstance⟩, rfl, rfl, ?_⟩
    simpa [PrimeSpectrum.ext_iff] using lo.over.symm
  | cons l q lt ih =>
    simp only [RelSeries.head_cons] at lo
    obtain ⟨Q, PQlt, hQ, Qlo⟩ :

Depends on / 依赖: Ideal.exists_ideal_gt_liesOver_of_lt, L.cons, PrimeSpectrum, PrimeSpectrum.e, PrimeSpectrum.ext_iff, RelSeries, RelSeries.head_cons, RelSeries.inductionOn, RelSeries.singleton, Set.mem_ofPred_eq, exists_ideal_gt_liesOver_of_lt, ext_iff, generalizing, head_cons, inductionOn, lo.over.symm, mem_ofPred_eq, singleton
-/
lemma exists_ltSeries_of_hasGoingUp [Algebra.HasGoingUp R S]
    (l : LTSeries (PrimeSpectrum R))
    (P : Ideal S) [P.IsPrime]
    [lo : P.LiesOver (RelSeries.head l).asIdeal] :
    exists L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧
      L.head = (⟨P, inferInstance⟩ : PrimeSpectrum S) ∧
      List.map (PrimeSpectrum.comap (algebraMap R S)) (L.toList) = l.toList := by
  induction l using RelSeries.inductionOn generalizing P with
  | singleton q =>
    refine ⟨RelSeries.singleton _ ⟨P, inferInstance⟩, rfl, rfl, ?_⟩
    simpa [PrimeSpectrum.ext_iff] using lo.over.symm
  | cons l q lt ih =>
    simp only [RelSeries.head_cons] at lo
    obtain ⟨Q, PQlt, hQ, Qlo⟩ :=
      Ideal.exists_ideal_gt_liesOver_of_lt P lt
    obtain ⟨L, len, head, spec⟩ := ih Q
    refine ⟨L.cons ⟨P, inferInstance⟩ (by
      simp_all only [Set.mem_ofPred_eq]
      exact PQlt), by simpa using len, rfl, ?_⟩
    simpa [spec, PrimeSpectrum.ext_iff] using lo.over.symm

end Ideal

namespace Algebra.HasGoingUp

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` has the going up property if and only if specializations lift
along `Spec S → Spec R`. -/
@[stacks 00HW "(2)"]
/--
lemma `iff_specializingMap_primeSpectrumComap` / 引理 `iff_specializingMap_primeSpectrumComap`

English:
lemma iff_specializingMap_primeSpectrumComap
  proof: by
  refine ⟨?_, fun h => ⟨fun {q} hq P hP hlt => ?_⟩⟩
  · intro h P q hq
    simp only [flip] at hq
    rw [← PrimeSpectrum.le_iff_specializes] at hq
    obtain ⟨Q, hle, hQ, h⟩ := P.asIdeal.exists_ideal_ge_liesOver_of_le (q := q.asIdeal)
      (p := P.asIdeal.under R) hq
    refine ⟨⟨Q, hQ⟩, (Prime

中文:
引理 iff_specializingMap_primeSpectrumComap
  证明: by
  refine ⟨?_, fun h => ⟨fun {q} hq P hP hlt => ?_⟩⟩
  · intro h P q hq
    simp only [flip] at hq
    rw [← PrimeSpectrum.le_iff_specializes] at hq
    obtain ⟨Q, hle, hQ, h⟩ := P.asIdeal.exists_ideal_ge_liesOver_of_le (q := q.asIdeal)
      (p := P.asIdeal.under R) hq
    refine ⟨⟨Q, hQ⟩, (Prime

Depends on / 依赖: P.asIdeal.exists_ideal_ge_liesOver_of_le, P.asIdeal.under, PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.le_iff_specializes, algebraMap, asIdeal, exists_ideal_ge_liesOver_of_le, h.over.symm, hlt.le, le_iff_specializes, q.asIdeal
-/
lemma iff_specializingMap_primeSpectrumComap :
    Algebra.HasGoingUp R S ↔
      SpecializingMap (PrimeSpectrum.comap (algebraMap R S)) := by
  refine ⟨?_, fun h => ⟨fun {q} hq P hP hlt => ?_⟩⟩
  · intro h P q hq
    simp only [flip] at hq
    rw [← PrimeSpectrum.le_iff_specializes] at hq
    obtain ⟨Q, hle, hQ, h⟩ := P.asIdeal.exists_ideal_ge_liesOver_of_le (q := q.asIdeal)
      (p := P.asIdeal.under R) hq
    refine ⟨⟨Q, hQ⟩, (PrimeSpectrum.le_iff_specializes P _).mp hle, ?_⟩
    ext : 1
    exact h.over.symm
  · have : PrimeSpectrum.comap (algebraMap R S) ⟨P, hP⟩ ⤳ (⟨q, hq⟩ : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hlt.le
    obtain ⟨Q, hs, heq⟩ := h this
    refine ⟨Q.asIdeal, (PrimeSpectrum.le_iff_specializes _ _).mpr hs, Q.2, ⟨?_⟩⟩
    simpa [PrimeSpectrum.ext_iff] using heq.symm

variable (R S) in
@[stacks 00HX]
/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  statement: (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  proof: by
  rw [iff_specializingMap_primeSpectrumComap]; rw [IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply SpecializingMap.comp
  · rwa [← iff_specializingMap_primeSpectrumComap]
  · rwa [← iff_specializingMap_primeSpectrumComap]

中文:
引理 trans
  结论: (T : 类型) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  证明: by
  rw [iff_specializingMap_primeSpectrumComap]; rw [IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply SpecializingMap.comp
  · rwa [← iff_specializingMap_primeSpectrumComap]
  · rwa [← iff_specializingMap_primeSpectrumComap]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, PrimeSpectrum, PrimeSpectrum.comap_comp, SpecializingMap, SpecializingMap.comp, algebraMap_eq, comap_comp, iff_specializingMap_primeSpectrumComap
-/
lemma trans (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.HasGoingUp R S] [Algebra.HasGoingUp S T] :
    Algebra.HasGoingUp R T := by
  rw [iff_specializingMap_primeSpectrumComap]; rw [IsScalarTower.algebraMap_eq R S T]
  simp only [PrimeSpectrum.comap_comp]
  apply SpecializingMap.comp
  · rwa [← iff_specializingMap_primeSpectrumComap]
  · rwa [← iff_specializingMap_primeSpectrumComap]

/-- Integral algebras satisfy the going up property. -/
@[stacks 00GU]
/--
Instance `of_isIntegral` / 实例 `of_isIntegral`

English:
instance of_isIntegral
  signature: [Algebra.IsIntegral R S]
  body: let ⟨Q, hPQ, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime q P hPq.le
    ⟨Q, hPQ, hQ, ⟨hQq.symm⟩⟩

中文:
实例 of_isIntegral
  签名: [Algebra.Is整数egral R S]
  定义体: let ⟨Q, hPQ, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime q P hPq.le
    ⟨Q, hPQ, hQ, ⟨hQq.symm⟩⟩

Depends on / 依赖: Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime, exists_ideal_over_prime_of_isIntegral_of_isPrime, hPq.le, hQq.symm
-/
instance of_isIntegral [Algebra.IsIntegral R S] : Algebra.HasGoingUp R S where
  exists_ideal_ge_liesOver_of_lt {q} _ P _ hPq :=
    let ⟨Q, hPQ, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime q P hPq.le
    ⟨Q, hPQ, hQ, ⟨hQq.symm⟩⟩

end Algebra.HasGoingUp
