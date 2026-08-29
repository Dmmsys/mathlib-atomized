/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# Minimal polynomial of roots of unity

We gather several results about minimal polynomial of root of unity.

## Main results

* `IsPrimitiveRoot.totient_le_degree_minpoly`: The degree of the minimal polynomial of an `n`-th
  primitive root of unity is at least `totient n`.

-/

public section


open minpoly Polynomial

open scoped Polynomial

namespace IsPrimitiveRoot

section CommRing

variable {n : Nat} {K : Type*} [CommRing K] {μ : K} (h : IsPrimitiveRoot μ n)
include h

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  given: (hpos : 0 < n)
  statement: IsIntegral Int μ
  proof: by
  use X ^ n - 1
  constructor
  · exact monic_X_pow_sub_C 1 (ne_of_lt hpos).symm
  · simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self]

中文:
定理 is整数egral
  条件: (hpos : 0 < n)
  结论: 是整 整数 μ
  证明: by
  use X ^ n - 1
  constructor
  · exact monic_X_pow_sub_C 1 (ne_of_lt hpos).symm
  · simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self]

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.iff_def, iff_def, monic_X_pow_sub_C, ne_of_lt, sub_self
-/
theorem isIntegral (hpos : 0 < n) : IsIntegral Int μ := by
  use X ^ n - 1
  constructor
  · exact monic_X_pow_sub_C 1 (ne_of_lt hpos).symm
  · simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self]

section IsDomain

variable [IsDomain K] [CharZero K]

/--
theorem `minpoly_dvd_x_pow_sub_one` / 定理 `minpoly_dvd_x_pow_sub_one`

English:
theorem minpoly_dvd_x_pow_sub_one
  statement: minpoly Int μ ∣ X ^ n - 1
  proof: by
  rcases n.eq_zero_or_pos with (rfl | h0)
  · simp
  apply minpoly.isIntegrallyClosed_dvd (isIntegral h h0)
  simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, aeval_X_pow,
    aeval_one, map_sub, sub_self]

中文:
定理 minpoly_dvd_x_pow_sub_one
  结论: minpoly 整数 μ ∣ X ^ n - 1
  证明: by
  rcases n.eq_zero_or_pos with (rfl | h0)
  · simp
  apply minpoly.isIntegrallyClosed_dvd (isIntegral h h0)
  simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, aeval_X_pow,
    aeval_one, map_sub, sub_self]

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.iff_def, aeval_X_pow, aeval_one, eq_zero_or_pos, iff_def, isIntegral, isIntegrallyClosed_dvd, map_sub, minpoly, minpoly.isIntegrallyClosed_dvd, n.eq_zero_or_pos, sub_self
-/
theorem minpoly_dvd_x_pow_sub_one : minpoly Int μ ∣ X ^ n - 1 := by
  rcases n.eq_zero_or_pos with (rfl | h0)
  · simp
  apply minpoly.isIntegrallyClosed_dvd (isIntegral h h0)
  simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, aeval_X_pow,
    aeval_one, map_sub, sub_self]

/--
theorem `separable_minpoly_mod` / 定理 `separable_minpoly_mod`

English:
theorem separable_minpoly_mod
  given: {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n)
  proof: by
  have hdvd : map (Int.castRingHom (ZMod p)) (minpoly Int μ) ∣ X ^ n - 1 := by
    convert! _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p))) (minpoly_dvd_x_pow_sub_one h)
    simp only [map_sub, map_pow, coe_mapRingHom, map_X, map_one]
  refine Separable.of_dvd (separable_X_pow_sub_C 1 ?_ o

中文:
定理 separable_minpoly_mod
  条件: {p : 自然数} [Fact p.素] (hdiv : ¬p ∣ n)
  证明: by
  have hdvd : map (Int.castRingHom (ZMod p)) (minpoly Int μ) ∣ X ^ n - 1 := by
    convert! _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p))) (minpoly_dvd_x_pow_sub_one h)
    simp only [map_sub, map_pow, coe_mapRingHom, map_X, map_one]
  refine Separable.of_dvd (separable_X_pow_sub_C 1 ?_ o

Depends on / 依赖: Int.castRingHom, Separable, Separable.of_dvd, ZMod.natCast_eq_zero_iff, _root_, _root_.map_dvd, castRingHom, coe_mapRingHom, convert, mapRingHom, map_X, map_dvd, map_one, map_pow, map_sub, minpoly, minpoly_dvd_x_pow_sub_one, natCast_eq_zero_iff, of_dvd, one_ne_zero
-/
theorem separable_minpoly_mod {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Separable (map (Int.castRingHom (ZMod p)) (minpoly Int μ)) := by
  have hdvd : map (Int.castRingHom (ZMod p)) (minpoly Int μ) ∣ X ^ n - 1 := by
    convert! _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p))) (minpoly_dvd_x_pow_sub_one h)
    simp only [map_sub, map_pow, coe_mapRingHom, map_X, map_one]
  refine Separable.of_dvd (separable_X_pow_sub_C 1 ?_ one_ne_zero) hdvd
  by_contra hzero
  exact hdiv ((ZMod.natCast_eq_zero_iff n p).1 hzero)

/--
theorem `squarefree_minpoly_mod` / 定理 `squarefree_minpoly_mod`

English:
theorem squarefree_minpoly_mod
  given: {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n)
  proof: (separable_minpoly_mod h hdiv).squarefree

中文:
定理 squarefree_minpoly_mod
  条件: {p : 自然数} [Fact p.素] (hdiv : ¬p ∣ n)
  证明: (separable_minpoly_mod h hdiv).squarefree

Depends on / 依赖: separable_minpoly_mod, squarefree
-/
theorem squarefree_minpoly_mod {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Squarefree (map (Int.castRingHom (ZMod p)) (minpoly Int μ)) :=
  (separable_minpoly_mod h hdiv).squarefree

/--
theorem `minpoly_dvd_expand` / 定理 `minpoly_dvd_expand`

English:
theorem minpoly_dvd_expand
  given: {p : Nat} (hdiv : ¬p ∣ n)
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp_all
  let : IsIntegrallyClosed Int := GCDMonoid.toIsIntegrallyClosed
  refine minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos) ?_
  rw [aeval_def]; rw [coe_expand]; rw [← comp]; rw [eval₂_eq_eval_map]; rw [map_comp]; rw [Polynomial.map_pow]; 

中文:
定理 minpoly_dvd_expand
  条件: {p : 自然数} (hdiv : ¬p ∣ n)
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp_all
  let : IsIntegrallyClosed Int := GCDMonoid.toIsIntegrallyClosed
  refine minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos) ?_
  rw [aeval_def]; rw [coe_expand]; rw [← comp]; rw [eval₂_eq_eval_map]; rw [map_comp]; rw [Polynomial.map_pow]; 

Depends on / 依赖: GCDMonoid, GCDMonoid.toIsIntegrallyClosed, IsIntegrallyClosed, Polynomial, Polynomial.map_pow, aeval_def, coe_expand, eq_zero_or_pos, eval_X_pow, eval_comp, h.isIntegral, isIntegral, isIntegrallyClosed_dvd, map_X, map_comp, map_pow, minpoly, minpoly.aeval, minpoly.isIntegrallyClosed_dvd, n.eq_zero_or_pos
-/
theorem minpoly_dvd_expand {p : Nat} (hdiv : ¬p ∣ n) :
    minpoly Int μ ∣ expand Int p (minpoly Int (μ ^ p)) := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp_all
  let : IsIntegrallyClosed Int := GCDMonoid.toIsIntegrallyClosed
  refine minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos) ?_
  rw [aeval_def]; rw [coe_expand]; rw [← comp]; rw [eval₂_eq_eval_map]; rw [map_comp]; rw [Polynomial.map_pow]; rw [map_X]; rw [eval_comp]; rw [eval_X_pow]; rw [← eval₂_eq_eval_map]; rw [← aeval_def]
  exact minpoly.aeval _ _

/--
theorem `minpoly_dvd_pow_mod` / 定理 `minpoly_dvd_pow_mod`

English:
theorem minpoly_dvd_pow_mod
  given: {p : Nat} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n)
  proof: by
  set Q := minpoly Int (μ ^ p)
  have hfrob :
    map (Int.castRingHom (ZMod p)) Q ^ p = map (Int.castRingHom (ZMod p)) (expand Int p Q) := by
    rw [← ZMod.expand_card]; rw [map_expand]
  rw [hfrob]
  apply _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
  exact minpoly_dvd_expand h hdiv

中文:
定理 minpoly_dvd_pow_mod
  条件: {p : 自然数} [hprime : Fact p.素] (hdiv : ¬p ∣ n)
  证明: by
  set Q := minpoly Int (μ ^ p)
  have hfrob :
    map (Int.castRingHom (ZMod p)) Q ^ p = map (Int.castRingHom (ZMod p)) (expand Int p Q) := by
    rw [← ZMod.expand_card]; rw [map_expand]
  rw [hfrob]
  apply _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
  exact minpoly_dvd_expand h hdiv

Depends on / 依赖: Int.castRingHom, ZMod.expand_card, _root_, _root_.map_dvd, castRingHom, expand, expand_card, mapRingHom, map_dvd, map_expand, minpoly, minpoly_dvd_expand
-/
theorem minpoly_dvd_pow_mod {p : Nat} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly Int μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly Int (μ ^ p)) ^ p := by
  set Q := minpoly Int (μ ^ p)
  have hfrob :
    map (Int.castRingHom (ZMod p)) Q ^ p = map (Int.castRingHom (ZMod p)) (expand Int p Q) := by
    rw [← ZMod.expand_card]; rw [map_expand]
  rw [hfrob]
  apply _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
  exact minpoly_dvd_expand h hdiv

/--
theorem `minpoly_dvd_mod_p` / 定理 `minpoly_dvd_mod_p`

English:
theorem minpoly_dvd_mod_p
  given: {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n)
  proof: (squarefree_minpoly_mod h hdiv).isRadical _ _ (minpoly_dvd_pow_mod h hdiv)

中文:
定理 minpoly_dvd_mod_p
  条件: {p : 自然数} [Fact p.素] (hdiv : ¬p ∣ n)
  证明: (squarefree_minpoly_mod h hdiv).isRadical _ _ (minpoly_dvd_pow_mod h hdiv)

Depends on / 依赖: isRadical, minpoly_dvd_pow_mod, squarefree_minpoly_mod
-/
theorem minpoly_dvd_mod_p {p : Nat} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly Int μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly Int (μ ^ p)) :=
  (squarefree_minpoly_mod h hdiv).isRadical _ _ (minpoly_dvd_pow_mod h hdiv)

/--
theorem `minpoly_eq_pow` / 定理 `minpoly_eq_pow`

English:
theorem minpoly_eq_pow
  given: {p : Nat} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n)
  proof: by
  by_cases hn : n = 0
  · simp_all
  have hpos := Nat.pos_of_ne_zero hn
  by_contra hdiff
  set P := minpoly Int μ
  set Q := minpoly Int (μ ^ p)
  have Pmonic : P.Monic := minpoly.monic (h.isIntegral hpos)
  have Qmonic : Q.Monic := minpoly.monic ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)


中文:
定理 minpoly_eq_pow
  条件: {p : 自然数} [hprime : Fact p.素] (hdiv : ¬p ∣ n)
  证明: by
  by_cases hn : n = 0
  · simp_all
  have hpos := Nat.pos_of_ne_zero hn
  by_contra hdiff
  set P := minpoly Int μ
  set Q := minpoly Int (μ ^ p)
  have Pmonic : P.Monic := minpoly.monic (h.isIntegral hpos)
  have Qmonic : Q.Monic := minpoly.monic ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)


Depends on / 依赖: Irreducible, IsPrimitive, Nat.pos_of_ne_zero, P.Monic, PQprim, Pmonic, Pmonic.isPri, Q.Monic, Qmonic, h.isIntegral, h.pow_of_prime, hprime, irreducible, isIntegral, minpoly, minpoly.irreducible, minpoly.monic, pos_of_ne_zero, pow_of_prime
-/
theorem minpoly_eq_pow {p : Nat} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    minpoly Int μ = minpoly Int (μ ^ p) := by
  by_cases hn : n = 0
  · simp_all
  have hpos := Nat.pos_of_ne_zero hn
  by_contra hdiff
  set P := minpoly Int μ
  set Q := minpoly Int (μ ^ p)
  have Pmonic : P.Monic := minpoly.monic (h.isIntegral hpos)
  have Qmonic : Q.Monic := minpoly.monic ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)
  have Pirr : Irreducible P := minpoly.irreducible (h.isIntegral hpos)
  have Qirr : Irreducible Q := minpoly.irreducible ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)
  have PQprim : IsPrimitive (P * Q) := Pmonic.isPrimitive.mul Qmonic.isPrimitive
  have prod : P * Q ∣ X ^ n - 1 := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (P * Q) (X ^ n - 1) PQprim]; rw [Polynomial.map_mul]
    refine IsCoprime.mul_dvd ?_ ?_ ?_
    · have aux := IsPrimitive.Int.irreducible_iff_irreducible_map_cast Pmonic.isPrimitive
      refine (dvd_or_isCoprime _ _ (aux.1 Pirr)).resolve_left ?_
      rw [map_dvd_map (Int.castRingHom Rat) Int.cast_injective Pmonic]
      intro hdiv
      refine hdiff (eq_of_monic_of_associated Pmonic Qmonic ?_)
      exact associated_of_dvd_dvd hdiv (Pirr.dvd_symm Qirr hdiv)
    · apply (map_dvd_map (Int.castRingHom Rat) Int.cast_injective Pmonic).2
      exact minpoly_dvd_x_pow_sub_one h
    · apply (map_dvd_map (Int.castRingHom Rat) Int.cast_injective Qmonic).2
      exact minpoly_dvd_x_pow_sub_one (pow_of_prime h hprime.1 hdiv)
  replace prod := _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p))) prod
  rw [coe_mapRingHom]; rw [Polynomial.map_mul]; rw [Polynomial.map_sub]; rw [Polynomial.map_one]; rw [Polynomial.map_pow]; rw [map_X] at prod
  obtain ⟨R, hR⟩ := minpoly_dvd_mod_p h hdiv
  rw [hR]; rw [← mul_assoc]; rw [← Polynomial.map_mul]; rw [← sq]; rw [Polynomial.map_pow] at prod
  have habs : map (Int.castRingHom (ZMod p)) P ^ 2 ∣ map (Int.castRingHom (ZMod p)) P ^ 2 * R := by
    use R
  replace habs :=
    lt_of_lt_of_le (Nat.cast_lt.2 one_lt_two)
      (le_emultiplicity_of_pow_dvd (dvd_trans habs prod))
  have hfree : Squarefree (X ^ n - 1 : (ZMod p)[X]) :=
    (separable_X_pow_sub_C 1 (fun h => hdiv <| (ZMod.natCast_eq_zero_iff n p).1 h)
        one_ne_zero).squarefree
  rcases (squarefree_iff_emultiplicity_le_one (X ^ n - 1)).1 hfree
      (map (Int.castRingHom (ZMod p)) P) with hle | hunit
  · rw [Nat.cast_one] at habs; exact hle.not_gt habs
  · replace hunit := degree_eq_zero_of_isUnit hunit
    rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom (ZMod p)) _] at hunit
    · exact (minpoly.degree_pos (isIntegral h hpos)).ne' hunit
    simp only [Pmonic, eq_intCast, Monic.leadingCoeff, Int.cast_one, Ne, not_false_iff,
      one_ne_zero]

/--
theorem `minpoly_eq_pow_coprime` / 定理 `minpoly_eq_pow_coprime`

English:
theorem minpoly_eq_pow_coprime
  given: {m : Nat} (hcop : Nat.Coprime m n)
  proof: by
  revert n hcop
  refine UniqueFactorizationMonoid.induction_on_prime m ?_ ?_ ?_
  · intro h hn
    congr
    simpa [(Nat.coprime_zero_left _).mp hn] using h
  · intro u hunit _ _
    congr
    simp [Nat.isUnit_iff.mp hunit]
  · intro a p _ hprime hind h hcop
    rw [hind h (Nat.Coprime.coprime_m

中文:
定理 minpoly_eq_pow_coprime
  条件: {m : 自然数} (hcop : 自然数.Coprime m n)
  证明: by
  revert n hcop
  refine UniqueFactorizationMonoid.induction_on_prime m ?_ ?_ ?_
  · intro h hn
    congr
    simpa [(Nat.coprime_zero_left _).mp hn] using h
  · intro u hunit _ _
    congr
    simp [Nat.isUnit_iff.mp hunit]
  · intro a p _ hprime hind h hcop
    rw [hind h (Nat.Coprime.coprime_m

Depends on / 依赖: Coprime, Fact.mk, Nat.Coprime.co, Nat.Coprime.coprime_mul_left, Nat.Coprime.coprime_mul_right, Nat.Prime.coprime_iff_not_dvd, Nat.coprime_zero_left, Nat.isUnit_iff.mp, UniqueFactorizationMonoid, UniqueFactorizationMonoid.induction_on_prime, coprime_iff_not_dvd, coprime_mul_left, coprime_mul_right, coprime_zero_left, h.pow_of_coprime, hprime, hprime.nat_prime, induction_on_prime, isUnit_iff, minpoly_eq_pow
-/
theorem minpoly_eq_pow_coprime {m : Nat} (hcop : Nat.Coprime m n) :
    minpoly Int μ = minpoly Int (μ ^ m) := by
  revert n hcop
  refine UniqueFactorizationMonoid.induction_on_prime m ?_ ?_ ?_
  · intro h hn
    congr
    simpa [(Nat.coprime_zero_left _).mp hn] using h
  · intro u hunit _ _
    congr
    simp [Nat.isUnit_iff.mp hunit]
  · intro a p _ hprime hind h hcop
    rw [hind h (Nat.Coprime.coprime_mul_left hcop)]; clear hind
    replace hprime := hprime.nat_prime
    have hdiv := (Nat.Prime.coprime_iff_not_dvd hprime).1 (Nat.Coprime.coprime_mul_right hcop)
    have := Fact.mk hprime
    rw [minpoly_eq_pow (h.pow_of_coprime a (Nat.Coprime.coprime_mul_left hcop)) hdiv]
    congr 1
    ring

/--
theorem `pow_isRoot_minpoly` / 定理 `pow_isRoot_minpoly`

English:
theorem pow_isRoot_minpoly
  given: {m : Nat} (hcop : Nat.Coprime m n)
  proof: by
  simp only [minpoly_eq_pow_coprime h hcop, IsRoot.def, eval_map]
  exact minpoly.aeval Int (μ ^ m)

中文:
定理 pow_isRoot_minpoly
  条件: {m : 自然数} (hcop : 自然数.Coprime m n)
  证明: by
  simp only [minpoly_eq_pow_coprime h hcop, IsRoot.def, eval_map]
  exact minpoly.aeval Int (μ ^ m)

Depends on / 依赖: IsRoot, IsRoot.def, eval_map, minpoly, minpoly.aeval, minpoly_eq_pow_coprime
-/
theorem pow_isRoot_minpoly {m : Nat} (hcop : Nat.Coprime m n) :
    IsRoot (map (Int.castRingHom K) (minpoly Int μ)) (μ ^ m) := by
  simp only [minpoly_eq_pow_coprime h hcop, IsRoot.def, eval_map]
  exact minpoly.aeval Int (μ ^ m)

/--
theorem `is_roots_of_minpoly` / 定理 `is_roots_of_minpoly`

English:
theorem is_roots_of_minpoly
  given: [DecidableEq K]
  proof: by
  by_cases hn : n = 0; · simp_all
  have : NeZero n := ⟨hn⟩
  have hpos := Nat.pos_of_ne_zero hn
  intro x hx
  obtain ⟨m, _, hcop, rfl⟩ := (isPrimitiveRoot_iff h).1 ((mem_primitiveRoots hpos).1 hx)
  simp only [Multiset.mem_toFinset]
  convert! pow_isRoot_minpoly h hcop using 0
  rw [← mem_roots

中文:
定理 is_roots_of_minpoly
  条件: [DecidableEq K]
  证明: by
  by_cases hn : n = 0; · simp_all
  have : NeZero n := ⟨hn⟩
  have hpos := Nat.pos_of_ne_zero hn
  intro x hx
  obtain ⟨m, _, hcop, rfl⟩ := (isPrimitiveRoot_iff h).1 ((mem_primitiveRoots hpos).1 hx)
  simp only [Multiset.mem_toFinset]
  convert! pow_isRoot_minpoly h hcop using 0
  rw [← mem_roots

Depends on / 依赖: Multiset, Multiset.mem_toFinset, Nat.pos_of_ne_zero, NeZero, convert, isIntegral, isPrimitiveRoot_iff, map_monic_ne_zero, mem_primitiveRoots, mem_roots, mem_toFinset, minpoly, minpoly.monic, pos_of_ne_zero, pow_isRoot_minpoly
-/
theorem is_roots_of_minpoly [DecidableEq K] :
    primitiveRoots n K subseteq (map (Int.castRingHom K) (minpoly Int μ)).roots.toFinset := by
  by_cases hn : n = 0; · simp_all
  have : NeZero n := ⟨hn⟩
  have hpos := Nat.pos_of_ne_zero hn
  intro x hx
  obtain ⟨m, _, hcop, rfl⟩ := (isPrimitiveRoot_iff h).1 ((mem_primitiveRoots hpos).1 hx)
  simp only [Multiset.mem_toFinset]
  convert! pow_isRoot_minpoly h hcop using 0
  rw [← mem_roots]
exact map_monic_ne_zero minpoly.monic isIntegral h hpos

/--
theorem `totient_le_degree_minpoly` / 定理 `totient_le_degree_minpoly`

English:
theorem totient_le_degree_minpoly
  statement: Nat.totient n <= (minpoly Int μ).natDegree
  proof: by
  classical
  let P : Int[X] := minpoly Int μ
  -- minimal polynomial of `μ`
  let P_K : K[X] := map (Int.castRingHom K) P
  -- minimal polynomial of `μ` sent to `K[X]`
  calc
    n.totient = (primitiveRoots n K).card := h.card_primitiveRoots.symm
    _ <= P_K.roots.toFinset.card := Finset.card_l

中文:
定理 totient_le_degree_minpoly
  结论: 自然数.totient n <= (minpoly 整数 μ).natDegree
  证明: by
  classical
  let P : Int[X] := minpoly Int μ
  -- minimal polynomial of `μ`
  let P_K : K[X] := map (Int.castRingHom K) P
  -- minimal polynomial of `μ` sent to `K[X]`
  calc
    n.totient = (primitiveRoots n K).card := h.card_primitiveRoots.symm
    _ <= P_K.roots.toFinset.card := Finset.card_l

Depends on / 依赖: CompactSpace, Subsingleton, Subsingleton.compactSpace, classical, compactSpace, minpoly
-/
theorem totient_le_degree_minpoly : Nat.totient n <= (minpoly Int μ).natDegree := by
  classical
  let P : Int[X] := minpoly Int μ
  -- minimal polynomial of `μ`
  let P_K : K[X] := map (Int.castRingHom K) P
  -- minimal polynomial of `μ` sent to `K[X]`
  calc
    n.totient = (primitiveRoots n K).card := h.card_primitiveRoots.symm
    _ <= P_K.roots.toFinset.card := Finset.card_le_card (is_roots_of_minpoly h)
    _ <= Multiset.card P_K.roots := Multiset.toFinset_card_le _
    _ <= P_K.natDegree := card_roots' _
    _ <= P.natDegree := natDegree_map_le

end IsDomain

end CommRing

end IsPrimitiveRoot
