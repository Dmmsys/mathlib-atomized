/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Invariant.Defs

/-!
# Invariant Extensions of Rings

Given an extension of rings `B/A` and an action of `G` on `B`, we introduce a predicate
`Algebra.IsInvariant A B G` which states that every fixed point of `B` lies in the image of `A`.

The main application is in algebraic number theory, where `G := Gal(L/K)` is the Galois group
of some finite Galois extension of number fields, and `A := 𝓞K` and `B := 𝓞L` are their ring of
integers. This main result in this file implies the existence of Frobenius elements in this setting.
See `Mathlib/RingTheory/Frobenius.lean`.

## Main statements

Let `G` be a finite group acting on a commutative ring `B` satisfying `Algebra.IsInvariant A B G`.

* `Algebra.IsInvariant.isIntegral`: `B/A` is an integral extension.
* `Algebra.IsInvariant.exists_smul_of_under_eq`: `G` acts transitivity on the prime ideals of `B`
  lying above a given prime ideal of `A`.

If `Q` is a prime ideal of `B` lying over a prime ideal `P` of `A`, then

* `IsFractionRing.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut(Frac(B/Q)/Frac(A/P))`.
* `Ideal.Quotient.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.
* `Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under`:
  If `k` is a domain containing `B/Q`, then any `A/P`-algebra automorphism of `k` restricts to
  an automorphism of `B/Q`.
-/

@[expose] public section

-- this file should not import any field theory beyond the contents of `FieldTheory/Fixed.lean`
-- material involving Galois theory should be placed in `RingTheory/Invariant/Galois.lean`
assert_not_exists IntermediateField.adjoin

open scoped Pointwise

section Quotient

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

set_option backward.isDefEq.respectTransparency.types false in
instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subring B H) where
  smul := Quotient.lift (fun g x => ⟨g • x, fun h => by
    simpa [mul_smul] using! congr(g • $(x.2 ⟨_, ‹H.Normal›.conj_mem' _ h.2 g⟩))⟩) (by
    rintro _ a ⟨⟨⟨b⟩, hb⟩, rfl⟩
    ext c
    simpa [mul_smul] using! congr(a • $(c.2 ⟨b, hb⟩)))
  one_smul b := Subtype.ext (one_smul G b.1)
  mul_smul := Quotient.ind₂ fun _ _ _ => Subtype.ext (mul_smul _ _ _)
  smul_zero := Quotient.ind fun _ => Subtype.ext (smul_zero _)
  smul_add := Quotient.ind fun _ _ _ => Subtype.ext (smul_add _ _ _)
  smul_one := Quotient.ind fun _ => Subtype.ext (smul_one _)
  smul_mul := Quotient.ind fun _ _ _ => Subtype.ext (MulSemiringAction.smul_mul _ _ _)

instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  inferInstanceAs (MulSemiringAction (G ⧸ H) (FixedPoints.subring B H))

set_option backward.isDefEq.respectTransparency.types false in
instance (H : Subgroup G) [H.Normal] :
    SMulCommClass (G ⧸ H) A (FixedPoints.subalgebra A B H) where
  smul_comm := Quotient.ind fun g r h => Subtype.ext (smul_comm g r h.1)

set_option backward.isDefEq.respectTransparency.types false in
instance (H : Subgroup G) [H.Normal] [Algebra.IsInvariant A B G] :
    Algebra.IsInvariant A (FixedPoints.subalgebra A B H) (G ⧸ H) where
  isInvariant x hx := by
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) x.1
      (fun g => congr_arg Subtype.val (hx g))
    exact ⟨y, Subtype.ext hy⟩

end Quotient

section transitivity

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

namespace MulSemiringAction

open Polynomial

variable {B} [Fintype G]

/--
Definition of `charpoly` / `charpoly` 的定义

English:
definition charpoly
  signature: (b : B)
  body: ∏ g : G, (X - C (g • b))

中文:
定义 charpoly
  签名: (b : B)
  定义体: ∏ g : G, (X - C (g • b))
-/
noncomputable def charpoly (b : B) : B[X] := ∏ g : G, (X - C (g • b))

/--
theorem `charpoly_eq` / 定理 `charpoly_eq`

English:
theorem charpoly_eq
  given: (b : B)
  statement: charpoly G b = ∏ g : G, (X - C (g • b))
  proof: rfl

中文:
定理 charpoly_eq
  条件: (b : B)
  结论: charpoly G b = ∏ g : G, (X - C (g • b))
  证明: rfl
-/
theorem charpoly_eq (b : B) : charpoly G b = ∏ g : G, (X - C (g • b)) := rfl

/--
theorem `charpoly_eq_prod_smul` / 定理 `charpoly_eq_prod_smul`

English:
theorem charpoly_eq_prod_smul
  given: (b : B)
  statement: charpoly G b = ∏ g : G, g • (X - C b)
  proof: by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]

中文:
定理 charpoly_eq_prod_smul
  条件: (b : B)
  结论: charpoly G b = ∏ g : G, g • (X - C b)
  证明: by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]

Depends on / 依赖: charpoly_eq, smul_C, smul_X, smul_sub
-/
theorem charpoly_eq_prod_smul (b : B) : charpoly G b = ∏ g : G, g • (X - C b) := by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]

/--
theorem `monic_charpoly` / 定理 `monic_charpoly`

English:
theorem monic_charpoly
  given: (b : B)
  statement: (charpoly G b).Monic
  proof: monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

中文:
定理 monic_charpoly
  条件: (b : B)
  结论: (charpoly G b).Monic
  证明: monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

Depends on / 依赖: monic_X_sub_C, monic_prod_of_monic
-/
theorem monic_charpoly (b : B) : (charpoly G b).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

/--
theorem `splits_charpoly` / 定理 `splits_charpoly`

English:
theorem splits_charpoly
  given: (b : B)
  statement: (charpoly G b).Splits
  proof: .prod fun g _ => .X_sub_C (g • b)

中文:
定理 splits_charpoly
  条件: (b : B)
  结论: (charpoly G b).Splits
  证明: .prod fun g _ => .X_sub_C (g • b)

Depends on / 依赖: X_sub_C
-/
theorem splits_charpoly (b : B) : (charpoly G b).Splits :=
  .prod fun g _ => .X_sub_C (g • b)

/--
theorem `eval_charpoly` / 定理 `eval_charpoly`

English:
theorem eval_charpoly
  given: (b : B)
  statement: (charpoly G b).eval b = 0
  proof: by
  rw [charpoly_eq]; rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul]; rw [eval_sub]; rw [eval_C]; rw [eval_X]; rw [sub_self]

中文:
定理 eval_charpoly
  条件: (b : B)
  结论: (charpoly G b).eval b = 0
  证明: by
  rw [charpoly_eq]; rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul]; rw [eval_sub]; rw [eval_C]; rw [eval_X]; rw [sub_self]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_eq_zero, charpoly_eq, eval_C, eval_X, eval_prod, eval_sub, mem_univ, one_smul, prod_eq_zero, sub_self
-/
theorem eval_charpoly (b : B) : (charpoly G b).eval b = 0 := by
  rw [charpoly_eq]; rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul]; rw [eval_sub]; rw [eval_C]; rw [eval_X]; rw [sub_self]

variable {G}

/--
theorem `smul_charpoly` / 定理 `smul_charpoly`

English:
theorem smul_charpoly
  given: (b : B) (g : G)
  statement: g • (charpoly G b) = charpoly G b
  proof: by
  rw [charpoly_eq_prod_smul]; rw [Finset.smul_prod_perm]

中文:
定理 smul_charpoly
  条件: (b : B) (g : G)
  结论: g • (charpoly G b) = charpoly G b
  证明: by
  rw [charpoly_eq_prod_smul]; rw [Finset.smul_prod_perm]

Depends on / 依赖: Finset, Finset.smul_prod_perm, charpoly_eq_prod_smul, smul_prod_perm
-/
theorem smul_charpoly (b : B) (g : G) : g • (charpoly G b) = charpoly G b := by
  rw [charpoly_eq_prod_smul]; rw [Finset.smul_prod_perm]

/--
theorem `smul_coeff_charpoly` / 定理 `smul_coeff_charpoly`

English:
theorem smul_coeff_charpoly
  given: (b : B) (n : Nat) (g : G)
  proof: by
  rw [← coeff_smul]; rw [smul_charpoly]

中文:
定理 smul_coeff_charpoly
  条件: (b : B) (n : 自然数) (g : G)
  证明: by
  rw [← coeff_smul]; rw [smul_charpoly]

Depends on / 依赖: coeff_smul, smul_charpoly
-/
theorem smul_coeff_charpoly (b : B) (n : Nat) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul]; rw [smul_charpoly]

end MulSemiringAction

namespace Algebra.IsInvariant

open MulSemiringAction Polynomial

variable [IsInvariant A B G]

/--
theorem `charpoly_mem_lifts` / 定理 `charpoly_mem_lifts`

English:
theorem charpoly_mem_lifts
  given: [Fintype G] (b : B)
  proof: (charpoly G b).lifts_iff_coeff_lifts.mpr fun n => isInvariant _ (smul_coeff_charpoly b n)

中文:
定理 charpoly_mem_lifts
  条件: [Fintype G] (b : B)
  证明: (charpoly G b).lifts_iff_coeff_lifts.mpr fun n => isInvariant _ (smul_coeff_charpoly b n)

Depends on / 依赖: charpoly, isInvariant, lifts_iff_coeff_lifts, lifts_iff_coeff_lifts.mpr, smul_coeff_charpoly
-/
theorem charpoly_mem_lifts [Fintype G] (b : B) :
    charpoly G b in Polynomial.lifts (algebraMap A B) :=
  (charpoly G b).lifts_iff_coeff_lifts.mpr fun n => isInvariant _ (smul_coeff_charpoly b n)

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  given: [Finite G]
  statement: Algebra.IsIntegral A B
  proof: by
  cases nonempty_fintype G
  refine ⟨fun b => ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (monic_charpoly G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩

中文:
定理 isIntegral
  条件: [Finite G]
  结论: Algebra.Is整数egral A B
  证明: by
  cases nonempty_fintype G
  refine ⟨fun b => ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (monic_charpoly G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩

Depends on / 依赖: Polynomial, Polynomial.lifts_and_natDegree_eq_and_monic, charpoly_mem_lifts, eval_charpoly, eval_map, lifts_and_natDegree_eq_and_monic, monic_charpoly, nonempty_fintype
-/
theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by
  cases nonempty_fintype G
  refine ⟨fun b => ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (monic_charpoly G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩

/--
theorem `exists_smul_of_under_eq` / 定理 `exists_smul_of_under_eq`

English:
theorem exists_smul_of_under_eq
  statement: [Finite G] [SMulCommClass G A B]
  proof: by
  cases nonempty_fintype G
  have : forall (P Q : Ideal B) [P.IsPrime] [Q.IsPrime], P.under A = Q.under A ->
      exists g in (⊤ : Finset G), Q <= g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ => hP.smul _)]
    intro b hb
    suffices h : exists g in Fi

中文:
定理 exists_smul_of_under_eq
  结论: [Finite G] [SMulCommClass G A B]
  证明: by
  cases nonempty_fintype G
  have : forall (P Q : Ideal B) [P.IsPrime] [Q.IsPrime], P.under A = Q.under A ->
      exists g in (⊤ : Finset G), Q <= g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ => hP.smul _)]
    intro b hb
    suffices h : exists g in Fi

Depends on / 依赖: Finset, Finset.mem_univ, Finset.smul_prod_perm, Finset.univ, Ideal.mem_inv_pointwise_smul_iff.mpr, Ideal.subset_union_prime, IsPrime, P.IsPrime, P.under, Q.IsPrime, Q.under, Set.mem_biUnion, hP.p, hP.smul, isInvariant, mem_biUnion, mem_inv_pointwise_smul_iff, mem_univ, nonempty_fintype, smul_prod_perm
-/
theorem exists_smul_of_under_eq [Finite G] [SMulCommClass G A B]
    (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime]
    (hPQ : P.under A = Q.under A) :
    exists g : G, Q = g • P := by
  cases nonempty_fintype G
  have : forall (P Q : Ideal B) [P.IsPrime] [Q.IsPrime], P.under A = Q.under A ->
      exists g in (⊤ : Finset G), Q <= g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ => hP.smul _)]
    intro b hb
    suffices h : exists g in Finset.univ, g • b in P by
      obtain ⟨g, -, hg⟩ := h
      apply Set.mem_biUnion (Finset.mem_univ g⁻¹) (Ideal.mem_inv_pointwise_smul_iff.mpr hg)
    obtain ⟨a, ha⟩ := isInvariant (A := A) (∏ g : G, g • b) (Finset.smul_prod_perm b)
    rw [← hP.prod_mem_iff]; rw [← ha]; rw [← P.mem_comap]; rw [← P.under_def A]; rw [hPQ]; rw [Q.mem_comap]; rw [ha]; rw [hQ.prod_mem_iff]
    exact ⟨1, Finset.mem_univ 1, (one_smul G b).symm ▸ hb⟩
  obtain ⟨g, -, hg⟩ := this P Q hPQ
  obtain ⟨g', -, hg'⟩ := this Q (g • P) ((P.under_smul A g).trans hPQ).symm
  exact ⟨g, le_antisymm hg (smul_eq_of_le_smul (hg.trans hg') ▸ hg')⟩

/--
theorem `orbit_eq_primesOver` / 定理 `orbit_eq_primesOver`

English:
theorem orbit_eq_primesOver
  statement: [Finite G] [SMulCommClass G A B] (P : Ideal A) (Q : Ideal B)
  proof: by
  refine Set.ext fun R => ⟨fun ⟨g, hg⟩ => hg ▸ ⟨hQ.smul g, hP.smul g⟩, fun h => ?_⟩
  have : R.IsPrime := h.1
  obtain ⟨g, hg⟩ := exists_smul_of_under_eq A B G Q R (hP.over.symm.trans h.2.over)
  exact ⟨g, hg.symm⟩

中文:
定理 orbit_eq_primesOver
  结论: [Finite G] [SMulCommClass G A B] (P : Ideal A) (Q : Ideal B)
  证明: by
  refine Set.ext fun R => ⟨fun ⟨g, hg⟩ => hg ▸ ⟨hQ.smul g, hP.smul g⟩, fun h => ?_⟩
  have : R.IsPrime := h.1
  obtain ⟨g, hg⟩ := exists_smul_of_under_eq A B G Q R (hP.over.symm.trans h.2.over)
  exact ⟨g, hg.symm⟩

Depends on / 依赖: IsPrime, R.IsPrime, Set.ext, exists_smul_of_under_eq, hP.over.symm.trans, hP.smul, hQ.smul, hg.symm
-/
theorem orbit_eq_primesOver [Finite G] [SMulCommClass G A B] (P : Ideal A) (Q : Ideal B)
    [hP : Q.LiesOver P] [hQ : Q.IsPrime] : MulAction.orbit G Q = P.primesOver B := by
  refine Set.ext fun R => ⟨fun ⟨g, hg⟩ => hg ▸ ⟨hQ.smul g, hP.smul g⟩, fun h => ?_⟩
  have : R.IsPrime := h.1
  obtain ⟨g, hg⟩ := exists_smul_of_under_eq A B G Q R (hP.over.symm.trans h.2.over)
  exact ⟨g, hg.symm⟩

end Algebra.IsInvariant

end transitivity

section surjectivity

open FaithfulSMul IsScalarTower Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]

variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [Algebra (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
  [Algebra.IsInvariant A B G]

/--
theorem `fixed_of_fixed1_aux1` / 定理 `fixed_of_fixed1_aux1`

English:
theorem fixed_of_fixed1_aux1
  proof: by
  obtain ⟨_⟩ := nonempty_fintype G
  let P := Finset.inf {g : G | g • Q != Q} (fun g => g • Q)
  have h1 : ¬ P <= Q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨b, hbP, hbQ⟩ := SetLike.not_le_

中文:
定理 fixed_of_fixed1_aux1
  证明: by
  obtain ⟨_⟩ := nonempty_fintype G
  let P := Finset.inf {g : G | g • Q != Q} (fun g => g • Q)
  have h1 : ¬ P <= Q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨b, hbP, hbQ⟩ := SetLike.not_le_
-/
private theorem fixed_of_fixed1_aux1 :
    exists a b : B, (forall g : G, g • a = a) ∧ a ∉ Q ∧
    forall g : G, algebraMap B (B ⧸ Q) (g • b) = algebraMap B (B ⧸ Q) (if g • Q = Q then a else 0) := by
  obtain ⟨_⟩ := nonempty_fintype G
  let P := Finset.inf {g : G | g • Q != Q} (fun g => g • Q)
  have h1 : ¬ P <= Q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨b, hbP, hbQ⟩ := SetLike.not_le_iff_exists.mp h1
  replace hbP : forall g : G, g • Q != Q -> b in g • Q :=
    fun g hg => (Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩) : P <= g • Q) hbP
  let f := MulSemiringAction.charpoly G b
  obtain ⟨q, hq, hq0⟩ :=
    (f.map (algebraMap B (B ⧸ Q))).exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      (Polynomial.map_monic_ne_zero (MulSemiringAction.monic_charpoly G b)) 0
  rw [map_zero]; rw [sub_zero] at hq hq0
  let j := (f.map (algebraMap B (B ⧸ Q))).rootMultiplicity 0
  let k := q.natDegree
  let r := ∑ i in Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j))
  have hr : r.map (algebraMap B (B ⧸ Q)) = q := by
    ext n
    rw [Polynomial.coeff_map]; rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range_succ_iff]
    split_ifs with hn
    · rw [← Polynomial.coeff_map, hq, Polynomial.coeff_X_pow_mul]
    · rw [map_zero, eq_comm, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
  have hf : f.eval b = 0 := MulSemiringAction.eval_charpoly G b
  have hr : r.eval b in Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [← Ideal.Quotient.algebraMap_eq] at hbQ ⊢
    replace hf := congrArg (algebraMap B (B ⧸ Q)) hf
    rw [← Polynomial.eval₂_at_apply]; rw [← Polynomial.eval_map] at hf ⊢
    rwa [map_zero, hq, ← hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      mul_eq_zero, or_iff_right (pow_ne_zero _ hbQ)] at hf
  let a := f.coeff j
  have ha : forall g : G, g • a = a := MulSemiringAction.smul_coeff_charpoly b j
  have hr' : forall g : G, g • Q != Q -> a - r.eval b in g • Q := by
    intro g hg
    have hr : r = ∑ i in Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j)) := rfl
    rw [← Ideal.neg_mem_iff]; rw [neg_sub]; rw [hr]; rw [Finset.sum_range_succ']; rw [Polynomial.eval_add]; rw [Polynomial.eval_monomial]; rw [zero_add]; rw [pow_zero]; rw [mul_one]; rw [add_sub_cancel_right]
    simp only [← Polynomial.monomial_mul_X]
    rw [← Finset.sum_mul]; rw [Polynomial.eval_mul_X]
    exact Ideal.mul_mem_left (g • Q) _ (hbP g hg)
  refine ⟨a, a - r.eval b, ha, ?_, fun h => ?_⟩
  · rwa [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, ← Polynomial.coeff_map,
      ← zero_add j, hq, Polynomial.coeff_X_pow_mul, ← Polynomial.X_dvd_iff]
  · rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.smul_mem_pointwise_smul_iff (a := h⁻¹), smul_sub, inv_smul_smul]
    simp only [← eq_inv_smul_iff (g := h), eq_comm (a := Q)]
    split_ifs with hh
    · rwa [ha, sub_sub_cancel_left, hh, Q.neg_mem_iff]
    · rw [smul_zero, sub_zero]
      exact hr' h⁻¹ hh

/--
theorem `fixed_of_fixed1_aux2` / 定理 `fixed_of_fixed1_aux2`

English:
theorem fixed_of_fixed1_aux2
  statement: (b₀ : B)
  proof: by
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux1 G Q
  refine ⟨a, b * b₀, ha1, ha2, fun g => ?_⟩
  rw [smul_mul']; rw [map_mul]; rw [hb]
  specialize hb g
  split_ifs with hg
  · rw [map_mul, hx g hg]
  · rw [map_zero, zero_mul]

中文:
定理 fixed_of_fixed1_aux2
  结论: (b₀ : B)
  证明: by
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux1 G Q
  refine ⟨a, b * b₀, ha1, ha2, fun g => ?_⟩
  rw [smul_mul']; rw [map_mul]; rw [hb]
  specialize hb g
  split_ifs with hg
  · rw [map_mul, hx g hg]
  · rw [map_zero, zero_mul]
-/
private theorem fixed_of_fixed1_aux2 (b₀ : B)
    (hx : forall g : G, g • Q = Q -> algebraMap B (B ⧸ Q) (g • b₀) = algebraMap B (B ⧸ Q) b₀) :
    exists a b : B, (forall g : G, g • a = a) ∧ a ∉ Q ∧
    (forall g : G, algebraMap B (B ⧸ Q) (g • b) =
      algebraMap B (B ⧸ Q) (if g • Q = Q then a * b₀ else 0)) := by
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux1 G Q
  refine ⟨a, b * b₀, ha1, ha2, fun g => ?_⟩
  rw [smul_mul']; rw [map_mul]; rw [hb]
  specialize hb g
  split_ifs with hg
  · rw [map_mul, hx g hg]
  · rw [map_zero, zero_mul]

/--
theorem `fixed_of_fixed1_aux3` / 定理 `fixed_of_fixed1_aux3`

English:
theorem fixed_of_fixed1_aux3
  statement: [NoZeroDivisors B] {b : B} {i j : Nat} {p : Polynomial A}
  proof: by
  by_cases ha : b = 0
  · rw [ha, map_zero]
  have hf := congrArg (eval b) (congrArg (Polynomial.mapAlgHom f.toAlgHom) h)
  rw [coe_mapAlgHom]; rw [map_map]; rw [f.toAlgHom.comp_algebraMap]; rw [h] at hf
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
    eval

中文:
定理 fixed_of_fixed1_aux3
  结论: [NoZeroDivisors B] {b : B} {i j : 自然数} {p : Polynomial A}
  证明: by
  by_cases ha : b = 0
  · rw [ha, map_zero]
  have hf := congrArg (eval b) (congrArg (Polynomial.mapAlgHom f.toAlgHom) h)
  rw [coe_mapAlgHom]; rw [map_map]; rw [f.toAlgHom.comp_algebraMap]; rw [h] at hf
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
    eval
-/
private theorem fixed_of_fixed1_aux3 [NoZeroDivisors B] {b : B} {i j : Nat} {p : Polynomial A}
    (h : p.map (algebraMap A B) = (X - C b) ^ i * X ^ j) (f : B ≃ₐ[A] B) (hi : i != 0) :
    f b = b := by
  by_cases ha : b = 0
  · rw [ha, map_zero]
  have hf := congrArg (eval b) (congrArg (Polynomial.mapAlgHom f.toAlgHom) h)
  rw [coe_mapAlgHom]; rw [map_map]; rw [f.toAlgHom.comp_algebraMap]; rw [h] at hf
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
    eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hi, zero_mul,
    zero_eq_mul, or_iff_left (pow_ne_zero j ha), pow_eq_zero_iff hi, sub_eq_zero] at hf
  exact hf.symm

/--
theorem `fixed_of_fixed1` / 定理 `fixed_of_fixed1`

English:
theorem fixed_of_fixed1
  statement: [Module.IsTorsionFree (B ⧸ Q) L] (f : Gal(L/K)) (b : B ⧸ Q)
  proof: by
  cases nonempty_fintype G
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux2 G Q b₀ (fun g hg => hx ⟨g, hg⟩)
  obtain ⟨M, key⟩ := (mem_lifts _).mp (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
  repl

中文:
定理 fixed_of_fixed1
  结论: [Module.IsTorsionFree (B ⧸ Q) L] (f : Gal(L/K)) (b : B ⧸ Q)
  证明: by
  cases nonempty_fintype G
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux2 G Q b₀ (fun g hg => hx ⟨g, hg⟩)
  obtain ⟨M, key⟩ := (mem_lifts _).mp (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
  repl
-/
private theorem fixed_of_fixed1 [Module.IsTorsionFree (B ⧸ Q) L] (f : Gal(L/K)) (b : B ⧸ Q)
    (hx : forall g : MulAction.stabilizer G Q, Ideal.Quotient.stabilizerHom Q P G g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  cases nonempty_fintype G
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux2 G Q b₀ (fun g hg => hx ⟨g, hg⟩)
  obtain ⟨M, key⟩ := (mem_lifts _).mp (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
  replace key := congrArg (map (algebraMap B (B ⧸ Q))) key
  rw [map_map]; rw [← algebraMap_eq]; rw [algebraMap_eq A (A ⧸ P) (B ⧸ Q)]; rw [← map_map]; rw [MulSemiringAction.charpoly]; rw [Polynomial.map_prod] at key
  have key₀ : forall g : G, (X - C (g • b)).map (algebraMap B (B ⧸ Q)) =
      if g • Q = Q then X - C (algebraMap B (B ⧸ Q) (a * b₀)) else X := by
    intro g
    rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]; rw [hb]
    split_ifs
    · rfl
    · rw [map_zero, map_zero, sub_zero]
  simp only [key₀, Finset.prod_ite, Finset.prod_const] at key
  replace key := congrArg (map (algebraMap (B ⧸ Q) L)) key
  rw [map_map]; rw [← algebraMap_eq]; rw [algebraMap_eq (A ⧸ P) K L]; rw [← map_map]; rw [Polynomial.map_mul]; rw [Polynomial.map_pow]; rw [Polynomial.map_pow]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C] at key
  replace key := fixed_of_fixed1_aux3 key f (Finset.card_ne_zero_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, one_smul G Q⟩))
  simp only [map_mul] at key
  obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) a ha1
  rwa [← algebraMap_apply A B (B ⧸ Q), algebraMap_apply A (A ⧸ P) (B ⧸ Q),
      ← algebraMap_apply, algebraMap_apply (A ⧸ P) K L, f.commutes, mul_right_inj'] at key
  rwa [← algebraMap_apply, algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      ← algebraMap_apply A (A ⧸ P) (B ⧸ Q), algebraMap_apply A B (B ⧸ Q),
      Ne, algebraMap_eq_zero_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

variable [IsFractionRing (A ⧸ P) K] [IsFractionRing (B ⧸ Q) L]

/--
Definition of `IsFractionRing.stabilizerHom` / `IsFractionRing.stabilizerHom` 的定义

English:
definition IsFractionRing.stabilizerHom
  signature: : MulAction.stabilizer G Q ->* Gal(L/K)
  body: MonoidHom.comp (IsFractionRing.fieldEquivOfAlgEquivHom K L) (Ideal.Quotient.stabilizerHom Q P G)

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in
@[simp]

中文:
定义 IsFractionRing.stabilizerHom
  签名: : MulAction.stabilizer G Q ->* Gal(L/K)
  定义体: MonoidHom.comp (IsFractionRing.fieldEquivOfAlgEquivHom K L) (Ideal.Quotient.stabilizerHom Q P G)

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in
@[simp]

Depends on / 依赖: Ideal.Quotient.stabilizerHom, IsFractionRing, IsFractionRing.fieldEquivOfAlgEquivHom, MonoidHom, MonoidHom.comp, Quotient, fieldEquivOfAlgEquivHom, stabilizerHom
-/
noncomputable def IsFractionRing.stabilizerHom : MulAction.stabilizer G Q ->* Gal(L/K) :=
  MonoidHom.comp (IsFractionRing.fieldEquivOfAlgEquivHom K L) (Ideal.Quotient.stabilizerHom Q P G)

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in
@[simp]
/--
theorem `IsFractionRing.stabilizerHom_apply_apply_mk` / 定理 `IsFractionRing.stabilizerHom_apply_apply_mk`

English:
theorem IsFractionRing.stabilizerHom_apply_apply_mk
  given: (σ : MulAction.stabilizer G Q) (x : B)
  proof: by
  simp [IsFractionRing.stabilizerHom, MulAction.subgroup_smul_def]

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in

中文:
定理 IsFractionRing.stabilizerHom_apply_apply_mk
  条件: (σ : MulAction.stabilizer G Q) (x : B)
  证明: by
  simp [IsFractionRing.stabilizerHom, MulAction.subgroup_smul_def]

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in

Depends on / 依赖: IsFractionRing, IsFractionRing.stabilizerHom, MulAction, MulAction.subgroup_smul_def, stabilizerHom, subgroup_smul_def
-/
theorem IsFractionRing.stabilizerHom_apply_apply_mk (σ : MulAction.stabilizer G Q) (x : B) :
    IsFractionRing.stabilizerHom G P Q K L σ (algebraMap _ L (Ideal.Quotient.mk Q x)) =
      algebraMap _ L (Ideal.Quotient.mk Q (σ.val • x)) := by
  simp [IsFractionRing.stabilizerHom, MulAction.subgroup_smul_def]

omit [Finite G] [Q.IsPrime] [Algebra.IsInvariant A B G] in
/--
theorem `IsFractionRing.ker_stabilizerHom` / 定理 `IsFractionRing.ker_stabilizerHom`

English:
theorem IsFractionRing.ker_stabilizerHom
  proof: by
  rw [stabilizerHom]; rw [MonoidHom.ker_comp_of_injective]; rw [Ideal.Quotient.ker_stabilizerHom]
  apply fieldEquivOfAlgEquivHom_injective

中文:
定理 IsFractionRing.ker_stabilizerHom
  证明: by
  rw [stabilizerHom]; rw [MonoidHom.ker_comp_of_injective]; rw [Ideal.Quotient.ker_stabilizerHom]
  apply fieldEquivOfAlgEquivHom_injective

Depends on / 依赖: Ideal.Quotient.ker_stabilizerHom, MonoidHom, MonoidHom.ker_comp_of_injective, Quotient, fieldEquivOfAlgEquivHom_injective, ker_comp_of_injective, ker_stabilizerHom, stabilizerHom
-/
theorem IsFractionRing.ker_stabilizerHom :
    (stabilizerHom G P Q K L).ker = Q.inertia (MulAction.stabilizer G Q) := by
  rw [stabilizerHom]; rw [MonoidHom.ker_comp_of_injective]; rw [Ideal.Quotient.ker_stabilizerHom]
  apply fieldEquivOfAlgEquivHom_injective

/--
theorem `fixed_of_fixed2` / 定理 `fixed_of_fixed2`

English:
theorem fixed_of_fixed2
  statement: (f : Gal(L/K)) (x : L)
  proof: by
  obtain ⟨_⟩ := nonempty_fintype G
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebr

中文:
定理 fixed_of_fixed2
  结论: (f : Gal(L/K)) (x : L)
  证明: by
  obtain ⟨_⟩ := nonempty_fintype G
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebr
-/
private theorem fixed_of_fixed2 (f : Gal(L/K)) (x : L)
    (hx : forall g : MulAction.stabilizer G Q, IsFractionRing.stabilizerHom G P Q K L g x = x) :
    f x = x := by
  obtain ⟨_⟩ := nonempty_fintype G
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  replace ha : algebraMap (A ⧸ P) L a != 0 := by
    rwa [Ne, algebraMap_apply (A ⧸ P) K L, algebraMap_eq_zero_iff, algebraMap_eq_zero_iff]
  replace hy : algebraMap (B ⧸ Q) L y != 0 :=
    mt (algebraMap_eq_zero_iff (B ⧸ Q) L).mp (nonZeroDivisors.ne_zero hy)
  replace h : algebraMap (B ⧸ Q) L x / algebraMap (B ⧸ Q) L y =
      algebraMap (B ⧸ Q) L b / algebraMap (A ⧸ P) L a := by
    rw [mul_comm]; rw [Algebra.smul_def]; rw [mul_comm] at h
    rw [div_eq_div_iff hy ha]; rw [← map_mul]; rw [← h]; rw [map_mul]; rw [← algebraMap_apply]
  simp only [h, map_div₀, algebraMap_apply (A ⧸ P) K L, AlgEquiv.commutes] at hx ⊢
  simp only [← algebraMap_apply, div_left_inj' ha] at hx ⊢
  exact fixed_of_fixed1 G P Q K L f b (fun g => IsFractionRing.injective (B ⧸ Q) L
    ((IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L
      (Ideal.Quotient.stabilizerHom Q P G g) b).symm.trans (hx g)))

/--
theorem `IsFractionRing.stabilizerHom_surjective` / 定理 `IsFractionRing.stabilizerHom_surjective`

English:
theorem IsFractionRing.stabilizerHom_surjective
  proof: by
  let _ := MulSemiringAction.compHom L (stabilizerHom G P Q K L)
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x => fixed_of_fixed2 G P Q K L f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

中文:
定理 IsFractionRing.stabilizerHom_surjective
  证明: by
  let _ := MulSemiringAction.compHom L (stabilizerHom G P Q K L)
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x => fixed_of_fixed2 G P Q K L f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.ext_iff, AlgEquiv.ofRingEquiv, FixedPoints, FixedPoints.toAlgAut_surjective, MulAction, MulAction.stabilizer, MulSemiringAction, MulSemiringAction.compHom, compHom, ext_iff, fixed_of_fixed2, ofRingEquiv, stabilizer, stabilizerHom, toAlgAut_surjective
-/
theorem IsFractionRing.stabilizerHom_surjective :
    Function.Surjective (stabilizerHom G P Q K L) := by
  let _ := MulSemiringAction.compHom L (stabilizerHom G P Q K L)
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x => fixed_of_fixed2 G P Q K L f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

/--
theorem `Ideal.Quotient.stabilizerHom_surjective` / 定理 `Ideal.Quotient.stabilizerHom_surjective`

English:
theorem Ideal.Quotient.stabilizerHom_surjective
  proof: by
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  let _ := FractionRing.liftAlgebra (A ⧸ P) (FractionRing (B ⧸ Q))
  have key := IsFractionRing.stabilizerHom_surjective G P Q
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q))
  rw [IsFractionRing.stabilizerHom]; rw [MonoidHom.co

中文:
定理 Ideal.Quotient.stabilizerHom_surjective
  证明: by
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  let _ := FractionRing.liftAlgebra (A ⧸ P) (FractionRing (B ⧸ Q))
  have key := IsFractionRing.stabilizerHom_surjective G P Q
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q))
  rw [IsFractionRing.stabilizerHom]; rw [MonoidHom.co

Depends on / 依赖: FractionRing, FractionRing.liftAlgebra, Ideal.IsPrime.under, Ideal.over_def, IsFractionRing, IsFractionRing.fieldEquivOfAlgEquivHom_injective, IsFractionRing.stabilizerHom, IsFractionRing.stabilizerHom_surjective, IsPrime, MonoidHom, MonoidHom.coe_comp, P.IsPrime, coe_comp, fieldEquivOfAlgEquivHom_injective, key.of_comp_left, liftAlgebra, of_comp_left, over_def, stabilizerHom, stabilizerHom_surjective
-/
theorem Ideal.Quotient.stabilizerHom_surjective :
    Function.Surjective (Ideal.Quotient.stabilizerHom Q P G) := by
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  let _ := FractionRing.liftAlgebra (A ⧸ P) (FractionRing (B ⧸ Q))
  have key := IsFractionRing.stabilizerHom_surjective G P Q
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q))
  rw [IsFractionRing.stabilizerHom]; rw [MonoidHom.coe_comp] at key
  exact key.of_comp_left (IsFractionRing.fieldEquivOfAlgEquivHom_injective (A ⧸ P) (B ⧸ Q)
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q)))

/--
Definition of `IsFractionRing.stabilizerQuotientInertiaEquiv` / `IsFractionRing.stabilizerQuotientInertiaEquiv` 的定义

English:
definition IsFractionRing.stabilizerQuotientInertiaEquiv
  signature: :
  body: QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q K L) (ker_stabilizerHom G P Q K L).symm

@[simp]

中文:
定义 IsFractionRing.stabilizerQuotientInertiaEquiv
  签名: :
  定义体: QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q K L) (ker_stabilizerHom G P Q K L).symm

@[simp]

Depends on / 依赖: MulAction, MulAction.stabilizer, Q.inertia, QuotientGroup, QuotientGroup.liftEquiv, inertia, ker_stabilizerHom, liftEquiv, stabilizer, stabilizerHom_surjective
-/
noncomputable def IsFractionRing.stabilizerQuotientInertiaEquiv :
    MulAction.stabilizer G Q ⧸ Q.inertia (MulAction.stabilizer G Q) ≃* Gal(L/K) :=
  QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q K L) (ker_stabilizerHom G P Q K L).symm

@[simp]
/--
theorem `IsFractionRing.stabilizerQuotientInertiaEquiv_mk` / 定理 `IsFractionRing.stabilizerQuotientInertiaEquiv_mk`

English:
theorem IsFractionRing.stabilizerQuotientInertiaEquiv_mk
  given: (g : MulAction.stabilizer G Q)
  proof: rfl

中文:
定理 IsFractionRing.stabilizerQuotientInertiaEquiv_mk
  条件: (g : MulAction.stabilizer G Q)
  证明: rfl
-/
theorem IsFractionRing.stabilizerQuotientInertiaEquiv_mk (g : MulAction.stabilizer G Q) :
    stabilizerQuotientInertiaEquiv G P Q K L g = stabilizerHom G P Q K L g := rfl

/--
Definition of `Ideal.Quotient.stabilizerQuotientInertiaEquiv` / `Ideal.Quotient.stabilizerQuotientInertiaEquiv` 的定义

English:
definition Ideal.Quotient.stabilizerQuotientInertiaEquiv
  signature: :
  body: QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q) (ker_stabilizerHom Q P G).symm

@[simp]

中文:
定义 Ideal.Quotient.stabilizerQuotientInertiaEquiv
  签名: :
  定义体: QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q) (ker_stabilizerHom Q P G).symm

@[simp]

Depends on / 依赖: MulAction, MulAction.stabilizer, Q.inertia, QuotientGroup, QuotientGroup.liftEquiv, inertia, ker_stabilizerHom, liftEquiv, stabilizer, stabilizerHom_surjective
-/
noncomputable def Ideal.Quotient.stabilizerQuotientInertiaEquiv :
    MulAction.stabilizer G Q ⧸ Q.inertia (MulAction.stabilizer G Q) ≃*
      Gal((B ⧸ Q)/(A ⧸ P)) :=
  QuotientGroup.liftEquiv (N := Q.inertia (MulAction.stabilizer G Q))
    (stabilizerHom_surjective G P Q) (ker_stabilizerHom Q P G).symm

@[simp]
/--
theorem `Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk` / 定理 `Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk`

English:
theorem Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk
  given: (g : MulAction.stabilizer G Q)
  proof: rfl

中文:
定理 Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk
  条件: (g : MulAction.stabilizer G Q)
  证明: rfl
-/
theorem Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk (g : MulAction.stabilizer G Q) :
    stabilizerQuotientInertiaEquiv G P Q g = stabilizerHom Q P G g := rfl

end surjectivity

section normal

variable {A B k : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  [CommRing k] [Algebra (A ⧸ P) k] [Algebra (B ⧸ Q) k] [IsScalarTower (A ⧸ P) (B ⧸ Q) k]
  [IsDomain k] [FaithfulSMul (B ⧸ Q) k]

include G in
/--
lemma `Ideal.Quotient.exists_algHom_fixedPoint_quotient_under` / 引理 `Ideal.Quotient.exists_algHom_fixedPoint_quotient_under`

English:
lemma Ideal.Quotient.exists_algHom_fixedPoint_quotient_under
  proof: by
  let f : (B ⧸ Q) ->ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  suffices (σ.comp f).range <= f.range by
    let e := (AlgEquiv.ofInjective f hf)
    exact ⟨(e.symm.toAlgHom.comp (Subalgebra.inclusion this)).comp (σ.comp f)

中文:
引理 Ideal.Quotient.exists_algHom_fixedPoint_quotient_under
  证明: by
  let f : (B ⧸ Q) ->ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  suffices (σ.comp f).range <= f.range by
    let e := (AlgEquiv.ofInjective f hf)
    exact ⟨(e.symm.toAlgHom.comp (Subalgebra.inclusion this)).comp (σ.comp f)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjective, FaithfulSMul, FaithfulSMul.algebraMap_injective, Function, Function.Injective, Ideal.Quotient.mk_surjective, Injective, IsScalarTower, IsScalarTower.toAlgHom, Quotient, Subalgebra, Subalgebra.inclusion, Subtype, Subtype.val, algebraMap, algebraMap_injective, algebraize, apply_symm_apply, congr_arg
-/
lemma Ideal.Quotient.exists_algHom_fixedPoint_quotient_under
    (σ : k ->ₐ[A ⧸ P] k) :
    exists τ : (B ⧸ Q) ->ₐ[A ⧸ P] B ⧸ Q, forall x : B ⧸ Q,
      algebraMap _ _ (τ x) = σ (algebraMap (B ⧸ Q) k x) := by
  let f : (B ⧸ Q) ->ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  suffices (σ.comp f).range <= f.range by
    let e := (AlgEquiv.ofInjective f hf)
    exact ⟨(e.symm.toAlgHom.comp (Subalgebra.inclusion this)).comp (σ.comp f).rangeRestrict,
      fun x => congr_arg Subtype.val (e.apply_symm_apply ⟨_, _⟩)⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  cases nonempty_fintype G
  algebraize [(algebraMap (A ⧸ P) k).comp (algebraMap A (A ⧸ P)),
    (algebraMap (B ⧸ Q) k).comp (algebraMap B (B ⧸ Q))]
  have : IsScalarTower A (B ⧸ Q) k := .of_algebraMap_eq fun x =>
    (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (mk P x))
  have : IsScalarTower A B k := .of_algebraMap_eq fun x =>
    (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (mk P x))
  obtain ⟨P, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G x
  have : Polynomial.aeval x P = 0 := by
    rw [Polynomial.aeval_def]; rw [← Polynomial.eval_map]; rw [← Polynomial.coe_mapRingHom (R := A)]; rw [hp]; rw [MulSemiringAction.eval_charpoly]
  have : Polynomial.aeval (σ (algebraMap (B ⧸ Q) k (mk _ x))) P = 0 := by
    refine (DFunLike.congr_fun (Polynomial.aeval_algHom ((σ.restrictScalars A).comp
      (IsScalarTower.toAlgHom A (B ⧸ Q) k)) _) P).trans ?_
    rw [AlgHom.comp_apply]; rw [← algebraMap_eq]; rw [Polynomial.aeval_algebraMap_apply]; rw [this]; rw [map_zero]; rw [map_zero]
  rw [← Polynomial.aeval_map_algebraMap B]; rw [← Polynomial.coe_mapRingHom]; rw [hp] at this
  obtain ⟨τ, hτ⟩ : exists τ : G, σ (algebraMap _ _ x) = algebraMap _ _ (τ • x) := by
    simpa [MulSemiringAction.charpoly, sub_eq_zero, Finset.prod_eq_zero_iff] using! this
  exact ⟨Ideal.Quotient.mk _ (τ • x), hτ.symm⟩

include G in
/--
lemma `Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under` / 引理 `Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under`

English:
lemma Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under
  proof: by
  let f : (B ⧸ Q) ->ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨τ₁, h₁⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.toAlgHom
  obtain ⟨τ₂, h₂⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotie

中文:
引理 Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under
  证明: by
  let f : (B ⧸ Q) ->ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨τ₁, h₁⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.toAlgHom
  obtain ⟨τ₂, h₂⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotie

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Function, Function.Injective, Ideal.Quotient.exists_algHom_fixedPoint_quotient_under, Ideal.Quotient.mk_surjectiv, Ideal.Quotient.mk_surjective, Injective, IsScalarTower, IsScalarTower.toAlgHom, Quotient, algebraMap_injective, exists_algHom_fixedPoint_quotient_under, invFun, left_inv, mk_surjectiv, mk_surjective, right_inv, symm.toAlgHom, toAlgHom
-/
lemma Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under
    (σ : k ≃ₐ[A ⧸ P] k) :
    exists τ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q, forall x : B ⧸ Q,
      algebraMap _ _ (τ x) = σ (algebraMap (B ⧸ Q) k x) := by
  let f : (B ⧸ Q) ->ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨τ₁, h₁⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.toAlgHom
  obtain ⟨τ₂, h₂⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.symm.toAlgHom
  refine ⟨{ __ := τ₁, invFun := τ₂, left_inv := ?_, right_inv := ?_ }, h₁⟩
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, e⟩ := Ideal.Quotient.mk_surjective (τ₁ (Ideal.Quotient.mk Q x))
    apply hf
    dsimp [f] at h₁ h₂ ⊢
    refine .trans ?_ (σ.symm_apply_apply _)
    rw [← h₁]; rw [← e]; rw [h₂]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, e⟩ := Ideal.Quotient.mk_surjective (τ₂ (Ideal.Quotient.mk Q x))
    apply hf
    dsimp [f] at h₁ h₂ ⊢
    refine .trans ?_ (σ.apply_symm_apply _)
    rw [← h₂]; rw [← e]; rw [h₁]

end normal

namespace IsFractionRing

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
  [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L] [IsFractionRing A K] [IsFractionRing B L]
  [IsScalarTower A K L] [IsScalarTower A B L] [MulSemiringAction G B] [MulSemiringAction G L]
  [SMulDistribClass G B L] [hAB : Algebra.IsInvariant A B G] [SMulCommClass G A B]

/--
theorem `isInvariant_of_isIntegral` / 定理 `isInvariant_of_isIntegral`

English:
theorem isInvariant_of_isIntegral
  given: [Algebra.IsIntegral A B]
  statement: Algebra.IsInvariant K L G
  proof: by
  refine ⟨fun x h => ?_⟩
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
  have : Nontrivial B := (IsFractio

中文:
定理 isInvariant_of_isIntegral
  条件: [Algebra.Is整数egral A B]
  结论: Algebra.IsInvariant K L G
  证明: by
  refine ⟨fun x h => ?_⟩
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
  have : Nontrivial B := (IsFractio

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, IsFractionRing.nontrivial_iff_nontrivial, IsScalarTower, IsScalarTower.algebraMap_apply, Nontrivial, algebraMap, algebraMap_apply, div_surjective, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero, nontrivial_iff_nontrivial, simp_rw
-/
theorem isInvariant_of_isIntegral [Algebra.IsIntegral A B] : Algebra.IsInvariant K L G := by
  refine ⟨fun x h => ?_⟩
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
  have : Nontrivial B := (IsFractionRing.nontrivial_iff_nontrivial B L).mpr inferInstance
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective B x
  have hy' : algebraMap B L y != 0 := by simpa using nonZeroDivisors.ne_zero hy
  obtain ⟨b, a, ha, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) y).exists_smul_eq_mul x hy
  rw [mul_comm]; rw [Algebra.smul_def]; rw [mul_comm] at hb
  replace ha : (algebraMap B L) (algebraMap A B a) != 0 := by simpa [← hc]
  have hxy : algebraMap B L x / algebraMap B L y =
    algebraMap B L b / algebraMap B L (algebraMap A B a) := by
    rw [div_eq_div_iff hy' ha]; rw [← map_mul]; rw [hb]; rw [map_mul]
  obtain ⟨b, rfl⟩ := hAB.isInvariant b
    (by simpa [ha, hxy, smul_div₀', ← algebraMap.coe_smul'] using h)
  use algebraMap A K b / algebraMap A K a
  rw [hxy]; rw [map_div₀]; rw [hc]; rw [hc]

include A B in
/--
theorem `isInvariant` / 定理 `isInvariant`

English:
theorem isInvariant
  given: [Finite G]
  statement: Algebra.IsInvariant K L G
  proof: have := hAB.isIntegral
  isInvariant_of_isIntegral G A B K L

中文:
定理 isInvariant
  条件: [Finite G]
  结论: Algebra.IsInvariant K L G
  证明: have := hAB.isIntegral
  isInvariant_of_isIntegral G A B K L

Depends on / 依赖: hAB.isIntegral, isIntegral, isInvariant_of_isIntegral
-/
theorem isInvariant [Finite G] : Algebra.IsInvariant K L G :=
  have := hAB.isIntegral
  isInvariant_of_isIntegral G A B K L

end IsFractionRing
