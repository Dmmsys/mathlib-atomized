/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Classification of Algebraically closed fields

This file contains results related to classifying algebraically closed fields.

## Main statements

* `IsAlgClosed.equivOfTranscendenceBasis` Two algebraically closed fields with the same
  characteristic and the same cardinality of transcendence basis are isomorphic.
* `IsAlgClosed.ringEquivOfCardinalEqOfCharEq` Two uncountable algebraically closed fields
  are isomorphic if they have the same characteristic and the same cardinality.
-/

@[expose] public section


universe u v w

open scoped Cardinal Polynomial

open Cardinal

namespace IsAlgClosed

section Classification

noncomputable section

variable {R L K : Type*} [CommRing R]
variable [Field K] [Algebra R K]
variable [Field L] [Algebra R L]
variable {ι : Type*} (v : ι -> K)
variable {κ : Type*} (w : κ -> L)
variable (hv : AlgebraicIndependent R v)

/--
theorem `isAlgClosure_of_transcendence_basis` / 定理 `isAlgClosure_of_transcendence_basis`

English:
theorem isAlgClosure_of_transcendence_basis
  given: [IsAlgClosed K] (hv : IsTranscendenceBasis R v)
  proof: letI := RingHom.domain_nontrivial (algebraMap R K)
  { isAlgClosed := by infer_instance
    isAlgebraic := hv.isAlgebraic }

中文:
定理 isAlgClosure_of_transcendence_basis
  条件: [IsAlgClosed K] (hv : IsTranscendenceBasis R v)
  证明: letI := RingHom.domain_nontrivial (algebraMap R K)
  { isAlgClosed := by infer_instance
    isAlgebraic := hv.isAlgebraic }

Depends on / 依赖: RingHom, RingHom.domain_nontrivial, algebraMap, domain_nontrivial, hv.isAlgebraic, infer_instance, isAlgClosed, isAlgebraic
-/
theorem isAlgClosure_of_transcendence_basis [IsAlgClosed K] (hv : IsTranscendenceBasis R v) :
    IsAlgClosure (Algebra.adjoin R (Set.range v)) K :=
  letI := RingHom.domain_nontrivial (algebraMap R K)
  { isAlgClosed := by infer_instance
    isAlgebraic := hv.isAlgebraic }

variable (hw : AlgebraicIndependent R w)

/--
Definition of `equivOfTranscendenceBasis` / `equivOfTranscendenceBasis` 的定义

English:
definition equivOfTranscendenceBasis
  signature: [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ)
  body: by
  letI := isAlgClosure_of_transcendence_basis v hv
  letI := isAlgClosure_of_transcendence_basis w hw
  have e : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range w) := by
    refine hv.1.aevalEquiv.symm.toRingEquiv.trans ?_
    refine (AlgEquiv.ofAlgHom (MvPolynomial.rename e)
     

中文:
定义 equivOfTranscendenceBasis
  签名: [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ)
  定义体: by
  letI := isAlgClosure_of_transcendence_basis v hv
  letI := isAlgClosure_of_transcendence_basis w hw
  have e : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range w) := by
    refine hv.1.aevalEquiv.symm.toRingEquiv.trans ?_
    refine (AlgEquiv.ofAlgHom (MvPolynomial.rename e)
     

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, Algebra, Algebra.adjoin, IsAlgClosure, IsAlgClosure.equivOfEquiv, MvPolynomial, MvPolynomial.rename, Set.range, adjoin, aevalEquiv, aevalEquiv.symm.toRingEquiv.trans, aevalEquiv.toRingEquiv, e.symm, equivOfEquiv, isAlgClosure_of_transcendence_basis, ofAlgHom, toRingEquiv, toRingEquiv.trans
-/
def equivOfTranscendenceBasis [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ)
    (hv : IsTranscendenceBasis R v) (hw : IsTranscendenceBasis R w) : K ≃+* L := by
  letI := isAlgClosure_of_transcendence_basis v hv
  letI := isAlgClosure_of_transcendence_basis w hw
  have e : Algebra.adjoin R (Set.range v) ≃+* Algebra.adjoin R (Set.range w) := by
    refine hv.1.aevalEquiv.symm.toRingEquiv.trans ?_
    refine (AlgEquiv.ofAlgHom (MvPolynomial.rename e)
      (MvPolynomial.rename e.symm) ?_ ?_).toRingEquiv.trans ?_
    · ext; simp
    · ext; simp
    exact hw.1.aevalEquiv.toRingEquiv
  exact IsAlgClosure.equivOfEquiv K L e

end

end Classification

section Cardinal

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K] [IsAlgClosed K]
variable {ι : Type w} (v : ι -> K)

variable {K' : Type u} [Field K'] [Algebra R K'] [IsAlgClosed K']
variable {ι' : Type u} (v' : ι' -> K')

/--
theorem `cardinal_le_max_transcendence_basis` / 定理 `cardinal_le_max_transcendence_basis`

English:
theorem cardinal_le_max_transcendence_basis
  given: (hv : IsTranscendenceBasis R v)
  proof: calc
    Cardinal.lift.{max u w} #K <= Cardinal.lift.{max u w}
        (max #(Algebra.adjoin R (Set.range v)) ℵ₀) := by
      let := isAlgClosure_of_transcendence_basis v hv
      simpa using Algebra.IsAlgebraic.cardinalMk_le_max (Algebra.adjoin R (Set.range v)) K
    _ = Cardinal.lift.{v} (max #(Mv

中文:
定理 cardinal_le_max_transcendence_basis
  条件: (hv : IsTranscendenceBasis R v)
  证明: calc
    Cardinal.lift.{max u w} #K <= Cardinal.lift.{max u w}
        (max #(Algebra.adjoin R (Set.range v)) ℵ₀) := by
      let := isAlgClosure_of_transcendence_basis v hv
      simpa using Algebra.IsAlgebraic.cardinalMk_le_max (Algebra.adjoin R (Set.range v)) K
    _ = Cardinal.lift.{v} (max #(Mv

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.cardinalMk_le_max, Algebra.adjoin, Cardinal, Cardinal.lif, Cardinal.lift, Cardinal.lift_mk_eq, IsAlgebraic, MvPolynomial, Set.range, adjoin, aevalEquiv, aevalEquiv.toEquiv, cardinalMk_le_max, isAlgClosure_of_transcendence_basis, lift_aleph0, lift_max, lift_mk_eq, lift_umax, toEquiv
-/
theorem cardinal_le_max_transcendence_basis (hv : IsTranscendenceBasis R v) :
    Cardinal.lift.{max u w} #K <= max (max (Cardinal.lift.{max v w} #R)
      (Cardinal.lift.{max u v} #ι)) ℵ₀ :=
  calc
    Cardinal.lift.{max u w} #K <= Cardinal.lift.{max u w}
        (max #(Algebra.adjoin R (Set.range v)) ℵ₀) := by
      let := isAlgClosure_of_transcendence_basis v hv
      simpa using Algebra.IsAlgebraic.cardinalMk_le_max (Algebra.adjoin R (Set.range v)) K
    _ = Cardinal.lift.{v} (max #(MvPolynomial ι R) ℵ₀) := by
      rw [lift_max]; rw [← Cardinal.lift_mk_eq.2 ⟨hv.1.aevalEquiv.toEquiv⟩]; rw [lift_aleph0]; rw [← lift_aleph0.{max u v w]; rw [max u w}]; rw [← lift_max]; rw [lift_umax.{max u w]; rw [v}]
    _ <= Cardinal.lift.{v} (max (max (max (Cardinal.lift #R) (Cardinal.lift #ι)) ℵ₀) ℵ₀) :=
        lift_le.2 (max_le_max MvPolynomial.cardinalMk_le_max_lift le_rfl)
    _ = _ := by simp

/--
theorem `cardinal_le_max_transcendence_basis'` / 定理 `cardinal_le_max_transcendence_basis'`

English:
theorem cardinal_le_max_transcendence_basis'
  given: (hv : IsTranscendenceBasis R v')
  proof: by
  simpa using cardinal_le_max_transcendence_basis v' hv

中文:
定理 cardinal_le_max_transcendence_basis'
  条件: (hv : IsTranscendenceBasis R v')
  证明: by
  simpa using cardinal_le_max_transcendence_basis v' hv

Depends on / 依赖: cardinal_le_max_transcendence_basis
-/
theorem cardinal_le_max_transcendence_basis' (hv : IsTranscendenceBasis R v') :
    #K' <= max (max #R #ι') ℵ₀ := by
  simpa using cardinal_le_max_transcendence_basis v' hv

/--
theorem `cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt` / 定理 `cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt`

English:
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt
  statement: [Nontrivial R]
  proof: have : ℵ₀ <= Cardinal.lift.{max u v} #ι := le_of_not_gt fun h => not_le_of_gt
(show ℵ₀ < Cardinal.lift.{max u w} #K by simpa)
    calc
      Cardinal.lift.{max u w, v} #K <= max (max (Cardinal.lift.{max v w, u} #R)
        (Cardinal.lift.{max u v, w} #ι)) ℵ₀ := cardinal_le_max_transcendence_basis v 

中文:
定理 cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt
  结论: [Nontrivial R]
  证明: have : ℵ₀ <= Cardinal.lift.{max u v} #ι := le_of_not_gt fun h => not_le_of_gt
(show ℵ₀ < Cardinal.lift.{max u w} #K by simpa)
    calc
      Cardinal.lift.{max u w, v} #K <= max (max (Cardinal.lift.{max v w, u} #R)
        (Cardinal.lift.{max u v, w} #ι)) ℵ₀ := cardinal_le_max_transcendence_basis v 

Depends on / 依赖: Cardina, Cardinal, Cardinal.lift, Cardinal.lift_injective, cardinal_le_max_transcendence_basis, le_antisymm, le_of_lt, le_of_not_gt, le_rfl, lift_injective, max_le, not_le_of_gt
-/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt [Nontrivial R]
    (hv : IsTranscendenceBasis R v) (hR : #R <= ℵ₀) (hK : ℵ₀ < #K) :
    Cardinal.lift.{w} #K = Cardinal.lift.{v} #ι :=
  have : ℵ₀ <= Cardinal.lift.{max u v} #ι := le_of_not_gt fun h => not_le_of_gt
(show ℵ₀ < Cardinal.lift.{max u w} #K by simpa)
    calc
      Cardinal.lift.{max u w, v} #K <= max (max (Cardinal.lift.{max v w, u} #R)
        (Cardinal.lift.{max u v, w} #ι)) ℵ₀ := cardinal_le_max_transcendence_basis v hv
      _ <= _ := max_le (max_le (by simpa) (by simpa using le_of_lt h)) le_rfl
  suffices Cardinal.lift.{max u w} #K = Cardinal.lift.{max u v} #ι
    from Cardinal.lift_injective.{u, max v w} (by simpa)
  le_antisymm
    (calc
      Cardinal.lift.{max u w} #K <= max (max
        (Cardinal.lift.{max v w} #R) (Cardinal.lift.{max u v} #ι)) ℵ₀ :=
        cardinal_le_max_transcendence_basis v hv
      _ = Cardinal.lift #ι := by
        rw [max_eq_left]; rw [max_eq_right]
        · exact le_trans (by simpa using hR) this
        · exact le_max_of_le_right this)
    (lift_mk_le.2 ⟨⟨v, hv.1.injective⟩⟩)

/--
theorem `cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'` / 定理 `cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'`

English:
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
  statement: [Nontrivial R]
  proof: by
  simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt v' hv hR hK

中文:
定理 cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
  结论: [Nontrivial R]
  证明: by
  simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt v' hv hR hK

Depends on / 依赖: cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt
-/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' [Nontrivial R]
    (hv : IsTranscendenceBasis R v') (hR : #R <= ℵ₀) (hK : ℵ₀ < #K') : #K' = #ι' := by
  simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt v' hv hR hK

end Cardinal

variable {K : Type u} {L : Type v} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]

/--
theorem `ringEquiv_of_equiv_of_charZero` / 定理 `ringEquiv_of_equiv_of_charZero`

English:
theorem ringEquiv_of_equiv_of_charZero
  statement: [CharZero K] [CharZero L] (hK : ℵ₀ < #K)
  proof: by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Int K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis Int L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardina

中文:
定理 ringEquiv_of_equiv_of_charZero
  结论: [CharZero K] [CharZero L] (hK : ℵ₀ < #K)
  证明: by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Int K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis Int L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardina

Depends on / 依赖: Cardinal, Cardinal.lift, Cardinal.lift_mk_eq, aleph0_lt_lift, cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt, exists_isTranscendenceBasis, le_of_eq, lift_injective, lift_mk_eq, mk_int
-/
theorem ringEquiv_of_equiv_of_charZero [CharZero K] [CharZero L] (hK : ℵ₀ < #K)
    (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Int K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis Int L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        hs (le_of_eq mk_int) hK)]; rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        ht (le_of_eq mk_int) hL)]
    exact Cardinal.lift_mk_eq'.2 hKL
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 this
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩

/--
theorem `ringEquiv_of_Cardinal_eq_of_charP` / 定理 `ringEquiv_of_Cardinal_eq_of_charP`

English:
theorem ringEquiv_of_Cardinal_eq_of_charP
  statement: (p : Nat) [Fact p.Prime] [CharP K p] [CharP L p]
  proof: by
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  let : Algebra (ZMod p) L := ZMod.algebra _ _
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis (ZMod p) L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, alep

中文:
定理 ringEquiv_of_Cardinal_eq_of_charP
  结论: (p : 自然数) [Fact p.Prime] [CharP K p] [CharP L p]
  证明: by
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  let : Algebra (ZMod p) L := ZMod.algebra _ _
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis (ZMod p) L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, alep
-/
private theorem ringEquiv_of_Cardinal_eq_of_charP (p : Nat) [Fact p.Prime] [CharP K p] [CharP L p]
    (hK : ℵ₀ < #K) (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  let : Algebra (ZMod p) L := ZMod.algebra _ _
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis (ZMod p) L
  have hL : ℵ₀ < #L := by
    rwa [← aleph0_lt_lift.{v, u}, ← lift_mk_eq'.2 hKL, aleph0_lt_lift]
  have : Cardinal.lift.{v} #s = Cardinal.lift.{u} #t := by
    rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        hs (le_of_lt (lt_aleph0_of_finite _)) hK)]; rw [← lift_injective (cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _
        ht (le_of_lt (lt_aleph0_of_finite _)) hL)]
    exact Cardinal.lift_mk_eq'.2 hKL
  obtain ⟨e⟩ := Cardinal.lift_mk_eq'.1 this
  exact ⟨equivOfTranscendenceBasis _ _ e hs ht⟩

/--
theorem `ringEquiv_of_equiv_of_char_eq` / 定理 `ringEquiv_of_equiv_of_char_eq`

English:
theorem ringEquiv_of_equiv_of_char_eq
  statement: (p : Nat) [CharP K p] [CharP L p] (hK : ℵ₀ < #K)
  proof: by
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  · have : Fact p.Prime := ⟨hp⟩
    exact ringEquiv_of_Cardinal_eq_of_charP p hK hKL
  · simp only [hp] at *
    let : CharZero K := CharP.charP_to_charZero K
    let : CharZero L := CharP.charP_to_charZero L
    exact ringEquiv_of_equiv_of_

中文:
定理 ringEquiv_of_equiv_of_char_eq
  结论: (p : 自然数) [CharP K p] [CharP L p] (hK : ℵ₀ < #K)
  证明: by
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  · have : Fact p.Prime := ⟨hp⟩
    exact ringEquiv_of_Cardinal_eq_of_charP p hK hKL
  · simp only [hp] at *
    let : CharZero K := CharP.charP_to_charZero K
    let : CharZero L := CharP.charP_to_charZero L
    exact ringEquiv_of_equiv_of_

Depends on / 依赖: CharP.charP_to_charZero, CharP.char_is_prime_or_zero, CharZero, charP_to_charZero, char_is_prime_or_zero, p.Prime, ringEquiv_of_Cardinal_eq_of_charP, ringEquiv_of_equiv_of_charZero
-/
theorem ringEquiv_of_equiv_of_char_eq (p : Nat) [CharP K p] [CharP L p] (hK : ℵ₀ < #K)
    (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) := by
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  · have : Fact p.Prime := ⟨hp⟩
    exact ringEquiv_of_Cardinal_eq_of_charP p hK hKL
  · simp only [hp] at *
    let : CharZero K := CharP.charP_to_charZero K
    let : CharZero L := CharP.charP_to_charZero L
    exact ringEquiv_of_equiv_of_charZero hK hKL

end IsAlgClosed
