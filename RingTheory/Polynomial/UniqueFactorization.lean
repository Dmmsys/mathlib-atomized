/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Unique factorization for univariate and multivariate polynomials

## Main results
* `Polynomial.wfDvdMonoid`:
  If an integral domain is a `WFDvdMonoid`, then so is its polynomial ring.
* `Polynomial.uniqueFactorizationMonoid`, `MvPolynomial.uniqueFactorizationMonoid`:
  If an integral domain is a `UniqueFactorizationMonoid`, then so is its polynomial ring (of any
  number of variables).
-/

@[expose] public section

noncomputable section

open Polynomial

universe u v

namespace Polynomial

variable {R : Type*} [CommSemiring R] [NoZeroDivisors R] [WfDvdMonoid R] {f : R[X]}

instance (priority := 100) wfDvdMonoid : WfDvdMonoid R[X] where
  wf := by
    classical
      refine
        RelHomClass.wellFounded
          (⟨fun p : R[X] =>
              ((if p = 0 then ⊤ else ↑p.degree : WithTop (WithBot Nat)), p.leadingCoeff), ?_⟩ :
            DvdNotUnit ->r Prod.Lex (· < ·) DvdNotUnit)
          (wellFounded_lt.prod_lex ‹WfDvdMonoid R›.wf)
      rintro a b ⟨ane0, ⟨c, ⟨not_unit_c, rfl⟩⟩⟩
      rw [Polynomial.degree_mul]; rw [if_neg ane0]
      split_ifs with hac
      · rw [hac, Polynomial.leadingCoeff_zero]
        apply Prod.Lex.left
        exact WithTop.coe_lt_top _
      have cne0 : c != 0 := right_ne_zero_of_mul hac
      simp only [Polynomial.leadingCoeff_mul]
      by_cases hdeg : c.degree = (0 : Nat)
      · simp only [hdeg, Nat.cast_zero, add_zero]
        refine Prod.Lex.right _ ⟨?_, ⟨c.leadingCoeff, fun unit_c => not_unit_c ?_, rfl⟩⟩
        · rwa [Ne, Polynomial.leadingCoeff_eq_zero]
        rw [Polynomial.isUnit_iff]; rw [Polynomial.eq_C_of_degree_eq_zero hdeg]
        use c.leadingCoeff, unit_c
        rw [Polynomial.leadingCoeff]; rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
      · apply Prod.Lex.left
        rw [Polynomial.degree_eq_natDegree cne0] at *
        simp only [Nat.cast_inj] at hdeg
        rw [WithTop.coe_lt_coe]; rw [Polynomial.degree_eq_natDegree ane0]; rw [← Nat.cast_add]; rw [Nat.cast_lt]
        exact lt_add_of_pos_right _ (Nat.pos_of_ne_zero hdeg)

variable [Nontrivial R]

/--
theorem `exists_irreducible_of_degree_pos` / 定理 `exists_irreducible_of_degree_pos`

English:
theorem exists_irreducible_of_degree_pos
  given: (hf : 0 < f.degree)
  statement: exists g, Irreducible g ∧ g ∣ f
  proof: WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gt hf <| degree_eq_zero_of_isUnit huf)
fun hf0 => not_lt_of_gt hf hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _

中文:
定理 存在_irreducible_of_degree_pos
  条件: (hf : 0 < f.degree)
  结论: 存在 g, 不可约 g ∧ g ∣ f
  证明: WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gt hf <| degree_eq_zero_of_isUnit huf)
fun hf0 => not_lt_of_gt hf hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.exists_irreducible_factor, WithBot, WithBot.bot_lt_coe, bot_lt_coe, degree_eq_zero_of_isUnit, degree_zero, exists_irreducible_factor, hf0.symm, ne_of_gt, not_lt_of_gt
-/
theorem exists_irreducible_of_degree_pos (hf : 0 < f.degree) : exists g, Irreducible g ∧ g ∣ f :=
  WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gt hf <| degree_eq_zero_of_isUnit huf)
fun hf0 => not_lt_of_gt hf hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _

/--
theorem `exists_irreducible_of_natDegree_pos` / 定理 `exists_irreducible_of_natDegree_pos`

English:
theorem exists_irreducible_of_natDegree_pos
  given: (hf : 0 < f.natDegree)
  statement: exists g, Irreducible g ∧ g ∣ f
  proof: exists_irreducible_of_degree_pos by
    contrapose! hf
    exact natDegree_le_of_degree_le hf

中文:
定理 存在_irreducible_of_natDegree_pos
  条件: (hf : 0 < f.natDegree)
  结论: 存在 g, 不可约 g ∧ g ∣ f
  证明: exists_irreducible_of_degree_pos by
    contrapose! hf
    exact natDegree_le_of_degree_le hf

Depends on / 依赖: contrapose, exists_irreducible_of_degree_pos, natDegree_le_of_degree_le
-/
theorem exists_irreducible_of_natDegree_pos (hf : 0 < f.natDegree) : exists g, Irreducible g ∧ g ∣ f :=
exists_irreducible_of_degree_pos by
    contrapose! hf
    exact natDegree_le_of_degree_le hf

/--
theorem `exists_irreducible_of_natDegree_ne_zero` / 定理 `exists_irreducible_of_natDegree_ne_zero`

English:
theorem exists_irreducible_of_natDegree_ne_zero
  given: (hf : f.natDegree != 0)
  proof: exists_irreducible_of_natDegree_pos Nat.pos_of_ne_zero hf

中文:
定理 存在_irreducible_of_natDegree_ne_zero
  条件: (hf : f.natDegree != 0)
  证明: exists_irreducible_of_natDegree_pos Nat.pos_of_ne_zero hf

Depends on / 依赖: Nat.pos_of_ne_zero, exists_irreducible_of_natDegree_pos, pos_of_ne_zero
-/
theorem exists_irreducible_of_natDegree_ne_zero (hf : f.natDegree != 0) :
    exists g, Irreducible g ∧ g ∣ f :=
exists_irreducible_of_natDegree_pos Nat.pos_of_ne_zero hf

end Polynomial

section UniqueFactorizationDomain

variable (σ : Type v) {D : Type u} [CommRing D] [UniqueFactorizationMonoid D]

open UniqueFactorizationMonoid

namespace Polynomial

instance (priority := 100) uniqueFactorizationMonoid : UniqueFactorizationMonoid D[X] := by
  let := Classical.arbitrary (NormalizedGCDMonoid D)
  exact ufm_of_decomposition_of_wfDvdMonoid

/-- If `D` is a unique factorization domain, `f` is a non-zero polynomial in `D[X]`, then `f` has
only finitely many monic factors.
(Note that its factors up to unit may be more than monic factors.)
See also `UniqueFactorizationMonoid.fintypeSubtypeDvd`. -/
@[instance_reducible]
/--
Definition of `fintypeSubtypeMonicDvd` / `fintypeSubtypeMonicDvd` 的定义

English:
definition fintypeSubtypeMonicDvd
  signature: (f : D[X]) (hf : f != 0)
  body: by
  set G := { g : D[X] // g.Monic ∧ g ∣ f }
  let y : Associates D[X] := Associates.mk f
  have hy : y != 0 := Associates.mk_ne_zero.mpr hf
  let H := { x : Associates D[X] // x ∣ y }
  let hfin : Fintype H := UniqueFactorizationMonoid.fintypeSubtypeDvd y hy
  let i : G -> H := fun x => ⟨Associate

中文:
定义 fintypeSubtypeMonicDvd
  签名: (f : D[X]) (hf : f != 0)
  定义体: by
  set G := { g : D[X] // g.Monic ∧ g ∣ f }
  let y : Associates D[X] := Associates.mk f
  have hy : y != 0 := Associates.mk_ne_zero.mpr hf
  let H := { x : Associates D[X] // x ∣ y }
  let hfin : Fintype H := UniqueFactorizationMonoid.fintypeSubtypeDvd y hy
  let i : G -> H := fun x => ⟨Associate

Depends on / 依赖: Associates, Associates.mk, Associates.mk_dvd_mk, Associates.mk_eq_mk_iff_associated.mp, Associates.mk_ne_zero.mpr, Fintype, Fintype.ofInjective, Subtype, Subtype.mk.injEq, UniqueFactorizationMonoid, UniqueFactorizationMonoid.fintypeSubtypeDvd, eq_of_monic_of_associated, fintypeSubtypeDvd, g.Monic, mk_dvd_mk, mk_eq_mk_iff_associated, mk_ne_zero, ofInjective
-/
noncomputable def fintypeSubtypeMonicDvd (f : D[X]) (hf : f != 0) :
    Fintype { g : D[X] // g.Monic ∧ g ∣ f } := by
  set G := { g : D[X] // g.Monic ∧ g ∣ f }
  let y : Associates D[X] := Associates.mk f
  have hy : y != 0 := Associates.mk_ne_zero.mpr hf
  let H := { x : Associates D[X] // x ∣ y }
  let hfin : Fintype H := UniqueFactorizationMonoid.fintypeSubtypeDvd y hy
  let i : G -> H := fun x => ⟨Associates.mk x.1, Associates.mk_dvd_mk.2 x.2.2⟩
  refine Fintype.ofInjective i fun x y heq => ?_
  rw [Subtype.mk.injEq] at heq ⊢
  exact eq_of_monic_of_associated x.2.1 y.2.1 (Associates.mk_eq_mk_iff_associated.mp heq)

end Polynomial

namespace MvPolynomial
variable (d : Nat)

/--
theorem `uniqueFactorizationMonoid_of_fintype` / 定理 `uniqueFactorizationMonoid_of_fintype`

English:
theorem uniqueFactorizationMonoid_of_fintype
  given: [Finite σ]
  proof: have := Fintype.ofFinite σ
(renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid by
    induction Fintype.card σ with
    | zero =>
      apply (isEmptyAlgEquiv D (Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
      infer_instance
    | succ d hd =>
      apply (finSuccE

中文:
定理 uniqueFactorizationMonoid_of_fintype
  条件: [有限 σ]
  证明: have := Fintype.ofFinite σ
(renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid by
    induction Fintype.card σ with
    | zero =>
      apply (isEmptyAlgEquiv D (Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
      infer_instance
    | succ d hd =>
      apply (finSuccE
-/
private theorem uniqueFactorizationMonoid_of_fintype [Finite σ] :
    UniqueFactorizationMonoid (MvPolynomial σ D) :=
  have := Fintype.ofFinite σ
(renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid by
    induction Fintype.card σ with
    | zero =>
      apply (isEmptyAlgEquiv D (Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
      infer_instance
    | succ d hd =>
      apply (finSuccEquiv D d).toMulEquiv.symm.uniqueFactorizationMonoid
      exact Polynomial.uniqueFactorizationMonoid

instance (priority := 100) uniqueFactorizationMonoid :
    UniqueFactorizationMonoid (MvPolynomial σ D) := by
  rw [iff_exists_prime_factors]
  intro a ha; obtain ⟨s, a', rfl⟩ := exists_finset_rename a
  obtain ⟨w, h, u, hw⟩ :=
    iff_exists_prime_factors.1 (uniqueFactorizationMonoid_of_fintype s) a' fun h =>
ha by simp [h]
  exact
    ⟨w.map (rename (↑)), fun b hb =>
      let ⟨b', hb', he⟩ := Multiset.mem_map.1 hb
      he ▸ (prime_rename_iff (σ := σ) ↑s).2 (h b' hb'),
      Units.map (@rename s σ D _ (↑)).toRingHom.toMonoidHom u, by
      rw [Multiset.prod_hom]; rw [Units.coe_map]; rw [AlgHom.toRingHom_eq_coe]; rw [RingHom.toMonoidHom_eq_coe]; rw [AlgHom.toRingHom_toMonoidHom]; rw [MonoidHom.coe_coe]; rw [← map_mul]; rw [hw]⟩

end MvPolynomial

end UniqueFactorizationDomain

/--
theorem `Polynomial.exists_monic_irreducible_factor` / 定理 `Polynomial.exists_monic_irreducible_factor`

English:
theorem Polynomial.exists_monic_irreducible_factor
  statement: {F : Type*} [Field F] (f : F[X])
  proof: by
  by_cases hf : f = 0
  · exact ⟨X, monic_X, irreducible_X, hf ▸ dvd_zero X⟩
  obtain ⟨g, hi, hf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf
have ha : Associated g (g * C g.leadingCoeff⁻¹) := associated_mul_unit_right _ _
    isUnit_C.2 (leadingCoeff_ne_zero.2 hi.ne_zero).isUnit.inv
  exact ⟨

中文:
定理 多项式.存在_monic_irreducible_factor
  结论: {F : 类型} [域 F] (f : F[X])
  证明: by
  by_cases hf : f = 0
  · exact ⟨X, monic_X, irreducible_X, hf ▸ dvd_zero X⟩
  obtain ⟨g, hi, hf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf
have ha : Associated g (g * C g.leadingCoeff⁻¹) := associated_mul_unit_right _ _
    isUnit_C.2 (leadingCoeff_ne_zero.2 hi.ne_zero).isUnit.inv
  exact ⟨

Depends on / 依赖: Associated, WfDvdMonoid, WfDvdMonoid.exists_irreducible_factor, associated_mul_unit_right, dvd_iff_dvd_left, dvd_zero, exists_irreducible_factor, g.leadingCoeff, ha.dvd_iff_dvd_left, ha.irreducible, hi.ne_zero, irreducible, irreducible_X, isUnit, isUnit.inv, isUnit_C, leadingCoeff, leadingCoeff_ne_zero, monic_X, monic_mul_leadingCoeff_inv
-/
theorem Polynomial.exists_monic_irreducible_factor {F : Type*} [Field F] (f : F[X])
    (hu : ¬IsUnit f) : exists g : F[X], g.Monic ∧ Irreducible g ∧ g ∣ f := by
  by_cases hf : f = 0
  · exact ⟨X, monic_X, irreducible_X, hf ▸ dvd_zero X⟩
  obtain ⟨g, hi, hf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf
have ha : Associated g (g * C g.leadingCoeff⁻¹) := associated_mul_unit_right _ _
    isUnit_C.2 (leadingCoeff_ne_zero.2 hi.ne_zero).isUnit.inv
  exact ⟨_, monic_mul_leadingCoeff_inv hi.ne_zero, ha.irreducible hi, ha.dvd_iff_dvd_left.1 hf⟩
