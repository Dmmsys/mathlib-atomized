/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Algebra.Polynomial.CoeffMem
public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.RingTheory.Spectrum.Prime.Polynomial

/-!
# Chevalley's theorem with complexity bound

⚠ For general usage, see `Mathlib/RingTheory/Spectrum/Prime/Chevalley.lean`.

Chevalley's theorem states that if `f : R → S` is a finitely presented ring hom between commutative
rings, then the image of a constructible set in `Spec S` is a constructible set in `Spec R`.

Constructible sets in the prime spectrum of `R[X]` are made of closed sets in the prime spectrum
(using unions, intersections, and complements), which are themselves made from a family of
polynomials.

We say a closed set *has complexity at most `M`* if it can be written as the zero locus of a family
of at most `M` polynomials each of degree at most `M`. We say a constructible set *has complexity
at most `M`* if it can be written as `(C₁ ∪ ... ∪ Cₖ) \ D` where `k ≤ M`, `C₁, ..., Cₖ` are closed
sets of complexity at most `M` and `D` is a closed set.

This file proves a complexity-aware version of Chevalley's theorem, namely that a constructible set
of complexity at most `M` in `Spec R[X₁, ..., Xₘ]` gets mapped under
`f : R[Y₁, ..., Yₙ] → R[X₁, ..., Xₘ]` to a constructible set of complexity `O_{M, m, n}(1)` in
`Spec R[Y₁, ..., Yₙ]`.

The bound `O_{M, m, n}(1)` we find is of tower type.

## Sketch proof

We first show the result in the case of `C : R → R[X]`. We prove this by induction on the number of
components of the form `(C₁ ∪ ... ∪ Cₖ) \ D`, then by induction again on the number of polynomials
used to describe `(C₁ ∪ ... ∪ Cₖ)`. See the (private) lemma `chevalley_polynomialC`.

Secondly, we prove the result in the case of `C : R → R[X₁, ..., Xₘ]` by composing the first result
with itself `m` times. See the (private) lemma `chevalley_mvPolynomialC`.

Note that, if composing the first result for `C : R → R[X₁]` and `C : R[X₁] → R[X₁, X₂]` naïvely,
the second map `C : R[X₁] → R[X₁, X₂]` won't *see* the `X₁`-degree of the polynomials used to
describe the constructible set in `Spec R[X₁]`. One therefore needs to track a subgroup of the ring
which all coefficients of all used polynomials lie in.

Finally, we deduce the result for any `f : R[Y₁, ..., Yₙ] → R[X₁, ..., Xₘ]` by decomposing it into
two maps `C : R[Y₁, ..., Yₙ] → R[X₁, ..., Xₘ, Y₁, ..., Yₙ]` and
`σ : R[X₁, ..., Xₘ, Y₁, ..., Yₙ] → R[X₁, ..., Xₘ]`. See `chevalley_mvPolynomial_mvPolynomial`.

## Main reference

The structure of the proof follows https://stacks.math.columbia.edu/tag/00FE, although they do
not give an explicit bound on the complexity.

-/

@[expose] public section

variable {R₀ R S M A : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R] [CommRing S] [Algebra R₀ S]
variable [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A] {n : Nat}

open Function Localization MvPolynomial Polynomial TensorProduct PrimeSpectrum
open scoped Pointwise

namespace ChevalleyThm

/-! ### The `C : R → R[X]` case -/

namespace PolynomialC

local notation3 "coeff("p")" => Set.range (Polynomial.coeff p)

variable (n) in
/--
Definition of `DegreeType` / `DegreeType` 的定义

English:
abbreviation DegreeType
  body: (Fin n -> WithBot Nat) ×ₗ Prop

中文:
缩写 DegreeType
  定义体: (Fin n -> WithBot Nat) ×ₗ Prop
-/
private abbrev DegreeType := (Fin n -> WithBot Nat) ×ₗ Prop

variable (R n) in
/-- A type synonym for families of polynomials. This is used in the induction for the case of
`C : R → R[X]` of Chevalley's theorem with complexity bound. -/
@[ext]
/--
Definition of `InductionObj` / `InductionObj` 的定义

English:
structure InductionObj
  parameters: where
  axioms and operations (1):
    - val : Fin n -> R[X]

中文:
结构 InductionObj
  参数: where
  公理与运算 (1 个):
    - val : Fin n -> R[X]
-/
private structure InductionObj where
  /-- The underlying family of polynomials of an induction object. -/
  val : Fin n -> R[X]

namespace InductionObj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (InductionObj R n) (fun _ => Fin n -> R[X])
  body: ⟨InductionObj.val⟩

中文:
实例 :
  签名: CoeFun (InductionObj R n) (fun _ => Fin n -> R[X])
  定义体: ⟨InductionObj.val⟩
-/
private instance : CoeFun (InductionObj R n) (fun _ => Fin n -> R[X]) := ⟨InductionObj.val⟩

variable (R₀) in
/--
Definition of `coeffSubmodule` / `coeffSubmodule` 的定义

English:
definition coeffSubmodule
  signature: (e : InductionObj R n)
  body: .span R₀ ({1} union ⋃ i, coeff(e i))

中文:
定义 coeffSubmodule
  签名: (e : InductionObj R n)
  定义体: .span R₀ ({1} union ⋃ i, coeff(e i))
-/
private def coeffSubmodule (e : InductionObj R n) : Submodule R₀ R :=
  .span R₀ ({1} union ⋃ i, coeff(e i))

/--
lemma `coeffSubmodule_mapRingHom_comp` / 引理 `coeffSubmodule_mapRingHom_comp`

English:
lemma coeffSubmodule_mapRingHom_comp
  given: (e : InductionObj R n) (f : R ->ₐ[R₀] S)
  proof: by
  simp [coeffSubmodule, Submodule.map_span, Set.image_insert_eq, Set.image_iUnion, ← Set.range_comp,
    coeff_map_eq_comp]

中文:
引理 coeffSubmodule_mapRingHom_comp
  条件: (e : InductionObj R n) (f : R ->ₐ[R₀] S)
  证明: by
  simp [coeffSubmodule, Submodule.map_span, Set.image_insert_eq, Set.image_iUnion, ← Set.range_comp,
    coeff_map_eq_comp]
-/
private lemma coeffSubmodule_mapRingHom_comp (e : InductionObj R n) (f : R ->ₐ[R₀] S) :
    ({ val := mapRingHom f ∘ e } : InductionObj S n).coeffSubmodule R₀
      = (e.coeffSubmodule R₀).map f.toLinearMap := by
  simp [coeffSubmodule, Submodule.map_span, Set.image_insert_eq, Set.image_iUnion, ← Set.range_comp,
    coeff_map_eq_comp]

variable {e T : InductionObj R n}

set_option backward.privateInPublic true in
/--
lemma `coeff_mem_coeffSubmodule` / 引理 `coeff_mem_coeffSubmodule`

English:
lemma coeff_mem_coeffSubmodule
  given: {i : Fin n} {d : Nat}
  proof: Submodule.subset_span .inr Set.mem_iUnion.2 ⟨i, Set.mem_range_self _⟩

中文:
引理 coeff_mem_coeffSubmodule
  条件: {i : Fin n} {d : 自然数}
  证明: Submodule.subset_span .inr Set.mem_iUnion.2 ⟨i, Set.mem_range_self _⟩
-/
private lemma coeff_mem_coeffSubmodule {i : Fin n} {d : Nat} :
    (e i).coeff d in e.coeffSubmodule R₀ :=
Submodule.subset_span .inr Set.mem_iUnion.2 ⟨i, Set.mem_range_self _⟩

set_option backward.privateInPublic true in
/--
lemma `one_mem_coeffSubmodule` / 引理 `one_mem_coeffSubmodule`

English:
lemma one_mem_coeffSubmodule
  statement: 1 in e.coeffSubmodule R₀
  proof: Submodule.subset_span (.inl rfl)

中文:
引理 one_mem_coeffSubmodule
  结论: 1 in e.coeffSubmodule R₀
  证明: Submodule.subset_span (.inl rfl)
-/
private lemma one_mem_coeffSubmodule : 1 in e.coeffSubmodule R₀ := Submodule.subset_span (.inl rfl)

set_option backward.privateInPublic true in
/--
lemma `one_le_coeffSubmodule` / 引理 `one_le_coeffSubmodule`

English:
lemma one_le_coeffSubmodule
  statement: 1 <= e.coeffSubmodule R₀
  proof: by
  rw [Submodule.one_eq_span]; rw [Submodule.span_le]; rw [Set.singleton_subset_iff]
  exact one_mem_coeffSubmodule

中文:
引理 one_le_coeffSubmodule
  结论: 1 <= e.coeffSubmodule R₀
  证明: by
  rw [Submodule.one_eq_span]; rw [Submodule.span_le]; rw [Set.singleton_subset_iff]
  exact one_mem_coeffSubmodule
-/
private lemma one_le_coeffSubmodule : 1 <= e.coeffSubmodule R₀ := by
  rw [Submodule.one_eq_span]; rw [Submodule.span_le]; rw [Set.singleton_subset_iff]
  exact one_mem_coeffSubmodule

set_option backward.privateInPublic true in
variable (e) in
/--
Definition of `degree` / `degree` 的定义

English:
definition degree
  signature: : DegreeType n
  body: toLex (Polynomial.degree ∘ e, ¬ exists i, (e i).Monic ∧ forall j, e j != 0 -> (e i).degree <= (e j).degree)

中文:
定义 degree
  签名: : DegreeType n
  定义体: toLex (Polynomial.degree ∘ e, ¬ exists i, (e i).Monic ∧ forall j, e j != 0 -> (e i).degree <= (e j).degree)
-/
private def degree : DegreeType n :=
  toLex (Polynomial.degree ∘ e, ¬ exists i, (e i).Monic ∧ forall j, e j != 0 -> (e i).degree <= (e j).degree)

set_option backward.privateInPublic true in
/--
lemma `ofLex_degree_fst` / 引理 `ofLex_degree_fst`

English:
lemma ofLex_degree_fst
  given: (i)
  statement: (ofLex e.degree).fst i = (e i).degree
  proof: rfl

中文:
引理 ofLex_degree_fst
  条件: (i)
  结论: (ofLex e.degree).fst i = (e i).degree
  证明: rfl
-/
@[simp] private lemma ofLex_degree_fst (i) : (ofLex e.degree).fst i = (e i).degree := rfl

set_option backward.privateInPublic true in
/--
lemma `ofLex_degree_snd` / 引理 `ofLex_degree_snd`

English:
lemma ofLex_degree_snd
  proof: .rfl

中文:
引理 ofLex_degree_snd
  证明: .rfl
-/
private lemma ofLex_degree_snd :
    (ofLex e.degree).snd ↔
     ¬ exists i, (e i).Monic ∧ forall j, e j != 0 -> (e i).degree <= (e j).degree := .rfl

set_option backward.privateInPublic true in
variable (e) in
/--
Definition of `degBound` / `degBound` 的定义

English:
definition degBound
  signature: : Nat
  body: ∑ i, (e i).degree.succ

中文:
定义 degBound
  签名: : 自然数
  定义体: ∑ i, (e i).degree.succ
-/
private def degBound : Nat := ∑ i, (e i).degree.succ

set_option backward.privateInPublic true in
variable (e) in
/--
Definition of `powBound` / `powBound` 的定义

English:
definition powBound
  signature: : Nat
  body: e.degBound ^ e.degBound

中文:
定义 powBound
  签名: : 自然数
  定义体: e.degBound ^ e.degBound
-/
private def powBound : Nat := e.degBound ^ e.degBound

set_option backward.privateInPublic true in
/--
lemma `powBound_ne_zero` / 引理 `powBound_ne_zero`

English:
lemma powBound_ne_zero
  statement: e.powBound != 0
  proof: Nat.pow_self_pos.ne'

中文:
引理 powBound_ne_zero
  结论: e.powBound != 0
  证明: Nat.pow_self_pos.ne'
-/
private lemma powBound_ne_zero : e.powBound != 0 := Nat.pow_self_pos.ne'

set_option backward.privateInPublic true in
variable (R₀ R n e) in
/--
Definition of `Statement` / `Statement` 的定义

English:
definition Statement
  signature: : Prop
  body: forall f : R[X], exists T : ConstructibleSetData R,
    comap Polynomial.C '' (zeroLocus (Set.range e) \ zeroLocus {f}) = T.toSet ∧
    forall C in T, C.n <= e.degBound ∧ forall i, C.g i in e.coeffSubmodule R₀ ^ e.powBound

中文:
定义 Statement
  签名: : 命题
  定义体: forall f : R[X], exists T : ConstructibleSetData R,
    comap Polynomial.C '' (zeroLocus (Set.range e) \ zeroLocus {f}) = T.toSet ∧
    forall C in T, C.n <= e.degBound ∧ forall i, C.g i in e.coeffSubmodule R₀ ^ e.powBound
-/
private def Statement : Prop := forall f : R[X], exists T : ConstructibleSetData R,
    comap Polynomial.C '' (zeroLocus (Set.range e) \ zeroLocus {f}) = T.toSet ∧
    forall C in T, C.n <= e.degBound ∧ forall i, C.g i in e.coeffSubmodule R₀ ^ e.powBound

end InductionObj

open InductionObj

universe u

/--
lemma `induction_structure` / 引理 `induction_structure`

English:
lemma induction_structure
  statement: (n : Nat)
  proof: by
  classical
  set v := e.degree with hv
  clear_value v
  induction v using WellFoundedLT.induction generalizing R with
  | ind v H_IH =>
    by_cases he0 : e = ⟨0⟩
    · exact he0 ▸ hP₁ R
    cases subsingleton_or_nontrivial R
    · convert! hP₁ R; ext; exact Subsingleton.elim _ _
    simp only 

中文:
引理 induction_structure
  结论: (n : 自然数)
  证明: by
  classical
  set v := e.degree with hv
  clear_value v
  induction v using WellFoundedLT.induction generalizing R with
  | ind v H_IH =>
    by_cases he0 : e = ⟨0⟩
    · exact he0 ▸ hP₁ R
    cases subsingleton_or_nontrivial R
    · convert! hP₁ R; ext; exact Subsingleton.elim _ _
    simp only 
-/
private lemma induction_structure (n : Nat)
    (P : forall (R : Type u) [CommRing R], (InductionObj R n) -> Prop)
    (hP₁ : forall (R) [CommRing R], P R ⟨0⟩)
    (hP₂ : forall (R) [CommRing R] (e : InductionObj R n) (i : Fin n),
      (e.1 i).Monic -> (forall j != i, e.1 j = 0) -> P R e)
    (hP₃ : forall (R) [CommRing R] (e : InductionObj R n) (i j : Fin n),
      (e.1 i).Monic -> (e.1 i).degree <= (e.1 j).degree -> i != j ->
      P R ⟨update e.1 j (e.1 j %ₘ e.1 i)⟩ -> P R e)
    (hP₄ : forall (R) [CommRing R] (c : R) (i : Fin n) (e : InductionObj R n), c = (e.1 i).leadingCoeff ->
      c != 0 ->
      P (Away c) ⟨Polynomial.C (IsLocalization.Away.invSelf (S := Away c) c) •
        mapRingHom (algebraMap _ _) ∘ e⟩ ->
      P (R ⧸ Ideal.span {c}) ⟨mapRingHom (algebraMap _ _) ∘ e⟩ -> P R e)
    {R} [CommRing R] (e : InductionObj R n) : P R e := by
  classical
  set v := e.degree with hv
  clear_value v
  induction v using WellFoundedLT.induction generalizing R with
  | ind v H_IH =>
    by_cases he0 : e = ⟨0⟩
    · exact he0 ▸ hP₁ R
    cases subsingleton_or_nontrivial R
    · convert! hP₁ R; ext; exact Subsingleton.elim _ _
    simp only [InductionObj.ext_iff, funext_iff, Pi.zero_apply, not_forall] at he0
    -- Case I : The `e i ≠ 0` with minimal degree has invertible leading coefficient
    by_cases H : (exists i, (e.1 i).Monic ∧ forall j, e.1 j != 0 -> (e.1 i).degree <= (e.1 j).degree)
    · obtain ⟨i, hi, i_min⟩ := H
      -- Case I.ii : `e j = 0` for all `j ≠ i`.
      by_cases! H' : forall j != i, e.1 j = 0
      -- then `I = Ideal.span {e i}`
      · exact hP₂ R e i hi H'
      -- Case I.i : There is another `e j ≠ 0`
      · obtain ⟨j, hj, hj'⟩ := H'
        replace i_min := i_min j hj'
        -- then we can replace `e j` with `e j %ₘ (C h.unit⁻¹ * e i) `
        -- with `h : IsUnit (e i).leadingCoeff`.
        apply hP₃ R e i j hi i_min (hj.symm) (H_IH _ ?_ _ rfl)
        refine .left _ _ (lt_of_le_of_ne (b := (ofLex v).1) ?_ ?_)
        · intro k
          simp only [comp_apply, update_apply, hv]
          split_ifs with hjk
          · rw [hjk]
            exact (degree_modByMonic_le _ hi).trans i_min
          · exact le_rfl
        · simp only [hv, ne_eq, not_forall, funext_iff,
            comp_apply]
          use j
          simp only [update_self]
          refine ((degree_modByMonic_lt _ hi).trans_le i_min).ne
    -- Case II : The `e i ≠ 0` with minimal degree has non-invertible leading coefficient
    obtain ⟨i, hi, i_min⟩ : exists i, e.1 i != 0 ∧ forall j, e.1 j != 0 -> (e.1 i).degree <= (e.1 j).degree := by
      have : exists n : Nat, exists i, (e.1 i).degree = n ∧ (e.1 i) != 0 := by
        obtain ⟨i, hi⟩ := he0; exact ⟨(e.1 i).natDegree, i, degree_eq_natDegree hi, hi⟩
      let m := Nat.find this
      obtain ⟨i, hi, hi'⟩ : exists i, (e.1 i).degree = m ∧ (e.1 i) != 0 := Nat.find_spec this
      refine ⟨i, hi', fun j hj => ?_⟩
      refine hi.le.trans ?_
      rw [degree_eq_natDegree hj]; rw [Nat.cast_le]
      exact Nat.find_min' _ ⟨j, degree_eq_natDegree hj, hj⟩
    -- We replace `R` by `R ⧸ Ideal.span {(e i).leadingCoeff}` where `(e i).degree` is lowered
    -- and `Away (e i).leadingCoeff` where `(e i).leadingCoeff` becomes invertible.
    apply hP₄ _ _ i e rfl (by simpa using hi) (H_IH _ ?_ _ rfl) (H_IH _ ?_ _ rfl)
    · rw [hv, Prod.Lex.lt_iff']
      constructor
      · intro j
        simp only [coe_mapRingHom, InductionObj.ofLex_degree_fst, Pi.smul_apply,
          comp_apply, smul_eq_mul]
        refine ((degree_mul_le _ _).trans (add_le_add degree_C_le degree_map_le)).trans ?_
        simp
      rw [lt_iff_le_not_ge]
      simp only [coe_mapRingHom, funext_iff, InductionObj.ofLex_degree_fst, Pi.smul_apply,
        comp_apply, smul_eq_mul, show (ofLex e.degree).2 from H,
        le_Prop_eq, implies_true, true_implies, true_and]
      simp only [InductionObj.ofLex_degree_snd, Pi.smul_apply, comp_apply, smul_eq_mul,
        ne_eq, not_exists, not_and, not_forall, not_le, not_lt]
      intro h_eq
      refine ⟨i, ?_, ?_⟩
      · rw [Monic.def, ← coeff_natDegree (p := _ * _), natDegree_eq_of_degree_eq (h_eq i),
          Polynomial.coeff_C_mul, Polynomial.coeff_map, coeff_natDegree, mul_comm,
          IsLocalization.Away.mul_invSelf]
      · intro j hj; rw [h_eq, h_eq]; exact i_min j fun H => (by simp [H] at hj)
    · rw [hv]
      refine .left _ _ (lt_of_le_of_ne ?_ ?_)
      · intro j; simpa using degree_map_le
      simp only [coe_mapRingHom, ne_eq]
      intro h_eq
      replace h_eq := congr_fun h_eq i
      simp only [Ideal.Quotient.algebraMap_eq, comp_apply, degree_map_eq_iff,
        Ideal.Quotient.mk_singleton_self, ne_eq, not_true_eq_false, false_or] at h_eq
      exact hi h_eq

-- TODO: fix non-terminal simp (large simp set)
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
open IsLocalization in
open Submodule hiding comap in
/--
lemma `induction_aux` / 引理 `induction_aux`

English:
lemma induction_aux
  statement: (R : Type*) [CommRing R] [Algebra R₀ R]
  proof: by
  set q₁ := IsScalarTower.toAlgHom R₀ R (Away c)
  set q₂ := Ideal.Quotient.mkₐ R₀ (.span {c})
  have q₂_surjective : Surjective q₂ := Ideal.Quotient.mk_surjective
  set e₁ : InductionObj (Away c) n :=
    ⟨Polynomial.C (IsLocalization.Away.invSelf (S := Away c) c) • mapRingHom q₁ ∘ e⟩
  set e₂ :

中文:
引理 induction_aux
  结论: (R : 类型) [CommRing R] [Algebra R₀ R]
  证明: by
  set q₁ := IsScalarTower.toAlgHom R₀ R (Away c)
  set q₂ := Ideal.Quotient.mkₐ R₀ (.span {c})
  have q₂_surjective : Surjective q₂ := Ideal.Quotient.mk_surjective
  set e₁ : InductionObj (Away c) n :=
    ⟨Polynomial.C (IsLocalization.Away.invSelf (S := Away c) c) • mapRingHom q₁ ∘ e⟩
  set e₂ :
-/
private lemma induction_aux (R : Type*) [CommRing R] [Algebra R₀ R]
    (c : R) (i : Fin n) (e : InductionObj R n) (hi : c = (e.1 i).leadingCoeff) (hc : c != 0) :
    Statement R₀ (Away c) n
      ⟨Polynomial.C (IsLocalization.Away.invSelf (S := Away c) c) •
        mapRingHom (algebraMap _ _) ∘ e⟩ ->
    Statement R₀ (R ⧸ Ideal.span {c}) n ⟨mapRingHom (algebraMap _ _) ∘ e⟩ ->
      Statement R₀ R n e := by
  set q₁ := IsScalarTower.toAlgHom R₀ R (Away c)
  set q₂ := Ideal.Quotient.mkₐ R₀ (.span {c})
  have q₂_surjective : Surjective q₂ := Ideal.Quotient.mk_surjective
  set e₁ : InductionObj (Away c) n :=
    ⟨Polynomial.C (IsLocalization.Away.invSelf (S := Away c) c) • mapRingHom q₁ ∘ e⟩
  set e₂ : InductionObj (R ⧸ Ideal.span {c}) n := ⟨mapRingHom q₂ ∘ e⟩
  have degBound_e₁_le : e₁.degBound <= e.degBound := by
    unfold degBound
    gcongr with j
exact (degree_mul_le _ _).trans (add_le_of_nonpos_left degree_C_le).trans degree_map_le
  have degBound_e₂_lt : e₂.degBound < e.degBound := by
    unfold degBound
refine Fintype.sum_strictMono Pi.lt_def.2 ⟨fun j => ?_, i, ?_⟩
    · dsimp
      gcongr
      exact degree_map_le
    · gcongr
      exact degree_map_lt (by simp [q₂, ← hi]) (by simpa [hi] using hc)
  intro (H₁ : Statement R₀ _ _ e₁) (H₂ : Statement R₀ _ _ e₂) f
  obtain ⟨T₁, hT₁⟩ := H₁ (mapRingHom q₁ f)
  obtain ⟨T₂, hT₂⟩ := H₂ (mapRingHom q₂ f)
  simp only [forall_and] at hT₁ hT₂
  obtain ⟨hT₁, hT₁deg, hT₁span⟩ := hT₁
  obtain ⟨hT₂, hT₂deg, hT₂span⟩ := hT₂
  -- Lift the tuples of `T₁` from `Away c` to `R`
  let _ : Invertible (q₁ c) :=
    -- TODO(Andrew): add API for `IsLocalization.Away.invSelf`
    ⟨IsLocalization.Away.invSelf c, by simp [q₁, IsLocalization.Away.invSelf], by
      simp [q₁, IsLocalization.Away.invSelf]⟩
  have he₁span :
      e₁.coeffSubmodule R₀ ^ e₁.powBound = ⅟(q₁ c ^ e₁.powBound) •
        (span R₀ ({c} union ⋃ i, coeff(e i)) ^ e₁.powBound).map q₁.toLinearMap := by
    unfold coeffSubmodule
    rw [Submodule.map_pow]; rw [map_span]; rw [invOf_pow]; rw [← smul_pow]; rw [← span_smul]
    simp [Set.image_insert_eq, Set.smul_set_insert, Set.image_iUnion, Set.smul_set_iUnion, q₁, e₁]
    congr! with i
    change _ = IsLocalization.Away.invSelf c • _
    simp [← Set.range_comp, Set.smul_set_range]
    ext
    simp
  replace hT₁span x hx i :=
    smul_mem_pointwise_smul _ (q₁ c ^ e₁.powBound) _ (hT₁span x hx i)
  simp only [he₁span, smul_invOf_smul, smul_eq_mul] at hT₁span
  choose! g₁ hg₁ hq₁g₁ using hT₁span
  -- Lift the constants of `T₁` from `Away c` to `R`
  choose! n₁ f₁ hf₁ using Away.surj (S := Away c) c
  change (forall _, _ * q₁ _ ^ _ = q₁ _) at hf₁
  -- Lift the tuples of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  rw [coeffSubmodule_mapRingHom_comp]; rw [← Submodule.map_pow] at hT₂span
  choose! g₂ hg₂ hq₂g₂ using hT₂span
  -- Lift the constants of `T₂` from `R ⧸ Ideal.span {c}` to `R`
  choose! f₂ hf₂ using Ideal.Quotient.mkₐ_surjective R₀ (I := .span {c})
  change (forall _, q₂ _ = _) at hf₂
  -- Lift everything together
  let S₁ : Finset (BasicConstructibleSetData R) := T₁.image fun x => ⟨c * f₁ x.f, _, g₁ x⟩
  let S₂ : Finset (BasicConstructibleSetData R) := T₂.image fun x => ⟨f₂ x.f, _, Fin.cons c (g₂ x)⟩
  refine ⟨S₁ union S₂, ?_, ?_⟩
  · calc
      comap Polynomial.C '' (zeroLocus (.range e) \ zeroLocus {f})
        = comap q₁ '' (comap Polynomial.C ''
            (comap (mapRingHom q₁.toRingHom) ⁻¹' (zeroLocus (.range e) \ zeroLocus {f}))) union
          comap q₂ '' (comap Polynomial.C ''
            (comap (mapRingHom q₂.toRingHom) ⁻¹' (zeroLocus (.range e) \ zeroLocus {f}))) :=
        Set.image_of_range_union_range_eq_univ (by ext; simp) (by ext; simp)
          (by rw [Ideal.Quotient.mkₐ_toRingHom,
            ← range_comap_algebraMap_localization_compl_eq_range_comap_quotientMk,
            RingHom.algebraMap_toAlgebra]; exact Set.union_compl_self _) _
      _ = (⋃ C in S₁, C.toSet) union ⋃ C in S₂, C.toSet := ?_
      _ = ⋃ C in S₁ union S₂, C.toSet := by
        simpa using (Set.biUnion_union (SetLike.coe S₁) S₂ _).symm
    congr 1
    · convert! congr(comap q₁.toRingHom '' $hT₁)
      · dsimp only [e₁]
        rw [Set.preimage_sdiff]; rw [preimage_comap_zeroLocus]; rw [preimage_comap_zeroLocus]; rw [Set.image_singleton]; rw [Pi.smul_def]; rw [← Set.smul_set_range]; rw [Set.range_comp]
        congr 1
        refine (PrimeSpectrum.zeroLocus_smul_of_isUnit (.map _ ?_) _).symm
        exact isUnit_iff_exists_inv'.mpr ⟨_, IsLocalization.Away.mul_invSelf c⟩
      · rw [ConstructibleSetData.toSet, Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₁, Finset.coe_image, Set.biUnion_image]
        congr! with x hxT₁
        apply Set.injOn_preimage subset_rfl (f := comap q₁.toRingHom)
        · dsimp only [q₁, AlgHom.toRingHom_eq_coe]
          rw [IsScalarTower.coe_toAlgHom]; rw [localization_away_comap_range (S := Localization.Away c) (r := c)]; rw [BasicConstructibleSetData.toSet]; rw [sdiff_eq]; rw [← basicOpen_eq_zeroLocus_compl]; rw [basicOpen_mul]
          exact Set.inter_subset_right.trans Set.inter_subset_left
        · exact Set.image_subset_range ..
        · rw [BasicConstructibleSetData.toSet, BasicConstructibleSetData.toSet, Set.preimage_sdiff,
            preimage_comap_zeroLocus, preimage_comap_zeroLocus, Set.preimage_image_eq]
          swap; · exact localization_comap_injective _ (.powers c)
          simp only [AlgHom.toLinearMap_apply] at hq₁g₁
          simp only [← Set.range_comp, comp_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            hq₁g₁ _ hxT₁, Set.image_singleton, map_mul, ← hf₁, mul_comm x.1, ← mul_assoc,
            ← pow_succ']
          simp only [← smul_eq_mul, ← Set.smul_set_range, ← Set.smul_set_singleton,
            zeroLocus_smul_of_isUnit ((isUnit_of_invertible (q₁ c)).pow _)]
    · convert! congr(comap q₂.toRingHom '' $hT₂)
      · rw [Set.preimage_sdiff, preimage_comap_zeroLocus, preimage_comap_zeroLocus,
          Set.image_singleton, Set.range_comp, AlgHom.toRingHom_eq_coe]
      · rw [ConstructibleSetData.toSet, Set.image_iUnion₂]
        simp_rw [← Finset.mem_coe, S₂, Finset.coe_image, Set.biUnion_image]
        congr! 3 with x hxT₂
        apply Set.injOn_preimage subset_rfl (f := comap q₂.toRingHom)
        · rw [range_comap_of_surjective _ _ q₂_surjective]
          simp only [AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_ker, zeroLocus_span, q₂]
          exact Set.sdiff_subset.trans (zeroLocus_anti_mono (by simp))
        · exact Set.image_subset_range _ _
        · simp only [AlgHom.toLinearMap_apply] at hq₂g₂
          have : q₂ c = 0 := by simp [q₂]
          simp only [BasicConstructibleSetData.toSet, Set.preimage_sdiff, preimage_comap_zeroLocus,
            preimage_comap_zeroLocus,
            Set.preimage_image_eq _ (comap_injective_of_surjective _ q₂_surjective)]
          simp only [Fin.range_cons, Set.image_singleton, Set.image_insert_eq,
            ← Set.range_comp, comp_def]
          simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hq₂g₂ _ hxT₂, hf₂]
          rw [← Set.union_singleton]; rw [zeroLocus_union]; rw [this]; rw [zeroLocus_singleton_zero]; rw [Set.inter_univ]
  · simp only [Finset.mem_union, forall_and, or_imp, Finset.forall_mem_image, S₁, S₂]
    refine ⟨⟨fun x hx => (hT₁deg _ hx).trans degBound_e₁_le,
      fun x hx => (hT₂deg _ hx).trans_lt degBound_e₂_lt⟩,
      fun x hx k => SetLike.mem_of_subset ?_ (hg₁ _ hx _),
      fun x hx => Fin.cons ?_ fun k => SetLike.mem_of_subset ?_ (hg₂ _ hx _)⟩
    · norm_cast
      calc
        span R₀ ({c} union ⋃ i, coeff(e i)) ^ e₁.powBound
        _ <= span R₀ (⋃ i, coeff(e i)) ^ e₁.powBound := by
          gcongr; simpa [Set.insert_subset_iff] using ⟨_, _, hi.symm⟩
        _ <= e.coeffSubmodule R₀ ^ e.powBound := by
          unfold coeffSubmodule powBound
          gcongr
          · exact one_le_coeffSubmodule
          · exact Set.subset_union_right
          · lia
· exact le_self_pow one_le_coeffSubmodule powBound_ne_zero subset_span .inr by
        simpa using ⟨_, _, hi.symm⟩
    · unfold powBound
      gcongr
      · exact one_le_coeffSubmodule
      · lia

/--
lemma `statement` / 引理 `statement`

English:
lemma statement
  statement: forall S : InductionObj R n, Statement R₀ R n S
  proof: by
  intro S; revert R₀; revert S
  apply induction_structure
  · intro R _ R₀ _ _ f
    refine ⟨(Finset.range (f.natDegree + 2)).image fun j => ⟨f.coeff j, 0, 0⟩, ?_, ?_⟩
    · convert! image_comap_C_basicOpen f
      · simp only [basicOpen_eq_zeroLocus_compl, Set.compl_eq_univ_sdiff]
        congr

中文:
引理 statement
  结论: 对任意 S : InductionObj R n, Statement R₀ R n S
  证明: by
  intro S; revert R₀; revert S
  apply induction_structure
  · intro R _ R₀ _ _ f
    refine ⟨(Finset.range (f.natDegree + 2)).image fun j => ⟨f.coeff j, 0, 0⟩, ?_, ?_⟩
    · convert! image_comap_C_basicOpen f
      · simp only [basicOpen_eq_zeroLocus_compl, Set.compl_eq_univ_sdiff]
        congr
-/
private lemma statement : forall S : InductionObj R n, Statement R₀ R n S := by
  intro S; revert R₀; revert S
  apply induction_structure
  · intro R _ R₀ _ _ f
    refine ⟨(Finset.range (f.natDegree + 2)).image fun j => ⟨f.coeff j, 0, 0⟩, ?_, ?_⟩
    · convert! image_comap_C_basicOpen f
      · simp only [basicOpen_eq_zeroLocus_compl, Set.compl_eq_univ_sdiff]
        congr 1
        rw [← Set.univ_subset_iff]
        rintro x _ _ ⟨_, rfl⟩
        exact zero_mem x.asIdeal
      · suffices Set.range f.coeff = ⋃ i < f.natDegree + 2, {f.coeff i} by
          simp [BasicConstructibleSetData.toSet, ConstructibleSetData.toSet,
            ← Set.compl_eq_univ_sdiff, eq_compl_comm (y := zeroLocus _), ← zeroLocus_iUnion₂, this]
        trans f.coeff '' (Set.Iio (f.natDegree + 2))
        · refine ((Set.image_subset_range _ _).antisymm ?_).symm
          rintro _ ⟨i, rfl⟩
          by_cases! hi : i <= f.natDegree
          · exact ⟨i, hi.trans_lt (by simp), rfl⟩
          · exact ⟨f.natDegree + 1, by simp, by simp [f.coeff_eq_zero_of_natDegree_lt hi]⟩
        · ext; simp [eq_comm]
    · simp
  · intro R _ g i hi hi_min _ R₀ _ f
    let M := R[X] ⧸ Ideal.span {g.1 i}
    have : Module.Free R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    have : Module.Finite R M := .of_basis (AdjoinRoot.powerBasis' hi).basis
    refine ⟨(Finset.range (Module.finrank R M)).image
      fun j => ⟨(Algebra.lmul R M (Ideal.Quotient.mk _ f)).charpoly.coeff j, 0, 0⟩, ?_, ?_⟩
    · ext x
      have : zeroLocus (Set.range g.val) = zeroLocus {g.1 i} := by
        rw [Set.range_eq_iUnion]; rw [zeroLocus_iUnion]
        refine (Set.iInter_subset _ _).antisymm (Set.subset_iInter fun j => ?_)
        by_cases hij : i = j
        · subst hij; rfl
        · rw [hi_min j (.symm hij), zeroLocus_singleton_zero]; exact Set.subset_univ _
      rw [this]; rw [← Polynomial.algebraMap_eq]; rw [mem_image_comap_zeroLocus_sdiff]; rw [IsScalarTower.algebraMap_apply R[X] M, isNilpotent_tensor_residueField_iff]
      simp [BasicConstructibleSetData.toSet, ConstructibleSetData.toSet, Set.subset_def, M]
    · simp
  · intro R _ c i j hi hle hne H R₀ _ _ f
    cases subsingleton_or_nontrivial R
    · use ∅
      simp [ConstructibleSetData.toSet, Subsingleton.elim f 0]
    obtain ⟨S, hS, hS'⟩ := H (R₀ := R₀) f
    refine ⟨S, Eq.trans ?_ hS, ?_⟩
    · rw [← zeroLocus_span (Set.range _), ← zeroLocus_span (Set.range _),
        idealSpan_range_update_divByMonic hne]
    · intro C hC
      let c' : InductionObj _ _ := ⟨update c.val j (c.val j %ₘ c.val i)⟩
      have deg_bound₁ : c'.degBound <= c.degBound := by
        dsimp [InductionObj.degBound, c']
        gcongr with k
        · rw [update_apply]
          split_ifs with hkj
          · subst hkj; exact (degree_modByMonic_le _ hi).trans hle
          · rfl
      refine ⟨(hS' C hC).1.trans deg_bound₁, fun k => SetLike.le_def.mp ?_ ((hS' C hC).2 k)⟩
      change c'.coeffSubmodule R₀ ^ c'.powBound <= _
      delta powBound
      suffices hij : c'.coeffSubmodule R₀ <= c.coeffSubmodule R₀ ^ (c.val j).degree.succ by
        by_cases hi' : c.val i = 1
        · gcongr
          · exact c.one_le_coeffSubmodule
          · refine Submodule.span_le.mpr (Set.union_subset ?_ ?_)
            · exact Set.subset_union_left.trans Submodule.subset_span
            · refine Set.iUnion_subset fun k => ?_
              simp only [update_apply, hi', modByMonic_one, c']
              split_ifs
              · rintro _ ⟨_, rfl⟩
                exact zero_mem _
              · exact (Set.subset_iUnion (fun i => coeff(c.val i)) k).trans
                  (Set.subset_union_right.trans Submodule.subset_span)
          rw [Nat.one_le_iff_ne_zero]; rw [← Nat.pos_iff_ne_zero]; rw [InductionObj.degBound]
          refine Fintype.sum_pos (Pi.lt_def.mpr ⟨by positivity, i, by simp [hi']⟩)
        refine (pow_le_pow_left' hij _).trans ?_
        rw [← pow_mul]
        apply pow_le_pow_right' c.one_le_coeffSubmodule
        have deg_bound₂ : c'.degBound < c.degBound := by
          dsimp [InductionObj.degBound, c']
          apply Finset.sum_lt_sum ?_ ⟨j, Finset.mem_univ _, ?_⟩
          · intro k _
            rw [update_apply]
            split_ifs with hkj
            · subst hkj; gcongr; exact (degree_modByMonic_le _ hi).trans hle
            · rfl
          · gcongr; simpa using (degree_modByMonic_lt _ hi).trans_le hle
        calc (c.val j).degree.succ * c'.degBound ^ c'.degBound
          _ <= c.degBound * c.degBound ^ c'.degBound := by
            gcongr
            delta InductionObj.degBound
            exact Finset.single_le_sum (f := fun i => (c.val i).degree.succ)
              (by intros; positivity) (Finset.mem_univ _)
          _ = c.degBound ^ (c'.degBound + 1) := by rw [pow_succ']
          _ <= c.degBound ^ c.degBound := by gcongr <;> lia
      rw [coeffSubmodule]
      simp only [Submodule.span_le, Set.union_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
        Set.iUnion_subset_iff, Set.range_subset_iff, c']
      constructor
      · apply one_le_pow_of_one_le' c.one_le_coeffSubmodule
        rw [Submodule.one_eq_span]
        exact Submodule.subset_span rfl
      · intro l m
        rw [update_apply]
        split_ifs with hlj
        · convert!
          coeff_modByMonic_mem_pow_natDegree_mul _ _ _ (fun _ => coeff_mem_coeffSubmodule)
            one_mem_coeffSubmodule _ (fun _ => coeff_mem_coeffSubmodule) one_mem_coeffSubmodule _
          rw [← pow_succ]; rw [Polynomial.degree_eq_natDegree]; rw [WithBot.succ_natCast]; rw [Nat.cast_id]
          intro e
          simp [show c.val i = 0 by simpa [e] using hle] at hi
        · have : (c.val j).degree.succ != 0 := by
            rw [← Nat.pos_iff_ne_zero]
            apply WithBot.succ_lt_succ (x := ⊥)
            refine lt_of_lt_of_le ?_ hle
            rw [bot_lt_iff_ne_bot]; rw [ne_eq]; rw [degree_eq_bot]
            intro e
            simp [e] at hi
          refine le_self_pow c.one_le_coeffSubmodule this ?_
          exact Submodule.subset_span (.inr (Set.mem_iUnion_of_mem l ⟨m, rfl⟩))
  · intro R _ c i e he hc H₁ H₂ R₀ _ _
    exact induction_aux (R₀ := R₀) R c i e he hc H₁ H₂

end PolynomialC

open PolynomialC InductionObj in
/--
lemma `chevalley_polynomialC` / 引理 `chevalley_polynomialC`

English:
lemma chevalley_polynomialC
  statement: {R : Type*} [CommRing R] (M : Submodule Int R) (hM : 1 in M)
  proof: by
  choose f hf₁ hf₂ hf₃ using fun C : BasicConstructibleSetData R[X] => statement (R₀ := Int) ⟨C.g⟩ C.f
  refine ⟨S.biUnion f, ?_, ?_⟩
  · simp only [BasicConstructibleSetData.toSet, ConstructibleSetData.toSet, Set.image_iUnion,
      Finset.set_biUnion_biUnion, hf₁]
  · simp only [Finset.mem_biUn

中文:
引理 chevalley_polynomialC
  结论: {R : 类型} [CommRing R] (M : Submodule 整数 R) (hM : 1 in M)
  证明: by
  choose f hf₁ hf₂ hf₃ using fun C : BasicConstructibleSetData R[X] => statement (R₀ := Int) ⟨C.g⟩ C.f
  refine ⟨S.biUnion f, ?_, ?_⟩
  · simp only [BasicConstructibleSetData.toSet, ConstructibleSetData.toSet, Set.image_iUnion,
      Finset.set_biUnion_biUnion, hf₁]
  · simp only [Finset.mem_biUn

Depends on / 依赖: BasicConstructibleSetData, BasicConstructibleSetData.toSet, ConstructibleSetData, ConstructibleSetData.toSet, Finset, Finset.le_sup, Finset.mem_biUnion, Finset.set_biUnion_biUnion, S.biUnion, S.degBound, Set.image_iUnion, SetLike, SetLike.le_def.mp, and_imp, biUnion, degBound, degree, degree.succ, forall_exists_index, image_iUnion
-/
lemma chevalley_polynomialC {R : Type*} [CommRing R] (M : Submodule Int R) (hM : 1 in M)
    (S : ConstructibleSetData R[X]) (hS : forall C in S, forall j k, (C.g j).coeff k in M) :
    exists T : ConstructibleSetData R,
      comap Polynomial.C '' S.toSet = T.toSet ∧ forall C in T, C.n <= S.degBound ∧
      forall i, C.g i in M ^ S.degBound ^ S.degBound := by
  choose f hf₁ hf₂ hf₃ using fun C : BasicConstructibleSetData R[X] => statement (R₀ := Int) ⟨C.g⟩ C.f
  refine ⟨S.biUnion f, ?_, ?_⟩
  · simp only [BasicConstructibleSetData.toSet, ConstructibleSetData.toSet, Set.image_iUnion,
      Finset.set_biUnion_biUnion, hf₁]
  · simp only [Finset.mem_biUnion, forall_exists_index, and_imp]
    intro x y hy hx
    have H : degBound ⟨y.g⟩ <= S.degBound :=
      Finset.le_sup (f := fun e => ∑ i, (e.g i).degree.succ) hy
    refine ⟨(hf₂ y x hx).trans H, fun i => SetLike.le_def.mp ?_ (hf₃ y x hx i)⟩
    gcongr
    · simpa [Submodule.one_eq_span]
    · refine Submodule.span_le.mpr ?_
      simp [Set.subset_def, hM, forall_comm (α := R), hS y hy]
    · delta powBound
      by_cases h : S.degBound = 0
      · have : degBound ⟨y.g⟩ = 0 := by nlinarith
        rw [h]; rw [this]
      gcongr
      rwa [Nat.one_le_iff_ne_zero]

/-! ### The `C : R → R[X₁, ..., Xₘ]` case -/

namespace MvPolynomialC

mutual

/--
Definition of `numBound` / `numBound` 的定义

English:
definition numBound
  signature: (k : Nat) (D : Nat -> Nat)

中文:
定义 numBound
  签名: (k : 自然数) (D : 自然数 -> 自然数)
-/
def numBound (k : Nat) (D : Nat -> Nat) : Nat -> Nat
  | 0 => k
  | n + 1 => numBound k D n * degBound k D n * D n

/--
Definition of `degBound` / `degBound` 的定义

English:
definition degBound
  signature: (k : Nat) (D : Nat -> Nat)

中文:
定义 degBound
  签名: (k : 自然数) (D : 自然数 -> 自然数)
-/
def degBound (k : Nat) (D : Nat -> Nat) : Nat -> Nat
  | 0 => 1
  | n + 1 => numBound k D (n + 1) ^ numBound k D (n + 1) * degBound k D n

end

/--
lemma `degBound_zero` / 引理 `degBound_zero`

English:
lemma degBound_zero
  given: (k : Nat) (D : Nat -> Nat)
  statement: degBound k D 0 = 1
  proof: by rw [degBound]

中文:
引理 degBound_zero
  条件: (k : 自然数) (D : 自然数 -> 自然数)
  结论: degBound k D 0 = 1
  证明: by rw [degBound]
-/
@[simp] lemma degBound_zero (k : Nat) (D : Nat -> Nat) : degBound k D 0 = 1 := by rw [degBound]
/--
lemma `numBound_zero` / 引理 `numBound_zero`

English:
lemma numBound_zero
  given: (k : Nat) (D : Nat -> Nat)
  statement: numBound k D 0 = k
  proof: by rw [numBound]

@[simp]

中文:
引理 numBound_zero
  条件: (k : 自然数) (D : 自然数 -> 自然数)
  结论: numBound k D 0 = k
  证明: by rw [numBound]

@[simp]
-/
@[simp] lemma numBound_zero (k : Nat) (D : Nat -> Nat) : numBound k D 0 = k := by rw [numBound]

@[simp]
/--
lemma `degBound_succ` / 引理 `degBound_succ`

English:
lemma degBound_succ
  given: (k : Nat) (D : Nat -> Nat) (n)
  proof: by
  rw [degBound]

@[simp]

中文:
引理 degBound_succ
  条件: (k : 自然数) (D : 自然数 -> 自然数) (n)
  证明: by
  rw [degBound]

@[simp]

Depends on / 依赖: degBound
-/
lemma degBound_succ (k : Nat) (D : Nat -> Nat) (n) :
    degBound k D (n + 1) = numBound k D (n + 1) ^ numBound k D (n + 1) * degBound k D n := by
  rw [degBound]

@[simp]
/--
lemma `numBound_succ` / 引理 `numBound_succ`

English:
lemma numBound_succ
  given: (k : Nat) (D : Nat -> Nat) (n)
  proof: by
  rw [numBound]

mutual

中文:
引理 numBound_succ
  条件: (k : 自然数) (D : 自然数 -> 自然数) (n)
  证明: by
  rw [numBound]

mutual

Depends on / 依赖: numBound
-/
lemma numBound_succ (k : Nat) (D : Nat -> Nat) (n) :
    numBound k D (n + 1) = numBound k D n * degBound k D n * D n := by
  rw [numBound]

mutual

/--
lemma `degBound_casesOn_succ` / 引理 `degBound_casesOn_succ`

English:
lemma degBound_casesOn_succ
  given: (k₀ k : Nat) (D : Nat -> Nat)

中文:
引理 degBound_casesOn_succ
  条件: (k₀ k : 自然数) (D : 自然数 -> 自然数)
-/
lemma degBound_casesOn_succ (k₀ k : Nat) (D : Nat -> Nat) :
    forall n, degBound k₀ (fun t => Nat.casesOn t k D) (n + 1) =
      (k₀ * k) ^ (k₀ * k) * degBound (k₀ * k) ((k₀ * k) ^ (k₀ * k) • D) n
  | 0 => by simp
  | n + 1 => by
    rw [degBound_succ]; rw [numBound_casesOn_succ]; rw [degBound_casesOn_succ]; rw [numBound_succ]; rw [degBound_succ]; rw [numBound_succ]
    ring

/--
lemma `numBound_casesOn_succ` / 引理 `numBound_casesOn_succ`

English:
lemma numBound_casesOn_succ
  given: (k₀ k : Nat) (D : Nat -> Nat)

中文:
引理 numBound_casesOn_succ
  条件: (k₀ k : 自然数) (D : 自然数 -> 自然数)

Depends on / 依赖: degBound_casesOn_succ, numBound_casesOn_succ, numBound_succ
-/
lemma numBound_casesOn_succ (k₀ k : Nat) (D : Nat -> Nat) :
    forall n, numBound k₀ (Nat.casesOn · k D) (n + 1) = numBound (k₀ * k) ((k₀ * k) ^ (k₀ * k) • D) n
  | 0 => by simp
  | n + 1 => by
    rw [numBound_succ (n := n + 1)]; rw [numBound_casesOn_succ k₀ k D n]; rw [numBound_succ]; rw [degBound_casesOn_succ]
    dsimp
    ring

end

variable {k₁ k₂ : Nat} (hk : k₁ <= k₂) {D₁ D₂ : Nat -> Nat}

mutual

/--
lemma `degBound_le_degBound` / 引理 `degBound_le_degBound`

English:
lemma degBound_le_degBound
  given: (hk : k₁ <= k₂)

中文:
引理 degBound_le_degBound
  条件: (hk : k₁ <= k₂)
-/
lemma degBound_le_degBound (hk : k₁ <= k₂) :
    forall (n) (_ : forall i < n, D₁ i <= D₂ i), degBound k₁ D₁ n <= degBound k₂ D₂ n
  | 0, hD => by simp
  | n + 1, hD => by
    rw [degBound_succ]; rw [degBound_succ]
    refine Nat.mul_le_mul (Nat.pow_self_mono (numBound_mono hk _ hD)) (degBound_le_degBound hk _
      fun i hi => hD _ (hi.trans n.lt_succ_self))

/--
lemma `numBound_mono` / 引理 `numBound_mono`

English:
lemma numBound_mono
  given: (hk : k₁ <= k₂)

中文:
引理 numBound_mono
  条件: (hk : k₁ <= k₂)
-/
lemma numBound_mono (hk : k₁ <= k₂) :
    forall n, (forall i < n, D₁ i <= D₂ i) -> numBound k₁ D₁ n <= numBound k₂ D₂ n
  | 0, hD => by simpa using hk
  | n + 1, hD => by
    rw [numBound_succ]; rw [numBound_succ]
    gcongr
    · exact numBound_mono hk _ fun i hi => hD _ (hi.trans n.lt_succ_self)
    · exact degBound_le_degBound hk _ fun i hi => hD _ (hi.trans n.lt_succ_self)
    · exact hD _ n.lt_succ_self

end

/--
lemma `degBound_pos` / 引理 `degBound_pos`

English:
lemma degBound_pos
  given: (k : Nat) (D : Nat -> Nat)
  statement: forall n, 0 < degBound k D n

中文:
引理 degBound_pos
  条件: (k : 自然数) (D : 自然数 -> 自然数)
  结论: 对任意 n, 0 < degBound k D n
-/
lemma degBound_pos (k : Nat) (D : Nat -> Nat) : forall n, 0 < degBound k D n
  | 0 => by simp
  | n + 1 => by simp [degBound_succ, Nat.pow_self_pos, degBound_pos]

end MvPolynomialC

set_option backward.isDefEq.respectTransparency false in
open MvPolynomialC in
/--
lemma `chevalley_mvPolynomialC` / 引理 `chevalley_mvPolynomialC`

English:
lemma chevalley_mvPolynomialC
  proof: by
  induction n generalizing k M with
  | zero =>
    refine ⟨(S.map (isEmptyRingEquiv _ _).toRingHom), ?_, ?_⟩
    · rw [ConstructibleSetData.toSet_map]
      change _ = (comapEquiv (isEmptyRingEquiv _ _)).symm ⁻¹' _
      rw [← OrderIso.image_eq_preimage_symm]
      rfl
    · simp only [Construct

中文:
引理 chevalley_mvPolynomialC
  证明: by
  induction n generalizing k M with
  | zero =>
    refine ⟨(S.map (isEmptyRingEquiv _ _).toRingHom), ?_, ?_⟩
    · rw [ConstructibleSetData.toSet_map]
      change _ = (comapEquiv (isEmptyRingEquiv _ _)).symm ⁻¹' _
      rw [← OrderIso.image_eq_preimage_symm]
      rfl
    · simp only [Construct

Depends on / 依赖: BasicConstructibleSetData, BasicConstructibleSetData.map, ConstructibleSetData, ConstructibleSetData.map, ConstructibleSetData.toSet_map, Finset, Finset.mem_image, OrderIso, OrderIso.image_eq_preimage_symm, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.coe_coe, S.map, and_imp, coe_coe, comapEquiv, comp_apply, degBound_zero, forall_app
-/
lemma chevalley_mvPolynomialC
    {M : Submodule Int R} (hM : 1 in M) (k : Nat) (d : Multiset (Fin n))
    (S : ConstructibleSetData (MvPolynomial (Fin n) R))
    (hSn : forall C in S, C.n <= k)
    (hS : forall C in S, forall j, C.g j in coeffsIn _ M ⊓ (degreesLE _ _ d).restrictScalars _) :
    exists T : ConstructibleSetData R,
      comap MvPolynomial.C '' S.toSet = T.toSet ∧
      forall C in T, C.n <= numBound k (fun i => 1 + (d.map Fin.val).count i) n ∧
      forall i, C.g i in M ^ (degBound k (fun i => 1 + (d.map Fin.val).count i) n) := by
  induction n generalizing k M with
  | zero =>
    refine ⟨(S.map (isEmptyRingEquiv _ _).toRingHom), ?_, ?_⟩
    · rw [ConstructibleSetData.toSet_map]
      change _ = (comapEquiv (isEmptyRingEquiv _ _)).symm ⁻¹' _
      rw [← OrderIso.image_eq_preimage_symm]
      rfl
    · simp only [ConstructibleSetData.map, RingEquiv.toRingHom_eq_coe, Finset.mem_image, comp_apply,
        BasicConstructibleSetData.map, RingHom.coe_coe, isEmptyRingEquiv_eq_coeff_zero, pow_one,
        numBound_zero, degBound_zero, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun a haS => ⟨hSn a haS, fun i => (hS a haS i).1 0⟩
  | succ n IH => ?_
  let e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] (MvPolynomial (Fin n) R)[X] := finSuccEquiv R n
  let S' := S.map e.toRingHom
  have hS' : S'.degBound <= k * (1 + d.count 0) := by
    apply Finset.sup_le fun x hxS => ?_
    simp only [ConstructibleSetData.map, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, Finset.mem_image, BasicConstructibleSetData.map,
      RingHom.coe_coe, S'] at hxS
    obtain ⟨C, hxS, rfl⟩ := hxS
    trans ∑ i : Fin C.n, (1 + d.count 0)
    · gcongr with j hj
      simp only [e, comp_apply]
      by_cases hgj : C.g j = 0
      · rw [hgj, map_zero]
        simp
      rw [degree_finSuccEquiv hgj]; rw [WithBot.succ_natCast]; rw [add_comm]
      simp only [Nat.cast_id, add_le_add_iff_left, degreeOf_def]
      exact Multiset.count_le_of_le _ (hS _ hxS _).2
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      gcongr
      exact hSn _ hxS
  let B : Multiset (Fin n) :=
    (d.toFinsupp.comapDomain Fin.succ (Fin.succ_injective _).injOn).toMultiset
  obtain ⟨T, hT₁, hT₂⟩ := chevalley_polynomialC
      (R := MvPolynomial (Fin n) R)
      (coeffsIn _ M ⊓ (degreesLE _ _ B).restrictScalars Int)
      (by simpa [MvPolynomial.coeff_one, apply_ite] using hM)
      S' (fun x hxS j k => by
        simp only [ConstructibleSetData.map,
          RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, Finset.mem_image,
          BasicConstructibleSetData.map, RingHom.coe_coe, S', e] at hxS
        obtain ⟨C, hxS, rfl⟩ := hxS
        simp only [comp_apply, Submodule.mem_inf, mem_coeffsIn, Submodule.restrictScalars_mem,
          mem_degreesLE]
        constructor
        · intro d
          simp only [finSuccEquiv_coeff_coeff]
          exact (hS _ hxS _).1 _
        · simp only [B]
          replace hS := (hS _ hxS j).2
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe, mem_degreesLE,
            Multiset.le_iff_count, Finsupp.count_toMultiset, Finsupp.comapDomain_apply,
            Multiset.toFinsupp_apply, ← degreeOf_def] at hS ⊢
          intro a
          exact (degreeOf_coeff_finSuccEquiv (C.g j) a k).trans (hS _))
  let N := (k * (1 + d.count 0)) ^ (k * (1 + d.count 0))
  have (C) (hCT : C in T) (a) : C.g a in coeffsIn (Fin n) (M ^ N) ⊓
        (degreesLE R (Fin n) (N • B)).restrictScalars Int := by
    refine SetLike.le_def.mp ?_ ((hT₂ C hCT).2 a)
    refine pow_inf_le.trans (inf_le_inf ?_ ?_)
    · refine (pow_le_pow_right' ?_ (Nat.pow_self_mono hS')).trans le_coeffsIn_pow
      simpa [MvPolynomial.coeff_one, apply_ite] using hM
    · rw [degreesLE_nsmul, Submodule.restrictScalars_pow Nat.pow_self_pos.ne']
      refine pow_le_pow_right' ?_ (Nat.pow_self_mono hS')
      simp
  have h1M : 1 <= M := Submodule.one_le.mpr hM
  obtain ⟨U, hU₁, hU₂⟩ := IH (M := M ^ N)
    (SetLike.le_def.mp (le_self_pow h1M Nat.pow_self_pos.ne') hM) _ _ T
    (fun C hCT => (hT₂ C hCT).1)
    (fun C hCT k => this C hCT k)
  simp only [Multiset.map_nsmul, Multiset.count_nsmul, ← pow_mul, N] at hU₂
  have : forall i < n + 1, i.casesOn (1 + d.count 0) (1 + (B.map Fin.val).count ·) <=
      1 + (d.map Fin.val).count i := by
    intro t ht
    change _ <= 1 + (d.map Fin.val).count (Fin.mk t ht).val
    rw [Multiset.count_map_eq_count' _ _ Fin.val_injective]
    obtain - | t := t
    · exact le_rfl
    · simp only [add_lt_add_iff_right] at ht
      change 1 + (B.map Fin.val).count (Fin.mk t ht).val <= _
      rw [Multiset.count_map_eq_count' _ _ Fin.val_injective]
      simp [B]
  refine ⟨U, ?_, fun C hCU => ⟨(hU₂ C hCU).1.trans ?_,
fun i => pow_le_pow_right' h1M ?_ (hU₂ C hCU).2 i⟩⟩
  · unfold S' at hT₁
    rw [← hU₁]; rw [← hT₁]; rw [← Set.image_comp]; rw [← comap_comp]; rw [ConstructibleSetData.toSet_map]
    change _ = _ '' ((comapEquiv e.toRingEquiv).symm ⁻¹' _)
    rw [← OrderIso.image_eq_preimage_symm]; rw [Set.image_image]
    simp only [comapEquiv_apply, ← comap_comp_apply]
    congr!
    exact e.symm.toAlgHom.comp_algebraMap.symm
  · refine (numBound_mono hS' _ fun _ _ => ?_).trans
      ((numBound_casesOn_succ k _ _ _).symm.trans_le (numBound_mono le_rfl _ this))
    simp +contextual [mul_add, Nat.one_le_iff_ne_zero]
  · refine (Nat.mul_le_mul le_rfl (degBound_le_degBound hS' _ fun _ _ => ?_)).trans
      ((degBound_casesOn_succ k _ _ _).symm.trans_le (degBound_le_degBound le_rfl _ this))
    simp +contextual [mul_add, Nat.one_le_iff_ne_zero]

/-! ### The general `f : R[Y₁, ..., Yₙ] → R[X₁, ..., Xₘ]` case -/

/--
Definition of `numBound` / `numBound` 的定义

English:
definition numBound
  signature: (k m n : Nat) (d : Multiset (Fin m))
  body: MvPolynomialC.numBound (k + n) (1 + (d.map Fin.val).count ·) m

中文:
定义 numBound
  签名: (k m n : 自然数) (d : Multiset (Fin m))
  定义体: MvPolynomialC.numBound (k + n) (1 + (d.map Fin.val).count ·) m

Depends on / 依赖: Fin.val, MvPolynomialC, MvPolynomialC.numBound, d.map, numBound
-/
def numBound (k m n : Nat) (d : Multiset (Fin m)) : Nat :=
  MvPolynomialC.numBound (k + n) (1 + (d.map Fin.val).count ·) m

/--
Definition of `degBound` / `degBound` 的定义

English:
definition degBound
  signature: (k m n : Nat) (d : Multiset (Fin m))
  body: MvPolynomialC.degBound (k + n) (1 + (d.map Fin.val).count ·) m

中文:
定义 degBound
  签名: (k m n : 自然数) (d : Multiset (Fin m))
  定义体: MvPolynomialC.degBound (k + n) (1 + (d.map Fin.val).count ·) m

Depends on / 依赖: Fin.val, MvPolynomialC, MvPolynomialC.degBound, d.map, degBound
-/
def degBound (k m n : Nat) (d : Multiset (Fin m)) : Nat :=
  MvPolynomialC.degBound (k + n) (1 + (d.map Fin.val).count ·) m

end ChevalleyThm

open ChevalleyThm

/--
lemma `chevalley_mvPolynomial_mvPolynomial` / 引理 `chevalley_mvPolynomial_mvPolynomial`

English:
lemma chevalley_mvPolynomial_mvPolynomial
  proof: by
  let g : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) ->+* MvPolynomial (Fin m) R :=
    eval₂Hom f.toRingHom X
  have hg : g.comp (algebraMap (MvPolynomial (Fin n) R) _) = f := by ext x : 2 <;> simp [g]
  let σ : MvPolynomial (Fin m) R ->+* MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    

中文:
引理 chevalley_mvPolynomial_mvPolynomial
  证明: by
  let g : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) ->+* MvPolynomial (Fin m) R :=
    eval₂Hom f.toRingHom X
  have hg : g.comp (algebraMap (MvPolynomial (Fin n) R) _) = f := by ext x : 2 <;> simp [g]
  let σ : MvPolynomial (Fin m) R ->+* MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    

Depends on / 依赖: ConstructibleSetDat, DFunLike, DFunLike.congr_fun, LeftInverse, LeftInverse.surjective, MvPolynomial, Surjective, algebraMap, congr_fun, f.toRingHom, g.comp, surjective, toRingHom
-/
lemma chevalley_mvPolynomial_mvPolynomial
    {m n : Nat} (f : MvPolynomial (Fin n) R ->ₐ[R] MvPolynomial (Fin m) R)
    (k : Nat) (d : Multiset (Fin m))
    (S : ConstructibleSetData (MvPolynomial (Fin m) R))
    (hSn : forall C in S, C.n <= k)
    (hS : forall C in S, forall j, (C.g j).degrees <= d)
    (hf : forall i, (f (.X i)).degrees <= d) :
    exists T : ConstructibleSetData (MvPolynomial (Fin n) R),
      comap f '' S.toSet = T.toSet ∧
      forall C in T, C.n <= numBound k m n d ∧ forall i j, (C.g i).degreeOf j <= degBound k m n d := by
  let g : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) ->+* MvPolynomial (Fin m) R :=
    eval₂Hom f.toRingHom X
  have hg : g.comp (algebraMap (MvPolynomial (Fin n) R) _) = f := by ext x : 2 <;> simp [g]
  let σ : MvPolynomial (Fin m) R ->+* MvPolynomial (Fin m) (MvPolynomial (Fin n) R) :=
    map (algebraMap _ _)
  have hσ : g.comp σ = .id _ := by ext : 2 <;> simp [g, σ]
  have hσ' (x) : g (σ x) = x := DFunLike.congr_fun hσ x
  have hg' : Surjective g := LeftInverse.surjective hσ'
  let S' : ConstructibleSetData (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) := S.image
    fun ⟨fk, k, gk⟩ => ⟨σ fk, k + n, fun s => (finSumFinEquiv.symm s).elim (σ ∘ gk)
      fun i => .C (.X i) - σ (f (.X i))⟩
  let s₀ : Set (MvPolynomial (Fin m) (MvPolynomial (Fin n) R)) :=
    .range fun i => .C (.X i) - σ (f (.X i))
  have hs : zeroLocus s₀ = Set.range (comap g) := by
    rw [range_comap_of_surjective _ _ hg']; rw [← zeroLocus_span]
    congr! 2
    have H : Ideal.span s₀ <= RingHom.ker g := by
      simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
        hσ', s₀]
      simp [g]
    refine H.antisymm fun p hp => ?_
    obtain ⟨q₁, q₂, hq₁, rfl⟩ : exists q₁ q₂, q₁ in Ideal.span s₀ ∧ p = q₁ + σ q₂ := by
      clear hp
      obtain ⟨p, rfl⟩ := (commAlgEquiv _ _ _).surjective p
      simp_rw [← (commAlgEquiv R (Fin n) (Fin m)).symm.injective.eq_iff,
        AlgEquiv.symm_apply_apply]
      induction p using MvPolynomial.induction_on with
      | C q =>
exact ⟨0, q, by simp, (commAlgEquiv _ _ _).injective
          by simp [commAlgEquiv_C, σ]⟩
      | add p q hp hq =>
        obtain ⟨q₁, q₂, hq₁, rfl⟩ := hp
        obtain ⟨q₃, q₄, hq₃, rfl⟩ := hq
        refine ⟨q₁ + q₃, q₂ + q₄, add_mem hq₁ hq₃, by simp only [map_add, add_add_add_comm]⟩
      | mul_X p i hp =>
        obtain ⟨q₁, q₂, hq₁, rfl⟩ := hp
        simp only [← (commAlgEquiv R (Fin n) (Fin m)).injective.eq_iff,
          map_mul, AlgEquiv.apply_symm_apply, commAlgEquiv_X]
        refine ⟨q₁ * .C (.X i) + σ q₂ * (.C (.X i) - σ (f (.X i))), q₂ * f (.X i), ?_, ?_⟩
        · exact add_mem (Ideal.mul_mem_right _ _ hq₁)
            (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self _)))
        · simp; ring
    obtain rfl : q₂ = 0 := by simpa [hσ', show g q₁ = 0 from H hq₁] using hp
    simpa using hq₁
  have hg'' (t) : comap g '' t = comap σ ⁻¹' t inter zeroLocus s₀ := by
    refine Set.injOn_preimage (f := comap g) .rfl ?_ ?_ ?_
    · simp
    · simp [hs]
    · rw [Set.preimage_image_eq _ (comap_injective_of_surjective g hg'),
        Set.preimage_inter, hs, Set.preimage_range, Set.inter_univ,
        ← Set.preimage_comp, ← comap_comp, hσ]
      simp only [comap_id, Set.preimage_id']
  have hS' : comap g '' S.toSet = S'.toSet := by
    simp only [S', BasicConstructibleSetData.toSet, ConstructibleSetData.toSet, Set.image_iUnion₂,
      Finset.set_biUnion_finset_image, ← comp_def (g := finSumFinEquiv.symm), Set.range_comp,
      Equiv.range_eq_univ, Set.image_univ, Set.Sum.elim_range,
      Set.image_sdiff (hf := comap_injective_of_surjective g hg'), zeroLocus_union]
    simp [hg'', ← Set.inter_sdiff_distrib_right, Set.sdiff_inter_right_comm, s₀]
  obtain ⟨T, hT, hT'⟩ :=
    chevalley_mvPolynomialC
    (M := (degreesLE R (Fin n) Finset.univ.1).restrictScalars Int) (by simp) (k + n) d S'
    (Finset.forall_mem_image.mpr fun x hx => (by simpa using hSn _ hx))
    (Finset.forall_mem_image.mpr fun x hx => by
      intro j
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      simp only [Equiv.symm_apply_apply, Submodule.mem_inf, mem_coeffsIn,
        Submodule.restrictScalars_mem, mem_degreesLE]
      constructor
      · intro i
        obtain j | j := j
        · simp [σ, MvPolynomial.coeff_map, degrees_C]
        · simp only [MvPolynomial.algebraMap_eq, Sum.elim_inr, MvPolynomial.coeff_sub,
            MvPolynomial.coeff_C, MvPolynomial.coeff_map, σ]
          refine degrees_sub_le.trans ?_
          simp only [degrees_C, apply_ite, degrees_zero,
            Multiset.union_zero]
          split_ifs with h
          · refine (degrees_X' _).trans ?_
            simp
          · simp
      · obtain j | j := j
        · simp only [MvPolynomial.algebraMap_eq, Sum.elim_inl, comp_apply, σ]
          exact degrees_map_le.trans (hS _ hx j)
        · refine degrees_sub_le.trans ?_
          simp only [degrees_C, Multiset.zero_union]
          exact degrees_map_le.trans (hf _))
  refine ⟨T, ?_, fun C hCT => ⟨(hT' C hCT).1, fun i j => ?_⟩⟩
  · rwa [← hg, comap_comp, Set.image_comp, hS']
  · have := (hT' C hCT).2 i
    rw [← Submodule.restrictScalars_pow (MvPolynomialC.degBound_pos ..).ne']; rw [← degreesLE_nsmul]; rw [Submodule.restrictScalars_mem]; rw [mem_degreesLE]; rw [Multiset.le_iff_count] at this
    simpa only [Multiset.count_nsmul, Multiset.count_univ, mul_one, ← degreeOf_def]
      using! this j
