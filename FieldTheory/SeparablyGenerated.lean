/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten, Junyan Xu
-/
module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Order.Ring.Finset
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!

# Separably generated extensions

We aim to formalize the following result:

Let `K/k` be a finitely generated field extension with characteristic `p > 0`, then TFAE
1. `K/k` is separably generated
2. If `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
  `{ sᵢᵖ } ⊆ K` is also `k`-linearly independent
3. `K ⊗ₖ k^{1/p}` is reduced
4. `K` is geometrically reduced over `k`.
5. `k` and `Kᵖ` are linearly disjoint over `kᵖ` in `K`.

## Main result
- `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`: (2) ⇒ (1)

-/

@[expose] public noncomputable section

section

attribute [local instance 2000] Polynomial.isScalarTower Algebra.toSMul IsScalarTower.right

open MvPolynomial
open scoped IntermediateField

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K] (p : Nat) (hp : p.Prime)
variable (H : forall s : Finset K,
  LinearIndepOn k _root_.id (s : Set K) -> LinearIndepOn k (· ^ p) (s : Set K))
variable {a : ι -> K} (n : ι)

namespace MvPolynomial

/--
Definition of `toPolynomialAdjoinImageCompl` / `toPolynomialAdjoinImageCompl` 的定义

English:
definition toPolynomialAdjoinImageCompl
  signature: (F : MvPolynomial ι k) (a : ι -> K) (i : ι)
  body: letI := Classical.typeDecidableEq ι
  (optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)).mapAlgHom
    (aeval fun j : {j // j != i} =>
      (⟨a j, Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩ : Algebra.adjoin k (a '' {i}ᶜ)))

中文:
定义 toPolynomialAdjoinImageCompl
  签名: (F : MvPolynomial ι k) (a : ι -> K) (i : ι)
  定义体: letI := Classical.typeDecidableEq ι
  (optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)).mapAlgHom
    (aeval fun j : {j // j != i} =>
      (⟨a j, Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩ : Algebra.adjoin k (a '' {i}ᶜ)))

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, Classical, Classical.typeDecidableEq, Equiv.optionSubtypeNe, adjoin, mapAlgHom, optionEquivLeft, optionSubtypeNe, renameEquiv, subset_adjoin, typeDecidableEq
-/
def toPolynomialAdjoinImageCompl (F : MvPolynomial ι k) (a : ι -> K) (i : ι) :
    Polynomial (Algebra.adjoin k (a '' {i}ᶜ)) :=
  letI := Classical.typeDecidableEq ι
  (optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)).mapAlgHom
    (aeval fun j : {j // j != i} =>
      (⟨a j, Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩ : Algebra.adjoin k (a '' {i}ᶜ)))

/--
theorem `aeval_toPolynomialAdjoinImageCompl_eq_zero` / 定理 `aeval_toPolynomialAdjoinImageCompl_eq_zero`

English:
theorem aeval_toPolynomialAdjoinImageCompl_eq_zero
  proof: by
  rw [← hFa]; rw [← AlgHom.restrictScalars_apply k]
  simp_rw [toPolynomialAdjoinImageCompl, ← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr; ext; aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)

中文:
定理 aeval_toPolynomialAdjoinImageCompl_eq_zero
  证明: by
  rw [← hFa]; rw [← AlgHom.restrictScalars_apply k]
  simp_rw [toPolynomialAdjoinImageCompl, ← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr; ext; aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.comp_apply, AlgHom.restrictScalars_apply, coe_toAlgHom, comp_apply, optionEquivLeft_X_none, optionEquivLeft_X_some, restrictScalars_apply, simp_rw, toPolynomialAdjoinImageCompl
-/
theorem aeval_toPolynomialAdjoinImageCompl_eq_zero
    {a : ι -> K} {F : MvPolynomial ι k} (hFa : F.aeval a = 0) (i : ι) :
    (toPolynomialAdjoinImageCompl F a i).aeval (a i) = 0 := by
  rw [← hFa]; rw [← AlgHom.restrictScalars_apply k]
  simp_rw [toPolynomialAdjoinImageCompl, ← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr; ext; aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)

/--
theorem `irreducible_toPolynomialAdjoinImageCompl` / 定理 `irreducible_toPolynomialAdjoinImageCompl`

English:
theorem irreducible_toPolynomialAdjoinImageCompl
  statement: {F : MvPolynomial ι k} (hF : Irreducible F) (i : ι)
  proof: by
  classical
  unfold toPolynomialAdjoinImageCompl
  have hc : a '' {i}ᶜ = Set.range (fun x : {j | j != i} => a x) := by ext; simp
  let d : {j // j != i} ≃ {j | j != i} := .subtypeEquivRight (by simp)
refine (congrArg Irreducible ?_).mp
.map hF.map (renameEquiv k ((Equiv.optionSubtypeNe i).symm))

中文:
定理 irreducible_toPolynomialAdjoinImageCompl
  结论: {F : MvPolynomial ι k} (hF : Irreducible F) (i : ι)
  证明: by
  classical
  unfold toPolynomialAdjoinImageCompl
  have hc : a '' {i}ᶜ = Set.range (fun x : {j | j != i} => a x) := by ext; simp
  let d : {j // j != i} ≃ {j | j != i} := .subtypeEquivRight (by simp)
refine (congrArg Irreducible ?_).mp
.map hF.map (renameEquiv k ((Equiv.optionSubtypeNe i).symm))

Depends on / 依赖: Algebra, Algebra.adjoin, Equiv.optionSubtypeNe, H.aevalEquiv.trans, Irreducible, Polynomial, Polynomial.c, Polynomial.coe_mapAlgEquiv, Polynomial.mapAlgEquiv, Set.range, Subalgebra, Subalgebra.equivOfEq, adjoin, aevalEquiv, classical, coe_mapAlgEquiv, equivOfEq, hF.map, hc.symm, mapAlgEquiv
-/
theorem irreducible_toPolynomialAdjoinImageCompl {F : MvPolynomial ι k} (hF : Irreducible F) (i : ι)
    (H : AlgebraicIndependent k fun x : {j | j != i} => a x) :
    Irreducible (toPolynomialAdjoinImageCompl F a i) := by
  classical
  unfold toPolynomialAdjoinImageCompl
  have hc : a '' {i}ᶜ = Set.range (fun x : {j | j != i} => a x) := by ext; simp
  let d : {j // j != i} ≃ {j | j != i} := .subtypeEquivRight (by simp)
refine (congrArg Irreducible ?_).mp
.map hF.map (renameEquiv k ((Equiv.optionSubtypeNe i).symm))
.map (Polynomial.mapAlgEquiv <| (optionEquivLeft k _)
(renameEquiv k d).trans H.aevalEquiv.trans
        (Subalgebra.equivOfEq _ _ congr(Algebra.adjoin k $hc.symm)))
  rw [Polynomial.coe_mapAlgEquiv]; rw [Polynomial.coe_mapAlgHom]
  refine congrFun (congrArg Polynomial.map ?_) _
  ext <;> simp [d]

-- Suppose `F` has minimal total degree among the relations of `a`.
variable {F : MvPolynomial ι k}
variable (HF : forall F' : MvPolynomial ι k, F' != 0 -> F'.aeval a = 0 -> F.totalDegree <= F'.totalDegree)

include HF

/--
lemma `irreducible_of_forall_totalDegree_le` / 引理 `irreducible_of_forall_totalDegree_le`

English:
lemma irreducible_of_forall_totalDegree_le
  given: (hF0 : F != 0) (hFa : F.aeval a = 0)
  statement: Irreducible F
  proof: by
  refine ⟨fun h' => (h'.map (aeval a)).ne_zero hFa, fun q₁ q₂ e => ?_⟩
  wlog h₁ : aeval a q₁ = 0 generalizing q₁ q₂
  · exact .symm (this q₂ q₁ (e.trans (mul_comm ..)) <| by
simpa [h₁, hFa] using Eq.symm congr(aeval a $e))
  have ne := mul_ne_zero_iff.mp (e ▸ hF0)
  have := HF q₁ ne.1 h₁
  rw [e

中文:
引理 irreducible_of_forall_totalDegree_le
  条件: (hF0 : F != 0) (hFa : F.aeval a = 0)
  结论: Irreducible F
  证明: by
  refine ⟨fun h' => (h'.map (aeval a)).ne_zero hFa, fun q₁ q₂ e => ?_⟩
  wlog h₁ : aeval a q₁ = 0 generalizing q₁ q₂
  · exact .symm (this q₂ q₁ (e.trans (mul_comm ..)) <| by
simpa [h₁, hFa] using Eq.symm congr(aeval a $e))
  have ne := mul_ne_zero_iff.mp (e ▸ hF0)
  have := HF q₁ ne.1 h₁
  rw [e

Depends on / 依赖: Eq.symm, add_le_iff_nonpos_right, e.trans, generalizing, isUnit_iff_totalDegree_of_isReduced, isUnit_iff_totalDegree_of_isReduced.mpr, mul_comm, mul_ne_zero_iff, mul_ne_zero_iff.mp, ne_zero, nonpos_iff_eq_zero, totalDegree_eq_zero_iff_eq_C, totalDegree_eq_zero_iff_eq_C.mp, totalDegree_mul_of_isDomain
-/
lemma irreducible_of_forall_totalDegree_le (hF0 : F != 0) (hFa : F.aeval a = 0) : Irreducible F := by
  refine ⟨fun h' => (h'.map (aeval a)).ne_zero hFa, fun q₁ q₂ e => ?_⟩
  wlog h₁ : aeval a q₁ = 0 generalizing q₁ q₂
  · exact .symm (this q₂ q₁ (e.trans (mul_comm ..)) <| by
simpa [h₁, hFa] using Eq.symm congr(aeval a $e))
  have ne := mul_ne_zero_iff.mp (e ▸ hF0)
  have := HF q₁ ne.1 h₁
  rw [e]; rw [totalDegree_mul_of_isDomain ne.1 ne.2]; rw [add_le_iff_nonpos_right]; rw [nonpos_iff_eq_zero] at this
  refine .inr (isUnit_iff_totalDegree_of_isReduced.mpr ⟨?_, this⟩)
  rw [totalDegree_eq_zero_iff_eq_C.mp this] at ne
  simpa using ne.2

/--
theorem `coeff_toPolynomialAdjoinImageCompl_ne_zero` / 定理 `coeff_toPolynomialAdjoinImageCompl_ne_zero`

English:
theorem coeff_toPolynomialAdjoinImageCompl_ne_zero
  proof: by
  classical
  intro H
  let F₀ := optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
  have H := HF (rename (↑) (F₀.coeff (σ i))) ?_ ?_
  · have : (F₀.coeff (σ i)).totalDegree + σ i <= _ :=
totalDegree_coeff_optionEquivLeft_add_le _ _ _ (σ i) by
        rw [totalDegree_renameEqu

中文:
定理 coeff_toPolynomialAdjoinImageCompl_ne_zero
  证明: by
  classical
  intro H
  let F₀ := optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
  have H := HF (rename (↑) (F₀.coeff (σ i))) ?_ ?_
  · have : (F₀.coeff (σ i)).totalDegree + σ i <= _ :=
totalDegree_coeff_optionEquivLeft_add_le _ _ _ (σ i) by
        rw [totalDegree_renameEqu

Depends on / 依赖: Equiv.optionSubtypeNe, Finsupp, Finsupp.le_degree, Subtype, classical, le_degree, le_totalDegree, map_eq_zero_iff, optionEquivLeft, optionSubtypeNe, renameEquiv, rename_injective, this.trans, totalDegree, totalDegree_coeff_optionEquivLeft_add_le, totalDegree_renameEquiv, totalDegree_rename_le
-/
theorem coeff_toPolynomialAdjoinImageCompl_ne_zero
    (σ : ι ->₀ Nat) (hσ : σ in F.support) (i : ι) (hσi : σ i != 0) :
    (toPolynomialAdjoinImageCompl F a i).coeff (σ i) != 0 := by
  classical
  intro H
  let F₀ := optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)
  have H := HF (rename (↑) (F₀.coeff (σ i))) ?_ ?_
  · have : (F₀.coeff (σ i)).totalDegree + σ i <= _ :=
totalDegree_coeff_optionEquivLeft_add_le _ _ _ (σ i) by
        rw [totalDegree_renameEquiv]
        exact (Finsupp.le_degree ..).trans (le_totalDegree hσ)
    rw [totalDegree_renameEquiv] at this
    simpa [hσi] using (this.trans H).trans (totalDegree_rename_le _ _)
  · refine (map_eq_zero_iff _ (rename_injective _ Subtype.val_injective)).not.mpr fun H => ?_
    let e := (Equiv.optionSubtypeNe i).symm
    have : coeff _ (F₀.coeff _) = _ :=
      optionEquivLeft_coeff_some_coeff_none _ _ (σ.equivMapDomain e) (renameEquiv k e F)
    dsimp only [F₀] at this
    rw [renameEquiv_apply]; rw [Finsupp.equivMapDomain_eq_mapDomain]; rw [coeff_rename_mapDomain _
      e.injective]; rw [Finsupp.mapDomain_equiv_apply]; rw [Equiv.symm_symm]; rw [Equiv.optionSubtypeNe_none]; rw [← renameEquiv_apply]; rw [H]; rw [coeff_zero]; rw [eq_comm]; rw [← notMem_support_iff] at this
    exact this hσ
  · apply_fun Subalgebra.val _ at H
    simp_rw [toPolynomialAdjoinImageCompl, Polynomial.coe_mapAlgHom, Polynomial.coeff_map,
      AlgHom.coe_toRingHom, map_zero] at H
    simp_rw [← H, ← AlgHom.comp_apply]
    congr; ext; simp

/--
theorem `isAlgebraic_of_mem_vars_of_forall_totalDegree_le` / 定理 `isAlgebraic_of_mem_vars_of_forall_totalDegree_le`

English:
theorem isAlgebraic_of_mem_vars_of_forall_totalDegree_le
  statement: (hFa : F.aeval a = 0) (i : ι)
  proof: by
  have ⟨σ, hσ, hσi⟩ := (mem_vars_iff_mem_support i).mp hi
  refine ⟨toPolynomialAdjoinImageCompl F a i,
    fun h => coeff_toPolynomialAdjoinImageCompl_ne_zero HF σ hσ i
      (Finsupp.mem_support_iff.mp hσi) ?_, aeval_toPolynomialAdjoinImageCompl_eq_zero hFa ..⟩
  rw [h]; rw [Polynomial.coeff_ze

中文:
定理 isAlgebraic_of_mem_vars_of_forall_totalDegree_le
  结论: (hFa : F.aeval a = 0) (i : ι)
  证明: by
  have ⟨σ, hσ, hσi⟩ := (mem_vars_iff_mem_support i).mp hi
  refine ⟨toPolynomialAdjoinImageCompl F a i,
    fun h => coeff_toPolynomialAdjoinImageCompl_ne_zero HF σ hσ i
      (Finsupp.mem_support_iff.mp hσi) ?_, aeval_toPolynomialAdjoinImageCompl_eq_zero hFa ..⟩
  rw [h]; rw [Polynomial.coeff_ze

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff.mp, Polynomial, Polynomial.coeff_zero, aeval_toPolynomialAdjoinImageCompl_eq_zero, coeff_toPolynomialAdjoinImageCompl_ne_zero, coeff_zero, mem_support_iff, mem_vars_iff_mem_support, toPolynomialAdjoinImageCompl
-/
theorem isAlgebraic_of_mem_vars_of_forall_totalDegree_le (hFa : F.aeval a = 0) (i : ι)
    (hi : i in F.vars) : IsAlgebraic (Algebra.adjoin k (a '' {i}ᶜ)) (a i) := by
  have ⟨σ, hσ, hσi⟩ := (mem_vars_iff_mem_support i).mp hi
  refine ⟨toPolynomialAdjoinImageCompl F a i,
    fun h => coeff_toPolynomialAdjoinImageCompl_ne_zero HF σ hσ i
      (Finsupp.mem_support_iff.mp hσi) ?_, aeval_toPolynomialAdjoinImageCompl_eq_zero hFa ..⟩
  rw [h]; rw [Polynomial.coeff_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hp H in
/--
theorem `exists_mem_support_not_dvd_of_forall_totalDegree_le` / 定理 `exists_mem_support_not_dvd_of_forall_totalDegree_le`

English:
theorem exists_mem_support_not_dvd_of_forall_totalDegree_le
  given: (hF0 : F != 0) (hFa : F.aeval a = 0)
  proof: by
  by_contra!
  have (σ) (hσ : σ in F.support) : exists σ', σ = p • σ' := by
    choose σ' hσ' using (this · σ hσ)
    exact ⟨⟨σ.support, σ', by simp [hσ', hp.ne_zero]⟩, Finsupp.ext hσ'⟩
  choose! σ' hσ' using this
  have hσ'' (σ : F.support) : σ.1 = p • σ' σ := hσ' σ.1 σ.2
  classical
  replace H

中文:
定理 exists_mem_support_not_dvd_of_forall_totalDegree_le
  条件: (hF0 : F != 0) (hFa : F.aeval a = 0)
  证明: by
  by_contra!
  have (σ) (hσ : σ in F.support) : exists σ', σ = p • σ' := by
    choose σ' hσ' using (this · σ hσ)
    exact ⟨⟨σ.support, σ', by simp [hσ', hp.ne_zero]⟩, Finsupp.ext hσ'⟩
  choose! σ' hσ' using this
  have hσ'' (σ : F.support) : σ.1 = p • σ' σ := hσ' σ.1 σ.2
  classical
  replace H

Depends on / 依赖: F.support, Finset, Finset.coe_image, Finset.coe_univ, Finsupp, Finsupp.ext, Fintype, LinearIndependent, Set.image_univ, classical, coe_image, coe_univ, hp.ne_zero, hv.injective, image_univ, injective, linearIndepOn_range_iff, ne_zero, replace, support
-/
theorem exists_mem_support_not_dvd_of_forall_totalDegree_le (hF0 : F != 0) (hFa : F.aeval a = 0) :
    exists i, exists σ in F.support, ¬ p ∣ σ i := by
  by_contra!
  have (σ) (hσ : σ in F.support) : exists σ', σ = p • σ' := by
    choose σ' hσ' using (this · σ hσ)
    exact ⟨⟨σ.support, σ', by simp [hσ', hp.ne_zero]⟩, Finsupp.ext hσ'⟩
  choose! σ' hσ' using this
  have hσ'' (σ : F.support) : σ.1 = p • σ' σ := hσ' σ.1 σ.2
  classical
  replace H (ι : Type u_3) (_ : Fintype ι) (v : ι -> K) (hv : LinearIndependent k v) :
      LinearIndependent k (v · ^ p) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, linearIndepOn_range_iff
      hv.injective] using! H (Finset.univ.image v) (by simpa using! hv.linearIndepOn_id)
  have := mt (H F.support inferInstance (fun s => aeval a (monomial (σ' s) (1 : k)))) (by
    simp_rw [← map_pow, monomial_pow, ← hσ'', one_pow, not_linearIndependent_iff]
    refine ⟨.univ, (F.coeff ·), ?_, by simpa [MvPolynomial.eq_zero_iff] using! hF0⟩
    simp only [← map_smul, ← map_sum, Finset.univ_eq_attach, smul_eq_mul, mul_one]
    rw [F.support.sum_attach (fun i => monomial i (F.coeff i))]; rw [support_sum_monomial_coeff]; rw [hFa])
  simp only [LinearIndependent, injective_iff_map_eq_zero, not_forall] at this
  obtain ⟨F', hF', hF'0⟩ := this
let F'' : MvPolynomial ι k := .ofCoeff F'.mapDomain fun s => σ' s.1
  have hF''0 : F'' != 0 := ne_of_ne_of_eq (AddMonoidAlgebra.ofCoeff_eq_zero.ne.2 <|
    (Finsupp.mapDomain_injective fun s t h => Subtype.ext
    (Finsupp.ext fun i => by rw [hσ' _ s.2, hσ' _ t.2, h])).ne hF'0) (by simp)
  have hF'' : aeval a F'' = 0 := by
    have : (aeval a).toLinearMap ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap ∘ₗ
      Finsupp.lmapDomain k k (fun s : F.support => σ' s) =
        (Finsupp.linearCombination k fun s : F.support => aeval a (monomial (σ' s) (1 : k))) := by
      ext v; simp [monomial]
    simp only [← hF', F'', ← this]; rfl
  suffices hpm : p * F''.totalDegree <= F.totalDegree by
    have hF''0' : F''.totalDegree != 0 := by
      contrapose hF''0
      rw [totalDegree_eq_zero_iff_eq_C.mp hF''0]; rw [aeval_C]; rw [map_eq_zero] at hF''
      rw [totalDegree_eq_zero_iff_eq_C.mp hF''0]; rw [hF'']; rw [map_zero]
    replace this := hpm.trans ((HF F'' hF''0 hF'').trans_eq (one_mul _).symm)
    exact hp.one_lt.not_ge ((mul_le_mul_iff_of_pos_right hF''0'.bot_lt).mp this)
  rw [totalDegree]; rw [Finset.mul_sup₀]; rw [Finset.sup_le_iff]
  intro σ hσ
  obtain ⟨σ, hσ₂, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
  refine le_trans ?_ (Finset.le_sup σ.2)
  conv_rhs => rw [hσ' _ σ.2, Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]

end MvPolynomial

open IntermediateField

section

variable [ExpChar k p]

include hp H

/--
lemma `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow` / 引理 `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`

English:
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
  proof: by
  set S := {F : MvPolynomial ι k | F != 0 ∧ F.aeval a = 0}
  obtain ⟨F, ⟨hF₀, hFa⟩, hFmin⟩ :
      exists F in S, forall G : MvPolynomial ι k, G != 0 -> G.aeval a = 0 -> totalDegree F <= totalDegree G := by
    suffices S.Nonempty from
      ⟨totalDegree.argminOn S this, totalDegree.argminOn_mem 

中文:
引理 exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
  证明: by
  set S := {F : MvPolynomial ι k | F != 0 ∧ F.aeval a = 0}
  obtain ⟨F, ⟨hF₀, hFa⟩, hFmin⟩ :
      exists F in S, forall G : MvPolynomial ι k, G != 0 -> G.aeval a = 0 -> totalDegree F <= totalDegree G := by
    suffices S.Nonempty from
      ⟨totalDegree.argminOn S this, totalDegree.argminOn_mem 

Depends on / 依赖: AlgebraicIndependent, F.aeval, G.aeval, MvPolynomial, Nonempty, S.Nonempty, algebraicIndependent_iff, and_comm, argminOn, argminOn_le, argminOn_mem, h.transcendental_adjoin, totalDegree, totalDegree.argminOn, totalDegree.argminOn_le, totalDegree.argminOn_mem, transcendental_adjoin
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    (ha' : IsTranscendenceBasis k fun i : {i // i != n} => a i) :
    exists i : ι, IsTranscendenceBasis k (fun j : {j // j != i} => a j) ∧
      IsSeparable (adjoin k (a '' {i}ᶜ)) (a i) := by
  set S := {F : MvPolynomial ι k | F != 0 ∧ F.aeval a = 0}
  obtain ⟨F, ⟨hF₀, hFa⟩, hFmin⟩ :
      exists F in S, forall G : MvPolynomial ι k, G != 0 -> G.aeval a = 0 -> totalDegree F <= totalDegree G := by
    suffices S.Nonempty from
      ⟨totalDegree.argminOn S this, totalDegree.argminOn_mem ..,
        fun _ h₁ h₂ => totalDegree.argminOn_le S ⟨h₁, h₂⟩⟩
    suffices ¬ AlgebraicIndependent k a by simpa [S, algebraicIndependent_iff, and_comm] using! this
    intro h
    refine h.transcendental_adjoin (i := n) (s := {n}ᶜ) (by simp) ?_
    have : a '' {n}ᶜ = Set.range (ι := {i // i != n}) (a ·) := by aesop
    convert! ha'.isAlgebraic.isAlgebraic _
  have hFirr : Irreducible F := irreducible_of_forall_totalDegree_le hFmin hF₀ hFa
  obtain ⟨i, σ, hσ, hi⟩ := exists_mem_support_not_dvd_of_forall_totalDegree_le p hp H hFmin hF₀ hFa
  have hσi : σ i != 0 := by aesop
have alg := isAlgebraic_of_mem_vars_of_forall_totalDegree_le hFmin hFa i
    (mem_vars_iff_mem_support i).mpr ⟨σ, hσ, by simpa⟩
  have Hi := ha'.of_isAlgebraic_adjoin_image_compl _ i _ alg
  refine ⟨i, Hi, ?_⟩
  let k' := adjoin k (a '' {i}ᶜ)
  have hF₁irr := irreducible_toPolynomialAdjoinImageCompl hFirr i Hi.1
  have := (AlgebraicIndepOn.aevalEquiv (s := {i}ᶜ) Hi.1).uniqueFactorizationMonoid inferInstance
  have coeff_ne := coeff_toPolynomialAdjoinImageCompl_ne_zero hFmin σ hσ i hσi
  open scoped algebraAdjoinAdjoin in
  have hF₂irr := (hF₁irr.isPrimitive fun h => coeff_ne <| Polynomial.coeff_eq_zero_of_natDegree_lt <|
h.trans_lt Nat.pos_iff_ne_zero.2 hσi).irreducible_iff_irreducible_map_fraction_map
    (K := k').1 hF₁irr
  contrapose coeff_ne with Hsep
  have : CharP k' p := (expChar_of_injective_algebraMap (algebraMap k k').injective p).casesOn
    (fun e => (e rfl).elim) (fun _ _ _ => ‹_›) hp.ne_one
  obtain ⟨g, hg, eq⟩ := (((minpoly k' (a i)).separable_or p (minpoly.irreducible
    (isAlgebraic_iff_isIntegral.mp <| isAlgebraic_adjoin_iff.mpr alg))).resolve_left Hsep).2
  replace eq := congr(Polynomial.coeff $eq (σ i))
  rwa [← minpoly.eq_of_irreducible hF₂irr ((Polynomial.aeval_map_algebraMap ..).trans
    (aeval_toPolynomialAdjoinImageCompl_eq_zero hFa i)), Polynomial.coeff_mul_C,
    Polynomial.coeff_expand hp.pos, if_neg hi, eq_mul_inv_iff_mul_eq₀
    (by simpa using hF₂irr.ne_zero), zero_mul, eq_comm,
    Polynomial.coeff_map, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ..)] at eq

/--
lemma `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'` / 引理 `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'`

English:
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
  proof: by
  let e₁ : {j : ↥(insert n s) // j != ⟨n, by simp⟩} ≃ ↑s :=
    ⟨fun x => ⟨x, by aesop⟩, fun x => ⟨⟨x, by aesop⟩, by aesop⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨i, hi, hi'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H
    (a := fun i : ↥(insert n s) => a i) ⟨n, by 

中文:
引理 exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
  证明: by
  let e₁ : {j : ↥(insert n s) // j != ⟨n, by simp⟩} ≃ ↑s :=
    ⟨fun x => ⟨x, by aesop⟩, fun x => ⟨⟨x, by aesop⟩, by aesop⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨i, hi, hi'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H
    (a := fun i : ↥(insert n s) => a i) ⟨n, by 

Depends on / 依赖: Subtype, Subtype.ext, comp_equiv, exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow, ha.comp_equiv, insert
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
    (s : Set ι) (n : ι) (ha : IsTranscendenceBasis k fun i : s => a i) (hn : n ∉ s) :
    exists i : ι, IsTranscendenceBasis k (fun j : ↥(insert n s \ {i}) => a j) ∧
      IsSeparable (adjoin k (a '' (insert n s \ {i}))) (a i) := by
  let e₁ : {j : ↥(insert n s) // j != ⟨n, by simp⟩} ≃ ↑s :=
    ⟨fun x => ⟨x, by aesop⟩, fun x => ⟨⟨x, by aesop⟩, by aesop⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨i, hi, hi'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H
    (a := fun i : ↥(insert n s) => a i) ⟨n, by simp⟩ (ha.comp_equiv e₁)
  let e₂ : {j // j != i} ≃ ↥(insert n s \ {i.1}) := ⟨fun x => ⟨x, x.1.2, fun h => x.2 (Subtype.ext h)⟩,
    fun x => ⟨⟨x, x.2.1⟩, fun h => x.2.2 congr($h.1)⟩, fun _ => rfl, fun _ => rfl⟩
  have : a '' (insert n s \ {i.1}) = (a ·.1) '' {i}ᶜ := by ext; aesop
  refine ⟨i, hi.comp_equiv e₂.symm, by convert! hi'⟩

/--
Suppose `k` has characteristic `p` and `K/k` is generated by `a₁,...,aₙ₊₁`,
where `a₁,...aₙ` form a transcendence basis.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then some subset of `a₁,...,aₙ₊₁` forms a separating transcendence basis.
-/
@[stacks 0H71]
/--
lemma `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top` / 引理 `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top`

English:
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
  proof: by
  have ⟨i, hi⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H n ha'
  refine ⟨i, hi.1, ?_⟩
  rw [← separableClosure.eq_top_iff]; rw [← (restrictScalars_injective k).eq_iff]; rw [restrictScalars_top]; rw [eq_top_iff]; rw [← ha]; rw [adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  

中文:
引理 exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
  证明: by
  have ⟨i, hi⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H n ha'
  refine ⟨i, hi.1, ?_⟩
  rw [← separableClosure.eq_top_iff]; rw [← (restrictScalars_injective k).eq_iff]; rw [restrictScalars_top]; rw [eq_top_iff]; rw [← ha]; rw [adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  

Depends on / 依赖: adjoin, adjoin_le_iff, eq_iff, eq_or_ne, eq_top_iff, exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow, isSeparable_algebraMap, restrictScalars_injective, restrictScalars_top, separableClosure, separableClosure.eq_top_iff, subset_adjoin
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_adjoin_eq_top
    (ha : IntermediateField.adjoin k (Set.range a) = ⊤)
    (ha' : IsTranscendenceBasis k fun i : {i // i != n} => a i) :
    exists i : ι, IsTranscendenceBasis k (fun j : {j // j != i} => a j) ∧
      Algebra.IsSeparable (adjoin k (a '' {i}ᶜ)) K := by
  have ⟨i, hi⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H n ha'
  refine ⟨i, hi.1, ?_⟩
  rw [← separableClosure.eq_top_iff]; rw [← (restrictScalars_injective k).eq_iff]; rw [restrictScalars_top]; rw [eq_top_iff]; rw [← ha]; rw [adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  obtain rfl | ne := eq_or_ne x i
  · exact hi.2
  · exact isSeparable_algebraMap (F := adjoin k (a '' {i}ᶜ)) ⟨_, subset_adjoin _ _ ⟨x, ne, rfl⟩⟩

/--
Suppose `k` has characteristic `p` and `K/k` is finitely generated.
Suppose furthermore that if `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
`{ sᵢᵖ } ⊆ K` is also `k`-linearly independent (which is true when `K ⊗ₖ k^{1/p}` is reduced).

Then `K/k` is finite separably generated.

TODO: show that this is an if and only if.
-/
@[stacks 030W "(2) ⇒ (1) finitely generated case"]
/--
lemma `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType` / 引理 `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`

English:
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
  proof: by
  have ⟨s, hs, Hs⟩ := exists_finset_maximalFor_isTranscendenceBasis_separableClosure k K
  refine ⟨s, hs, ⟨fun n => of_not_not fun hn => ?_⟩⟩
  have hns : n ∉ s := fun h => hn (le_restrictScalars_separableClosure _ (subset_adjoin _ _ h))
  have ⟨i, hi₁, hi₂⟩ := exists_isTranscendenceBasis_and_isS

中文:
引理 exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
  证明: by
  have ⟨s, hs, Hs⟩ := exists_finset_maximalFor_isTranscendenceBasis_separableClosure k K
  refine ⟨s, hs, ⟨fun n => of_not_not fun hn => ?_⟩⟩
  have hns : n ∉ s := fun h => hn (le_restrictScalars_separableClosure _ (subset_adjoin _ _ h))
  have ⟨i, hi₁, hi₂⟩ := exists_isTranscendenceBasis_and_isS

Depends on / 依赖: Set.image_id, SetLike, SetLike.lt_iff_le_and_exists.mpr, exists_finset_maximalFor_isTranscendenceBasis_separableClosure, exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow, image_id, le_restrictScalars_separableClosure, lt_iff_le_and_exists, not_lt_iff_le_imp_ge, not_lt_iff_le_imp_ge.mpr, of_not_not, separableClosure_le_separa, subset_adjoin
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
    [Algebra.EssFiniteType k K] :
    exists s : Finset K, IsTranscendenceBasis k ((↑) : s -> K) ∧
      Algebra.IsSeparable (adjoin k (s : Set K)) K := by
  have ⟨s, hs, Hs⟩ := exists_finset_maximalFor_isTranscendenceBasis_separableClosure k K
  refine ⟨s, hs, ⟨fun n => of_not_not fun hn => ?_⟩⟩
  have hns : n ∉ s := fun h => hn (le_restrictScalars_separableClosure _ (subset_adjoin _ _ h))
  have ⟨i, hi₁, hi₂⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
    p hp (a := id) H s n hs hns
  rw [Set.image_id] at hi₂
  refine not_lt_iff_le_imp_ge.mpr (Hs hi₁) (SetLike.lt_iff_le_and_exists.mpr ⟨?_, n, ?_, hn⟩)
  · rw [separableClosure_le_separableClosure_iff, adjoin_le_iff]
    intro x hx
    obtain rfl | ne := eq_or_ne x i
    exacts [hi₂, le_restrictScalars_separableClosure _ (subset_adjoin _ _ ⟨.inr hx, ne⟩)]
  · obtain rfl | ne := eq_or_ne n i
    exacts [hi₂, le_restrictScalars_separableClosure _ (subset_adjoin _ _ ⟨.inl rfl, ne⟩)]

end

set_option backward.isDefEq.respectTransparency.types false in
variable (k K) in
/--
lemma `exists_isTranscendenceBasis_and_isSeparable_of_perfectField` / 引理 `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`

English:
lemma exists_isTranscendenceBasis_and_isSeparable_of_perfectField
  proof: by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · obtain ⟨s, hs⟩ := IntermediateField.fg_top k K
    have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set K)) K := by
      rw [← isAlgebraic_adjoin_iff_top]; rw [hs]; rw [Algebra.isAlgebraic_iff_isIntegral]
      exact Algebra.isIntegral_of_surject

中文:
引理 exists_isTranscendenceBasis_and_isSeparable_of_perfectField
  证明: by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · obtain ⟨s, hs⟩ := IntermediateField.fg_top k K
    have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set K)) K := by
      rw [← isAlgebraic_adjoin_iff_top]; rw [hs]; rw [Algebra.isAlgebraic_iff_isIntegral]
      exact Algebra.isIntegral_of_surject

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.adjoin, Algebra.isAlgebraic_iff_isIntegral, Algebra.isIntegral_of_surjective, CharP.exists, Finset, IntermediateField, IntermediateField.adjoin, IntermediateField.fg_top, IsAlgebraic, adjoin, exists_isTranscendenceBasis_subset, fg_top, finite_toSet, isAlgebraic_adjoin_iff_top, isAlgebraic_iff_isIntegral, isIntegral_of_surjective, s.finite_toSet.subset, subset
-/
lemma exists_isTranscendenceBasis_and_isSeparable_of_perfectField
    [PerfectField k] [Algebra.EssFiniteType k K] :
    exists s : Finset K, IsTranscendenceBasis k ((↑) : s -> K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · obtain ⟨s, hs⟩ := IntermediateField.fg_top k K
    have : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set K)) K := by
      rw [← isAlgebraic_adjoin_iff_top]; rw [hs]; rw [Algebra.isAlgebraic_iff_isIntegral]
      exact Algebra.isIntegral_of_surjective topEquiv.surjective
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) (s : Set K)
    lift t to Finset K using s.finite_toSet.subset hts
    have : Algebra.IsAlgebraic (IntermediateField.adjoin k (t : Set K)) K := by
      convert! ht.isAlgebraic_field <;> simp
    exact ⟨t, ht, inferInstance⟩
  have : ExpChar k p := .prime hp.out
  have : CharP K p := .of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
  refine exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
    p hp.out fun s hs => ?_
  apply hs.map_of_injective_injective (frobeniusEquiv k p).symm (frobenius K p).toAddMonoidHom <;>
    simp [frobenius, Algebra.smul_def, mul_pow, ← map_pow, frobeniusEquiv_symm_pow]

end
