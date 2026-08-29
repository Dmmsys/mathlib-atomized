/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Artinian.Module

/-!
# Results on the eigenvalue 0

In this file we provide equivalent characterizations of properties related to the eigenvalue 0,
such as being nilpotent, having determinant equal to 0, having a non-trivial kernel, etc...

## Main results

* `LinearMap.charpoly_nilpotent_tfae`:
  equivalent characterizations of nilpotent endomorphisms
* `LinearMap.hasEigenvalue_zero_tfae`:
  equivalent characterizations of endomorphisms with eigenvalue 0
* `LinearMap.not_hasEigenvalue_zero_tfae`:
  endomorphisms without eigenvalue 0
* `LinearMap.finrank_maxGenEigenspace`:
  the dimension of the maximal generalized eigenspace of an endomorphism
  is the trailing degree of its characteristic polynomial

-/

public section

variable {R K M : Type*} [CommRing R] [IsDomain R] [Field K] [AddCommGroup M]
variable [Module R M] [Module.Finite R M] [Module.Free R M]
variable [Module K M] [Module.Finite K M]

open Module Module.Free Polynomial

/--
lemma `IsNilpotent.charpoly_eq_X_pow_finrank` / 引理 `IsNilpotent.charpoly_eq_X_pow_finrank`

English:
lemma IsNilpotent.charpoly_eq_X_pow_finrank
  given: {φ : Module.End R M} (h : IsNilpotent φ)
  proof: by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [finrank_eq_card_chooseBasisIndex]
  apply Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
  exact h.map (LinearMap.toMatrixAlgEquiv (chooseBasis R M))

中文:
引理 是幂零.charpoly_eq_X_pow_finrank
  条件: {φ : 模.End R M} (h : 是幂零 φ)
  证明: by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [finrank_eq_card_chooseBasisIndex]
  apply Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
  exact h.map (LinearMap.toMatrixAlgEquiv (chooseBasis R M))

Depends on / 依赖: IsNilpotent, IsNilpotent.eq_zero, LinearMap, LinearMap.toMatrixAlgEquiv, Matrix, Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent, chooseBasis, eq_zero, finrank_eq_card_chooseBasisIndex, h.map, isNilpotent_charpoly_sub_pow_of_isNilpotent, sub_eq_zero, toMatrixAlgEquiv
-/
lemma IsNilpotent.charpoly_eq_X_pow_finrank {φ : Module.End R M} (h : IsNilpotent φ) :
    φ.charpoly = X ^ finrank R M := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [finrank_eq_card_chooseBasisIndex]
  apply Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent
  exact h.map (LinearMap.toMatrixAlgEquiv (chooseBasis R M))

namespace LinearMap

/--
lemma `isNilpotent_iff_charpoly` / 引理 `isNilpotent_iff_charpoly`

English:
lemma isNilpotent_iff_charpoly
  given: (φ : End R M)
  proof: ⟨IsNilpotent.charpoly_eq_X_pow_finrank,
    fun h => ⟨finrank R M, by rw [← @aeval_X_pow R, ← h, aeval_self_charpoly φ]⟩⟩

中文:
引理 isNilpotent_iff_charpoly
  条件: (φ : End R M)
  证明: ⟨IsNilpotent.charpoly_eq_X_pow_finrank,
    fun h => ⟨finrank R M, by rw [← @aeval_X_pow R, ← h, aeval_self_charpoly φ]⟩⟩

Depends on / 依赖: IsNilpotent, IsNilpotent.charpoly_eq_X_pow_finrank, aeval_X_pow, aeval_self_charpoly, charpoly_eq_X_pow_finrank, finrank
-/
lemma isNilpotent_iff_charpoly (φ : End R M) :
    IsNilpotent φ ↔ charpoly φ = X ^ finrank R M :=
  ⟨IsNilpotent.charpoly_eq_X_pow_finrank,
    fun h => ⟨finrank R M, by rw [← @aeval_X_pow R, ← h, aeval_self_charpoly φ]⟩⟩

open Module.Free in
/--
lemma `charpoly_nilpotent_tfae` / 引理 `charpoly_nilpotent_tfae`

English:
lemma charpoly_nilpotent_tfae
  given: [IsNoetherian R M] (φ : Module.End R M)
  proof: by
  tfae_have 1 -> 2 := IsNilpotent.charpoly_eq_X_pow_finrank
  tfae_have 2 -> 3
  | h, m => by
    use finrank R M
    suffices φ ^ finrank R M = 0 by simp only [this, LinearMap.zero_apply]
    simpa only [h, map_pow, aeval_X] using φ.aeval_self_charpoly
  tfae_have 3 -> 1
  | h => by
obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp φ.eventually_iSup_ker_pow_eq
    use n
    ext x
    rw [zero_apply]; rw [← mem_ker]; rw [← hn n le_rfl]
    obtain ⟨k, hk⟩ := h x
    rw [← mem_ker] at hk
    exact Submodule.mem_iSup_of_mem _ hk
  tfae_have 2 ↔ 4 := by
    rw [← φ.charpoly_natDegree]; rw [φ.charpoly_monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree]
  tfae_finish

中文:
引理 charpoly_nilpotent_tfae
  条件: [是Noether R M] (φ : 模.End R M)
  证明: by
  tfae_have 1 -> 2 := IsNilpotent.charpoly_eq_X_pow_finrank
  tfae_have 2 -> 3
  | h, m => by
    use finrank R M
    suffices φ ^ finrank R M = 0 by simp only [this, LinearMap.zero_apply]
    simpa only [h, map_pow, aeval_X] using φ.aeval_self_charpoly
  tfae_have 3 -> 1
  | h => by
obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp φ.eventually_iSup_ker_pow_eq
    use n
    ext x
    rw [zero_apply]; rw [← mem_ker]; rw [← hn n le_rfl]
    obtain ⟨k, hk⟩ := h x
    rw [← mem_ker] at hk
    exact Submodule.mem_iSup_of_mem _ hk
  tfae_have 2 ↔ 4 := by
    rw [← φ.charpoly_natDegree]; rw [φ.charpoly_monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree]
  tfae_finish

Depends on / 依赖: Filter, Filter.eventually_atTop.mp, IsNilpotent, IsNilpotent.charpoly_eq_X_pow_finrank, LinearMap, LinearMap.zero_apply, Submodule, Submodule.mem_iSup_of_mem, aeval_X, aeval_self_charpoly, charpoly_eq_X_pow_finrank, eventually_atTop, eventually_iSup_ker_pow_eq, finrank, le_rfl, map_pow, mem_iSup_of_mem, mem_ker, tfae_have, zero_apply
-/
lemma charpoly_nilpotent_tfae [IsNoetherian R M] (φ : Module.End R M) :
    List.TFAE [
      IsNilpotent φ,
      φ.charpoly = X ^ finrank R M,
      forall m : M, exists (n : Nat), (φ ^ n) m = 0,
      natTrailingDegree φ.charpoly = finrank R M ] := by
  tfae_have 1 -> 2 := IsNilpotent.charpoly_eq_X_pow_finrank
  tfae_have 2 -> 3
  | h, m => by
    use finrank R M
    suffices φ ^ finrank R M = 0 by simp only [this, LinearMap.zero_apply]
    simpa only [h, map_pow, aeval_X] using φ.aeval_self_charpoly
  tfae_have 3 -> 1
  | h => by
obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp φ.eventually_iSup_ker_pow_eq
    use n
    ext x
    rw [zero_apply]; rw [← mem_ker]; rw [← hn n le_rfl]
    obtain ⟨k, hk⟩ := h x
    rw [← mem_ker] at hk
    exact Submodule.mem_iSup_of_mem _ hk
  tfae_have 2 ↔ 4 := by
    rw [← φ.charpoly_natDegree]; rw [φ.charpoly_monic.eq_X_pow_iff_natTrailingDegree_eq_natDegree]
  tfae_finish

/--
lemma `charpoly_eq_X_pow_iff` / 引理 `charpoly_eq_X_pow_iff`

English:
lemma charpoly_eq_X_pow_iff
  given: [IsNoetherian R M] (φ : Module.End R M)
  proof: (charpoly_nilpotent_tfae φ).out 1 2

中文:
引理 charpoly_eq_X_pow_iff
  条件: [是Noether R M] (φ : 模.End R M)
  证明: (charpoly_nilpotent_tfae φ).out 1 2

Depends on / 依赖: charpoly_nilpotent_tfae
-/
lemma charpoly_eq_X_pow_iff [IsNoetherian R M] (φ : Module.End R M) :
    φ.charpoly = X ^ finrank R M ↔ forall m : M, exists (n : Nat), (φ ^ n) m = 0 :=
  (charpoly_nilpotent_tfae φ).out 1 2

open Module.Free in
/--
lemma `hasEigenvalue_zero_tfae` / 引理 `hasEigenvalue_zero_tfae`

English:
lemma hasEigenvalue_zero_tfae
  given: (φ : Module.End K M)
  proof: by
  tfae_have 1 ↔ 2 := Module.End.hasEigenvalue_iff_isRoot
  tfae_have 2 -> 3 := by
    obtain ⟨F, hF⟩ := minpoly_dvd_charpoly φ
    simp only [IsRoot.def, constantCoeff_apply, coeff_zero_eq_eval_zero, hF, eval_mul]
    intro h; rw [h, zero_mul]
  tfae_have 3 -> 4 := by
    rw [← LinearMap.det_toMatrix (chooseBasis K M)]; rw [Matrix.det_eq_sign_charpoly_coeff]; rw [constantCoeff_apply]; rw [charpoly]
    intro h; rw [h, mul_zero]
  tfae_have 4 -> 5 := bot_lt_ker_of_det_eq_zero
  tfae_have 5 -> 6 := by
    contrapose!
    simp only [not_bot_lt_iff, eq_bot_iff]
    intro h x
    simp only [mem_ker, Submodule.mem_bot]
    contrapose!
    apply h
  tfae_have 6 -> 1
  | ⟨x, h1, h2⟩ => by
    apply Module.End.hasEigenvalue_of_hasEigenvector ⟨_, h1⟩
    simpa only [Module.End.eigenspace_zero, mem_ker] using h2
  tfae_finish

中文:
引理 hasEigenvalue_zero_tfae
  条件: (φ : 模.End K M)
  证明: by
  tfae_have 1 ↔ 2 := Module.End.hasEigenvalue_iff_isRoot
  tfae_have 2 -> 3 := by
    obtain ⟨F, hF⟩ := minpoly_dvd_charpoly φ
    simp only [IsRoot.def, constantCoeff_apply, coeff_zero_eq_eval_zero, hF, eval_mul]
    intro h; rw [h, zero_mul]
  tfae_have 3 -> 4 := by
    rw [← LinearMap.det_toMatrix (chooseBasis K M)]; rw [Matrix.det_eq_sign_charpoly_coeff]; rw [constantCoeff_apply]; rw [charpoly]
    intro h; rw [h, mul_zero]
  tfae_have 4 -> 5 := bot_lt_ker_of_det_eq_zero
  tfae_have 5 -> 6 := by
    contrapose!
    simp only [not_bot_lt_iff, eq_bot_iff]
    intro h x
    simp only [mem_ker, Submodule.mem_bot]
    contrapose!
    apply h
  tfae_have 6 -> 1
  | ⟨x, h1, h2⟩ => by
    apply Module.End.hasEigenvalue_of_hasEigenvector ⟨_, h1⟩
    simpa only [Module.End.eigenspace_zero, mem_ker] using h2
  tfae_finish

Depends on / 依赖: IsRoot, IsRoot.def, LinearMap, LinearMap.det_toMatrix, Matrix, Matrix.det_eq_sign_charpoly_coeff, Module, Module.End.hasEigenvalue_iff_isRoot, bot_lt_ker_of_det_eq_zero, charpoly, chooseBasis, coeff_zero_eq_eval_zero, constantCoeff_apply, contrapose, det_eq_sign_charpoly_coeff, det_toMatrix, eval_mul, hasEigenvalue_iff_isRoot, minpoly_dvd_charpoly, mul_zero
-/
lemma hasEigenvalue_zero_tfae (φ : Module.End K M) :
    List.TFAE [
      Module.End.HasEigenvalue φ 0,
      IsRoot (minpoly K φ) 0,
      constantCoeff φ.charpoly = 0,
      LinearMap.det φ = 0,
      ⊥ < ker φ,
      exists (m : M), m != 0 ∧ φ m = 0 ] := by
  tfae_have 1 ↔ 2 := Module.End.hasEigenvalue_iff_isRoot
  tfae_have 2 -> 3 := by
    obtain ⟨F, hF⟩ := minpoly_dvd_charpoly φ
    simp only [IsRoot.def, constantCoeff_apply, coeff_zero_eq_eval_zero, hF, eval_mul]
    intro h; rw [h, zero_mul]
  tfae_have 3 -> 4 := by
    rw [← LinearMap.det_toMatrix (chooseBasis K M)]; rw [Matrix.det_eq_sign_charpoly_coeff]; rw [constantCoeff_apply]; rw [charpoly]
    intro h; rw [h, mul_zero]
  tfae_have 4 -> 5 := bot_lt_ker_of_det_eq_zero
  tfae_have 5 -> 6 := by
    contrapose!
    simp only [not_bot_lt_iff, eq_bot_iff]
    intro h x
    simp only [mem_ker, Submodule.mem_bot]
    contrapose!
    apply h
  tfae_have 6 -> 1
  | ⟨x, h1, h2⟩ => by
    apply Module.End.hasEigenvalue_of_hasEigenvector ⟨_, h1⟩
    simpa only [Module.End.eigenspace_zero, mem_ker] using h2
  tfae_finish

/--
lemma `charpoly_constantCoeff_eq_zero_iff` / 引理 `charpoly_constantCoeff_eq_zero_iff`

English:
lemma charpoly_constantCoeff_eq_zero_iff
  given: (φ : Module.End K M)
  proof: (hasEigenvalue_zero_tfae φ).out 2 5

中文:
引理 charpoly_constantCoeff_eq_zero_iff
  条件: (φ : 模.End K M)
  证明: (hasEigenvalue_zero_tfae φ).out 2 5

Depends on / 依赖: hasEigenvalue_zero_tfae
-/
lemma charpoly_constantCoeff_eq_zero_iff (φ : Module.End K M) :
    constantCoeff φ.charpoly = 0 ↔ exists (m : M), m != 0 ∧ φ m = 0 :=
  (hasEigenvalue_zero_tfae φ).out 2 5

open Module.Free in
/--
lemma `not_hasEigenvalue_zero_tfae` / 引理 `not_hasEigenvalue_zero_tfae`

English:
lemma not_hasEigenvalue_zero_tfae
  given: (φ : Module.End K M)
  proof: by
  have := (hasEigenvalue_zero_tfae φ).not
  dsimp only [List.map] at this
  push Not at this
  have aux₁ : forall m, (m != 0 -> φ m != 0) ↔ (φ m = 0 -> m = 0) := by intro m; apply not_imp_not
  have aux₂ : ker φ = ⊥ ↔ ¬ ⊥ < ker φ := by rw [bot_lt_iff_ne_bot, not_not]
  simpa only [aux₁, aux₂] using this

中文:
引理 not_hasEigenvalue_zero_tfae
  条件: (φ : 模.End K M)
  证明: by
  have := (hasEigenvalue_zero_tfae φ).not
  dsimp only [List.map] at this
  push Not at this
  have aux₁ : forall m, (m != 0 -> φ m != 0) ↔ (φ m = 0 -> m = 0) := by intro m; apply not_imp_not
  have aux₂ : ker φ = ⊥ ↔ ¬ ⊥ < ker φ := by rw [bot_lt_iff_ne_bot, not_not]
  simpa only [aux₁, aux₂] using this

Depends on / 依赖: List.map, bot_lt_iff_ne_bot, hasEigenvalue_zero_tfae, not_imp_not, not_not
-/
lemma not_hasEigenvalue_zero_tfae (φ : Module.End K M) :
    List.TFAE [
      ¬ Module.End.HasEigenvalue φ 0,
      ¬ IsRoot (minpoly K φ) 0,
      constantCoeff φ.charpoly != 0,
      LinearMap.det φ != 0,
      ker φ = ⊥,
      forall (m : M), φ m = 0 -> m = 0 ] := by
  have := (hasEigenvalue_zero_tfae φ).not
  dsimp only [List.map] at this
  push Not at this
  have aux₁ : forall m, (m != 0 -> φ m != 0) ↔ (φ m = 0 -> m = 0) := by intro m; apply not_imp_not
  have aux₂ : ker φ = ⊥ ↔ ¬ ⊥ < ker φ := by rw [bot_lt_iff_ne_bot, not_not]
  simpa only [aux₁, aux₂] using this

open Module.Free in
/--
lemma `finrank_maxGenEigenspace_zero_eq` / 引理 `finrank_maxGenEigenspace_zero_eq`

English:
lemma finrank_maxGenEigenspace_zero_eq
  given: (φ : Module.End K M)
  proof: by
  set V := φ.maxGenEigenspace 0
  have hV : V = ⨆ (n : Nat), ker (φ ^ n) := by
    simp [V, ← Module.End.iSup_genEigenspace_eq, Module.End.genEigenspace_nat]
  let W := ⨅ (n : Nat), LinearMap.range (φ ^ n)
  have hVW : IsCompl V W := by
    rw [hV]
    exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have hφV : forall x in V, φ x in V := by
    simp only [V, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero,
      forall_exists_index]
    intro x n hx
    use n
    rw [← Module.End.mul_apply]; rw [← pow_succ]; rw [pow_succ']; rw [Module.End.mul_apply]; rw [hx]; rw [map_zero]
  have hφW : forall x in W, φ x in W := by
    simp only [W, Submodule.mem_iInf, mem_range]
    intro x H n
    obtain ⟨y, rfl⟩ := H n
    use φ y
    rw [← Module.End.mul_apply]; rw [← pow_succ]; rw [pow_succ']; rw [Module.End.mul_apply]
  let F := φ.restrict hφV
  let G := φ.restrict hφW
  let ψ := F.prodMap G
  let e := Submodule.prodEquivOfIsCompl V W hVW
  let bV := chooseBasis K V
  let bW := chooseBasis K W
  let b := bV.prod bW
  have hψ : ψ = e.symm.conj φ := by
    apply b.ext
    simp only [Basis.prod_apply, coe_inl, coe_inr, prodMap_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl, coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, coprod_apply, Submodule.coe_subtype, map_add, Sum.forall, Sum.elim_inl,
      map_zero, ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply, and_self,
      Submodule.coe_prodEquivOfIsCompl', coe_restrict_apply, implies_true, Sum.elim_inr, zero_add,
      e, V, W, ψ, F, G, b]
  rw [← e.symm.charpoly_conj φ]; rw [← hψ]; rw [charpoly_prodMap]; rw [natTrailingDegree_mul (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero]
  have hG : natTrailingDegree (charpoly G) = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
    apply ((not_hasEigenvalue_zero_tfae G).out 2 5).mpr
    intro x hx
    apply Subtype.ext
    suffices x.1 in V ⊓ W by rwa [hVW.inf_eq_bot, Submodule.mem_bot] at this
    suffices x.1 in V from ⟨this, x.2⟩
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V]
    use 1
    rw [pow_one]
    rwa [Subtype.ext_iff] at hx
  rw [hG]; rw [add_zero]; rw [eq_comm]
  apply ((charpoly_nilpotent_tfae F).out 2 3).mp
  simp only [Subtype.forall, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V, F]
  rintro x ⟨n, hx⟩
  use n
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  refine .trans ?_ hx
  generalize_proofs h'
  clear hx
  induction n <;> simp [pow_succ', *]

中文:
引理 finrank_maxGenEigenspace_zero_eq
  条件: (φ : 模.End K M)
  证明: by
  set V := φ.maxGenEigenspace 0
  have hV : V = ⨆ (n : Nat), ker (φ ^ n) := by
    simp [V, ← Module.End.iSup_genEigenspace_eq, Module.End.genEigenspace_nat]
  let W := ⨅ (n : Nat), LinearMap.range (φ ^ n)
  have hVW : IsCompl V W := by
    rw [hV]
    exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have hφV : forall x in V, φ x in V := by
    simp only [V, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero,
      forall_exists_index]
    intro x n hx
    use n
    rw [← Module.End.mul_apply]; rw [← pow_succ]; rw [pow_succ']; rw [Module.End.mul_apply]; rw [hx]; rw [map_zero]
  have hφW : forall x in W, φ x in W := by
    simp only [W, Submodule.mem_iInf, mem_range]
    intro x H n
    obtain ⟨y, rfl⟩ := H n
    use φ y
    rw [← Module.End.mul_apply]; rw [← pow_succ]; rw [pow_succ']; rw [Module.End.mul_apply]
  let F := φ.restrict hφV
  let G := φ.restrict hφW
  let ψ := F.prodMap G
  let e := Submodule.prodEquivOfIsCompl V W hVW
  let bV := chooseBasis K V
  let bW := chooseBasis K W
  let b := bV.prod bW
  have hψ : ψ = e.symm.conj φ := by
    apply b.ext
    simp only [Basis.prod_apply, coe_inl, coe_inr, prodMap_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl, coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, coprod_apply, Submodule.coe_subtype, map_add, Sum.forall, Sum.elim_inl,
      map_zero, ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply, and_self,
      Submodule.coe_prodEquivOfIsCompl', coe_restrict_apply, implies_true, Sum.elim_inr, zero_add,
      e, V, W, ψ, F, G, b]
  rw [← e.symm.charpoly_conj φ]; rw [← hψ]; rw [charpoly_prodMap]; rw [natTrailingDegree_mul (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero]
  have hG : natTrailingDegree (charpoly G) = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
    apply ((not_hasEigenvalue_zero_tfae G).out 2 5).mpr
    intro x hx
    apply Subtype.ext
    suffices x.1 in V ⊓ W by rwa [hVW.inf_eq_bot, Submodule.mem_bot] at this
    suffices x.1 in V from ⟨this, x.2⟩
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V]
    use 1
    rw [pow_one]
    rwa [Subtype.ext_iff] at hx
  rw [hG]; rw [add_zero]; rw [eq_comm]
  apply ((charpoly_nilpotent_tfae F).out 2 3).mp
  simp only [Subtype.forall, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V, F]
  rintro x ⟨n, hx⟩
  use n
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  refine .trans ?_ hx
  generalize_proofs h'
  clear hx
  induction n <;> simp [pow_succ', *]

Depends on / 依赖: IsCompl, LinearMap, LinearMap.isCompl_iSup_ker_pow_iInf_range_pow, LinearMap.range, Module, Module.End.genEigenspace_nat, Module.End.iSup_genEigenspace_eq, Module.End.mem_maxGenEigenspace, Module.End.mul_apply, forall_exists_index, genEigenspace_nat, iSup_genEigenspace_eq, isCompl_iSup_ker_pow_iInf_range_pow, maxGenEigenspace, mem_maxGenEigenspace, mul_apply, pow_succ, sub_zero, zero_smul
-/
lemma finrank_maxGenEigenspace_zero_eq (φ : Module.End K M) :
    finrank K (φ.maxGenEigenspace 0) = natTrailingDegree (φ.charpoly) := by
  set V := φ.maxGenEigenspace 0
  have hV : V = ⨆ (n : Nat), ker (φ ^ n) := by
    simp [V, ← Module.End.iSup_genEigenspace_eq, Module.End.genEigenspace_nat]
  let W := ⨅ (n : Nat), LinearMap.range (φ ^ n)
  have hVW : IsCompl V W := by
    rw [hV]
    exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow φ
  have hφV : forall x in V, φ x in V := by
    simp only [V, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero,
      forall_exists_index]
    intro x n hx
    use n
    rw [← Module.End.mul_apply]; rw [← pow_succ]; rw [pow_succ']; rw [Module.End.mul_apply]; rw [hx]; rw [map_zero]
  have hφW : forall x in W, φ x in W := by
    simp only [W, Submodule.mem_iInf, mem_range]
    intro x H n
    obtain ⟨y, rfl⟩ := H n
    use φ y
    rw [← Module.End.mul_apply]; rw [← pow_succ]; rw [pow_succ']; rw [Module.End.mul_apply]
  let F := φ.restrict hφV
  let G := φ.restrict hφW
  let ψ := F.prodMap G
  let e := Submodule.prodEquivOfIsCompl V W hVW
  let bV := chooseBasis K V
  let bW := chooseBasis K W
  let b := bV.prod bW
  have hψ : ψ = e.symm.conj φ := by
    apply b.ext
    simp only [Basis.prod_apply, coe_inl, coe_inr, prodMap_apply, LinearEquiv.conj_apply,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl, coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, coprod_apply, Submodule.coe_subtype, map_add, Sum.forall, Sum.elim_inl,
      map_zero, ZeroMemClass.coe_zero, add_zero, LinearEquiv.eq_symm_apply, and_self,
      Submodule.coe_prodEquivOfIsCompl', coe_restrict_apply, implies_true, Sum.elim_inr, zero_add,
      e, V, W, ψ, F, G, b]
  rw [← e.symm.charpoly_conj φ]; rw [← hψ]; rw [charpoly_prodMap]; rw [natTrailingDegree_mul (charpoly_monic _).ne_zero (charpoly_monic _).ne_zero]
  have hG : natTrailingDegree (charpoly G) = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
    apply ((not_hasEigenvalue_zero_tfae G).out 2 5).mpr
    intro x hx
    apply Subtype.ext
    suffices x.1 in V ⊓ W by rwa [hVW.inf_eq_bot, Submodule.mem_bot] at this
    suffices x.1 in V from ⟨this, x.2⟩
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V]
    use 1
    rw [pow_one]
    rwa [Subtype.ext_iff] at hx
  rw [hG]; rw [add_zero]; rw [eq_comm]
  apply ((charpoly_nilpotent_tfae F).out 2 3).mp
  simp only [Subtype.forall, Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, V, F]
  rintro x ⟨n, hx⟩
  use n
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  refine .trans ?_ hx
  generalize_proofs h'
  clear hx
  induction n <;> simp [pow_succ', *]

/--
lemma `finrank_maxGenEigenspace_eq` / 引理 `finrank_maxGenEigenspace_eq`

English:
lemma finrank_maxGenEigenspace_eq
  given: (φ : Module.End K M) (μ : K)
  proof: by
  rw [φ.maxGenEigenspace_eq_maxGenEigenspace_zero]; rw [finrank_maxGenEigenspace_zero_eq]; rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]; rw [LinearMap.charpoly_sub_smul]

中文:
引理 finrank_maxGenEigenspace_eq
  条件: (φ : 模.End K M) (μ : K)
  证明: by
  rw [φ.maxGenEigenspace_eq_maxGenEigenspace_zero]; rw [finrank_maxGenEigenspace_zero_eq]; rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]; rw [LinearMap.charpoly_sub_smul]

Depends on / 依赖: LinearMap, LinearMap.charpoly_sub_smul, Polynomial, Polynomial.rootMultiplicity_eq_natTrailingDegree, charpoly_sub_smul, finrank_maxGenEigenspace_zero_eq, maxGenEigenspace_eq_maxGenEigenspace_zero, rootMultiplicity_eq_natTrailingDegree
-/
lemma finrank_maxGenEigenspace_eq (φ : Module.End K M) (μ : K) :
    finrank K (φ.maxGenEigenspace μ) = φ.charpoly.rootMultiplicity μ := by
  rw [φ.maxGenEigenspace_eq_maxGenEigenspace_zero]; rw [finrank_maxGenEigenspace_zero_eq]; rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]; rw [LinearMap.charpoly_sub_smul]

/--
lemma `finrank_genEigenspace_le` / 引理 `finrank_genEigenspace_le`

English:
lemma finrank_genEigenspace_le
  given: (φ : Module.End K M) (μ : K) (k : Nat)
  proof: by
  grw [Submodule.finrank_mono (φ.genEigenspace_le_maximal μ k), finrank_maxGenEigenspace_eq]

中文:
引理 finrank_genEigenspace_le
  条件: (φ : 模.End K M) (μ : K) (k : 自然数)
  证明: by
  grw [Submodule.finrank_mono (φ.genEigenspace_le_maximal μ k), finrank_maxGenEigenspace_eq]

Depends on / 依赖: Submodule, Submodule.finrank_mono, finrank_maxGenEigenspace_eq, finrank_mono, genEigenspace_le_maximal
-/
lemma finrank_genEigenspace_le (φ : Module.End K M) (μ : K) (k : Nat) :
    finrank K (φ.genEigenspace μ k) <= φ.charpoly.rootMultiplicity μ := by
  grw [Submodule.finrank_mono (φ.genEigenspace_le_maximal μ k), finrank_maxGenEigenspace_eq]

/--
lemma `finrank_eigenspace_le` / 引理 `finrank_eigenspace_le`

English:
lemma finrank_eigenspace_le
  given: (φ : Module.End K M) (μ : K)
  proof: finrank_genEigenspace_le ..

中文:
引理 finrank_eigenspace_le
  条件: (φ : 模.End K M) (μ : K)
  证明: finrank_genEigenspace_le ..

Depends on / 依赖: finrank_genEigenspace_le
-/
lemma finrank_eigenspace_le (φ : Module.End K M) (μ : K) :
    finrank K (φ.eigenspace μ) <= φ.charpoly.rootMultiplicity μ :=
  finrank_genEigenspace_le ..

end LinearMap
