/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Topology on the upper half plane

In this file we introduce a `TopologicalSpace` structure on the upper half plane and provide
various instances.
-/

@[expose] public section

noncomputable section

open Complex Filter Function Set TopologicalSpace Topology

open scoped ComplexConjugate

namespace UpperHalfPlane

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace ℍ
  body: .induced UpperHalfPlane.coe inferInstance

@[fun_prop]

中文:
实例 :
  签名: TopologicalSpace ℍ
  定义体: .induced UpperHalfPlane.coe inferInstance

@[fun_prop]

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.coe, induced
-/
instance : TopologicalSpace ℍ :=
  .induced UpperHalfPlane.coe inferInstance

@[fun_prop]
/--
theorem `isEmbedding_coe` / 定理 `isEmbedding_coe`

English:
theorem isEmbedding_coe
  statement: IsEmbedding ((↑) : ℍ -> Complex)
  proof: coe_injective.isEmbedding_induced

中文:
定理 isEmbedding_coe
  结论: IsEmbedding ((↑) : ℍ -> Complex)
  证明: coe_injective.isEmbedding_induced

Depends on / 依赖: coe_injective, coe_injective.isEmbedding_induced, isEmbedding_induced
-/
theorem isEmbedding_coe : IsEmbedding ((↑) : ℍ -> Complex) :=
  coe_injective.isEmbedding_induced

/--
theorem `isOpenEmbedding_coe` / 定理 `isOpenEmbedding_coe`

English:
theorem isOpenEmbedding_coe
  statement: IsOpenEmbedding ((↑) : ℍ -> Complex)
  proof: ⟨isEmbedding_coe, by simp [isOpen_upperHalfPlaneSet]⟩

@[fun_prop]

中文:
定理 isOpenEmbedding_coe
  结论: IsOpenEmbedding ((↑) : ℍ -> Complex)
  证明: ⟨isEmbedding_coe, by simp [isOpen_upperHalfPlaneSet]⟩

@[fun_prop]

Depends on / 依赖: isEmbedding_coe, isOpen_upperHalfPlaneSet
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℍ -> Complex) :=
  ⟨isEmbedding_coe, by simp [isOpen_upperHalfPlaneSet]⟩

@[fun_prop]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : ℍ -> Complex)
  proof: isEmbedding_coe.continuous

@[fun_prop]

中文:
定理 continuous_coe
  结论: Continuous ((↑) : ℍ -> Complex)
  证明: isEmbedding_coe.continuous

@[fun_prop]

Depends on / 依赖: continuous, isEmbedding_coe, isEmbedding_coe.continuous
-/
theorem continuous_coe : Continuous ((↑) : ℍ -> Complex) :=
  isEmbedding_coe.continuous

@[fun_prop]
/--
theorem `continuous_re` / 定理 `continuous_re`

English:
theorem continuous_re
  statement: Continuous re
  proof: Complex.continuous_re.comp continuous_coe

@[fun_prop]

中文:
定理 continuous_re
  结论: Continuous re
  证明: Complex.continuous_re.comp continuous_coe

@[fun_prop]

Depends on / 依赖: Complex.continuous_re.comp, continuous_coe, continuous_re
-/
theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe

@[fun_prop]
/--
theorem `continuous_im` / 定理 `continuous_im`

English:
theorem continuous_im
  statement: Continuous im
  proof: Complex.continuous_im.comp continuous_coe

@[fun_prop]

中文:
定理 continuous_im
  结论: Continuous im
  证明: Complex.continuous_im.comp continuous_coe

@[fun_prop]

Depends on / 依赖: Complex.continuous_im.comp, continuous_coe, continuous_im
-/
theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe

@[fun_prop]
/--
theorem `_root_.Continuous.upperHalfPlaneMk` / 定理 `_root_.Continuous.upperHalfPlaneMk`

English:
theorem _root_.Continuous.upperHalfPlaneMk
  statement: {X : Type*} [TopologicalSpace X] {f : X -> Complex}
  proof: isEmbedding_coe.continuous_iff.mpr hf

中文:
定理 _root_.Continuous.upperHalfPlaneMk
  结论: {X : 类型} [TopologicalSpace X] {f : X -> Complex}
  证明: isEmbedding_coe.continuous_iff.mpr hf

Depends on / 依赖: continuous_iff, isEmbedding_coe, isEmbedding_coe.continuous_iff.mpr
-/
theorem _root_.Continuous.upperHalfPlaneMk {X : Type*} [TopologicalSpace X] {f : X -> Complex}
    (hf : Continuous f) (hf₀ : forall x, 0 < (f x).im) :
    Continuous fun x => mk (f x) (hf₀ x) :=
  isEmbedding_coe.continuous_iff.mpr hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SecondCountableTopology ℍ
  body: secondCountableTopology_induced ..

中文:
实例 :
  签名: SecondCountableTopology ℍ
  定义体: secondCountableTopology_induced ..

Depends on / 依赖: secondCountableTopology_induced
-/
instance : SecondCountableTopology ℍ :=
  secondCountableTopology_induced ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T3Space ℍ
  body: isEmbedding_coe.t3Space

中文:
实例 :
  签名: T3Space ℍ
  定义体: isEmbedding_coe.t3Space

Depends on / 依赖: isEmbedding_coe, isEmbedding_coe.t3Space, t3Space
-/
instance : T3Space ℍ := isEmbedding_coe.t3Space

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T4Space ℍ
  body: inferInstance

中文:
实例 :
  签名: T4Space ℍ
  定义体: inferInstance
-/
instance : T4Space ℍ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContractibleSpace ℍ
  body: by
  rw [isEmbedding_coe.toHomeomorph.trans (.setCongr range_coe) |>.contractibleSpace_iff]
  exact (convex_halfSpace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

中文:
实例 :
  签名: ContractibleSpace ℍ
  定义体: by
  rw [isEmbedding_coe.toHomeomorph.trans (.setCongr range_coe) |>.contractibleSpace_iff]
  exact (convex_halfSpace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

Depends on / 依赖: I_im, I_im.symm, contractibleSpace, contractibleSpace_iff, convex_halfSpace_im_gt, isEmbedding_coe, isEmbedding_coe.toHomeomorph.trans, one_pos, one_pos.trans_eq, range_coe, setCongr, toHomeomorph, trans_eq
-/
instance : ContractibleSpace ℍ := by
  rw [isEmbedding_coe.toHomeomorph.trans (.setCongr range_coe) |>.contractibleSpace_iff]
  exact (convex_halfSpace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyPathConnectedSpace ℍ
  body: isOpenEmbedding_coe.locallyPathConnectedSpace

中文:
实例 :
  签名: LocallyPathConnectedSpace ℍ
  定义体: isOpenEmbedding_coe.locallyPathConnectedSpace

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.locallyPathConnectedSpace, locallyPathConnectedSpace
-/
instance : LocallyPathConnectedSpace ℍ := isOpenEmbedding_coe.locallyPathConnectedSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoncompactSpace ℍ
  body: by
    have : IsCompact (Complex.im ⁻¹' Ioi 0) := by
      simpa [isEmbedding_coe.isCompact_iff] using! h
    simpa [closure_preimage_im] using! congr(0 in $this.isClosed.closure_eq)

中文:
实例 :
  签名: NoncompactSpace ℍ
  定义体: by
    have : IsCompact (Complex.im ⁻¹' Ioi 0) := by
      simpa [isEmbedding_coe.isCompact_iff] using! h
    simpa [closure_preimage_im] using! congr(0 in $this.isClosed.closure_eq)

Depends on / 依赖: Complex.im, IsCompact, closure_eq, closure_preimage_im, isClosed, isCompact_iff, isEmbedding_coe, isEmbedding_coe.isCompact_iff, this.isClosed.closure_eq
-/
instance : NoncompactSpace ℍ where
  noncompact_univ h := by
    have : IsCompact (Complex.im ⁻¹' Ioi 0) := by
      simpa [isEmbedding_coe.isCompact_iff] using! h
    simpa [closure_preimage_im] using! congr(0 in $this.isClosed.closure_eq)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallyCompactSpace ℍ
  body: isOpenEmbedding_coe.locallyCompactSpace

中文:
实例 :
  签名: LocallyCompactSpace ℍ
  定义体: isOpenEmbedding_coe.locallyCompactSpace

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.locallyCompactSpace, locallyCompactSpace
-/
instance : LocallyCompactSpace ℍ :=
  isOpenEmbedding_coe.locallyCompactSpace

/--
Instance `instContinuousGLSMul` / 实例 `instContinuousGLSMul`

English:
instance instContinuousGLSMul
  signature: : ContinuousConstSMul (GL (Fin 2) Real) ℍ where
  body: by
    simp_rw [continuous_induced_rng (f := UpperHalfPlane.coe), Function.comp_def,
      UpperHalfPlane.coe_smul, UpperHalfPlane.σ]
    refine .comp ?_ ?_
    · split_ifs
      exacts [continuous_id, continuous_conj]
    · refine .div ?_ ?_ (fun x => denom_ne_zero g x) <;>
      exact (continuous_

中文:
实例 instContinuousGLSMul
  签名: : ContinuousConstSMul (GL (Fin 2) 实数) ℍ where
  定义体: by
    simp_rw [continuous_induced_rng (f := UpperHalfPlane.coe), Function.comp_def,
      UpperHalfPlane.coe_smul, UpperHalfPlane.σ]
    refine .comp ?_ ?_
    · split_ifs
      exacts [continuous_id, continuous_conj]
    · refine .div ?_ ?_ (fun x => denom_ne_zero g x) <;>
      exact (continuous_

Depends on / 依赖: Function, Function.comp_def, UpperHalfPlane, UpperHalfPlane.coe, UpperHalfPlane.coe_smul, coe_smul, comp_def, continuous_coe, continuous_conj, continuous_const, continuous_const.mul, continuous_id, continuous_induced_rng, denom_ne_zero, exacts, simp_rw, split_ifs
-/
instance instContinuousGLSMul : ContinuousConstSMul (GL (Fin 2) Real) ℍ where
  continuous_const_smul g := by
    simp_rw [continuous_induced_rng (f := UpperHalfPlane.coe), Function.comp_def,
      UpperHalfPlane.coe_smul, UpperHalfPlane.σ]
    refine .comp ?_ ?_
    · split_ifs
      exacts [continuous_id, continuous_conj]
    · refine .div ?_ ?_ (fun x => denom_ne_zero g x) <;>
      exact (continuous_const.mul continuous_coe).add continuous_const

section strips

/--
Definition of `verticalStrip` / `verticalStrip` 的定义

English:
definition verticalStrip
  signature: (A B : Real)
  body: {z : ℍ | |z.re| <= A ∧ B <= z.im}

中文:
定义 verticalStrip
  签名: (A B : 实数)
  定义体: {z : ℍ | |z.re| <= A ∧ B <= z.im}

Depends on / 依赖: z.im, z.re
-/
def verticalStrip (A B : Real) := {z : ℍ | |z.re| <= A ∧ B <= z.im}

/--
theorem `mem_verticalStrip_iff` / 定理 `mem_verticalStrip_iff`

English:
theorem mem_verticalStrip_iff
  given: (A B : Real) (z : ℍ)
  statement: z in verticalStrip A B ↔ |z.re| <= A ∧ B <= z.im
  proof: Iff.rfl

@[gcongr]

中文:
定理 mem_verticalStrip_iff
  条件: (A B : 实数) (z : ℍ)
  结论: z in verticalStrip A B ↔ |z.re| <= A ∧ B <= z.im
  证明: Iff.rfl

@[gcongr]

Depends on / 依赖: Iff.rfl
-/
theorem mem_verticalStrip_iff (A B : Real) (z : ℍ) : z in verticalStrip A B ↔ |z.re| <= A ∧ B <= z.im :=
  Iff.rfl

@[gcongr]
/--
lemma `verticalStrip_mono` / 引理 `verticalStrip_mono`

English:
lemma verticalStrip_mono
  given: {A B A' B' : Real} (hA : A <= A') (hB : B' <= B)
  proof: by
  rintro z ⟨hzre, hzim⟩
  exact ⟨hzre.trans hA, hB.trans hzim⟩

中文:
引理 verticalStrip_mono
  条件: {A B A' B' : 实数} (hA : A <= A') (hB : B' <= B)
  证明: by
  rintro z ⟨hzre, hzim⟩
  exact ⟨hzre.trans hA, hB.trans hzim⟩

Depends on / 依赖: hB.trans, hzre.trans
-/
lemma verticalStrip_mono {A B A' B' : Real} (hA : A <= A') (hB : B' <= B) :
    verticalStrip A B subseteq verticalStrip A' B' := by
  rintro z ⟨hzre, hzim⟩
  exact ⟨hzre.trans hA, hB.trans hzim⟩

/--
lemma `verticalStrip_mono_left` / 引理 `verticalStrip_mono_left`

English:
lemma verticalStrip_mono_left
  given: {A A'} (h : A <= A') (B)
  statement: verticalStrip A B subseteq verticalStrip A' B
  proof: verticalStrip_mono h le_rfl

中文:
引理 verticalStrip_mono_left
  条件: {A A'} (h : A <= A') (B)
  结论: verticalStrip A B subseteq verticalStrip A' B
  证明: verticalStrip_mono h le_rfl

Depends on / 依赖: le_rfl, verticalStrip_mono
-/
lemma verticalStrip_mono_left {A A'} (h : A <= A') (B) : verticalStrip A B subseteq verticalStrip A' B :=
  verticalStrip_mono h le_rfl

/--
lemma `verticalStrip_anti_right` / 引理 `verticalStrip_anti_right`

English:
lemma verticalStrip_anti_right
  given: (A) {B B'} (h : B' <= B)
  statement: verticalStrip A B subseteq verticalStrip A B'
  proof: verticalStrip_mono le_rfl h

中文:
引理 verticalStrip_anti_right
  条件: (A) {B B'} (h : B' <= B)
  结论: verticalStrip A B subseteq verticalStrip A B'
  证明: verticalStrip_mono le_rfl h

Depends on / 依赖: le_rfl, verticalStrip_mono
-/
lemma verticalStrip_anti_right (A) {B B'} (h : B' <= B) : verticalStrip A B subseteq verticalStrip A B' :=
  verticalStrip_mono le_rfl h

/--
lemma `subset_verticalStrip_of_isCompact` / 引理 `subset_verticalStrip_of_isCompact`

English:
lemma subset_verticalStrip_of_isCompact
  given: {K : Set ℍ} (hK : IsCompact K)
  proof: by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, Real.zero_lt_one, empty_subset _⟩
  obtain ⟨u, _, hu⟩ := hK.exists_isMaxOn hne (_root_.continuous_abs.comp continuous_re).continuousOn
  obtain ⟨v, _, hv⟩ := hK.exists_isMinOn hne continuous_im.continuousOn
  exact ⟨|re u|, im v, v.i

中文:
引理 subset_verticalStrip_of_isCompact
  条件: {K : Set ℍ} (hK : IsCompact K)
  证明: by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, Real.zero_lt_one, empty_subset _⟩
  obtain ⟨u, _, hu⟩ := hK.exists_isMaxOn hne (_root_.continuous_abs.comp continuous_re).continuousOn
  obtain ⟨v, _, hv⟩ := hK.exists_isMinOn hne continuous_im.continuousOn
  exact ⟨|re u|, im v, v.i

Depends on / 依赖: K.eq_empty_or_nonempty, Real.zero_lt_one, _root_, _root_.continuous_abs.comp, continuousOn, continuous_abs, continuous_im, continuous_im.continuousOn, continuous_re, empty_subset, eq_empty_or_nonempty, exists_isMaxOn, exists_isMinOn, hK.exists_isMaxOn, hK.exists_isMinOn, im_pos, isMaxOn_iff, isMaxOn_iff.mp, isMinOn_iff, isMinOn_iff.mp
-/
lemma subset_verticalStrip_of_isCompact {K : Set ℍ} (hK : IsCompact K) :
    exists A B : Real, 0 < B ∧ K subseteq verticalStrip A B := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, Real.zero_lt_one, empty_subset _⟩
  obtain ⟨u, _, hu⟩ := hK.exists_isMaxOn hne (_root_.continuous_abs.comp continuous_re).continuousOn
  obtain ⟨v, _, hv⟩ := hK.exists_isMinOn hne continuous_im.continuousOn
  exact ⟨|re u|, im v, v.im_pos, fun k hk => ⟨isMaxOn_iff.mp hu _ hk, isMinOn_iff.mp hv _ hk⟩⟩

/--
theorem `ModularGroup_T_zpow_mem_verticalStrip` / 定理 `ModularGroup_T_zpow_mem_verticalStrip`

English:
theorem ModularGroup_T_zpow_mem_verticalStrip
  given: (z : ℍ) {N : Nat} (hn : 0 < N)
  proof: by
  let n := Int.floor (z.re / N)
  use -n
  rw [modular_T_zpow_smul z (N * -n)]
  refine ⟨?_, by simp⟩
  have h : (N * (-n : Real) +ᵥ z).re = -N * Int.floor (z.re / N) + z.re := by
    simp only [n, mul_neg, vadd_re, neg_mul]
  norm_cast at *
  rw [h]; rw [add_comm]
  simp only [neg_mul, Int.cast_

中文:
定理 ModularGroup_T_zpow_mem_verticalStrip
  条件: (z : ℍ) {N : 自然数} (hn : 0 < N)
  证明: by
  let n := Int.floor (z.re / N)
  use -n
  rw [modular_T_zpow_smul z (N * -n)]
  refine ⟨?_, by simp⟩
  have h : (N * (-n : Real) +ᵥ z).re = -N * Int.floor (z.re / N) + z.re := by
    simp only [n, mul_neg, vadd_re, neg_mul]
  norm_cast at *
  rw [h]; rw [add_comm]
  simp only [neg_mul, Int.cast_

Depends on / 依赖: Int.cast_mul, Int.cast_natCast, Int.cast_neg, Int.floor, Int.sub_floor_div_mul_nonneg, abs_eq_self, add_comm, cast_mul, cast_natCast, cast_neg, modular_T_zpow_smul, mul_neg, neg_mul, sub_floor_div_mul_nonneg, vadd_re, z.re
-/
theorem ModularGroup_T_zpow_mem_verticalStrip (z : ℍ) {N : Nat} (hn : 0 < N) :
    exists n : Int, ModularGroup.T ^ (N * n) • z in verticalStrip N z.im := by
  let n := Int.floor (z.re / N)
  use -n
  rw [modular_T_zpow_smul z (N * -n)]
  refine ⟨?_, by simp⟩
  have h : (N * (-n : Real) +ᵥ z).re = -N * Int.floor (z.re / N) + z.re := by
    simp only [n, mul_neg, vadd_re, neg_mul]
  norm_cast at *
  rw [h]; rw [add_comm]
  simp only [neg_mul, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  have hnn : (0 : Real) < (N : Real) := by norm_cast at *
  have h2 : z.re + -(N * n) = z.re - n * N := by ring
  rw [h2]; rw [abs_eq_self.2 (Int.sub_floor_div_mul_nonneg (z.re : Real) hnn)]
  apply (Int.sub_floor_div_mul_lt (z.re : Real) hnn).le

end strips

section ofComplex

/--
Definition of `ofComplex` / `ofComplex` 的定义

English:
definition ofComplex
  signature: : OpenPartialHomeomorph Complex ℍ
  body: (isOpenEmbedding_coe.toOpenPartialHomeomorph _).symm

中文:
定义 ofComplex
  签名: : OpenPartialHomeomorph Complex ℍ
  定义体: (isOpenEmbedding_coe.toOpenPartialHomeomorph _).symm

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.toOpenPartialHomeomorph, toOpenPartialHomeomorph
-/
def ofComplex : OpenPartialHomeomorph Complex ℍ := (isOpenEmbedding_coe.toOpenPartialHomeomorph _).symm

/-- Extend a function on `ℍ` arbitrarily to a function on all of `ℂ`. -/
scoped notation "↑ₕ" f => f ∘ ofComplex

@[simp]
/--
lemma `ofComplex_apply` / 引理 `ofComplex_apply`

English:
lemma ofComplex_apply
  given: (z : ℍ)
  statement: ofComplex (z : Complex) = z
  proof: IsOpenEmbedding.toOpenPartialHomeomorph_left_inv ..

中文:
引理 ofComplex_apply
  条件: (z : ℍ)
  结论: ofComplex (z : Complex) = z
  证明: IsOpenEmbedding.toOpenPartialHomeomorph_left_inv ..

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, toOpenPartialHomeomorph_left_inv
-/
lemma ofComplex_apply (z : ℍ) : ofComplex (z : Complex) = z :=
  IsOpenEmbedding.toOpenPartialHomeomorph_left_inv ..

/--
lemma `ofComplex_apply_eq_ite` / 引理 `ofComplex_apply_eq_ite`

English:
lemma ofComplex_apply_eq_ite
  given: (w : Complex)
  proof: by
  split_ifs with hw
  · exact ofComplex_apply ⟨w, hw⟩
  · change (Function.invFunOn UpperHalfPlane.coe Set.univ w) = _
    simp only [invFunOn, dite_eq_right_iff, mem_univ, true_and]
    rintro ⟨a, rfl⟩
    exact (a.im_pos.not_ge (by simpa using hw)).elim

中文:
引理 ofComplex_apply_eq_ite
  条件: (w : Complex)
  证明: by
  split_ifs with hw
  · exact ofComplex_apply ⟨w, hw⟩
  · change (Function.invFunOn UpperHalfPlane.coe Set.univ w) = _
    simp only [invFunOn, dite_eq_right_iff, mem_univ, true_and]
    rintro ⟨a, rfl⟩
    exact (a.im_pos.not_ge (by simpa using hw)).elim

Depends on / 依赖: Function, Function.invFunOn, Set.univ, UpperHalfPlane, UpperHalfPlane.coe, a.im_pos.not_ge, dite_eq_right_iff, im_pos, invFunOn, mem_univ, not_ge, ofComplex_apply, split_ifs, true_and
-/
lemma ofComplex_apply_eq_ite (w : Complex) :
    ofComplex w = if hw : 0 < w.im then ⟨w, hw⟩ else Classical.choice inferInstance := by
  split_ifs with hw
  · exact ofComplex_apply ⟨w, hw⟩
  · change (Function.invFunOn UpperHalfPlane.coe Set.univ w) = _
    simp only [invFunOn, dite_eq_right_iff, mem_univ, true_and]
    rintro ⟨a, rfl⟩
    exact (a.im_pos.not_ge (by simpa using hw)).elim

/--
lemma `ofComplex_apply_of_im_pos` / 引理 `ofComplex_apply_of_im_pos`

English:
lemma ofComplex_apply_of_im_pos
  given: {z : Complex} (hz : 0 < z.im)
  proof: ofComplex_apply ⟨z, hz⟩

中文:
引理 ofComplex_apply_of_im_pos
  条件: {z : Complex} (hz : 0 < z.im)
  证明: ofComplex_apply ⟨z, hz⟩

Depends on / 依赖: ofComplex_apply
-/
lemma ofComplex_apply_of_im_pos {z : Complex} (hz : 0 < z.im) :
    ofComplex z = ⟨z, hz⟩ :=
  ofComplex_apply ⟨z, hz⟩

/--
lemma `ofComplex_apply_of_im_nonpos` / 引理 `ofComplex_apply_of_im_nonpos`

English:
lemma ofComplex_apply_of_im_nonpos
  given: {w : Complex} (hw : w.im <= 0)
  proof: by
  simp [ofComplex_apply_eq_ite w, hw]

中文:
引理 ofComplex_apply_of_im_nonpos
  条件: {w : Complex} (hw : w.im <= 0)
  证明: by
  simp [ofComplex_apply_eq_ite w, hw]

Depends on / 依赖: ofComplex_apply_eq_ite
-/
lemma ofComplex_apply_of_im_nonpos {w : Complex} (hw : w.im <= 0) :
    ofComplex w = Classical.choice inferInstance := by
  simp [ofComplex_apply_eq_ite w, hw]

/--
lemma `ofComplex_apply_eq_of_im_nonpos` / 引理 `ofComplex_apply_eq_of_im_nonpos`

English:
lemma ofComplex_apply_eq_of_im_nonpos
  given: {w w' : Complex} (hw : w.im <= 0) (hw' : w'.im <= 0)
  proof: by
  simp [ofComplex_apply_of_im_nonpos, hw, hw']

中文:
引理 ofComplex_apply_eq_of_im_nonpos
  条件: {w w' : Complex} (hw : w.im <= 0) (hw' : w'.im <= 0)
  证明: by
  simp [ofComplex_apply_of_im_nonpos, hw, hw']

Depends on / 依赖: ofComplex_apply_of_im_nonpos
-/
lemma ofComplex_apply_eq_of_im_nonpos {w w' : Complex} (hw : w.im <= 0) (hw' : w'.im <= 0) :
    ofComplex w = ofComplex w' := by
  simp [ofComplex_apply_of_im_nonpos, hw, hw']

/--
lemma `comp_ofComplex` / 引理 `comp_ofComplex`

English:
lemma comp_ofComplex
  given: (f : ℍ -> Complex) (z : ℍ)
  statement: (↑ₕf) z = f z
  proof: congrArg _ ofComplex_apply z

中文:
引理 comp_ofComplex
  条件: (f : ℍ -> Complex) (z : ℍ)
  结论: (↑ₕf) z = f z
  证明: congrArg _ ofComplex_apply z

Depends on / 依赖: ofComplex_apply
-/
lemma comp_ofComplex (f : ℍ -> Complex) (z : ℍ) : (↑ₕf) z = f z :=
congrArg _ ofComplex_apply z

/--
lemma `comp_ofComplex_of_im_pos` / 引理 `comp_ofComplex_of_im_pos`

English:
lemma comp_ofComplex_of_im_pos
  given: (f : ℍ -> Complex) (z : Complex) (hz : 0 < z.im)
  statement: (↑ₕf) z = f ⟨z, hz⟩
  proof: congrArg _ ofComplex_apply ⟨z, hz⟩

中文:
引理 comp_ofComplex_of_im_pos
  条件: (f : ℍ -> Complex) (z : Complex) (hz : 0 < z.im)
  结论: (↑ₕf) z = f ⟨z, hz⟩
  证明: congrArg _ ofComplex_apply ⟨z, hz⟩

Depends on / 依赖: ofComplex_apply
-/
lemma comp_ofComplex_of_im_pos (f : ℍ -> Complex) (z : Complex) (hz : 0 < z.im) : (↑ₕf) z = f ⟨z, hz⟩ :=
congrArg _ ofComplex_apply ⟨z, hz⟩

/--
lemma `comp_ofComplex_of_im_le_zero` / 引理 `comp_ofComplex_of_im_le_zero`

English:
lemma comp_ofComplex_of_im_le_zero
  given: (f : ℍ -> Complex) (z z' : Complex) (hz : z.im <= 0) (hz' : z'.im <= 0)
  proof: by
  simp [ofComplex_apply_of_im_nonpos, hz, hz']

中文:
引理 comp_ofComplex_of_im_le_zero
  条件: (f : ℍ -> Complex) (z z' : Complex) (hz : z.im <= 0) (hz' : z'.im <= 0)
  证明: by
  simp [ofComplex_apply_of_im_nonpos, hz, hz']

Depends on / 依赖: ofComplex_apply_of_im_nonpos
-/
lemma comp_ofComplex_of_im_le_zero (f : ℍ -> Complex) (z z' : Complex) (hz : z.im <= 0) (hz' : z'.im <= 0) :
    (↑ₕf) z = (↑ₕf) z' := by
  simp [ofComplex_apply_of_im_nonpos, hz, hz']

/--
lemma `eventuallyEq_coe_comp_ofComplex` / 引理 `eventuallyEq_coe_comp_ofComplex`

English:
lemma eventuallyEq_coe_comp_ofComplex
  given: {z : Complex} (hz : 0 < z.im)
  proof: by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with x hx
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hx, id_eq]

@[fun_prop]

中文:
引理 eventuallyEq_coe_comp_ofComplex
  条件: {z : Complex} (hz : 0 < z.im)
  证明: by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with x hx
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hx, id_eq]

@[fun_prop]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, filter_upwards, id_eq, isOpen_upperHalfPlaneSet, isOpen_upperHalfPlaneSet.mem_nhds, mem_nhds, ofComplex_apply_of_im_pos
-/
lemma eventuallyEq_coe_comp_ofComplex {z : Complex} (hz : 0 < z.im) :
    UpperHalfPlane.coe ∘ ofComplex =ᶠ[𝓝 z] id := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with x hx
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hx, id_eq]

@[fun_prop]
/--
lemma `continuousOn_ofComplex_I_mul` / 引理 `continuousOn_ofComplex_I_mul`

English:
lemma continuousOn_ofComplex_I_mul
  proof: by
  simp only [ofComplex_apply_eq_ite, continuousOn_iff_continuous_domRestrict,
    continuous_induced_rng]
  have : Continuous (fun t : Real => Complex.I * t) := by fun_prop
  exact (this.comp continuous_subtype_val).congr (by simp +contextual)

中文:
引理 continuousOn_ofComplex_I_mul
  证明: by
  simp only [ofComplex_apply_eq_ite, continuousOn_iff_continuous_domRestrict,
    continuous_induced_rng]
  have : Continuous (fun t : Real => Complex.I * t) := by fun_prop
  exact (this.comp continuous_subtype_val).congr (by simp +contextual)

Depends on / 依赖: Complex.I, Continuous, contextual, continuousOn_iff_continuous_domRestrict, continuous_induced_rng, continuous_subtype_val, fun_prop, ofComplex_apply_eq_ite, this.comp
-/
lemma continuousOn_ofComplex_I_mul :
    ContinuousOn (fun t : Real => ofComplex (I * t)) (Set.Ioi 0) := by
  simp only [ofComplex_apply_eq_ite, continuousOn_iff_continuous_domRestrict,
    continuous_induced_rng]
  have : Continuous (fun t : Real => Complex.I * t) := by fun_prop
  exact (this.comp continuous_subtype_val).congr (by simp +contextual)

/--
lemma `J_smul` / 引理 `J_smul`

English:
lemma J_smul
  given: (τ : ℍ)
  statement: J • τ = ofComplex (-(conj ↑τ))
  proof: by
  ext
  rw [coe_J_smul]; rw [ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]

中文:
引理 J_smul
  条件: (τ : ℍ)
  结论: J • τ = ofComplex (-(conj ↑τ))
  证明: by
  ext
  rw [coe_J_smul]; rw [ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]

Depends on / 依赖: coe_J_smul, im_pos, ofComplex_apply_of_im_pos
-/
lemma J_smul (τ : ℍ) : J • τ = ofComplex (-(conj ↑τ)) := by
  ext
  rw [coe_J_smul]; rw [ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]

end ofComplex

section IsOpenMap

/--
lemma `isOpenMap_re` / 引理 `isOpenMap_re`

English:
lemma isOpenMap_re
  statement: IsOpenMap re
  proof: Complex.isOpenMap_re.comp isOpenEmbedding_coe.isOpenMap

中文:
引理 isOpenMap_re
  结论: IsOpenMap re
  证明: Complex.isOpenMap_re.comp isOpenEmbedding_coe.isOpenMap

Depends on / 依赖: Complex.isOpenMap_re.comp, isOpenEmbedding_coe, isOpenEmbedding_coe.isOpenMap, isOpenMap, isOpenMap_re
-/
lemma isOpenMap_re : IsOpenMap re :=
  Complex.isOpenMap_re.comp isOpenEmbedding_coe.isOpenMap

/--
lemma `isOpenMap_im` / 引理 `isOpenMap_im`

English:
lemma isOpenMap_im
  statement: IsOpenMap im
  proof: Complex.isOpenMap_im.comp isOpenEmbedding_coe.isOpenMap

中文:
引理 isOpenMap_im
  结论: IsOpenMap im
  证明: Complex.isOpenMap_im.comp isOpenEmbedding_coe.isOpenMap

Depends on / 依赖: Complex.isOpenMap_im.comp, isOpenEmbedding_coe, isOpenEmbedding_coe.isOpenMap, isOpenMap, isOpenMap_im
-/
lemma isOpenMap_im : IsOpenMap im :=
  Complex.isOpenMap_im.comp isOpenEmbedding_coe.isOpenMap

/--
lemma `isOpenMap_norm` / 引理 `isOpenMap_norm`

English:
lemma isOpenMap_norm
  statement: IsOpenMap (fun τ : ℍ => ‖(τ : Complex)‖)
  proof: by
  refine .of_nhds_le fun τ U hU => ?_
  obtain ⟨s, hs, hs'⟩ := Filter.mem_map_iff_exists_image.mp hU
  simp_rw [← isOpenEmbedding_coe.image_mem_nhds, Metric.mem_nhds_iff] at hs ⊢
  obtain ⟨ε, hεpos, hεs⟩ := hs
  refine ⟨ε, hεpos, subset_trans (fun r hr => ?_) hs'⟩
  have hr' : 0 <= r := by
    by

中文:
引理 isOpenMap_norm
  结论: IsOpenMap (fun τ : ℍ => ‖(τ : Complex)‖)
  证明: by
  refine .of_nhds_le fun τ U hU => ?_
  obtain ⟨s, hs, hs'⟩ := Filter.mem_map_iff_exists_image.mp hU
  simp_rw [← isOpenEmbedding_coe.image_mem_nhds, Metric.mem_nhds_iff] at hs ⊢
  obtain ⟨ε, hεpos, hεs⟩ := hs
  refine ⟨ε, hεpos, subset_trans (fun r hr => ?_) hs'⟩
  have hr' : 0 <= r := by
    by

Depends on / 依赖: Filter, Filter.mem_map_iff_exists_image.mp, Metric, Metric.ball, Metric.mem_nhds_iff, Real.norm_eq_abs, UpperHal, abs_lt, image_mem_nhds, isOpenEmbedding_coe, isOpenEmbedding_coe.image_mem_nhds, mem_ball_iff_norm, mem_map_iff_exists_image, mem_nhds_iff, norm_eq_abs, of_nhds_le, simp_rw, sub_zero, subset_trans
-/
lemma isOpenMap_norm : IsOpenMap (fun τ : ℍ => ‖(τ : Complex)‖) := by
  refine .of_nhds_le fun τ U hU => ?_
  obtain ⟨s, hs, hs'⟩ := Filter.mem_map_iff_exists_image.mp hU
  simp_rw [← isOpenEmbedding_coe.image_mem_nhds, Metric.mem_nhds_iff] at hs ⊢
  obtain ⟨ε, hεpos, hεs⟩ := hs
  refine ⟨ε, hεpos, subset_trans (fun r hr => ?_) hs'⟩
  have hr' : 0 <= r := by
    by_contra! hr'
    rw [mem_ball_iff_norm]; rw [Real.norm_eq_abs]; rw [abs_lt] at hr
    have : ‖(τ : Complex)‖ < ε := by linarith
    have : 0 in Metric.ball (τ : Complex) ε := by rwa [mem_ball_iff_norm', sub_zero]
    simpa [UpperHalfPlane.ne_zero] using hεs this
  have : r / ‖(τ : Complex)‖ * (τ : Complex) in Metric.ball (τ : Complex) ε := by
    rwa [mem_ball_iff_norm,
      show r / ‖(τ : Complex)‖ * (τ : Complex) - τ = ↑(r / ‖(τ : Complex)‖ - 1) * (τ : Complex) by simp; ring,
      norm_mul, norm_real, ← norm_norm (τ : Complex), ← norm_mul, sub_mul, norm_norm, one_mul,
      div_mul_cancel₀ _ (by simpa using τ.ne_zero), ← mem_ball_iff_norm]
  obtain ⟨ξ, hξs, hξτ⟩ := Set.mem_of_mem_of_subset this hεs
  use ξ, hξs
  simp_rw [hξτ, norm_mul, norm_div, norm_real, norm_norm]
  rw [div_mul_cancel₀ _ (by simpa using τ.ne_zero)]; rw [Real.norm_of_nonneg hr']

end IsOpenMap

end UpperHalfPlane
