/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive

/-!

# Inner product space structure on tensor product spaces

This file provides the inner product space structure on tensor product spaces.

We define the inner product on `E ⊗ F` by `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`, when `E` and `F` are
inner product spaces.

## Main definitions:

* `TensorProduct.instNormedAddCommGroup`: the normed additive group structure on tensor products,
  where `‖x ⊗ₜ y‖ = ‖x‖ * ‖y‖`.
* `TensorProduct.instInnerProductSpace`: the inner product space structure on tensor products, where
  `⟪a ⊗ₜ b, c ⊗ₜ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`.
* `TensorProduct.mapIsometry`: the linear isometry version of `TensorProduct.map f g` when
  `f` and `g` are linear isometries.
* `TensorProduct.congrIsometry`: the linear isometry equivalence version of
  `TensorProduct.congr f g` when `f` and `g` are linear isometry equivalences.
* `TensorProduct.mapInclIsometry`: the linear isometry version of `TensorProduct.mapIncl`.
* `TensorProduct.commIsometry`: the linear isometry version of `TensorProduct.comm`.
* `TensorProduct.lidIsometry`: the linear isometry version of `TensorProduct.lid`.
* `TensorProduct.assocIsometry`: the linear isometry version of `TensorProduct.assoc`.
* `TensorProduct.mapL`: the continuous version of `TensorProduct.map f g` when
  `f` and `g` are continuous linear maps.
* `OrthonormalBasis.tensorProduct`: the orthonormal basis of the tensor product of two orthonormal
  bases.

## TODO:

* Define the normed space without needing inner products, this should be analogous to
  `Mathlib/Analysis/NormedSpace/PiTensorProduct/InjectiveSeminorm.lean`.

-/

@[expose] public section

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

open scoped TensorProduct

namespace TensorProduct

/--
Instance `instInner` / 实例 `instInner`

English:
instance instInner
  signature: : Inner 𝕜 (E otimes[𝕜] F) where inner x y
  body: ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂ (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y

中文:
实例 instInner
  签名: : Inner 𝕜 (E otimes[𝕜] F) where inner x y
  定义体: ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂ (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y

Depends on / 依赖: mapBilinear
-/
instance instInner : Inner 𝕜 (E otimes[𝕜] F) where inner x y :=
  ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂ (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y

/--
lemma `inner_def` / 引理 `inner_def`

English:
lemma inner_def
  given: (x y : E otimes[𝕜] F)
  proof: rfl

中文:
引理 inner_def
  条件: (x y : E otimes[𝕜] F)
  证明: rfl

Depends on / 依赖: toContinuousSemilinearMapClass
-/
lemma inner_def (x y : E otimes[𝕜] F) :
    inner 𝕜 x y = ((lift <| mapBilinear (.id 𝕜) E F 𝕜 𝕜).compr₂
      (.mul' 𝕜 𝕜) ∘ₛₗ map (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x y := rfl

variable (𝕜) in
/--
theorem `inner_tmul` / 定理 `inner_tmul`

English:
theorem inner_tmul
  given: (x x' : E) (y y' : F)
  proof: rfl

中文:
定理 inner_tmul
  条件: (x x' : E) (y y' : F)
  证明: rfl

Depends on / 依赖: SemilinearIsometryClass, toIsometryClass
-/
@[simp] theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x otimesₜ[𝕜] y) (x' otimesₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl

/--
lemma `inner_map_map` / 引理 `inner_map_map`

English:
lemma inner_map_map
  given: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x y : E otimes[𝕜] F)
  proof: x.induction_on (by simp [inner_def]) (y.induction_on (by simp [inner_def]) (by simp)
    (by simp_all [inner_def])) (by simp_all [inner_def])

中文:
引理 inner_map_map
  条件: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x y : E otimes[𝕜] F)
  证明: x.induction_on (by simp [inner_def]) (y.induction_on (by simp [inner_def]) (by simp)
    (by simp_all [inner_def])) (by simp_all [inner_def])
-/
@[simp] lemma inner_map_map (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x y : E otimes[𝕜] F) :
    inner 𝕜 (map f.toLinearMap g.toLinearMap x) (map f.toLinearMap g.toLinearMap y) = inner 𝕜 x y :=
  x.induction_on (by simp [inner_def]) (y.induction_on (by simp [inner_def]) (by simp)
    (by simp_all [inner_def])) (by simp_all [inner_def])

/--
lemma `inner_mapIncl_mapIncl` / 引理 `inner_mapIncl_mapIncl`

English:
lemma inner_mapIncl_mapIncl
  given: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' otimes[𝕜] F')
  proof: inner_map_map E'.subtypeₗᵢ F'.subtypeₗᵢ x y

中文:
引理 inner_mapIncl_mapIncl
  条件: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' otimes[𝕜] F')
  证明: inner_map_map E'.subtypeₗᵢ F'.subtypeₗᵢ x y

Depends on / 依赖: inner_map_map
-/
lemma inner_mapIncl_mapIncl (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) (x y : E' otimes[𝕜] F') :
    inner 𝕜 (mapIncl E' F' x) (mapIncl E' F' y) = inner 𝕜 x y :=
  inner_map_map E'.subtypeₗᵢ F'.subtypeₗᵢ x y

open scoped ComplexOrder
open Module

/--
theorem `inner_self` / 定理 `inner_self`

English:
theorem inner_self
  statement: {ι ι' : Type*} [Fintype ι] [Fintype ι'] (x : E otimes[𝕜] F)
  proof: by
  classical
  have : x = ∑ i : ι, ∑ j : ι', (e.toBasis.tensorProduct f.toBasis).repr x (i, j) • e i otimesₜ f j := by
    conv_lhs => rw [← (e.toBasis.tensorProduct f.toBasis).sum_repr x]
    simp [← Finset.sum_product', Basis.tensorProduct_apply']
  conv_lhs => rw [this]
  simp only [inner_def, 

中文:
定理 inner_self
  结论: {ι ι' : 类型} [Fintype ι] [Fintype ι'] (x : E otimes[𝕜] F)
  证明: by
  classical
  have : x = ∑ i : ι, ∑ j : ι', (e.toBasis.tensorProduct f.toBasis).repr x (i, j) • e i otimesₜ f j := by
    conv_lhs => rw [← (e.toBasis.tensorProduct f.toBasis).sum_repr x]
    simp [← Finset.sum_product', Basis.tensorProduct_apply']
  conv_lhs => rw [this]
  simp only [inner_def, 
-/
private theorem inner_self {ι ι' : Type*} [Fintype ι] [Fintype ι'] (x : E otimes[𝕜] F)
    (e : OrthonormalBasis ι 𝕜 E) (f : OrthonormalBasis ι' 𝕜 F) :
    inner 𝕜 x x = ∑ i, ‖(e.toBasis.tensorProduct f.toBasis).repr x i‖ ^ 2 := by
  classical
  have : x = ∑ i : ι, ∑ j : ι', (e.toBasis.tensorProduct f.toBasis).repr x (i, j) • e i otimesₜ f j := by
    conv_lhs => rw [← (e.toBasis.tensorProduct f.toBasis).sum_repr x]
    simp [← Finset.sum_product', Basis.tensorProduct_apply']
  conv_lhs => rw [this]
  simp only [inner_def, map_sum, LinearMap.sum_apply]
  simp [OrthonormalBasis.inner_eq_ite, ← Finset.sum_product', RCLike.mul_conj]

set_option backward.privateInPublic true in
/--
theorem `inner_definite` / 定理 `inner_definite`

English:
theorem inner_definite
  given: (x : E otimes[𝕜] F) (hx : inner 𝕜 x x = 0)
  statement: x = 0
  proof: by
  /-
  The way we prove this is by noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl

中文:
定理 inner_definite
  条件: (x : E otimes[𝕜] F) (hx : inner 𝕜 x x = 0)
  结论: x = 0
  证明: by
  /-
  The way we prove this is by noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl
-/
private theorem inner_definite (x : E otimes[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := by
  /-
  The way we prove this is by noting that every element of a tensor product lies
  in the tensor product of some finite submodules.
  So for `x : E ⊗ F`, there exists finite submodules `E', F'` such that `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y : E' otimes F', rfl : mapIncl E' F' y = x⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  have (i) (j) : (e.toBasis.tensorProduct f.toBasis).repr y (i, j) = 0 := by
    rw [inner_mapIncl_mapIncl]; rw [inner_self y e f]; rw [RCLike.ofReal_eq_zero]; rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hx
    simpa using hx (i, j)
  have : y = 0 := by simp [(e.toBasis.tensorProduct f.toBasis).ext_elem_iff, this]
  rw [this]; rw [map_zero]

set_option backward.privateInPublic true in
/--
theorem `protected` / 定理 `protected`

English:
theorem protected
  given: theorem re_inner_self_nonneg (x : E otimes[𝕜] F)
  proof: by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinit

中文:
定理 protected
  条件: theorem re_inner_self_nonneg (x : E otimes[𝕜] F)
  证明: by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinit
-/
private protected theorem re_inner_self_nonneg (x : E otimes[𝕜] F) :
    0 <= RCLike.re (inner 𝕜 x x) := by
  /-
  Similarly to the above proof, for `x : E ⊗ F`, there exists finite submodules `E', F'` such that
  `x ∈ mapIncl E' F'`.
  And so the rest then follows from the above lemmas `inner_mapIncl_mapIncl` and `inner_self`.
  -/
  obtain ⟨E', F', iE', iF', hz⟩ := exists_finite_submodule_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hz
  obtain e := stdOrthonormalBasis 𝕜 E'
  obtain f := stdOrthonormalBasis 𝕜 F'
  rw [inner_mapIncl_mapIncl]; rw [inner_self y e f]; rw [RCLike.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: : NormedAddCommGroup (E otimes[𝕜] F)
  body: letI : InnerProductSpace.Core 𝕜 (E otimes[𝕜] F) :=
  { conj_inner_symm x y :=
      x.induction_on (by simp [inner]) (y.induction_on (by simp [inner]) (by simp)
        (by simp_all [inner])) (by simp_all [inner])
    add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
    smul_left _ _ _ := LinearMap.map_

中文:
实例 instNormedAddCommGroup
  签名: : NormedAddCommGroup (E otimes[𝕜] F)
  定义体: letI : InnerProductSpace.Core 𝕜 (E otimes[𝕜] F) :=
  { conj_inner_symm x y :=
      x.induction_on (by simp [inner]) (y.induction_on (by simp [inner]) (by simp)
        (by simp_all [inner])) (by simp_all [inner])
    add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
    smul_left _ _ _ := LinearMap.map_

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core, LinearMap, LinearMap.map_add, LinearMap.map_smul, TensorProduct, TensorProduct.inner_definite, TensorProduct.re_inner_self_nonneg, add_left, conj_inner_symm, definite, induction_on, inner_definite, otimes, re_inner_nonneg, re_inner_self_nonneg, smul_left, this.toNormedAddCommGroup, toNormedAddCommGroup, x.induction_on
-/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (E otimes[𝕜] F) :=
  letI : InnerProductSpace.Core 𝕜 (E otimes[𝕜] F) :=
  { conj_inner_symm x y :=
      x.induction_on (by simp [inner]) (y.induction_on (by simp [inner]) (by simp)
        (by simp_all [inner])) (by simp_all [inner])
    add_left _ _ _ := LinearMap.map_add₂ _ _ _ _
    smul_left _ _ _ := LinearMap.map_smulₛₗ₂ _ _ _ _
    definite := TensorProduct.inner_definite
    re_inner_nonneg := TensorProduct.re_inner_self_nonneg }
  this.toNormedAddCommGroup

/--
Instance `instInnerProductSpace` / 实例 `instInnerProductSpace`

English:
instance instInnerProductSpace
  signature: : InnerProductSpace 𝕜 (E otimes[𝕜] F)
  body: .ofCore _

中文:
实例 instInnerProductSpace
  签名: : InnerProductSpace 𝕜 (E otimes[𝕜] F)
  定义体: .ofCore _

Depends on / 依赖: ofCore
-/
instance instInnerProductSpace : InnerProductSpace 𝕜 (E otimes[𝕜] F) := .ofCore _

/--
theorem `norm_tmul` / 定理 `norm_tmul`

English:
theorem norm_tmul
  given: (x : E) (y : F)
  proof: by
  simpa using congr(√(RCLike.re $(inner_tmul 𝕜 x x y y)))

中文:
定理 norm_tmul
  条件: (x : E) (y : F)
  证明: by
  simpa using congr(√(RCLike.re $(inner_tmul 𝕜 x x y y)))
-/
@[simp] theorem norm_tmul (x : E) (y : F) :
    ‖x otimesₜ[𝕜] y‖ = ‖x‖ * ‖y‖ := by
  simpa using congr(√(RCLike.re $(inner_tmul 𝕜 x x y y)))

/--
theorem `nnnorm_tmul` / 定理 `nnnorm_tmul`

English:
theorem nnnorm_tmul
  given: (x : E) (y : F)
  proof: by simp [← NNReal.coe_inj]

中文:
定理 nnnorm_tmul
  条件: (x : E) (y : F)
  证明: by simp [← NNReal.coe_inj]
-/
@[simp] theorem nnnorm_tmul (x : E) (y : F) :
    ‖x otimesₜ[𝕜] y‖₊ = ‖x‖₊ * ‖y‖₊ := by simp [← NNReal.coe_inj]

/--
theorem `enorm_tmul` / 定理 `enorm_tmul`

English:
theorem enorm_tmul
  given: (x : E) (y : F)
  proof: ENNReal.coe_inj.mpr by simp

中文:
定理 enorm_tmul
  条件: (x : E) (y : F)
  证明: ENNReal.coe_inj.mpr by simp
-/
@[simp] theorem enorm_tmul (x : E) (y : F) :
‖x otimesₜ[𝕜] y‖ₑ = ‖x‖ₑ * ‖y‖ₑ := ENNReal.coe_inj.mpr by simp

/--
theorem `dist_tmul_le` / 定理 `dist_tmul_le`

English:
theorem dist_tmul_le
  given: (x x' : E) (y y' : F)
  proof: by
  grw [dist_eq_norm, norm_sub_le]; simp

中文:
定理 dist_tmul_le
  条件: (x x' : E) (y y' : F)
  证明: by
  grw [dist_eq_norm, norm_sub_le]; simp

Depends on / 依赖: dist_eq_norm, norm_sub_le
-/
theorem dist_tmul_le (x x' : E) (y y' : F) :
    dist (x otimesₜ[𝕜] y) (x' otimesₜ y') <= ‖x‖ * ‖y‖ + ‖x'‖ * ‖y'‖ := by
  grw [dist_eq_norm, norm_sub_le]; simp

/--
theorem `nndist_tmul_le` / 定理 `nndist_tmul_le`

English:
theorem nndist_tmul_le
  given: (x x' : E) (y y' : F)
  proof: by
  grw [nndist_eq_nnnorm, nnnorm_sub_le]; simp

中文:
定理 nndist_tmul_le
  条件: (x x' : E) (y y' : F)
  证明: by
  grw [nndist_eq_nnnorm, nnnorm_sub_le]; simp

Depends on / 依赖: nndist_eq_nnnorm, nnnorm_sub_le
-/
theorem nndist_tmul_le (x x' : E) (y y' : F) :
    nndist (x otimesₜ[𝕜] y) (x' otimesₜ y') <= ‖x‖₊ * ‖y‖₊ + ‖x'‖₊ * ‖y'‖₊ := by
  grw [nndist_eq_nnnorm, nnnorm_sub_le]; simp

/--
theorem `edist_tmul_le` / 定理 `edist_tmul_le`

English:
theorem edist_tmul_le
  given: (x x' : E) (y y' : F)
  proof: by
  grw [edist_eq_enorm_sub, enorm_sub_le]; simp

中文:
定理 edist_tmul_le
  条件: (x x' : E) (y y' : F)
  证明: by
  grw [edist_eq_enorm_sub, enorm_sub_le]; simp

Depends on / 依赖: edist_eq_enorm_sub, enorm_sub_le
-/
theorem edist_tmul_le (x x' : E) (y y' : F) :
    edist (x otimesₜ[𝕜] y) (x' otimesₜ y') <= ‖x‖ₑ * ‖y‖ₑ + ‖x'‖ₑ * ‖y'‖ₑ := by
  grw [edist_eq_enorm_sub, enorm_sub_le]; simp

/--
theorem `_root_.RCLike.inner_tmul_eq` / 定理 `_root_.RCLike.inner_tmul_eq`

English:
theorem _root_.RCLike.inner_tmul_eq
  given: (a b c d : 𝕜)
  proof: by
  simp; ring

中文:
定理 _root_.RCLike.inner_tmul_eq
  条件: (a b c d : 𝕜)
  证明: by
  simp; ring
-/
theorem _root_.RCLike.inner_tmul_eq (a b c d : 𝕜) :
    inner 𝕜 (a otimesₜ[𝕜] b) (c otimesₜ[𝕜] d) = inner 𝕜 (a * b) (c * d) := by
  simp; ring

/--
theorem `ext_iff_inner_right` / 定理 `ext_iff_inner_right`

English:
theorem ext_iff_inner_right
  given: {x y : E otimes[𝕜] F}
  proof: ⟨fun h _ _ => h ▸ rfl, fun h => innerSL_inj.mp ContinuousLinearMap.coe_inj.mp ext' h⟩

中文:
定理 ext_iff_inner_right
  条件: {x y : E otimes[𝕜] F}
  证明: ⟨fun h _ _ => h ▸ rfl, fun h => innerSL_inj.mp ContinuousLinearMap.coe_inj.mp ext' h⟩
-/
protected theorem ext_iff_inner_right {x y : E otimes[𝕜] F} :
    x = y ↔ forall a b, inner 𝕜 x (a otimesₜ[𝕜] b) = inner 𝕜 y (a otimesₜ[𝕜] b) :=
⟨fun h _ _ => h ▸ rfl, fun h => innerSL_inj.mp ContinuousLinearMap.coe_inj.mp ext' h⟩

/--
theorem `ext_iff_inner_left` / 定理 `ext_iff_inner_left`

English:
theorem ext_iff_inner_left
  given: {x y : E otimes[𝕜] F}
  proof: by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    TensorProduct.ext_iff_inner_right (x := x) (y := y)

中文:
定理 ext_iff_inner_left
  条件: {x y : E otimes[𝕜] F}
  证明: by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    TensorProduct.ext_iff_inner_right (x := x) (y := y)
-/
protected theorem ext_iff_inner_left {x y : E otimes[𝕜] F} :
    x = y ↔ forall a b, inner 𝕜 (a otimesₜ b) x = inner 𝕜 (a otimesₜ b) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    TensorProduct.ext_iff_inner_right (x := x) (y := y)

/--
theorem `ext_iff_inner_right_threefold` / 定理 `ext_iff_inner_right_threefold`

English:
theorem ext_iff_inner_right_threefold
  given: {x y : E otimes[𝕜] F otimes[𝕜] G}
  proof: ⟨fun h _ _ _ => h ▸ rfl, fun h => innerSL_inj.mp (ContinuousLinearMap.coe_inj.mp (ext_threefold h))⟩

中文:
定理 ext_iff_inner_right_threefold
  条件: {x y : E otimes[𝕜] F otimes[𝕜] G}
  证明: ⟨fun h _ _ _ => h ▸ rfl, fun h => innerSL_inj.mp (ContinuousLinearMap.coe_inj.mp (ext_threefold h))⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_inj.mp, coe_inj, ext_threefold, innerSL_inj, innerSL_inj.mp
-/
theorem ext_iff_inner_right_threefold {x y : E otimes[𝕜] F otimes[𝕜] G} :
    x = y ↔ forall a b c, inner 𝕜 x (a otimesₜ[𝕜] b otimesₜ[𝕜] c) = inner 𝕜 y (a otimesₜ[𝕜] b otimesₜ[𝕜] c) :=
  ⟨fun h _ _ _ => h ▸ rfl, fun h => innerSL_inj.mp (ContinuousLinearMap.coe_inj.mp (ext_threefold h))⟩

/--
theorem `ext_iff_inner_left_threefold` / 定理 `ext_iff_inner_left_threefold`

English:
theorem ext_iff_inner_left_threefold
  given: {x y : E otimes[𝕜] F otimes[𝕜] G}
  proof: by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold (x := x) (y := y)

中文:
定理 ext_iff_inner_left_threefold
  条件: {x y : E otimes[𝕜] F otimes[𝕜] G}
  证明: by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold (x := x) (y := y)

Depends on / 依赖: ext_iff_inner_right_threefold, inner_conj_symm, starRingEnd_apply, star_inj
-/
theorem ext_iff_inner_left_threefold {x y : E otimes[𝕜] F otimes[𝕜] G} :
    x = y ↔ forall a b c, inner 𝕜 (a otimesₜ b otimesₜ c) x = inner 𝕜 (a otimesₜ b otimesₜ c) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold (x := x) (y := y)

variable (𝕜 E F) in
/--
Definition of `mkL` / `mkL` 的定义

English:
definition mkL
  signature: : E ->L[𝕜] F ->L[𝕜] E otimes[𝕜] F
  body: (mk 𝕜 E F).mkContinuous₂ 1 fun _ _ => by simp

中文:
定义 mkL
  签名: : E ->L[𝕜] F ->L[𝕜] E otimes[𝕜] F
  定义体: (mk 𝕜 E F).mkContinuous₂ 1 fun _ _ => by simp
-/
noncomputable def mkL : E ->L[𝕜] F ->L[𝕜] E otimes[𝕜] F := (mk 𝕜 E F).mkContinuous₂ 1 fun _ _ => by simp

/--
lemma `coe_mkL_apply` / 引理 `coe_mkL_apply`

English:
lemma coe_mkL_apply
  given: (x : E)
  statement: ⇑(mkL 𝕜 E F x) = mk 𝕜 E F x
  proof: rfl

中文:
引理 coe_mkL_apply
  条件: (x : E)
  结论: ⇑(mkL 𝕜 E F x) = mk 𝕜 E F x
  证明: rfl
-/
@[simp] lemma coe_mkL_apply (x : E) : ⇑(mkL 𝕜 E F x) = mk 𝕜 E F x := rfl
/--
lemma `toLinearMap₁₂_mkL` / 引理 `toLinearMap₁₂_mkL`

English:
lemma toLinearMap₁₂_mkL
  statement: (mkL 𝕜 E F).toLinearMap₁₂ = mk 𝕜 E F
  proof: rfl

中文:
引理 toLinearMap₁₂_mkL
  结论: (mkL 𝕜 E F).toLinearMap₁₂ = mk 𝕜 E F
  证明: rfl
-/
@[simp] lemma toLinearMap₁₂_mkL : (mkL 𝕜 E F).toLinearMap₁₂ = mk 𝕜 E F := rfl
/--
lemma `toLinearMap_mkL_apply` / 引理 `toLinearMap_mkL_apply`

English:
lemma toLinearMap_mkL_apply
  given: (x : E)
  statement: (mkL 𝕜 E F x).toLinearMap = mk 𝕜 E F x
  proof: rfl

中文:
引理 toLinearMap_mkL_apply
  条件: (x : E)
  结论: (mkL 𝕜 E F x).toLinearMap = mk 𝕜 E F x
  证明: rfl
-/
@[simp] lemma toLinearMap_mkL_apply (x : E) : (mkL 𝕜 E F x).toLinearMap = mk 𝕜 E F x := rfl
/--
lemma `mkL_apply_apply` / 引理 `mkL_apply_apply`

English:
lemma mkL_apply_apply
  given: (x : E) (y : F)
  statement: mkL 𝕜 E F x y = x otimesₜ y
  proof: rfl

中文:
引理 mkL_apply_apply
  条件: (x : E) (y : F)
  结论: mkL 𝕜 E F x y = x otimesₜ y
  证明: rfl
-/
lemma mkL_apply_apply (x : E) (y : F) : mkL 𝕜 E F x y = x otimesₜ y := rfl

/--
lemma `continuous_tmul` / 引理 `continuous_tmul`

English:
lemma continuous_tmul
  statement: Continuous fun x : E × F => x.1 otimesₜ[𝕜] x.2
  proof: (mkL 𝕜 E F).continuous₂

中文:
引理 continuous_tmul
  结论: Continuous fun x : E × F => x.1 otimesₜ[𝕜] x.2
  证明: (mkL 𝕜 E F).continuous₂
-/
@[fun_prop] lemma continuous_tmul : Continuous fun x : E × F => x.1 otimesₜ[𝕜] x.2 :=
  (mkL 𝕜 E F).continuous₂

section isometry

/--
Definition of `mapIsometry` / `mapIsometry` 的定义

English:
definition mapIsometry
  signature: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H)
  body: .isometryOfInner inner_map_map _ _ map f.toLinearMap g.toLinearMap

中文:
定义 mapIsometry
  签名: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H)
  定义体: .isometryOfInner inner_map_map _ _ map f.toLinearMap g.toLinearMap

Depends on / 依赖: f.toLinearMap, g.toLinearMap, inner_map_map, isometryOfInner, toLinearMap
-/
noncomputable def mapIsometry (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) :
    E otimes[𝕜] F ->ₗᵢ[𝕜] G otimes[𝕜] H :=
.isometryOfInner inner_map_map _ _ map f.toLinearMap g.toLinearMap

/--
lemma `mapIsometry_apply` / 引理 `mapIsometry_apply`

English:
lemma mapIsometry_apply
  given: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  proof: rfl

中文:
引理 mapIsometry_apply
  条件: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  证明: rfl
-/
@[simp] lemma mapIsometry_apply (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F) :
    mapIsometry f g x = map f.toLinearMap g.toLinearMap x := rfl

/--
lemma `toLinearMap_mapIsometry` / 引理 `toLinearMap_mapIsometry`

English:
lemma toLinearMap_mapIsometry
  given: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H)
  proof: rfl

中文:
引理 toLinearMap_mapIsometry
  条件: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H)
  证明: rfl
-/
@[simp] lemma toLinearMap_mapIsometry (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) :
    (mapIsometry f g).toLinearMap = map f.toLinearMap g.toLinearMap := rfl

/--
lemma `norm_map` / 引理 `norm_map`

English:
lemma norm_map
  given: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  proof: mapIsometry f g

中文:
引理 norm_map
  条件: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  证明: mapIsometry f g
-/
@[simp] lemma norm_map (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F) :
.norm_map x ‖map f.toLinearMap g.toLinearMap x‖ = ‖x‖ := mapIsometry f g
/--
lemma `nnnorm_map` / 引理 `nnnorm_map`

English:
lemma nnnorm_map
  given: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  proof: mapIsometry f g

中文:
引理 nnnorm_map
  条件: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  证明: mapIsometry f g
-/
@[simp] lemma nnnorm_map (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F) :
.nnnorm_map x ‖map f.toLinearMap g.toLinearMap x‖₊ = ‖x‖₊ := mapIsometry f g
/--
lemma `enorm_map` / 引理 `enorm_map`

English:
lemma enorm_map
  given: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  proof: mapIsometry f g

中文:
引理 enorm_map
  条件: (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  证明: mapIsometry f g
-/
@[simp] lemma enorm_map (f : E ->ₗᵢ[𝕜] G) (g : F ->ₗᵢ[𝕜] H) (x : E otimes[𝕜] F) :
.enorm_map x ‖map f.toLinearMap g.toLinearMap x‖ₑ = ‖x‖ₑ := mapIsometry f g

/--
lemma `mapIsometry_id_id` / 引理 `mapIsometry_id_id`

English:
lemma mapIsometry_id_id
  proof: by ext; simp

中文:
引理 mapIsometry_id_id
  证明: by ext; simp
-/
@[simp] lemma mapIsometry_id_id :
    mapIsometry (.id : E ->ₗᵢ[𝕜] E) (.id : F ->ₗᵢ[𝕜] F) = .id := by ext; simp

variable (E) in
/--
Definition of `_root_.LinearIsometry.lTensor` / `_root_.LinearIsometry.lTensor` 的定义

English:
definition _root_.LinearIsometry.lTensor
  signature: (f : F ->ₗᵢ[𝕜] G)
  body: mapIsometry .id f

中文:
定义 _root_.LinearIsometry.lTensor
  签名: (f : F ->ₗᵢ[𝕜] G)
  定义体: mapIsometry .id f

Depends on / 依赖: mapIsometry
-/
noncomputable def _root_.LinearIsometry.lTensor (f : F ->ₗᵢ[𝕜] G) :
    E otimes[𝕜] F ->ₗᵢ[𝕜] E otimes[𝕜] G := mapIsometry .id f

variable (G) in
/--
Definition of `_root_.LinearIsometry.rTensor` / `_root_.LinearIsometry.rTensor` 的定义

English:
definition _root_.LinearIsometry.rTensor
  signature: (f : E ->ₗᵢ[𝕜] F)
  body: mapIsometry f .id

中文:
定义 _root_.LinearIsometry.rTensor
  签名: (f : E ->ₗᵢ[𝕜] F)
  定义体: mapIsometry f .id

Depends on / 依赖: mapIsometry
-/
noncomputable def _root_.LinearIsometry.rTensor (f : E ->ₗᵢ[𝕜] F) :
    E otimes[𝕜] G ->ₗᵢ[𝕜] F otimes[𝕜] G := mapIsometry f .id

/--
lemma `_root_.LinearIsometry.lTensor_def` / 引理 `_root_.LinearIsometry.lTensor_def`

English:
lemma _root_.LinearIsometry.lTensor_def
  given: (f : F ->ₗᵢ[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometry.lTensor_def
  条件: (f : F ->ₗᵢ[𝕜] G)
  证明: rfl
-/
lemma _root_.LinearIsometry.lTensor_def (f : F ->ₗᵢ[𝕜] G) :
    f.lTensor E = mapIsometry .id f := rfl

/--
lemma `_root_.LinearIsometry.rTensor_def` / 引理 `_root_.LinearIsometry.rTensor_def`

English:
lemma _root_.LinearIsometry.rTensor_def
  given: (f : E ->ₗᵢ[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometry.rTensor_def
  条件: (f : E ->ₗᵢ[𝕜] F)
  证明: rfl
-/
lemma _root_.LinearIsometry.rTensor_def (f : E ->ₗᵢ[𝕜] F) :
    f.rTensor G = mapIsometry f .id := rfl

/--
lemma `_root_.LinearIsometry.toLinearMap_lTensor` / 引理 `_root_.LinearIsometry.toLinearMap_lTensor`

English:
lemma _root_.LinearIsometry.toLinearMap_lTensor
  given: (f : F ->ₗᵢ[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometry.toLinearMap_lTensor
  条件: (f : F ->ₗᵢ[𝕜] G)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometry.toLinearMap_lTensor (f : F ->ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearMap = f.toLinearMap.lTensor E := rfl

/--
lemma `_root_.LinearIsometry.toLinearMap_rTensor` / 引理 `_root_.LinearIsometry.toLinearMap_rTensor`

English:
lemma _root_.LinearIsometry.toLinearMap_rTensor
  given: (f : E ->ₗᵢ[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometry.toLinearMap_rTensor
  条件: (f : E ->ₗᵢ[𝕜] F)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometry.toLinearMap_rTensor (f : E ->ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearMap = f.toLinearMap.rTensor G := rfl

/--
lemma `_root_.LinearIsometry.lTensor_apply` / 引理 `_root_.LinearIsometry.lTensor_apply`

English:
lemma _root_.LinearIsometry.lTensor_apply
  given: (f : F ->ₗᵢ[𝕜] G) (x : E otimes[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometry.lTensor_apply
  条件: (f : F ->ₗᵢ[𝕜] G) (x : E otimes[𝕜] F)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometry.lTensor_apply (f : F ->ₗᵢ[𝕜] G) (x : E otimes[𝕜] F) :
    f.lTensor E x = f.toLinearMap.lTensor E x := rfl

/--
lemma `_root_.LinearIsometry.rTensor_apply` / 引理 `_root_.LinearIsometry.rTensor_apply`

English:
lemma _root_.LinearIsometry.rTensor_apply
  given: (f : E ->ₗᵢ[𝕜] F) (x : E otimes[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometry.rTensor_apply
  条件: (f : E ->ₗᵢ[𝕜] F) (x : E otimes[𝕜] G)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometry.rTensor_apply (f : E ->ₗᵢ[𝕜] F) (x : E otimes[𝕜] G) :
    f.rTensor G x = f.toLinearMap.rTensor G x := rfl

/--
Definition of `congrIsometry` / `congrIsometry` 的定义

English:
definition congrIsometry
  signature: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
  body: .isometryOfInner congr f.toLinearEquiv g.toLinearEquiv
    inner_map_map f.toLinearIsometry g.toLinearIsometry

中文:
定义 congrIsometry
  签名: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
  定义体: .isometryOfInner congr f.toLinearEquiv g.toLinearEquiv
    inner_map_map f.toLinearIsometry g.toLinearIsometry

Depends on / 依赖: f.toLinearEquiv, f.toLinearIsometry, g.toLinearEquiv, g.toLinearIsometry, inner_map_map, isometryOfInner, toLinearEquiv, toLinearIsometry
-/
noncomputable def congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    E otimes[𝕜] F ≃ₗᵢ[𝕜] G otimes[𝕜] H :=
.isometryOfInner congr f.toLinearEquiv g.toLinearEquiv
    inner_map_map f.toLinearIsometry g.toLinearIsometry

/--
lemma `congrIsometry_apply` / 引理 `congrIsometry_apply`

English:
lemma congrIsometry_apply
  given: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  proof: rfl

中文:
引理 congrIsometry_apply
  条件: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E otimes[𝕜] F)
  证明: rfl
-/
@[simp] lemma congrIsometry_apply (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) (x : E otimes[𝕜] F) :
    congrIsometry f g x = congr (σ₁₂ := .id _) f g x := rfl

/--
lemma `congrIsometry_symm` / 引理 `congrIsometry_symm`

English:
lemma congrIsometry_symm
  given: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
  proof: rfl

中文:
引理 congrIsometry_symm
  条件: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
  证明: rfl
-/
lemma congrIsometry_symm (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).symm = congrIsometry f.symm g.symm := rfl

/--
lemma `toLinearEquiv_congrIsometry` / 引理 `toLinearEquiv_congrIsometry`

English:
lemma toLinearEquiv_congrIsometry
  given: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
  proof: rfl

中文:
引理 toLinearEquiv_congrIsometry
  条件: (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H)
  证明: rfl
-/
@[simp] lemma toLinearEquiv_congrIsometry (f : E ≃ₗᵢ[𝕜] G) (g : F ≃ₗᵢ[𝕜] H) :
    (congrIsometry f g).toLinearEquiv = congr f.toLinearEquiv g.toLinearEquiv := rfl

/--
lemma `congrIsometry_refl_refl` / 引理 `congrIsometry_refl_refl`

English:
lemma congrIsometry_refl_refl
  proof: LinearIsometryEquiv.toLinearEquiv_inj.mp LinearEquiv.toLinearMap_inj.mp by ext; simp

中文:
引理 congrIsometry_refl_refl
  证明: LinearIsometryEquiv.toLinearEquiv_inj.mp LinearEquiv.toLinearMap_inj.mp by ext; simp
-/
@[simp] lemma congrIsometry_refl_refl :
    congrIsometry (.refl 𝕜 E) (.refl 𝕜 F) = .refl 𝕜 (E otimes F) :=
LinearIsometryEquiv.toLinearEquiv_inj.mp LinearEquiv.toLinearMap_inj.mp by ext; simp

variable (E) in
/--
Definition of `_root_.LinearIsometryEquiv.lTensor` / `_root_.LinearIsometryEquiv.lTensor` 的定义

English:
definition _root_.LinearIsometryEquiv.lTensor
  signature: (f : F ≃ₗᵢ[𝕜] G)
  body: congrIsometry (.refl 𝕜 E) f

中文:
定义 _root_.LinearIsometryEquiv.lTensor
  签名: (f : F ≃ₗᵢ[𝕜] G)
  定义体: congrIsometry (.refl 𝕜 E) f

Depends on / 依赖: congrIsometry
-/
noncomputable def _root_.LinearIsometryEquiv.lTensor (f : F ≃ₗᵢ[𝕜] G) :
    E otimes[𝕜] F ≃ₗᵢ[𝕜] E otimes[𝕜] G := congrIsometry (.refl 𝕜 E) f

variable (G) in
/--
Definition of `_root_.LinearIsometryEquiv.rTensor` / `_root_.LinearIsometryEquiv.rTensor` 的定义

English:
definition _root_.LinearIsometryEquiv.rTensor
  signature: (f : E ≃ₗᵢ[𝕜] F)
  body: congrIsometry f (.refl 𝕜 G)

中文:
定义 _root_.LinearIsometryEquiv.rTensor
  签名: (f : E ≃ₗᵢ[𝕜] F)
  定义体: congrIsometry f (.refl 𝕜 G)

Depends on / 依赖: congrIsometry
-/
noncomputable def _root_.LinearIsometryEquiv.rTensor (f : E ≃ₗᵢ[𝕜] F) :
    E otimes[𝕜] G ≃ₗᵢ[𝕜] F otimes[𝕜] G := congrIsometry f (.refl 𝕜 G)

/--
lemma `_root_.LinearIsometryEquiv.lTensor_def` / 引理 `_root_.LinearIsometryEquiv.lTensor_def`

English:
lemma _root_.LinearIsometryEquiv.lTensor_def
  given: (f : F ≃ₗᵢ[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.lTensor_def
  条件: (f : F ≃ₗᵢ[𝕜] G)
  证明: rfl
-/
lemma _root_.LinearIsometryEquiv.lTensor_def (f : F ≃ₗᵢ[𝕜] G) :
    f.lTensor E = congrIsometry (.refl 𝕜 E) f := rfl

/--
lemma `_root_.LinearIsometryEquiv.rTensor_def` / 引理 `_root_.LinearIsometryEquiv.rTensor_def`

English:
lemma _root_.LinearIsometryEquiv.rTensor_def
  given: (f : E ≃ₗᵢ[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.rTensor_def
  条件: (f : E ≃ₗᵢ[𝕜] F)
  证明: rfl
-/
lemma _root_.LinearIsometryEquiv.rTensor_def (f : E ≃ₗᵢ[𝕜] F) :
    f.rTensor G = congrIsometry f (.refl 𝕜 G) := rfl

/--
lemma `_root_.LinearIsometryEquiv.symm_lTensor` / 引理 `_root_.LinearIsometryEquiv.symm_lTensor`

English:
lemma _root_.LinearIsometryEquiv.symm_lTensor
  given: (f : F ≃ₗᵢ[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.symm_lTensor
  条件: (f : F ≃ₗᵢ[𝕜] G)
  证明: rfl
-/
lemma _root_.LinearIsometryEquiv.symm_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).symm = f.symm.lTensor E := rfl

/--
lemma `_root_.LinearIsometryEquiv.symm_rTensor` / 引理 `_root_.LinearIsometryEquiv.symm_rTensor`

English:
lemma _root_.LinearIsometryEquiv.symm_rTensor
  given: (f : E ≃ₗᵢ[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.symm_rTensor
  条件: (f : E ≃ₗᵢ[𝕜] F)
  证明: rfl
-/
lemma _root_.LinearIsometryEquiv.symm_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).symm = f.symm.rTensor G := rfl

/--
lemma `_root_.LinearIsometryEquiv.toLinearEquiv_lTensor` / 引理 `_root_.LinearIsometryEquiv.toLinearEquiv_lTensor`

English:
lemma _root_.LinearIsometryEquiv.toLinearEquiv_lTensor
  given: (f : F ≃ₗᵢ[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.toLinearEquiv_lTensor
  条件: (f : F ≃ₗᵢ[𝕜] G)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearEquiv = f.toLinearEquiv.lTensor E := rfl

/--
lemma `_root_.LinearIsometryEquiv.toLinearIsometry_lTensor` / 引理 `_root_.LinearIsometryEquiv.toLinearIsometry_lTensor`

English:
lemma _root_.LinearIsometryEquiv.toLinearIsometry_lTensor
  given: (f : F ≃ₗᵢ[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.toLinearIsometry_lTensor
  条件: (f : F ≃ₗᵢ[𝕜] G)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_lTensor (f : F ≃ₗᵢ[𝕜] G) :
    (f.lTensor E).toLinearIsometry = f.toLinearIsometry.lTensor E := rfl

/--
lemma `_root_.LinearIsometryEquiv.toLinearEquiv_rTensor` / 引理 `_root_.LinearIsometryEquiv.toLinearEquiv_rTensor`

English:
lemma _root_.LinearIsometryEquiv.toLinearEquiv_rTensor
  given: (f : E ≃ₗᵢ[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.toLinearEquiv_rTensor
  条件: (f : E ≃ₗᵢ[𝕜] F)
  证明: rfl

Depends on / 依赖: EquivLike, toSemilinearIsometryClass
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearEquiv_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearEquiv = f.toLinearEquiv.rTensor G := rfl

/--
lemma `_root_.LinearIsometryEquiv.toLinearIsometry_rTensor` / 引理 `_root_.LinearIsometryEquiv.toLinearIsometry_rTensor`

English:
lemma _root_.LinearIsometryEquiv.toLinearIsometry_rTensor
  given: (f : E ≃ₗᵢ[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.toLinearIsometry_rTensor
  条件: (f : E ≃ₗᵢ[𝕜] F)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometryEquiv.toLinearIsometry_rTensor (f : E ≃ₗᵢ[𝕜] F) :
    (f.rTensor G).toLinearIsometry = f.toLinearIsometry.rTensor G := rfl

/--
lemma `_root_.LinearIsometryEquiv.lTensor_apply` / 引理 `_root_.LinearIsometryEquiv.lTensor_apply`

English:
lemma _root_.LinearIsometryEquiv.lTensor_apply
  given: (f : F ≃ₗᵢ[𝕜] G) (x : E otimes[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.lTensor_apply
  条件: (f : F ≃ₗᵢ[𝕜] G) (x : E otimes[𝕜] F)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometryEquiv.lTensor_apply (f : F ≃ₗᵢ[𝕜] G) (x : E otimes[𝕜] F) :
    f.lTensor E x = f.toLinearEquiv.lTensor E x := rfl

/--
lemma `_root_.LinearIsometryEquiv.rTensor_apply` / 引理 `_root_.LinearIsometryEquiv.rTensor_apply`

English:
lemma _root_.LinearIsometryEquiv.rTensor_apply
  given: (f : E ≃ₗᵢ[𝕜] F) (x : E otimes[𝕜] G)
  proof: rfl

中文:
引理 _root_.LinearIsometryEquiv.rTensor_apply
  条件: (f : E ≃ₗᵢ[𝕜] F) (x : E otimes[𝕜] G)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometryEquiv.rTensor_apply (f : E ≃ₗᵢ[𝕜] F) (x : E otimes[𝕜] G) :
    f.rTensor G x = f.toLinearEquiv.rTensor G x := rfl

/--
Definition of `mapInclIsometry` / `mapInclIsometry` 的定义

English:
definition mapInclIsometry
  signature: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
  body: mapIsometry E'.subtypeₗᵢ F'.subtypeₗᵢ

中文:
定义 mapInclIsometry
  签名: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
  定义体: mapIsometry E'.subtypeₗᵢ F'.subtypeₗᵢ

Depends on / 依赖: mapIsometry
-/
noncomputable def mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    E' otimes[𝕜] F' ->ₗᵢ[𝕜] E otimes[𝕜] F :=
  mapIsometry E'.subtypeₗᵢ F'.subtypeₗᵢ

/--
lemma `mapInclIsometry_apply` / 引理 `mapInclIsometry_apply`

English:
lemma mapInclIsometry_apply
  statement: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
  proof: rfl

中文:
引理 mapInclIsometry_apply
  结论: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
  证明: rfl
-/
@[simp] lemma mapInclIsometry_apply (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
    (x : E' otimes[𝕜] F') : mapInclIsometry E' F' x = mapIncl E' F' x := rfl

/--
lemma `toLinearMap_mapInclIsometry` / 引理 `toLinearMap_mapInclIsometry`

English:
lemma toLinearMap_mapInclIsometry
  given: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
  proof: rfl

中文:
引理 toLinearMap_mapInclIsometry
  条件: (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F)
  证明: rfl
-/
@[simp] lemma toLinearMap_mapInclIsometry (E' : Submodule 𝕜 E) (F' : Submodule 𝕜 F) :
    (mapInclIsometry E' F').toLinearMap = mapIncl E' F' := rfl

/--
theorem `inner_comm_comm` / 定理 `inner_comm_comm`

English:
theorem inner_comm_comm
  given: (x y : E otimes[𝕜] F)
  proof: x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [mul_comm])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

中文:
定理 inner_comm_comm
  条件: (x y : E otimes[𝕜] F)
  证明: x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [mul_comm])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]
-/
@[simp] theorem inner_comm_comm (x y : E otimes[𝕜] F) :
    inner 𝕜 (TensorProduct.comm 𝕜 E F x) (TensorProduct.comm 𝕜 E F y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [mul_comm])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F) in
/--
Definition of `commIsometry` / `commIsometry` 的定义

English:
definition commIsometry
  signature: : E otimes[𝕜] F ≃ₗᵢ[𝕜] F otimes[𝕜] E
  body: .isometryOfInner inner_comm_comm TensorProduct.comm 𝕜 E F

中文:
定义 commIsometry
  签名: : E otimes[𝕜] F ≃ₗᵢ[𝕜] F otimes[𝕜] E
  定义体: .isometryOfInner inner_comm_comm TensorProduct.comm 𝕜 E F

Depends on / 依赖: TensorProduct, TensorProduct.comm, inner_comm_comm, isometryOfInner
-/
noncomputable def commIsometry : E otimes[𝕜] F ≃ₗᵢ[𝕜] F otimes[𝕜] E :=
.isometryOfInner inner_comm_comm TensorProduct.comm 𝕜 E F

/--
lemma `commIsometry_apply` / 引理 `commIsometry_apply`

English:
lemma commIsometry_apply
  given: (x : E otimes[𝕜] F)
  proof: rfl

中文:
引理 commIsometry_apply
  条件: (x : E otimes[𝕜] F)
  证明: rfl
-/
@[simp] lemma commIsometry_apply (x : E otimes[𝕜] F) :
    commIsometry 𝕜 E F x = TensorProduct.comm 𝕜 E F x := rfl
/--
lemma `commIsometry_symm` / 引理 `commIsometry_symm`

English:
lemma commIsometry_symm
  proof: rfl

中文:
引理 commIsometry_symm
  证明: rfl
-/
@[simp] lemma commIsometry_symm :
    (commIsometry 𝕜 E F).symm = commIsometry 𝕜 F E := rfl

/--
lemma `toLinearEquiv_commIsometry` / 引理 `toLinearEquiv_commIsometry`

English:
lemma toLinearEquiv_commIsometry
  proof: rfl

中文:
引理 toLinearEquiv_commIsometry
  证明: rfl
-/
@[simp] lemma toLinearEquiv_commIsometry :
    (commIsometry 𝕜 E F).toLinearEquiv = TensorProduct.comm 𝕜 E F := rfl

/--
lemma `norm_comm` / 引理 `norm_comm`

English:
lemma norm_comm
  given: (x : E otimes[𝕜] F)
  proof: commIsometry 𝕜 E F

中文:
引理 norm_comm
  条件: (x : E otimes[𝕜] F)
  证明: commIsometry 𝕜 E F
-/
@[simp] lemma norm_comm (x : E otimes[𝕜] F) :
.norm_map x ‖TensorProduct.comm 𝕜 E F x‖ = ‖x‖ := commIsometry 𝕜 E F
/--
lemma `nnnorm_comm` / 引理 `nnnorm_comm`

English:
lemma nnnorm_comm
  given: (x : E otimes[𝕜] F)
  proof: commIsometry 𝕜 E F

中文:
引理 nnnorm_comm
  条件: (x : E otimes[𝕜] F)
  证明: commIsometry 𝕜 E F
-/
@[simp] lemma nnnorm_comm (x : E otimes[𝕜] F) :
.nnnorm_map x ‖TensorProduct.comm 𝕜 E F x‖₊ = ‖x‖₊ := commIsometry 𝕜 E F
/--
lemma `enorm_comm` / 引理 `enorm_comm`

English:
lemma enorm_comm
  given: (x : E otimes[𝕜] F)
  proof: commIsometry 𝕜 E F

中文:
引理 enorm_comm
  条件: (x : E otimes[𝕜] F)
  证明: commIsometry 𝕜 E F
-/
@[simp] lemma enorm_comm (x : E otimes[𝕜] F) :
.toLinearIsometry.enorm_map x ‖TensorProduct.comm 𝕜 E F x‖ₑ = ‖x‖ₑ := commIsometry 𝕜 E F

/--
theorem `inner_lid_lid` / 定理 `inner_lid_lid`

English:
theorem inner_lid_lid
  given: (x y : 𝕜 otimes[𝕜] E)
  proof: x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

中文:
定理 inner_lid_lid
  条件: (x y : 𝕜 otimes[𝕜] E)
  证明: x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]
-/
@[simp] theorem inner_lid_lid (x y : 𝕜 otimes[𝕜] E) :
    inner 𝕜 (TensorProduct.lid 𝕜 E x) (TensorProduct.lid 𝕜 E y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun _ _ =>
    y.induction_on (by simp) (by simp [inner_smul_left, inner_smul_right, mul_assoc])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E) in
/--
Definition of `lidIsometry` / `lidIsometry` 的定义

English:
definition lidIsometry
  signature: : 𝕜 otimes[𝕜] E ≃ₗᵢ[𝕜] E
  body: .isometryOfInner inner_lid_lid TensorProduct.lid 𝕜 E

中文:
定义 lidIsometry
  签名: : 𝕜 otimes[𝕜] E ≃ₗᵢ[𝕜] E
  定义体: .isometryOfInner inner_lid_lid TensorProduct.lid 𝕜 E

Depends on / 依赖: TensorProduct, TensorProduct.lid, inner_lid_lid, isometryOfInner
-/
noncomputable def lidIsometry : 𝕜 otimes[𝕜] E ≃ₗᵢ[𝕜] E :=
.isometryOfInner inner_lid_lid TensorProduct.lid 𝕜 E

/--
lemma `toLinearEquiv_lidIsometry` / 引理 `toLinearEquiv_lidIsometry`

English:
lemma toLinearEquiv_lidIsometry
  proof: rfl

中文:
引理 toLinearEquiv_lidIsometry
  证明: rfl
-/
@[simp] lemma toLinearEquiv_lidIsometry :
    (lidIsometry 𝕜 E).toLinearEquiv = TensorProduct.lid 𝕜 E := rfl

/--
lemma `toContinuousLinearMap_symm_lidIsometry` / 引理 `toContinuousLinearMap_symm_lidIsometry`

English:
lemma toContinuousLinearMap_symm_lidIsometry
  proof: rfl

中文:
引理 toContinuousLinearMap_symm_lidIsometry
  证明: rfl
-/
lemma toContinuousLinearMap_symm_lidIsometry :
    (lidIsometry 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap = mkL 𝕜 𝕜 E 1 := rfl

/--
lemma `lidIsometry_apply` / 引理 `lidIsometry_apply`

English:
lemma lidIsometry_apply
  given: (x : 𝕜 otimes[𝕜] E)
  statement: lidIsometry 𝕜 E x = TensorProduct.lid 𝕜 E x
  proof: rfl

中文:
引理 lidIsometry_apply
  条件: (x : 𝕜 otimes[𝕜] E)
  结论: lidIsometry 𝕜 E x = TensorProduct.lid 𝕜 E x
  证明: rfl
-/
@[simp] lemma lidIsometry_apply (x : 𝕜 otimes[𝕜] E) : lidIsometry 𝕜 E x = TensorProduct.lid 𝕜 E x := rfl
/--
lemma `lidIsometry_symm_apply` / 引理 `lidIsometry_symm_apply`

English:
lemma lidIsometry_symm_apply
  given: (x : E)
  statement: (lidIsometry 𝕜 E).symm x = 1 otimesₜ x
  proof: rfl

中文:
引理 lidIsometry_symm_apply
  条件: (x : E)
  结论: (lidIsometry 𝕜 E).symm x = 1 otimesₜ x
  证明: rfl
-/
@[simp] lemma lidIsometry_symm_apply (x : E) : (lidIsometry 𝕜 E).symm x = 1 otimesₜ x := rfl

/--
lemma `norm_lid` / 引理 `norm_lid`

English:
lemma norm_lid
  given: (x)
  statement: ‖TensorProduct.lid 𝕜 E x‖ = ‖x‖
  proof: (lidIsometry 𝕜 E).norm_map x
.nnnorm_map x @[simp] lemma nnnorm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖₊ = ‖x‖₊ := lidIsometry 𝕜 E

中文:
引理 norm_lid
  条件: (x)
  结论: ‖TensorProduct.lid 𝕜 E x‖ = ‖x‖
  证明: (lidIsometry 𝕜 E).norm_map x
.nnnorm_map x @[simp] lemma nnnorm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖₊ = ‖x‖₊ := lidIsometry 𝕜 E
-/
@[simp] lemma norm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖ = ‖x‖ := (lidIsometry 𝕜 E).norm_map x
.nnnorm_map x @[simp] lemma nnnorm_lid (x) : ‖TensorProduct.lid 𝕜 E x‖₊ = ‖x‖₊ := lidIsometry 𝕜 E

/--
lemma `enorm_lid` / 引理 `enorm_lid`

English:
lemma enorm_lid
  given: (x : 𝕜 otimes[𝕜] E)
  proof: lidIsometry 𝕜 E

中文:
引理 enorm_lid
  条件: (x : 𝕜 otimes[𝕜] E)
  证明: lidIsometry 𝕜 E
-/
@[simp] lemma enorm_lid (x : 𝕜 otimes[𝕜] E) :
.toLinearIsometry.enorm_map x ‖TensorProduct.lid 𝕜 E x‖ₑ = ‖x‖ₑ := lidIsometry 𝕜 E

/--
theorem `inner_rid_rid` / 定理 `inner_rid_rid`

English:
theorem inner_rid_rid
  given: (x y : E otimes[𝕜] 𝕜)
  proof: by
  simp [← lid_comm]

中文:
定理 inner_rid_rid
  条件: (x y : E otimes[𝕜] 𝕜)
  证明: by
  simp [← lid_comm]
-/
@[simp] theorem inner_rid_rid (x y : E otimes[𝕜] 𝕜) :
    inner 𝕜 (TensorProduct.rid 𝕜 E x) (TensorProduct.rid 𝕜 E y) = inner 𝕜 x y := by
  simp [← lid_comm]

variable (𝕜 E) in
/--
Definition of `ridIsometry` / `ridIsometry` 的定义

English:
definition ridIsometry
  signature: : E otimes[𝕜] 𝕜 ≃ₗᵢ[𝕜] E
  body: .isometryOfInner inner_rid_rid TensorProduct.rid 𝕜 E

中文:
定义 ridIsometry
  签名: : E otimes[𝕜] 𝕜 ≃ₗᵢ[𝕜] E
  定义体: .isometryOfInner inner_rid_rid TensorProduct.rid 𝕜 E

Depends on / 依赖: TensorProduct, TensorProduct.rid, inner_rid_rid, isometryOfInner
-/
noncomputable def ridIsometry : E otimes[𝕜] 𝕜 ≃ₗᵢ[𝕜] E :=
.isometryOfInner inner_rid_rid TensorProduct.rid 𝕜 E

/--
lemma `toLinearEquiv_ridIsometry` / 引理 `toLinearEquiv_ridIsometry`

English:
lemma toLinearEquiv_ridIsometry
  proof: rfl

中文:
引理 toLinearEquiv_ridIsometry
  证明: rfl
-/
@[simp] lemma toLinearEquiv_ridIsometry :
    (ridIsometry 𝕜 E).toLinearEquiv = TensorProduct.rid 𝕜 E := rfl

/--
lemma `toContinuousLinearMap_symm_ridIsometry` / 引理 `toContinuousLinearMap_symm_ridIsometry`

English:
lemma toContinuousLinearMap_symm_ridIsometry
  proof: rfl

中文:
引理 toContinuousLinearMap_symm_ridIsometry
  证明: rfl
-/
lemma toContinuousLinearMap_symm_ridIsometry :
    (ridIsometry 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap = (mkL 𝕜 E 𝕜).flip 1 := rfl

/--
lemma `ridIsometry_apply` / 引理 `ridIsometry_apply`

English:
lemma ridIsometry_apply
  given: (x)
  statement: ridIsometry 𝕜 E x = TensorProduct.rid 𝕜 E x
  proof: rfl

中文:
引理 ridIsometry_apply
  条件: (x)
  结论: ridIsometry 𝕜 E x = TensorProduct.rid 𝕜 E x
  证明: rfl
-/
@[simp] lemma ridIsometry_apply (x) : ridIsometry 𝕜 E x = TensorProduct.rid 𝕜 E x := rfl
/--
lemma `symm_ridIsometry_apply` / 引理 `symm_ridIsometry_apply`

English:
lemma symm_ridIsometry_apply
  given: (x)
  statement: (ridIsometry 𝕜 E).symm x = x otimesₜ 1
  proof: rfl

中文:
引理 symm_ridIsometry_apply
  条件: (x)
  结论: (ridIsometry 𝕜 E).symm x = x otimesₜ 1
  证明: rfl
-/
@[simp] lemma symm_ridIsometry_apply (x) : (ridIsometry 𝕜 E).symm x = x otimesₜ 1 := rfl

/--
lemma `lidIsometry_eq_ridIsometry` / 引理 `lidIsometry_eq_ridIsometry`

English:
lemma lidIsometry_eq_ridIsometry
  statement: lidIsometry 𝕜 𝕜 = ridIsometry 𝕜 𝕜
  proof: by ext; simp [lid_eq_rid]

中文:
引理 lidIsometry_eq_ridIsometry
  结论: lidIsometry 𝕜 𝕜 = ridIsometry 𝕜 𝕜
  证明: by ext; simp [lid_eq_rid]

Depends on / 依赖: lid_eq_rid
-/
lemma lidIsometry_eq_ridIsometry : lidIsometry 𝕜 𝕜 = ridIsometry 𝕜 𝕜 := by ext; simp [lid_eq_rid]

/--
lemma `norm_rid` / 引理 `norm_rid`

English:
lemma norm_rid
  given: (x)
  statement: ‖TensorProduct.rid 𝕜 E x‖ = ‖x‖
  proof: (ridIsometry 𝕜 E).norm_map x

中文:
引理 norm_rid
  条件: (x)
  结论: ‖TensorProduct.rid 𝕜 E x‖ = ‖x‖
  证明: (ridIsometry 𝕜 E).norm_map x
-/
@[simp] lemma norm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖ = ‖x‖ := (ridIsometry 𝕜 E).norm_map x
/--
lemma `nnnorm_rid` / 引理 `nnnorm_rid`

English:
lemma nnnorm_rid
  given: (x)
  statement: ‖TensorProduct.rid 𝕜 E x‖₊ = ‖x‖₊
  proof: by simp [← NNReal.coe_inj]

中文:
引理 nnnorm_rid
  条件: (x)
  结论: ‖TensorProduct.rid 𝕜 E x‖₊ = ‖x‖₊
  证明: by simp [← NNReal.coe_inj]
-/
@[simp] lemma nnnorm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖₊ = ‖x‖₊ := by simp [← NNReal.coe_inj]

/--
lemma `enorm_rid` / 引理 `enorm_rid`

English:
lemma enorm_rid
  given: (x)
  statement: ‖TensorProduct.rid 𝕜 E x‖ₑ = ‖x‖ₑ
  proof: .toLinearIsometry.enorm_map x ridIsometry 𝕜 E

中文:
引理 enorm_rid
  条件: (x)
  结论: ‖TensorProduct.rid 𝕜 E x‖ₑ = ‖x‖ₑ
  证明: .toLinearIsometry.enorm_map x ridIsometry 𝕜 E
-/
@[simp] lemma enorm_rid (x) : ‖TensorProduct.rid 𝕜 E x‖ₑ = ‖x‖ₑ :=
.toLinearIsometry.enorm_map x ridIsometry 𝕜 E

/--
lemma `commIsometry_trans_lidIsometry` / 引理 `commIsometry_trans_lidIsometry`

English:
lemma commIsometry_trans_lidIsometry
  proof: by ext; simp

中文:
引理 commIsometry_trans_lidIsometry
  证明: by ext; simp
-/
@[simp] lemma commIsometry_trans_lidIsometry :
    (commIsometry 𝕜 E 𝕜).trans (lidIsometry 𝕜 E) = ridIsometry 𝕜 E := by ext; simp

/--
lemma `commIsometry_trans_ridIsometry` / 引理 `commIsometry_trans_ridIsometry`

English:
lemma commIsometry_trans_ridIsometry
  proof: by ext; simp

中文:
引理 commIsometry_trans_ridIsometry
  证明: by ext; simp
-/
@[simp] lemma commIsometry_trans_ridIsometry :
    (commIsometry 𝕜 𝕜 E).trans (ridIsometry 𝕜 E) = lidIsometry 𝕜 E := by ext; simp

/--
theorem `inner_assoc_assoc` / 定理 `inner_assoc_assoc`

English:
theorem inner_assoc_assoc
  given: (x y : E otimes[𝕜] F otimes[𝕜] G)
  proof: x.induction_on (by simp) (fun a _ =>
    y.induction_on (by simp) (fun c _ =>
      a.induction_on (by simp) (fun _ _ =>
        c.induction_on (by simp) (by simp [mul_assoc])
        fun _ _ h1 h2 => by simp only [add_tmul, inner_add_right, map_add, h1, h2])
      fun _ _ h1 h2 => by simp only [add

中文:
定理 inner_assoc_assoc
  条件: (x y : E otimes[𝕜] F otimes[𝕜] G)
  证明: x.induction_on (by simp) (fun a _ =>
    y.induction_on (by simp) (fun c _ =>
      a.induction_on (by simp) (fun _ _ =>
        c.induction_on (by simp) (by simp [mul_assoc])
        fun _ _ h1 h2 => by simp only [add_tmul, inner_add_right, map_add, h1, h2])
      fun _ _ h1 h2 => by simp only [add
-/
@[simp] theorem inner_assoc_assoc (x y : E otimes[𝕜] F otimes[𝕜] G) :
    inner 𝕜 (TensorProduct.assoc 𝕜 E F G x) (TensorProduct.assoc 𝕜 E F G y) = inner 𝕜 x y :=
  x.induction_on (by simp) (fun a _ =>
    y.induction_on (by simp) (fun c _ =>
      a.induction_on (by simp) (fun _ _ =>
        c.induction_on (by simp) (by simp [mul_assoc])
        fun _ _ h1 h2 => by simp only [add_tmul, inner_add_right, map_add, h1, h2])
      fun _ _ h1 h2 => by simp only [add_tmul, inner_add_left, map_add, h1, h2])
    fun _ _ h1 h2 => by simp only [inner_add_right, map_add, h1, h2])
  fun _ _ h1 h2 => by simp only [inner_add_left, map_add, h1, h2]

variable (𝕜 E F G) in
/--
Definition of `assocIsometry` / `assocIsometry` 的定义

English:
definition assocIsometry
  signature: : E otimes[𝕜] F otimes[𝕜] G ≃ₗᵢ[𝕜] E otimes[𝕜] (F otimes[𝕜] G)
  body: .isometryOfInner inner_assoc_assoc TensorProduct.assoc 𝕜 E F G

中文:
定义 assocIsometry
  签名: : E otimes[𝕜] F otimes[𝕜] G ≃ₗᵢ[𝕜] E otimes[𝕜] (F otimes[𝕜] G)
  定义体: .isometryOfInner inner_assoc_assoc TensorProduct.assoc 𝕜 E F G

Depends on / 依赖: TensorProduct, TensorProduct.assoc, inner_assoc_assoc, isometryOfInner
-/
noncomputable def assocIsometry : E otimes[𝕜] F otimes[𝕜] G ≃ₗᵢ[𝕜] E otimes[𝕜] (F otimes[𝕜] G) :=
.isometryOfInner inner_assoc_assoc TensorProduct.assoc 𝕜 E F G

/--
lemma `assocIsometry_apply` / 引理 `assocIsometry_apply`

English:
lemma assocIsometry_apply
  given: (x : E otimes[𝕜] F otimes[𝕜] G)
  proof: rfl

中文:
引理 assocIsometry_apply
  条件: (x : E otimes[𝕜] F otimes[𝕜] G)
  证明: rfl
-/
@[simp] lemma assocIsometry_apply (x : E otimes[𝕜] F otimes[𝕜] G) :
    assocIsometry 𝕜 E F G x = TensorProduct.assoc 𝕜 E F G x := rfl

/--
lemma `assocIsometry_symm_apply` / 引理 `assocIsometry_symm_apply`

English:
lemma assocIsometry_symm_apply
  given: (x : E otimes[𝕜] (F otimes[𝕜] G))
  proof: rfl

中文:
引理 assocIsometry_symm_apply
  条件: (x : E otimes[𝕜] (F otimes[𝕜] G))
  证明: rfl
-/
@[simp] lemma assocIsometry_symm_apply (x : E otimes[𝕜] (F otimes[𝕜] G)) :
    (assocIsometry 𝕜 E F G).symm x = (TensorProduct.assoc 𝕜 E F G).symm x := rfl

/--
lemma `toLinearEquiv_assocIsometry` / 引理 `toLinearEquiv_assocIsometry`

English:
lemma toLinearEquiv_assocIsometry
  proof: rfl

中文:
引理 toLinearEquiv_assocIsometry
  证明: rfl
-/
@[simp] lemma toLinearEquiv_assocIsometry :
    (assocIsometry 𝕜 E F G).toLinearEquiv = TensorProduct.assoc 𝕜 E F G := rfl

/--
lemma `norm_assoc` / 引理 `norm_assoc`

English:
lemma norm_assoc
  given: (x : E otimes[𝕜] F otimes[𝕜] G)
  proof: assocIsometry 𝕜 E F G

中文:
引理 norm_assoc
  条件: (x : E otimes[𝕜] F otimes[𝕜] G)
  证明: assocIsometry 𝕜 E F G
-/
@[simp] lemma norm_assoc (x : E otimes[𝕜] F otimes[𝕜] G) :
.norm_map x ‖TensorProduct.assoc 𝕜 E F G x‖ = ‖x‖ := assocIsometry 𝕜 E F G

/--
lemma `nnnorm_assoc` / 引理 `nnnorm_assoc`

English:
lemma nnnorm_assoc
  given: (x : E otimes[𝕜] F otimes[𝕜] G)
  proof: assocIsometry 𝕜 E F G

中文:
引理 nnnorm_assoc
  条件: (x : E otimes[𝕜] F otimes[𝕜] G)
  证明: assocIsometry 𝕜 E F G
-/
@[simp] lemma nnnorm_assoc (x : E otimes[𝕜] F otimes[𝕜] G) :
.nnnorm_map x ‖TensorProduct.assoc 𝕜 E F G x‖₊ = ‖x‖₊ := assocIsometry 𝕜 E F G

/--
lemma `enorm_assoc` / 引理 `enorm_assoc`

English:
lemma enorm_assoc
  given: (x : E otimes[𝕜] F otimes[𝕜] G)
  proof: assocIsometry 𝕜 E F G

中文:
引理 enorm_assoc
  条件: (x : E otimes[𝕜] F otimes[𝕜] G)
  证明: assocIsometry 𝕜 E F G
-/
@[simp] lemma enorm_assoc (x : E otimes[𝕜] F otimes[𝕜] G) :
.toLinearIsometry.enorm_map x ‖TensorProduct.assoc 𝕜 E F G x‖ₑ = ‖x‖ₑ := assocIsometry 𝕜 E F G

end isometry

end TensorProduct

namespace ContinuousLinearMap

open TensorProduct

variable (G)

/--
Definition of `rTensor` / `rTensor` 的定义

English:
definition rTensor
  signature: (f : E ->L[𝕜] F)
  body: (f.toLinearMap.rTensor G).mkContinuous ‖f‖ fun x => by
    /-
    Any tensor `x` can be written as a linear combination of pure tensors, `x = ∑ e n ⊗ₜ g n`. This
    induces three Gram matrices, one based on `e`, one on `f ∘ e` and one on `g`. Up to a constant,
    the `e`-based Gram matrix is large

中文:
定义 rTensor
  签名: (f : E ->L[𝕜] F)
  定义体: (f.toLinearMap.rTensor G).mkContinuous ‖f‖ fun x => by
    /-
    Any tensor `x` can be written as a linear combination of pure tensors, `x = ∑ e n ⊗ₜ g n`. This
    induces three Gram matrices, one based on `e`, one on `f ∘ e` and one on `g`. Up to a constant,
    the `e`-based Gram matrix is large

Depends on / 依赖: f.toLinearMap.rTensor, mkContinuous, rTensor, toLinearMap
-/
noncomputable def rTensor (f : E ->L[𝕜] F) : (E otimes[𝕜] G) ->L[𝕜] (F otimes[𝕜] G) :=
  (f.toLinearMap.rTensor G).mkContinuous ‖f‖ fun x => by
    /-
    Any tensor `x` can be written as a linear combination of pure tensors, `x = ∑ e n ⊗ₜ g n`. This
    induces three Gram matrices, one based on `e`, one on `f ∘ e` and one on `g`. Up to a constant,
    the `e`-based Gram matrix is larger than the `f ∘ e`-based one. This implies the existence of
    a matrix, whose form is used to show that `‖f‖ ^ 2 * ‖x‖ ^ 2 - ‖f x‖ ^ 2` is a sum of
    nonnegative terms.
    -/
    obtain ⟨n, e, g, hx⟩ := exists_sum_tmul_eq x
    obtain ⟨c, hc_supp, hc⟩ := Submodule.mem_span_set.mp
      ((span_tmul_eq_top 𝕜 E G) ▸ Submodule.mem_top (x := x))
    obtain ⟨m, A, hA⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp
      (Matrix.posSemidef_opNorm_smul_gram_sub_gram e f)
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simp_rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add, ← Matrix.ext_iff, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.gram_apply, Function.comp_apply] at hA
    simp_rw [mul_pow, hx, map_sum, LinearMap.rTensor_tmul, coe_coe,
      ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_sum, sum_inner, inner_tmul, ← hA, sub_mul,
      Finset.sum_sub_distrib, map_sub, ← RCLike.smul_re, Finset.smul_sum, smul_mul_assoc,
      sub_le_self_iff, Matrix.sum_apply, mul_comm, Finset.mul_sum]
    simp_rw +singlePass [Finset.sum_comm_cycle, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
      ← mul_left_comm, ← mul_assoc, ← starRingEnd_self_apply (A _ _), ← inner_smul_left]
    simp [mul_comm, ← inner_smul_right, ← sum_inner, ← inner_sum, Finset.sum_nonneg]

variable {G} in
/--
lemma `rTensor_apply` / 引理 `rTensor_apply`

English:
lemma rTensor_apply
  given: (f : E ->L[𝕜] F) (x : E otimes G)
  proof: rfl

中文:
引理 rTensor_apply
  条件: (f : E ->L[𝕜] F) (x : E otimes G)
  证明: rfl
-/
@[simp] lemma rTensor_apply (f : E ->L[𝕜] F) (x : E otimes G) :
    f.rTensor G x = f.toLinearMap.rTensor G x := rfl

variable {G} in
/--
lemma `rTensor_tmul` / 引理 `rTensor_tmul`

English:
lemma rTensor_tmul
  given: (f : E ->L[𝕜] F) (m : E) (n : G)
  statement: f.rTensor G (m otimesₜ n) = f m otimesₜ n
  proof: rfl

中文:
引理 rTensor_tmul
  条件: (f : E ->L[𝕜] F) (m : E) (n : G)
  结论: f.rTensor G (m otimesₜ n) = f m otimesₜ n
  证明: rfl
-/
lemma rTensor_tmul (f : E ->L[𝕜] F) (m : E) (n : G) : f.rTensor G (m otimesₜ n) = f m otimesₜ n := rfl

/--
lemma `toLinearMap_rTensor` / 引理 `toLinearMap_rTensor`

English:
lemma toLinearMap_rTensor
  given: (f : E ->L[𝕜] F)
  proof: rfl

中文:
引理 toLinearMap_rTensor
  条件: (f : E ->L[𝕜] F)
  证明: rfl
-/
@[simp] lemma toLinearMap_rTensor (f : E ->L[𝕜] F) :
    (f.rTensor G).toLinearMap = f.toLinearMap.rTensor G := rfl

/--
lemma `_root_.LinearIsometry.toContinuousLinearMap_rTensor` / 引理 `_root_.LinearIsometry.toContinuousLinearMap_rTensor`

English:
lemma _root_.LinearIsometry.toContinuousLinearMap_rTensor
  given: (f : E ->ₗᵢ[𝕜] F)
  proof: rfl

中文:
引理 _root_.LinearIsometry.toContinuousLinearMap_rTensor
  条件: (f : E ->ₗᵢ[𝕜] F)
  证明: rfl
-/
@[simp] lemma _root_.LinearIsometry.toContinuousLinearMap_rTensor (f : E ->ₗᵢ[𝕜] F) :
    (f.rTensor G).toContinuousLinearMap = f.toContinuousLinearMap.rTensor G := rfl

/--
theorem `norm_rTensor_le` / 定理 `norm_rTensor_le`

English:
theorem norm_rTensor_le
  given: (f : E ->L[𝕜] F)
  statement: ‖f.rTensor G‖ <= ‖f‖
  proof: LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

中文:
定理 norm_rTensor_le
  条件: (f : E ->L[𝕜] F)
  结论: ‖f.rTensor G‖ <= ‖f‖
  证明: LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, h.symm, mkContinuous_norm_le, norm_nonneg
-/
theorem norm_rTensor_le (f : E ->L[𝕜] F) : ‖f.rTensor G‖ <= ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/--
lemma `rTensor_add` / 引理 `rTensor_add`

English:
lemma rTensor_add
  given: (f₁ f₂ : E ->L[𝕜] F)
  proof: by ext; simp

中文:
引理 rTensor_add
  条件: (f₁ f₂ : E ->L[𝕜] F)
  证明: by ext; simp
-/
@[simp] lemma rTensor_add (f₁ f₂ : E ->L[𝕜] F) :
    (f₁ + f₂).rTensor G = f₁.rTensor G + f₂.rTensor G := by ext; simp

/--
lemma `rTensor_smul` / 引理 `rTensor_smul`

English:
lemma rTensor_smul
  given: (r : 𝕜) (f : E ->L[𝕜] F)
  proof: by ext; simp

中文:
引理 rTensor_smul
  条件: (r : 𝕜) (f : E ->L[𝕜] F)
  证明: by ext; simp
-/
@[simp] lemma rTensor_smul (r : 𝕜) (f : E ->L[𝕜] F) :
    (r • f).rTensor G = r • f.rTensor G := by ext; simp

/--
lemma `rTensor_id` / 引理 `rTensor_id`

English:
lemma rTensor_id
  statement: (.id 𝕜 E : E ->L[𝕜] E).rTensor G = .id 𝕜 _
  proof: by ext; simp

中文:
引理 rTensor_id
  结论: (.id 𝕜 E : E ->L[𝕜] E).rTensor G = .id 𝕜 _
  证明: by ext; simp
-/
@[simp] lemma rTensor_id : (.id 𝕜 E : E ->L[𝕜] E).rTensor G = .id 𝕜 _ := by ext; simp
/--
lemma `rTensor_one` / 引理 `rTensor_one`

English:
lemma rTensor_one
  statement: (1 : E ->L[𝕜] E).rTensor G = 1
  proof: rTensor_id _

中文:
引理 rTensor_one
  结论: (1 : E ->L[𝕜] E).rTensor G = 1
  证明: rTensor_id _
-/
@[simp] lemma rTensor_one : (1 : E ->L[𝕜] E).rTensor G = 1 := rTensor_id _
/--
lemma `rTensor_zero` / 引理 `rTensor_zero`

English:
lemma rTensor_zero
  statement: (0 : E ->L[𝕜] F).rTensor G = 0
  proof: by ext; simp

中文:
引理 rTensor_zero
  结论: (0 : E ->L[𝕜] F).rTensor G = 0
  证明: by ext; simp
-/
@[simp] lemma rTensor_zero : (0 : E ->L[𝕜] F).rTensor G = 0 := by ext; simp
/--
lemma `rTensor_neg` / 引理 `rTensor_neg`

English:
lemma rTensor_neg
  given: (f : E ->L[𝕜] F)
  statement: (-f).rTensor G = -f.rTensor G
  proof: by ext; simp

中文:
引理 rTensor_neg
  条件: (f : E ->L[𝕜] F)
  结论: (-f).rTensor G = -f.rTensor G
  证明: by ext; simp
-/
@[simp] lemma rTensor_neg (f : E ->L[𝕜] F) : (-f).rTensor G = -f.rTensor G := by ext; simp

/--
lemma `rTensor_sub` / 引理 `rTensor_sub`

English:
lemma rTensor_sub
  given: (f₁ f₂ : E ->L[𝕜] F)
  proof: by ext; simp

中文:
引理 rTensor_sub
  条件: (f₁ f₂ : E ->L[𝕜] F)
  证明: by ext; simp
-/
@[simp] lemma rTensor_sub (f₁ f₂ : E ->L[𝕜] F) :
    (f₁ - f₂).rTensor G = f₁.rTensor G - f₂.rTensor G := by ext; simp

/--
lemma `rTensor_comp` / 引理 `rTensor_comp`

English:
lemma rTensor_comp
  given: (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E)
  proof: by ext; simp [LinearMap.rTensor_comp]

中文:
引理 rTensor_comp
  条件: (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E)
  证明: by ext; simp [LinearMap.rTensor_comp]

Depends on / 依赖: LinearMap, LinearMap.rTensor_comp, rTensor_comp
-/
lemma rTensor_comp (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E) :
    (f₁ ∘L f₂).rTensor G = f₁.rTensor G ∘L f₂.rTensor G := by ext; simp [LinearMap.rTensor_comp]

/--
lemma `rTensor_mul` / 引理 `rTensor_mul`

English:
lemma rTensor_mul
  given: (f₁ f₂ : E ->L[𝕜] E)
  statement: (f₁ * f₂).rTensor G = f₁.rTensor G * f₂.rTensor G
  proof: rTensor_comp _ _ _

中文:
引理 rTensor_mul
  条件: (f₁ f₂ : E ->L[𝕜] E)
  结论: (f₁ * f₂).rTensor G = f₁.rTensor G * f₂.rTensor G
  证明: rTensor_comp _ _ _

Depends on / 依赖: rTensor_comp
-/
lemma rTensor_mul (f₁ f₂ : E ->L[𝕜] E) : (f₁ * f₂).rTensor G = f₁.rTensor G * f₂.rTensor G :=
  rTensor_comp _ _ _

/--
lemma `rTensor_pow` / 引理 `rTensor_pow`

English:
lemma rTensor_pow
  given: (f : E ->L[𝕜] E) (n : Nat)
  statement: (f ^ n).rTensor G = (f.rTensor G) ^ n
  proof: by
  simp [← coe_inj]

中文:
引理 rTensor_pow
  条件: (f : E ->L[𝕜] E) (n : 自然数)
  结论: (f ^ n).rTensor G = (f.rTensor G) ^ n
  证明: by
  simp [← coe_inj]
-/
@[simp] lemma rTensor_pow (f : E ->L[𝕜] E) (n : Nat) : (f ^ n).rTensor G = (f.rTensor G) ^ n := by
  simp [← coe_inj]

/--
Definition of `lTensor` / `lTensor` 的定义

English:
definition lTensor
  signature: (g : E ->L[𝕜] F)
  body: commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E

中文:
定义 lTensor
  签名: (g : E ->L[𝕜] F)
  定义体: commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E

Depends on / 依赖: commIsometry, g.rTensor, rTensor
-/
noncomputable def lTensor (g : E ->L[𝕜] F) : (G otimes[𝕜] E) ->L[𝕜] (G otimes[𝕜] F) :=
  commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E

variable {G} in
/--
lemma `lTensor_apply` / 引理 `lTensor_apply`

English:
lemma lTensor_apply
  given: (g : G ->L[𝕜] H) (x : E otimes G)
  proof: by
  simp [lTensor, ← LinearMap.comm_comp_rTensor_comp_comm_eq]

中文:
引理 lTensor_apply
  条件: (g : G ->L[𝕜] H) (x : E otimes G)
  证明: by
  simp [lTensor, ← LinearMap.comm_comp_rTensor_comp_comm_eq]
-/
@[simp] lemma lTensor_apply (g : G ->L[𝕜] H) (x : E otimes G) :
    g.lTensor E x = g.toLinearMap.lTensor E x := by
  simp [lTensor, ← LinearMap.comm_comp_rTensor_comp_comm_eq]

/--
lemma `lTensor_tmul` / 引理 `lTensor_tmul`

English:
lemma lTensor_tmul
  given: (g : E ->L[𝕜] F) (m : G) (n : E)
  statement: g.lTensor G (m otimesₜ n) = m otimesₜ g n
  proof: rfl

中文:
引理 lTensor_tmul
  条件: (g : E ->L[𝕜] F) (m : G) (n : E)
  结论: g.lTensor G (m otimesₜ n) = m otimesₜ g n
  证明: rfl
-/
lemma lTensor_tmul (g : E ->L[𝕜] F) (m : G) (n : E) : g.lTensor G (m otimesₜ n) = m otimesₜ g n := rfl

/--
theorem `commIsometry_comp_lTensor_comp_commIsometry_eq` / 定理 `commIsometry_comp_lTensor_comp_commIsometry_eq`

English:
theorem commIsometry_comp_lTensor_comp_commIsometry_eq
  given: (g : E ->L[𝕜] F)
  proof: rfl

中文:
定理 commIsometry_comp_lTensor_comp_commIsometry_eq
  条件: (g : E ->L[𝕜] F)
  证明: rfl
-/
theorem commIsometry_comp_lTensor_comp_commIsometry_eq (g : E ->L[𝕜] F) :
    commIsometry 𝕜 F G ∘L g.rTensor G ∘L commIsometry 𝕜 G E = g.lTensor G :=
  rfl

/--
theorem `commIsometry_comp_rTensor_comp_commIsometry_eq` / 定理 `commIsometry_comp_rTensor_comp_commIsometry_eq`

English:
theorem commIsometry_comp_rTensor_comp_commIsometry_eq
  given: (f : E ->L[𝕜] F)
  proof: by
  ext; simp [lTensor]

中文:
定理 commIsometry_comp_rTensor_comp_commIsometry_eq
  条件: (f : E ->L[𝕜] F)
  证明: by
  ext; simp [lTensor]

Depends on / 依赖: lTensor
-/
theorem commIsometry_comp_rTensor_comp_commIsometry_eq (f : E ->L[𝕜] F) :
    commIsometry 𝕜 G F ∘L f.lTensor G ∘L commIsometry 𝕜 E G = f.rTensor G := by
  ext; simp [lTensor]

/--
theorem `lTensor_comp_commIsometry` / 定理 `lTensor_comp_commIsometry`

English:
theorem lTensor_comp_commIsometry
  given: (f : E ->L[𝕜] F)
  proof: by
  ext; simp [lTensor]

中文:
定理 lTensor_comp_commIsometry
  条件: (f : E ->L[𝕜] F)
  证明: by
  ext; simp [lTensor]

Depends on / 依赖: lTensor
-/
theorem lTensor_comp_commIsometry (f : E ->L[𝕜] F) :
    f.lTensor G ∘L commIsometry 𝕜 E G = commIsometry 𝕜 F G ∘L f.rTensor G := by
  ext; simp [lTensor]

/--
theorem `rTensor_comp_commIsometry` / 定理 `rTensor_comp_commIsometry`

English:
theorem rTensor_comp_commIsometry
  given: (g : E ->L[𝕜] F)
  proof: by
  ext; simp [lTensor]

中文:
定理 rTensor_comp_commIsometry
  条件: (g : E ->L[𝕜] F)
  证明: by
  ext; simp [lTensor]

Depends on / 依赖: lTensor
-/
theorem rTensor_comp_commIsometry (g : E ->L[𝕜] F) :
    g.rTensor G ∘L commIsometry 𝕜 G E = commIsometry 𝕜 G F ∘L g.lTensor G := by
  ext; simp [lTensor]

/--
lemma `toLinearMap_lTensor` / 引理 `toLinearMap_lTensor`

English:
lemma toLinearMap_lTensor
  given: (g : E ->L[𝕜] F)
  proof: by ext; simp

中文:
引理 toLinearMap_lTensor
  条件: (g : E ->L[𝕜] F)
  证明: by ext; simp
-/
@[simp] lemma toLinearMap_lTensor (g : E ->L[𝕜] F) :
    (g.lTensor G).toLinearMap = g.toLinearMap.lTensor G := by ext; simp

/--
lemma `_root_.LinearIsometry.toContinuousLinearMap_lTensor` / 引理 `_root_.LinearIsometry.toContinuousLinearMap_lTensor`

English:
lemma _root_.LinearIsometry.toContinuousLinearMap_lTensor
  given: (g : E ->ₗᵢ[𝕜] F)
  proof: by ext; simp

中文:
引理 _root_.LinearIsometry.toContinuousLinearMap_lTensor
  条件: (g : E ->ₗᵢ[𝕜] F)
  证明: by ext; simp
-/
@[simp] lemma _root_.LinearIsometry.toContinuousLinearMap_lTensor (g : E ->ₗᵢ[𝕜] F) :
    (g.lTensor G).toContinuousLinearMap = g.toContinuousLinearMap.lTensor G := by ext; simp

/--
theorem `norm_lTensor_le` / 定理 `norm_lTensor_le`

English:
theorem norm_lTensor_le
  given: (g : E ->L[𝕜] F)
  statement: ‖g.lTensor G‖ <= ‖g‖
  proof: by
  simp_rw [lTensor, ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry]
  grw [opNorm_comp_le, opNorm_comp_le, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le, mul_one, one_mul, norm_rTensor_le]

中文:
定理 norm_lTensor_le
  条件: (g : E ->L[𝕜] F)
  结论: ‖g.lTensor G‖ <= ‖g‖
  证明: by
  simp_rw [lTensor, ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry]
  grw [opNorm_comp_le, opNorm_comp_le, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le, mul_one, one_mul, norm_rTensor_le]

Depends on / 依赖: LinearIsometry, LinearIsometry.norm_toContinuousLinearMap_le, LinearIsometryEquiv, LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry, lTensor, mul_one, norm_rTensor_le, norm_toContinuousLinearMap_le, one_mul, opNorm_comp_le, simp_rw, toContinuousLinearMap_toLinearIsometry
-/
theorem norm_lTensor_le (g : E ->L[𝕜] F) : ‖g.lTensor G‖ <= ‖g‖ := by
  simp_rw [lTensor, ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry]
  grw [opNorm_comp_le, opNorm_comp_le, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le, mul_one, one_mul, norm_rTensor_le]

/--
lemma `lTensor_add` / 引理 `lTensor_add`

English:
lemma lTensor_add
  given: (f₁ f₂ : E ->L[𝕜] F)
  proof: by ext; simp

中文:
引理 lTensor_add
  条件: (f₁ f₂ : E ->L[𝕜] F)
  证明: by ext; simp
-/
@[simp] lemma lTensor_add (f₁ f₂ : E ->L[𝕜] F) :
    (f₁ + f₂).lTensor G = f₁.lTensor G + f₂.lTensor G := by ext; simp

/--
lemma `lTensor_smul` / 引理 `lTensor_smul`

English:
lemma lTensor_smul
  given: (r : 𝕜) (f : E ->L[𝕜] F)
  statement: (r • f).lTensor G = r • f.lTensor G
  proof: by
  ext; simp

中文:
引理 lTensor_smul
  条件: (r : 𝕜) (f : E ->L[𝕜] F)
  结论: (r • f).lTensor G = r • f.lTensor G
  证明: by
  ext; simp
-/
@[simp] lemma lTensor_smul (r : 𝕜) (f : E ->L[𝕜] F) : (r • f).lTensor G = r • f.lTensor G := by
  ext; simp

/--
lemma `lTensor_id` / 引理 `lTensor_id`

English:
lemma lTensor_id
  statement: (.id 𝕜 E : E ->L[𝕜] E).lTensor G = .id 𝕜 _
  proof: by ext; simp

中文:
引理 lTensor_id
  结论: (.id 𝕜 E : E ->L[𝕜] E).lTensor G = .id 𝕜 _
  证明: by ext; simp
-/
@[simp] lemma lTensor_id : (.id 𝕜 E : E ->L[𝕜] E).lTensor G = .id 𝕜 _ := by ext; simp
/--
lemma `lTensor_one` / 引理 `lTensor_one`

English:
lemma lTensor_one
  statement: (1 : E ->L[𝕜] E).lTensor G = 1
  proof: lTensor_id _

中文:
引理 lTensor_one
  结论: (1 : E ->L[𝕜] E).lTensor G = 1
  证明: lTensor_id _
-/
@[simp] lemma lTensor_one : (1 : E ->L[𝕜] E).lTensor G = 1 := lTensor_id _
/--
lemma `lTensor_zero` / 引理 `lTensor_zero`

English:
lemma lTensor_zero
  statement: (0 : E ->L[𝕜] F).lTensor G = 0
  proof: by ext; simp

中文:
引理 lTensor_zero
  结论: (0 : E ->L[𝕜] F).lTensor G = 0
  证明: by ext; simp
-/
@[simp] lemma lTensor_zero : (0 : E ->L[𝕜] F).lTensor G = 0 := by ext; simp
/--
lemma `lTensor_neg` / 引理 `lTensor_neg`

English:
lemma lTensor_neg
  given: (f : E ->L[𝕜] F)
  statement: (-f).lTensor G = -f.lTensor G
  proof: by ext; simp

中文:
引理 lTensor_neg
  条件: (f : E ->L[𝕜] F)
  结论: (-f).lTensor G = -f.lTensor G
  证明: by ext; simp
-/
@[simp] lemma lTensor_neg (f : E ->L[𝕜] F) : (-f).lTensor G = -f.lTensor G := by ext; simp

/--
lemma `lTensor_sub` / 引理 `lTensor_sub`

English:
lemma lTensor_sub
  given: (f₁ f₂ : E ->L[𝕜] F)
  proof: by ext; simp

中文:
引理 lTensor_sub
  条件: (f₁ f₂ : E ->L[𝕜] F)
  证明: by ext; simp
-/
@[simp] lemma lTensor_sub (f₁ f₂ : E ->L[𝕜] F) :
    (f₁ - f₂).lTensor G = f₁.lTensor G - f₂.lTensor G := by ext; simp

/--
lemma `lTensor_comp` / 引理 `lTensor_comp`

English:
lemma lTensor_comp
  given: (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E)
  proof: by ext; simp [LinearMap.lTensor_comp]

中文:
引理 lTensor_comp
  条件: (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E)
  证明: by ext; simp [LinearMap.lTensor_comp]

Depends on / 依赖: LinearMap, LinearMap.lTensor_comp, lTensor_comp
-/
lemma lTensor_comp (f₁ : E ->L[𝕜] F) (f₂ : H ->L[𝕜] E) :
    (f₁ ∘L f₂).lTensor G = f₁.lTensor G ∘L f₂.lTensor G := by ext; simp [LinearMap.lTensor_comp]

/--
lemma `lTensor_mul` / 引理 `lTensor_mul`

English:
lemma lTensor_mul
  given: (f₁ f₂ : E ->L[𝕜] E)
  statement: (f₁ * f₂).lTensor G = f₁.lTensor G * f₂.lTensor G
  proof: lTensor_comp _ _ _

中文:
引理 lTensor_mul
  条件: (f₁ f₂ : E ->L[𝕜] E)
  结论: (f₁ * f₂).lTensor G = f₁.lTensor G * f₂.lTensor G
  证明: lTensor_comp _ _ _

Depends on / 依赖: lTensor_comp
-/
lemma lTensor_mul (f₁ f₂ : E ->L[𝕜] E) : (f₁ * f₂).lTensor G = f₁.lTensor G * f₂.lTensor G :=
  lTensor_comp _ _ _

/--
lemma `lTensor_pow` / 引理 `lTensor_pow`

English:
lemma lTensor_pow
  given: (f : E ->L[𝕜] E) (n : Nat)
  statement: (f ^ n).lTensor G = (f.lTensor G) ^ n
  proof: by
  simp [← coe_inj]

中文:
引理 lTensor_pow
  条件: (f : E ->L[𝕜] E) (n : 自然数)
  结论: (f ^ n).lTensor G = (f.lTensor G) ^ n
  证明: by
  simp [← coe_inj]
-/
@[simp] lemma lTensor_pow (f : E ->L[𝕜] E) (n : Nat) : (f ^ n).lTensor G = (f.lTensor G) ^ n := by
  simp [← coe_inj]

end ContinuousLinearMap

namespace TensorProduct

/--
Definition of `mapL` / `mapL` 的定义

English:
definition mapL
  signature: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  body: f.rTensor H ∘L g.lTensor E

中文:
定义 mapL
  签名: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  定义体: f.rTensor H ∘L g.lTensor E

Depends on / 依赖: f.rTensor, g.lTensor, lTensor, rTensor
-/
noncomputable def mapL (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : (E otimes[𝕜] G) ->L[𝕜] (F otimes[𝕜] H) :=
  f.rTensor H ∘L g.lTensor E

/--
theorem `norm_mapL_le` / 定理 `norm_mapL_le`

English:
theorem norm_mapL_le
  given: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  statement: ‖mapL f g‖ <= ‖f‖ * ‖g‖
  proof: by
  grw [mapL, ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.norm_rTensor_le,
    ContinuousLinearMap.norm_lTensor_le]

中文:
定理 norm_mapL_le
  条件: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  结论: ‖mapL f g‖ <= ‖f‖ * ‖g‖
  证明: by
  grw [mapL, ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.norm_rTensor_le,
    ContinuousLinearMap.norm_lTensor_le]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.norm_lTensor_le, ContinuousLinearMap.norm_rTensor_le, ContinuousLinearMap.opNorm_comp_le, norm_lTensor_le, norm_rTensor_le, opNorm_comp_le
-/
theorem norm_mapL_le (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : ‖mapL f g‖ <= ‖f‖ * ‖g‖ := by
  grw [mapL, ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.norm_rTensor_le,
    ContinuousLinearMap.norm_lTensor_le]

/--
lemma `mapL_apply` / 引理 `mapL_apply`

English:
lemma mapL_apply
  given: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) (x)
  proof: by
  simp [mapL, ← LinearMap.rTensor_comp_lTensor]

中文:
引理 mapL_apply
  条件: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) (x)
  证明: by
  simp [mapL, ← LinearMap.rTensor_comp_lTensor]
-/
@[simp] lemma mapL_apply (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) (x) :
    mapL f g x = map f.toLinearMap g.toLinearMap x := by
  simp [mapL, ← LinearMap.rTensor_comp_lTensor]

/--
lemma `mapL_tmul` / 引理 `mapL_tmul`

English:
lemma mapL_tmul
  given: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) (m : E) (n : G)
  proof: rfl

中文:
引理 mapL_tmul
  条件: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) (m : E) (n : G)
  证明: rfl
-/
lemma mapL_tmul (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) (m : E) (n : G) :
    mapL f g (m otimesₜ n) = f m otimesₜ g n := rfl

/--
lemma `mapL_zero_left` / 引理 `mapL_zero_left`

English:
lemma mapL_zero_left
  given: (f : E ->L[𝕜] F)
  statement: mapL (0 : G ->L[𝕜] H) f = 0
  proof: by simp [mapL]

中文:
引理 mapL_zero_left
  条件: (f : E ->L[𝕜] F)
  结论: mapL (0 : G ->L[𝕜] H) f = 0
  证明: by simp [mapL]
-/
@[simp] lemma mapL_zero_left (f : E ->L[𝕜] F) : mapL (0 : G ->L[𝕜] H) f = 0 := by simp [mapL]
/--
lemma `mapL_zero_right` / 引理 `mapL_zero_right`

English:
lemma mapL_zero_right
  given: (f : E ->L[𝕜] F)
  statement: mapL f (0 : G ->L[𝕜] H) = 0
  proof: by simp [mapL]

中文:
引理 mapL_zero_right
  条件: (f : E ->L[𝕜] F)
  结论: mapL f (0 : G ->L[𝕜] H) = 0
  证明: by simp [mapL]
-/
@[simp] lemma mapL_zero_right (f : E ->L[𝕜] F) : mapL f (0 : G ->L[𝕜] H) = 0 := by simp [mapL]
/--
lemma `mapL_id_id` / 引理 `mapL_id_id`

English:
lemma mapL_id_id
  statement: mapL (.id 𝕜 E) (.id 𝕜 G) = .id 𝕜 _
  proof: by simp [mapL]

中文:
引理 mapL_id_id
  结论: mapL (.id 𝕜 E) (.id 𝕜 G) = .id 𝕜 _
  证明: by simp [mapL]
-/
@[simp] lemma mapL_id_id : mapL (.id 𝕜 E) (.id 𝕜 G) = .id 𝕜 _ := by simp [mapL]

/--
lemma `mapL_comp_commIsometry` / 引理 `mapL_comp_commIsometry`

English:
lemma mapL_comp_commIsometry
  given: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  proof: by ext; simp [map_comm]

中文:
引理 mapL_comp_commIsometry
  条件: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  证明: by ext; simp [map_comm]

Depends on / 依赖: map_comm
-/
lemma mapL_comp_commIsometry (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) :
    mapL f g ∘L commIsometry 𝕜 G E = commIsometry 𝕜 H F ∘L mapL g f := by ext; simp [map_comm]

/--
lemma `mapL_add_left` / 引理 `mapL_add_left`

English:
lemma mapL_add_left
  given: (f₁ f₂ : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  proof: by ext; simp [map_add_left]

中文:
引理 mapL_add_left
  条件: (f₁ f₂ : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  证明: by ext; simp [map_add_left]

Depends on / 依赖: map_add_left
-/
lemma mapL_add_left (f₁ f₂ : E ->L[𝕜] F) (g : G ->L[𝕜] H) :
    mapL (f₁ + f₂) g = mapL f₁ g + mapL f₂ g := by ext; simp [map_add_left]

/--
lemma `mapL_add_right` / 引理 `mapL_add_right`

English:
lemma mapL_add_right
  given: (f : E ->L[𝕜] F) (g₁ g₂ : G ->L[𝕜] H)
  proof: by ext; simp [map_add_right]

中文:
引理 mapL_add_right
  条件: (f : E ->L[𝕜] F) (g₁ g₂ : G ->L[𝕜] H)
  证明: by ext; simp [map_add_right]

Depends on / 依赖: map_add_right
-/
lemma mapL_add_right (f : E ->L[𝕜] F) (g₁ g₂ : G ->L[𝕜] H) :
    mapL f (g₁ + g₂) = mapL f g₁ + mapL f g₂ := by ext; simp [map_add_right]

/--
lemma `mapL_smul_left` / 引理 `mapL_smul_left`

English:
lemma mapL_smul_left
  given: (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  proof: by ext; simp [map_smul_left]

中文:
引理 mapL_smul_left
  条件: (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  证明: by ext; simp [map_smul_left]

Depends on / 依赖: map_smul_left
-/
lemma mapL_smul_left (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) :
    mapL (r • f) g = r • mapL f g := by ext; simp [map_smul_left]

/--
lemma `mapL_smul_right` / 引理 `mapL_smul_right`

English:
lemma mapL_smul_right
  given: (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  proof: by ext; simp [map_smul_right]

中文:
引理 mapL_smul_right
  条件: (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  证明: by ext; simp [map_smul_right]

Depends on / 依赖: map_smul_right
-/
lemma mapL_smul_right (r : 𝕜) (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) :
    mapL f (r • g) = r • mapL f g := by ext; simp [map_smul_right]

/--
lemma `toLinearMap_mapL` / 引理 `toLinearMap_mapL`

English:
lemma toLinearMap_mapL
  given: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  proof: by ext; simp

中文:
引理 toLinearMap_mapL
  条件: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  证明: by ext; simp
-/
@[simp] lemma toLinearMap_mapL (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) :
    (mapL f g).toLinearMap = map f g := by ext; simp

/--
lemma `toContinuousLinearMap_mapIsometry` / 引理 `toContinuousLinearMap_mapIsometry`

English:
lemma toContinuousLinearMap_mapIsometry
  given: (f : E ->ₗᵢ[𝕜] F) (g : G ->ₗᵢ[𝕜] H)
  proof: by
  ext; simp

中文:
引理 toContinuousLinearMap_mapIsometry
  条件: (f : E ->ₗᵢ[𝕜] F) (g : G ->ₗᵢ[𝕜] H)
  证明: by
  ext; simp
-/
@[simp] lemma toContinuousLinearMap_mapIsometry (f : E ->ₗᵢ[𝕜] F) (g : G ->ₗᵢ[𝕜] H) :
    (mapIsometry f g).toContinuousLinearMap =
      mapL f.toContinuousLinearMap g.toContinuousLinearMap := by
  ext; simp

section comp

variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [NormedAddCommGroup B]
  [InnerProductSpace 𝕜 B]

/--
lemma `mapL_comp` / 引理 `mapL_comp`

English:
lemma mapL_comp
  given: (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E) (g₁ : G ->L[𝕜] H) (g₂ : B ->L[𝕜] G)
  proof: by ext; simp [map_map]

中文:
引理 mapL_comp
  条件: (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E) (g₁ : G ->L[𝕜] H) (g₂ : B ->L[𝕜] G)
  证明: by ext; simp [map_map]

Depends on / 依赖: map_map
-/
lemma mapL_comp (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E) (g₁ : G ->L[𝕜] H) (g₂ : B ->L[𝕜] G) :
    mapL (f₁ ∘L f₂) (g₁ ∘L g₂) = mapL f₁ g₁ ∘L mapL f₂ g₂ := by ext; simp [map_map]

/--
lemma `mapL_mul` / 引理 `mapL_mul`

English:
lemma mapL_mul
  given: (f₁ f₂ : E ->L[𝕜] E) (g₁ g₂ : F ->L[𝕜] F)
  proof: mapL_comp _ _ _ _

中文:
引理 mapL_mul
  条件: (f₁ f₂ : E ->L[𝕜] E) (g₁ g₂ : F ->L[𝕜] F)
  证明: mapL_comp _ _ _ _

Depends on / 依赖: mapL_comp
-/
lemma mapL_mul (f₁ f₂ : E ->L[𝕜] E) (g₁ g₂ : F ->L[𝕜] F) :
    mapL (f₁ * f₂) (g₁ * g₂) = mapL f₁ g₁ * mapL f₂ g₂ := mapL_comp _ _ _ _

/--
lemma `mapL_pow` / 引理 `mapL_pow`

English:
lemma mapL_pow
  given: (f : E ->L[𝕜] E) (g : F ->L[𝕜] F) (n : Nat)
  proof: by simp [← ContinuousLinearMap.coe_inj]

中文:
引理 mapL_pow
  条件: (f : E ->L[𝕜] E) (g : F ->L[𝕜] F) (n : 自然数)
  证明: by simp [← ContinuousLinearMap.coe_inj]
-/
@[simp] lemma mapL_pow (f : E ->L[𝕜] E) (g : F ->L[𝕜] F) (n : Nat) :
    (mapL f g) ^ n = mapL (f ^ n) (g ^ n) := by simp [← ContinuousLinearMap.coe_inj]

/--
lemma `_root_.ContinuousLinearMap.mapL_comp_rTensor` / 引理 `_root_.ContinuousLinearMap.mapL_comp_rTensor`

English:
lemma _root_.ContinuousLinearMap.mapL_comp_rTensor
  statement: (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E)
  proof: by ext; simp

中文:
引理 _root_.ContinuousLinearMap.mapL_comp_rTensor
  结论: (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E)
  证明: by ext; simp
-/
@[simp] lemma _root_.ContinuousLinearMap.mapL_comp_rTensor (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E)
    (g : G ->L[𝕜] H) : mapL f₁ g ∘L f₂.rTensor G = mapL (f₁ ∘L f₂) g := by ext; simp

/--
lemma `_root_.ContinuousLinearMap.mapL_comp_lTensor` / 引理 `_root_.ContinuousLinearMap.mapL_comp_lTensor`

English:
lemma _root_.ContinuousLinearMap.mapL_comp_lTensor
  statement: (f : E ->L[𝕜] F) (g₁ : G ->L[𝕜] H)
  proof: by ext; simp

中文:
引理 _root_.ContinuousLinearMap.mapL_comp_lTensor
  结论: (f : E ->L[𝕜] F) (g₁ : G ->L[𝕜] H)
  证明: by ext; simp
-/
@[simp] lemma _root_.ContinuousLinearMap.mapL_comp_lTensor (f : E ->L[𝕜] F) (g₁ : G ->L[𝕜] H)
    (g₂ : A ->L[𝕜] G) : mapL f g₁ ∘L g₂.lTensor E = mapL f (g₁ ∘L g₂) := by ext; simp

/--
lemma `_root_.ContinuousLinearMap.rTensor_comp_mapL` / 引理 `_root_.ContinuousLinearMap.rTensor_comp_mapL`

English:
lemma _root_.ContinuousLinearMap.rTensor_comp_mapL
  statement: (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E)
  proof: by ext; simp

中文:
引理 _root_.ContinuousLinearMap.rTensor_comp_mapL
  结论: (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E)
  证明: by ext; simp
-/
@[simp] lemma _root_.ContinuousLinearMap.rTensor_comp_mapL (f₁ : E ->L[𝕜] F) (f₂ : A ->L[𝕜] E)
    (g : G ->L[𝕜] H) : f₁.rTensor H ∘L mapL f₂ g = mapL (f₁ ∘L f₂) g := by ext; simp

/--
lemma `_root_.ContinuousLinearMap.lTensor_comp_mapL` / 引理 `_root_.ContinuousLinearMap.lTensor_comp_mapL`

English:
lemma _root_.ContinuousLinearMap.lTensor_comp_mapL
  statement: (f : E ->L[𝕜] F) (g₁ : G ->L[𝕜] H)
  proof: by ext; simp

中文:
引理 _root_.ContinuousLinearMap.lTensor_comp_mapL
  结论: (f : E ->L[𝕜] F) (g₁ : G ->L[𝕜] H)
  证明: by ext; simp
-/
@[simp] lemma _root_.ContinuousLinearMap.lTensor_comp_mapL (f : E ->L[𝕜] F) (g₁ : G ->L[𝕜] H)
    (g₂ : A ->L[𝕜] G) : g₁.lTensor F ∘L mapL f g₂ = mapL f (g₁ ∘L g₂) := by ext; simp

end comp

variable (G) in
/--
theorem `_root_.ContinuousLinearMap.rTensor_eq_mapL` / 定理 `_root_.ContinuousLinearMap.rTensor_eq_mapL`

English:
theorem _root_.ContinuousLinearMap.rTensor_eq_mapL
  given: (f : E ->L[𝕜] F)
  proof: by simp [mapL]

中文:
定理 _root_.ContinuousLinearMap.rTensor_eq_mapL
  条件: (f : E ->L[𝕜] F)
  证明: by simp [mapL]
-/
theorem _root_.ContinuousLinearMap.rTensor_eq_mapL (f : E ->L[𝕜] F) :
    f.rTensor G = mapL f (.id 𝕜 G) := by simp [mapL]

variable (E) in
/--
theorem `_root_.ContinuousLinearMap.lTensor_eq_mapL` / 定理 `_root_.ContinuousLinearMap.lTensor_eq_mapL`

English:
theorem _root_.ContinuousLinearMap.lTensor_eq_mapL
  given: (g : G ->L[𝕜] H)
  proof: by simp [mapL]

中文:
定理 _root_.ContinuousLinearMap.lTensor_eq_mapL
  条件: (g : G ->L[𝕜] H)
  证明: by simp [mapL]
-/
theorem _root_.ContinuousLinearMap.lTensor_eq_mapL (g : G ->L[𝕜] H) :
    g.lTensor E = mapL (.id 𝕜 E) g := by simp [mapL]

/--
lemma `_root_.ContinuousLinearMap.lTensor_comp_rTensor` / 引理 `_root_.ContinuousLinearMap.lTensor_comp_rTensor`

English:
lemma _root_.ContinuousLinearMap.lTensor_comp_rTensor
  given: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  proof: by ext; simp [← LinearMap.lTensor_comp_rTensor]

中文:
引理 _root_.ContinuousLinearMap.lTensor_comp_rTensor
  条件: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  证明: by ext; simp [← LinearMap.lTensor_comp_rTensor]
-/
@[simp] lemma _root_.ContinuousLinearMap.lTensor_comp_rTensor (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) :
    f.lTensor H ∘L g.rTensor E = mapL g f := by ext; simp [← LinearMap.lTensor_comp_rTensor]

/--
lemma `_root_.ContinuousLinearMap.rTensor_comp_lTensor` / 引理 `_root_.ContinuousLinearMap.rTensor_comp_lTensor`

English:
lemma _root_.ContinuousLinearMap.rTensor_comp_lTensor
  given: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  proof: rfl

中文:
引理 _root_.ContinuousLinearMap.rTensor_comp_lTensor
  条件: (f : E ->L[𝕜] F) (g : G ->L[𝕜] H)
  证明: rfl
-/
@[simp] lemma _root_.ContinuousLinearMap.rTensor_comp_lTensor (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) :
    f.rTensor H ∘L g.lTensor E = mapL f g := rfl

/--
theorem `adjoint_mapL` / 定理 `adjoint_mapL`

English:
theorem adjoint_mapL
  statement: [CompleteSpace E] [CompleteSpace G] [CompleteSpace (E otimes[𝕜] G)]
  proof: by
apply ContinuousLinearMap.coe_inj.mp ext' ?_
  simp [TensorProduct.ext_iff_inner_right, ContinuousLinearMap.adjoint_inner_left]

中文:
定理 adjoint_mapL
  结论: [CompleteSpace E] [CompleteSpace G] [CompleteSpace (E otimes[𝕜] G)]
  证明: by
apply ContinuousLinearMap.coe_inj.mp ext' ?_
  simp [TensorProduct.ext_iff_inner_right, ContinuousLinearMap.adjoint_inner_left]
-/
@[simp] theorem adjoint_mapL [CompleteSpace E] [CompleteSpace G] [CompleteSpace (E otimes[𝕜] G)]
    [CompleteSpace F] [CompleteSpace H] [CompleteSpace (F otimes[𝕜] H)]
    (f : E ->L[𝕜] F) (g : G ->L[𝕜] H) : (mapL f g).adjoint = mapL f.adjoint g.adjoint := by
apply ContinuousLinearMap.coe_inj.mp ext' ?_
  simp [TensorProduct.ext_iff_inner_right, ContinuousLinearMap.adjoint_inner_left]

set_option backward.isDefEq.respectTransparency.types false in
variable (G) in
/--
theorem `_root_.ContinuousLinearMap.adjoint_rTensor` / 定理 `_root_.ContinuousLinearMap.adjoint_rTensor`

English:
theorem _root_.ContinuousLinearMap.adjoint_rTensor
  statement: [CompleteSpace E] [CompleteSpace G]
  proof: by simp [ContinuousLinearMap.rTensor_eq_mapL]

中文:
定理 _root_.ContinuousLinearMap.adjoint_rTensor
  结论: [CompleteSpace E] [CompleteSpace G]
  证明: by simp [ContinuousLinearMap.rTensor_eq_mapL]
-/
@[simp] theorem _root_.ContinuousLinearMap.adjoint_rTensor [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E otimes[𝕜] G)] [CompleteSpace (F otimes[𝕜] G)] [CompleteSpace F] (f : E ->L[𝕜] F) :
    (f.rTensor G).adjoint = f.adjoint.rTensor G := by simp [ContinuousLinearMap.rTensor_eq_mapL]

set_option backward.isDefEq.respectTransparency.types false in
variable (E) in
/--
theorem `_root_.ContinuousLinearMap.adjoint_lTensor` / 定理 `_root_.ContinuousLinearMap.adjoint_lTensor`

English:
theorem _root_.ContinuousLinearMap.adjoint_lTensor
  statement: [CompleteSpace E] [CompleteSpace G]
  proof: by simp [ContinuousLinearMap.lTensor_eq_mapL]

中文:
定理 _root_.ContinuousLinearMap.adjoint_lTensor
  结论: [CompleteSpace E] [CompleteSpace G]
  证明: by simp [ContinuousLinearMap.lTensor_eq_mapL]
-/
@[simp] theorem _root_.ContinuousLinearMap.adjoint_lTensor [CompleteSpace E] [CompleteSpace G]
    [CompleteSpace (E otimes[𝕜] H)] [CompleteSpace (E otimes[𝕜] G)] [CompleteSpace H] (g : G ->L[𝕜] H) :
    (g.lTensor E).adjoint = g.adjoint.lTensor E := by simp [ContinuousLinearMap.lTensor_eq_mapL]

open LinearMap

/--
theorem `adjoint_map` / 定理 `adjoint_map`

English:
theorem adjoint_map
  statement: [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
  proof: ext' fun _ _ => by simp [TensorProduct.ext_iff_inner_right, adjoint_inner_left]

中文:
定理 adjoint_map
  结论: [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
  证明: ext' fun _ _ => by simp [TensorProduct.ext_iff_inner_right, adjoint_inner_left]
-/
@[simp] theorem adjoint_map [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]
    [FiniteDimensional 𝕜 H] (f : E ->ₗ[𝕜] F) (g : G ->ₗ[𝕜] H) :
    (map f g).adjoint = map f.adjoint g.adjoint :=
  ext' fun _ _ => by simp [TensorProduct.ext_iff_inner_right, adjoint_inner_left]

/--
theorem `_root_.LinearMap.adjoint_rTensor` / 定理 `_root_.LinearMap.adjoint_rTensor`

English:
theorem _root_.LinearMap.adjoint_rTensor
  statement: [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  proof: by simp [rTensor]

中文:
定理 _root_.LinearMap.adjoint_rTensor
  结论: [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  证明: by simp [rTensor]
-/
@[simp] theorem _root_.LinearMap.adjoint_rTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E ->ₗ[𝕜] F) :
    (f.rTensor G).adjoint = f.adjoint.rTensor G := by simp [rTensor]

/--
theorem `_root_.LinearMap.adjoint_lTensor` / 定理 `_root_.LinearMap.adjoint_lTensor`

English:
theorem _root_.LinearMap.adjoint_lTensor
  statement: [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  proof: by simp [lTensor]

中文:
定理 _root_.LinearMap.adjoint_lTensor
  结论: [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  证明: by simp [lTensor]
-/
@[simp] theorem _root_.LinearMap.adjoint_lTensor [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    [FiniteDimensional 𝕜 G] (f : E ->ₗ[𝕜] F) :
    (f.lTensor G).adjoint = f.adjoint.lTensor G := by simp [lTensor]

/--
theorem `ext_iff_inner_right_threefold'` / 定理 `ext_iff_inner_right_threefold'`

English:
theorem ext_iff_inner_right_threefold'
  given: {x y : E otimes[𝕜] (F otimes[𝕜] G)}
  proof: by
  simp only [← (assocIsometry 𝕜 E F G).symm.injective.eq_iff,
    ext_iff_inner_right_threefold, LinearIsometryEquiv.inner_map_eq_flip]
  simp

中文:
定理 ext_iff_inner_right_threefold'
  条件: {x y : E otimes[𝕜] (F otimes[𝕜] G)}
  证明: by
  simp only [← (assocIsometry 𝕜 E F G).symm.injective.eq_iff,
    ext_iff_inner_right_threefold, LinearIsometryEquiv.inner_map_eq_flip]
  simp

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.inner_map_eq_flip, assocIsometry, eq_iff, ext_iff_inner_right_threefold, injective, inner_map_eq_flip, symm.injective.eq_iff
-/
theorem ext_iff_inner_right_threefold' {x y : E otimes[𝕜] (F otimes[𝕜] G)} :
    x = y ↔ forall a b c, inner 𝕜 x (a otimesₜ[𝕜] (b otimesₜ[𝕜] c)) = inner 𝕜 y (a otimesₜ[𝕜] (b otimesₜ[𝕜] c)) := by
  simp only [← (assocIsometry 𝕜 E F G).symm.injective.eq_iff,
    ext_iff_inner_right_threefold, LinearIsometryEquiv.inner_map_eq_flip]
  simp

/--
theorem `ext_iff_inner_left_threefold'` / 定理 `ext_iff_inner_left_threefold'`

English:
theorem ext_iff_inner_left_threefold'
  given: {x y : E otimes[𝕜] (F otimes[𝕜] G)}
  proof: by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold' (x := x) (y := y)

中文:
定理 ext_iff_inner_left_threefold'
  条件: {x y : E otimes[𝕜] (F otimes[𝕜] G)}
  证明: by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold' (x := x) (y := y)

Depends on / 依赖: ext_iff_inner_right_threefold, inner_conj_symm, starRingEnd_apply, star_inj
-/
theorem ext_iff_inner_left_threefold' {x y : E otimes[𝕜] (F otimes[𝕜] G)} :
    x = y ↔ forall a b c, inner 𝕜 (a otimesₜ[𝕜] (b otimesₜ[𝕜] c)) x = inner 𝕜 (a otimesₜ[𝕜] (b otimesₜ[𝕜] c)) y := by
  simpa only [← inner_conj_symm x, ← inner_conj_symm y, starRingEnd_apply, star_inj] using
    ext_iff_inner_right_threefold' (x := x) (y := y)

end TensorProduct

section orthonormal
variable {ι₁ ι₂ : Type*}

open Module

/--
theorem `Orthonormal.tmul` / 定理 `Orthonormal.tmul`

English:
theorem Orthonormal.tmul
  proof: by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

中文:
定理 Orthonormal.tmul
  证明: by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

Depends on / 依赖: and_comm, classical, ite_and, orthonormal_iff_ite, orthonormal_iff_ite.mp
-/
theorem Orthonormal.tmul
    {b₁ : ι₁ -> E} {b₂ : ι₂ -> F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 fun i : ι₁ × ι₂ => b₁ i.1 otimesₜ[𝕜] b₂ i.2 := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [orthonormal_iff_ite.mp, hb₁, hb₂, ← ite_and, and_comm]

/--
theorem `Orthonormal.basisTensorProduct` / 定理 `Orthonormal.basisTensorProduct`

English:
theorem Orthonormal.basisTensorProduct
  proof: by
  convert! hb₁.tmul hb₂
  exact b₁.tensorProduct_apply' b₂ _

中文:
定理 Orthonormal.basisTensorProduct
  证明: by
  convert! hb₁.tmul hb₂
  exact b₁.tensorProduct_apply' b₂ _

Depends on / 依赖: convert, tensorProduct_apply
-/
theorem Orthonormal.basisTensorProduct
    {b₁ : Basis ι₁ 𝕜 E} {b₂ : Basis ι₂ 𝕜 F} (hb₁ : Orthonormal 𝕜 b₁) (hb₂ : Orthonormal 𝕜 b₂) :
    Orthonormal 𝕜 (b₁.tensorProduct b₂) := by
  convert! hb₁.tmul hb₂
  exact b₁.tensorProduct_apply' b₂ _

namespace OrthonormalBasis
variable [Fintype ι₁] [Fintype ι₂]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def tensorProduct
  body: (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (b₁.orthonormal.basisTensorProduct b₂.orthonormal)

@[simp]

中文:
定义 noncomputable
  签名: def tensorProduct
  定义体: (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (b₁.orthonormal.basisTensorProduct b₂.orthonormal)

@[simp]
-/
protected noncomputable def tensorProduct
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    OrthonormalBasis (ι₁ × ι₂) 𝕜 (E otimes[𝕜] F) :=
  (b₁.toBasis.tensorProduct b₂.toBasis).toOrthonormalBasis
    (b₁.orthonormal.basisTensorProduct b₂.orthonormal)

@[simp]
/--
lemma `tensorProduct_apply` / 引理 `tensorProduct_apply`

English:
lemma tensorProduct_apply
  proof: by simp [OrthonormalBasis.tensorProduct]

中文:
引理 tensorProduct_apply
  证明: by simp [OrthonormalBasis.tensorProduct]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.tensorProduct, tensorProduct
-/
lemma tensorProduct_apply
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁) (j : ι₂) :
    b₁.tensorProduct b₂ (i, j) = b₁ i otimesₜ[𝕜] b₂ j := by simp [OrthonormalBasis.tensorProduct]

/--
lemma `tensorProduct_apply'` / 引理 `tensorProduct_apply'`

English:
lemma tensorProduct_apply'
  proof: tensorProduct_apply _ _ _ _

@[simp]

中文:
引理 tensorProduct_apply'
  证明: tensorProduct_apply _ _ _ _

@[simp]

Depends on / 依赖: tensorProduct_apply
-/
lemma tensorProduct_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (i : ι₁ × ι₂) :
    b₁.tensorProduct b₂ i = b₁ i.1 otimesₜ[𝕜] b₂ i.2 := tensorProduct_apply _ _ _ _

@[simp]
/--
lemma `tensorProduct_repr_tmul_apply` / 引理 `tensorProduct_repr_tmul_apply`

English:
lemma tensorProduct_repr_tmul_apply
  statement: (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  proof: by
  simp [OrthonormalBasis.tensorProduct]

中文:
引理 tensorProduct_repr_tmul_apply
  结论: (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  证明: by
  simp [OrthonormalBasis.tensorProduct]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.tensorProduct, tensorProduct
-/
lemma tensorProduct_repr_tmul_apply (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
    (x : E) (y : F) (i : ι₁) (j : ι₂) :
    (b₁.tensorProduct b₂).repr (x otimesₜ[𝕜] y) (i, j) = b₂.repr y j * b₁.repr x i := by
  simp [OrthonormalBasis.tensorProduct]

/--
lemma `tensorProduct_repr_tmul_apply'` / 引理 `tensorProduct_repr_tmul_apply'`

English:
lemma tensorProduct_repr_tmul_apply'
  proof: tensorProduct_repr_tmul_apply _ _ _ _ _ _

@[simp]

中文:
引理 tensorProduct_repr_tmul_apply'
  证明: tensorProduct_repr_tmul_apply _ _ _ _ _ _

@[simp]

Depends on / 依赖: tensorProduct_repr_tmul_apply
-/
lemma tensorProduct_repr_tmul_apply'
    (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) (x : E) (y : F) (i : ι₁ × ι₂) :
    (b₁.tensorProduct b₂).repr (x otimesₜ[𝕜] y) i = b₂.repr y i.2 * b₁.repr x i.1 :=
  tensorProduct_repr_tmul_apply _ _ _ _ _ _

@[simp]
/--
lemma `toBasis_tensorProduct` / 引理 `toBasis_tensorProduct`

English:
lemma toBasis_tensorProduct
  given: (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  proof: by
  simp [OrthonormalBasis.tensorProduct]

中文:
引理 toBasis_tensorProduct
  条件: (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F)
  证明: by
  simp [OrthonormalBasis.tensorProduct]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.tensorProduct, tensorProduct
-/
lemma toBasis_tensorProduct (b₁ : OrthonormalBasis ι₁ 𝕜 E) (b₂ : OrthonormalBasis ι₂ 𝕜 F) :
    (b₁.tensorProduct b₂).toBasis = b₁.toBasis.tensorProduct b₂.toBasis := by
  simp [OrthonormalBasis.tensorProduct]

end OrthonormalBasis
end orthonormal
