/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Inner product space structure on exterior powers

Given a real inner product space `E`, we construct a canonical inner product on `⋀[ℝ]^n E`
via the Gram determinant formula: on decomposable elements,
`⟪v₁ ∧ ⋯ ∧ vₙ, w₁ ∧ ⋯ ∧ wₙ⟫ = det (⟪vⱼ, wᵢ⟫)ᵢⱼ`.

## Main results

- `exteriorPower.inner_ιMulti_ιMulti`: The inner product on decomposable elements equals the
  Gram determinant.
- `exteriorPower.inner_ιMulti_self`: `⟪v₁ ∧ ⋯ ∧ vₙ, v₁ ∧ ⋯ ∧ vₙ⟫ = det (gram ℝ v)`.
- `OrthonormalBasis.exteriorPower`: An orthonormal basis of `E` induces an orthonormal basis
  of `⋀[ℝ]^n E`.

## Future work

- Generalize to `RCLike 𝕜`. To define `innerProductForm` in this case, we would probably
  want a semilinear generalization of `exteriorPower.map`, which in turn requires
  generalizing `AlternatingMap` to the semilinear setting.
- Remove the `FiniteDimensional` hypothesis from the `InnerProductSpace` instance.
  Currently the proofs of `re_inner_nonneg` and `definite` require finite dimension, because
  we need to choose an orthonormal basis of `E`. But we can reduce the general case to
  the finite-dimensional case by noticing that any `x : ⋀[𝕜]^n E` is contained in some
  `⋀[𝕜]^n F` for a finite-dimensional subspace `F ≤ E`.

-/

@[expose] public noncomputable section

namespace exteriorPower

open RealInnerProductSpace Matrix

variable {n : Nat} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

/--
Definition of `innerProductForm` / `innerProductForm` 的定义

English:
definition innerProductForm
  signature: : ⋀[Real]^n E ->ₗ[Real] ⋀[Real]^n E ->ₗ[Real] Real
  body: pairingDual Real E n ∘ₗ map n (innerₗ E)

中文:
定义 innerProductForm
  签名: : ⋀[实数]^n E ->ₗ[实数] ⋀[实数]^n E ->ₗ[实数] 实数
  定义体: pairingDual Real E n ∘ₗ map n (innerₗ E)
-/
private def innerProductForm : ⋀[Real]^n E ->ₗ[Real] ⋀[Real]^n E ->ₗ[Real] Real :=
  pairingDual Real E n ∘ₗ map n (innerₗ E)

/--
lemma `innerProductForm_ιMulti_ιMulti` / 引理 `innerProductForm_ιMulti_ιMulti`

English:
lemma innerProductForm_ιMulti_ιMulti
  given: (x y : Fin n -> E)
  proof: by
  simp [innerProductForm]

@[simp]

中文:
引理 innerProductForm_ιMulti_ιMulti
  条件: (x y : Fin n -> E)
  证明: by
  simp [innerProductForm]

@[simp]
-/
private lemma innerProductForm_ιMulti_ιMulti (x y : Fin n -> E) :
    innerProductForm (ιMulti Real n x) (ιMulti Real n y) = det (of fun i j => ⟪x j, y i⟫) := by
  simp [innerProductForm]

@[simp]
/--
lemma `innerProductForm_ιMulti_self` / 引理 `innerProductForm_ιMulti_self`

English:
lemma innerProductForm_ιMulti_self
  given: (x : Fin n -> E)
  proof: by
  simp [gram, innerProductForm_ιMulti_ιMulti, real_inner_comm]

中文:
引理 innerProductForm_ιMulti_self
  条件: (x : Fin n -> E)
  证明: by
  simp [gram, innerProductForm_ιMulti_ιMulti, real_inner_comm]
-/
private lemma innerProductForm_ιMulti_self (x : Fin n -> E) :
    innerProductForm (ιMulti Real n x) (ιMulti Real n x) = det (gram Real x) := by
  simp [gram, innerProductForm_ιMulti_ιMulti, real_inner_comm]

/--
lemma `flip_innerProductForm` / 引理 `flip_innerProductForm`

English:
lemma flip_innerProductForm
  proof: by
  apply linearMap_ext
  ext
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
    innerProductForm_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext
  exact real_inner_comm _ _

中文:
引理 flip_innerProductForm
  证明: by
  apply linearMap_ext
  ext
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
    innerProductForm_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext
  exact real_inner_comm _ _
-/
private lemma flip_innerProductForm :
    (innerProductForm (E := E) (n := n)).flip = innerProductForm := by
  apply linearMap_ext
  ext
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply,
    innerProductForm_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext
  exact real_inner_comm _ _

/--
lemma `innerProductForm_symm` / 引理 `innerProductForm_symm`

English:
lemma innerProductForm_symm
  given: (x y : ⋀[Real]^n E)
  proof: congr($flip_innerProductForm x y)

@[simp]

中文:
引理 innerProductForm_symm
  条件: (x y : ⋀[实数]^n E)
  证明: congr($flip_innerProductForm x y)

@[simp]
-/
private lemma innerProductForm_symm (x y : ⋀[Real]^n E) :
    innerProductForm y x = innerProductForm x y :=
  congr($flip_innerProductForm x y)

@[simp]
/--
lemma `innerProductForm_ιMulti_family_of_orthonormal` / 引理 `innerProductForm_ιMulti_family_of_orthonormal`

English:
lemma innerProductForm_ιMulti_family_of_orthonormal
  statement: {ι : Type*} [LinearOrder ι] {v : ι -> E}
  proof: by
  simp only [ιMulti_family]
  split_ifs with h
  · subst h
    simp [gram_eq_one_iff_orthonormal.mpr (hv.comp _ (RelEmbedding.injective _))]
  · rw [innerProductForm_ιMulti_ιMulti]
    obtain ⟨x, hxt, hxs⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp (.symm h)
    simp only [Set.mem_rang

中文:
引理 innerProductForm_ιMulti_family_of_orthonormal
  结论: {ι : 类型} [LinearOrder ι] {v : ι -> E}
  证明: by
  simp only [ιMulti_family]
  split_ifs with h
  · subst h
    simp [gram_eq_one_iff_orthonormal.mpr (hv.comp _ (RelEmbedding.injective _))]
  · rw [innerProductForm_ιMulti_ιMulti]
    obtain ⟨x, hxt, hxs⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp (.symm h)
    simp only [Set.mem_rang
-/
private lemma innerProductForm_ιMulti_family_of_orthonormal {ι : Type*} [LinearOrder ι] {v : ι -> E}
    (hv : Orthonormal Real v) (s t : Set.powersetCard ι n) :
    innerProductForm (ιMulti_family Real n v s) (ιMulti_family Real n v t) = if s = t then 1 else 0 := by
  simp only [ιMulti_family]
  split_ifs with h
  · subst h
    simp [gram_eq_one_iff_orthonormal.mpr (hv.comp _ (RelEmbedding.injective _))]
  · rw [innerProductForm_ιMulti_ιMulti]
    obtain ⟨x, hxt, hxs⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp (.symm h)
    simp only [Set.mem_range, not_exists,
      ← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem] at hxs hxt
    obtain ⟨i, rfl⟩ := hxt
    exact det_eq_zero_of_row_eq_zero i (fun j => hv.inner_eq_zero (hxs j))

/--
lemma `innerProductForm_eq_sum` / 引理 `innerProductForm_eq_sum`

English:
lemma innerProductForm_eq_sum
  statement: {ι : Type*} [Fintype ι] [LinearOrder ι]
  proof: by
  conv_lhs =>
    rw [← (b.toBasis.exteriorPower n).sum_repr x]; rw [← (b.toBasis.exteriorPower n).sum_repr y]
  simp

中文:
引理 innerProductForm_eq_sum
  结论: {ι : 类型} [Fintype ι] [LinearOrder ι]
  证明: by
  conv_lhs =>
    rw [← (b.toBasis.exteriorPower n).sum_repr x]; rw [← (b.toBasis.exteriorPower n).sum_repr y]
  simp

Depends on / 依赖: NormedSpace, SubmoduleClass, SubmoduleClass.toNormedSpace, toNormedSpace
-/
private lemma innerProductForm_eq_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι Real E) (x y : ⋀[Real]^n E) :
    innerProductForm x y =
      ∑ s, (b.toBasis.exteriorPower n).repr y s * (b.toBasis.exteriorPower n).repr x s := by
  conv_lhs =>
    rw [← (b.toBasis.exteriorPower n).sum_repr x]; rw [← (b.toBasis.exteriorPower n).sum_repr y]
  simp

/--
lemma `innerProductForm_self` / 引理 `innerProductForm_self`

English:
lemma innerProductForm_self
  statement: (x : ⋀[Real]^n E) {ι : Type*} [Fintype ι] [LinearOrder ι]
  proof: by
  simp_rw [innerProductForm_eq_sum b, pow_two]

中文:
引理 innerProductForm_self
  结论: (x : ⋀[实数]^n E) {ι : 类型} [Fintype ι] [LinearOrder ι]
  证明: by
  simp_rw [innerProductForm_eq_sum b, pow_two]
-/
private lemma innerProductForm_self (x : ⋀[Real]^n E) {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι Real E) :
    innerProductForm x x = ∑ s, (b.toBasis.exteriorPower n).repr x s ^ 2 := by
  simp_rw [innerProductForm_eq_sum b, pow_two]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteDimensional
  signature: Real E] : InnerProductSpace.Core Real (⋀[Real]^n E) where
  body: innerProductForm x y
  conj_inner_symm := innerProductForm_symm
  add_left := by simp
  smul_left := by simp
  re_inner_nonneg x := by
    rw [innerProductForm_self x (stdOrthonormalBasis Real E)]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  definite x h := by
    rw [innerProductForm_self

中文:
实例 [FiniteDimensional
  签名: 实数 E] : InnerProductSpace.Core 实数 (⋀[实数]^n E) where
  定义体: innerProductForm x y
  conj_inner_symm := innerProductForm_symm
  add_left := by simp
  smul_left := by simp
  re_inner_nonneg x := by
    rw [innerProductForm_self x (stdOrthonormalBasis Real E)]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  definite x h := by
    rw [innerProductForm_self
-/
@[no_expose] instance [FiniteDimensional Real E] : InnerProductSpace.Core Real (⋀[Real]^n E) where
  inner x y := innerProductForm x y
  conj_inner_symm := innerProductForm_symm
  add_left := by simp
  smul_left := by simp
  re_inner_nonneg x := by
    rw [innerProductForm_self x (stdOrthonormalBasis Real E)]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  definite x h := by
    rw [innerProductForm_self x (stdOrthonormalBasis Real E)]; rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h
    apply Module.Basis.ext_elem ((stdOrthonormalBasis Real E).toBasis.exteriorPower n)
    simpa using h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteDimensional
  signature: Real E] : NormedAddCommGroup (⋀[Real]^n E)
  body: InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := Real)

中文:
实例 [FiniteDimensional
  签名: 实数 E] : NormedAddCommGroup (⋀[实数]^n E)
  定义体: InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := Real)

Depends on / 依赖: InnerProductSpace, InnerProductSpace.Core.toNormedAddCommGroup, NontriviallyNormedField, NontriviallyNormedField.cobounded_neBot, cobounded, cobounded_neBot, toNormedAddCommGroup
-/
instance [FiniteDimensional Real E] : NormedAddCommGroup (⋀[Real]^n E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteDimensional
  signature: Real E] : InnerProductSpace Real (⋀[Real]^n E)
  body: InnerProductSpace.ofCore _

中文:
实例 [FiniteDimensional
  签名: 实数 E] : InnerProductSpace 实数 (⋀[实数]^n E)
  定义体: InnerProductSpace.ofCore _

Depends on / 依赖: InnerProductSpace, InnerProductSpace.ofCore, NormedSpace, RealNormedSpace, RealNormedSpace.cobounded_neBot, cobounded_neBot, ofCore
-/
instance [FiniteDimensional Real E] : InnerProductSpace Real (⋀[Real]^n E) :=
  InnerProductSpace.ofCore _

/--
lemma `inner_ιMulti_ιMulti` / 引理 `inner_ιMulti_ιMulti`

English:
lemma inner_ιMulti_ιMulti
  given: [FiniteDimensional Real E] (x y : Fin n -> E)
  proof: innerProductForm_ιMulti_ιMulti x y

中文:
引理 inner_ιMulti_ιMulti
  条件: [FiniteDimensional 实数 E] (x y : Fin n -> E)
  证明: innerProductForm_ιMulti_ιMulti x y

Depends on / 依赖: Infinite, NontriviallyNormedField, NontriviallyNormedField.infinite, infinite
-/
lemma inner_ιMulti_ιMulti [FiniteDimensional Real E] (x y : Fin n -> E) :
    ⟪ιMulti Real n x, ιMulti Real n y⟫ = det (of fun i j => ⟪x j, y i⟫) :=
  innerProductForm_ιMulti_ιMulti x y

/--
lemma `inner_ιMulti_self` / 引理 `inner_ιMulti_self`

English:
lemma inner_ιMulti_self
  given: [FiniteDimensional Real E] (x : Fin n -> E)
  proof: innerProductForm_ιMulti_self x

中文:
引理 inner_ιMulti_self
  条件: [FiniteDimensional 实数 E] (x : Fin n -> E)
  证明: innerProductForm_ιMulti_self x

Depends on / 依赖: NoncompactSpace, NormedField, NormedField.noncompactSpace, noncompactSpace
-/
lemma inner_ιMulti_self [FiniteDimensional Real E] (x : Fin n -> E) :
    ⟪ιMulti Real n x, ιMulti Real n x⟫ = det (gram Real x) :=
  innerProductForm_ιMulti_self x

end exteriorPower

section OrthonormalBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
variable {I : Type*} [Fintype I] [LinearOrder I]

/--
Definition of `OrthonormalBasis.exteriorPower` / `OrthonormalBasis.exteriorPower` 的定义

English:
definition OrthonormalBasis.exteriorPower
  signature: (b : OrthonormalBasis I Real E) (n : Nat)
  body: (b.toBasis.exteriorPower n).toOrthonormalBasis by
    rw [orthonormal_iff_ite]
    intro i j
    rw [exteriorPower.coe_basis]; rw [OrthonormalBasis.coe_toBasis]
    exact exteriorPower.innerProductForm_ιMulti_family_of_orthonormal b.orthonormal i j

@[simp]

中文:
定义 OrthonormalBasis.exteriorPower
  签名: (b : OrthonormalBasis I 实数 E) (n : 自然数)
  定义体: (b.toBasis.exteriorPower n).toOrthonormalBasis by
    rw [orthonormal_iff_ite]
    intro i j
    rw [exteriorPower.coe_basis]; rw [OrthonormalBasis.coe_toBasis]
    exact exteriorPower.innerProductForm_ιMulti_family_of_orthonormal b.orthonormal i j

@[simp]

Depends on / 依赖: NoncompactSpace, NormedSpace, OrthonormalBasis, OrthonormalBasis.coe_toBasis, RealNormedSpace, RealNormedSpace.noncompactSpace, b.orthonormal, b.toBasis.exteriorPower, coe_basis, coe_toBasis, exteriorPower, exteriorPower.coe_basis, exteriorPower.innerProductForm_, noncompactSpace, orthonormal, orthonormal_iff_ite, toBasis, toOrthonormalBasis
-/
def OrthonormalBasis.exteriorPower (b : OrthonormalBasis I Real E) (n : Nat) :
    OrthonormalBasis (Set.powersetCard I n) Real (⋀[Real]^n E) :=
(b.toBasis.exteriorPower n).toOrthonormalBasis by
    rw [orthonormal_iff_ite]
    intro i j
    rw [exteriorPower.coe_basis]; rw [OrthonormalBasis.coe_toBasis]
    exact exteriorPower.innerProductForm_ιMulti_family_of_orthonormal b.orthonormal i j

@[simp]
/--
lemma `OrthonormalBasis.toBasis_exteriorPower` / 引理 `OrthonormalBasis.toBasis_exteriorPower`

English:
lemma OrthonormalBasis.toBasis_exteriorPower
  given: (b : OrthonormalBasis I Real E) (n : Nat)
  proof: (b.toBasis.exteriorPower n).toBasis_toOrthonormalBasis _

中文:
引理 OrthonormalBasis.toBasis_exteriorPower
  条件: (b : OrthonormalBasis I 实数 E) (n : 自然数)
  证明: (b.toBasis.exteriorPower n).toBasis_toOrthonormalBasis _

Depends on / 依赖: NormedAlgebra, NormedAlgebra.toNormedSpace, NormedSpace, b.toBasis.exteriorPower, exteriorPower, toBasis, toBasis_toOrthonormalBasis, toNormedSpace
-/
lemma OrthonormalBasis.toBasis_exteriorPower (b : OrthonormalBasis I Real E) (n : Nat) :
    (b.exteriorPower n).toBasis = b.toBasis.exteriorPower n :=
  (b.toBasis.exteriorPower n).toBasis_toOrthonormalBasis _

end OrthonormalBasis
