/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Unitization norms

Given a not-necessarily-unital normed `𝕜`-algebra `A`, it is frequently of interest to equip its
`Unitization` with a norm which simultaneously makes it into a normed algebra and also satisfies
two properties:

- `‖1‖ = 1` (i.e., `NormOneClass`)
- The embedding of `A` in `Unitization 𝕜 A` is an isometry. (i.e., `Isometry Unitization.inr`)

One way to do this is to pull back the norm from `WithLp 1 (𝕜 × A)`, that is,
`‖(k, a)‖ = ‖k‖ + ‖a‖` using `Unitization.addEquiv` (i.e., the identity map).
This is implemented for the type synonym `WithLp 1 (Unitization 𝕜 A)` in
`WithLp.instUnitizationNormedAddCommGroup`, and it is shown there that this is a Banach algebra.
However, when the norm on `A` is *regular* (i.e., `ContinuousLinearMap.mul` is an isometry), there
is another natural choice: the pullback of the norm on `𝕜 × (A →L[𝕜] A)` under the map
`(k, a) ↦ (k, k • 1 + ContinuousLinearMap.mul 𝕜 A a)`. It turns out that among all norms on the
unitization satisfying the properties specified above, the norm inherited from
`WithLp 1 (𝕜 × A)` is maximal, and the norm inherited from this pullback is minimal.
Of course, this means that `WithLp.equiv : WithLp 1 (Unitization 𝕜 A) → Unitization 𝕜 A` can be
upgraded to a continuous linear equivalence (when `𝕜` and `A` are complete).

structure on `Unitization 𝕜 A` using the pullback described above. The reason for choosing this norm
is that for a C⋆-algebra `A` its norm is always regular, and the pullback norm on `Unitization 𝕜 A`
is then also a C⋆-norm.

## Main definitions

- `Unitization.splitMul : Unitization 𝕜 A →ₐ[𝕜] (𝕜 × (A →L[𝕜] A))`: The first coordinate of this
  map is just `Unitization.fst` and the second is the `Unitization.lift` of the left regular
  representation of `A` (i.e., `NonUnitalAlgHom.Lmul`). We use this map to pull back the
  `NormedRing` and `NormedAlgebra` structures.

## Main statements

- `Unitization.instNormedRing`, `Unitization.instNormedAlgebra`, `Unitization.instNormOneClass`,
  `Unitization.instCompleteSpace`: when `A` is a non-unital Banach `𝕜`-algebra with a regular norm,
  then `Unitization 𝕜 A` is a unital Banach `𝕜`-algebra with `‖1‖ = 1`.
- `Unitization.norm_inr`, `Unitization.isometry_inr`: the natural inclusion `A → Unitization 𝕜 A`
  is an isometry, or in mathematical parlance, the norm on `A` extends to a norm on
  `Unitization 𝕜 A`.

## Implementation details

We ensure that the uniform structure, and hence also the topological structure, is definitionally
equal to the pullback of `instUniformSpaceProd` along `Unitization.addEquiv` (this is essentially
viewing `Unitization 𝕜 A` as `𝕜 × A`) by means of forgetful inheritance. The same is true of the
bornology.

-/

@[expose] public section

suppress_compilation

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

open ContinuousLinearMap

namespace Unitization

/--
Definition of `splitMul` / `splitMul` 的定义

English:
definition splitMul
  signature: : Unitization 𝕜 A ->ₐ[𝕜] 𝕜 × (A ->L[𝕜] A)
  body: (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)

中文:
定义 splitMul
  签名: : Unitization 𝕜 A ->ₐ[𝕜] 𝕜 × (A ->L[𝕜] A)
  定义体: (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)

Depends on / 依赖: NonUnitalAlgHom, NonUnitalAlgHom.Lmul
-/
def splitMul : Unitization 𝕜 A ->ₐ[𝕜] 𝕜 × (A ->L[𝕜] A) :=
  (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)

variable {𝕜 A}

@[simp]
/--
theorem `splitMul_apply` / 定理 `splitMul_apply`

English:
theorem splitMul_apply
  given: (x : Unitization 𝕜 A)
  proof: show (x.fst + 0, _) = (x.fst, _) by rw [add_zero]; rfl

中文:
定理 splitMul_apply
  条件: (x : Unitization 𝕜 A)
  证明: show (x.fst + 0, _) = (x.fst, _) by rw [add_zero]; rfl

Depends on / 依赖: add_zero, x.fst
-/
theorem splitMul_apply (x : Unitization 𝕜 A) :
    splitMul 𝕜 A x = (x.fst, algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd) :=
  show (x.fst + 0, _) = (x.fst, _) by rw [add_zero]; rfl

/--
theorem `splitMul_injective_of_clm_mul_injective` / 定理 `splitMul_injective_of_clm_mul_injective`

English:
theorem splitMul_injective_of_clm_mul_injective
  proof: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x
  rw [map_add] at hx
  simp only [splitMul_apply, fst_inl, snd_inl, map_zero, add_zero, fst_inr, snd_inr,
    zero_add, Prod.mk_add_mk, Prod.mk_eq_zero] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [map_zero, zero_add, inl_zero] at hx ⊢
  

中文:
定理 splitMul_injective_of_clm_mul_injective
  证明: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x
  rw [map_add] at hx
  simp only [splitMul_apply, fst_inl, snd_inl, map_zero, add_zero, fst_inr, snd_inr,
    zero_add, Prod.mk_add_mk, Prod.mk_eq_zero] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [map_zero, zero_add, inl_zero] at hx ⊢
  

Depends on / 依赖: Prod.mk_add_mk, Prod.mk_eq_zero, add_zero, fst_inl, fst_inr, injective_iff_map_eq_zero, inl_zero, inr_zero, map_add, map_zero, mk_add_mk, mk_eq_zero, snd_inl, snd_inr, splitMul_apply, zero_add
-/
theorem splitMul_injective_of_clm_mul_injective
    (h : Function.Injective (mul 𝕜 A)) :
    Function.Injective (splitMul 𝕜 A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x
  rw [map_add] at hx
  simp only [splitMul_apply, fst_inl, snd_inl, map_zero, add_zero, fst_inr, snd_inr,
    zero_add, Prod.mk_add_mk, Prod.mk_eq_zero] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [map_zero, zero_add, inl_zero] at hx ⊢
  rw [← map_zero (mul 𝕜 A)] at hx
  rw [h hx]; rw [inr_zero]

variable [RegularNormedAlgebra 𝕜 A]
variable (𝕜 A)

/--
theorem `splitMul_injective` / 定理 `splitMul_injective`

English:
theorem splitMul_injective
  statement: Function.Injective (splitMul 𝕜 A)
  proof: splitMul_injective_of_clm_mul_injective (isometry_mul 𝕜 A).injective

中文:
定理 splitMul_injective
  结论: 函数.单射 (splitMul 𝕜 A)
  证明: splitMul_injective_of_clm_mul_injective (isometry_mul 𝕜 A).injective

Depends on / 依赖: injective, isometry_mul, splitMul_injective_of_clm_mul_injective
-/
theorem splitMul_injective : Function.Injective (splitMul 𝕜 A) :=
  splitMul_injective_of_clm_mul_injective (isometry_mul 𝕜 A).injective

variable {𝕜 A}

section Aux

/--
Definition of `normedRingAux` / `normedRingAux` 的定义

English:
abbreviation normedRingAux
  signature: : NormedRing (Unitization 𝕜 A)
  body: NormedRing.induced (Unitization 𝕜 A) (𝕜 × (A ->L[𝕜] A)) (splitMul 𝕜 A) (splitMul_injective 𝕜 A)

中文:
缩写 normedRingAux
  签名: : 赋范环 (Unitization 𝕜 A)
  定义体: NormedRing.induced (Unitization 𝕜 A) (𝕜 × (A ->L[𝕜] A)) (splitMul 𝕜 A) (splitMul_injective 𝕜 A)

Depends on / 依赖: NormedRing, NormedRing.induced, Unitization, induced, splitMul, splitMul_injective
-/
noncomputable abbrev normedRingAux : NormedRing (Unitization 𝕜 A) :=
  NormedRing.induced (Unitization 𝕜 A) (𝕜 × (A ->L[𝕜] A)) (splitMul 𝕜 A) (splitMul_injective 𝕜 A)

attribute [local instance] Unitization.normedRingAux

/--
Definition of `normedAlgebraAux` / `normedAlgebraAux` 的定义

English:
abbreviation normedAlgebraAux
  signature: : NormedAlgebra 𝕜 (Unitization 𝕜 A)
  body: NormedAlgebra.induced 𝕜 (Unitization 𝕜 A) (𝕜 × (A ->L[𝕜] A)) (splitMul 𝕜 A)

中文:
缩写 normedAlgebraAux
  签名: : 赋范代数 𝕜 (Unitization 𝕜 A)
  定义体: NormedAlgebra.induced 𝕜 (Unitization 𝕜 A) (𝕜 × (A ->L[𝕜] A)) (splitMul 𝕜 A)

Depends on / 依赖: NormedAlgebra, NormedAlgebra.induced, Unitization, induced, splitMul
-/
noncomputable abbrev normedAlgebraAux : NormedAlgebra 𝕜 (Unitization 𝕜 A) :=
  NormedAlgebra.induced 𝕜 (Unitization 𝕜 A) (𝕜 × (A ->L[𝕜] A)) (splitMul 𝕜 A)

attribute [local instance] Unitization.normedAlgebraAux

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (x : Unitization 𝕜 A)
  statement: ‖x‖ = ‖splitMul 𝕜 A x‖
  proof: rfl

中文:
定理 norm_def
  条件: (x : Unitization 𝕜 A)
  结论: ‖x‖ = ‖splitMul 𝕜 A x‖
  证明: rfl
-/
theorem norm_def (x : Unitization 𝕜 A) : ‖x‖ = ‖splitMul 𝕜 A x‖ :=
  rfl

/--
theorem `nnnorm_def` / 定理 `nnnorm_def`

English:
theorem nnnorm_def
  given: (x : Unitization 𝕜 A)
  statement: ‖x‖₊ = ‖splitMul 𝕜 A x‖₊
  proof: rfl

中文:
定理 nnnorm_def
  条件: (x : Unitization 𝕜 A)
  结论: ‖x‖₊ = ‖splitMul 𝕜 A x‖₊
  证明: rfl
-/
theorem nnnorm_def (x : Unitization 𝕜 A) : ‖x‖₊ = ‖splitMul 𝕜 A x‖₊ :=
  rfl

/--
theorem `norm_eq_sup` / 定理 `norm_eq_sup`

English:
theorem norm_eq_sup
  given: (x : Unitization 𝕜 A)
  proof: by
  rw [norm_def]; rw [splitMul_apply]; rw [Prod.norm_def]

中文:
定理 norm_eq_sup
  条件: (x : Unitization 𝕜 A)
  证明: by
  rw [norm_def]; rw [splitMul_apply]; rw [Prod.norm_def]

Depends on / 依赖: Prod.norm_def, norm_def, splitMul_apply
-/
theorem norm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖ = ‖x.fst‖ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd‖ := by
  rw [norm_def]; rw [splitMul_apply]; rw [Prod.norm_def]

/--
theorem `nnnorm_eq_sup` / 定理 `nnnorm_eq_sup`

English:
theorem nnnorm_eq_sup
  given: (x : Unitization 𝕜 A)
  proof: NNReal.eq norm_eq_sup x

中文:
定理 nnnorm_eq_sup
  条件: (x : Unitization 𝕜 A)
  证明: NNReal.eq norm_eq_sup x

Depends on / 依赖: NNReal, NNReal.eq, norm_eq_sup
-/
theorem nnnorm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖₊ = ‖x.fst‖₊ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd‖₊ :=
NNReal.eq norm_eq_sup x

/--
theorem `lipschitzWith_addEquiv` / 定理 `lipschitzWith_addEquiv`

English:
theorem lipschitzWith_addEquiv
  proof: by
  rw [← Real.toNNReal_ofNat]
  refine AddMonoidHomClass.lipschitz_of_bound (Unitization.addEquiv 𝕜 A) 2 fun x => ?_
  rw [norm_eq_sup]; rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm

中文:
定理 lipschitzWith_addEquiv
  证明: by
  rw [← Real.toNNReal_ofNat]
  refine AddMonoidHomClass.lipschitz_of_bound (Unitization.addEquiv 𝕜 A) 2 fun x => ?_
  rw [norm_eq_sup]; rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.lipschitz_of_bound, Prod.norm_def, Real.toNNReal_ofNat, Unitization, Unitization.addEquiv, addEquiv, algebraMap, isometry_mul, le_add_of_nonneg_left, le_max_of_le_left, lipschitz_of_bound, map_zero, max_le, mul_max_of_nonneg, nontriviality, norm_def, norm_eq_sup, norm_map_of_map_zero, norm_nonneg
-/
theorem lipschitzWith_addEquiv :
    LipschitzWith 2 (Unitization.addEquiv 𝕜 A) := by
  rw [← Real.toNNReal_ofNat]
  refine AddMonoidHomClass.lipschitz_of_bound (Unitization.addEquiv 𝕜 A) 2 fun x => ?_
  rw [norm_eq_sup]; rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    rw [two_mul]
    calc
      ‖x.snd‖ = ‖mul 𝕜 A x.snd‖ :=
.symm (isometry_mul 𝕜 A).norm_map_of_map_zero (map_zero _) _
      _ <= ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ + ‖x.fst‖ := by
        simpa only [add_comm _ (mul 𝕜 A x.snd), norm_algebraMap'] using
          norm_le_add_norm_add (mul 𝕜 A x.snd) (algebraMap 𝕜 _ x.fst)
      _ <= _ := add_le_add le_sup_right le_sup_left

/--
theorem `antilipschitzWith_addEquiv` / 定理 `antilipschitzWith_addEquiv`

English:
theorem antilipschitzWith_addEquiv
  proof: by
  refine AddMonoidHomClass.antilipschitz_of_bound (addEquiv 𝕜 A) fun x => ?_
  rw [norm_eq_sup]; rw [Prod.norm_def]; rw [NNReal.coe_two]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_

中文:
定理 antilipschitzWith_addEquiv
  证明: by
  refine AddMonoidHomClass.antilipschitz_of_bound (addEquiv 𝕜 A) fun x => ?_
  rw [norm_eq_sup]; rw [Prod.norm_def]; rw [NNReal.coe_two]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_

Depends on / 依赖: AddMonoidH, AddMonoidHomClass, AddMonoidHomClass.antilipschitz_of_bound, NNReal, NNReal.coe_two, Prod.norm_def, addEquiv, algebraMap, antilipschitz_of_bound, coe_two, le_add_of_nonneg_left, le_max_of_le_left, max_le, mul_max_of_nonneg, nontriviality, norm_add_le, norm_algebraMap, norm_def, norm_eq_sup, norm_nonneg
-/
theorem antilipschitzWith_addEquiv :
    AntilipschitzWith 2 (addEquiv 𝕜 A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound (addEquiv 𝕜 A) fun x => ?_
  rw [norm_eq_sup]; rw [Prod.norm_def]; rw [NNReal.coe_two]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : Real) <= 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    calc
      ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ <= ‖algebraMap 𝕜 _ x.fst‖ + ‖mul 𝕜 A x.snd‖ :=
        norm_add_le _ _
      _ = ‖x.fst‖ + ‖x.snd‖ := by
        rw [norm_algebraMap']; rw [(AddMonoidHomClass.isometry_iff_norm (mul 𝕜 A)).mp (isometry_mul 𝕜 A)]
      _ <= _ := (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm

open Bornology Filter
open scoped Uniformity Topology

/--
theorem `uniformity_eq_aux` / 定理 `uniformity_eq_aux`

English:
theorem uniformity_eq_aux
  proof: by
  have key : IsUniformInducing (addEquiv 𝕜 A) :=
    antilipschitzWith_addEquiv.isUniformInducing lipschitzWith_addEquiv.uniformContinuous
  rw [← key.comap_uniformity]
  rfl

中文:
定理 uniformity_eq_aux
  证明: by
  have key : IsUniformInducing (addEquiv 𝕜 A) :=
    antilipschitzWith_addEquiv.isUniformInducing lipschitzWith_addEquiv.uniformContinuous
  rw [← key.comap_uniformity]
  rfl

Depends on / 依赖: IsUniformInducing, addEquiv, antilipschitzWith_addEquiv, antilipschitzWith_addEquiv.isUniformInducing, comap_uniformity, isUniformInducing, key.comap_uniformity, lipschitzWith_addEquiv, lipschitzWith_addEquiv.uniformContinuous, uniformContinuous
-/
theorem uniformity_eq_aux :
    𝓤[instUniformSpaceProd.comap <| addEquiv 𝕜 A] = 𝓤 (Unitization 𝕜 A) := by
  have key : IsUniformInducing (addEquiv 𝕜 A) :=
    antilipschitzWith_addEquiv.isUniformInducing lipschitzWith_addEquiv.uniformContinuous
  rw [← key.comap_uniformity]
  rfl

/--
theorem `cobounded_eq_aux` / 定理 `cobounded_eq_aux`

English:
theorem cobounded_eq_aux
  proof: le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
    antilipschitzWith_addEquiv.tendsto_cobounded.le_comap

中文:
定理 cobounded_eq_aux
  证明: le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
    antilipschitzWith_addEquiv.tendsto_cobounded.le_comap

Depends on / 依赖: antilipschitzWith_addEquiv, antilipschitzWith_addEquiv.tendsto_cobounded.le_comap, comap_cobounded_le, le_antisymm, le_comap, lipschitzWith_addEquiv, lipschitzWith_addEquiv.comap_cobounded_le, tendsto_cobounded
-/
theorem cobounded_eq_aux :
    @cobounded _ (Bornology.induced <| addEquiv 𝕜 A) = cobounded (Unitization 𝕜 A) :=
  le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
    antilipschitzWith_addEquiv.tendsto_cobounded.le_comap

end Aux

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (Unitization 𝕜 A)
  body: instUniformSpaceProd.comap (addEquiv 𝕜 A)

中文:
实例 instUniformSpace
  签名: : 一致空间 (Unitization 𝕜 A)
  定义体: instUniformSpaceProd.comap (addEquiv 𝕜 A)

Depends on / 依赖: addEquiv, instUniformSpaceProd, instUniformSpaceProd.comap
-/
instance instUniformSpace : UniformSpace (Unitization 𝕜 A) :=
  instUniformSpaceProd.comap (addEquiv 𝕜 A)

/--
Definition of `uniformEquivProd` / `uniformEquivProd` 的定义

English:
definition uniformEquivProd
  signature: : (Unitization 𝕜 A) ≃ᵤ (𝕜 × A)
  body: Equiv.toUniformEquivOfIsUniformInducing (addEquiv 𝕜 A) ⟨rfl⟩

中文:
定义 uniformEquivProd
  签名: : (Unitization 𝕜 A) ≃ᵤ (𝕜 × A)
  定义体: Equiv.toUniformEquivOfIsUniformInducing (addEquiv 𝕜 A) ⟨rfl⟩

Depends on / 依赖: Equiv.toUniformEquivOfIsUniformInducing, addEquiv, toUniformEquivOfIsUniformInducing
-/
def uniformEquivProd : (Unitization 𝕜 A) ≃ᵤ (𝕜 × A) :=
  Equiv.toUniformEquivOfIsUniformInducing (addEquiv 𝕜 A) ⟨rfl⟩

/--
Instance `instBornology` / 实例 `instBornology`

English:
instance instBornology
  signature: : Bornology (Unitization 𝕜 A)
  body: Bornology.induced addEquiv 𝕜 A

中文:
实例 instBornology
  签名: : 有界结构 (Unitization 𝕜 A)
  定义体: Bornology.induced addEquiv 𝕜 A

Depends on / 依赖: Bornology, Bornology.induced, addEquiv, induced
-/
instance instBornology : Bornology (Unitization 𝕜 A) :=
Bornology.induced addEquiv 𝕜 A

/--
theorem `isUniformEmbedding_addEquiv` / 定理 `isUniformEmbedding_addEquiv`

English:
theorem isUniformEmbedding_addEquiv
  given: {𝕜} [NontriviallyNormedField 𝕜]
  proof: rfl
  injective := (addEquiv 𝕜 A).injective

中文:
定理 isUniformEmbedding_addEquiv
  条件: {𝕜} [NontriviallyNormedField 𝕜]
  证明: rfl
  injective := (addEquiv 𝕜 A).injective
-/
theorem isUniformEmbedding_addEquiv {𝕜} [NontriviallyNormedField 𝕜] :
    IsUniformEmbedding (addEquiv 𝕜 A) where
  comap_uniformity := rfl
  injective := (addEquiv 𝕜 A).injective

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [CompleteSpace 𝕜] [CompleteSpace A]
  body: uniformEquivProd.completeSpace_iff.2 .prod

中文:
实例 instCompleteSpace
  签名: [完备空间 𝕜] [完备空间 A]
  定义体: uniformEquivProd.completeSpace_iff.2 .prod

Depends on / 依赖: completeSpace_iff, uniformEquivProd, uniformEquivProd.completeSpace_iff
-/
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (Unitization 𝕜 A) :=
  uniformEquivProd.completeSpace_iff.2 .prod

/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: : T2Space (Unitization 𝕜 A)
  body: Unitization.uniformEquivProd.symm.toHomeomorph.t2Space

中文:
实例 instT2Space
  签名: : T2空间 (Unitization 𝕜 A)
  定义体: Unitization.uniformEquivProd.symm.toHomeomorph.t2Space

Depends on / 依赖: Unitization, Unitization.uniformEquivProd.symm.toHomeomorph.t2Space, t2Space, toHomeomorph, uniformEquivProd
-/
instance instT2Space : T2Space (Unitization 𝕜 A) :=
  Unitization.uniformEquivProd.symm.toHomeomorph.t2Space

/--
Instance `instMetricSpace` / 实例 `instMetricSpace`

English:
instance instMetricSpace
  signature: : MetricSpace (Unitization 𝕜 A)
  body: (normedRingAux.toMetricSpace.replaceUniformity uniformity_eq_aux).replaceBornology
    fun s => Filter.ext_iff.1 cobounded_eq_aux (sᶜ)

中文:
实例 instMetricSpace
  签名: : 度量空间 (Unitization 𝕜 A)
  定义体: (normedRingAux.toMetricSpace.replaceUniformity uniformity_eq_aux).replaceBornology
    fun s => Filter.ext_iff.1 cobounded_eq_aux (sᶜ)

Depends on / 依赖: Filter, Filter.ext_iff, cobounded_eq_aux, ext_iff, normedRingAux, normedRingAux.toMetricSpace.replaceUniformity, replaceBornology, replaceUniformity, toMetricSpace, uniformity_eq_aux
-/
noncomputable instance instMetricSpace : MetricSpace (Unitization 𝕜 A) :=
  (normedRingAux.toMetricSpace.replaceUniformity uniformity_eq_aux).replaceBornology
    fun s => Filter.ext_iff.1 cobounded_eq_aux (sᶜ)

/--
Instance `instNormedRing` / 实例 `instNormedRing`

English:
instance instNormedRing
  signature: : NormedRing (Unitization 𝕜 A) where
  body: normedRingAux.dist_eq
  norm_mul_le := normedRingAux.norm_mul_le
  norm := normedRingAux.norm

中文:
实例 instNormedRing
  签名: : 赋范环 (Unitization 𝕜 A) where
  定义体: normedRingAux.dist_eq
  norm_mul_le := normedRingAux.norm_mul_le
  norm := normedRingAux.norm

Depends on / 依赖: dist_eq, normedRingAux, normedRingAux.dist_eq
-/
noncomputable instance instNormedRing : NormedRing (Unitization 𝕜 A) where
  dist_eq := normedRingAux.dist_eq
  norm_mul_le := normedRingAux.norm_mul_le
  norm := normedRingAux.norm

/--
Instance `instNormedAlgebra` / 实例 `instNormedAlgebra`

English:
instance instNormedAlgebra
  signature: : NormedAlgebra 𝕜 (Unitization 𝕜 A) where
  body: by rw [norm_def, map_smul, norm_smul, ← norm_def]

中文:
实例 instNormedAlgebra
  签名: : 赋范代数 𝕜 (Unitization 𝕜 A) where
  定义体: by rw [norm_def, map_smul, norm_smul, ← norm_def]

Depends on / 依赖: map_smul, norm_def, norm_smul
-/
instance instNormedAlgebra : NormedAlgebra 𝕜 (Unitization 𝕜 A) where
  norm_smul_le k x := by rw [norm_def, map_smul, norm_smul, ← norm_def]

/--
Instance `instNormOneClass` / 实例 `instNormOneClass`

English:
instance instNormOneClass
  signature: : NormOneClass (Unitization 𝕜 A) where
  body: by simpa only [norm_eq_sup, fst_one, norm_one, snd_one, map_one, map_zero,
      add_zero, sup_eq_left] using opNorm_le_bound _ zero_le_one fun x => by simp

中文:
实例 instNormOneClass
  签名: : NormOne类 (Unitization 𝕜 A) where
  定义体: by simpa only [norm_eq_sup, fst_one, norm_one, snd_one, map_one, map_zero,
      add_zero, sup_eq_left] using opNorm_le_bound _ zero_le_one fun x => by simp

Depends on / 依赖: add_zero, fst_one, map_one, map_zero, norm_eq_sup, norm_one, opNorm_le_bound, snd_one, sup_eq_left, zero_le_one
-/
instance instNormOneClass : NormOneClass (Unitization 𝕜 A) where
  norm_one := by simpa only [norm_eq_sup, fst_one, norm_one, snd_one, map_one, map_zero,
      add_zero, sup_eq_left] using opNorm_le_bound _ zero_le_one fun x => by simp

/--
lemma `norm_inr` / 引理 `norm_inr`

English:
lemma norm_inr
  given: (a : A)
  statement: ‖(a : Unitization 𝕜 A)‖ = ‖a‖
  proof: by
  simp [norm_eq_sup]

中文:
引理 norm_inr
  条件: (a : A)
  结论: ‖(a : Unitization 𝕜 A)‖ = ‖a‖
  证明: by
  simp [norm_eq_sup]

Depends on / 依赖: norm_eq_sup
-/
lemma norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖ := by
  simp [norm_eq_sup]

/--
lemma `nnnorm_inr` / 引理 `nnnorm_inr`

English:
lemma nnnorm_inr
  given: (a : A)
  statement: ‖(a : Unitization 𝕜 A)‖₊ = ‖a‖₊
  proof: NNReal.eq norm_inr a

中文:
引理 nnnorm_inr
  条件: (a : A)
  结论: ‖(a : Unitization 𝕜 A)‖₊ = ‖a‖₊
  证明: NNReal.eq norm_inr a

Depends on / 依赖: NNReal, NNReal.eq, norm_inr
-/
lemma nnnorm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖₊ = ‖a‖₊ :=
NNReal.eq norm_inr a

/--
lemma `isometry_inr` / 引理 `isometry_inr`

English:
lemma isometry_inr
  statement: Isometry ((↑) : A -> Unitization 𝕜 A)
  proof: AddMonoidHomClass.isometry_of_norm (inrNonUnitalAlgHom 𝕜 A) norm_inr

@[fun_prop]

中文:
引理 isometry_inr
  结论: 等距 ((↑) : A -> Unitization 𝕜 A)
  证明: AddMonoidHomClass.isometry_of_norm (inrNonUnitalAlgHom 𝕜 A) norm_inr

@[fun_prop]

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, inrNonUnitalAlgHom, isometry_of_norm, norm_inr
-/
lemma isometry_inr : Isometry ((↑) : A -> Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm (inrNonUnitalAlgHom 𝕜 A) norm_inr

@[fun_prop]
/--
theorem `continuous_inr` / 定理 `continuous_inr`

English:
theorem continuous_inr
  statement: Continuous (inr : A -> Unitization 𝕜 A)
  proof: isometry_inr.continuous

中文:
定理 continuous_inr
  结论: 连续 (inr : A -> Unitization 𝕜 A)
  证明: isometry_inr.continuous

Depends on / 依赖: continuous, isometry_inr, isometry_inr.continuous
-/
theorem continuous_inr : Continuous (inr : A -> Unitization 𝕜 A) :=
  isometry_inr.continuous

/--
lemma `dist_inr` / 引理 `dist_inr`

English:
lemma dist_inr
  given: (a b : A)
  statement: dist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = dist a b
  proof: isometry_inr.dist_eq a b

中文:
引理 dist_inr
  条件: (a b : A)
  结论: dist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = dist a b
  证明: isometry_inr.dist_eq a b

Depends on / 依赖: dist_eq, isometry_inr, isometry_inr.dist_eq
-/
lemma dist_inr (a b : A) : dist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = dist a b :=
  isometry_inr.dist_eq a b

/--
lemma `nndist_inr` / 引理 `nndist_inr`

English:
lemma nndist_inr
  given: (a b : A)
  statement: nndist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = nndist a b
  proof: isometry_inr.nndist_eq a b

中文:
引理 nndist_inr
  条件: (a b : A)
  结论: nndist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = nndist a b
  证明: isometry_inr.nndist_eq a b

Depends on / 依赖: isometry_inr, isometry_inr.nndist_eq, nndist_eq
-/
lemma nndist_inr (a b : A) : nndist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = nndist a b :=
  isometry_inr.nndist_eq a b

/-! These examples verify that the bornology and uniformity (hence also the topology) are the
correct ones. -/
example : (instNormedRing (𝕜 := 𝕜) (A := A)).toMetricSpace = instMetricSpace := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toBornology = instBornology := rfl
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toUniformSpace = instUniformSpace := rfl

section

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]

/--
theorem `uniformContinuous_fst` / 定理 `uniformContinuous_fst`

English:
theorem uniformContinuous_fst
  statement: UniformContinuous (fun x : Unitization 𝕜 A => x.fst)
  proof: uniformContinuous_fst.comp Unitization.uniformEquivProd.uniformContinuous

中文:
定理 uniformContinuous_fst
  结论: 一致连续 (fun x : Unitization 𝕜 A => x.fst)
  证明: uniformContinuous_fst.comp Unitization.uniformEquivProd.uniformContinuous
-/
protected theorem uniformContinuous_fst : UniformContinuous (fun x : Unitization 𝕜 A => x.fst) :=
  uniformContinuous_fst.comp Unitization.uniformEquivProd.uniformContinuous

/--
theorem `uniformContinuous_snd` / 定理 `uniformContinuous_snd`

English:
theorem uniformContinuous_snd
  statement: UniformContinuous (fun x : Unitization 𝕜 A => x.snd)
  proof: uniformContinuous_snd.comp Unitization.uniformEquivProd.uniformContinuous

@[fun_prop]

中文:
定理 uniformContinuous_snd
  结论: 一致连续 (fun x : Unitization 𝕜 A => x.snd)
  证明: uniformContinuous_snd.comp Unitization.uniformEquivProd.uniformContinuous

@[fun_prop]
-/
protected theorem uniformContinuous_snd : UniformContinuous (fun x : Unitization 𝕜 A => x.snd) :=
  uniformContinuous_snd.comp Unitization.uniformEquivProd.uniformContinuous

@[fun_prop]
/--
theorem `continuous_fst` / 定理 `continuous_fst`

English:
theorem continuous_fst
  statement: Continuous (fun x : Unitization 𝕜 A => x.fst)
  proof: Unitization.uniformContinuous_fst.continuous

@[fun_prop]

中文:
定理 continuous_fst
  结论: 连续 (fun x : Unitization 𝕜 A => x.fst)
  证明: Unitization.uniformContinuous_fst.continuous

@[fun_prop]
-/
protected theorem continuous_fst : Continuous (fun x : Unitization 𝕜 A => x.fst) :=
  Unitization.uniformContinuous_fst.continuous

@[fun_prop]
/--
theorem `continuous_snd` / 定理 `continuous_snd`

English:
theorem continuous_snd
  statement: Continuous (fun x : Unitization 𝕜 A => x.snd)
  proof: Unitization.uniformContinuous_snd.continuous

中文:
定理 continuous_snd
  结论: 连续 (fun x : Unitization 𝕜 A => x.snd)
  证明: Unitization.uniformContinuous_snd.continuous
-/
protected theorem continuous_snd : Continuous (fun x : Unitization 𝕜 A => x.snd) :=
  Unitization.uniformContinuous_snd.continuous

end

end Unitization
