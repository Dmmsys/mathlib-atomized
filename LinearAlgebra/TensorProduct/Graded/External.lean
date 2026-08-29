/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Graded tensor products over graded algebras

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ℕ`, `ℤ`, or `ZMod 2` (or more generally, any index
that satisfies `Module ι (Additive ℤˣ)`).

The results for internally-graded algebras (via `GradedAlgebra`) are elsewhere, as is the type
`GradedTensorProduct`.

## Main results

* `TensorProduct.gradedComm`: the symmetric braiding operator on the tensor product of
  externally-graded rings.
* `TensorProduct.gradedMul`: the previously-described multiplication on externally-graded rings, as
  a bilinear map.

## Implementation notes

Rather than implementing the multiplication directly as above, we first implement the canonical
non-trivial braiding sending $a \otimes b$ to $(-1)^{\deg a' \deg b} (b \otimes a)$, as the
multiplication follows trivially from this after some point-free nonsense.

## References

* https://math.stackexchange.com/q/202718/1896
* [*Algebra I*, Bourbaki : Chapter III, §4.7, example (2)][bourbaki1989]

-/

@[expose] public section

open scoped TensorProduct DirectSum

variable {R ι : Type*}

namespace TensorProduct

variable [CommSemiring ι] [Module ι (Additive Intˣ)] [DecidableEq ι]
variable (𝒜 : ι -> Type*) (ℬ : ι -> Type*)
variable [CommRing R]
variable [forall i, AddCommGroup (𝒜 i)] [forall i, AddCommGroup (ℬ i)]
variable [forall i, Module R (𝒜 i)] [forall i, Module R (ℬ i)]

-- this helps with performance
instance (i : ι × ι) : Module R (𝒜 (Prod.fst i) otimes[R] ℬ (Prod.snd i)) :=
  TensorProduct.leftModule

open DirectSum (lof)

variable (R)

section gradedComm

local notation "𝒜ℬ" => (fun i : ι × ι => 𝒜 (Prod.fst i) otimes[R] ℬ (Prod.snd i))
local notation "ℬ𝒜" => (fun i : ι × ι => ℬ (Prod.fst i) otimes[R] 𝒜 (Prod.snd i))

/--
Definition of `gradedCommAux` / `gradedCommAux` 的定义

English:
definition gradedCommAux
  signature: : DirectSum _ 𝒜ℬ ->ₗ[R] DirectSum _ ℬ𝒜
  body: DirectSum.toModule R _ _ fun i =>
    have o := DirectSum.lof R _ ℬ𝒜 (i.2, i.1)
    have s : Intˣ := ((-1 : Intˣ) ^ (i.1 * i.2 : ι) : Intˣ)
    (s • o) ∘ₗ (TensorProduct.comm R _ _).toLinearMap

@[simp]

中文:
定义 gradedCommAux
  签名: : DirectSum _ 𝒜ℬ ->ₗ[R] DirectSum _ ℬ𝒜
  定义体: DirectSum.toModule R _ _ fun i =>
    have o := DirectSum.lof R _ ℬ𝒜 (i.2, i.1)
    have s : Intˣ := ((-1 : Intˣ) ^ (i.1 * i.2 : ι) : Intˣ)
    (s • o) ∘ₗ (TensorProduct.comm R _ _).toLinearMap

@[simp]

Depends on / 依赖: DirectSum, DirectSum.lof, DirectSum.toModule, TensorProduct, TensorProduct.comm, toLinearMap, toModule
-/
def gradedCommAux : DirectSum _ 𝒜ℬ ->ₗ[R] DirectSum _ ℬ𝒜 :=
  DirectSum.toModule R _ _ fun i =>
    have o := DirectSum.lof R _ ℬ𝒜 (i.2, i.1)
    have s : Intˣ := ((-1 : Intˣ) ^ (i.1 * i.2 : ι) : Intˣ)
    (s • o) ∘ₗ (TensorProduct.comm R _ _).toLinearMap

@[simp]
/--
theorem `gradedCommAux_lof_tmul` / 定理 `gradedCommAux_lof_tmul`

English:
theorem gradedCommAux_lof_tmul
  given: (i j : ι) (a : 𝒜 i) (b : ℬ j)
  proof: by
  rw [gradedCommAux]
  simp [mul_comm i j]

中文:
定理 gradedCommAux_lof_tmul
  条件: (i j : ι) (a : 𝒜 i) (b : ℬ j)
  证明: by
  rw [gradedCommAux]
  simp [mul_comm i j]

Depends on / 依赖: gradedCommAux, mul_comm
-/
theorem gradedCommAux_lof_tmul (i j : ι) (a : 𝒜 i) (b : ℬ j) :
    gradedCommAux R 𝒜 ℬ (lof R _ 𝒜ℬ (i, j) (a otimesₜ b)) =
      (-1 : Intˣ) ^ (j * i) • lof R _ ℬ𝒜 (j, i) (b otimesₜ a) := by
  rw [gradedCommAux]
  simp [mul_comm i j]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `gradedCommAux_comp_gradedCommAux` / 定理 `gradedCommAux_comp_gradedCommAux`

English:
theorem gradedCommAux_comp_gradedCommAux
  proof: by
  ext i a b
  dsimp
  rw [gradedCommAux_lof_tmul]; rw [LinearMap.map_smul_of_tower]; rw [gradedCommAux_lof_tmul]; rw [smul_smul]; rw [mul_comm i.2 i.1]; rw [Int.units_mul_self]; rw [one_smul]

中文:
定理 gradedCommAux_comp_gradedCommAux
  证明: by
  ext i a b
  dsimp
  rw [gradedCommAux_lof_tmul]; rw [LinearMap.map_smul_of_tower]; rw [gradedCommAux_lof_tmul]; rw [smul_smul]; rw [mul_comm i.2 i.1]; rw [Int.units_mul_self]; rw [one_smul]

Depends on / 依赖: Int.units_mul_self, LinearMap, LinearMap.map_smul_of_tower, gradedCommAux_lof_tmul, map_smul_of_tower, mul_comm, one_smul, smul_smul, units_mul_self
-/
theorem gradedCommAux_comp_gradedCommAux :
    gradedCommAux R 𝒜 ℬ ∘ₗ gradedCommAux R ℬ 𝒜 = LinearMap.id := by
  ext i a b
  dsimp
  rw [gradedCommAux_lof_tmul]; rw [LinearMap.map_smul_of_tower]; rw [gradedCommAux_lof_tmul]; rw [smul_smul]; rw [mul_comm i.2 i.1]; rw [Int.units_mul_self]; rw [one_smul]

/--
Definition of `gradedComm` / `gradedComm` 的定义

English:
definition gradedComm
  signature: :
  body: by
  refine TensorProduct.directSum R R 𝒜 ℬ ≪≫ₗ ?_ ≪≫ₗ (TensorProduct.directSum R R ℬ 𝒜).symm
  exact LinearEquiv.ofLinearMap (gradedCommAux _ _ _) (gradedCommAux _ _ _)
    (gradedCommAux_comp_gradedCommAux _ _ _) (gradedCommAux_comp_gradedCommAux _ _ _)

中文:
定义 gradedComm
  签名: :
  定义体: by
  refine TensorProduct.directSum R R 𝒜 ℬ ≪≫ₗ ?_ ≪≫ₗ (TensorProduct.directSum R R ℬ 𝒜).symm
  exact LinearEquiv.ofLinearMap (gradedCommAux _ _ _) (gradedCommAux _ _ _)
    (gradedCommAux_comp_gradedCommAux _ _ _) (gradedCommAux_comp_gradedCommAux _ _ _)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, TensorProduct, TensorProduct.directSum, directSum, gradedCommAux, gradedCommAux_comp_gradedCommAux, ofLinearMap
-/
def gradedComm :
    (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i) ≃ₗ[R] (⨁ i, ℬ i) otimes[R] (⨁ i, 𝒜 i) := by
  refine TensorProduct.directSum R R 𝒜 ℬ ≪≫ₗ ?_ ≪≫ₗ (TensorProduct.directSum R R ℬ 𝒜).symm
  exact LinearEquiv.ofLinearMap (gradedCommAux _ _ _) (gradedCommAux _ _ _)
    (gradedCommAux_comp_gradedCommAux _ _ _) (gradedCommAux_comp_gradedCommAux _ _ _)

/-- The braiding is symmetric. -/
@[simp]
/--
theorem `gradedComm_symm` / 定理 `gradedComm_symm`

English:
theorem gradedComm_symm
  statement: (gradedComm R 𝒜 ℬ).symm = gradedComm R ℬ 𝒜
  proof: by
  rfl

中文:
定理 gradedComm_symm
  结论: (gradedComm R 𝒜 ℬ).symm = gradedComm R ℬ 𝒜
  证明: by
  rfl
-/
theorem gradedComm_symm : (gradedComm R 𝒜 ℬ).symm = gradedComm R ℬ 𝒜 := by
  rfl

/--
theorem `gradedComm_of_tmul_of` / 定理 `gradedComm_of_tmul_of`

English:
theorem gradedComm_of_tmul_of
  given: (i j : ι) (a : 𝒜 i) (b : ℬ j)
  proof: by
  rw [gradedComm]
  dsimp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap]
  rw [TensorProduct.directSum_lof_tmul_lof]; rw [gradedCommAux_lof_tmul]; rw [Units.smul_def]; rw [-- Note: https://github.com/leanprover-community/mathlib4/pull/8386 specialized `map_smul` to `LinearEquiv.map_s

中文:
定理 gradedComm_of_tmul_of
  条件: (i j : ι) (a : 𝒜 i) (b : ℬ j)
  证明: by
  rw [gradedComm]
  dsimp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap]
  rw [TensorProduct.directSum_lof_tmul_lof]; rw [gradedCommAux_lof_tmul]; rw [Units.smul_def]; rw [-- Note: https://github.com/leanprover-community/mathlib4/pull/8386 specialized `map_smul` to `LinearEquiv.map_s

Depends on / 依赖: Int.cast_smul_eq_zsmul, LinearEquiv, LinearEquiv.coe_ofLinearMap, LinearEquiv.map_smul, LinearEquiv.trans_apply, TensorProduct, TensorProduct.directSum_lof_tmul_lof, TensorProduct.directSum_symm_lof_tmul, Units.smul_def, cast_smul_eq_zsmul, coe_ofLinearMap, community, directSum_lof_tmul_lof, directSum_symm_lof_tmul, github, github.com, gradedComm, gradedCommAux_lof_tmul, leanprover, map_smul
-/
theorem gradedComm_of_tmul_of (i j : ι) (a : 𝒜 i) (b : ℬ j) :
    gradedComm R 𝒜 ℬ (lof R _ 𝒜 i a otimesₜ lof R _ ℬ j b) =
      (-1 : Intˣ) ^ (j * i) • (lof R _ ℬ _ b otimesₜ lof R _ 𝒜 _ a) := by
  rw [gradedComm]
  dsimp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap]
  rw [TensorProduct.directSum_lof_tmul_lof]; rw [gradedCommAux_lof_tmul]; rw [Units.smul_def]; rw [-- Note: https://github.com/leanprover-community/mathlib4/pull/8386 specialized `map_smul` to `LinearEquiv.map_smul` to avoid timeouts.
    ← Int.cast_smul_eq_zsmul R]; rw [LinearEquiv.map_smul]; rw [TensorProduct.directSum_symm_lof_tmul]; rw [Int.cast_smul_eq_zsmul]; rw [← Units.smul_def]

/--
theorem `gradedComm_tmul_of_zero` / 定理 `gradedComm_tmul_of_zero`

English:
theorem gradedComm_tmul_of_zero
  given: (a : ⨁ i, 𝒜 i) (b : ℬ 0)
  proof: by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ
        (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)).flip (lof R _ ℬ 0 b) =
      TensorProduct.mk R _ _ (lof R _ ℬ 0 b) from
    DFunLike.congr_fun this a
  ext i a
  dsimp
  rw [gradedComm_of_tmul_of]; rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]

中文:
定理 gradedComm_tmul_of_zero
  条件: (a : ⨁ i, 𝒜 i) (b : ℬ 0)
  证明: by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ
        (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)).flip (lof R _ ℬ 0 b) =
      TensorProduct.mk R _ _ (lof R _ ℬ 0 b) from
    DFunLike.congr_fun this a
  ext i a
  dsimp
  rw [gradedComm_of_tmul_of]; rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, TensorProduct, TensorProduct.mk, congr_fun, gradedComm, gradedComm_of_tmul_of, one_smul, toLinearMap, uzpow_zero, zero_mul
-/
theorem gradedComm_tmul_of_zero (a : ⨁ i, 𝒜 i) (b : ℬ 0) :
    gradedComm R 𝒜 ℬ (a otimesₜ lof R _ ℬ 0 b) = lof R _ ℬ _ b otimesₜ a := by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ
        (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)).flip (lof R _ ℬ 0 b) =
      TensorProduct.mk R _ _ (lof R _ ℬ 0 b) from
    DFunLike.congr_fun this a
  ext i a
  dsimp
  rw [gradedComm_of_tmul_of]; rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]

/--
theorem `gradedComm_of_zero_tmul` / 定理 `gradedComm_of_zero_tmul`

English:
theorem gradedComm_of_zero_tmul
  given: (a : 𝒜 0) (b : ⨁ i, ℬ i)
  proof: by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)) (lof R _ 𝒜 0 a) =
      (TensorProduct.mk R _ _).flip (lof R _ 𝒜 0 a) from
    DFunLike.congr_fun this b
  ext i b
  dsimp
  rw [gradedComm_of_tmul_of]; rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]

中文:
定理 gradedComm_of_zero_tmul
  条件: (a : 𝒜 0) (b : ⨁ i, ℬ i)
  证明: by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)) (lof R _ 𝒜 0 a) =
      (TensorProduct.mk R _ _).flip (lof R _ 𝒜 0 a) from
    DFunLike.congr_fun this b
  ext i b
  dsimp
  rw [gradedComm_of_tmul_of]; rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, TensorProduct, TensorProduct.mk, congr_fun, gradedComm, gradedComm_of_tmul_of, mul_zero, one_smul, toLinearMap, uzpow_zero
-/
theorem gradedComm_of_zero_tmul (a : 𝒜 0) (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (lof R _ 𝒜 0 a otimesₜ b) = b otimesₜ lof R _ 𝒜 _ a := by
  suffices
    (gradedComm R 𝒜 ℬ).toLinearMap ∘ₗ (TensorProduct.mk R (⨁ i, 𝒜 i) (⨁ i, ℬ i)) (lof R _ 𝒜 0 a) =
      (TensorProduct.mk R _ _).flip (lof R _ 𝒜 0 a) from
    DFunLike.congr_fun this b
  ext i b
  dsimp
  rw [gradedComm_of_tmul_of]; rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]

/--
theorem `gradedComm_tmul_one` / 定理 `gradedComm_tmul_one`

English:
theorem gradedComm_tmul_one
  given: [GradedMonoid.GOne ℬ] (a : ⨁ i, 𝒜 i)
  proof: gradedComm_tmul_of_zero _ _ _ _ _

中文:
定理 gradedComm_tmul_one
  条件: [GradedMonoid.GOne ℬ] (a : ⨁ i, 𝒜 i)
  证明: gradedComm_tmul_of_zero _ _ _ _ _

Depends on / 依赖: gradedComm_tmul_of_zero
-/
theorem gradedComm_tmul_one [GradedMonoid.GOne ℬ] (a : ⨁ i, 𝒜 i) :
    gradedComm R 𝒜 ℬ (a otimesₜ 1) = 1 otimesₜ a :=
  gradedComm_tmul_of_zero _ _ _ _ _

/--
theorem `gradedComm_one_tmul` / 定理 `gradedComm_one_tmul`

English:
theorem gradedComm_one_tmul
  given: [GradedMonoid.GOne 𝒜] (b : ⨁ i, ℬ i)
  proof: gradedComm_of_zero_tmul _ _ _ _ _

@[simp]

中文:
定理 gradedComm_one_tmul
  条件: [GradedMonoid.GOne 𝒜] (b : ⨁ i, ℬ i)
  证明: gradedComm_of_zero_tmul _ _ _ _ _

@[simp]

Depends on / 依赖: gradedComm_of_zero_tmul
-/
theorem gradedComm_one_tmul [GradedMonoid.GOne 𝒜] (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (1 otimesₜ b) = b otimesₜ 1 :=
  gradedComm_of_zero_tmul _ _ _ _ _

@[simp]
/--
theorem `gradedComm_one` / 定理 `gradedComm_one`

English:
theorem gradedComm_one
  given: [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ]
  statement: gradedComm R 𝒜 ℬ 1 = 1
  proof: gradedComm_one_tmul _ _ _ _

中文:
定理 gradedComm_one
  条件: [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ]
  结论: gradedComm R 𝒜 ℬ 1 = 1
  证明: gradedComm_one_tmul _ _ _ _

Depends on / 依赖: gradedComm_one_tmul
-/
theorem gradedComm_one [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ] : gradedComm R 𝒜 ℬ 1 = 1 :=
  gradedComm_one_tmul _ _ _ _

/--
theorem `gradedComm_tmul_algebraMap` / 定理 `gradedComm_tmul_algebraMap`

English:
theorem gradedComm_tmul_algebraMap
  statement: [DirectSum.GSemiring ℬ] [DirectSum.GAlgebra R ℬ]
  proof: gradedComm_tmul_of_zero _ _ _ _ _

中文:
定理 gradedComm_tmul_algebraMap
  结论: [DirectSum.GSemiring ℬ] [DirectSum.GAlgebra R ℬ]
  证明: gradedComm_tmul_of_zero _ _ _ _ _

Depends on / 依赖: gradedComm_tmul_of_zero
-/
theorem gradedComm_tmul_algebraMap [DirectSum.GSemiring ℬ] [DirectSum.GAlgebra R ℬ]
    (a : ⨁ i, 𝒜 i) (r : R) :
    gradedComm R 𝒜 ℬ (a otimesₜ algebraMap R _ r) = algebraMap R _ r otimesₜ a :=
  gradedComm_tmul_of_zero _ _ _ _ _

/--
theorem `gradedComm_algebraMap_tmul` / 定理 `gradedComm_algebraMap_tmul`

English:
theorem gradedComm_algebraMap_tmul
  statement: [DirectSum.GSemiring 𝒜] [DirectSum.GAlgebra R 𝒜]
  proof: gradedComm_of_zero_tmul _ _ _ _ _

中文:
定理 gradedComm_algebraMap_tmul
  结论: [DirectSum.GSemiring 𝒜] [DirectSum.GAlgebra R 𝒜]
  证明: gradedComm_of_zero_tmul _ _ _ _ _

Depends on / 依赖: gradedComm_of_zero_tmul
-/
theorem gradedComm_algebraMap_tmul [DirectSum.GSemiring 𝒜] [DirectSum.GAlgebra R 𝒜]
    (r : R) (b : ⨁ i, ℬ i) :
    gradedComm R 𝒜 ℬ (algebraMap R _ r otimesₜ b) = b otimesₜ algebraMap R _ r :=
  gradedComm_of_zero_tmul _ _ _ _ _

/--
theorem `gradedComm_algebraMap` / 定理 `gradedComm_algebraMap`

English:
theorem gradedComm_algebraMap
  statement: [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ]
  proof: (gradedComm_algebraMap_tmul R 𝒜 ℬ r 1).trans (Algebra.TensorProduct.algebraMap_apply' r).symm

中文:
定理 gradedComm_algebraMap
  结论: [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ]
  证明: (gradedComm_algebraMap_tmul R 𝒜 ℬ r 1).trans (Algebra.TensorProduct.algebraMap_apply' r).symm

Depends on / 依赖: Algebra, Algebra.TensorProduct.algebraMap_apply, TensorProduct, algebraMap_apply, gradedComm_algebraMap_tmul
-/
theorem gradedComm_algebraMap [DirectSum.GSemiring 𝒜] [DirectSum.GSemiring ℬ]
    [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ] (r : R) :
    gradedComm R 𝒜 ℬ (algebraMap R _ r) = algebraMap R _ r :=
  (gradedComm_algebraMap_tmul R 𝒜 ℬ r 1).trans (Algebra.TensorProduct.algebraMap_apply' r).symm

end gradedComm

variable [DirectSum.GRing 𝒜] [DirectSum.GRing ℬ]
variable [DirectSum.GAlgebra R 𝒜] [DirectSum.GAlgebra R ℬ]

open TensorProduct (assoc map) in
/-- The multiplication operation for tensor products of externally `ι`-graded algebras. -/
noncomputable irreducible_def gradedMul :
    letI AB := DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ
    letI : Module R AB := TensorProduct.leftModule
    AB ->ₗ[R] AB ->ₗ[R] AB := by
  refine TensorProduct.curry ?_
  refine map (LinearMap.mul' R (⨁ i, 𝒜 i)) (LinearMap.mul' R (⨁ i, ℬ i)) ∘ₗ ?_
  refine (assoc R _ _ _).symm.toLinearMap ∘ₗ .lTensor _ ?_ ∘ₗ (assoc R _ _ _).toLinearMap
  refine (assoc R _ _ _).toLinearMap ∘ₗ .rTensor _ ?_ ∘ₗ (assoc R _ _ _).symm.toLinearMap
  exact (gradedComm _ _ _).toLinearMap

/--
theorem `tmul_of_gradedMul_of_tmul` / 定理 `tmul_of_gradedMul_of_tmul`

English:
theorem tmul_of_gradedMul_of_tmul
  statement: (j₁ i₂ : ι)
  proof: by
  rw [gradedMul]
  dsimp only [curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_tmul,
    map_tmul, LinearMap.id_coe, id_eq, assoc_symm_tmul, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  rw [mul_comm j₁ i₂]; rw [gradedComm_of_tmul_of]
  -- the tower smul l

中文:
定理 tmul_of_gradedMul_of_tmul
  结论: (j₁ i₂ : ι)
  证明: by
  rw [gradedMul]
  dsimp only [curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_tmul,
    map_tmul, LinearMap.id_coe, id_eq, assoc_symm_tmul, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  rw [mul_comm j₁ i₂]; rw [gradedComm_of_tmul_of]
  -- the tower smul l

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, LinearMap.id_coe, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, assoc_symm_tmul, assoc_tmul, coe_coe, coe_comp, comp_apply, curry_apply, gradedComm_of_tmul_of, gradedMul, id_coe, id_eq, lTensor_tmul
-/
theorem tmul_of_gradedMul_of_tmul (j₁ i₂ : ι)
    (a₁ : ⨁ i, 𝒜 i) (b₁ : ℬ j₁) (a₂ : 𝒜 i₂) (b₂ : ⨁ i, ℬ i) :
    gradedMul R 𝒜 ℬ (a₁ otimesₜ lof R _ ℬ j₁ b₁) (lof R _ 𝒜 i₂ a₂ otimesₜ b₂) =
      (-1 : Intˣ) ^ (j₁ * i₂) • ((a₁ * lof R _ 𝒜 _ a₂) otimesₜ (lof R _ ℬ _ b₁ * b₂)) := by
  rw [gradedMul]
  dsimp only [curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_tmul,
    map_tmul, LinearMap.id_coe, id_eq, assoc_symm_tmul, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]
  rw [mul_comm j₁ i₂]; rw [gradedComm_of_tmul_of]
  -- the tower smul lemmas elaborate too slowly
  rw [Units.smul_def]; rw [Units.smul_def]; rw [← Int.cast_smul_eq_zsmul R]; rw [← Int.cast_smul_eq_zsmul R]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to avoid timeouts.
  rw [← smul_tmul']; rw [LinearEquiv.map_smul]; rw [tmul_smul]; rw [LinearEquiv.map_smul]; rw [map_smul]
  dsimp

variable {R}

set_option backward.defeqAttrib.useBackward true in
/--
theorem `algebraMap_gradedMul` / 定理 `algebraMap_gradedMul`

English:
theorem algebraMap_gradedMul
  given: (r : R) (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i))
  proof: by
  suffices gradedMul R 𝒜 ℬ (algebraMap R _ r otimesₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext ia a ib b
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]; rw [smul_tmul']
  erw [one_mul, _root_.Algebra.smul_def]

中文:
定理 algebraMap_gradedMul
  条件: (r : R) (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i))
  证明: by
  suffices gradedMul R 𝒜 ℬ (algebraMap R _ r otimesₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext ia a ib b
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]; rw [smul_tmul']
  erw [one_mul, _root_.Algebra.smul_def]

Depends on / 依赖: Algebra, DFunLike, DFunLike.congr_fun, DistribSMul, DistribSMul.toLinearMap, _root_, _root_.Algebra.smul_def, algebraMap, congr_fun, gradedMul, one_mul, one_smul, smul_def, smul_tmul, tmul_of_gradedMul_of_tmul, toLinearMap, uzpow_zero, zero_mul
-/
theorem algebraMap_gradedMul (r : R) (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ (algebraMap R _ r otimesₜ 1) x = r • x := by
  suffices gradedMul R 𝒜 ℬ (algebraMap R _ r otimesₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext ia a ib b
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [zero_mul]; rw [uzpow_zero]; rw [one_smul]; rw [smul_tmul']
  erw [one_mul, _root_.Algebra.smul_def]

/--
theorem `one_gradedMul` / 定理 `one_gradedMul`

English:
theorem one_gradedMul
  given: (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i))
  proof: by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! algebraMap_gradedMul 𝒜 ℬ 1 x

中文:
定理 one_gradedMul
  条件: (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i))
  证明: by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! algebraMap_gradedMul 𝒜 ℬ 1 x
-/
theorem one_gradedMul (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ 1 x = x := by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! algebraMap_gradedMul 𝒜 ℬ 1 x

set_option backward.defeqAttrib.useBackward true in
/--
theorem `gradedMul_algebraMap` / 定理 `gradedMul_algebraMap`

English:
theorem gradedMul_algebraMap
  given: (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) (r : R)
  proof: by
  suffices (gradedMul R 𝒜 ℬ).flip (algebraMap R _ r otimesₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]; rw [smul_tmul']; rw [mul_one]; rw [_root_.Algebra.smul_def]; rw [A

中文:
定理 gradedMul_algebraMap
  条件: (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) (r : R)
  证明: by
  suffices (gradedMul R 𝒜 ℬ).flip (algebraMap R _ r otimesₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]; rw [smul_tmul']; rw [mul_one]; rw [_root_.Algebra.smul_def]; rw [A

Depends on / 依赖: Algebra, Algebra.commutes, DFunLike, DFunLike.congr_fun, DistribSMul, DistribSMul.toLinearMap, _root_, _root_.Algebra.smul_def, algebraMap, commutes, congr_fun, gradedMul, mul_one, mul_zero, one_smul, smul_def, smul_tmul, tmul_of_gradedMul_of_tmul, toLinearMap, uzpow_zero
-/
theorem gradedMul_algebraMap (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) (r : R) :
    gradedMul R 𝒜 ℬ x (algebraMap R _ r otimesₜ 1) = r • x := by
  suffices (gradedMul R 𝒜 ℬ).flip (algebraMap R _ r otimesₜ 1) = DistribSMul.toLinearMap R _ r by
    exact DFunLike.congr_fun this x
  ext
  dsimp
  erw [tmul_of_gradedMul_of_tmul]
  rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]; rw [smul_tmul']; rw [mul_one]; rw [_root_.Algebra.smul_def]; rw [Algebra.commutes]
  rfl

/--
theorem `gradedMul_one` / 定理 `gradedMul_one`

English:
theorem gradedMul_one
  given: (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i))
  proof: by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! gradedMul_algebraMap 𝒜 ℬ x 1

中文:
定理 gradedMul_one
  条件: (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i))
  证明: by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! gradedMul_algebraMap 𝒜 ℬ x 1
-/
theorem gradedMul_one (x : (⨁ i, 𝒜 i) otimes[R] (⨁ i, ℬ i)) :
    gradedMul R 𝒜 ℬ x 1 = x := by
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_one` to avoid timeouts.
  simpa only [RingHom.map_one, one_smul] using! gradedMul_algebraMap 𝒜 ℬ x 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `gradedMul_assoc` / 定理 `gradedMul_assoc`

English:
theorem gradedMul_assoc
  given: (x y z : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ)
  proof: by
  let mA := gradedMul R 𝒜 ℬ
    -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mA ∘ₗ mA =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mA.flip ∘ₗ mA).flip by
    exact DFunLike.congr_fun (DFunL

中文:
定理 gradedMul_assoc
  条件: (x y z : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ)
  证明: by
  let mA := gradedMul R 𝒜 ℬ
    -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mA ∘ₗ mA =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mA.flip ∘ₗ mA).flip by
    exact DFunLike.congr_fun (DFunL

Depends on / 依赖: gradedMul
-/
theorem gradedMul_assoc (x y z : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ) :
    gradedMul R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y) z = gradedMul R 𝒜 ℬ x (gradedMul R 𝒜 ℬ y z) := by
  let mA := gradedMul R 𝒜 ℬ
    -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mA ∘ₗ mA =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mA.flip ∘ₗ mA).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext ixa xa ixb xb iya ya iyb yb iza za izb zb
  dsimp [mA]
  simp_rw [tmul_of_gradedMul_of_tmul, Units.smul_def, ← Int.cast_smul_eq_zsmul R,
    LinearMap.map_smul₂, map_smul, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, tmul_of_gradedMul_of_tmul, DirectSum.lof_eq_of, ← DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, mul_assoc]
  simp_rw [Int.cast_smul_eq_zsmul R, ← Units.smul_def, smul_smul, ← uzpow_add, add_mul, mul_add]
  congr 2
  abel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `gradedComm_gradedMul` / 定理 `gradedComm_gradedMul`

English:
theorem gradedComm_gradedMul
  given: (x y : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ)
  proof: by
  suffices (gradedMul R 𝒜 ℬ).compr₂ (gradedComm R 𝒜 ℬ).toLinearMap
      = (gradedMul R ℬ 𝒜 ∘ₗ (gradedComm R 𝒜 ℬ).toLinearMap).compl₂
        (gradedComm R 𝒜 ℬ).toLinearMap from
    LinearMap.congr_fun₂ this x y
  ext i₁ a₁ j₁ b₁ i₂ a₂ j₂ b₂
  dsimp
  rw [gradedComm_of_tmul_of]; rw [gradedComm_of

中文:
定理 gradedComm_gradedMul
  条件: (x y : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ)
  证明: by
  suffices (gradedMul R 𝒜 ℬ).compr₂ (gradedComm R 𝒜 ℬ).toLinearMap
      = (gradedMul R ℬ 𝒜 ∘ₗ (gradedComm R 𝒜 ℬ).toLinearMap).compl₂
        (gradedComm R 𝒜 ℬ).toLinearMap from
    LinearMap.congr_fun₂ this x y
  ext i₁ a₁ j₁ b₁ i₂ a₂ j₂ b₂
  dsimp
  rw [gradedComm_of_tmul_of]; rw [gradedComm_of

Depends on / 依赖: LinearMap, LinearMap.congr_fun, gradedComm, gradedComm_of_tmul_of, gradedMul, tmul_of_gradedMul_of_tmul, toLinearMap
-/
theorem gradedComm_gradedMul (x y : DirectSum _ 𝒜 otimes[R] DirectSum _ ℬ) :
    gradedComm R 𝒜 ℬ (gradedMul R 𝒜 ℬ x y)
      = gradedMul R ℬ 𝒜 (gradedComm R 𝒜 ℬ x) (gradedComm R 𝒜 ℬ y) := by
  suffices (gradedMul R 𝒜 ℬ).compr₂ (gradedComm R 𝒜 ℬ).toLinearMap
      = (gradedMul R ℬ 𝒜 ∘ₗ (gradedComm R 𝒜 ℬ).toLinearMap).compl₂
        (gradedComm R 𝒜 ℬ).toLinearMap from
    LinearMap.congr_fun₂ this x y
  ext i₁ a₁ j₁ b₁ i₂ a₂ j₂ b₂
  dsimp
  rw [gradedComm_of_tmul_of]; rw [gradedComm_of_tmul_of]; rw [tmul_of_gradedMul_of_tmul]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specialize `map_smul` to avoid timeouts.
  simp_rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R, LinearEquiv.map_smul, map_smul,
    LinearMap.smul_apply]
  simp_rw [Int.cast_smul_eq_zsmul R, ← Units.smul_def, DirectSum.lof_eq_of, DirectSum.of_mul_of,
    ← DirectSum.lof_eq_of R, gradedComm_of_tmul_of, tmul_of_gradedMul_of_tmul, smul_smul,
    DirectSum.lof_eq_of, ← DirectSum.of_mul_of, ← DirectSum.lof_eq_of R]
  simp_rw [← uzpow_add, mul_add, add_mul, mul_comm i₁ j₂]
  congr 1
  abel_nf
  rw [two_nsmul]; rw [uzpow_add]; rw [uzpow_add]; rw [Int.units_mul_self]; rw [one_mul]

end TensorProduct
