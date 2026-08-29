/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Basis

/-!
# Mₙ(R)-module structure on `Mⁿ`

## Main Results

- `Matrix.Module.matrixModule`: This instance shows `ι → M` is a module over `Matrix ι ι R`, and
  the action of it is a generalization of `Matrix.mulVec`, this is only available in the
  `Matrix.Module` namespace.
- `LinearMap.mapMatrixModule`: This defines a linear map from `ι → M` to `ι → N` over
  `Matrix ι ι R` induced by a linear map from `M` to `N` and together with `Matrix.matrixModule`
  it gives a functor from the category of `R`-modules to the category of `Matrix ι ι R`-modules.

## Tags
matrix, module
-/

@[expose] public section

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

namespace Matrix.Module

/-- `Mⁿ` is a `Mₙ(R)` module, note that this creates a diamond when `M` is `Matrix ι ι R` or when
  `M` is `R`. -/
scoped instance matrixModule : Module (Matrix ι ι R) (ι -> M) where
  smul N v i := ∑ j : ι, N i j • v j
  one_smul v := funext fun i => show ∑ _, _ = _ by simp [one_apply]
  mul_smul N₁ N₂ v := funext fun i => show ∑ _, _ = ∑ _, _ • (∑ _, _) by
    simp_rw [mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
  smul_zero v := funext fun i => show ∑ _, _ = _ by simp
  smul_add N v₁ v₂ := funext fun i => show ∑ j : ι, N i j • (v₁ + v₂) j = (∑ _, _) + (∑ _, _) by
    simp [smul_add, Finset.sum_add_distrib]
  add_smul N₁ N₂ v := funext fun i => show ∑ j : ι, (N₁ + N₂) i j • v j = (∑ _, _) + (∑ _, _) by
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul v := funext fun i => show ∑ _, _ = _ by simp

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (N : Matrix ι ι R) (v : ι -> M)
  proof: rfl

中文:
引理 smul_def
  条件: (N : 矩阵 ι ι R) (v : ι -> M)
  证明: rfl
-/
lemma smul_def (N : Matrix ι ι R) (v : ι -> M) :
    N • v = fun i => ∑ j : ι, N i j • v j := rfl

/--
lemma `smul_def'` / 引理 `smul_def'`

English:
lemma smul_def'
  given: (N : Matrix ι ι R) (v : ι -> M)
  statement: N • v = ∑ j : ι, fun i => N i j • v j
  proof: by
  ext; simp [smul_def]

@[simp]

中文:
引理 smul_def'
  条件: (N : 矩阵 ι ι R) (v : ι -> M)
  结论: N • v = ∑ j : ι, fun i => N i j • v j
  证明: by
  ext; simp [smul_def]

@[simp]

Depends on / 依赖: smul_def
-/
lemma smul_def' (N : Matrix ι ι R) (v : ι -> M) : N • v = ∑ j : ι, fun i => N i j • v j := by
  ext; simp [smul_def]

@[simp]
/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: (N : Matrix ι ι R) (v : ι -> M) (i : ι)
  proof: rfl

@[simp]

中文:
引理 smul_apply
  条件: (N : 矩阵 ι ι R) (v : ι -> M) (i : ι)
  证明: rfl

@[simp]
-/
lemma smul_apply (N : Matrix ι ι R) (v : ι -> M) (i : ι) :
    (N • v) i = ∑ j : ι, N i j • v j := rfl

@[simp]
/--
theorem `single_smul` / 定理 `single_smul`

English:
theorem single_smul
  given: (i j : ι) (r : R) (v : ι -> M)
  proof: by
  ext i'
  dsimp
  rw [Fintype.sum_eq_single j fun j' hj => ?_]
  · obtain rfl | hi := eq_or_ne i i' <;> simp [*]
  · simp [hj.symm]

@[simp]

中文:
定理 single_smul
  条件: (i j : ι) (r : R) (v : ι -> M)
  证明: by
  ext i'
  dsimp
  rw [Fintype.sum_eq_single j fun j' hj => ?_]
  · obtain rfl | hi := eq_or_ne i i' <;> simp [*]
  · simp [hj.symm]

@[simp]

Depends on / 依赖: Fintype, Fintype.sum_eq_single, eq_or_ne, hj.symm, sum_eq_single
-/
theorem single_smul (i j : ι) (r : R) (v : ι -> M) :
    Matrix.single i j r • v = Pi.single i (r • v j) := by
  ext i'
  dsimp
  rw [Fintype.sum_eq_single j fun j' hj => ?_]
  · obtain rfl | hi := eq_or_ne i i' <;> simp [*]
  · simp [hj.symm]

@[simp]
/--
lemma `diagonal_const_smul` / 引理 `diagonal_const_smul`

English:
lemma diagonal_const_smul
  given: (r : R) (v : ι -> M)
  proof: by
  ext i
  simp [Matrix.diagonal_apply]

中文:
引理 diagonal_const_smul
  条件: (r : R) (v : ι -> M)
  证明: by
  ext i
  simp [Matrix.diagonal_apply]

Depends on / 依赖: Matrix, Matrix.diagonal_apply, diagonal_apply
-/
lemma diagonal_const_smul (r : R) (v : ι -> M) :
    diagonal (fun _ : ι => r) • v = r • v := by
  ext i
  simp [Matrix.diagonal_apply]

/--
lemma `scalar_smul` / 引理 `scalar_smul`

English:
lemma scalar_smul
  given: (r : R) (v : ι -> M)
  proof: by
  simp

scoped instance (S : Type*) [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    IsScalarTower R (Matrix ι ι S) (ι -> M) where
  smul_assoc _ _ _ := by ext; simp [Finset.smul_sum]

中文:
引理 scalar_smul
  条件: (r : R) (v : ι -> M)
  证明: by
  simp

scoped instance (S : Type*) [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    IsScalarTower R (Matrix ι ι S) (ι -> M) where
  smul_assoc _ _ _ := by ext; simp [Finset.smul_sum]
-/
lemma scalar_smul (r : R) (v : ι -> M) :
    Matrix.scalar ι r • v = r • v := by
  simp

scoped instance (S : Type*) [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    IsScalarTower R (Matrix ι ι S) (ι -> M) where
  smul_assoc _ _ _ := by ext; simp [Finset.smul_sum]

end Matrix.Module

namespace LinearMap

open Matrix.Module

variable (ι) in
/-- The induced linear map from `Mⁿ` to `Nⁿ` by a linear map `f : M → N`, this is the matrix linear
  version of `LinearMap.compLeft`. -/
@[simps]
/--
Definition of `mapMatrixModule` / `mapMatrixModule` 的定义

English:
definition mapMatrixModule
  signature: (f : M ->ₗ[R] N)
  body: LinearMap.compLeft f ι
  map_add' := map_add _
  map_smul' _ _ := by ext; simp

@[simp]

中文:
定义 mapMatrixModule
  签名: (f : M ->ₗ[R] N)
  定义体: LinearMap.compLeft f ι
  map_add' := map_add _
  map_smul' _ _ := by ext; simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.compLeft, compLeft
-/
def mapMatrixModule (f : M ->ₗ[R] N) : (ι -> M) ->ₗ[Matrix ι ι R] (ι -> N) where
  toFun := LinearMap.compLeft f ι
  map_add' := map_add _
  map_smul' _ _ := by ext; simp

@[simp]
/--
lemma `mapMatrixModule_id` / 引理 `mapMatrixModule_id`

English:
lemma mapMatrixModule_id
  proof: by
  ext; simp

中文:
引理 mapMatrixModule_id
  证明: by
  ext; simp

Depends on / 依赖: Matrix
-/
lemma mapMatrixModule_id :
    LinearMap.id.mapMatrixModule ι = .id (R := Matrix ι ι R) (M := ι -> M) := by
  ext; simp

/--
lemma `mapMatrixModule_id_apply` / 引理 `mapMatrixModule_id_apply`

English:
lemma mapMatrixModule_id_apply
  given: (v : ι -> M)
  proof: by
  simp

中文:
引理 mapMatrixModule_id_apply
  条件: (v : ι -> M)
  证明: by
  simp
-/
lemma mapMatrixModule_id_apply (v : ι -> M) :
    LinearMap.id.mapMatrixModule ι (R := R) v = v := by
  simp

/--
lemma `mapMatrixModule_comp` / 引理 `mapMatrixModule_comp`

English:
lemma mapMatrixModule_comp
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  proof: by
  ext; simp

@[simp]

中文:
引理 mapMatrixModule_comp
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  证明: by
  ext; simp

@[simp]
-/
lemma mapMatrixModule_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) :
    (g ∘ₗ f).mapMatrixModule ι = g.mapMatrixModule ι ∘ₗ f.mapMatrixModule ι := by
  ext; simp

@[simp]
/--
lemma `mapMatrixModule_comp_apply` / 引理 `mapMatrixModule_comp_apply`

English:
lemma mapMatrixModule_comp_apply
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (v : ι -> M)
  proof: by
  simp [mapMatrixModule_comp]

中文:
引理 mapMatrixModule_comp_apply
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (v : ι -> M)
  证明: by
  simp [mapMatrixModule_comp]

Depends on / 依赖: mapMatrixModule_comp
-/
lemma mapMatrixModule_comp_apply (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (v : ι -> M) :
    (g ∘ₗ f).mapMatrixModule ι v =
      g.mapMatrixModule ι (f.mapMatrixModule ι v) := by
  simp [mapMatrixModule_comp]

end LinearMap
