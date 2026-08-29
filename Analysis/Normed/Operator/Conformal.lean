/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Conformal Linear Maps

A continuous linear map between `R`-normed spaces `X` and `Y` `IsConformalMap` if it is
a nonzero multiple of a linear isometry.

## Main definitions

* `IsConformalMap`: the main definition of conformal linear maps

## Main results

* The conformality of the composition of two conformal linear maps, the identity map
  and multiplications by nonzero constants as continuous linear maps
* `isConformalMap_of_subsingleton`: all continuous linear maps on singleton spaces are conformal

See `Analysis.InnerProductSpace.ConformalLinearMap` for
* `isConformalMap_iff`: a map between inner product spaces is conformal
  iff it preserves inner products up to a fixed scalar factor.


## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
-/

@[expose] public section


noncomputable section

open Function LinearIsometry ContinuousLinearMap

/--
Definition of `IsConformalMap` / `IsConformalMap` 的定义

English:
definition IsConformalMap
  signature: {R : Type*} {X Y : Type*} [NormedField R] [SeminormedAddCommGroup X]
  body: exists c != (0 : R), exists li : X ->ₗᵢ[R] Y, f' = c • li.toContinuousLinearMap

中文:
定义 IsConformalMap
  签名: {R : 类型} {X Y : 类型} [赋范域 R] [SeminormedAddComm群 X]
  定义体: exists c != (0 : R), exists li : X ->ₗᵢ[R] Y, f' = c • li.toContinuousLinearMap

Depends on / 依赖: li.toContinuousLinearMap, toContinuousLinearMap
-/
def IsConformalMap {R : Type*} {X Y : Type*} [NormedField R] [SeminormedAddCommGroup X]
    [SeminormedAddCommGroup Y] [NormedSpace R X] [NormedSpace R Y] (f' : X ->L[R] Y) :=
  exists c != (0 : R), exists li : X ->ₗᵢ[R] Y, f' = c • li.toContinuousLinearMap

variable {R M N G M' : Type*} [NormedField R] [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]
  [SeminormedAddCommGroup G] [NormedSpace R M] [NormedSpace R N] [NormedSpace R G]
  [NormedAddCommGroup M'] [NormedSpace R M'] {f : M ->L[R] N} {g : N ->L[R] G} {c : R}

/--
theorem `isConformalMap_id` / 定理 `isConformalMap_id`

English:
theorem isConformalMap_id
  statement: IsConformalMap (.id R M)
  proof: ⟨1, one_ne_zero, id, by simp⟩

中文:
定理 isConformalMap_id
  结论: IsConformalMap (.id R M)
  证明: ⟨1, one_ne_zero, id, by simp⟩

Depends on / 依赖: one_ne_zero
-/
theorem isConformalMap_id : IsConformalMap (.id R M) :=
  ⟨1, one_ne_zero, id, by simp⟩

/--
theorem `IsConformalMap.smul` / 定理 `IsConformalMap.smul`

English:
theorem IsConformalMap.smul
  given: (hf : IsConformalMap f) {c : R} (hc : c != 0)
  proof: by
  rcases hf with ⟨c', hc', li, rfl⟩
  exact ⟨c * c', mul_ne_zero hc hc', li, smul_smul _ _ _⟩

中文:
定理 IsConformalMap.smul
  条件: (hf : IsConformalMap f) {c : R} (hc : c != 0)
  证明: by
  rcases hf with ⟨c', hc', li, rfl⟩
  exact ⟨c * c', mul_ne_zero hc hc', li, smul_smul _ _ _⟩

Depends on / 依赖: mul_ne_zero, smul_smul
-/
theorem IsConformalMap.smul (hf : IsConformalMap f) {c : R} (hc : c != 0) :
    IsConformalMap (c • f) := by
  rcases hf with ⟨c', hc', li, rfl⟩
  exact ⟨c * c', mul_ne_zero hc hc', li, smul_smul _ _ _⟩

/--
theorem `isConformalMap_const_smul` / 定理 `isConformalMap_const_smul`

English:
theorem isConformalMap_const_smul
  given: (hc : c != 0)
  statement: IsConformalMap (c • .id R M)
  proof: isConformalMap_id.smul hc

中文:
定理 isConformalMap_const_smul
  条件: (hc : c != 0)
  结论: IsConformalMap (c • .id R M)
  证明: isConformalMap_id.smul hc

Depends on / 依赖: isConformalMap_id, isConformalMap_id.smul
-/
theorem isConformalMap_const_smul (hc : c != 0) : IsConformalMap (c • .id R M) :=
  isConformalMap_id.smul hc

/--
theorem `LinearIsometry.isConformalMap` / 定理 `LinearIsometry.isConformalMap`

English:
theorem LinearIsometry.isConformalMap
  given: (f' : M ->ₗᵢ[R] N)
  proof: ⟨1, one_ne_zero, f', (one_smul _ _).symm⟩

@[nontriviality]

中文:
定理 线性等距.isConformalMap
  条件: (f' : M ->ₗᵢ[R] N)
  证明: ⟨1, one_ne_zero, f', (one_smul _ _).symm⟩

@[nontriviality]
-/
protected theorem LinearIsometry.isConformalMap (f' : M ->ₗᵢ[R] N) :
    IsConformalMap f'.toContinuousLinearMap :=
  ⟨1, one_ne_zero, f', (one_smul _ _).symm⟩

@[nontriviality]
/--
theorem `isConformalMap_of_subsingleton` / 定理 `isConformalMap_of_subsingleton`

English:
theorem isConformalMap_of_subsingleton
  given: [Subsingleton M] (f' : M ->L[R] N)
  statement: IsConformalMap f'
  proof: ⟨1, one_ne_zero, ⟨0, fun x => by simp [Subsingleton.elim x 0]⟩, Subsingleton.elim _ _⟩

中文:
定理 isConformalMap_of_subsingleton
  条件: [子单例 M] (f' : M ->L[R] N)
  结论: IsConformalMap f'
  证明: ⟨1, one_ne_zero, ⟨0, fun x => by simp [Subsingleton.elim x 0]⟩, Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, one_ne_zero
-/
theorem isConformalMap_of_subsingleton [Subsingleton M] (f' : M ->L[R] N) : IsConformalMap f' :=
  ⟨1, one_ne_zero, ⟨0, fun x => by simp [Subsingleton.elim x 0]⟩, Subsingleton.elim _ _⟩

namespace IsConformalMap

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hg : IsConformalMap g) (hf : IsConformalMap f)
  statement: IsConformalMap (g.comp f)
  proof: by
  rcases hf with ⟨cf, hcf, lif, rfl⟩
  rcases hg with ⟨cg, hcg, lig, rfl⟩
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, ?_⟩
  rw [smul_comp]; rw [comp_smul]; rw [mul_smul]
  rfl

中文:
定理 comp
  条件: (hg : IsConformalMap g) (hf : IsConformalMap f)
  结论: IsConformalMap (g.comp f)
  证明: by
  rcases hf with ⟨cf, hcf, lif, rfl⟩
  rcases hg with ⟨cg, hcg, lig, rfl⟩
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, ?_⟩
  rw [smul_comp]; rw [comp_smul]; rw [mul_smul]
  rfl

Depends on / 依赖: comp_smul, lig.comp, mul_ne_zero, mul_smul, smul_comp
-/
theorem comp (hg : IsConformalMap g) (hf : IsConformalMap f) : IsConformalMap (g.comp f) := by
  rcases hf with ⟨cf, hcf, lif, rfl⟩
  rcases hg with ⟨cg, hcg, lig, rfl⟩
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, ?_⟩
  rw [smul_comp]; rw [comp_smul]; rw [mul_smul]
  rfl

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: {f : M' ->L[R] N} (h : IsConformalMap f)
  statement: Function.Injective f
  proof: by
  rcases h with ⟨c, hc, li, rfl⟩
  exact (smul_right_injective _ hc).comp li.injective

中文:
定理 injective
  条件: {f : M' ->L[R] N} (h : IsConformalMap f)
  结论: 函数.单射 f
  证明: by
  rcases h with ⟨c, hc, li, rfl⟩
  exact (smul_right_injective _ hc).comp li.injective
-/
protected theorem injective {f : M' ->L[R] N} (h : IsConformalMap f) : Function.Injective f := by
  rcases h with ⟨c, hc, li, rfl⟩
  exact (smul_right_injective _ hc).comp li.injective

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: [Nontrivial M'] {f' : M' ->L[R] N} (hf' : IsConformalMap f')
  statement: f' != 0
  proof: by
  rintro rfl
  rcases exists_ne (0 : M') with ⟨a, ha⟩
  exact ha (hf'.injective rfl)

中文:
定理 ne_zero
  条件: [非平凡 M'] {f' : M' ->L[R] N} (hf' : IsConformalMap f')
  结论: f' != 0
  证明: by
  rintro rfl
  rcases exists_ne (0 : M') with ⟨a, ha⟩
  exact ha (hf'.injective rfl)

Depends on / 依赖: exists_ne, injective
-/
theorem ne_zero [Nontrivial M'] {f' : M' ->L[R] N} (hf' : IsConformalMap f') : f' != 0 := by
  rintro rfl
  rcases exists_ne (0 : M') with ⟨a, ha⟩
  exact ha (hf'.injective rfl)

end IsConformalMap
