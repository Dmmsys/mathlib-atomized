/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Separation.DisjointCover

/-!
# Uniform approximation by products

We show that if `X, Y` are compact Hausdorff spaces with `X` profinite, then any continuous function
on `X × Y` valued in a ring (with a uniform structure) can be uniformly approximated by finite
sums of functions of the form `f x * g y`.
-/

public section

open UniformSpace

open scoped Uniformity

namespace ContinuousMap

variable {X Y R V : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y]
  [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] {S : Set (V × V)}

/--
lemma `exists_finite_sum_smul_approximation_of_mem_uniformity` / 引理 `exists_finite_sum_smul_approximation_of_mem_uniformity`

English:
lemma exists_finite_sum_smul_approximation_of_mem_uniformity
  statement: [TopologicalSpace R]
  proof: by
  have hS' : {(f, g) | forall y, (f y, g y) in S} in 𝓤 C(Y, V) :=
    (mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
    f.curry (nhdsSet_diagonal_le_uniformity hS')
refine ⟨n, fun i => ⟨_, (U i).isClopen.continuous_indicator continuous_const (y := 1)⟩,
    v, fun x y => ?_⟩
  convert! hv x y using 2
  simp only [sum_apply]
  congr 1 with i
  by_cases hi : x in U i <;> simp [hi]

中文:
引理 存在_finite_sum_smul_approximation_of_mem_uniformity
  结论: [拓扑空间 R]
  证明: by
  have hS' : {(f, g) | forall y, (f y, g y) in S} in 𝓤 C(Y, V) :=
    (mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
    f.curry (nhdsSet_diagonal_le_uniformity hS')
refine ⟨n, fun i => ⟨_, (U i).isClopen.continuous_indicator continuous_const (y := 1)⟩,
    v, fun x y => ?_⟩
  convert! hv x y using 2
  simp only [sum_apply]
  congr 1 with i
  by_cases hi : x in U i <;> simp [hi]

Depends on / 依赖: Set.mem_univ, continuous_const, continuous_indicator, convert, exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal, f.curry, isClopen, isClopen.continuous_indicator, isCompact_univ, mem_compactConvergence_entourage_iff, mem_univ, nhdsSet_diagonal_le_uniformity, subset_refl, sum_apply, true_implies
-/
lemma exists_finite_sum_smul_approximation_of_mem_uniformity [TopologicalSpace R]
    [MonoidWithZero R] [MulActionWithZero R V] (f : C(X × Y, V)) (hS : S in 𝓤 V) :
    exists (n : Nat) (g : Fin n -> C(X, R)) (h : Fin n -> C(Y, V)),
    forall x y, (f (x, y), ∑ i, g i x • h i y) in S := by
  have hS' : {(f, g) | forall y, (f y, g y) in S} in 𝓤 C(Y, V) :=
    (mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
    f.curry (nhdsSet_diagonal_le_uniformity hS')
refine ⟨n, fun i => ⟨_, (U i).isClopen.continuous_indicator continuous_const (y := 1)⟩,
    v, fun x y => ?_⟩
  convert! hv x y using 2
  simp only [sum_apply]
  congr 1 with i
  by_cases hi : x in U i <;> simp [hi]

/--
lemma `exists_finite_sum_mul_approximation_of_mem_uniformity` / 引理 `exists_finite_sum_mul_approximation_of_mem_uniformity`

English:
lemma exists_finite_sum_mul_approximation_of_mem_uniformity
  statement: [Ring R] [UniformSpace R]
  proof: exists_finite_sum_smul_approximation_of_mem_uniformity f hS

中文:
引理 存在_finite_sum_mul_approximation_of_mem_uniformity
  结论: [环 R] [一致空间 R]
  证明: exists_finite_sum_smul_approximation_of_mem_uniformity f hS

Depends on / 依赖: exists_finite_sum_smul_approximation_of_mem_uniformity
-/
lemma exists_finite_sum_mul_approximation_of_mem_uniformity [Ring R] [UniformSpace R]
    [IsUniformAddGroup R] (f : C(X × Y, R)) {S : Set (R × R)} (hS : S in 𝓤 R) :
    exists (n : Nat) (g : Fin n -> C(X, R)) (h : Fin n -> C(Y, R)),
    forall x y, (f (x, y), ∑ i, g i x * h i y) in S :=
  exists_finite_sum_smul_approximation_of_mem_uniformity f hS

section prodMul

open scoped TensorProduct

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/--
Definition of `prodMul` / `prodMul` 的定义

English:
definition prodMul
  signature: : C(X, R) ->ₗ[R] C(Y, R) ->ₗ[R] C(X × Y, R)
  body: LinearMap.mk₂ R (fun f g => (f.comp .fst) * (g.comp .snd))
    (fun f f' g => by ext; simp [add_mul])
    (fun r f g => by ext; simp)
    (fun f g g' => by ext; simp [mul_add])
    (fun r f g => by ext; simp)

中文:
定义 prodMul
  签名: : C(X, R) ->ₗ[R] C(Y, R) ->ₗ[R] C(X × Y, R)
  定义体: LinearMap.mk₂ R (fun f g => (f.comp .fst) * (g.comp .snd))
    (fun f f' g => by ext; simp [add_mul])
    (fun r f g => by ext; simp)
    (fun f g g' => by ext; simp [mul_add])
    (fun r f g => by ext; simp)

Depends on / 依赖: LinearMap, LinearMap.mk, add_mul, f.comp, g.comp, mul_add
-/
def prodMul : C(X, R) ->ₗ[R] C(Y, R) ->ₗ[R] C(X × Y, R) :=
  LinearMap.mk₂ R (fun f g => (f.comp .fst) * (g.comp .snd))
    (fun f f' g => by ext; simp [add_mul])
    (fun r f g => by ext; simp)
    (fun f g g' => by ext; simp [mul_add])
    (fun r f g => by ext; simp)

/--
lemma `prodMul_apply` / 引理 `prodMul_apply`

English:
lemma prodMul_apply
  given: (f : C(X, R)) (g : C(Y, R)) (p : X × Y)
  proof: (rfl)

中文:
引理 prodMul_apply
  条件: (f : C(X, R)) (g : C(Y, R)) (p : X × Y)
  证明: (rfl)
-/
@[simp] lemma prodMul_apply (f : C(X, R)) (g : C(Y, R)) (p : X × Y) :
    f.prodMul g p = f p.1 * g p.2 :=
  (rfl)

/--
lemma `prodMul_def` / 引理 `prodMul_def`

English:
lemma prodMul_def
  given: (f : C(X, R)) (g : C(Y, R))
  proof: (rfl)

中文:
引理 prodMul_def
  条件: (f : C(X, R)) (g : C(Y, R))
  证明: (rfl)
-/
lemma prodMul_def (f : C(X, R)) (g : C(Y, R)) :
    f.prodMul g = f.comp .fst * g.comp .snd :=
  (rfl)

/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
definition tensorHom
  signature: : C(X, R) otimes[R] C(Y, R) ->ₗ[R] C(X × Y, R)
  body: TensorProduct.lift prodMul

@[simp]

中文:
定义 tensorHom
  签名: : C(X, R) otimes[R] C(Y, R) ->ₗ[R] C(X × Y, R)
  定义体: TensorProduct.lift prodMul

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.lift, prodMul
-/
def tensorHom : C(X, R) otimes[R] C(Y, R) ->ₗ[R] C(X × Y, R) :=
  TensorProduct.lift prodMul

@[simp]
/--
lemma `tensorHom_tmul` / 引理 `tensorHom_tmul`

English:
lemma tensorHom_tmul
  given: (f : C(X, R)) (g : C(Y, R))
  proof: by
  rw [tensorHom]; rw [TensorProduct.lift.tmul]

中文:
引理 tensorHom_tmul
  条件: (f : C(X, R)) (g : C(Y, R))
  证明: by
  rw [tensorHom]; rw [TensorProduct.lift.tmul]

Depends on / 依赖: TensorProduct, TensorProduct.lift.tmul, tensorHom
-/
lemma tensorHom_tmul (f : C(X, R)) (g : C(Y, R)) :
    tensorHom (f otimesₜ g) = prodMul f g := by
  rw [tensorHom]; rw [TensorProduct.lift.tmul]

/--
lemma `denseRange_tensorHom` / 引理 `denseRange_tensorHom`

English:
lemma denseRange_tensorHom
  statement: [CompactSpace X] [T2Space X] [CompactSpace Y]
  proof: by
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  intro f
  simp_rw [mem_closure_iff, Set.nonempty_def]
  intro U hUo hUf
  have := mem_nhds_uniformity_iff_right.mp (hUo.mem_nhds hUf)
  obtain ⟨J, hJu, hJ'⟩ := (hasBasis_compactConvergenceUniformity_of_compact).mem_iff.mp this
  obtain ⟨n, g, h, hgh⟩ := exists_finite_sum_mul_approximation_of_mem_uniformity f hJu
  have hG := Set.mem_of_subset_of_mem hJ' (a := (f, tensorHom <| ∑ i, g i otimesₜ h i))
  simp only [Prod.forall, Set.mem_ofPred_eq, forall_const] at hG
simpa using ⟨_, hG by simpa [tensorHom] using hgh⟩

中文:
引理 denseRange_tensorHom
  结论: [紧空间 X] [T2空间 X] [紧空间 Y]
  证明: by
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  intro f
  simp_rw [mem_closure_iff, Set.nonempty_def]
  intro U hUo hUf
  have := mem_nhds_uniformity_iff_right.mp (hUo.mem_nhds hUf)
  obtain ⟨J, hJu, hJ'⟩ := (hasBasis_compactConvergenceUniformity_of_compact).mem_iff.mp this
  obtain ⟨n, g, h, hgh⟩ := exists_finite_sum_mul_approximation_of_mem_uniformity f hJu
  have hG := Set.mem_of_subset_of_mem hJ' (a := (f, tensorHom <| ∑ i, g i otimesₜ h i))
  simp only [Prod.forall, Set.mem_ofPred_eq, forall_const] at hG
simpa using ⟨_, hG by simpa [tensorHom] using hgh⟩

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsUniformAddGroup, Set.mem_of_subset_of_mem, Set.nonempty_def, UniformSpace, exists_finite_sum_mul_approximation_of_mem_uniformity, hUo.mem_nhds, hasBasis_compactConvergenceUniformity_of_compact, isUniformAddGroup_of_addCommGroup, mem_closure_iff, mem_iff, mem_iff.mp, mem_nhds, mem_nhds_uniformity_iff_right, mem_nhds_uniformity_iff_right.mp, mem_of_subset_of_mem, nonempty_def, rightUniformSpace, simp_rw
-/
lemma denseRange_tensorHom [CompactSpace X] [T2Space X] [CompactSpace Y]
    [TotallyDisconnectedSpace X] : DenseRange (tensorHom : C(X, R) otimes[R] C(Y, R) -> C(X × Y, R)) := by
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  intro f
  simp_rw [mem_closure_iff, Set.nonempty_def]
  intro U hUo hUf
  have := mem_nhds_uniformity_iff_right.mp (hUo.mem_nhds hUf)
  obtain ⟨J, hJu, hJ'⟩ := (hasBasis_compactConvergenceUniformity_of_compact).mem_iff.mp this
  obtain ⟨n, g, h, hgh⟩ := exists_finite_sum_mul_approximation_of_mem_uniformity f hJu
  have hG := Set.mem_of_subset_of_mem hJ' (a := (f, tensorHom <| ∑ i, g i otimesₜ h i))
  simp only [Prod.forall, Set.mem_ofPred_eq, forall_const] at hG
simpa using ⟨_, hG by simpa [tensorHom] using hgh⟩

end prodMul

end ContinuousMap
