/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Cross products

This module defines the cross product of vectors in $R^3$ for $R$ a commutative ring,
as a bilinear map.

## Main definitions

* `crossProduct` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`
* `cross_dot_cross`
* `jacobi_cross`

## Notation

The scope `Matrix` gives the following notation:

* `⨯₃` for the cross product

## Tags

cross product
-/

@[expose] public section


open Matrix

variable {R : Type*} [CommRing R]

/--
Definition of `crossProduct` / `crossProduct` 的定义

English:
definition crossProduct
  signature: : (Fin 3 -> R) ->ₗ[R] (Fin 3 -> R) ->ₗ[R] Fin 3 -> R
  body: by
  apply LinearMap.mk₂ R fun a b : Fin 3 -> R =>
      ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, smul_mul_assoc]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, mul_smul_comm]

@[inherit_doc] scoped[Matrix] infixl:74 " ⨯₃ " => crossProduct

中文:
定义 crossProduct
  签名: : (有限集 3 -> R) ->ₗ[R] (有限集 3 -> R) ->ₗ[R] 有限集 3 -> R
  定义体: by
  apply LinearMap.mk₂ R fun a b : Fin 3 -> R =>
      ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, smul_mul_assoc]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, mul_smul_comm]

@[inherit_doc] scoped[Matrix] infixl:74 " ⨯₃ " => crossProduct

Depends on / 依赖: LinearMap, LinearMap.mk, Pi.add_apply, Pi.smul_apply, add_apply, intros, mul_smul_comm, simp_rw, smul_apply, smul_mul_assoc, smul_sub, smul_vec3, vec3_add, vec3_eq
-/
def crossProduct : (Fin 3 -> R) ->ₗ[R] (Fin 3 -> R) ->ₗ[R] Fin 3 -> R := by
  apply LinearMap.mk₂ R fun a b : Fin 3 -> R =>
      ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, smul_mul_assoc]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, mul_smul_comm]

@[inherit_doc] scoped[Matrix] infixl:74 " ⨯₃ " => crossProduct

/--
theorem `cross_apply` / 定理 `cross_apply`

English:
theorem cross_apply
  given: (a b : Fin 3 -> R)
  proof: rfl

中文:
定理 cross_apply
  条件: (a b : 有限集 3 -> R)
  证明: rfl
-/
theorem cross_apply (a b : Fin 3 -> R) :
    a ⨯₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := rfl

section ProductsProperties

@[simp]
/--
theorem `cross_anticomm` / 定理 `cross_anticomm`

English:
theorem cross_anticomm
  given: (v w : Fin 3 -> R)
  statement: -(v ⨯₃ w) = w ⨯₃ v
  proof: by
  simp [cross_apply, mul_comm]

alias neg_cross := cross_anticomm

@[simp]

中文:
定理 cross_anticomm
  条件: (v w : 有限集 3 -> R)
  结论: -(v ⨯₃ w) = w ⨯₃ v
  证明: by
  simp [cross_apply, mul_comm]

alias neg_cross := cross_anticomm

@[simp]

Depends on / 依赖: cross_apply, mul_comm
-/
theorem cross_anticomm (v w : Fin 3 -> R) : -(v ⨯₃ w) = w ⨯₃ v := by
  simp [cross_apply, mul_comm]

alias neg_cross := cross_anticomm

@[simp]
/--
theorem `cross_anticomm'` / 定理 `cross_anticomm'`

English:
theorem cross_anticomm'
  given: (v w : Fin 3 -> R)
  statement: v ⨯₃ w + w ⨯₃ v = 0
  proof: by
  rw [add_eq_zero_iff_eq_neg]; rw [cross_anticomm]

@[simp]

中文:
定理 cross_anticomm'
  条件: (v w : 有限集 3 -> R)
  结论: v ⨯₃ w + w ⨯₃ v = 0
  证明: by
  rw [add_eq_zero_iff_eq_neg]; rw [cross_anticomm]

@[simp]

Depends on / 依赖: add_eq_zero_iff_eq_neg, cross_anticomm
-/
theorem cross_anticomm' (v w : Fin 3 -> R) : v ⨯₃ w + w ⨯₃ v = 0 := by
  rw [add_eq_zero_iff_eq_neg]; rw [cross_anticomm]

@[simp]
/--
theorem `cross_self` / 定理 `cross_self`

English:
theorem cross_self
  given: (v : Fin 3 -> R)
  statement: v ⨯₃ v = 0
  proof: by
  simp [cross_apply, mul_comm]

中文:
定理 cross_self
  条件: (v : 有限集 3 -> R)
  结论: v ⨯₃ v = 0
  证明: by
  simp [cross_apply, mul_comm]

Depends on / 依赖: cross_apply, mul_comm
-/
theorem cross_self (v : Fin 3 -> R) : v ⨯₃ v = 0 := by
  simp [cross_apply, mul_comm]

/-- The cross product of two vectors is perpendicular to the first vector. -/
@[simp]
/--
theorem `dot_self_cross` / 定理 `dot_self_cross`

English:
theorem dot_self_cross
  given: (v w : Fin 3 -> R)
  statement: v ⬝ᵥ v ⨯₃ w = 0
  proof: by
  rw [cross_apply]; rw [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

中文:
定理 dot_self_cross
  条件: (v w : 有限集 3 -> R)
  结论: v ⬝ᵥ v ⨯₃ w = 0
  证明: by
  rw [cross_apply]; rw [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

Depends on / 依赖: Matrix, Matrix.cons_val, cons_val, cross_apply, vec3_dotProduct
-/
theorem dot_self_cross (v w : Fin 3 -> R) : v ⬝ᵥ v ⨯₃ w = 0 := by
  rw [cross_apply]; rw [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

/-- The cross product of two vectors is perpendicular to the second vector. -/
@[simp]
/--
theorem `dot_cross_self` / 定理 `dot_cross_self`

English:
theorem dot_cross_self
  given: (v w : Fin 3 -> R)
  statement: w ⬝ᵥ v ⨯₃ w = 0
  proof: by
  rw [← cross_anticomm]; rw [dotProduct_neg]; rw [dot_self_cross]; rw [neg_zero]

中文:
定理 dot_cross_self
  条件: (v w : 有限集 3 -> R)
  结论: w ⬝ᵥ v ⨯₃ w = 0
  证明: by
  rw [← cross_anticomm]; rw [dotProduct_neg]; rw [dot_self_cross]; rw [neg_zero]

Depends on / 依赖: cross_anticomm, dotProduct_neg, dot_self_cross, neg_zero
-/
theorem dot_cross_self (v w : Fin 3 -> R) : w ⬝ᵥ v ⨯₃ w = 0 := by
  rw [← cross_anticomm]; rw [dotProduct_neg]; rw [dot_self_cross]; rw [neg_zero]

/--
theorem `triple_product_permutation` / 定理 `triple_product_permutation`

English:
theorem triple_product_permutation
  given: (u v w : Fin 3 -> R)
  statement: u ⬝ᵥ v ⨯₃ w = v ⬝ᵥ w ⨯₃ u
  proof: by
  simp_rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

中文:
定理 triple_product_permutation
  条件: (u v w : 有限集 3 -> R)
  结论: u ⬝ᵥ v ⨯₃ w = v ⬝ᵥ w ⨯₃ u
  证明: by
  simp_rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

Depends on / 依赖: Matrix, Matrix.cons_val, cons_val, cross_apply, simp_rw, vec3_dotProduct
-/
theorem triple_product_permutation (u v w : Fin 3 -> R) : u ⬝ᵥ v ⨯₃ w = v ⬝ᵥ w ⨯₃ u := by
  simp_rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `triple_product_eq_det` / 定理 `triple_product_eq_det`

English:
theorem triple_product_eq_det
  given: (u v w : Fin 3 -> R)
  statement: u ⬝ᵥ v ⨯₃ w = Matrix.det ![u, v, w]
  proof: by
  rw [vec3_dotProduct]; rw [cross_apply]; rw [det_fin_three]
  dsimp only [Matrix.cons_val]
  ring

中文:
定理 triple_product_eq_det
  条件: (u v w : 有限集 3 -> R)
  结论: u ⬝ᵥ v ⨯₃ w = 矩阵.det ![u, v, w]
  证明: by
  rw [vec3_dotProduct]; rw [cross_apply]; rw [det_fin_three]
  dsimp only [Matrix.cons_val]
  ring

Depends on / 依赖: Matrix, Matrix.cons_val, cons_val, cross_apply, det_fin_three, vec3_dotProduct
-/
theorem triple_product_eq_det (u v w : Fin 3 -> R) : u ⬝ᵥ v ⨯₃ w = Matrix.det ![u, v, w] := by
  rw [vec3_dotProduct]; rw [cross_apply]; rw [det_fin_three]
  dsimp only [Matrix.cons_val]
  ring

/--
theorem `cross_dot_cross` / 定理 `cross_dot_cross`

English:
theorem cross_dot_cross
  given: (u v w x : Fin 3 -> R)
  proof: by
  simp_rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

中文:
定理 cross_dot_cross
  条件: (u v w x : 有限集 3 -> R)
  证明: by
  simp_rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

Depends on / 依赖: Matrix, Matrix.cons_val, cons_val, cross_apply, simp_rw, vec3_dotProduct
-/
theorem cross_dot_cross (u v w x : Fin 3 -> R) :
    u ⨯₃ v ⬝ᵥ w ⨯₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w := by
  simp_rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

end ProductsProperties

section LeibnizProperties

/--
theorem `leibniz_cross` / 定理 `leibniz_cross`

English:
theorem leibniz_cross
  given: (u v w : Fin 3 -> R)
  statement: u ⨯₃ (v ⨯₃ w) = u ⨯₃ v ⨯₃ w + v ⨯₃ (u ⨯₃ w)
  proof: by
  simp_rw [cross_apply, vec3_add]
  apply vec3_eq <;> dsimp <;> ring

中文:
定理 leibniz_cross
  条件: (u v w : 有限集 3 -> R)
  结论: u ⨯₃ (v ⨯₃ w) = u ⨯₃ v ⨯₃ w + v ⨯₃ (u ⨯₃ w)
  证明: by
  simp_rw [cross_apply, vec3_add]
  apply vec3_eq <;> dsimp <;> ring

Depends on / 依赖: cross_apply, simp_rw, vec3_add, vec3_eq
-/
theorem leibniz_cross (u v w : Fin 3 -> R) : u ⨯₃ (v ⨯₃ w) = u ⨯₃ v ⨯₃ w + v ⨯₃ (u ⨯₃ w) := by
  simp_rw [cross_apply, vec3_add]
  apply vec3_eq <;> dsimp <;> ring

/-- The three-dimensional vectors together with the operations + and ⨯₃ form a Lie ring.
Note we do not make this an instance as a conflicting one already exists
via `LieRing.ofAssociativeRing`. -/
@[instance_reducible]
/--
Definition of `Cross.lieRing` / `Cross.lieRing` 的定义

English:
definition Cross.lieRing
  signature: : LieRing (Fin 3 -> R)
  body: { Pi.addCommGroup with
    bracket := fun u v => u ⨯₃ v
    add_lie := LinearMap.map_add₂ _
    lie_add := fun _ => map_add _
    lie_self := cross_self
    leibniz_lie := leibniz_cross }

中文:
定义 Cross.lieRing
  签名: : Lie环 (有限集 3 -> R)
  定义体: { Pi.addCommGroup with
    bracket := fun u v => u ⨯₃ v
    add_lie := LinearMap.map_add₂ _
    lie_add := fun _ => map_add _
    lie_self := cross_self
    leibniz_lie := leibniz_cross }

Depends on / 依赖: LinearMap, LinearMap.map_add, Pi.addCommGroup, addCommGroup, add_lie, bracket, cross_self, leibniz_cross, leibniz_lie, lie_add, lie_self, map_add
-/
def Cross.lieRing : LieRing (Fin 3 -> R) :=
  { Pi.addCommGroup with
    bracket := fun u v => u ⨯₃ v
    add_lie := LinearMap.map_add₂ _
    lie_add := fun _ => map_add _
    lie_self := cross_self
    leibniz_lie := leibniz_cross }

attribute [local instance] Cross.lieRing

/--
theorem `cross_cross` / 定理 `cross_cross`

English:
theorem cross_cross
  given: (u v w : Fin 3 -> R)
  statement: u ⨯₃ v ⨯₃ w = u ⨯₃ (v ⨯₃ w) - v ⨯₃ (u ⨯₃ w)
  proof: lie_lie u v w

中文:
定理 cross_cross
  条件: (u v w : 有限集 3 -> R)
  结论: u ⨯₃ v ⨯₃ w = u ⨯₃ (v ⨯₃ w) - v ⨯₃ (u ⨯₃ w)
  证明: lie_lie u v w

Depends on / 依赖: lie_lie
-/
theorem cross_cross (u v w : Fin 3 -> R) : u ⨯₃ v ⨯₃ w = u ⨯₃ (v ⨯₃ w) - v ⨯₃ (u ⨯₃ w) :=
  lie_lie u v w

/--
theorem `jacobi_cross` / 定理 `jacobi_cross`

English:
theorem jacobi_cross
  given: (u v w : Fin 3 -> R)
  statement: u ⨯₃ (v ⨯₃ w) + v ⨯₃ (w ⨯₃ u) + w ⨯₃ (u ⨯₃ v) = 0
  proof: lie_jacobi u v w

中文:
定理 jacobi_cross
  条件: (u v w : 有限集 3 -> R)
  结论: u ⨯₃ (v ⨯₃ w) + v ⨯₃ (w ⨯₃ u) + w ⨯₃ (u ⨯₃ v) = 0
  证明: lie_jacobi u v w

Depends on / 依赖: lie_jacobi
-/
theorem jacobi_cross (u v w : Fin 3 -> R) : u ⨯₃ (v ⨯₃ w) + v ⨯₃ (w ⨯₃ u) + w ⨯₃ (u ⨯₃ v) = 0 :=
  lie_jacobi u v w

end LeibnizProperties

-- this can also be proved via `dotProduct_eq_zero_iff` and `triple_product_eq_det`, but
-- that would require much heavier imports.
/--
lemma `crossProduct_ne_zero_iff_linearIndependent` / 引理 `crossProduct_ne_zero_iff_linearIndependent`

English:
lemma crossProduct_ne_zero_iff_linearIndependent
  given: {F : Type*} [Field F] {v w : Fin 3 -> F}
  proof: by
  rw [not_iff_comm]
  by_cases hv : v = 0
  · rw [hv, map_zero, LinearMap.zero_apply, eq_self, iff_true]
    exact fun h => h.ne_zero 0 rfl
  constructor
  · rw [LinearIndependent.pair_iff' hv, not_forall_not]
    rintro ⟨a, rfl⟩
    rw [map_smul]; rw [cross_self]; rw [smul_zero]
  have hv' : v = ![v 0, v 1, v 2] := by simp [← List.ofFn_inj]
  have hw' : w = ![w 0, w 1, w 2] := by simp [← List.ofFn_inj]
  intro h1 h2
  simp_rw [cross_apply, cons_eq_zero_iff, zero_empty, and_true, sub_eq_zero] at h1
  have h20 := LinearIndependent.pair_iff.mp h2 (- w 0) (v 0)
  have h21 := LinearIndependent.pair_iff.mp h2 (- w 1) (v 1)
  have h22 := LinearIndependent.pair_iff.mp h2 (- w 2) (v 2)
  rw [neg_smul]; rw [neg_add_eq_zero]; rw [hv']; rw [hw']; rw [smul_vec3]; rw [smul_vec3]; rw [← hv']; rw [← hw'] at h20 h21 h22
  simp only [smul_eq_mul, mul_comm (w 0), mul_comm (w 1), mul_comm (w 2), h1] at h20 h21 h22
  rw [hv']; rw [cons_eq_zero_iff]; rw [cons_eq_zero_iff]; rw [cons_eq_zero_iff]; rw [zero_empty] at hv
  exact hv ⟨(h20 trivial).2, (h21 trivial).2, (h22 trivial).2, rfl⟩

中文:
引理 crossProduct_ne_zero_iff_linearIndependent
  条件: {F : 类型} [域 F] {v w : 有限集 3 -> F}
  证明: by
  rw [not_iff_comm]
  by_cases hv : v = 0
  · rw [hv, map_zero, LinearMap.zero_apply, eq_self, iff_true]
    exact fun h => h.ne_zero 0 rfl
  constructor
  · rw [LinearIndependent.pair_iff' hv, not_forall_not]
    rintro ⟨a, rfl⟩
    rw [map_smul]; rw [cross_self]; rw [smul_zero]
  have hv' : v = ![v 0, v 1, v 2] := by simp [← List.ofFn_inj]
  have hw' : w = ![w 0, w 1, w 2] := by simp [← List.ofFn_inj]
  intro h1 h2
  simp_rw [cross_apply, cons_eq_zero_iff, zero_empty, and_true, sub_eq_zero] at h1
  have h20 := LinearIndependent.pair_iff.mp h2 (- w 0) (v 0)
  have h21 := LinearIndependent.pair_iff.mp h2 (- w 1) (v 1)
  have h22 := LinearIndependent.pair_iff.mp h2 (- w 2) (v 2)
  rw [neg_smul]; rw [neg_add_eq_zero]; rw [hv']; rw [hw']; rw [smul_vec3]; rw [smul_vec3]; rw [← hv']; rw [← hw'] at h20 h21 h22
  simp only [smul_eq_mul, mul_comm (w 0), mul_comm (w 1), mul_comm (w 2), h1] at h20 h21 h22
  rw [hv']; rw [cons_eq_zero_iff]; rw [cons_eq_zero_iff]; rw [cons_eq_zero_iff]; rw [zero_empty] at hv
  exact hv ⟨(h20 trivial).2, (h21 trivial).2, (h22 trivial).2, rfl⟩

Depends on / 依赖: LinearIndep, LinearIndependent, LinearIndependent.pair_iff, LinearMap, LinearMap.zero_apply, List.ofFn_inj, and_true, cons_eq_zero_iff, cross_apply, cross_self, eq_self, h.ne_zero, iff_true, map_smul, map_zero, ne_zero, not_forall_not, not_iff_comm, ofFn_inj, pair_iff
-/
lemma crossProduct_ne_zero_iff_linearIndependent {F : Type*} [Field F] {v w : Fin 3 -> F} :
    crossProduct v w != 0 ↔ LinearIndependent F ![v, w] := by
  rw [not_iff_comm]
  by_cases hv : v = 0
  · rw [hv, map_zero, LinearMap.zero_apply, eq_self, iff_true]
    exact fun h => h.ne_zero 0 rfl
  constructor
  · rw [LinearIndependent.pair_iff' hv, not_forall_not]
    rintro ⟨a, rfl⟩
    rw [map_smul]; rw [cross_self]; rw [smul_zero]
  have hv' : v = ![v 0, v 1, v 2] := by simp [← List.ofFn_inj]
  have hw' : w = ![w 0, w 1, w 2] := by simp [← List.ofFn_inj]
  intro h1 h2
  simp_rw [cross_apply, cons_eq_zero_iff, zero_empty, and_true, sub_eq_zero] at h1
  have h20 := LinearIndependent.pair_iff.mp h2 (- w 0) (v 0)
  have h21 := LinearIndependent.pair_iff.mp h2 (- w 1) (v 1)
  have h22 := LinearIndependent.pair_iff.mp h2 (- w 2) (v 2)
  rw [neg_smul]; rw [neg_add_eq_zero]; rw [hv']; rw [hw']; rw [smul_vec3]; rw [smul_vec3]; rw [← hv']; rw [← hw'] at h20 h21 h22
  simp only [smul_eq_mul, mul_comm (w 0), mul_comm (w 1), mul_comm (w 2), h1] at h20 h21 h22
  rw [hv']; rw [cons_eq_zero_iff]; rw [cons_eq_zero_iff]; rw [cons_eq_zero_iff]; rw [zero_empty] at hv
  exact hv ⟨(h20 trivial).2, (h21 trivial).2, (h22 trivial).2, rfl⟩

/--
theorem `cross_cross_eq_smul_sub_smul` / 定理 `cross_cross_eq_smul_sub_smul`

English:
theorem cross_cross_eq_smul_sub_smul
  given: (u v w : Fin 3 -> R)
  proof: by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
  · simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, cons_val,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

中文:
定理 cross_cross_eq_smul_sub_smul
  条件: (u v w : 有限集 3 -> R)
  证明: by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
  · simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, cons_val,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

Depends on / 依赖: Fin.isValue, Fin.reduceFinMk, Nat.reduceAdd, Nat.succ_eq_add_one, Pi.smul_apply, Pi.sub_apply, cons_val, cross_apply, fin_cases, isValue, reduceAdd, reduceFinMk, simp_rw, smul_apply, smul_eq_mul, sub_apply, succ_eq_add_one, vec3_dotProduct
-/
theorem cross_cross_eq_smul_sub_smul (u v w : Fin 3 -> R) :
    u ⨯₃ v ⨯₃ w = (u ⬝ᵥ w) • v - (v ⬝ᵥ w) • u := by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
  · simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, cons_val,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/--
theorem `cross_cross_eq_smul_sub_smul'` / 定理 `cross_cross_eq_smul_sub_smul'`

English:
theorem cross_cross_eq_smul_sub_smul'
  given: (u v w : Fin 3 -> R)
  proof: by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val, cons_val_one,
      cons_val_zero, Fin.reduceFinMk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

中文:
定理 cross_cross_eq_smul_sub_smul'
  条件: (u v w : 有限集 3 -> R)
  证明: by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val, cons_val_one,
      cons_val_zero, Fin.reduceFinMk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

Depends on / 依赖: Fin.isValue, Fin.reduceFinMk, Nat.reduceAdd, Nat.succ_eq_add_one, Pi.smul_apply, Pi.sub_apply, cons_val, cons_val_one, cons_val_zero, cross_apply, fin_cases, isValue, reduceAdd, reduceFinMk, simp_rw, smul_apply, smul_eq_mul, sub_apply, succ_eq_add_one, vec3_dotProduct
-/
theorem cross_cross_eq_smul_sub_smul' (u v w : Fin 3 -> R) :
    u ⨯₃ (v ⨯₃ w) = (u ⬝ᵥ w) • v - (v ⬝ᵥ u) • w := by
  simp_rw [cross_apply, vec3_dotProduct]
  ext i
  fin_cases i <;>
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val, cons_val_one,
      cons_val_zero, Fin.reduceFinMk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
