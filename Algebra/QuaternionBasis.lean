/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Quaternion
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Basis on a quaternion-like algebra

## Main definitions

* `QuaternionAlgebra.Basis A c₁ c₂ c₃`: a basis for a subspace of an `R`-algebra `A` that has the
  same algebra structure as `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.self R`: the canonical basis for `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.Basis.compHom b f`: transform a basis `b` by an AlgHom `f`.
* `QuaternionAlgebra.lift`: Define an `AlgHom` out of `ℍ[R,c₁,c₂,c₃]` by its action on the basis
  elements `i`, `j`, and `k`. In essence, this is a universal property. Analogous to `Complex.lift`,
  but takes a bundled `QuaternionAlgebra.Basis` instead of just a `Subtype` as the amount of
  data / proofs is non-negligible.
-/

@[expose] public section


open Quaternion

namespace QuaternionAlgebra

/--
Definition of `Basis` / `Basis` 的定义

English:
structure Basis
  parameters: {R : Type*} (A : Type*) [CommRing R] [Ring A] [Algebra R A] (c₁ c₂ c₃ : R)
  axioms and operations (7):
    - i : A
    - j : A
    - k : A
    - i_mul_i : i * i = c₁ • (1 : A) + c₂ • i
    - j_mul_j : j * j = c₃ • (1 : A)
    - i_mul_j : i * j = k
    - j_mul_i : j * i = c₂ • j - k

中文:
结构 基
  参数: {R : 类型} (A : 类型) [交换环 R] [环 A] [代数 R A] (c₁ c₂ c₃ : R)
  公理与运算 (7 个):
    - i : A
    - j : A
    - k : A
    - i_mul_i : i * i = c₁ • (1 : A) + c₂ • i
    - j_mul_j : j * j = c₃ • (1 : A)
    - i_mul_j : i * j = k
    - j_mul_i : j * i = c₂ • j - k
-/
structure Basis {R : Type*} (A : Type*) [CommRing R] [Ring A] [Algebra R A] (c₁ c₂ c₃ : R) where
  /-- The first imaginary unit -/
  i : A
  /-- The second imaginary unit -/
  j : A
  /-- The third imaginary unit -/
  k : A
  i_mul_i : i * i = c₁ • (1 : A) + c₂ • i
  j_mul_j : j * j = c₃ • (1 : A)
  i_mul_j : i * j = k
  j_mul_i : j * i = c₂ • j - k

initialize_simps_projections Basis
  (as_prefix i, as_prefix j, as_prefix k)

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable {c₁ c₂ c₃ : R}

namespace Basis

/-- Since `k` is redundant, it is not necessary to show `q₁.k = q₂.k` when showing `q₁ = q₂`. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃q₁ q₂
  statement: Basis A c₁ c₂ c₃⦄ (hi : q₁.i = q₂.i)
  proof: by
  cases q₁; cases q₂; grind

中文:
定理 ext
  条件: ⦃q₁ q₂
  结论: 基 A c₁ c₂ c₃⦄ (hi : q₁.i = q₂.i)
  证明: by
  cases q₁; cases q₂; grind
-/
protected theorem ext ⦃q₁ q₂ : Basis A c₁ c₂ c₃⦄ (hi : q₁.i = q₂.i)
    (hj : q₁.j = q₂.j) : q₁ = q₂ := by
  cases q₁; cases q₂; grind

variable (R) in
/-- There is a natural quaternionic basis for the `QuaternionAlgebra`. -/
@[simps i j k]
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: : Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃ where
  body: ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

中文:
定义 self
  签名: : 基 ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃ where
  定义体: ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp
-/
protected def self : Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃ where
  i := ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃)
  body: ⟨Basis.self R⟩

中文:
实例 :
  签名: 可居 (基 ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃)
  定义体: ⟨Basis.self R⟩

Depends on / 依赖: Basis.self
-/
instance : Inhabited (Basis ℍ[R,c₁,c₂,c₃] c₁ c₂ c₃) :=
  ⟨Basis.self R⟩

variable (q : Basis A c₁ c₂ c₃)

attribute [simp] i_mul_i j_mul_j i_mul_j j_mul_i

@[simp]
/--
theorem `i_mul_k` / 定理 `i_mul_k`

English:
theorem i_mul_k
  statement: q.i * q.k = c₁ • q.j + c₂ • q.k
  proof: by
  rw [← i_mul_j]; rw [← mul_assoc]; rw [i_mul_i]; rw [add_mul]; rw [smul_mul_assoc]; rw [one_mul]; rw [smul_mul_assoc]

@[simp]

中文:
定理 i_mul_k
  结论: q.i * q.k = c₁ • q.j + c₂ • q.k
  证明: by
  rw [← i_mul_j]; rw [← mul_assoc]; rw [i_mul_i]; rw [add_mul]; rw [smul_mul_assoc]; rw [one_mul]; rw [smul_mul_assoc]

@[simp]

Depends on / 依赖: add_mul, i_mul_i, i_mul_j, mul_assoc, one_mul, smul_mul_assoc
-/
theorem i_mul_k : q.i * q.k = c₁ • q.j + c₂ • q.k := by
  rw [← i_mul_j]; rw [← mul_assoc]; rw [i_mul_i]; rw [add_mul]; rw [smul_mul_assoc]; rw [one_mul]; rw [smul_mul_assoc]

@[simp]
/--
theorem `k_mul_i` / 定理 `k_mul_i`

English:
theorem k_mul_i
  statement: q.k * q.i = -c₁ • q.j
  proof: by
  rw [← i_mul_j]; rw [mul_assoc]; rw [j_mul_i]; rw [mul_sub]; rw [i_mul_k]; rw [neg_smul]; rw [mul_smul_comm]; rw [i_mul_j]
  linear_combination (norm := module)

@[simp]

中文:
定理 k_mul_i
  结论: q.k * q.i = -c₁ • q.j
  证明: by
  rw [← i_mul_j]; rw [mul_assoc]; rw [j_mul_i]; rw [mul_sub]; rw [i_mul_k]; rw [neg_smul]; rw [mul_smul_comm]; rw [i_mul_j]
  linear_combination (norm := module)

@[simp]

Depends on / 依赖: i_mul_j, i_mul_k, j_mul_i, linear_combination, module, mul_assoc, mul_smul_comm, mul_sub, neg_smul
-/
theorem k_mul_i : q.k * q.i = -c₁ • q.j := by
  rw [← i_mul_j]; rw [mul_assoc]; rw [j_mul_i]; rw [mul_sub]; rw [i_mul_k]; rw [neg_smul]; rw [mul_smul_comm]; rw [i_mul_j]
  linear_combination (norm := module)

@[simp]
/--
theorem `k_mul_j` / 定理 `k_mul_j`

English:
theorem k_mul_j
  statement: q.k * q.j = c₃ • q.i
  proof: by
  rw [← i_mul_j]; rw [mul_assoc]; rw [j_mul_j]; rw [mul_smul_comm]; rw [mul_one]

@[simp]

中文:
定理 k_mul_j
  结论: q.k * q.j = c₃ • q.i
  证明: by
  rw [← i_mul_j]; rw [mul_assoc]; rw [j_mul_j]; rw [mul_smul_comm]; rw [mul_one]

@[simp]

Depends on / 依赖: i_mul_j, j_mul_j, mul_assoc, mul_one, mul_smul_comm
-/
theorem k_mul_j : q.k * q.j = c₃ • q.i := by
  rw [← i_mul_j]; rw [mul_assoc]; rw [j_mul_j]; rw [mul_smul_comm]; rw [mul_one]

@[simp]
/--
theorem `j_mul_k` / 定理 `j_mul_k`

English:
theorem j_mul_k
  statement: q.j * q.k = (c₂ * c₃) • 1 - c₃ • q.i
  proof: by
  rw [← i_mul_j]; rw [← mul_assoc]; rw [j_mul_i]; rw [sub_mul]; rw [smul_mul_assoc]; rw [j_mul_j]; rw [← smul_assoc]; rw [k_mul_j]
  rfl

@[simp]

中文:
定理 j_mul_k
  结论: q.j * q.k = (c₂ * c₃) • 1 - c₃ • q.i
  证明: by
  rw [← i_mul_j]; rw [← mul_assoc]; rw [j_mul_i]; rw [sub_mul]; rw [smul_mul_assoc]; rw [j_mul_j]; rw [← smul_assoc]; rw [k_mul_j]
  rfl

@[simp]

Depends on / 依赖: i_mul_j, j_mul_i, j_mul_j, k_mul_j, mul_assoc, smul_assoc, smul_mul_assoc, sub_mul
-/
theorem j_mul_k : q.j * q.k = (c₂ * c₃) • 1 - c₃ • q.i := by
  rw [← i_mul_j]; rw [← mul_assoc]; rw [j_mul_i]; rw [sub_mul]; rw [smul_mul_assoc]; rw [j_mul_j]; rw [← smul_assoc]; rw [k_mul_j]
  rfl

@[simp]
/--
theorem `k_mul_k` / 定理 `k_mul_k`

English:
theorem k_mul_k
  statement: q.k * q.k = -((c₁ * c₃) • (1 : A))
  proof: by
  rw [← i_mul_j]; rw [mul_assoc]; rw [← mul_assoc q.j _ _]; rw [j_mul_i]; rw [← i_mul_j]; rw [← mul_assoc]; rw [mul_sub]; rw [←
    mul_assoc]; rw [i_mul_i]; rw [add_mul]; rw [smul_mul_assoc]; rw [one_mul]; rw [sub_mul]; rw [smul_mul_assoc]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [mul_assoc]

中文:
定理 k_mul_k
  结论: q.k * q.k = -((c₁ * c₃) • (1 : A))
  证明: by
  rw [← i_mul_j]; rw [mul_assoc]; rw [← mul_assoc q.j _ _]; rw [j_mul_i]; rw [← i_mul_j]; rw [← mul_assoc]; rw [mul_sub]; rw [←
    mul_assoc]; rw [i_mul_i]; rw [add_mul]; rw [smul_mul_assoc]; rw [one_mul]; rw [sub_mul]; rw [smul_mul_assoc]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [mul_assoc]

Depends on / 依赖: add_mul, i_mul_i, i_mul_j, j_mul_i, j_mul_j, linear_combination, module, mul_assoc, mul_smul_comm, mul_sub, one_mul, smul_mul_assoc, smul_smul, sub_mul
-/
theorem k_mul_k : q.k * q.k = -((c₁ * c₃) • (1 : A)) := by
  rw [← i_mul_j]; rw [mul_assoc]; rw [← mul_assoc q.j _ _]; rw [j_mul_i]; rw [← i_mul_j]; rw [← mul_assoc]; rw [mul_sub]; rw [←
    mul_assoc]; rw [i_mul_i]; rw [add_mul]; rw [smul_mul_assoc]; rw [one_mul]; rw [sub_mul]; rw [smul_mul_assoc]; rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [mul_assoc]; rw [j_mul_j]; rw [add_mul]; rw [smul_mul_assoc]; rw [j_mul_j]; rw [smul_smul]; rw [smul_mul_assoc]; rw [mul_assoc]; rw [j_mul_j]
  linear_combination (norm := module)


/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (x : ℍ[R,c₁,c₂,c₃])
  body: algebraMap R _ x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k

中文:
定义 lift
  签名: (x : ℍ[R,c₁,c₂,c₃])
  定义体: algebraMap R _ x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k

Depends on / 依赖: algebraMap, x.imI, x.imJ, x.imK, x.re
-/
def lift (x : ℍ[R,c₁,c₂,c₃]) : A :=
  algebraMap R _ x.re + x.imI • q.i + x.imJ • q.j + x.imK • q.k

/--
theorem `lift_zero` / 定理 `lift_zero`

English:
theorem lift_zero
  statement: q.lift (0 : ℍ[R,c₁,c₂,c₃]) = 0
  proof: by simp [lift]

中文:
定理 lift_zero
  结论: q.lift (0 : ℍ[R,c₁,c₂,c₃]) = 0
  证明: by simp [lift]
-/
theorem lift_zero : q.lift (0 : ℍ[R,c₁,c₂,c₃]) = 0 := by simp [lift]

/--
theorem `lift_one` / 定理 `lift_one`

English:
theorem lift_one
  statement: q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1
  proof: by simp [lift]

中文:
定理 lift_one
  结论: q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1
  证明: by simp [lift]
-/
theorem lift_one : q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1 := by simp [lift]

/--
theorem `lift_add` / 定理 `lift_add`

English:
theorem lift_add
  given: (x y : ℍ[R,c₁,c₂,c₃])
  statement: q.lift (x + y) = q.lift x + q.lift y
  proof: by
  simp only [lift, re_add, map_add, imI_add, add_smul, imJ_add, imK_add]
  abel

中文:
定理 lift_add
  条件: (x y : ℍ[R,c₁,c₂,c₃])
  结论: q.lift (x + y) = q.lift x + q.lift y
  证明: by
  simp only [lift, re_add, map_add, imI_add, add_smul, imJ_add, imK_add]
  abel

Depends on / 依赖: add_smul, imI_add, imJ_add, imK_add, map_add, re_add
-/
theorem lift_add (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x + y) = q.lift x + q.lift y := by
  simp only [lift, re_add, map_add, imI_add, add_smul, imJ_add, imK_add]
  abel

/--
theorem `lift_mul` / 定理 `lift_mul`

English:
theorem lift_mul
  given: (x y : ℍ[R,c₁,c₂,c₃])
  statement: q.lift (x * y) = q.lift x * q.lift y
  proof: by
  simp only [lift, Algebra.algebraMap_eq_smul_one]
  simp_rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k]
  simp only [smul_smul, smul_neg, sub_eq_add_neg, ← add_assoc, 

中文:
定理 lift_mul
  条件: (x y : ℍ[R,c₁,c₂,c₃])
  结论: q.lift (x * y) = q.lift x * q.lift y
  证明: by
  simp only [lift, Algebra.algebraMap_eq_smul_one]
  simp_rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k]
  simp only [smul_smul, smul_neg, sub_eq_add_neg, ← add_assoc, 

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, add_assoc, add_mul, add_smul, algebraMap_eq_smul_one, i_mul_i, i_mul_j, i_mul_k, j_mul_i, j_mul_j, j_mul_k, k_mul_i, k_mul_j, k_mul_k, mul_add, mul_assoc, mul_comm, mul_one, mul_right_comm
-/
theorem lift_mul (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x * y) = q.lift x * q.lift y := by
  simp only [lift, Algebra.algebraMap_eq_smul_one]
  simp_rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, i_mul_k, k_mul_i, k_mul_j, j_mul_k, k_mul_k]
  simp only [smul_smul, smul_neg, sub_eq_add_neg, ← add_assoc, neg_smul]
  simp only [mul_right_comm _ _ (c₁ * c₃), mul_comm _ (c₁ * c₃)]
  simp only [mul_comm _ c₁]
  simp only [mul_right_comm _ _ c₃]
  simp only [← mul_assoc]
  simp only [re_mul, sub_eq_add_neg, add_smul, neg_smul, imI_mul, ← add_assoc, imJ_mul, imK_mul]
  linear_combination (norm := module)

/--
theorem `lift_smul` / 定理 `lift_smul`

English:
theorem lift_smul
  given: (r : R) (x : ℍ[R,c₁,c₂,c₃])
  statement: q.lift (r • x) = r • q.lift x
  proof: by
  simp [lift, mul_smul, ← Algebra.smul_def]

中文:
定理 lift_smul
  条件: (r : R) (x : ℍ[R,c₁,c₂,c₃])
  结论: q.lift (r • x) = r • q.lift x
  证明: by
  simp [lift, mul_smul, ← Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, mul_smul, smul_def
-/
theorem lift_smul (r : R) (x : ℍ[R,c₁,c₂,c₃]) : q.lift (r • x) = r • q.lift x := by
  simp [lift, mul_smul, ← Algebra.smul_def]

/-- A `QuaternionAlgebra.Basis` implies an `AlgHom` from the quaternions. -/
@[simps!]
/--
Definition of `liftHom` / `liftHom` 的定义

English:
definition liftHom
  signature: : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A
  body: AlgHom.mk'
    { toFun := q.lift
      map_zero' := q.lift_zero
      map_one' := q.lift_one
      map_add' := q.lift_add
      map_mul' := q.lift_mul } q.lift_smul

@[simp]

中文:
定义 liftHom
  签名: : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A
  定义体: AlgHom.mk'
    { toFun := q.lift
      map_zero' := q.lift_zero
      map_one' := q.lift_one
      map_add' := q.lift_add
      map_mul' := q.lift_mul } q.lift_smul

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mk, lift_add, lift_mul, lift_one, lift_smul, lift_zero, map_add, map_mul, map_one, map_zero, q.lift, q.lift_add, q.lift_mul, q.lift_one, q.lift_smul, q.lift_zero
-/
def liftHom : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A :=
  AlgHom.mk'
    { toFun := q.lift
      map_zero' := q.lift_zero
      map_one' := q.lift_one
      map_add' := q.lift_add
      map_mul' := q.lift_mul } q.lift_smul

@[simp]
/--
theorem `range_liftHom` / 定理 `range_liftHom`

English:
theorem range_liftHom
  given: (B : Basis A c₁ c₂ c₃)
  proof: by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact algebraMap_mem _ _
    all_goals
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin <| by simp) _
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | rfl | rfl)
      <;> [use (Basis.self

中文:
定理 range_liftHom
  条件: (B : 基 A c₁ c₂ c₃)
  证明: by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact algebraMap_mem _ _
    all_goals
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin <| by simp) _
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | rfl | rfl)
      <;> [use (Basis.self

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, Algebra.subset_adjoin, Basis.self, Subalgebra, Subalgebra.smul_mem, add_mem, adjoin_le_iff, algebraMap_mem, all_goals, le_antisymm, smul_mem, subset_adjoin
-/
theorem range_liftHom (B : Basis A c₁ c₂ c₃) :
    (liftHom B).range = Algebra.adjoin R {B.i, B.j, B.k} := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact algebraMap_mem _ _
    all_goals
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin <| by simp) _
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | rfl | rfl)
      <;> [use (Basis.self R).i; use (Basis.self R).j; use (Basis.self R).k]
    all_goals simp [lift]

/-- Transform a `QuaternionAlgebra.Basis` through an `AlgHom`. -/
@[simps i j k]
/--
Definition of `compHom` / `compHom` 的定义

English:
definition compHom
  signature: (F : A ->ₐ[R] B)
  body: F q.i
  i_mul_i := by rw [← map_mul, q.i_mul_i, map_add, map_smul, map_smul, map_one]
  j := F q.j
  j_mul_j := by rw [← map_mul, q.j_mul_j, map_smul, map_one]
  k := F q.k
  i_mul_j := by rw [← map_mul, q.i_mul_j]
  j_mul_i := by rw [← map_mul, q.j_mul_i, map_sub, map_smul]

中文:
定义 compHom
  签名: (F : A ->ₐ[R] B)
  定义体: F q.i
  i_mul_i := by rw [← map_mul, q.i_mul_i, map_add, map_smul, map_smul, map_one]
  j := F q.j
  j_mul_j := by rw [← map_mul, q.j_mul_j, map_smul, map_one]
  k := F q.k
  i_mul_j := by rw [← map_mul, q.i_mul_j]
  j_mul_i := by rw [← map_mul, q.j_mul_i, map_sub, map_smul]
-/
def compHom (F : A ->ₐ[R] B) : Basis B c₁ c₂ c₃ where
  i := F q.i
  i_mul_i := by rw [← map_mul, q.i_mul_i, map_add, map_smul, map_smul, map_one]
  j := F q.j
  j_mul_j := by rw [← map_mul, q.j_mul_j, map_smul, map_one]
  k := F q.k
  i_mul_j := by rw [← map_mul, q.i_mul_j]
  j_mul_i := by rw [← map_mul, q.j_mul_i, map_sub, map_smul]

end Basis

set_option backward.defeqAttrib.useBackward true in
/-- A quaternionic basis on `A` is equivalent to a map from the quaternion algebra to `A`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : Basis A c₁ c₂ c₃ ≃ (ℍ[R,c₁,c₂,c₃] ->ₐ[R] A) where
  body: Basis.liftHom
  invFun := (Basis.self R).compHom
  left_inv q := by ext <;> simp [Basis.lift]
  right_inv F := by
    ext
    dsimp [Basis.lift]
    rw [← F.commutes]
    simp only [← map_smul, ← map_add, mk_add_mk, smul_mk, smul_zero, algebraMap_eq]
    congr <;> simp

中文:
定义 lift
  签名: : 基 A c₁ c₂ c₃ ≃ (ℍ[R,c₁,c₂,c₃] ->ₐ[R] A) where
  定义体: Basis.liftHom
  invFun := (Basis.self R).compHom
  left_inv q := by ext <;> simp [Basis.lift]
  right_inv F := by
    ext
    dsimp [Basis.lift]
    rw [← F.commutes]
    simp only [← map_smul, ← map_add, mk_add_mk, smul_mk, smul_zero, algebraMap_eq]
    congr <;> simp

Depends on / 依赖: Basis.liftHom, liftHom
-/
def lift : Basis A c₁ c₂ c₃ ≃ (ℍ[R,c₁,c₂,c₃] ->ₐ[R] A) where
  toFun := Basis.liftHom
  invFun := (Basis.self R).compHom
  left_inv q := by ext <;> simp [Basis.lift]
  right_inv F := by
    ext
    dsimp [Basis.lift]
    rw [← F.commutes]
    simp only [← map_smul, ← map_add, mk_add_mk, smul_mk, smul_zero, algebraMap_eq]
    congr <;> simp

/-- Two `R`-algebra morphisms from a quaternion algebra are equal if they agree on `i` and `j`. -/
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: ⦃f g
  statement: ℍ[R,c₁,c₂,c₃] ->ₐ[R] A⦄
  proof: lift.symm.injective Basis.ext hi hj

中文:
定理 hom_ext
  条件: ⦃f g
  结论: ℍ[R,c₁,c₂,c₃] ->ₐ[R] A⦄
  证明: lift.symm.injective Basis.ext hi hj

Depends on / 依赖: Basis.ext, injective, lift.symm.injective
-/
theorem hom_ext ⦃f g : ℍ[R,c₁,c₂,c₃] ->ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g :=
lift.symm.injective Basis.ext hi hj

end QuaternionAlgebra

namespace Quaternion
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

open QuaternionAlgebra (Basis)

/-- Two `R`-algebra morphisms from the quaternions are equal if they agree on `i` and `j`. -/
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: ⦃f g
  statement: ℍ[R] ->ₐ[R] A⦄
  proof: QuaternionAlgebra.hom_ext hi hj

中文:
定理 hom_ext
  条件: ⦃f g
  结论: ℍ[R] ->ₐ[R] A⦄
  证明: QuaternionAlgebra.hom_ext hi hj

Depends on / 依赖: QuaternionAlgebra, QuaternionAlgebra.hom_ext, hom_ext
-/
theorem hom_ext ⦃f g : ℍ[R] ->ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g :=
  QuaternionAlgebra.hom_ext hi hj

end Quaternion
