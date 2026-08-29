/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Rays in modules

This file defines rays in modules.

## Main definitions

* `SameRay`: two vectors belong to the same ray if they are proportional with a nonnegative
  coefficient.

* `Module.Ray` is a type for the equivalence class of nonzero vectors in a module with some
  common positive multiple.
-/

@[expose] public noncomputable section

open Module

section StrictOrderedCommSemiring

-- TODO: remove `[IsStrictOrderedRing R]` and `@[nolint unusedArguments]`.
/-- Two vectors are in the same ray if either one of them is zero or some positive multiples of them
are equal (in the typical case over a field, this means one of them is a nonnegative multiple of
the other). -/
@[nolint unusedArguments]
/--
Definition of `SameRay` / `SameRay` 的定义

English:
definition SameRay
  signature: (R : Type*) [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: v₁ = 0 ∨ v₂ = 0 ∨ exists r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂

中文:
定义 SameRay
  签名: (R : 类型) [交换半环 R] [偏序 R] [是StrictOrdered环 R]
  定义体: v₁ = 0 ∨ v₂ = 0 ∨ exists r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂
-/
def SameRay (R : Type*) [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    {M : Type*} [AddCommMonoid M] [Module R M] (v₁ v₂ : M) : Prop :=
  v₁ = 0 ∨ v₂ = 0 ∨ exists r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂

set_option linter.unusedVariables false in
/-- Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that
`RayVector.Setoid` can be an instance. -/
@[nolint unusedArguments]
/--
Definition of `RayVector` / `RayVector` 的定义

English:
definition RayVector
  signature: (R M : Type*) [Zero M]
  body: { v : M // v != 0 }

中文:
定义 RayVector
  签名: (R M : 类型) [零 M]
  定义体: { v : M // v != 0 }
-/
def RayVector (R M : Type*) [Zero M] :=
  { v : M // v != 0 }

/--
Definition of `RayVector.equiv` / `RayVector.equiv` 的定义

English:
definition RayVector.equiv
  signature: (R M : Type*) [Zero M]
  body: Equiv.refl _

中文:
定义 RayVector.equiv
  签名: (R M : 类型) [零 M]
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def RayVector.equiv (R M : Type*) [Zero M] : RayVector R M ≃ { v : M // v != 0 } :=
  Equiv.refl _

/--
Instance `RayVector.coe` / 实例 `RayVector.coe`

English:
instance RayVector.coe
  signature: {R M : Type*} [Zero M]
  body: (equiv R M x).val

@[simp]

中文:
实例 RayVector.coe
  签名: {R M : 类型} [零 M]
  定义体: (equiv R M x).val

@[simp]
-/
instance RayVector.coe {R M : Type*} [Zero M] : CoeOut (RayVector R M) M where
  coe x := (equiv R M x).val

@[simp]
/--
theorem `RayVector.coe_equiv_symm` / 定理 `RayVector.coe_equiv_symm`

English:
theorem RayVector.coe_equiv_symm
  given: {R M : Type*} [Zero M] {v : M} (h : v != 0)
  proof: rfl

@[ext]

中文:
定理 RayVector.coe_equiv_symm
  条件: {R M : 类型} [零 M] {v : M} (h : v != 0)
  证明: rfl

@[ext]
-/
theorem RayVector.coe_equiv_symm {R M : Type*} [Zero M] {v : M} (h : v != 0) :
    (RayVector.equiv R M).symm ⟨v, h⟩ = v := rfl

@[ext]
/--
theorem `RayVector.ext` / 定理 `RayVector.ext`

English:
theorem RayVector.ext
  given: {R M : Type*} [Zero M] {x y : RayVector R M} (h : (x : M) = (y : M))
  proof: Subtype.ext h

中文:
定理 RayVector.ext
  条件: {R M : 类型} [零 M] {x y : RayVector R M} (h : (x : M) = (y : M))
  证明: Subtype.ext h

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem RayVector.ext {R M : Type*} [Zero M] {x y : RayVector R M} (h : (x : M) = (y : M)) :
    x = y := Subtype.ext h

instance {R M : Type*} [Zero M] [Nontrivial M] : Nonempty (RayVector R M) :=
⟨Classical.indefiniteDescription _ exists_ne (0 : M)⟩

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (ι : Type*) [DecidableEq ι]

namespace SameRay

variable {x y z : M}

@[simp]
/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: (y : M)
  statement: SameRay R 0 y
  proof: Or.inl rfl

@[simp]

中文:
定理 zero_left
  条件: (y : M)
  结论: SameRay R 0 y
  证明: Or.inl rfl

@[simp]

Depends on / 依赖: Or.inl
-/
theorem zero_left (y : M) : SameRay R 0 y :=
  Or.inl rfl

@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: (x : M)
  statement: SameRay R x 0
  proof: Or.inr Or.inl rfl

@[nontriviality]

中文:
定理 zero_right
  条件: (x : M)
  结论: SameRay R x 0
  证明: Or.inr Or.inl rfl

@[nontriviality]

Depends on / 依赖: Or.inl, Or.inr
-/
theorem zero_right (x : M) : SameRay R x 0 :=
Or.inr Or.inl rfl

@[nontriviality]
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: [Subsingleton M] (x y : M)
  statement: SameRay R x y
  proof: by
  rw [Subsingleton.elim x 0]
  exact zero_left _

@[nontriviality]

中文:
定理 of_subsingleton
  条件: [子单例 M] (x y : M)
  结论: SameRay R x y
  证明: by
  rw [Subsingleton.elim x 0]
  exact zero_left _

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim, zero_left
-/
theorem of_subsingleton [Subsingleton M] (x y : M) : SameRay R x y := by
  rw [Subsingleton.elim x 0]
  exact zero_left _

@[nontriviality]
/--
theorem `of_subsingleton'` / 定理 `of_subsingleton'`

English:
theorem of_subsingleton'
  given: [Subsingleton R] (x y : M)
  statement: SameRay R x y
  proof: haveI := Module.subsingleton R M
  of_subsingleton x y

中文:
定理 of_subsingleton'
  条件: [子单例 R] (x y : M)
  结论: SameRay R x y
  证明: haveI := Module.subsingleton R M
  of_subsingleton x y

Depends on / 依赖: Module, Module.subsingleton, of_subsingleton, subsingleton
-/
theorem of_subsingleton' [Subsingleton R] (x y : M) : SameRay R x y :=
  haveI := Module.subsingleton R M
  of_subsingleton x y

/-- `SameRay` is reflexive. -/
@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (x : M)
  statement: SameRay R x x
  proof: Or.inr (Or.inr <| ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)

中文:
定理 refl
  条件: (x : M)
  结论: SameRay R x x
  证明: Or.inr (Or.inr <| ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)

Depends on / 依赖: Or.inr, zero_lt_one
-/
theorem refl (x : M) : SameRay R x x :=
  Or.inr (Or.inr <| ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  statement: SameRay R x x
  proof: refl _

中文:
定理 rfl
  结论: SameRay R x x
  证明: refl _
-/
protected theorem rfl : SameRay R x x :=
  refl _

/-- `SameRay` is symmetric. -/
@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : SameRay R x y)
  statement: SameRay R y x
  proof: (or_left_comm.1 h).imp_right Or.imp_right fun ⟨r₁, r₂, h₁, h₂, h⟩ => ⟨r₂, r₁, h₂, h₁, h.symm⟩

中文:
定理 symm
  条件: (h : SameRay R x y)
  结论: SameRay R y x
  证明: (or_left_comm.1 h).imp_right Or.imp_right fun ⟨r₁, r₂, h₁, h₂, h⟩ => ⟨r₂, r₁, h₂, h₁, h.symm⟩

Depends on / 依赖: Or.imp_right, h.symm, imp_right, or_left_comm
-/
theorem symm (h : SameRay R x y) : SameRay R y x :=
(or_left_comm.1 h).imp_right Or.imp_right fun ⟨r₁, r₂, h₁, h₂, h⟩ => ⟨r₂, r₁, h₂, h₁, h.symm⟩

/--
theorem `exists_pos` / 定理 `exists_pos`

English:
theorem exists_pos
  given: (h : SameRay R x y) (hx : x != 0) (hy : y != 0)
  proof: (h.resolve_left hx).resolve_left hy

中文:
定理 存在_pos
  条件: (h : SameRay R x y) (hx : x != 0) (hy : y != 0)
  证明: (h.resolve_left hx).resolve_left hy

Depends on / 依赖: h.resolve_left, resolve_left
-/
theorem exists_pos (h : SameRay R x y) (hx : x != 0) (hy : y != 0) :
    exists r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y :=
  (h.resolve_left hx).resolve_left hy

/--
theorem `sameRay_comm` / 定理 `sameRay_comm`

English:
theorem sameRay_comm
  statement: SameRay R x y ↔ SameRay R y x
  proof: ⟨SameRay.symm, SameRay.symm⟩

中文:
定理 sameRay_comm
  结论: SameRay R x y ↔ SameRay R y x
  证明: ⟨SameRay.symm, SameRay.symm⟩

Depends on / 依赖: SameRay, SameRay.symm
-/
theorem sameRay_comm : SameRay R x y ↔ SameRay R y x :=
  ⟨SameRay.symm, SameRay.symm⟩

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 -> x = 0 ∨ z = 0)
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx); · exact zero_left z
  rcases eq_or_ne z 0 with (rfl | hz); · exact zero_right x
  rcases eq_or_ne y 0 with (rfl | hy)
  · exact (hy rfl).elim (fun h => (hx h).elim) fun h => (hz h).elim
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩
  refine Or.inr (Or.inr <| ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, ?_⟩)
  rw [mul_smul]; rw [mul_smul]; rw [h₁]; rw [← h₂]; rw [smul_comm]

中文:
定理 trans
  条件: (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 -> x = 0 ∨ z = 0)
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx); · exact zero_left z
  rcases eq_or_ne z 0 with (rfl | hz); · exact zero_right x
  rcases eq_or_ne y 0 with (rfl | hy)
  · exact (hy rfl).elim (fun h => (hx h).elim) fun h => (hz h).elim
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩
  refine Or.inr (Or.inr <| ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, ?_⟩)
  rw [mul_smul]; rw [mul_smul]; rw [h₁]; rw [← h₂]; rw [smul_comm]

Depends on / 依赖: Or.inr, eq_or_ne, exists_pos, hxy.exists_pos, hyz.exists_pos, mul_pos, mul_smul, smul_comm, zero_left, zero_right
-/
theorem trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 -> x = 0 ∨ z = 0) :
    SameRay R x z := by
  rcases eq_or_ne x 0 with (rfl | hx); · exact zero_left z
  rcases eq_or_ne z 0 with (rfl | hz); · exact zero_right x
  rcases eq_or_ne y 0 with (rfl | hy)
  · exact (hy rfl).elim (fun h => (hx h).elim) fun h => (hz h).elim
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩
  refine Or.inr (Or.inr <| ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, ?_⟩)
  rw [mul_smul]; rw [mul_smul]; rw [h₁]; rw [← h₂]; rw [smul_comm]

variable {S : Type*} [CommSemiring S] [PartialOrder S]
  [Algebra S R] [Module S M] [SMulPosMono S R]
  [IsScalarTower S R M] {a : S}

/--
lemma `sameRay_nonneg_smul_right` / 引理 `sameRay_nonneg_smul_right`

English:
lemma sameRay_nonneg_smul_right
  given: (v : M) (h : 0 <= a)
  statement: SameRay R v (a • v)
  proof: by
  obtain h | h := (algebraMap_nonneg R h).eq_or_lt'
  · rw [← algebraMap_smul R a v, h, zero_smul]
    exact zero_right _
· refine Or.inr Or.inr ⟨algebraMap S R a, 1, h, by nontriviality R; exact zero_lt_one, ?_⟩
    module

中文:
引理 sameRay_nonneg_smul_right
  条件: (v : M) (h : 0 <= a)
  结论: SameRay R v (a • v)
  证明: by
  obtain h | h := (algebraMap_nonneg R h).eq_or_lt'
  · rw [← algebraMap_smul R a v, h, zero_smul]
    exact zero_right _
· refine Or.inr Or.inr ⟨algebraMap S R a, 1, h, by nontriviality R; exact zero_lt_one, ?_⟩
    module

Depends on / 依赖: Or.inr, algebraMap, algebraMap_nonneg, algebraMap_smul, eq_or_lt, module, nontriviality, zero_lt_one, zero_right, zero_smul
-/
lemma sameRay_nonneg_smul_right (v : M) (h : 0 <= a) : SameRay R v (a • v) := by
  obtain h | h := (algebraMap_nonneg R h).eq_or_lt'
  · rw [← algebraMap_smul R a v, h, zero_smul]
    exact zero_right _
· refine Or.inr Or.inr ⟨algebraMap S R a, 1, h, by nontriviality R; exact zero_lt_one, ?_⟩
    module

/--
lemma `sameRay_nonneg_smul_left` / 引理 `sameRay_nonneg_smul_left`

English:
lemma sameRay_nonneg_smul_left
  given: (v : M) (ha : 0 <= a)
  statement: SameRay R (a • v) v
  proof: (sameRay_nonneg_smul_right v ha).symm

中文:
引理 sameRay_nonneg_smul_left
  条件: (v : M) (ha : 0 <= a)
  结论: SameRay R (a • v) v
  证明: (sameRay_nonneg_smul_right v ha).symm

Depends on / 依赖: sameRay_nonneg_smul_right
-/
lemma sameRay_nonneg_smul_left (v : M) (ha : 0 <= a) : SameRay R (a • v) v :=
  (sameRay_nonneg_smul_right v ha).symm

/--
lemma `sameRay_pos_smul_right` / 引理 `sameRay_pos_smul_right`

English:
lemma sameRay_pos_smul_right
  given: (v : M) (ha : 0 < a)
  statement: SameRay R v (a • v)
  proof: sameRay_nonneg_smul_right v ha.le

中文:
引理 sameRay_pos_smul_right
  条件: (v : M) (ha : 0 < a)
  结论: SameRay R v (a • v)
  证明: sameRay_nonneg_smul_right v ha.le

Depends on / 依赖: ha.le, sameRay_nonneg_smul_right
-/
lemma sameRay_pos_smul_right (v : M) (ha : 0 < a) : SameRay R v (a • v) :=
  sameRay_nonneg_smul_right v ha.le

/--
lemma `sameRay_pos_smul_left` / 引理 `sameRay_pos_smul_left`

English:
lemma sameRay_pos_smul_left
  given: (v : M) (ha : 0 < a)
  statement: SameRay R (a • v) v
  proof: sameRay_nonneg_smul_left v ha.le

中文:
引理 sameRay_pos_smul_left
  条件: (v : M) (ha : 0 < a)
  结论: SameRay R (a • v) v
  证明: sameRay_nonneg_smul_left v ha.le

Depends on / 依赖: ha.le, sameRay_nonneg_smul_left
-/
lemma sameRay_pos_smul_left (v : M) (ha : 0 < a) : SameRay R (a • v) v :=
  sameRay_nonneg_smul_left v ha.le

/--
lemma `nonneg_smul_right` / 引理 `nonneg_smul_right`

English:
lemma nonneg_smul_right
  given: (h : SameRay R x y) (ha : 0 <= a)
  statement: SameRay R x (a • y)
  proof: h.trans (sameRay_nonneg_smul_right y ha) fun hy => Or.inr by rw [hy, smul_zero]

中文:
引理 nonneg_smul_right
  条件: (h : SameRay R x y) (ha : 0 <= a)
  结论: SameRay R x (a • y)
  证明: h.trans (sameRay_nonneg_smul_right y ha) fun hy => Or.inr by rw [hy, smul_zero]

Depends on / 依赖: Or.inr, h.trans, sameRay_nonneg_smul_right, smul_zero
-/
lemma nonneg_smul_right (h : SameRay R x y) (ha : 0 <= a) : SameRay R x (a • y) :=
h.trans (sameRay_nonneg_smul_right y ha) fun hy => Or.inr by rw [hy, smul_zero]

/--
lemma `nonneg_smul_left` / 引理 `nonneg_smul_left`

English:
lemma nonneg_smul_left
  given: (h : SameRay R x y) (ha : 0 <= a)
  statement: SameRay R (a • x) y
  proof: (h.symm.nonneg_smul_right ha).symm

中文:
引理 nonneg_smul_left
  条件: (h : SameRay R x y) (ha : 0 <= a)
  结论: SameRay R (a • x) y
  证明: (h.symm.nonneg_smul_right ha).symm

Depends on / 依赖: h.symm.nonneg_smul_right, nonneg_smul_right
-/
lemma nonneg_smul_left (h : SameRay R x y) (ha : 0 <= a) : SameRay R (a • x) y :=
  (h.symm.nonneg_smul_right ha).symm

/--
theorem `pos_smul_right` / 定理 `pos_smul_right`

English:
theorem pos_smul_right
  given: (h : SameRay R x y) (ha : 0 < a)
  statement: SameRay R x (a • y)
  proof: h.nonneg_smul_right ha.le

中文:
定理 pos_smul_right
  条件: (h : SameRay R x y) (ha : 0 < a)
  结论: SameRay R x (a • y)
  证明: h.nonneg_smul_right ha.le

Depends on / 依赖: h.nonneg_smul_right, ha.le, nonneg_smul_right
-/
theorem pos_smul_right (h : SameRay R x y) (ha : 0 < a) : SameRay R x (a • y) :=
  h.nonneg_smul_right ha.le

/--
theorem `pos_smul_left` / 定理 `pos_smul_left`

English:
theorem pos_smul_left
  given: (h : SameRay R x y) (hr : 0 < a)
  statement: SameRay R (a • x) y
  proof: h.nonneg_smul_left hr.le

中文:
定理 pos_smul_left
  条件: (h : SameRay R x y) (hr : 0 < a)
  结论: SameRay R (a • x) y
  证明: h.nonneg_smul_left hr.le

Depends on / 依赖: h.nonneg_smul_left, hr.le, nonneg_smul_left
-/
theorem pos_smul_left (h : SameRay R x y) (hr : 0 < a) : SameRay R (a • x) y :=
  h.nonneg_smul_left hr.le

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (f : M ->ₗ[R] N) (h : SameRay R x y)
  statement: SameRay R (f x) (f y)
  proof: (h.imp fun hx => by rw [hx, map_zero])
    Or.imp (fun hy => by rw [hy, map_zero]) fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
      ⟨r₁, r₂, hr₁, hr₂, by rw [← f.map_smul, ← f.map_smul, h]⟩

中文:
定理 map
  条件: (f : M ->ₗ[R] N) (h : SameRay R x y)
  结论: SameRay R (f x) (f y)
  证明: (h.imp fun hx => by rw [hx, map_zero])
    Or.imp (fun hy => by rw [hy, map_zero]) fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
      ⟨r₁, r₂, hr₁, hr₂, by rw [← f.map_smul, ← f.map_smul, h]⟩

Depends on / 依赖: Or.imp, f.map_smul, h.imp, map_smul, map_zero
-/
theorem map (f : M ->ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) (f y) :=
(h.imp fun hx => by rw [hx, map_zero])
    Or.imp (fun hy => by rw [hy, map_zero]) fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
      ⟨r₁, r₂, hr₁, hr₂, by rw [← f.map_smul, ← f.map_smul, h]⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.Function.Injective.sameRay_map_iff` / 定理 `_root_.Function.Injective.sameRay_map_iff`

English:
theorem _root_.Function.Injective.sameRay_map_iff
  proof: by
  simp only [SameRay, map_zero, ← hf.eq_iff, map_smul]

中文:
定理 _root_.函数.单射.sameRay_map_iff
  证明: by
  simp only [SameRay, map_zero, ← hf.eq_iff, map_smul]

Depends on / 依赖: SameRay, eq_iff, hf.eq_iff, map_smul, map_zero
-/
theorem _root_.Function.Injective.sameRay_map_iff
    {F : Type*} [FunLike F M N] [LinearMapClass F R M N]
    {f : F} (hf : Function.Injective f) :
    SameRay R (f x) (f y) ↔ SameRay R x y := by
  simp only [SameRay, map_zero, ← hf.eq_iff, map_smul]

/-- The images of two vectors under a linear equivalence are on the same ray if and only if the
original vectors are on the same ray. -/
@[simp]
/--
theorem `sameRay_map_iff` / 定理 `sameRay_map_iff`

English:
theorem sameRay_map_iff
  given: (e : M ≃ₗ[R] N)
  statement: SameRay R (e x) (e y) ↔ SameRay R x y
  proof: Function.Injective.sameRay_map_iff (EquivLike.injective e)

中文:
定理 sameRay_map_iff
  条件: (e : M ≃ₗ[R] N)
  结论: SameRay R (e x) (e y) ↔ SameRay R x y
  证明: Function.Injective.sameRay_map_iff (EquivLike.injective e)

Depends on / 依赖: EquivLike, EquivLike.injective, Function, Function.Injective.sameRay_map_iff, Injective, injective, sameRay_map_iff
-/
theorem sameRay_map_iff (e : M ≃ₗ[R] N) : SameRay R (e x) (e y) ↔ SameRay R x y :=
  Function.Injective.sameRay_map_iff (EquivLike.injective e)

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]
  proof: h.map (s • (LinearMap.id : M ->ₗ[R] M))

中文:
定理 smul
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S M] [标量交换类 R S M]
  证明: h.map (s • (LinearMap.id : M ->ₗ[R] M))

Depends on / 依赖: LinearMap, LinearMap.id, h.map
-/
theorem smul {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]
    (h : SameRay R x y) (s : S) : SameRay R (s • x) (s • y) :=
  h.map (s • (LinearMap.id : M ->ₗ[R] M))

/--
theorem `add_left` / 定理 `add_left`

English:
theorem add_left
  given: (hx : SameRay R x z) (hy : SameRay R y z)
  statement: SameRay R (x + y) z
  proof: by
  rcases eq_or_ne x 0 with (rfl | hx₀); · rwa [zero_add]
  rcases eq_or_ne y 0 with (rfl | hy₀); · rwa [add_zero]
  rcases eq_or_ne z 0 with (rfl | hz₀); · apply zero_right
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩
  refine Or.inr (Or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, ?_, ?_⟩)
  · positivity
  · convert! congr(ry • $Hx + rx • $Hy) using 1 <;> module

中文:
定理 add_left
  条件: (hx : SameRay R x z) (hy : SameRay R y z)
  结论: SameRay R (x + y) z
  证明: by
  rcases eq_or_ne x 0 with (rfl | hx₀); · rwa [zero_add]
  rcases eq_or_ne y 0 with (rfl | hy₀); · rwa [add_zero]
  rcases eq_or_ne z 0 with (rfl | hz₀); · apply zero_right
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩
  refine Or.inr (Or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, ?_, ?_⟩)
  · positivity
  · convert! congr(ry • $Hx + rx • $Hy) using 1 <;> module

Depends on / 依赖: Or.inr, add_zero, convert, eq_or_ne, exists_pos, hx.exists_pos, hy.exists_pos, module, mul_pos, zero_add, zero_right
-/
theorem add_left (hx : SameRay R x z) (hy : SameRay R y z) : SameRay R (x + y) z := by
  rcases eq_or_ne x 0 with (rfl | hx₀); · rwa [zero_add]
  rcases eq_or_ne y 0 with (rfl | hy₀); · rwa [add_zero]
  rcases eq_or_ne z 0 with (rfl | hz₀); · apply zero_right
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩
  refine Or.inr (Or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, ?_, ?_⟩)
  · positivity
  · convert! congr(ry • $Hx + rx • $Hy) using 1 <;> module

/--
theorem `add_right` / 定理 `add_right`

English:
theorem add_right
  given: (hy : SameRay R x y) (hz : SameRay R x z)
  statement: SameRay R x (y + z)
  proof: (hy.symm.add_left hz.symm).symm

中文:
定理 add_right
  条件: (hy : SameRay R x y) (hz : SameRay R x z)
  结论: SameRay R x (y + z)
  证明: (hy.symm.add_left hz.symm).symm

Depends on / 依赖: add_left, hy.symm.add_left, hz.symm
-/
theorem add_right (hy : SameRay R x y) (hz : SameRay R x z) : SameRay R x (y + z) :=
  (hy.symm.add_left hz.symm).symm

end SameRay

variable (R M)

/--
Instance `RayVector.Setoid` / 实例 `RayVector.Setoid`

English:
instance RayVector.Setoid
  signature: : Setoid (RayVector R M) where
  body: SameRay R (x : M) y
  iseqv :=
    ⟨fun _ => SameRay.refl _, fun h => h.symm, by
      intro x y z hxy hyz
      exact hxy.trans hyz fun hy => (y.2 hy).elim⟩

中文:
实例 RayVector.集合等价关系
  签名: : 集合等价关系 (RayVector R M) where
  定义体: SameRay R (x : M) y
  iseqv :=
    ⟨fun _ => SameRay.refl _, fun h => h.symm, by
      intro x y z hxy hyz
      exact hxy.trans hyz fun hy => (y.2 hy).elim⟩

Depends on / 依赖: SameRay
-/
instance RayVector.Setoid : Setoid (RayVector R M) where
  r x y := SameRay R (x : M) y
  iseqv :=
    ⟨fun _ => SameRay.refl _, fun h => h.symm, by
      intro x y z hxy hyz
      exact hxy.trans hyz fun hy => (y.2 hy).elim⟩

/--
Definition of `Module.Ray` / `Module.Ray` 的定义

English:
definition Module.Ray
  body: Quotient (RayVector.Setoid R M)

中文:
定义 模.Ray
  定义体: Quotient (RayVector.Setoid R M)

Depends on / 依赖: Quotient, RayVector, RayVector.Setoid, Setoid
-/
def Module.Ray :=
  Quotient (RayVector.Setoid R M)

variable {R M}

/--
theorem `equiv_iff_sameRay` / 定理 `equiv_iff_sameRay`

English:
theorem equiv_iff_sameRay
  given: {v₁ v₂ : RayVector R M}
  statement: v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂
  proof: Iff.rfl

中文:
定理 equiv_iff_sameRay
  条件: {v₁ v₂ : RayVector R M}
  结论: v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem equiv_iff_sameRay {v₁ v₂ : RayVector R M} : v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂ :=
  Iff.rfl

variable (R)

/--
Definition of `rayOfNeZero` / `rayOfNeZero` 的定义

English:
definition rayOfNeZero
  signature: (v : M) (h : v != 0)
  body: ⟦(RayVector.equiv R M).symm ⟨v, h⟩⟧

中文:
定义 rayOfNeZero
  签名: (v : M) (h : v != 0)
  定义体: ⟦(RayVector.equiv R M).symm ⟨v, h⟩⟧

Depends on / 依赖: RayVector, RayVector.equiv
-/
def rayOfNeZero (v : M) (h : v != 0) : Module.Ray R M :=
  ⟦(RayVector.equiv R M).symm ⟨v, h⟩⟧

/--
theorem `Module.Ray.ind` / 定理 `Module.Ray.ind`

English:
theorem Module.Ray.ind
  statement: {C : Module.Ray R M -> Prop} (h : forall (v) (hv : v != 0), C (rayOfNeZero R v hv))
  proof: Quotient.ind (Subtype.rec <| h) x

中文:
定理 模.Ray.ind
  结论: {C : 模.Ray R M -> 命题} (h : 对任意 (v) (hv : v != 0), C (rayOfNeZero R v hv))
  证明: Quotient.ind (Subtype.rec <| h) x

Depends on / 依赖: Quotient, Quotient.ind, Subtype, Subtype.rec
-/
theorem Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall (v) (hv : v != 0), C (rayOfNeZero R v hv))
    (x : Module.Ray R M) : C x :=
  Quotient.ind (Subtype.rec <| h) x

variable {R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nonempty (Module.Ray R M)
  body: Nonempty.map Quotient.mk' inferInstance

中文:
实例 [非平凡
  签名: M] : 非空 (模.Ray R M)
  定义体: Nonempty.map Quotient.mk' inferInstance

Depends on / 依赖: Nonempty, Nonempty.map, Quotient, Quotient.mk
-/
instance [Nontrivial M] : Nonempty (Module.Ray R M) :=
  Nonempty.map Quotient.mk' inferInstance

/--
theorem `ray_eq_iff` / 定理 `ray_eq_iff`

English:
theorem ray_eq_iff
  given: {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0)
  proof: Quotient.eq'

中文:
定理 ray_eq_iff
  条件: {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0)
  证明: Quotient.eq'

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) :
    rayOfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂ :=
  Quotient.eq'

/-- The ray given by a positive multiple of a nonzero vector. -/
@[simp]
/--
theorem `ray_pos_smul` / 定理 `ray_pos_smul`

English:
theorem ray_pos_smul
  given: {v : M} (h : v != 0) {r : R} (hr : 0 < r) (hrv : r • v != 0)
  proof: (ray_eq_iff _ _).2 SameRay.sameRay_pos_smul_left v hr

中文:
定理 ray_pos_smul
  条件: {v : M} (h : v != 0) {r : R} (hr : 0 < r) (hrv : r • v != 0)
  证明: (ray_eq_iff _ _).2 SameRay.sameRay_pos_smul_left v hr

Depends on / 依赖: SameRay, SameRay.sameRay_pos_smul_left, ray_eq_iff, sameRay_pos_smul_left
-/
theorem ray_pos_smul {v : M} (h : v != 0) {r : R} (hr : 0 < r) (hrv : r • v != 0) :
    rayOfNeZero R (r • v) hrv = rayOfNeZero R v h :=
(ray_eq_iff _ _).2 SameRay.sameRay_pos_smul_left v hr

/--
Definition of `RayVector.mapLinearEquiv` / `RayVector.mapLinearEquiv` 的定义

English:
definition RayVector.mapLinearEquiv
  signature: (e : M ≃ₗ[R] N)
  body: Equiv.subtypeEquiv e.toEquiv fun _ => e.map_ne_zero_iff.symm

中文:
定义 RayVector.mapLinearEquiv
  签名: (e : M ≃ₗ[R] N)
  定义体: Equiv.subtypeEquiv e.toEquiv fun _ => e.map_ne_zero_iff.symm

Depends on / 依赖: Equiv.subtypeEquiv, e.map_ne_zero_iff.symm, e.toEquiv, map_ne_zero_iff, subtypeEquiv, toEquiv
-/
def RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector R M ≃ RayVector R N :=
  Equiv.subtypeEquiv e.toEquiv fun _ => e.map_ne_zero_iff.symm

/--
Definition of `Module.Ray.map` / `Module.Ray.map` 的定义

English:
definition Module.Ray.map
  signature: (e : M ≃ₗ[R] N)
  body: Quotient.congr (RayVector.mapLinearEquiv e) fun _ _ => (SameRay.sameRay_map_iff _).symm

@[simp]

中文:
定义 模.Ray.map
  签名: (e : M ≃ₗ[R] N)
  定义体: Quotient.congr (RayVector.mapLinearEquiv e) fun _ _ => (SameRay.sameRay_map_iff _).symm

@[simp]

Depends on / 依赖: Quotient, Quotient.congr, RayVector, RayVector.mapLinearEquiv, SameRay, SameRay.sameRay_map_iff, mapLinearEquiv, sameRay_map_iff
-/
def Module.Ray.map (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N :=
  Quotient.congr (RayVector.mapLinearEquiv e) fun _ _ => (SameRay.sameRay_map_iff _).symm

@[simp]
/--
theorem `Module.Ray.map_apply` / 定理 `Module.Ray.map_apply`

English:
theorem Module.Ray.map_apply
  given: (e : M ≃ₗ[R] N) (v : M) (hv : v != 0)
  proof: rfl

@[simp]

中文:
定理 模.Ray.map_apply
  条件: (e : M ≃ₗ[R] N) (v : M) (hv : v != 0)
  证明: rfl

@[simp]
-/
theorem Module.Ray.map_apply (e : M ≃ₗ[R] N) (v : M) (hv : v != 0) :
    Module.Ray.map e (rayOfNeZero _ v hv) = rayOfNeZero _ (e v) (e.map_ne_zero_iff.2 hv) :=
  rfl

@[simp]
/--
theorem `Module.Ray.map_refl` / 定理 `Module.Ray.map_refl`

English:
theorem Module.Ray.map_refl
  statement: (Module.Ray.map <| LinearEquiv.refl R M) = Equiv.refl _
  proof: Equiv.ext Module.Ray.ind R fun _ _ => rfl

@[simp]

中文:
定理 模.Ray.map_refl
  结论: (模.Ray.map <| 线性等价.refl R M) = 等价.refl _
  证明: Equiv.ext Module.Ray.ind R fun _ _ => rfl

@[simp]

Depends on / 依赖: Equiv.ext, Module, Module.Ray.ind
-/
theorem Module.Ray.map_refl : (Module.Ray.map <| LinearEquiv.refl R M) = Equiv.refl _ :=
Equiv.ext Module.Ray.ind R fun _ _ => rfl

@[simp]
/--
theorem `Module.Ray.map_symm` / 定理 `Module.Ray.map_symm`

English:
theorem Module.Ray.map_symm
  given: (e : M ≃ₗ[R] N)
  statement: (Module.Ray.map e).symm = Module.Ray.map e.symm
  proof: rfl

中文:
定理 模.Ray.map_symm
  条件: (e : M ≃ₗ[R] N)
  结论: (模.Ray.map e).symm = 模.Ray.map e.symm
  证明: rfl
-/
theorem Module.Ray.map_symm (e : M ≃ₗ[R] N) : (Module.Ray.map e).symm = Module.Ray.map e.symm :=
  rfl

section Action

variable {G : Type*} [Group G] [DistribMulAction G M]

/-- Any invertible action preserves the non-zeroness of ray vectors. This is primarily of interest
when `G = Rˣ` -/
instance {R : Type*} : MulAction G (RayVector R M) where
  smul r := Subtype.map (r • ·) fun _ => (smul_ne_zero_iff_ne _).2
mul_smul a b _ := Subtype.ext mul_smul a b _
one_smul _ := Subtype.ext one_smul _ _

variable [SMulCommClass R G M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G (Module.Ray R M)
  body: Quotient.map (r • ·) fun _ _ h => h.smul _
mul_smul a b := Quotient.ind fun _ => congr_arg Quotient.mk' mul_smul a b _
one_smul := Quotient.ind fun _ => congr_arg Quotient.mk' one_smul _ _

中文:
实例 :
  签名: 乘法作用 G (模.Ray R M)
  定义体: Quotient.map (r • ·) fun _ _ h => h.smul _
mul_smul a b := Quotient.ind fun _ => congr_arg Quotient.mk' mul_smul a b _
one_smul := Quotient.ind fun _ => congr_arg Quotient.mk' one_smul _ _

Depends on / 依赖: Quotient, Quotient.map, h.smul
-/
instance : MulAction G (Module.Ray R M) where
  smul r := Quotient.map (r • ·) fun _ _ h => h.smul _
mul_smul a b := Quotient.ind fun _ => congr_arg Quotient.mk' mul_smul a b _
one_smul := Quotient.ind fun _ => congr_arg Quotient.mk' one_smul _ _

/-- The action via `LinearEquiv.apply_distribMulAction` corresponds to `Module.Ray.map`. -/
@[simp]
/--
theorem `Module.Ray.linearEquiv_smul_eq_map` / 定理 `Module.Ray.linearEquiv_smul_eq_map`

English:
theorem Module.Ray.linearEquiv_smul_eq_map
  given: (e : M ≃ₗ[R] M) (v : Module.Ray R M)
  proof: rfl

@[simp]

中文:
定理 模.Ray.linearEquiv_smul_eq_map
  条件: (e : M ≃ₗ[R] M) (v : 模.Ray R M)
  证明: rfl

@[simp]
-/
theorem Module.Ray.linearEquiv_smul_eq_map (e : M ≃ₗ[R] M) (v : Module.Ray R M) :
    e • v = Module.Ray.map e v :=
  rfl

@[simp]
/--
theorem `smul_rayOfNeZero` / 定理 `smul_rayOfNeZero`

English:
theorem smul_rayOfNeZero
  given: (g : G) (v : M) (hv)
  proof: rfl

中文:
定理 smul_rayOfNeZero
  条件: (g : G) (v : M) (hv)
  证明: rfl
-/
theorem smul_rayOfNeZero (g : G) (v : M) (hv) :
    g • rayOfNeZero R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv) :=
  rfl

end Action

namespace Module.Ray

/--
theorem `units_smul_of_pos` / 定理 `units_smul_of_pos`

English:
theorem units_smul_of_pos
  given: (u : Rˣ) (hu : 0 < (u : R)) (v : Module.Ray R M)
  statement: u • v = v
  proof: by
  induction v using Module.Ray.ind
  rw [smul_rayOfNeZero]; rw [ray_eq_iff]
  exact SameRay.sameRay_pos_smul_left _ hu

中文:
定理 units_smul_of_pos
  条件: (u : Rˣ) (hu : 0 < (u : R)) (v : 模.Ray R M)
  结论: u • v = v
  证明: by
  induction v using Module.Ray.ind
  rw [smul_rayOfNeZero]; rw [ray_eq_iff]
  exact SameRay.sameRay_pos_smul_left _ hu

Depends on / 依赖: Module, Module.Ray.ind, SameRay, SameRay.sameRay_pos_smul_left, ray_eq_iff, sameRay_pos_smul_left, smul_rayOfNeZero
-/
theorem units_smul_of_pos (u : Rˣ) (hu : 0 < (u : R)) (v : Module.Ray R M) : u • v = v := by
  induction v using Module.Ray.ind
  rw [smul_rayOfNeZero]; rw [ray_eq_iff]
  exact SameRay.sameRay_pos_smul_left _ hu

/--
Definition of `someRayVector` / `someRayVector` 的定义

English:
definition someRayVector
  signature: (x : Module.Ray R M)
  body: Quotient.out x

中文:
定义 someRayVector
  签名: (x : 模.Ray R M)
  定义体: Quotient.out x

Depends on / 依赖: Quotient, Quotient.out
-/
def someRayVector (x : Module.Ray R M) : RayVector R M :=
  Quotient.out x

/-- The ray of `someRayVector`. -/
@[simp]
/--
theorem `someRayVector_ray` / 定理 `someRayVector_ray`

English:
theorem someRayVector_ray
  given: (x : Module.Ray R M)
  statement: (⟦x.someRayVector⟧ : Module.Ray R M) = x
  proof: Quotient.out_eq _

中文:
定理 someRayVector_ray
  条件: (x : 模.Ray R M)
  结论: (⟦x.someRayVector⟧ : 模.Ray R M) = x
  证明: Quotient.out_eq _

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem someRayVector_ray (x : Module.Ray R M) : (⟦x.someRayVector⟧ : Module.Ray R M) = x :=
  Quotient.out_eq _

/--
Definition of `someVector` / `someVector` 的定义

English:
definition someVector
  signature: (x : Module.Ray R M)
  body: x.someRayVector

中文:
定义 someVector
  签名: (x : 模.Ray R M)
  定义体: x.someRayVector

Depends on / 依赖: someRayVector, x.someRayVector
-/
def someVector (x : Module.Ray R M) : M :=
  x.someRayVector

/-- `someVector` is nonzero. -/
@[simp]
/--
theorem `someVector_ne_zero` / 定理 `someVector_ne_zero`

English:
theorem someVector_ne_zero
  given: (x : Module.Ray R M)
  statement: x.someVector != 0
  proof: x.someRayVector.property

中文:
定理 someVector_ne_zero
  条件: (x : 模.Ray R M)
  结论: x.someVector != 0
  证明: x.someRayVector.property

Depends on / 依赖: property, someRayVector, x.someRayVector.property
-/
theorem someVector_ne_zero (x : Module.Ray R M) : x.someVector != 0 :=
  x.someRayVector.property

/-- The ray of `someVector`. -/
@[simp]
/--
theorem `someVector_ray` / 定理 `someVector_ray`

English:
theorem someVector_ray
  given: (x : Module.Ray R M)
  statement: rayOfNeZero R _ x.someVector_ne_zero = x
  proof: (congr_arg _ (Subtype.coe_eta _ _) :).trans x.out_eq

中文:
定理 someVector_ray
  条件: (x : 模.Ray R M)
  结论: rayOfNeZero R _ x.someVector_ne_zero = x
  证明: (congr_arg _ (Subtype.coe_eta _ _) :).trans x.out_eq

Depends on / 依赖: Subtype, Subtype.coe_eta, coe_eta, congr_arg, out_eq, x.out_eq
-/
theorem someVector_ray (x : Module.Ray R M) : rayOfNeZero R _ x.someVector_ne_zero = x :=
  (congr_arg _ (Subtype.coe_eta _ _) :).trans x.out_eq

end Module.Ray

end StrictOrderedCommSemiring

section StrictOrderedCommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] {x y : M}

/-- `SameRay.neg` as an `iff`. -/
@[simp]
/--
theorem `sameRay_neg_iff` / 定理 `sameRay_neg_iff`

English:
theorem sameRay_neg_iff
  statement: SameRay R (-x) (-y) ↔ SameRay R x y
  proof: by
  simp only [SameRay, neg_eq_zero, smul_neg, neg_inj]

alias ⟨SameRay.of_neg, SameRay.neg⟩ := sameRay_neg_iff

中文:
定理 sameRay_neg_iff
  结论: SameRay R (-x) (-y) ↔ SameRay R x y
  证明: by
  simp only [SameRay, neg_eq_zero, smul_neg, neg_inj]

alias ⟨SameRay.of_neg, SameRay.neg⟩ := sameRay_neg_iff

Depends on / 依赖: SameRay, neg_eq_zero, neg_inj, smul_neg
-/
theorem sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y := by
  simp only [SameRay, neg_eq_zero, smul_neg, neg_inj]

alias ⟨SameRay.of_neg, SameRay.neg⟩ := sameRay_neg_iff

/--
theorem `sameRay_neg_swap` / 定理 `sameRay_neg_swap`

English:
theorem sameRay_neg_swap
  statement: SameRay R (-x) y ↔ SameRay R x (-y)
  proof: by rw [← sameRay_neg_iff, neg_neg]

中文:
定理 sameRay_neg_swap
  结论: SameRay R (-x) y ↔ SameRay R x (-y)
  证明: by rw [← sameRay_neg_iff, neg_neg]

Depends on / 依赖: neg_neg, sameRay_neg_iff
-/
theorem sameRay_neg_swap : SameRay R (-x) y ↔ SameRay R x (-y) := by rw [← sameRay_neg_iff, neg_neg]

/--
lemma `eq_zero_of_sameRay_neg_smul_right` / 引理 `eq_zero_of_sameRay_neg_smul_right`

English:
lemma eq_zero_of_sameRay_neg_smul_right
  statement: [IsDomain R] [IsTorsionFree R M] {r : R} (hr : r < 0)
  proof: by
  rcases h with (rfl | h₀ | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rfl
  · simpa [hr.ne] using h₀
  · rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h
    refine h.resolve_left (ne_of_gt <| sub_pos.2 ?_)
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁

中文:
引理 eq_zero_of_sameRay_neg_smul_right
  结论: [是整环 R] [是无挠 R M] {r : R} (hr : r < 0)
  证明: by
  rcases h with (rfl | h₀ | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rfl
  · simpa [hr.ne] using h₀
  · rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h
    refine h.resolve_left (ne_of_gt <| sub_pos.2 ?_)
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁

Depends on / 依赖: h.resolve_left, hr.ne, mul_neg_of_pos_of_neg, ne_of_gt, resolve_left, smul_eq_zero, smul_smul, sub_eq_zero, sub_pos, sub_smul
-/
lemma eq_zero_of_sameRay_neg_smul_right [IsDomain R] [IsTorsionFree R M] {r : R} (hr : r < 0)
    (h : SameRay R x (r • x)) : x = 0 := by
  rcases h with (rfl | h₀ | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rfl
  · simpa [hr.ne] using h₀
  · rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h
    refine h.resolve_left (ne_of_gt <| sub_pos.2 ?_)
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁

/--
theorem `eq_zero_of_sameRay_self_neg` / 定理 `eq_zero_of_sameRay_self_neg`

English:
theorem eq_zero_of_sameRay_self_neg
  given: [IsDomain R] [IsTorsionFree R M] (h : SameRay R x (-x))
  proof: by
  refine eq_zero_of_sameRay_neg_smul_right (neg_lt_zero.2 (zero_lt_one' R)) ?_
  rwa [neg_one_smul]

中文:
定理 eq_zero_of_sameRay_self_neg
  条件: [是整环 R] [是无挠 R M] (h : SameRay R x (-x))
  证明: by
  refine eq_zero_of_sameRay_neg_smul_right (neg_lt_zero.2 (zero_lt_one' R)) ?_
  rwa [neg_one_smul]

Depends on / 依赖: eq_zero_of_sameRay_neg_smul_right, neg_lt_zero, neg_one_smul, zero_lt_one
-/
theorem eq_zero_of_sameRay_self_neg [IsDomain R] [IsTorsionFree R M] (h : SameRay R x (-x)) :
    x = 0 := by
  refine eq_zero_of_sameRay_neg_smul_right (neg_lt_zero.2 (zero_lt_one' R)) ?_
  rwa [neg_one_smul]

namespace RayVector

/-- Negating a nonzero vector. -/
instance {R : Type*} : Neg (RayVector R M) :=
  ⟨fun v => (equiv R M).symm ⟨-v, neg_ne_zero.2 v.prop⟩⟩

/-- Negating a nonzero vector commutes with coercion to the underlying module. -/
@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: {R : Type*} (v : RayVector R M)
  statement: ↑(-v) = -(v : M)
  proof: rfl

中文:
定理 coe_neg
  条件: {R : 类型} (v : RayVector R M)
  结论: ↑(-v) = -(v : M)
  证明: rfl
-/
theorem coe_neg {R : Type*} (v : RayVector R M) : ↑(-v) = -(v : M) :=
  rfl

/-- Negating a nonzero vector twice produces the original vector. -/
instance {R : Type*} : InvolutiveNeg (RayVector R M) where
  neg_neg v := by rw [RayVector.ext_iff, coe_neg, coe_neg, neg_neg]

/-- If two nonzero vectors are equivalent, so are their negations. -/
@[simp]
/--
theorem `equiv_neg_iff` / 定理 `equiv_neg_iff`

English:
theorem equiv_neg_iff
  given: {v₁ v₂ : RayVector R M}
  statement: -v₁ ≈ -v₂ ↔ v₁ ≈ v₂
  proof: sameRay_neg_iff

中文:
定理 equiv_neg_iff
  条件: {v₁ v₂ : RayVector R M}
  结论: -v₁ ≈ -v₂ ↔ v₁ ≈ v₂
  证明: sameRay_neg_iff

Depends on / 依赖: sameRay_neg_iff
-/
theorem equiv_neg_iff {v₁ v₂ : RayVector R M} : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ :=
  sameRay_neg_iff

end RayVector

variable (R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (Module.Ray R M)
  body: ⟨Quotient.map (fun v => -v) fun _ _ => RayVector.equiv_neg_iff.2⟩

中文:
实例 :
  签名: 取负 (模.Ray R M)
  定义体: ⟨Quotient.map (fun v => -v) fun _ _ => RayVector.equiv_neg_iff.2⟩

Depends on / 依赖: Quotient, Quotient.map, RayVector, RayVector.equiv_neg_iff, equiv_neg_iff
-/
instance : Neg (Module.Ray R M) :=
  ⟨Quotient.map (fun v => -v) fun _ _ => RayVector.equiv_neg_iff.2⟩

/-- The ray given by the negation of a nonzero vector. -/
@[simp]
/--
theorem `neg_rayOfNeZero` / 定理 `neg_rayOfNeZero`

English:
theorem neg_rayOfNeZero
  given: (v : M) (h : v != 0)
  proof: rfl

中文:
定理 neg_rayOfNeZero
  条件: (v : M) (h : v != 0)
  证明: rfl
-/
theorem neg_rayOfNeZero (v : M) (h : v != 0) :
    -rayOfNeZero R _ h = rayOfNeZero R (-v) (neg_ne_zero.2 h) :=
  rfl

namespace Module.Ray

variable {R}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveNeg (Module.Ray R M)
  body: by apply ind R (by simp) x
  -- Quotient.ind (fun a => congr_arg Quotient.mk' <| neg_neg _) x

中文:
实例 :
  签名: InvolutiveNeg (模.Ray R M)
  定义体: by apply ind R (by simp) x
  -- Quotient.ind (fun a => congr_arg Quotient.mk' <| neg_neg _) x
-/
instance : InvolutiveNeg (Module.Ray R M) where
  neg_neg x := by apply ind R (by simp) x
  -- Quotient.ind (fun a => congr_arg Quotient.mk' <| neg_neg _) x

/--
theorem `ne_neg_self` / 定理 `ne_neg_self`

English:
theorem ne_neg_self
  given: [IsDomain R] [IsTorsionFree R M] (x : Module.Ray R M)
  statement: x != -x
  proof: by
  induction x using Module.Ray.ind with | h x hx =>
  rw [neg_rayOfNeZero]; rw [Ne]; rw [ray_eq_iff]
  exact mt eq_zero_of_sameRay_self_neg hx

中文:
定理 ne_neg_self
  条件: [是整环 R] [是无挠 R M] (x : 模.Ray R M)
  结论: x != -x
  证明: by
  induction x using Module.Ray.ind with | h x hx =>
  rw [neg_rayOfNeZero]; rw [Ne]; rw [ray_eq_iff]
  exact mt eq_zero_of_sameRay_self_neg hx

Depends on / 依赖: Module, Module.Ray.ind, eq_zero_of_sameRay_self_neg, neg_rayOfNeZero, ray_eq_iff
-/
theorem ne_neg_self [IsDomain R] [IsTorsionFree R M] (x : Module.Ray R M) : x != -x := by
  induction x using Module.Ray.ind with | h x hx =>
  rw [neg_rayOfNeZero]; rw [Ne]; rw [ray_eq_iff]
  exact mt eq_zero_of_sameRay_self_neg hx

/--
theorem `neg_units_smul` / 定理 `neg_units_smul`

English:
theorem neg_units_smul
  given: (u : Rˣ) (v : Module.Ray R M)
  statement: -u • v = -(u • v)
  proof: by
  induction v using Module.Ray.ind
  simp only [smul_rayOfNeZero, Units.smul_def, Units.val_neg, neg_smul, neg_rayOfNeZero]

中文:
定理 neg_units_smul
  条件: (u : Rˣ) (v : 模.Ray R M)
  结论: -u • v = -(u • v)
  证明: by
  induction v using Module.Ray.ind
  simp only [smul_rayOfNeZero, Units.smul_def, Units.val_neg, neg_smul, neg_rayOfNeZero]

Depends on / 依赖: Module, Module.Ray.ind, Units.smul_def, Units.val_neg, neg_rayOfNeZero, neg_smul, smul_def, smul_rayOfNeZero, val_neg
-/
theorem neg_units_smul (u : Rˣ) (v : Module.Ray R M) : -u • v = -(u • v) := by
  induction v using Module.Ray.ind
  simp only [smul_rayOfNeZero, Units.smul_def, Units.val_neg, neg_smul, neg_rayOfNeZero]

/--
theorem `units_smul_of_neg` / 定理 `units_smul_of_neg`

English:
theorem units_smul_of_neg
  given: (u : Rˣ) (hu : (u : R) < 0) (v : Module.Ray R M)
  statement: u • v = -v
  proof: by
  rw [← neg_inj]; rw [neg_neg]; rw [← neg_units_smul]; rw [units_smul_of_pos]
  rwa [Units.val_neg, Right.neg_pos_iff]

@[simp]

中文:
定理 units_smul_of_neg
  条件: (u : Rˣ) (hu : (u : R) < 0) (v : 模.Ray R M)
  结论: u • v = -v
  证明: by
  rw [← neg_inj]; rw [neg_neg]; rw [← neg_units_smul]; rw [units_smul_of_pos]
  rwa [Units.val_neg, Right.neg_pos_iff]

@[simp]

Depends on / 依赖: Right.neg_pos_iff, Units.val_neg, neg_inj, neg_neg, neg_pos_iff, neg_units_smul, units_smul_of_pos, val_neg
-/
theorem units_smul_of_neg (u : Rˣ) (hu : (u : R) < 0) (v : Module.Ray R M) : u • v = -v := by
  rw [← neg_inj]; rw [neg_neg]; rw [← neg_units_smul]; rw [units_smul_of_pos]
  rwa [Units.val_neg, Right.neg_pos_iff]

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : M ≃ₗ[R] N) (v : Module.Ray R M)
  statement: map f (-v) = -map f v
  proof: by
  induction v using Module.Ray.ind with | h g hg => simp

中文:
定理 map_neg
  条件: (f : M ≃ₗ[R] N) (v : 模.Ray R M)
  结论: map f (-v) = -map f v
  证明: by
  induction v using Module.Ray.ind with | h g hg => simp
-/
protected theorem map_neg (f : M ≃ₗ[R] N) (v : Module.Ray R M) : map f (-v) = -map f v := by
  induction v using Module.Ray.ind with | h g hg => simp

end Module.Ray

end StrictOrderedCommRing

section LinearOrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/--
theorem `sameRay_of_mem_orbit` / 定理 `sameRay_of_mem_orbit`

English:
theorem sameRay_of_mem_orbit
  given: {v₁ v₂ : M} (h : v₁ in MulAction.orbit (Units.posSubgroup R) v₂)
  proof: by
  rcases h with ⟨⟨r, hr : 0 < r.1⟩, rfl : r • v₂ = v₁⟩
  exact SameRay.sameRay_pos_smul_left _ hr

中文:
定理 sameRay_of_mem_orbit
  条件: {v₁ v₂ : M} (h : v₁ in 乘法作用.orbit (单位群.posSubgroup R) v₂)
  证明: by
  rcases h with ⟨⟨r, hr : 0 < r.1⟩, rfl : r • v₂ = v₁⟩
  exact SameRay.sameRay_pos_smul_left _ hr

Depends on / 依赖: SameRay, SameRay.sameRay_pos_smul_left, sameRay_pos_smul_left
-/
theorem sameRay_of_mem_orbit {v₁ v₂ : M} (h : v₁ in MulAction.orbit (Units.posSubgroup R) v₂) :
    SameRay R v₁ v₂ := by
  rcases h with ⟨⟨r, hr : 0 < r.1⟩, rfl : r • v₂ = v₁⟩
  exact SameRay.sameRay_pos_smul_left _ hr

/-- Scaling by an inverse unit is the same as scaling by itself. -/
@[simp]
/--
theorem `units_inv_smul` / 定理 `units_inv_smul`

English:
theorem units_inv_smul
  given: (u : Rˣ) (v : Module.Ray R M)
  statement: u⁻¹ • v = u • v
  proof: have := mul_self_pos.2 u.ne_zero
  calc
u⁻¹ • v = (u * u) • u⁻¹ • v := Eq.symm (u⁻¹ • v).units_smul_of_pos _ (by exact this)
    _ = u • v := by rw [mul_smul, smul_inv_smul]

中文:
定理 units_inv_smul
  条件: (u : Rˣ) (v : 模.Ray R M)
  结论: u⁻¹ • v = u • v
  证明: have := mul_self_pos.2 u.ne_zero
  calc
u⁻¹ • v = (u * u) • u⁻¹ • v := Eq.symm (u⁻¹ • v).units_smul_of_pos _ (by exact this)
    _ = u • v := by rw [mul_smul, smul_inv_smul]

Depends on / 依赖: Eq.symm, mul_self_pos, mul_smul, ne_zero, smul_inv_smul, u.ne_zero, units_smul_of_pos
-/
theorem units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v = u • v :=
  have := mul_self_pos.2 u.ne_zero
  calc
u⁻¹ • v = (u * u) • u⁻¹ • v := Eq.symm (u⁻¹ • v).units_smul_of_pos _ (by exact this)
    _ = u • v := by rw [mul_smul, smul_inv_smul]

/--
theorem `sameRay_smul_smul_of_mul_nonneg` / 定理 `sameRay_smul_smul_of_mul_nonneg`

English:
theorem sameRay_smul_smul_of_mul_nonneg
  given: {v : M} {c₁ c₂ : R} (h : 0 <= c₁ * c₂)
  proof: by
  rcases eq_or_ne c₁ 0 with hc₁ | hc₁
  · rw [hc₁, zero_smul]; exact SameRay.zero_left _
  rcases eq_or_ne c₂ 0 with hc₂ | hc₂
  · rw [hc₂, zero_smul]; exact SameRay.zero_right _
  have hpos : 0 < c₁ * c₂ := h.lt_of_ne (mul_ne_zero hc₁ hc₂).symm
  rcases mul_pos_iff.mp hpos with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr (Or.inr ⟨c₂, c₁, h₂, h₁, by module⟩)
  · exact Or.inr (Or.inr ⟨-c₂, -c₁, neg_pos.2 h₂, neg_pos.2 h₁, by module⟩)

中文:
定理 sameRay_smul_smul_of_mul_nonneg
  条件: {v : M} {c₁ c₂ : R} (h : 0 <= c₁ * c₂)
  证明: by
  rcases eq_or_ne c₁ 0 with hc₁ | hc₁
  · rw [hc₁, zero_smul]; exact SameRay.zero_left _
  rcases eq_or_ne c₂ 0 with hc₂ | hc₂
  · rw [hc₂, zero_smul]; exact SameRay.zero_right _
  have hpos : 0 < c₁ * c₂ := h.lt_of_ne (mul_ne_zero hc₁ hc₂).symm
  rcases mul_pos_iff.mp hpos with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr (Or.inr ⟨c₂, c₁, h₂, h₁, by module⟩)
  · exact Or.inr (Or.inr ⟨-c₂, -c₁, neg_pos.2 h₂, neg_pos.2 h₁, by module⟩)

Depends on / 依赖: Or.inr, SameRay, SameRay.zero_left, SameRay.zero_right, eq_or_ne, h.lt_of_ne, lt_of_ne, module, mul_ne_zero, mul_pos_iff, mul_pos_iff.mp, neg_pos, zero_left, zero_right, zero_smul
-/
theorem sameRay_smul_smul_of_mul_nonneg {v : M} {c₁ c₂ : R} (h : 0 <= c₁ * c₂) :
    SameRay R (c₁ • v) (c₂ • v) := by
  rcases eq_or_ne c₁ 0 with hc₁ | hc₁
  · rw [hc₁, zero_smul]; exact SameRay.zero_left _
  rcases eq_or_ne c₂ 0 with hc₂ | hc₂
  · rw [hc₂, zero_smul]; exact SameRay.zero_right _
  have hpos : 0 < c₁ * c₂ := h.lt_of_ne (mul_ne_zero hc₁ hc₂).symm
  rcases mul_pos_iff.mp hpos with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr (Or.inr ⟨c₂, c₁, h₂, h₁, by module⟩)
  · exact Or.inr (Or.inr ⟨-c₂, -c₁, neg_pos.2 h₂, neg_pos.2 h₁, by module⟩)

section

variable [IsTorsionFree R M]

@[simp]
/--
theorem `sameRay_smul_right_iff` / 定理 `sameRay_smul_right_iff`

English:
theorem sameRay_smul_right_iff
  given: {v : M} {r : R}
  statement: SameRay R v (r • v) ↔ 0 <= r ∨ v = 0
  proof: ⟨fun hrv => or_iff_not_imp_left.2 fun hr => eq_zero_of_sameRay_neg_smul_right (not_le.1 hr) hrv,
    or_imp.2 ⟨SameRay.sameRay_nonneg_smul_right v, fun h => h.symm ▸ SameRay.zero_left _⟩⟩

中文:
定理 sameRay_smul_right_iff
  条件: {v : M} {r : R}
  结论: SameRay R v (r • v) ↔ 0 <= r ∨ v = 0
  证明: ⟨fun hrv => or_iff_not_imp_left.2 fun hr => eq_zero_of_sameRay_neg_smul_right (not_le.1 hr) hrv,
    or_imp.2 ⟨SameRay.sameRay_nonneg_smul_right v, fun h => h.symm ▸ SameRay.zero_left _⟩⟩

Depends on / 依赖: SameRay, SameRay.sameRay_nonneg_smul_right, SameRay.zero_left, eq_zero_of_sameRay_neg_smul_right, h.symm, not_le, or_iff_not_imp_left, or_imp, sameRay_nonneg_smul_right, zero_left
-/
theorem sameRay_smul_right_iff {v : M} {r : R} : SameRay R v (r • v) ↔ 0 <= r ∨ v = 0 :=
  ⟨fun hrv => or_iff_not_imp_left.2 fun hr => eq_zero_of_sameRay_neg_smul_right (not_le.1 hr) hrv,
    or_imp.2 ⟨SameRay.sameRay_nonneg_smul_right v, fun h => h.symm ▸ SameRay.zero_left _⟩⟩

/--
theorem `sameRay_smul_right_iff_of_ne` / 定理 `sameRay_smul_right_iff_of_ne`

English:
theorem sameRay_smul_right_iff_of_ne
  given: {v : M} (hv : v != 0) {r : R} (hr : r != 0)
  proof: by
  simp only [sameRay_smul_right_iff, hv, or_false, hr.symm.le_iff_lt]

@[simp]

中文:
定理 sameRay_smul_right_iff_of_ne
  条件: {v : M} (hv : v != 0) {r : R} (hr : r != 0)
  证明: by
  simp only [sameRay_smul_right_iff, hv, or_false, hr.symm.le_iff_lt]

@[simp]

Depends on / 依赖: hr.symm.le_iff_lt, le_iff_lt, or_false, sameRay_smul_right_iff
-/
theorem sameRay_smul_right_iff_of_ne {v : M} (hv : v != 0) {r : R} (hr : r != 0) :
    SameRay R v (r • v) ↔ 0 < r := by
  simp only [sameRay_smul_right_iff, hv, or_false, hr.symm.le_iff_lt]

@[simp]
/--
theorem `sameRay_smul_left_iff` / 定理 `sameRay_smul_left_iff`

English:
theorem sameRay_smul_left_iff
  given: {v : M} {r : R}
  statement: SameRay R (r • v) v ↔ 0 <= r ∨ v = 0
  proof: SameRay.sameRay_comm.trans sameRay_smul_right_iff

中文:
定理 sameRay_smul_left_iff
  条件: {v : M} {r : R}
  结论: SameRay R (r • v) v ↔ 0 <= r ∨ v = 0
  证明: SameRay.sameRay_comm.trans sameRay_smul_right_iff

Depends on / 依赖: SameRay, SameRay.sameRay_comm.trans, sameRay_comm, sameRay_smul_right_iff
-/
theorem sameRay_smul_left_iff {v : M} {r : R} : SameRay R (r • v) v ↔ 0 <= r ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_smul_right_iff

/--
theorem `sameRay_smul_left_iff_of_ne` / 定理 `sameRay_smul_left_iff_of_ne`

English:
theorem sameRay_smul_left_iff_of_ne
  given: {v : M} (hv : v != 0) {r : R} (hr : r != 0)
  proof: SameRay.sameRay_comm.trans (sameRay_smul_right_iff_of_ne hv hr)

@[simp]

中文:
定理 sameRay_smul_left_iff_of_ne
  条件: {v : M} (hv : v != 0) {r : R} (hr : r != 0)
  证明: SameRay.sameRay_comm.trans (sameRay_smul_right_iff_of_ne hv hr)

@[simp]

Depends on / 依赖: SameRay, SameRay.sameRay_comm.trans, sameRay_comm, sameRay_smul_right_iff_of_ne
-/
theorem sameRay_smul_left_iff_of_ne {v : M} (hv : v != 0) {r : R} (hr : r != 0) :
    SameRay R (r • v) v ↔ 0 < r :=
  SameRay.sameRay_comm.trans (sameRay_smul_right_iff_of_ne hv hr)

@[simp]
/--
theorem `sameRay_neg_smul_right_iff` / 定理 `sameRay_neg_smul_right_iff`

English:
theorem sameRay_neg_smul_right_iff
  given: {v : M} {r : R}
  statement: SameRay R (-v) (r • v) ↔ r <= 0 ∨ v = 0
  proof: by
  rw [← sameRay_neg_iff]; rw [neg_neg]; rw [← neg_smul]; rw [sameRay_smul_right_iff]; rw [neg_nonneg]

中文:
定理 sameRay_neg_smul_right_iff
  条件: {v : M} {r : R}
  结论: SameRay R (-v) (r • v) ↔ r <= 0 ∨ v = 0
  证明: by
  rw [← sameRay_neg_iff]; rw [neg_neg]; rw [← neg_smul]; rw [sameRay_smul_right_iff]; rw [neg_nonneg]

Depends on / 依赖: neg_neg, neg_nonneg, neg_smul, sameRay_neg_iff, sameRay_smul_right_iff
-/
theorem sameRay_neg_smul_right_iff {v : M} {r : R} : SameRay R (-v) (r • v) ↔ r <= 0 ∨ v = 0 := by
  rw [← sameRay_neg_iff]; rw [neg_neg]; rw [← neg_smul]; rw [sameRay_smul_right_iff]; rw [neg_nonneg]

/--
theorem `sameRay_neg_smul_right_iff_of_ne` / 定理 `sameRay_neg_smul_right_iff_of_ne`

English:
theorem sameRay_neg_smul_right_iff_of_ne
  given: {v : M} {r : R} (hv : v != 0) (hr : r != 0)
  proof: by
  simp only [sameRay_neg_smul_right_iff, hv, or_false, hr.le_iff_lt]

@[simp]

中文:
定理 sameRay_neg_smul_right_iff_of_ne
  条件: {v : M} {r : R} (hv : v != 0) (hr : r != 0)
  证明: by
  simp only [sameRay_neg_smul_right_iff, hv, or_false, hr.le_iff_lt]

@[simp]

Depends on / 依赖: hr.le_iff_lt, le_iff_lt, or_false, sameRay_neg_smul_right_iff
-/
theorem sameRay_neg_smul_right_iff_of_ne {v : M} {r : R} (hv : v != 0) (hr : r != 0) :
    SameRay R (-v) (r • v) ↔ r < 0 := by
  simp only [sameRay_neg_smul_right_iff, hv, or_false, hr.le_iff_lt]

@[simp]
/--
theorem `sameRay_neg_smul_left_iff` / 定理 `sameRay_neg_smul_left_iff`

English:
theorem sameRay_neg_smul_left_iff
  given: {v : M} {r : R}
  statement: SameRay R (r • v) (-v) ↔ r <= 0 ∨ v = 0
  proof: SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff

中文:
定理 sameRay_neg_smul_left_iff
  条件: {v : M} {r : R}
  结论: SameRay R (r • v) (-v) ↔ r <= 0 ∨ v = 0
  证明: SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff

Depends on / 依赖: SameRay, SameRay.sameRay_comm.trans, sameRay_comm, sameRay_neg_smul_right_iff
-/
theorem sameRay_neg_smul_left_iff {v : M} {r : R} : SameRay R (r • v) (-v) ↔ r <= 0 ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff

/--
theorem `sameRay_neg_smul_left_iff_of_ne` / 定理 `sameRay_neg_smul_left_iff_of_ne`

English:
theorem sameRay_neg_smul_left_iff_of_ne
  given: {v : M} {r : R} (hv : v != 0) (hr : r != 0)
  proof: SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff_of_ne hv hr

@[simp]

中文:
定理 sameRay_neg_smul_left_iff_of_ne
  条件: {v : M} {r : R} (hv : v != 0) (hr : r != 0)
  证明: SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff_of_ne hv hr

@[simp]

Depends on / 依赖: SameRay, SameRay.sameRay_comm.trans, sameRay_comm, sameRay_neg_smul_right_iff_of_ne
-/
theorem sameRay_neg_smul_left_iff_of_ne {v : M} {r : R} (hv : v != 0) (hr : r != 0) :
    SameRay R (r • v) (-v) ↔ r < 0 :=
SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff_of_ne hv hr

@[simp]
/--
theorem `units_smul_eq_self_iff` / 定理 `units_smul_eq_self_iff`

English:
theorem units_smul_eq_self_iff
  given: {u : Rˣ} {v : Module.Ray R M}
  statement: u • v = v ↔ 0 < (u : R)
  proof: by
  induction v using Module.Ray.ind with | h v hv =>
  simp only [smul_rayOfNeZero, ray_eq_iff, Units.smul_def, sameRay_smul_left_iff_of_ne hv u.ne_zero]

@[simp]

中文:
定理 units_smul_eq_self_iff
  条件: {u : Rˣ} {v : 模.Ray R M}
  结论: u • v = v ↔ 0 < (u : R)
  证明: by
  induction v using Module.Ray.ind with | h v hv =>
  simp only [smul_rayOfNeZero, ray_eq_iff, Units.smul_def, sameRay_smul_left_iff_of_ne hv u.ne_zero]

@[simp]

Depends on / 依赖: Module, Module.Ray.ind, Units.smul_def, ne_zero, ray_eq_iff, sameRay_smul_left_iff_of_ne, smul_def, smul_rayOfNeZero, u.ne_zero
-/
theorem units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray R M} : u • v = v ↔ 0 < (u : R) := by
  induction v using Module.Ray.ind with | h v hv =>
  simp only [smul_rayOfNeZero, ray_eq_iff, Units.smul_def, sameRay_smul_left_iff_of_ne hv u.ne_zero]

@[simp]
/--
theorem `units_smul_eq_neg_iff` / 定理 `units_smul_eq_neg_iff`

English:
theorem units_smul_eq_neg_iff
  given: {u : Rˣ} {v : Module.Ray R M}
  statement: u • v = -v ↔ u.1 < 0
  proof: by
  rw [← neg_inj]; rw [neg_neg]; rw [← Module.Ray.neg_units_smul]; rw [units_smul_eq_self_iff]; rw [Units.val_neg]; rw [neg_pos]

中文:
定理 units_smul_eq_neg_iff
  条件: {u : Rˣ} {v : 模.Ray R M}
  结论: u • v = -v ↔ u.1 < 0
  证明: by
  rw [← neg_inj]; rw [neg_neg]; rw [← Module.Ray.neg_units_smul]; rw [units_smul_eq_self_iff]; rw [Units.val_neg]; rw [neg_pos]

Depends on / 依赖: Module, Module.Ray.neg_units_smul, Units.val_neg, neg_inj, neg_neg, neg_pos, neg_units_smul, units_smul_eq_self_iff, val_neg
-/
theorem units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R M} : u • v = -v ↔ u.1 < 0 := by
  rw [← neg_inj]; rw [neg_neg]; rw [← Module.Ray.neg_units_smul]; rw [units_smul_eq_self_iff]; rw [Units.val_neg]; rw [neg_pos]

/--
theorem `sameRay_or_sameRay_neg_iff_not_linearIndependent` / 定理 `sameRay_or_sameRay_neg_iff_not_linearIndependent`

English:
theorem sameRay_or_sameRay_neg_iff_not_linearIndependent
  given: {x y : M}
  proof: by
  by_cases hx : x = 0; · simpa [hx] using fun h : LinearIndependent R ![0, y] => h.ne_zero 0 rfl
  by_cases hy : y = 0; · simpa [hy] using fun h : LinearIndependent R ![x, 0] => h.ne_zero 1 rfl
  simp_rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ((hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩) | (hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩))
    · exact False.elim (hx hx0)
    · exact False.elim (hy hy0)
    · refine ⟨![r₁, -r₂], ?_⟩
      rw [Fin.sum_univ_two]; rw [Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
    · exact False.elim (hx hx0)
    · exact False.elim (hy (neg_eq_zero.1 hy0))
    · refine ⟨![r₁, r₂], ?_⟩
      rw [Fin.sum_univ_two]; rw [Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
  · rcases h with ⟨m, hm, hmne⟩
    rw [Fin.sum_univ_two]; rw [add_eq_zero_iff_eq_neg] at hm
    dsimp only [Matrix.cons_val] at hm
    rcases lt_trichotomy (m 0) 0 with (hm0 | hm0 | hm0) <;>
      rcases lt_trichotomy (m 1) 0 with (hm1 | hm1 | hm1)
    · refine
        Or.inr (Or.inr (Or.inr ⟨-m 0, -m 1, Left.neg_pos_iff.2 hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm1, hx, hm0.ne] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨-m 0, m 1, Left.neg_pos_iff.2 hm0, hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm0, hy, hm1.ne] at hm
    · rw [Fin.exists_fin_two] at hmne
      exact False.elim (not_and_or.2 hmne ⟨hm0, hm1⟩)
    · exfalso
      simp [hm0, hy, hm1.ne.symm] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨m 0, -m 1, hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      rwa [neg_smul]
    · exfalso
      simp [hm1, hx, hm0.ne.symm] at hm
    · refine Or.inr (Or.inr (Or.inr ⟨m 0, m 1, hm0, hm1, ?_⟩))
      rwa [smul_neg]

中文:
定理 sameRay_or_sameRay_neg_iff_not_linearIndependent
  条件: {x y : M}
  证明: by
  by_cases hx : x = 0; · simpa [hx] using fun h : LinearIndependent R ![0, y] => h.ne_zero 0 rfl
  by_cases hy : y = 0; · simpa [hy] using fun h : LinearIndependent R ![x, 0] => h.ne_zero 1 rfl
  simp_rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ((hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩) | (hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩))
    · exact False.elim (hx hx0)
    · exact False.elim (hy hy0)
    · refine ⟨![r₁, -r₂], ?_⟩
      rw [Fin.sum_univ_two]; rw [Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
    · exact False.elim (hx hx0)
    · exact False.elim (hy (neg_eq_zero.1 hy0))
    · refine ⟨![r₁, r₂], ?_⟩
      rw [Fin.sum_univ_two]; rw [Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
  · rcases h with ⟨m, hm, hmne⟩
    rw [Fin.sum_univ_two]; rw [add_eq_zero_iff_eq_neg] at hm
    dsimp only [Matrix.cons_val] at hm
    rcases lt_trichotomy (m 0) 0 with (hm0 | hm0 | hm0) <;>
      rcases lt_trichotomy (m 1) 0 with (hm1 | hm1 | hm1)
    · refine
        Or.inr (Or.inr (Or.inr ⟨-m 0, -m 1, Left.neg_pos_iff.2 hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm1, hx, hm0.ne] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨-m 0, m 1, Left.neg_pos_iff.2 hm0, hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm0, hy, hm1.ne] at hm
    · rw [Fin.exists_fin_two] at hmne
      exact False.elim (not_and_or.2 hmne ⟨hm0, hm1⟩)
    · exfalso
      simp [hm0, hy, hm1.ne.symm] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨m 0, -m 1, hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      rwa [neg_smul]
    · exfalso
      simp [hm1, hx, hm0.ne.symm] at hm
    · refine Or.inr (Or.inr (Or.inr ⟨m 0, m 1, hm0, hm1, ?_⟩))
      rwa [smul_neg]

Depends on / 依赖: False.elim, Fin.exists_fin_two, Fin.sum_univ_two, Fintype, Fintype.not_linearIndependent_iff, LinearIndependent, exists_fin_two, h.ne_zero, ne_zero, not_linearIndependent_iff, simp_rw, sum_univ_two
-/
theorem sameRay_or_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  by_cases hx : x = 0; · simpa [hx] using fun h : LinearIndependent R ![0, y] => h.ne_zero 0 rfl
  by_cases hy : y = 0; · simpa [hy] using fun h : LinearIndependent R ![x, 0] => h.ne_zero 1 rfl
  simp_rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ((hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩) | (hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩))
    · exact False.elim (hx hx0)
    · exact False.elim (hy hy0)
    · refine ⟨![r₁, -r₂], ?_⟩
      rw [Fin.sum_univ_two]; rw [Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
    · exact False.elim (hx hx0)
    · exact False.elim (hy (neg_eq_zero.1 hy0))
    · refine ⟨![r₁, r₂], ?_⟩
      rw [Fin.sum_univ_two]; rw [Fin.exists_fin_two]
      simp [h, hr₁.ne.symm]
  · rcases h with ⟨m, hm, hmne⟩
    rw [Fin.sum_univ_two]; rw [add_eq_zero_iff_eq_neg] at hm
    dsimp only [Matrix.cons_val] at hm
    rcases lt_trichotomy (m 0) 0 with (hm0 | hm0 | hm0) <;>
      rcases lt_trichotomy (m 1) 0 with (hm1 | hm1 | hm1)
    · refine
        Or.inr (Or.inr (Or.inr ⟨-m 0, -m 1, Left.neg_pos_iff.2 hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm1, hx, hm0.ne] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨-m 0, m 1, Left.neg_pos_iff.2 hm0, hm1, ?_⟩))
      linear_combination (norm := module) -hm
    · exfalso
      simp [hm0, hy, hm1.ne] at hm
    · rw [Fin.exists_fin_two] at hmne
      exact False.elim (not_and_or.2 hmne ⟨hm0, hm1⟩)
    · exfalso
      simp [hm0, hy, hm1.ne.symm] at hm
    · refine Or.inl (Or.inr (Or.inr ⟨m 0, -m 1, hm0, Left.neg_pos_iff.2 hm1, ?_⟩))
      rwa [neg_smul]
    · exfalso
      simp [hm1, hx, hm0.ne.symm] at hm
    · refine Or.inr (Or.inr (Or.inr ⟨m 0, m 1, hm0, hm1, ?_⟩))
      rwa [smul_neg]

/--
theorem `sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent` / 定理 `sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent`

English:
theorem sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent
  given: {x y : M}
  proof: by
  rw [← sameRay_or_sameRay_neg_iff_not_linearIndependent]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0 <;> simp [hx, hy]

中文:
定理 sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent
  条件: {x y : M}
  证明: by
  rw [← sameRay_or_sameRay_neg_iff_not_linearIndependent]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0 <;> simp [hx, hy]

Depends on / 依赖: sameRay_or_sameRay_neg_iff_not_linearIndependent
-/
theorem sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ x != 0 ∧ y != 0 ∧ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  rw [← sameRay_or_sameRay_neg_iff_not_linearIndependent]
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0 <;> simp [hx, hy]

end

end LinearOrderedCommRing

namespace SameRay

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] {x y v₁ v₂ : M}

/--
theorem `exists_pos_left` / 定理 `exists_pos_left`

English:
theorem exists_pos_left
  given: (h : SameRay R x y) (hx : x != 0) (hy : y != 0)
  proof: let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩

中文:
定理 存在_pos_left
  条件: (h : SameRay R x y) (hx : x != 0) (hy : y != 0)
  证明: let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩

Depends on / 依赖: exists_pos, h.exists_pos, inv_pos, mul_pos, mul_smul
-/
theorem exists_pos_left (h : SameRay R x y) (hx : x != 0) (hy : y != 0) :
    exists r : R, 0 < r ∧ r • x = y :=
  let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩

/--
theorem `exists_pos_right` / 定理 `exists_pos_right`

English:
theorem exists_pos_right
  given: (h : SameRay R x y) (hx : x != 0) (hy : y != 0)
  proof: (h.symm.exists_pos_left hy hx).imp fun _ => And.imp_right Eq.symm

中文:
定理 存在_pos_right
  条件: (h : SameRay R x y) (hx : x != 0) (hy : y != 0)
  证明: (h.symm.exists_pos_left hy hx).imp fun _ => And.imp_right Eq.symm

Depends on / 依赖: And.imp_right, Eq.symm, exists_pos_left, h.symm.exists_pos_left, imp_right
-/
theorem exists_pos_right (h : SameRay R x y) (hx : x != 0) (hy : y != 0) :
    exists r : R, 0 < r ∧ x = r • y :=
  (h.symm.exists_pos_left hy hx).imp fun _ => And.imp_right Eq.symm

/--
theorem `exists_nonneg_left` / 定理 `exists_nonneg_left`

English:
theorem exists_nonneg_left
  given: (h : SameRay R x y) (hx : x != 0)
  statement: exists r : R, 0 <= r ∧ r • x = y
  proof: by
  obtain rfl | hy := eq_or_ne y 0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
  · exact (h.exists_pos_left hx hy).imp fun _ => And.imp_left le_of_lt

中文:
定理 存在_nonneg_left
  条件: (h : SameRay R x y) (hx : x != 0)
  结论: 存在 r : R, 0 <= r ∧ r • x = y
  证明: by
  obtain rfl | hy := eq_or_ne y 0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
  · exact (h.exists_pos_left hx hy).imp fun _ => And.imp_left le_of_lt

Depends on / 依赖: And.imp_left, eq_or_ne, exists_pos_left, h.exists_pos_left, imp_left, le_of_lt, le_rfl, zero_smul
-/
theorem exists_nonneg_left (h : SameRay R x y) (hx : x != 0) : exists r : R, 0 <= r ∧ r • x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
  · exact (h.exists_pos_left hx hy).imp fun _ => And.imp_left le_of_lt

/--
theorem `exists_nonneg_right` / 定理 `exists_nonneg_right`

English:
theorem exists_nonneg_right
  given: (h : SameRay R x y) (hy : y != 0)
  statement: exists r : R, 0 <= r ∧ x = r • y
  proof: (h.symm.exists_nonneg_left hy).imp fun _ => And.imp_right Eq.symm

中文:
定理 存在_nonneg_right
  条件: (h : SameRay R x y) (hy : y != 0)
  结论: 存在 r : R, 0 <= r ∧ x = r • y
  证明: (h.symm.exists_nonneg_left hy).imp fun _ => And.imp_right Eq.symm

Depends on / 依赖: And.imp_right, Eq.symm, exists_nonneg_left, h.symm.exists_nonneg_left, imp_right
-/
theorem exists_nonneg_right (h : SameRay R x y) (hy : y != 0) : exists r : R, 0 <= r ∧ x = r • y :=
  (h.symm.exists_nonneg_left hy).imp fun _ => And.imp_right Eq.symm

/--
theorem `exists_eq_smul_add` / 定理 `exists_eq_smul_add`

English:
theorem exists_eq_smul_add
  given: (h : SameRay R v₁ v₂)
  proof: by
  rcases h with (rfl | rfl | ⟨r₁, r₂, h₁, h₂, H⟩)
  · use 0, 1
    simp
  · use 1, 0
    simp
  · have h₁₂ : 0 < r₁ + r₂ := add_pos h₁ h₂
    refine
      ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le, ?_, ?_, ?_⟩
    · rw [← add_div, add_comm, div_self h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']

中文:
定理 存在_eq_smul_add
  条件: (h : SameRay R v₁ v₂)
  证明: by
  rcases h with (rfl | rfl | ⟨r₁, r₂, h₁, h₂, H⟩)
  · use 0, 1
    simp
  · use 1, 0
    simp
  · have h₁₂ : 0 < r₁ + r₂ := add_pos h₁ h₂
    refine
      ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le, ?_, ?_, ?_⟩
    · rw [← add_div, add_comm, div_self h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']

Depends on / 依赖: add_comm, add_div, add_pos, add_smul, div_eq_inv_mul, div_nonneg, div_self, mul_smul, smul_add
-/
theorem exists_eq_smul_add (h : SameRay R v₁ v₂) :
    exists a b : R, 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂) := by
  rcases h with (rfl | rfl | ⟨r₁, r₂, h₁, h₂, H⟩)
  · use 0, 1
    simp
  · use 1, 0
    simp
  · have h₁₂ : 0 < r₁ + r₂ := add_pos h₁ h₂
    refine
      ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le, ?_, ?_, ?_⟩
    · rw [← add_div, add_comm, div_self h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
    · rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']

/--
theorem `exists_eq_smul` / 定理 `exists_eq_smul`

English:
theorem exists_eq_smul
  given: (h : SameRay R v₁ v₂)
  proof: ⟨v₁ + v₂, h.exists_eq_smul_add⟩

中文:
定理 存在_eq_smul
  条件: (h : SameRay R v₁ v₂)
  证明: ⟨v₁ + v₂, h.exists_eq_smul_add⟩

Depends on / 依赖: exists_eq_smul_add, h.exists_eq_smul_add
-/
theorem exists_eq_smul (h : SameRay R v₁ v₂) :
    exists (u : M) (a b : R), 0 <= a ∧ 0 <= b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u :=
  ⟨v₁ + v₂, h.exists_eq_smul_add⟩

end SameRay

section LinearOrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] {x y : M}

/--
theorem `exists_pos_left_iff_sameRay` / 定理 `exists_pos_left_iff_sameRay`

English:
theorem exists_pos_left_iff_sameRay
  given: (hx : x != 0) (hy : y != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => h.exists_pos_left hx hy⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_pos_smul_right x hr

中文:
定理 存在_pos_left_iff_sameRay
  条件: (hx : x != 0) (hy : y != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => h.exists_pos_left hx hy⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_pos_smul_right x hr

Depends on / 依赖: SameRay, SameRay.sameRay_pos_smul_right, exists_pos_left, h.exists_pos_left, sameRay_pos_smul_right
-/
theorem exists_pos_left_iff_sameRay (hx : x != 0) (hy : y != 0) :
    (exists r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y := by
  refine ⟨fun h => ?_, fun h => h.exists_pos_left hx hy⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_pos_smul_right x hr

/--
theorem `exists_pos_left_iff_sameRay_and_ne_zero` / 定理 `exists_pos_left_iff_sameRay_and_ne_zero`

English:
theorem exists_pos_left_iff_sameRay_and_ne_zero
  given: (hx : x != 0)
  proof: by
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp [hx, hr.le, hr.ne']
  · rintro ⟨hxy, hy⟩
    exact (exists_pos_left_iff_sameRay hx hy).2 hxy

中文:
定理 存在_pos_left_iff_sameRay_and_ne_zero
  条件: (hx : x != 0)
  证明: by
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp [hx, hr.le, hr.ne']
  · rintro ⟨hxy, hy⟩
    exact (exists_pos_left_iff_sameRay hx hy).2 hxy

Depends on / 依赖: exists_pos_left_iff_sameRay, hr.le, hr.ne
-/
theorem exists_pos_left_iff_sameRay_and_ne_zero (hx : x != 0) :
    (exists r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y ∧ y != 0 := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp [hx, hr.le, hr.ne']
  · rintro ⟨hxy, hy⟩
    exact (exists_pos_left_iff_sameRay hx hy).2 hxy

/--
theorem `exists_nonneg_left_iff_sameRay` / 定理 `exists_nonneg_left_iff_sameRay`

English:
theorem exists_nonneg_left_iff_sameRay
  given: (hx : x != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => h.exists_nonneg_left hx⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_nonneg_smul_right x hr

中文:
定理 存在_nonneg_left_iff_sameRay
  条件: (hx : x != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => h.exists_nonneg_left hx⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_nonneg_smul_right x hr

Depends on / 依赖: SameRay, SameRay.sameRay_nonneg_smul_right, exists_nonneg_left, h.exists_nonneg_left, sameRay_nonneg_smul_right
-/
theorem exists_nonneg_left_iff_sameRay (hx : x != 0) :
    (exists r : R, 0 <= r ∧ r • x = y) ↔ SameRay R x y := by
  refine ⟨fun h => ?_, fun h => h.exists_nonneg_left hx⟩
  rcases h with ⟨r, hr, rfl⟩
  exact SameRay.sameRay_nonneg_smul_right x hr

/--
theorem `exists_pos_right_iff_sameRay` / 定理 `exists_pos_right_iff_sameRay`

English:
theorem exists_pos_right_iff_sameRay
  given: (hx : x != 0) (hy : y != 0)
  proof: by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay hy hx

中文:
定理 存在_pos_right_iff_sameRay
  条件: (hx : x != 0) (hy : y != 0)
  证明: by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay hy hx

Depends on / 依赖: SameRay, SameRay.sameRay_comm, eq_comm, exists_pos_left_iff_sameRay, sameRay_comm, simp_rw
-/
theorem exists_pos_right_iff_sameRay (hx : x != 0) (hy : y != 0) :
    (exists r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay hy hx

/--
theorem `exists_pos_right_iff_sameRay_and_ne_zero` / 定理 `exists_pos_right_iff_sameRay_and_ne_zero`

English:
theorem exists_pos_right_iff_sameRay_and_ne_zero
  given: (hy : y != 0)
  proof: by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay_and_ne_zero hy

中文:
定理 存在_pos_right_iff_sameRay_and_ne_zero
  条件: (hy : y != 0)
  证明: by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay_and_ne_zero hy

Depends on / 依赖: SameRay, SameRay.sameRay_comm, eq_comm, exists_pos_left_iff_sameRay_and_ne_zero, sameRay_comm, simp_rw
-/
theorem exists_pos_right_iff_sameRay_and_ne_zero (hy : y != 0) :
    (exists r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y ∧ x != 0 := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_pos_left_iff_sameRay_and_ne_zero hy

/--
theorem `exists_nonneg_right_iff_sameRay` / 定理 `exists_nonneg_right_iff_sameRay`

English:
theorem exists_nonneg_right_iff_sameRay
  given: (hy : y != 0)
  proof: by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_nonneg_left_iff_sameRay (R := R) hy

中文:
定理 存在_nonneg_right_iff_sameRay
  条件: (hy : y != 0)
  证明: by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_nonneg_left_iff_sameRay (R := R) hy

Depends on / 依赖: SameRay, SameRay.sameRay_comm, eq_comm, exists_nonneg_left_iff_sameRay, sameRay_comm, simp_rw
-/
theorem exists_nonneg_right_iff_sameRay (hy : y != 0) :
    (exists r : R, 0 <= r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  simp_rw [eq_comm (a := x)]
  exact exists_nonneg_left_iff_sameRay (R := R) hy

end LinearOrderedField
