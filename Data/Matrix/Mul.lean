/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Matrix multiplication

This file defines vector and matrix multiplication

## Main definitions
* `dotProduct`: the dot product between two vectors
* `Matrix.mul`: multiplication of two matrices
* `Matrix.mulVec`: multiplication of a matrix with a vector
* `Matrix.vecMul`: multiplication of a vector with a matrix
* `Matrix.vecMulVec`: multiplication of a vector with a vector to get a matrix
* `Matrix.instRing`: square matrices form a ring

## Notation

The scope `Matrix` gives the following notation:

* `⬝ᵥ` for `dotProduct`
* `*ᵥ` for `Matrix.mulVec`
* `ᵥ*` for `Matrix.vecMul`

See `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.

## TODO

Under various conditions, multiplication of infinite matrices makes sense.
These have not yet been implemented.
-/

@[expose] public section

assert_not_exists Algebra Field TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o -> Type*} {n' : o -> Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

open Matrix

section DotProduct

variable [Fintype m] [Fintype n]

/--
Definition of `dotProduct` / `dotProduct` 的定义

English:
definition dotProduct
  signature: [Mul α] [AddCommMonoid α] (v w : m -> α)
  body: ∑ i, v i * w i

中文:
定义 dotProduct
  签名: [乘法 α] [加法交换幺半群 α] (v w : m -> α)
  定义体: ∑ i, v i * w i
-/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m -> α) : α :=
  ∑ i, v i * w i

/- The precedence of 72 comes immediately after ` • ` for `SMul.smul`,
so that `r₁ • a ⬝ᵥ r₂ • b` is parsed as `(r₁ • a) ⬝ᵥ (r₂ • b)` here. -/
@[inherit_doc]
infixl:72 " ⬝ᵥ " => dotProduct

/--
theorem `dotProduct_assoc` / 定理 `dotProduct_assoc`

English:
theorem dotProduct_assoc
  given: [NonUnitalSemiring α] (u : m -> α) (w : n -> α) (v : Matrix m n α)
  proof: by
  simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm

中文:
定理 dotProduct_assoc
  条件: [非幺半环 α] (u : m -> α) (w : n -> α) (v : 矩阵 m n α)
  证明: by
  simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_comm, Finset.sum_mul, dotProduct, mul_assoc, mul_sum, sum_comm, sum_mul
-/
theorem dotProduct_assoc [NonUnitalSemiring α] (u : m -> α) (w : n -> α) (v : Matrix m n α) :
    (fun j => u ⬝ᵥ fun i => v i j) ⬝ᵥ w = u ⬝ᵥ fun i => v i ⬝ᵥ w := by
  simpa [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc] using Finset.sum_comm

/--
theorem `dotProduct_comm` / 定理 `dotProduct_comm`

English:
theorem dotProduct_comm
  given: [AddCommMonoid α] [CommMagma α] (v w : m -> α)
  statement: v ⬝ᵥ w = w ⬝ᵥ v
  proof: by
  simp_rw [dotProduct, mul_comm]

@[simp]

中文:
定理 dotProduct_comm
  条件: [加法交换幺半群 α] [交换原群 α] (v w : m -> α)
  结论: v ⬝ᵥ w = w ⬝ᵥ v
  证明: by
  simp_rw [dotProduct, mul_comm]

@[simp]

Depends on / 依赖: dotProduct, mul_comm, simp_rw
-/
theorem dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : m -> α) : v ⬝ᵥ w = w ⬝ᵥ v := by
  simp_rw [dotProduct, mul_comm]

@[simp]
/--
theorem `dotProduct_pUnit` / 定理 `dotProduct_pUnit`

English:
theorem dotProduct_pUnit
  given: [AddCommMonoid α] [Mul α] (v w : PUnit -> α)
  statement: v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩
  proof: by
  simp [dotProduct]

中文:
定理 dotProduct_pUnit
  条件: [加法交换幺半群 α] [乘法 α] (v w : 命题单元 -> α)
  结论: v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩
  证明: by
  simp [dotProduct]

Depends on / 依赖: dotProduct
-/
theorem dotProduct_pUnit [AddCommMonoid α] [Mul α] (v w : PUnit -> α) : v ⬝ᵥ w = v ⟨⟩ * w ⟨⟩ := by
  simp [dotProduct]

section MulOneClass

variable [MulOneClass α] [AddCommMonoid α]

/--
theorem `dotProduct_one` / 定理 `dotProduct_one`

English:
theorem dotProduct_one
  given: (v : n -> α)
  statement: v ⬝ᵥ 1 = ∑ i, v i
  proof: by simp [(· ⬝ᵥ ·)]

中文:
定理 dotProduct_one
  条件: (v : n -> α)
  结论: v ⬝ᵥ 1 = ∑ i, v i
  证明: by simp [(· ⬝ᵥ ·)]
-/
theorem dotProduct_one (v : n -> α) : v ⬝ᵥ 1 = ∑ i, v i := by simp [(· ⬝ᵥ ·)]

/--
theorem `one_dotProduct` / 定理 `one_dotProduct`

English:
theorem one_dotProduct
  given: (v : n -> α)
  statement: 1 ⬝ᵥ v = ∑ i, v i
  proof: by simp [(· ⬝ᵥ ·)]

中文:
定理 one_dotProduct
  条件: (v : n -> α)
  结论: 1 ⬝ᵥ v = ∑ i, v i
  证明: by simp [(· ⬝ᵥ ·)]
-/
theorem one_dotProduct (v : n -> α) : 1 ⬝ᵥ v = ∑ i, v i := by simp [(· ⬝ᵥ ·)]

end MulOneClass

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] (u v w : m -> α) (x y : n -> α)

@[simp]
/--
theorem `dotProduct_zero` / 定理 `dotProduct_zero`

English:
theorem dotProduct_zero
  statement: v ⬝ᵥ 0 = 0
  proof: by simp [dotProduct]

@[simp]

中文:
定理 dotProduct_zero
  结论: v ⬝ᵥ 0 = 0
  证明: by simp [dotProduct]

@[simp]

Depends on / 依赖: dotProduct
-/
theorem dotProduct_zero : v ⬝ᵥ 0 = 0 := by simp [dotProduct]

@[simp]
/--
theorem `dotProduct_zero'` / 定理 `dotProduct_zero'`

English:
theorem dotProduct_zero'
  statement: (v ⬝ᵥ fun _ => 0) = 0
  proof: dotProduct_zero v

@[simp]

中文:
定理 dotProduct_zero'
  结论: (v ⬝ᵥ fun _ => 0) = 0
  证明: dotProduct_zero v

@[simp]

Depends on / 依赖: dotProduct_zero
-/
theorem dotProduct_zero' : (v ⬝ᵥ fun _ => 0) = 0 :=
  dotProduct_zero v

@[simp]
/--
theorem `zero_dotProduct` / 定理 `zero_dotProduct`

English:
theorem zero_dotProduct
  statement: 0 ⬝ᵥ v = 0
  proof: by simp [dotProduct]

@[simp]

中文:
定理 zero_dotProduct
  结论: 0 ⬝ᵥ v = 0
  证明: by simp [dotProduct]

@[simp]

Depends on / 依赖: dotProduct
-/
theorem zero_dotProduct : 0 ⬝ᵥ v = 0 := by simp [dotProduct]

@[simp]
/--
theorem `zero_dotProduct'` / 定理 `zero_dotProduct'`

English:
theorem zero_dotProduct'
  statement: (fun _ => (0 : α)) ⬝ᵥ v = 0
  proof: zero_dotProduct v

@[simp]

中文:
定理 zero_dotProduct'
  结论: (fun _ => (0 : α)) ⬝ᵥ v = 0
  证明: zero_dotProduct v

@[simp]

Depends on / 依赖: zero_dotProduct
-/
theorem zero_dotProduct' : (fun _ => (0 : α)) ⬝ᵥ v = 0 :=
  zero_dotProduct v

@[simp]
/--
theorem `add_dotProduct` / 定理 `add_dotProduct`

English:
theorem add_dotProduct
  statement: (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
  proof: by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

@[simp]

中文:
定理 add_dotProduct
  结论: (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w
  证明: by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, add_mul, dotProduct, sum_add_distrib
-/
theorem add_dotProduct : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

@[simp]
/--
theorem `dotProduct_add` / 定理 `dotProduct_add`

English:
theorem dotProduct_add
  statement: u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w
  proof: by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

@[simp]

中文:
定理 dotProduct_add
  结论: u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w
  证明: by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

@[simp]

Depends on / 依赖: Finset, Finset.sum_add_distrib, dotProduct, mul_add, sum_add_distrib
-/
theorem dotProduct_add : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

@[simp]
/--
theorem `sumElim_dotProduct_sumElim` / 定理 `sumElim_dotProduct_sumElim`

English:
theorem sumElim_dotProduct_sumElim
  statement: Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y
  proof: by
  simp [dotProduct]

中文:
定理 sumElim_dotProduct_sumElim
  结论: 和.elim u x ⬝ᵥ 和.elim v y = u ⬝ᵥ v + x ⬝ᵥ y
  证明: by
  simp [dotProduct]

Depends on / 依赖: dotProduct
-/
theorem sumElim_dotProduct_sumElim : Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct]

/-- Permuting a vector on the left of a dot product can be transferred to the right. -/
@[simp]
/--
theorem `comp_equiv_symm_dotProduct` / 定理 `comp_equiv_symm_dotProduct`

English:
theorem comp_equiv_symm_dotProduct
  given: (e : m ≃ n)
  statement: u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e
  proof: (e.sum_comp _).symm.trans
    Finset.sum_congr rfl fun _ _ => by simp only [Function.comp, Equiv.symm_apply_apply]

中文:
定理 comp_equiv_symm_dotProduct
  条件: (e : m ≃ n)
  结论: u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e
  证明: (e.sum_comp _).symm.trans
    Finset.sum_congr rfl fun _ _ => by simp only [Function.comp, Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.symm_apply_apply, Finset, Finset.sum_congr, Function, Function.comp, e.sum_comp, sum_comp, sum_congr, symm.trans, symm_apply_apply
-/
theorem comp_equiv_symm_dotProduct (e : m ≃ n) : u ∘ e.symm ⬝ᵥ x = u ⬝ᵥ x ∘ e :=
(e.sum_comp _).symm.trans
    Finset.sum_congr rfl fun _ _ => by simp only [Function.comp, Equiv.symm_apply_apply]

/-- Permuting a vector on the right of a dot product can be transferred to the left. -/
@[simp]
/--
theorem `dotProduct_comp_equiv_symm` / 定理 `dotProduct_comp_equiv_symm`

English:
theorem dotProduct_comp_equiv_symm
  given: (e : n ≃ m)
  statement: u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x
  proof: by
  simpa only [Equiv.symm_symm] using (comp_equiv_symm_dotProduct u x e.symm).symm

中文:
定理 dotProduct_comp_equiv_symm
  条件: (e : n ≃ m)
  结论: u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x
  证明: by
  simpa only [Equiv.symm_symm] using (comp_equiv_symm_dotProduct u x e.symm).symm

Depends on / 依赖: Equiv.symm_symm, comp_equiv_symm_dotProduct, e.symm, symm_symm
-/
theorem dotProduct_comp_equiv_symm (e : n ≃ m) : u ⬝ᵥ x ∘ e.symm = u ∘ e ⬝ᵥ x := by
  simpa only [Equiv.symm_symm] using (comp_equiv_symm_dotProduct u x e.symm).symm

/-- Permuting vectors on both sides of a dot product is a no-op. -/
@[simp]
/--
theorem `comp_equiv_dotProduct_comp_equiv` / 定理 `comp_equiv_dotProduct_comp_equiv`

English:
theorem comp_equiv_dotProduct_comp_equiv
  given: (e : m ≃ n)
  statement: x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y
  proof: by
  simp [← dotProduct_comp_equiv_symm, Function.comp_def _ e.symm]

中文:
定理 comp_equiv_dotProduct_comp_equiv
  条件: (e : m ≃ n)
  结论: x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y
  证明: by
  simp [← dotProduct_comp_equiv_symm, Function.comp_def _ e.symm]

Depends on / 依赖: Function, Function.comp_def, comp_def, dotProduct_comp_equiv_symm, e.symm
-/
theorem comp_equiv_dotProduct_comp_equiv (e : m ≃ n) : x ∘ e ⬝ᵥ y ∘ e = x ⬝ᵥ y := by
  simp [← dotProduct_comp_equiv_symm, Function.comp_def _ e.symm]

/--
theorem `dotProduct_sum` / 定理 `dotProduct_sum`

English:
theorem dotProduct_sum
  given: {ι : Type*} (u : m -> α) (s : Finset ι) (v : ι -> (m -> α))
  proof: by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

中文:
定理 dotProduct_sum
  条件: {ι : 类型} (u : m -> α) (s : 有限集 ι) (v : ι -> (m -> α))
  证明: by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_apply, Finset.sum_comm, dotProduct, mul_sum, sum_apply, sum_comm
-/
theorem dotProduct_sum {ι : Type*} (u : m -> α) (s : Finset ι) (v : ι -> (m -> α)) :
    u ⬝ᵥ ∑ i in s, v i = ∑ i in s, u ⬝ᵥ v i := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/--
theorem `sum_dotProduct` / 定理 `sum_dotProduct`

English:
theorem sum_dotProduct
  given: {ι : Type*} (s : Finset ι) (u : ι -> (m -> α)) (v : m -> α)
  proof: by
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

中文:
定理 sum_dotProduct
  条件: {ι : 类型} (s : 有限集 ι) (u : ι -> (m -> α)) (v : m -> α)
  证明: by
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_comm, Finset.sum_mul, dotProduct, sum_apply, sum_comm, sum_mul
-/
theorem sum_dotProduct {ι : Type*} (s : Finset ι) (u : ι -> (m -> α)) (v : m -> α) :
    (∑ i in s, u i) ⬝ᵥ v = ∑ i in s, u i ⬝ᵥ v := by
  simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocSemiringDecidable

variable [DecidableEq m] [NonUnitalNonAssocSemiring α] (u v w : m -> α)

@[simp]
/--
theorem `diagonal_dotProduct` / 定理 `diagonal_dotProduct`

English:
theorem diagonal_dotProduct
  given: (i : m)
  statement: diagonal v i ⬝ᵥ w = v i * w i
  proof: by
  have : forall j != i, diagonal v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp


@[simp]

中文:
定理 diagonal_dotProduct
  条件: (i : m)
  结论: diagonal v i ⬝ᵥ w = v i * w i
  证明: by
  have : forall j != i, diagonal v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp


@[simp]

Depends on / 依赖: Finset, Finset.sum_eq_single, convert, diagonal, diagonal_apply_ne, sum_eq_single
-/
theorem diagonal_dotProduct (i : m) : diagonal v i ⬝ᵥ w = v i * w i := by
  have : forall j != i, diagonal v i j * w j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp


@[simp]
/--
theorem `dotProduct_diagonal` / 定理 `dotProduct_diagonal`

English:
theorem dotProduct_diagonal
  given: (i : m)
  statement: v ⬝ᵥ diagonal w i = v i * w i
  proof: by
  have : forall j != i, v j * diagonal w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]

中文:
定理 dotProduct_diagonal
  条件: (i : m)
  结论: v ⬝ᵥ diagonal w i = v i * w i
  证明: by
  have : forall j != i, v j * diagonal w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]

Depends on / 依赖: Finset, Finset.sum_eq_single, convert, diagonal, diagonal_apply_ne, sum_eq_single
-/
theorem dotProduct_diagonal (i : m) : v ⬝ᵥ diagonal w i = v i * w i := by
  have : forall j != i, v j * diagonal w i j = 0 := fun j hij => by
    simp [diagonal_apply_ne' _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
/--
theorem `dotProduct_diagonal'` / 定理 `dotProduct_diagonal'`

English:
theorem dotProduct_diagonal'
  given: (i : m)
  statement: (v ⬝ᵥ fun j => diagonal w j i) = v i * w i
  proof: by
  have : forall j != i, v j * diagonal w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]

中文:
定理 dotProduct_diagonal'
  条件: (i : m)
  结论: (v ⬝ᵥ fun j => diagonal w j i) = v i * w i
  证明: by
  have : forall j != i, v j * diagonal w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]

Depends on / 依赖: Finset, Finset.sum_eq_single, convert, diagonal, diagonal_apply_ne, sum_eq_single
-/
theorem dotProduct_diagonal' (i : m) : (v ⬝ᵥ fun j => diagonal w j i) = v i * w i := by
  have : forall j != i, v j * diagonal w j i = 0 := fun j hij => by
    simp [diagonal_apply_ne _ hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
/--
theorem `single_dotProduct` / 定理 `single_dotProduct`

English:
theorem single_dotProduct
  given: (x : α) (i : m)
  statement: Pi.single i x ⬝ᵥ v = x * v i
  proof: by

中文:
定理 single_dotProduct
  条件: (x : α) (i : m)
  结论: 依赖函数类型.single i x ⬝ᵥ v = x * v i
  证明: by
-/
theorem single_dotProduct (x : α) (i : m) : Pi.single i x ⬝ᵥ v = x * v i := by
-- Porting note: added `(_ : m → α)`
  have : forall j != i, (Pi.single i x : m -> α) j * v j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

@[simp]
/--
theorem `dotProduct_single` / 定理 `dotProduct_single`

English:
theorem dotProduct_single
  given: (x : α) (i : m)
  statement: v ⬝ᵥ Pi.single i x = v i * x
  proof: by

中文:
定理 dotProduct_single
  条件: (x : α) (i : m)
  结论: v ⬝ᵥ 依赖函数类型.single i x = v i * x
  证明: by
-/
theorem dotProduct_single (x : α) (i : m) : v ⬝ᵥ Pi.single i x = v i * x := by
-- Porting note: added `(_ : m → α)`
  have : forall j != i, v j * (Pi.single i x : m -> α) j = 0 := fun j hij => by
    simp [Pi.single_eq_of_ne hij]
  convert! Finset.sum_eq_single i (fun j _ => this j) _ using 1 <;> simp

end NonUnitalNonAssocSemiringDecidable

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
/--
theorem `one_dotProduct_one` / 定理 `one_dotProduct_one`

English:
theorem one_dotProduct_one
  statement: (1 : n -> α) ⬝ᵥ 1 = Fintype.card n
  proof: by
  simp [dotProduct]

中文:
定理 one_dotProduct_one
  结论: (1 : n -> α) ⬝ᵥ 1 = 有限类型.card n
  证明: by
  simp [dotProduct]

Depends on / 依赖: dotProduct
-/
theorem one_dotProduct_one : (1 : n -> α) ⬝ᵥ 1 = Fintype.card n := by
  simp [dotProduct]

/--
theorem `dotProduct_single_one` / 定理 `dotProduct_single_one`

English:
theorem dotProduct_single_one
  given: [DecidableEq n] (v : n -> α) (i : n)
  proof: by
  rw [dotProduct_single]; rw [mul_one]

中文:
定理 dotProduct_single_one
  条件: [DecidableEq n] (v : n -> α) (i : n)
  证明: by
  rw [dotProduct_single]; rw [mul_one]

Depends on / 依赖: dotProduct_single, mul_one
-/
theorem dotProduct_single_one [DecidableEq n] (v : n -> α) (i : n) :
    v ⬝ᵥ Pi.single i 1 = v i := by
  rw [dotProduct_single]; rw [mul_one]

/--
theorem `single_one_dotProduct` / 定理 `single_one_dotProduct`

English:
theorem single_one_dotProduct
  given: [DecidableEq n] (i : n) (v : n -> α)
  proof: by
  rw [single_dotProduct]; rw [one_mul]

中文:
定理 single_one_dotProduct
  条件: [DecidableEq n] (i : n) (v : n -> α)
  证明: by
  rw [single_dotProduct]; rw [one_mul]

Depends on / 依赖: one_mul, single_dotProduct
-/
theorem single_one_dotProduct [DecidableEq n] (i : n) (v : n -> α) :
    Pi.single i 1 ⬝ᵥ v = v i := by
  rw [single_dotProduct]; rw [one_mul]

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] (u v w : m -> α)

@[simp]
/--
theorem `neg_dotProduct` / 定理 `neg_dotProduct`

English:
theorem neg_dotProduct
  statement: -v ⬝ᵥ w = -(v ⬝ᵥ w)
  proof: by simp [dotProduct]

@[simp]

中文:
定理 neg_dotProduct
  结论: -v ⬝ᵥ w = -(v ⬝ᵥ w)
  证明: by simp [dotProduct]

@[simp]

Depends on / 依赖: dotProduct
-/
theorem neg_dotProduct : -v ⬝ᵥ w = -(v ⬝ᵥ w) := by simp [dotProduct]

@[simp]
/--
theorem `dotProduct_neg` / 定理 `dotProduct_neg`

English:
theorem dotProduct_neg
  statement: v ⬝ᵥ -w = -(v ⬝ᵥ w)
  proof: by simp [dotProduct]

中文:
定理 dotProduct_neg
  结论: v ⬝ᵥ -w = -(v ⬝ᵥ w)
  证明: by simp [dotProduct]

Depends on / 依赖: dotProduct
-/
theorem dotProduct_neg : v ⬝ᵥ -w = -(v ⬝ᵥ w) := by simp [dotProduct]

/--
lemma `neg_dotProduct_neg` / 引理 `neg_dotProduct_neg`

English:
lemma neg_dotProduct_neg
  statement: -v ⬝ᵥ -w = v ⬝ᵥ w
  proof: by
  rw [neg_dotProduct]; rw [dotProduct_neg]; rw [neg_neg]

@[simp]

中文:
引理 neg_dotProduct_neg
  结论: -v ⬝ᵥ -w = v ⬝ᵥ w
  证明: by
  rw [neg_dotProduct]; rw [dotProduct_neg]; rw [neg_neg]

@[simp]

Depends on / 依赖: dotProduct_neg, neg_dotProduct, neg_neg
-/
lemma neg_dotProduct_neg : -v ⬝ᵥ -w = v ⬝ᵥ w := by
  rw [neg_dotProduct]; rw [dotProduct_neg]; rw [neg_neg]

@[simp]
/--
theorem `sub_dotProduct` / 定理 `sub_dotProduct`

English:
theorem sub_dotProduct
  statement: (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w
  proof: by simp [sub_eq_add_neg]

@[simp]

中文:
定理 sub_dotProduct
  结论: (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w
  证明: by simp [sub_eq_add_neg]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem sub_dotProduct : (u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w := by simp [sub_eq_add_neg]

@[simp]
/--
theorem `dotProduct_sub` / 定理 `dotProduct_sub`

English:
theorem dotProduct_sub
  statement: u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w
  proof: by simp [sub_eq_add_neg]

中文:
定理 dotProduct_sub
  结论: u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w
  证明: by simp [sub_eq_add_neg]

Depends on / 依赖: sub_eq_add_neg
-/
theorem dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w := by simp [sub_eq_add_neg]

end NonUnitalNonAssocRing

section DistribMulAction

variable [Mul α] [AddCommMonoid α] [DistribSMul R α]

@[simp]
/--
theorem `smul_dotProduct` / 定理 `smul_dotProduct`

English:
theorem smul_dotProduct
  given: [IsScalarTower R α α] (x : R) (v w : m -> α)
  proof: by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]

@[simp]

中文:
定理 smul_dotProduct
  条件: [标量塔 R α α] (x : R) (v w : m -> α)
  证明: by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]

@[simp]

Depends on / 依赖: Finset, Finset.smul_sum, dotProduct, smul_mul_assoc, smul_sum
-/
theorem smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m -> α) :
    x • v ⬝ᵥ w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, smul_mul_assoc]

@[simp]
/--
theorem `dotProduct_smul` / 定理 `dotProduct_smul`

English:
theorem dotProduct_smul
  given: [SMulCommClass R α α] (x : R) (v w : m -> α)
  proof: by simp [dotProduct, Finset.smul_sum, mul_smul_comm]

中文:
定理 dotProduct_smul
  条件: [标量交换类 R α α] (x : R) (v w : m -> α)
  证明: by simp [dotProduct, Finset.smul_sum, mul_smul_comm]

Depends on / 依赖: Finset, Finset.smul_sum, dotProduct, mul_smul_comm, smul_sum
-/
theorem dotProduct_smul [SMulCommClass R α α] (x : R) (v w : m -> α) :
    v ⬝ᵥ x • w = x • (v ⬝ᵥ w) := by simp [dotProduct, Finset.smul_sum, mul_smul_comm]

end DistribMulAction

section CommRing
variable [CommRing α] [Nontrivial m] [Nontrivial α]

/--
theorem `exists_ne_zero_dotProduct_eq_zero` / 定理 `exists_ne_zero_dotProduct_eq_zero`

English:
theorem exists_ne_zero_dotProduct_eq_zero
  given: (a : m -> α)
  statement: exists b != 0, b ⬝ᵥ a = 0
  proof: by
  obtain ⟨i, j, hij⟩ : exists i j : m, i != j := nontrivial_iff.mp ‹_›
  classical
  use if a i = 0 then Pi.single i 1 else if a j = 0 then Pi.single j 1 else
    fun k => if k = i then a j else if k = j then - a i else 0
  split_ifs with h h2
  · simp [h]
  · simp [h2]
  · refine ⟨Function.ne_if

中文:
定理 存在_ne_zero_dotProduct_eq_zero
  条件: (a : m -> α)
  结论: 存在 b != 0, b ⬝ᵥ a = 0
  证明: by
  obtain ⟨i, j, hij⟩ : exists i j : m, i != j := nontrivial_iff.mp ‹_›
  classical
  use if a i = 0 then Pi.single i 1 else if a j = 0 then Pi.single j 1 else
    fun k => if k = i then a j else if k = j then - a i else 0
  split_ifs with h h2
  · simp [h]
  · simp [h2]
  · refine ⟨Function.ne_if

Depends on / 依赖: Finset, Finset.sum_eq_ite, Finset.sum_ite, Function, Function.ne_iff.mpr, Pi.single, classical, dotProduct, hij.symm, mul_comm, ne_iff, nontrivial_iff, nontrivial_iff.mp, single, split_ifs, sum_eq_ite, sum_ite
-/
theorem exists_ne_zero_dotProduct_eq_zero (a : m -> α) : exists b != 0, b ⬝ᵥ a = 0 := by
  obtain ⟨i, j, hij⟩ : exists i j : m, i != j := nontrivial_iff.mp ‹_›
  classical
  use if a i = 0 then Pi.single i 1 else if a j = 0 then Pi.single j 1 else
    fun k => if k = i then a j else if k = j then - a i else 0
  split_ifs with h h2
  · simp [h]
  · simp [h2]
  · refine ⟨Function.ne_iff.mpr ⟨i, by simp [h2]⟩, ?_⟩
    simp [dotProduct, Finset.sum_ite, Finset.sum_eq_ite i, hij.symm, mul_comm (a i)]

/--
lemma `not_injective_dotProduct_left` / 引理 `not_injective_dotProduct_left`

English:
lemma not_injective_dotProduct_left
  given: (a : m -> α)
  proof: by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [dotProduct_comm a b, hba, hb] using @h b 0

中文:
引理 not_injective_dotProduct_left
  条件: (a : m -> α)
  证明: by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [dotProduct_comm a b, hba, hb] using @h b 0

Depends on / 依赖: dotProduct_comm, exists_ne_zero_dotProduct_eq_zero
-/
lemma not_injective_dotProduct_left (a : m -> α) :
    ¬ Function.Injective (dotProduct a) := by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [dotProduct_comm a b, hba, hb] using @h b 0

/--
lemma `not_injective_dotProduct_right` / 引理 `not_injective_dotProduct_right`

English:
lemma not_injective_dotProduct_right
  given: (a : m -> α)
  proof: by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [hba, hb] using @h b 0

中文:
引理 not_injective_dotProduct_right
  条件: (a : m -> α)
  证明: by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [hba, hb] using @h b 0

Depends on / 依赖: exists_ne_zero_dotProduct_eq_zero
-/
lemma not_injective_dotProduct_right (a : m -> α) :
    ¬ Function.Injective (dotProduct · a) := by
  intro h
  obtain ⟨b, hb, hba⟩ := exists_ne_zero_dotProduct_eq_zero a
  simpa [hba, hb] using @h b 0

end CommRing

end DotProduct

open Matrix

namespace Matrix

/-- `M * N` is the usual product of matrices `M` and `N`, i.e. we have that
`(M * N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `N`.
This is currently only defined when `m` is finite. -/
-- We want to be lower priority than `instHMul`, but without this we can't have operands with
-- implicit dimensions.
@[default_instance 100]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: m] [Mul α] [AddCommMonoid α] :
  body: fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k

中文:
实例 [有限类型
  签名: m] [乘法 α] [加法交换幺半群 α] :
  定义体: fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k
-/
instance [Fintype m] [Mul α] [AddCommMonoid α] :
    HMul (Matrix l m α) (Matrix m n α) (Matrix l n α) where
  hMul M N := fun i k => (fun j => M i j) ⬝ᵥ fun j => N j k

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  statement: [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
  proof: rfl

中文:
定理 mul_apply
  结论: [有限类型 m] [乘法 α] [加法交换幺半群 α] {M : 矩阵 l m α} {N : 矩阵 m n α}
  证明: rfl
-/
theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = ∑ j, M i j * N j k :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: n] [Mul α] [AddCommMonoid α] : Mul (Matrix n n α) where
  body: M * N

中文:
实例 [有限类型
  签名: n] [乘法 α] [加法交换幺半群 α] : 乘法 (矩阵 n n α) where
  定义体: M * N
-/
instance [Fintype n] [Mul α] [AddCommMonoid α] : Mul (Matrix n n α) where
  mul M N := M * N

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: n] [DecidableEq n] [MulOne α] [AddCommMonoid α] : MulOne (Matrix n n α) where

中文:
实例 [有限类型
  签名: n] [DecidableEq n] [MulOne α] [加法交换幺半群 α] : MulOne (矩阵 n n α) where
-/
instance [Fintype n] [DecidableEq n] [MulOne α] [AddCommMonoid α] : MulOne (Matrix n n α) where

/--
theorem `mul_apply'` / 定理 `mul_apply'`

English:
theorem mul_apply'
  statement: [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
  proof: rfl

中文:
定理 mul_apply'
  结论: [有限类型 m] [乘法 α] [加法交换幺半群 α] {M : 矩阵 l m α} {N : 矩阵 m n α}
  证明: rfl
-/
theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
    {i k} : (M * N) i k = (M i) ⬝ᵥ fun j => N j k :=
  rfl

/--
theorem `two_mul_expl` / 定理 `two_mul_expl`

English:
theorem two_mul_expl
  given: {R : Type*} [NonUnitalNonAssocSemiring R] (A B : Matrix (Fin 2) (Fin 2) R)
  proof: by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    simp

中文:
定理 two_mul_expl
  条件: {R : 类型} [非幺非结合半环 R] (A B : 矩阵 (有限集 2) (有限集 2) R)
  证明: by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    simp

Depends on / 依赖: Finset, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Matrix, Matrix.mul_apply, mul_apply, sum_fin_eq_sum_range, sum_range_succ
-/
theorem two_mul_expl {R : Type*} [NonUnitalNonAssocSemiring R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
    (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
    (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
    (A * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]
    simp

section AddCommMonoid

variable [AddCommMonoid α] [Mul α]

@[simp]
/--
theorem `smul_mul` / 定理 `smul_mul`

English:
theorem smul_mul
  statement: [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
  proof: by
  ext
  apply smul_dotProduct a

@[simp]

中文:
定理 smul_mul
  结论: [有限类型 n] [幺半群 R] [分配乘法作用 R α] [标量塔 R α α] (a : R)
  证明: by
  ext
  apply smul_dotProduct a

@[simp]

Depends on / 依赖: smul_dotProduct
-/
theorem smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] [IsScalarTower R α α] (a : R)
    (M : Matrix m n α) (N : Matrix n l α) : (a • M) * N = a • (M * N) := by
  ext
  apply smul_dotProduct a

@[simp]
/--
theorem `mul_smul` / 定理 `mul_smul`

English:
theorem mul_smul
  statement: [Fintype n] [Monoid R] [DistribMulAction R α] [SMulCommClass R α α]
  proof: by
  ext
  apply dotProduct_smul

中文:
定理 mul_smul
  结论: [有限类型 n] [幺半群 R] [分配乘法作用 R α] [标量交换类 R α α]
  证明: by
  ext
  apply dotProduct_smul
-/
protected theorem mul_smul [Fintype n] [Monoid R] [DistribMulAction R α] [SMulCommClass R α α]
    (M : Matrix m n α) (a : R) (N : Matrix n l α) : M * (a • N) = a • (M * N) := by
  ext
  apply dotProduct_smul

end AddCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

@[simp]
/--
theorem `mul_zero` / 定理 `mul_zero`

English:
theorem mul_zero
  given: [Fintype n] (M : Matrix m n α)
  statement: M * (0 : Matrix n o α) = 0
  proof: by
  ext
  apply dotProduct_zero

@[simp]

中文:
定理 mul_zero
  条件: [有限类型 n] (M : 矩阵 m n α)
  结论: M * (0 : 矩阵 n o α) = 0
  证明: by
  ext
  apply dotProduct_zero

@[simp]
-/
protected theorem mul_zero [Fintype n] (M : Matrix m n α) : M * (0 : Matrix n o α) = 0 := by
  ext
  apply dotProduct_zero

@[simp]
/--
theorem `zero_mul` / 定理 `zero_mul`

English:
theorem zero_mul
  given: [Fintype m] (M : Matrix m n α)
  statement: (0 : Matrix l m α) * M = 0
  proof: by
  ext
  apply zero_dotProduct

中文:
定理 zero_mul
  条件: [有限类型 m] (M : 矩阵 m n α)
  结论: (0 : 矩阵 l m α) * M = 0
  证明: by
  ext
  apply zero_dotProduct
-/
protected theorem zero_mul [Fintype m] (M : Matrix m n α) : (0 : Matrix l m α) * M = 0 := by
  ext
  apply zero_dotProduct

/--
theorem `mul_add` / 定理 `mul_add`

English:
theorem mul_add
  given: [Fintype n] (L : Matrix m n α) (M N : Matrix n o α)
  proof: by
  ext
  apply dotProduct_add

中文:
定理 mul_add
  条件: [有限类型 n] (L : 矩阵 m n α) (M N : 矩阵 n o α)
  证明: by
  ext
  apply dotProduct_add
-/
protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) :
    L * (M + N) = L * M + L * N := by
  ext
  apply dotProduct_add

/--
theorem `add_mul` / 定理 `add_mul`

English:
theorem add_mul
  given: [Fintype m] (L M : Matrix l m α) (N : Matrix m n α)
  proof: by
  ext
  apply add_dotProduct

中文:
定理 add_mul
  条件: [有限类型 m] (L M : 矩阵 l m α) (N : 矩阵 m n α)
  证明: by
  ext
  apply add_dotProduct
-/
protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) :
    (L + M) * N = L * N + M * N := by
  ext
  apply add_dotProduct

/--
Instance `nonUnitalNonAssocSemiring` / 实例 `nonUnitalNonAssocSemiring`

English:
instance nonUnitalNonAssocSemiring
  signature: [Fintype n]
  body: { Matrix.addCommMonoid with
    mul_zero := Matrix.mul_zero
    zero_mul := Matrix.zero_mul
    left_distrib := Matrix.mul_add
    right_distrib := Matrix.add_mul }

@[simp]

中文:
实例 nonUnitalNonAssocSemiring
  签名: [有限类型 n]
  定义体: { Matrix.addCommMonoid with
    mul_zero := Matrix.mul_zero
    zero_mul := Matrix.zero_mul
    left_distrib := Matrix.mul_add
    right_distrib := Matrix.add_mul }

@[simp]

Depends on / 依赖: Matrix, Matrix.addCommMonoid, Matrix.add_mul, Matrix.mul_add, Matrix.mul_zero, Matrix.zero_mul, addCommMonoid, add_mul, left_distrib, mul_add, mul_zero, right_distrib, zero_mul
-/
instance nonUnitalNonAssocSemiring [Fintype n] : NonUnitalNonAssocSemiring (Matrix n n α) :=
  { Matrix.addCommMonoid with
    mul_zero := Matrix.mul_zero
    zero_mul := Matrix.zero_mul
    left_distrib := Matrix.mul_add
    right_distrib := Matrix.add_mul }

@[simp]
/--
theorem `diagonal_mul` / 定理 `diagonal_mul`

English:
theorem diagonal_mul
  given: [Fintype m] [DecidableEq m] (d : m -> α) (M : Matrix m n α) (i j)
  proof: diagonal_dotProduct _ _ _

@[simp]

中文:
定理 diagonal_mul
  条件: [有限类型 m] [DecidableEq m] (d : m -> α) (M : 矩阵 m n α) (i j)
  证明: diagonal_dotProduct _ _ _

@[simp]

Depends on / 依赖: diagonal_dotProduct
-/
theorem diagonal_mul [Fintype m] [DecidableEq m] (d : m -> α) (M : Matrix m n α) (i j) :
    (diagonal d * M) i j = d i * M i j :=
  diagonal_dotProduct _ _ _

@[simp]
/--
theorem `mul_diagonal` / 定理 `mul_diagonal`

English:
theorem mul_diagonal
  given: [Fintype n] [DecidableEq n] (d : n -> α) (M : Matrix m n α) (i j)
  proof: by
  rw [← diagonal_transpose]
  apply dotProduct_diagonal

@[simp]

中文:
定理 mul_diagonal
  条件: [有限类型 n] [DecidableEq n] (d : n -> α) (M : 矩阵 m n α) (i j)
  证明: by
  rw [← diagonal_transpose]
  apply dotProduct_diagonal

@[simp]

Depends on / 依赖: diagonal_transpose, dotProduct_diagonal
-/
theorem mul_diagonal [Fintype n] [DecidableEq n] (d : n -> α) (M : Matrix m n α) (i j) :
    (M * diagonal d) i j = M i j * d j := by
  rw [← diagonal_transpose]
  apply dotProduct_diagonal

@[simp]
/--
theorem `diagonal_mul_diagonal` / 定理 `diagonal_mul_diagonal`

English:
theorem diagonal_mul_diagonal
  given: [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α)
  proof: by
  ext i j
  by_cases h : i = j <;>
  simp [h]

中文:
定理 diagonal_mul_diagonal
  条件: [有限类型 n] [DecidableEq n] (d₁ d₂ : n -> α)
  证明: by
  ext i j
  by_cases h : i = j <;>
  simp [h]
-/
theorem diagonal_mul_diagonal [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

/--
theorem `diagonal_mul_diagonal'` / 定理 `diagonal_mul_diagonal'`

English:
theorem diagonal_mul_diagonal'
  given: [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α)
  proof: diagonal_mul_diagonal _ _

中文:
定理 diagonal_mul_diagonal'
  条件: [有限类型 n] [DecidableEq n] (d₁ d₂ : n -> α)
  证明: diagonal_mul_diagonal _ _

Depends on / 依赖: diagonal_mul_diagonal
-/
theorem diagonal_mul_diagonal' [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α) :
    diagonal d₁ * diagonal d₂ = diagonal fun i => d₁ i * d₂ i :=
  diagonal_mul_diagonal _ _

/--
theorem `commute_diagonal` / 定理 `commute_diagonal`

English:
theorem commute_diagonal
  statement: {α : Type*} [NonUnitalNonAssocCommSemiring α]
  proof: by
  simp_rw [commute_iff_eq, diagonal_mul_diagonal, mul_comm]

中文:
定理 commute_diagonal
  结论: {α : 类型} [非幺非结合交换半环 α]
  证明: by
  simp_rw [commute_iff_eq, diagonal_mul_diagonal, mul_comm]

Depends on / 依赖: commute_iff_eq, diagonal_mul_diagonal, mul_comm, simp_rw
-/
theorem commute_diagonal {α : Type*} [NonUnitalNonAssocCommSemiring α]
    [Fintype n] [DecidableEq n] (d₁ d₂ : n -> α) :
    Commute (diagonal d₁) (diagonal d₂) := by
  simp_rw [commute_iff_eq, diagonal_mul_diagonal, mul_comm]

/--
theorem `smul_eq_diagonal_mul` / 定理 `smul_eq_diagonal_mul`

English:
theorem smul_eq_diagonal_mul
  given: [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α)
  proof: by
  ext
  simp

中文:
定理 smul_eq_diagonal_mul
  条件: [有限类型 m] [DecidableEq m] (M : 矩阵 m n α) (a : α)
  证明: by
  ext
  simp
-/
theorem smul_eq_diagonal_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) (a : α) :
    a • M = (diagonal fun _ => a) * M := by
  ext
  simp

/--
theorem `op_smul_eq_mul_diagonal` / 定理 `op_smul_eq_mul_diagonal`

English:
theorem op_smul_eq_mul_diagonal
  given: [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α)
  proof: by
  ext
  simp

中文:
定理 op_smul_eq_mul_diagonal
  条件: [有限类型 n] [DecidableEq n] (M : 矩阵 m n α) (a : α)
  证明: by
  ext
  simp
-/
theorem op_smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α) :
    MulOpposite.op a • M = M * (diagonal fun _ : n => a) := by
  ext
  simp

/-- Left multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
/--
Definition of `addMonoidHomMulLeft` / `addMonoidHomMulLeft` 的定义

English:
definition addMonoidHomMulLeft
  signature: [Fintype m] (M : Matrix l m α)
  body: M * x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _

中文:
定义 addMonoidHomMulLeft
  签名: [有限类型 m] (M : 矩阵 l m α)
  定义体: M * x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _
-/
def addMonoidHomMulLeft [Fintype m] (M : Matrix l m α) : Matrix m n α ->+ Matrix l n α where
  toFun x := M * x
  map_zero' := Matrix.mul_zero _
  map_add' := Matrix.mul_add _

/-- Right multiplication by a matrix, as an `AddMonoidHom` from matrices to matrices. -/
@[simps]
/--
Definition of `addMonoidHomMulRight` / `addMonoidHomMulRight` 的定义

English:
definition addMonoidHomMulRight
  signature: [Fintype m] (M : Matrix m n α)
  body: x * M
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

中文:
定义 addMonoidHomMulRight
  签名: [有限类型 m] (M : 矩阵 m n α)
  定义体: x * M
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _
-/
def addMonoidHomMulRight [Fintype m] (M : Matrix m n α) : Matrix l m α ->+ Matrix l n α where
  toFun x := x * M
  map_zero' := Matrix.zero_mul _
  map_add' _ _ := Matrix.add_mul _ _ _

/--
theorem `sum_mul` / 定理 `sum_mul`

English:
theorem sum_mul
  given: [Fintype m] (s : Finset β) (f : β -> Matrix l m α) (M : Matrix m n α)
  proof: map_sum (addMonoidHomMulRight M) f s

中文:
定理 sum_mul
  条件: [有限类型 m] (s : 有限集 β) (f : β -> 矩阵 l m α) (M : 矩阵 m n α)
  证明: map_sum (addMonoidHomMulRight M) f s
-/
protected theorem sum_mul [Fintype m] (s : Finset β) (f : β -> Matrix l m α) (M : Matrix m n α) :
    (∑ a in s, f a) * M = ∑ a in s, f a * M :=
  map_sum (addMonoidHomMulRight M) f s

/--
theorem `mul_sum` / 定理 `mul_sum`

English:
theorem mul_sum
  given: [Fintype m] (s : Finset β) (f : β -> Matrix m n α) (M : Matrix l m α)
  proof: map_sum (addMonoidHomMulLeft M) f s

中文:
定理 mul_sum
  条件: [有限类型 m] (s : 有限集 β) (f : β -> 矩阵 m n α) (M : 矩阵 l m α)
  证明: map_sum (addMonoidHomMulLeft M) f s
-/
protected theorem mul_sum [Fintype m] (s : Finset β) (f : β -> Matrix m n α) (M : Matrix l m α) :
    (M * ∑ a in s, f a) = ∑ a in s, M * f a :=
  map_sum (addMonoidHomMulLeft M) f s

/--
Instance `Semiring.isScalarTower` / 实例 `Semiring.isScalarTower`

English:
instance Semiring.isScalarTower
  signature: [Fintype n] [Monoid R] [DistribMulAction R α]
  body: ⟨fun r m n => Matrix.smul_mul r m n⟩

中文:
实例 半环.isScalarTower
  签名: [有限类型 n] [幺半群 R] [分配乘法作用 R α]
  定义体: ⟨fun r m n => Matrix.smul_mul r m n⟩

Depends on / 依赖: Matrix, Matrix.smul_mul, smul_mul
-/
instance Semiring.isScalarTower [Fintype n] [Monoid R] [DistribMulAction R α]
    [IsScalarTower R α α] : IsScalarTower R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => Matrix.smul_mul r m n⟩

/--
Instance `Semiring.smulCommClass` / 实例 `Semiring.smulCommClass`

English:
instance Semiring.smulCommClass
  signature: [Fintype n] [Monoid R] [DistribMulAction R α]
  body: ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩

@[simp]

中文:
实例 半环.smulCommClass
  签名: [有限类型 n] [幺半群 R] [分配乘法作用 R α]
  定义体: ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩

@[simp]

Depends on / 依赖: Matrix, Matrix.mul_smul, mul_smul
-/
instance Semiring.smulCommClass [Fintype n] [Monoid R] [DistribMulAction R α]
    [SMulCommClass R α α] : SMulCommClass R (Matrix n n α) (Matrix n n α) :=
  ⟨fun r m n => (Matrix.mul_smul m r n).symm⟩

@[simp]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  statement: [Fintype n] {L : Matrix m n α} {M : Matrix n o α}
  proof: by
  ext
  simp [mul_apply, map_sum]

中文:
定理 map_mul
  结论: [有限类型 n] {L : 矩阵 m n α} {M : 矩阵 n o α}
  证明: by
  ext
  simp [mul_apply, map_sum]
-/
protected theorem map_mul [Fintype n] {L : Matrix m n α} {M : Matrix n o α}
    [NonUnitalNonAssocSemiring β] {F} [FunLike F α β] [NonUnitalRingHomClass F α β] {f : F} :
    (L * M).map f = L.map f * M.map f := by
  ext
  simp [mul_apply, map_sum]

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

@[simp]
/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: [Fintype m] [DecidableEq m] (M : Matrix m n α)
  proof: by
  ext
  rw [← diagonal_one]; rw [diagonal_mul]; rw [one_mul]

@[simp]

中文:
定理 one_mul
  条件: [有限类型 m] [DecidableEq m] (M : 矩阵 m n α)
  证明: by
  ext
  rw [← diagonal_one]; rw [diagonal_mul]; rw [one_mul]

@[simp]
-/
protected theorem one_mul [Fintype m] [DecidableEq m] (M : Matrix m n α) :
    (1 : Matrix m m α) * M = M := by
  ext
  rw [← diagonal_one]; rw [diagonal_mul]; rw [one_mul]

@[simp]
/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  given: [Fintype n] [DecidableEq n] (M : Matrix m n α)
  proof: by
  ext
  rw [← diagonal_one]; rw [mul_diagonal]; rw [mul_one]

中文:
定理 mul_one
  条件: [有限类型 n] [DecidableEq n] (M : 矩阵 m n α)
  证明: by
  ext
  rw [← diagonal_one]; rw [mul_diagonal]; rw [mul_one]
-/
protected theorem mul_one [Fintype n] [DecidableEq n] (M : Matrix m n α) :
    M * (1 : Matrix n n α) = M := by
  ext
  rw [← diagonal_one]; rw [mul_diagonal]; rw [mul_one]

/--
Instance `nonAssocSemiring` / 实例 `nonAssocSemiring`

English:
instance nonAssocSemiring
  signature: [Fintype n] [DecidableEq n]
  body: { Matrix.nonUnitalNonAssocSemiring, Matrix.instAddCommMonoidWithOne with
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one }

中文:
实例 nonAssocSemiring
  签名: [有限类型 n] [DecidableEq n]
  定义体: { Matrix.nonUnitalNonAssocSemiring, Matrix.instAddCommMonoidWithOne with
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one }

Depends on / 依赖: Matrix, Matrix.instAddCommMonoidWithOne, Matrix.mul_one, Matrix.nonUnitalNonAssocSemiring, Matrix.one_mul, instAddCommMonoidWithOne, mul_one, nonUnitalNonAssocSemiring, one_mul
-/
instance nonAssocSemiring [Fintype n] [DecidableEq n] : NonAssocSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.instAddCommMonoidWithOne with
    one_mul := Matrix.one_mul
    mul_one := Matrix.mul_one }

/--
theorem `smul_one_eq_diagonal` / 定理 `smul_one_eq_diagonal`

English:
theorem smul_one_eq_diagonal
  given: [DecidableEq m] (a : α)
  proof: by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, smul_eq_mul, mul_one]

中文:
定理 smul_one_eq_diagonal
  条件: [DecidableEq m] (a : α)
  证明: by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, smul_eq_mul, mul_one]

Depends on / 依赖: Pi.smul_def, diagonal_one, diagonal_smul, mul_one, simp_rw, smul_def, smul_eq_mul
-/
theorem smul_one_eq_diagonal [DecidableEq m] (a : α) :
    a • (1 : Matrix m m α) = diagonal fun _ => a := by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, smul_eq_mul, mul_one]

/--
theorem `op_smul_one_eq_diagonal` / 定理 `op_smul_one_eq_diagonal`

English:
theorem op_smul_one_eq_diagonal
  given: [DecidableEq m] (a : α)
  proof: by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, op_smul_eq_mul, one_mul]

中文:
定理 op_smul_one_eq_diagonal
  条件: [DecidableEq m] (a : α)
  证明: by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, op_smul_eq_mul, one_mul]

Depends on / 依赖: Pi.smul_def, diagonal_one, diagonal_smul, one_mul, op_smul_eq_mul, simp_rw, smul_def
-/
theorem op_smul_one_eq_diagonal [DecidableEq m] (a : α) :
    MulOpposite.op a • (1 : Matrix m m α) = diagonal fun _ => a := by
  simp_rw [← diagonal_one, ← diagonal_smul, Pi.smul_def, op_smul_eq_mul, one_mul]

end NonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α] [Fintype m] [Fintype n]

/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  given: (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α)
  proof: by
  ext
  apply dotProduct_assoc

中文:
定理 mul_assoc
  条件: (L : 矩阵 l m α) (M : 矩阵 m n α) (N : 矩阵 n o α)
  证明: by
  ext
  apply dotProduct_assoc
-/
protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
    L * M * N = L * (M * N) := by
  ext
  apply dotProduct_assoc

/--
Instance `nonUnitalSemiring` / 实例 `nonUnitalSemiring`

English:
instance nonUnitalSemiring
  signature: : NonUnitalSemiring (Matrix n n α)
  body: { Matrix.nonUnitalNonAssocSemiring with mul_assoc := Matrix.mul_assoc }

中文:
实例 nonUnitalSemiring
  签名: : 非幺半环 (矩阵 n n α)
  定义体: { Matrix.nonUnitalNonAssocSemiring with mul_assoc := Matrix.mul_assoc }

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.nonUnitalNonAssocSemiring, mul_assoc, nonUnitalNonAssocSemiring
-/
instance nonUnitalSemiring : NonUnitalSemiring (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring with mul_assoc := Matrix.mul_assoc }

end NonUnitalSemiring

section Semiring

variable [Semiring α]

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: [Fintype n] [DecidableEq n]
  body: { Matrix.nonUnitalSemiring, Matrix.nonAssocSemiring with }

中文:
实例 semiring
  签名: [有限类型 n] [DecidableEq n]
  定义体: { Matrix.nonUnitalSemiring, Matrix.nonAssocSemiring with }

Depends on / 依赖: Matrix, Matrix.nonAssocSemiring, Matrix.nonUnitalSemiring, nonAssocSemiring, nonUnitalSemiring
-/
instance semiring [Fintype n] [DecidableEq n] : Semiring (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.nonAssocSemiring with }

end Semiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] [Fintype n]

@[simp]
/--
theorem `neg_mul` / 定理 `neg_mul`

English:
theorem neg_mul
  given: (M : Matrix m n α) (N : Matrix n o α)
  statement: (-M) * N = -(M * N)
  proof: by
  ext
  apply neg_dotProduct

@[simp]

中文:
定理 neg_mul
  条件: (M : 矩阵 m n α) (N : 矩阵 n o α)
  结论: (-M) * N = -(M * N)
  证明: by
  ext
  apply neg_dotProduct

@[simp]
-/
protected theorem neg_mul (M : Matrix m n α) (N : Matrix n o α) : (-M) * N = -(M * N) := by
  ext
  apply neg_dotProduct

@[simp]
/--
theorem `mul_neg` / 定理 `mul_neg`

English:
theorem mul_neg
  given: (M : Matrix m n α) (N : Matrix n o α)
  statement: M * (-N) = -(M * N)
  proof: by
  ext
  apply dotProduct_neg

中文:
定理 mul_neg
  条件: (M : 矩阵 m n α) (N : 矩阵 n o α)
  结论: M * (-N) = -(M * N)
  证明: by
  ext
  apply dotProduct_neg
-/
protected theorem mul_neg (M : Matrix m n α) (N : Matrix n o α) : M * (-N) = -(M * N) := by
  ext
  apply dotProduct_neg

/--
theorem `sub_mul` / 定理 `sub_mul`

English:
theorem sub_mul
  given: (M M' : Matrix m n α) (N : Matrix n o α)
  proof: by
  rw [sub_eq_add_neg]; rw [Matrix.add_mul]; rw [Matrix.neg_mul]; rw [sub_eq_add_neg]

中文:
定理 sub_mul
  条件: (M M' : 矩阵 m n α) (N : 矩阵 n o α)
  证明: by
  rw [sub_eq_add_neg]; rw [Matrix.add_mul]; rw [Matrix.neg_mul]; rw [sub_eq_add_neg]
-/
protected theorem sub_mul (M M' : Matrix m n α) (N : Matrix n o α) :
    (M - M') * N = M * N - M' * N := by
  rw [sub_eq_add_neg]; rw [Matrix.add_mul]; rw [Matrix.neg_mul]; rw [sub_eq_add_neg]

/--
theorem `mul_sub` / 定理 `mul_sub`

English:
theorem mul_sub
  given: (M : Matrix m n α) (N N' : Matrix n o α)
  proof: by
  rw [sub_eq_add_neg]; rw [Matrix.mul_add]; rw [Matrix.mul_neg]; rw [sub_eq_add_neg]

中文:
定理 mul_sub
  条件: (M : 矩阵 m n α) (N N' : 矩阵 n o α)
  证明: by
  rw [sub_eq_add_neg]; rw [Matrix.mul_add]; rw [Matrix.mul_neg]; rw [sub_eq_add_neg]
-/
protected theorem mul_sub (M : Matrix m n α) (N N' : Matrix n o α) :
    M * (N - N') = M * N - M * N' := by
  rw [sub_eq_add_neg]; rw [Matrix.mul_add]; rw [Matrix.mul_neg]; rw [sub_eq_add_neg]

/--
Instance `nonUnitalNonAssocRing` / 实例 `nonUnitalNonAssocRing`

English:
instance nonUnitalNonAssocRing
  signature: : NonUnitalNonAssocRing (Matrix n n α)
  body: { Matrix.nonUnitalNonAssocSemiring, Matrix.addCommGroup with }

中文:
实例 nonUnitalNonAssocRing
  签名: : 非幺非结合环 (矩阵 n n α)
  定义体: { Matrix.nonUnitalNonAssocSemiring, Matrix.addCommGroup with }

Depends on / 依赖: Matrix, Matrix.addCommGroup, Matrix.nonUnitalNonAssocSemiring, addCommGroup, nonUnitalNonAssocSemiring
-/
instance nonUnitalNonAssocRing : NonUnitalNonAssocRing (Matrix n n α) :=
  { Matrix.nonUnitalNonAssocSemiring, Matrix.addCommGroup with }

end NonUnitalNonAssocRing

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [Fintype n] [NonUnitalRing α]
  body: { Matrix.nonUnitalSemiring, Matrix.addCommGroup with }

中文:
实例 instNonUnitalRing
  签名: [有限类型 n] [非幺环 α]
  定义体: { Matrix.nonUnitalSemiring, Matrix.addCommGroup with }

Depends on / 依赖: Matrix, Matrix.addCommGroup, Matrix.nonUnitalSemiring, addCommGroup, nonUnitalSemiring
-/
instance instNonUnitalRing [Fintype n] [NonUnitalRing α] : NonUnitalRing (Matrix n n α) :=
  { Matrix.nonUnitalSemiring, Matrix.addCommGroup with }

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [Fintype n] [DecidableEq n] [NonAssocRing α]
  body: { Matrix.nonAssocSemiring, Matrix.instAddCommGroupWithOne with }

中文:
实例 instNonAssocRing
  签名: [有限类型 n] [DecidableEq n] [非结合环 α]
  定义体: { Matrix.nonAssocSemiring, Matrix.instAddCommGroupWithOne with }

Depends on / 依赖: Matrix, Matrix.instAddCommGroupWithOne, Matrix.nonAssocSemiring, instAddCommGroupWithOne, nonAssocSemiring
-/
instance instNonAssocRing [Fintype n] [DecidableEq n] [NonAssocRing α] :
    NonAssocRing (Matrix n n α) :=
  { Matrix.nonAssocSemiring, Matrix.instAddCommGroupWithOne with }

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Fintype n] [DecidableEq n] [Ring α]
  body: { Matrix.semiring, Matrix.instAddCommGroupWithOne with }

中文:
实例 instRing
  签名: [有限类型 n] [DecidableEq n] [环 α]
  定义体: { Matrix.semiring, Matrix.instAddCommGroupWithOne with }

Depends on / 依赖: Matrix, Matrix.instAddCommGroupWithOne, Matrix.semiring, instAddCommGroupWithOne, semiring
-/
instance instRing [Fintype n] [DecidableEq n] [Ring α] : Ring (Matrix n n α) :=
  { Matrix.semiring, Matrix.instAddCommGroupWithOne with }

section Semiring

variable [Semiring α]

@[simp]
/--
theorem `mul_mul_left` / 定理 `mul_mul_left`

English:
theorem mul_mul_left
  given: [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α)
  proof: smul_mul a M N

中文:
定理 mul_mul_left
  条件: [有限类型 n] (M : 矩阵 m n α) (N : 矩阵 n o α) (a : α)
  证明: smul_mul a M N

Depends on / 依赖: smul_mul
-/
theorem mul_mul_left [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (of fun i j => a * M i j) * N = a • (M * N) :=
  smul_mul a M N

/--
lemma `pow_apply_nonneg` / 引理 `pow_apply_nonneg`

English:
lemma pow_apply_nonneg
  statement: [Fintype n] [DecidableEq n] [PartialOrder α] [IsOrderedRing α]
  proof: by
  induction k with
  | zero => aesop (add simp one_apply)
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

中文:
引理 pow_apply_nonneg
  结论: [有限类型 n] [DecidableEq n] [偏序 α] [是Ordered环 α]
  证明: by
  induction k with
  | zero => aesop (add simp one_apply)
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

Depends on / 依赖: Finset, Finset.sum_nonneg, mul_apply, mul_nonneg, one_apply, pow_succ, sum_nonneg
-/
lemma pow_apply_nonneg [Fintype n] [DecidableEq n] [PartialOrder α] [IsOrderedRing α]
    {A : Matrix n n α} (hA : forall i j, 0 <= A i j) (k : Nat) : forall i j, 0 <= (A ^ k) i j := by
  induction k with
  | zero => aesop (add simp one_apply)
  | succ m ih =>
    intro i j; rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hA l j)

end Semiring

section CommSemiring

variable [CommSemiring α]

/--
theorem `smul_eq_mul_diagonal` / 定理 `smul_eq_mul_diagonal`

English:
theorem smul_eq_mul_diagonal
  given: [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α)
  proof: by
  ext
  simp [mul_comm]

@[simp]

中文:
定理 smul_eq_mul_diagonal
  条件: [有限类型 n] [DecidableEq n] (M : 矩阵 m n α) (a : α)
  证明: by
  ext
  simp [mul_comm]

@[simp]

Depends on / 依赖: mul_comm
-/
theorem smul_eq_mul_diagonal [Fintype n] [DecidableEq n] (M : Matrix m n α) (a : α) :
    a • M = M * diagonal fun _ => a := by
  ext
  simp [mul_comm]

@[simp]
/--
theorem `mul_mul_right` / 定理 `mul_mul_right`

English:
theorem mul_mul_right
  given: [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α)
  proof: Matrix.mul_smul M a N

中文:
定理 mul_mul_right
  条件: [有限类型 n] (M : 矩阵 m n α) (N : 矩阵 n o α) (a : α)
  证明: Matrix.mul_smul M a N

Depends on / 依赖: Matrix, Matrix.mul_smul, mul_smul
-/
theorem mul_mul_right [Fintype n] (M : Matrix m n α) (N : Matrix n o α) (a : α) :
    (M * of fun i j => a * N i j) = a • (M * N) :=
  Matrix.mul_smul M a N

end CommSemiring

end Matrix

section IsStablyFiniteRing

/--
Definition of `IsStablyFiniteRing` / `IsStablyFiniteRing` 的定义

English:
class IsStablyFiniteRing
  parameters: (R) [MulOne R] [AddCommMonoid R]
  axioms and operations (1):
    - isDedekindFiniteMonoid((n : Nat)) : IsDedekindFiniteMonoid (Matrix (Fin n) (Fin n) R)

中文:
类 是StablyFinite环
  参数: (R) [MulOne R] [加法交换幺半群 R]
  公理与运算 (1 个):
    - isDedekindFiniteMonoid((n : 自然数)) : 是DedekindFinite幺半群 (矩阵 (有限集 n) (有限集 n) R)
-/
@[mk_iff] class IsStablyFiniteRing (R) [MulOne R] [AddCommMonoid R] : Prop where
  isDedekindFiniteMonoid (n : Nat) : IsDedekindFiniteMonoid (Matrix (Fin n) (Fin n) R)

attribute [instance] IsStablyFiniteRing.isDedekindFiniteMonoid

instance (priority := low) (R) [NonAssocSemiring R] [IsStablyFiniteRing R] :
    IsDedekindFiniteMonoid R :=
  let f : R ->* Matrix (Fin 1) (Fin 1) R :=
    ⟨⟨fun r => diagonal fun _ => r, rfl⟩, fun _ _ => (diagonal_mul_diagonal ..).symm⟩
  .of_injective f fun _ _ eq => by simpa [f] using congr($eq 0 0)

variable {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]

/--
theorem `IsStablyFiniteRing.of_injective` / 定理 `IsStablyFiniteRing.of_injective`

English:
theorem IsStablyFiniteRing.of_injective
  statement: [FunLike F R S] [RingHomClass F R S] (f : F)
  proof: let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) R => M.map f,
    Matrix.map_one _ (map_zero f) (map_one f)⟩ fun _ _ => Matrix.map_mul
.of_injective f Matrix.map_injective hf

中文:
定理 是StablyFinite环.of_injective
  结论: [函数状 F R S] [环态射类 F R S] (f : F)
  证明: let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) R => M.map f,
    Matrix.map_one _ (map_zero f) (map_one f)⟩ fun _ _ => Matrix.map_mul
.of_injective f Matrix.map_injective hf

Depends on / 依赖: M.map, Matrix, Matrix.map_injective, Matrix.map_mul, Matrix.map_one, MonoidHom, MonoidHom.mk, map_injective, map_mul, map_one, map_zero, of_injective
-/
theorem IsStablyFiniteRing.of_injective [FunLike F R S] [RingHomClass F R S] (f : F)
    (hf : Function.Injective f) [IsStablyFiniteRing S] : IsStablyFiniteRing R where
  isDedekindFiniteMonoid n :=
  let f := MonoidHom.mk ⟨fun M : Matrix (Fin n) (Fin n) R => M.map f,
    Matrix.map_one _ (map_zero f) (map_one f)⟩ fun _ _ => Matrix.map_mul
.of_injective f Matrix.map_injective hf

/--
theorem `RingEquiv.isStablyFiniteRing_iff` / 定理 `RingEquiv.isStablyFiniteRing_iff`

English:
theorem RingEquiv.isStablyFiniteRing_iff
  given: [EquivLike F R S] [RingEquivClass F R S] (f : F)
  proof: .of_injective _ (RingEquivClass.toRingEquiv f).symm.injective
  mpr _ := .of_injective f (EquivLike.injective f)

中文:
定理 环等价.isStablyFiniteRing_iff
  条件: [等价状 F R S] [环等价类 F R S] (f : F)
  证明: .of_injective _ (RingEquivClass.toRingEquiv f).symm.injective
  mpr _ := .of_injective f (EquivLike.injective f)

Depends on / 依赖: RingEquivClass, RingEquivClass.toRingEquiv, injective, of_injective, symm.injective, toRingEquiv
-/
theorem RingEquiv.isStablyFiniteRing_iff [EquivLike F R S] [RingEquivClass F R S] (f : F) :
    IsStablyFiniteRing R ↔ IsStablyFiniteRing S where
  mp _ := .of_injective _ (RingEquivClass.toRingEquiv f).symm.injective
  mpr _ := .of_injective f (EquivLike.injective f)

instance (priority := low) [SetLike F R] [SubsemiringClass F R] (S : F) [IsStablyFiniteRing R] :
    IsStablyFiniteRing S :=
  .of_injective _ (Subsemiring.subtype_injective <| .ofClass S)

end IsStablyFiniteRing

open Matrix

namespace Matrix

/--
Definition of `vecMulVec` / `vecMulVec` 的定义

English:
definition vecMulVec
  signature: [Mul α] (w : m -> α) (v : n -> α)
  body: of fun x y => w x * v y

中文:
定义 vecMulVec
  签名: [乘法 α] (w : m -> α) (v : n -> α)
  定义体: of fun x y => w x * v y
-/
def vecMulVec [Mul α] (w : m -> α) (v : n -> α) : Matrix m n α :=
  of fun x y => w x * v y

-- TODO: set as an equation lemma for `vecMulVec`, see https://github.com/leanprover-community/mathlib4/pull/3024
/--
theorem `vecMulVec_apply` / 定理 `vecMulVec_apply`

English:
theorem vecMulVec_apply
  given: [Mul α] (w : m -> α) (v : n -> α) (i j)
  statement: vecMulVec w v i j = w i * v j
  proof: rfl

中文:
定理 vecMulVec_apply
  条件: [乘法 α] (w : m -> α) (v : n -> α) (i j)
  结论: vecMulVec w v i j = w i * v j
  证明: rfl
-/
theorem vecMulVec_apply [Mul α] (w : m -> α) (v : n -> α) (i j) : vecMulVec w v i j = w i * v j :=
  rfl

/--
lemma `row_vecMulVec` / 引理 `row_vecMulVec`

English:
lemma row_vecMulVec
  given: [Mul α] (w : m -> α) (v : n -> α) (i : m)
  proof: rfl

中文:
引理 row_vecMulVec
  条件: [乘法 α] (w : m -> α) (v : n -> α) (i : m)
  证明: rfl
-/
lemma row_vecMulVec [Mul α] (w : m -> α) (v : n -> α) (i : m) :
    (vecMulVec w v).row i = w i • v := rfl

/--
lemma `col_vecMulVec` / 引理 `col_vecMulVec`

English:
lemma col_vecMulVec
  given: [Mul α] (w : m -> α) (v : n -> α) (j : n)
  proof: rfl

中文:
引理 col_vecMulVec
  条件: [乘法 α] (w : m -> α) (v : n -> α) (j : n)
  证明: rfl
-/
lemma col_vecMulVec [Mul α] (w : m -> α) (v : n -> α) (j : n) :
    (vecMulVec w v).col j = MulOpposite.op (v j) • w := rfl

/--
theorem `zero_vecMulVec` / 定理 `zero_vecMulVec`

English:
theorem zero_vecMulVec
  given: [MulZeroClass α] (v : n -> α)
  statement: vecMulVec (0 : m -> α) v = 0
  proof: ext fun _ _ => zero_mul _

中文:
定理 zero_vecMulVec
  条件: [乘零类 α] (v : n -> α)
  结论: vecMulVec (0 : m -> α) v = 0
  证明: ext fun _ _ => zero_mul _
-/
@[simp] theorem zero_vecMulVec [MulZeroClass α] (v : n -> α) : vecMulVec (0 : m -> α) v = 0 :=
  ext fun _ _ => zero_mul _

/--
theorem `vecMulVec_zero` / 定理 `vecMulVec_zero`

English:
theorem vecMulVec_zero
  given: [MulZeroClass α] (w : m -> α)
  statement: vecMulVec w (0 : m -> α) = 0
  proof: ext fun _ _ => mul_zero _

中文:
定理 vecMulVec_zero
  条件: [乘零类 α] (w : m -> α)
  结论: vecMulVec w (0 : m -> α) = 0
  证明: ext fun _ _ => mul_zero _
-/
@[simp] theorem vecMulVec_zero [MulZeroClass α] (w : m -> α) : vecMulVec w (0 : m -> α) = 0 :=
  ext fun _ _ => mul_zero _

/--
theorem `vecMulVec_ne_zero` / 定理 `vecMulVec_ne_zero`

English:
theorem vecMulVec_ne_zero
  statement: [Mul α] [Zero α] [NoZeroDivisors α] {a b : n -> α}
  proof: by
  intro h
  obtain ⟨i, ha⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hb⟩ := Function.ne_iff.mp hb
  exact mul_ne_zero ha hb congr($h i j)

中文:
定理 vecMulVec_ne_zero
  结论: [乘法 α] [零 α] [无零因子 α] {a b : n -> α}
  证明: by
  intro h
  obtain ⟨i, ha⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hb⟩ := Function.ne_iff.mp hb
  exact mul_ne_zero ha hb congr($h i j)

Depends on / 依赖: Function, Function.ne_iff.mp, mul_ne_zero, ne_iff
-/
theorem vecMulVec_ne_zero [Mul α] [Zero α] [NoZeroDivisors α] {a b : n -> α}
    (ha : a != 0) (hb : b != 0) : vecMulVec a b != 0 := by
  intro h
  obtain ⟨i, ha⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hb⟩ := Function.ne_iff.mp hb
  exact mul_ne_zero ha hb congr($h i j)

/--
theorem `vecMulVec_eq_zero` / 定理 `vecMulVec_eq_zero`

English:
theorem vecMulVec_eq_zero
  given: [MulZeroClass α] [NoZeroDivisors α] {a b : n -> α}
  proof: by
  simp only [← ext_iff, vecMulVec_apply, zero_apply, mul_eq_zero, funext_iff, Pi.zero_apply,
    forall_or_left, forall_or_right]

中文:
定理 vecMulVec_eq_zero
  条件: [乘零类 α] [无零因子 α] {a b : n -> α}
  证明: by
  simp only [← ext_iff, vecMulVec_apply, zero_apply, mul_eq_zero, funext_iff, Pi.zero_apply,
    forall_or_left, forall_or_right]
-/
@[simp] theorem vecMulVec_eq_zero [MulZeroClass α] [NoZeroDivisors α] {a b : n -> α} :
    vecMulVec a b = 0 ↔ a = 0 ∨ b = 0 := by
  simp only [← ext_iff, vecMulVec_apply, zero_apply, mul_eq_zero, funext_iff, Pi.zero_apply,
    forall_or_left, forall_or_right]

/--
theorem `add_vecMulVec` / 定理 `add_vecMulVec`

English:
theorem add_vecMulVec
  given: [Mul α] [Add α] [RightDistribClass α] (w₁ w₂ : m -> α) (v : n -> α)
  proof: ext fun _ _ => add_mul _ _ _

中文:
定理 add_vecMulVec
  条件: [乘法 α] [加法 α] [RightDistrib类 α] (w₁ w₂ : m -> α) (v : n -> α)
  证明: ext fun _ _ => add_mul _ _ _

Depends on / 依赖: add_mul
-/
theorem add_vecMulVec [Mul α] [Add α] [RightDistribClass α] (w₁ w₂ : m -> α) (v : n -> α) :
    vecMulVec (w₁ + w₂) v = vecMulVec w₁ v + vecMulVec w₂ v :=
  ext fun _ _ => add_mul _ _ _

/--
theorem `vecMulVec_add` / 定理 `vecMulVec_add`

English:
theorem vecMulVec_add
  given: [Mul α] [Add α] [LeftDistribClass α] (w : m -> α) (v₁ v₂ : n -> α)
  proof: ext fun _ _ => mul_add _ _ _

@[simp]

中文:
定理 vecMulVec_add
  条件: [乘法 α] [加法 α] [LeftDistrib类 α] (w : m -> α) (v₁ v₂ : n -> α)
  证明: ext fun _ _ => mul_add _ _ _

@[simp]

Depends on / 依赖: mul_add
-/
theorem vecMulVec_add [Mul α] [Add α] [LeftDistribClass α] (w : m -> α) (v₁ v₂ : n -> α) :
    vecMulVec w (v₁ + v₂) = vecMulVec w v₁ + vecMulVec w v₂ :=
  ext fun _ _ => mul_add _ _ _

@[simp]
/--
theorem `neg_vecMulVec` / 定理 `neg_vecMulVec`

English:
theorem neg_vecMulVec
  given: [Mul α] [HasDistribNeg α] (w : m -> α) (v : n -> α)
  proof: ext fun _ _ => neg_mul _ _

@[simp]

中文:
定理 neg_vecMulVec
  条件: [乘法 α] [有DistribNeg α] (w : m -> α) (v : n -> α)
  证明: ext fun _ _ => neg_mul _ _

@[simp]

Depends on / 依赖: neg_mul
-/
theorem neg_vecMulVec [Mul α] [HasDistribNeg α] (w : m -> α) (v : n -> α) :
    vecMulVec (-w) v = -vecMulVec w v :=
  ext fun _ _ => neg_mul _ _

@[simp]
/--
theorem `vecMulVec_neg` / 定理 `vecMulVec_neg`

English:
theorem vecMulVec_neg
  given: [Mul α] [HasDistribNeg α] (w : m -> α) (v : n -> α)
  proof: ext fun _ _ => mul_neg _ _

@[simp]

中文:
定理 vecMulVec_neg
  条件: [乘法 α] [有DistribNeg α] (w : m -> α) (v : n -> α)
  证明: ext fun _ _ => mul_neg _ _

@[simp]

Depends on / 依赖: corec_eq, mul_neg
-/
theorem vecMulVec_neg [Mul α] [HasDistribNeg α] (w : m -> α) (v : n -> α) :
    vecMulVec w (-v) = -vecMulVec w v :=
  ext fun _ _ => mul_neg _ _

@[simp]
/--
theorem `smul_vecMulVec` / 定理 `smul_vecMulVec`

English:
theorem smul_vecMulVec
  given: [Mul α] [SMul R α] [IsScalarTower R α α] (r : R) (w : m -> α) (v : n -> α)
  proof: ext fun _ _ => smul_mul_assoc _ _ _

@[simp]

中文:
定理 smul_vecMulVec
  条件: [乘法 α] [标量乘法 R α] [标量塔 R α α] (r : R) (w : m -> α) (v : n -> α)
  证明: ext fun _ _ => smul_mul_assoc _ _ _

@[simp]

Depends on / 依赖: smul_mul_assoc
-/
theorem smul_vecMulVec [Mul α] [SMul R α] [IsScalarTower R α α] (r : R) (w : m -> α) (v : n -> α) :
    vecMulVec (r • w) v = r • vecMulVec w v :=
  ext fun _ _ => smul_mul_assoc _ _ _

@[simp]
/--
theorem `vecMulVec_smul` / 定理 `vecMulVec_smul`

English:
theorem vecMulVec_smul
  given: [Mul α] [SMul R α] [SMulCommClass R α α] (r : R) (w : m -> α) (v : n -> α)
  proof: ext fun _ _ => mul_smul_comm _ _ _

中文:
定理 vecMulVec_smul
  条件: [乘法 α] [标量乘法 R α] [标量交换类 R α α] (r : R) (w : m -> α) (v : n -> α)
  证明: ext fun _ _ => mul_smul_comm _ _ _

Depends on / 依赖: mul_smul_comm
-/
theorem vecMulVec_smul [Mul α] [SMul R α] [SMulCommClass R α α] (r : R) (w : m -> α) (v : n -> α) :
    vecMulVec w (r • v) = r • vecMulVec w v :=
  ext fun _ _ => mul_smul_comm _ _ _

/--
theorem `vecMulVec_smul'` / 定理 `vecMulVec_smul'`

English:
theorem vecMulVec_smul'
  given: [Semigroup α] (w : m -> α) (r : α) (v : n -> α)
  proof: .symm ext fun _ _ => mul_assoc _ _ _

@[simp]

中文:
定理 vecMulVec_smul'
  条件: [半群 α] (w : m -> α) (r : α) (v : n -> α)
  证明: .symm ext fun _ _ => mul_assoc _ _ _

@[simp]

Depends on / 依赖: mul_assoc
-/
theorem vecMulVec_smul' [Semigroup α] (w : m -> α) (r : α) (v : n -> α) :
    vecMulVec w (r • v) = vecMulVec (MulOpposite.op r • w) v :=
.symm ext fun _ _ => mul_assoc _ _ _

@[simp]
/--
theorem `transpose_vecMulVec` / 定理 `transpose_vecMulVec`

English:
theorem transpose_vecMulVec
  given: [CommMagma α] (w : m -> α) (v : n -> α)
  proof: ext fun _ _ => mul_comm _ _

@[simp]

中文:
定理 transpose_vecMulVec
  条件: [交换原群 α] (w : m -> α) (v : n -> α)
  证明: ext fun _ _ => mul_comm _ _

@[simp]

Depends on / 依赖: mul_comm
-/
theorem transpose_vecMulVec [CommMagma α] (w : m -> α) (v : n -> α) :
    (vecMulVec w v)ᵀ = vecMulVec v w :=
  ext fun _ _ => mul_comm _ _

@[simp]
/--
theorem `diag_vecMulVec` / 定理 `diag_vecMulVec`

English:
theorem diag_vecMulVec
  given: [Mul α] (u v : n -> α)
  statement: diag (vecMulVec u v) = u * v
  proof: rfl

中文:
定理 diag_vecMulVec
  条件: [乘法 α] (u v : n -> α)
  结论: diag (vecMulVec u v) = u * v
  证明: rfl
-/
theorem diag_vecMulVec [Mul α] (u v : n -> α) : diag (vecMulVec u v) = u * v := rfl

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

/--
Definition of `mulVec` / `mulVec` 的定义

English:
definition mulVec
  signature: [Fintype n] (M : Matrix m n α) (v : n -> α)

中文:
定义 mulVec
  签名: [有限类型 n] (M : 矩阵 m n α) (v : n -> α)
-/
def mulVec [Fintype n] (M : Matrix m n α) (v : n -> α) : m -> α
  | i => (fun j => M i j) ⬝ᵥ v

@[inherit_doc]
scoped infixr:73 " *ᵥ " => Matrix.mulVec

/--
lemma `mulVec_apply` / 引理 `mulVec_apply`

English:
lemma mulVec_apply
  given: [Fintype n] (M : Matrix m n α) (v : n -> α) (i : m)
  proof: rfl

中文:
引理 mulVec_apply
  条件: [有限类型 n] (M : 矩阵 m n α) (v : n -> α) (i : m)
  证明: rfl
-/
lemma mulVec_apply [Fintype n] (M : Matrix m n α) (v : n -> α) (i : m) :
    (M *ᵥ v) i = M.row i ⬝ᵥ v := rfl

/--
lemma `mulVec_apply_eq_sum` / 引理 `mulVec_apply_eq_sum`

English:
lemma mulVec_apply_eq_sum
  given: [Fintype n] (M : Matrix m n α) (v : n -> α) (i : m)
  proof: rfl

中文:
引理 mulVec_apply_eq_sum
  条件: [有限类型 n] (M : 矩阵 m n α) (v : n -> α) (i : m)
  证明: rfl
-/
lemma mulVec_apply_eq_sum [Fintype n] (M : Matrix m n α) (v : n -> α) (i : m) :
    (M *ᵥ v) i = ∑ j : n, M i j * v j := rfl

/--
Definition of `vecMul` / `vecMul` 的定义

English:
definition vecMul
  signature: [Fintype m] (v : m -> α) (M : Matrix m n α)

中文:
定义 vecMul
  签名: [有限类型 m] (v : m -> α) (M : 矩阵 m n α)
-/
def vecMul [Fintype m] (v : m -> α) (M : Matrix m n α) : n -> α
  | j => v ⬝ᵥ fun i => M i j

@[inherit_doc]
scoped infixl:73 " ᵥ* " => Matrix.vecMul

/--
lemma `vecMul_apply` / 引理 `vecMul_apply`

English:
lemma vecMul_apply
  given: [Fintype m] (v : m -> α) (M : Matrix m n α) (i : n)
  proof: rfl

中文:
引理 vecMul_apply
  条件: [有限类型 m] (v : m -> α) (M : 矩阵 m n α) (i : n)
  证明: rfl
-/
lemma vecMul_apply [Fintype m] (v : m -> α) (M : Matrix m n α) (i : n) :
    (v ᵥ* M) i = v ⬝ᵥ M.col i := rfl

/--
lemma `vecMul_apply_eq_sum` / 引理 `vecMul_apply_eq_sum`

English:
lemma vecMul_apply_eq_sum
  given: [Fintype m] (v : m -> α) (M : Matrix m n α) (i : n)
  proof: rfl

中文:
引理 vecMul_apply_eq_sum
  条件: [有限类型 m] (v : m -> α) (M : 矩阵 m n α) (i : n)
  证明: rfl
-/
lemma vecMul_apply_eq_sum [Fintype m] (v : m -> α) (M : Matrix m n α) (i : n) :
    (v ᵥ* M) i = ∑ j : m, v j * M j i := rfl

/-- Left multiplication by a matrix, as an `AddMonoidHom` from vectors to vectors. -/
@[simps]
/--
Definition of `mulVec.addMonoidHomLeft` / `mulVec.addMonoidHomLeft` 的定义

English:
definition mulVec.addMonoidHomLeft
  signature: [Fintype n] (v : n -> α)
  body: M *ᵥ v
  map_zero' := by
    ext
    simp [mulVec]
  map_add' x y := by
    ext m
    apply add_dotProduct

中文:
定义 mulVec.addMonoidHomLeft
  签名: [有限类型 n] (v : n -> α)
  定义体: M *ᵥ v
  map_zero' := by
    ext
    simp [mulVec]
  map_add' x y := by
    ext m
    apply add_dotProduct
-/
def mulVec.addMonoidHomLeft [Fintype n] (v : n -> α) : Matrix m n α ->+ m -> α where
  toFun M := M *ᵥ v
  map_zero' := by
    ext
    simp [mulVec]
  map_add' x y := by
    ext m
    apply add_dotProduct

/--
theorem `mul_apply_eq_vecMul` / 定理 `mul_apply_eq_vecMul`

English:
theorem mul_apply_eq_vecMul
  given: [Fintype n] (A : Matrix m n α) (B : Matrix n o α) (i : m)
  proof: rfl

中文:
定理 mul_apply_eq_vecMul
  条件: [有限类型 n] (A : 矩阵 m n α) (B : 矩阵 n o α) (i : m)
  证明: rfl
-/
theorem mul_apply_eq_vecMul [Fintype n] (A : Matrix m n α) (B : Matrix n o α) (i : m) :
    (A * B) i = A i ᵥ* B :=
  rfl

/--
theorem `vecMul_eq_sum` / 定理 `vecMul_eq_sum`

English:
theorem vecMul_eq_sum
  given: [Fintype m] (v : m -> α) (M : Matrix m n α)
  statement: v ᵥ* M = ∑ i, v i • M i
  proof: (Finset.sum_fn ..).symm

中文:
定理 vecMul_eq_sum
  条件: [有限类型 m] (v : m -> α) (M : 矩阵 m n α)
  结论: v ᵥ* M = ∑ i, v i • M i
  证明: (Finset.sum_fn ..).symm

Depends on / 依赖: Finset, Finset.sum_fn, sum_fn
-/
theorem vecMul_eq_sum [Fintype m] (v : m -> α) (M : Matrix m n α) : v ᵥ* M = ∑ i, v i • M i :=
  (Finset.sum_fn ..).symm

/--
theorem `mulVec_eq_sum` / 定理 `mulVec_eq_sum`

English:
theorem mulVec_eq_sum
  given: [Fintype n] (v : n -> α) (M : Matrix m n α)
  proof: (Finset.sum_fn ..).symm

中文:
定理 mulVec_eq_sum
  条件: [有限类型 n] (v : n -> α) (M : 矩阵 m n α)
  证明: (Finset.sum_fn ..).symm

Depends on / 依赖: Finset, Finset.sum_fn, sum_fn
-/
theorem mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix m n α) :
    M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i :=
  (Finset.sum_fn ..).symm

/--
theorem `mulVec_diagonal` / 定理 `mulVec_diagonal`

English:
theorem mulVec_diagonal
  given: [Fintype m] [DecidableEq m] (v w : m -> α) (x : m)
  proof: diagonal_dotProduct v w x

中文:
定理 mulVec_diagonal
  条件: [有限类型 m] [DecidableEq m] (v w : m -> α) (x : m)
  证明: diagonal_dotProduct v w x

Depends on / 依赖: diagonal_dotProduct
-/
theorem mulVec_diagonal [Fintype m] [DecidableEq m] (v w : m -> α) (x : m) :
    (diagonal v *ᵥ w) x = v x * w x :=
  diagonal_dotProduct v w x

/--
theorem `vecMul_diagonal` / 定理 `vecMul_diagonal`

English:
theorem vecMul_diagonal
  given: [Fintype m] [DecidableEq m] (v w : m -> α) (x : m)
  proof: dotProduct_diagonal' v w x

中文:
定理 vecMul_diagonal
  条件: [有限类型 m] [DecidableEq m] (v w : m -> α) (x : m)
  证明: dotProduct_diagonal' v w x

Depends on / 依赖: dotProduct_diagonal
-/
theorem vecMul_diagonal [Fintype m] [DecidableEq m] (v w : m -> α) (x : m) :
    (v ᵥ* diagonal w) x = v x * w x :=
  dotProduct_diagonal' v w x

/--
theorem `dotProduct_mulVec` / 定理 `dotProduct_mulVec`

English:
theorem dotProduct_mulVec
  statement: [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m -> R)
  proof: by
  simp only [dotProduct, vecMul, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

中文:
定理 dotProduct_mulVec
  结论: [有限类型 n] [有限类型 m] [非幺半环 R] (v : m -> R)
  证明: by
  simp only [dotProduct, vecMul, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_comm, Finset.sum_mul, dotProduct, mulVec, mul_assoc, mul_sum, sum_comm, sum_mul, vecMul
-/
theorem dotProduct_mulVec [Fintype n] [Fintype m] [NonUnitalSemiring R] (v : m -> R)
    (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v ᵥ* A ⬝ᵥ w := by
  simp only [dotProduct, vecMul, mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/--
lemma `dot_mulVec_eq_sum_sum` / 引理 `dot_mulVec_eq_sum_sum`

English:
lemma dot_mulVec_eq_sum_sum
  statement: [Fintype n] [Fintype m] [NonUnitalSemiring R]
  proof: by
  simp_rw [dotProduct_mulVec, dotProduct, vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]

@[simp]

中文:
引理 dot_mulVec_eq_sum_sum
  结论: [有限类型 n] [有限类型 m] [非幺半环 R]
  证明: by
  simp_rw [dotProduct_mulVec, dotProduct, vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]

@[simp]

Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_mul, Pi.smul_apply, dotProduct, dotProduct_mulVec, simp_rw, smul_apply, smul_eq_mul, sum_apply, sum_mul, vecMul_eq_sum
-/
lemma dot_mulVec_eq_sum_sum [Fintype n] [Fintype m] [NonUnitalSemiring R]
    (v : m -> R) (A : Matrix m n R) (w : n -> R) :
    v ⬝ᵥ (A *ᵥ w) = ∑ j, ∑ i, v i * A i j * w j := by
  simp_rw [dotProduct_mulVec, dotProduct, vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]

@[simp]
/--
theorem `mulVec_zero` / 定理 `mulVec_zero`

English:
theorem mulVec_zero
  given: [Fintype n] (A : Matrix m n α)
  statement: A *ᵥ 0 = 0
  proof: by
  ext
  simp [mulVec]

@[simp]

中文:
定理 mulVec_zero
  条件: [有限类型 n] (A : 矩阵 m n α)
  结论: A *ᵥ 0 = 0
  证明: by
  ext
  simp [mulVec]

@[simp]

Depends on / 依赖: mulVec
-/
theorem mulVec_zero [Fintype n] (A : Matrix m n α) : A *ᵥ 0 = 0 := by
  ext
  simp [mulVec]

@[simp]
/--
theorem `zero_vecMul` / 定理 `zero_vecMul`

English:
theorem zero_vecMul
  given: [Fintype m] (A : Matrix m n α)
  statement: 0 ᵥ* A = 0
  proof: by
  ext
  simp [vecMul]

@[simp]

中文:
定理 zero_vecMul
  条件: [有限类型 m] (A : 矩阵 m n α)
  结论: 0 ᵥ* A = 0
  证明: by
  ext
  simp [vecMul]

@[simp]

Depends on / 依赖: vecMul
-/
theorem zero_vecMul [Fintype m] (A : Matrix m n α) : 0 ᵥ* A = 0 := by
  ext
  simp [vecMul]

@[simp]
/--
theorem `zero_mulVec` / 定理 `zero_mulVec`

English:
theorem zero_mulVec
  given: [Fintype n] (v : n -> α)
  statement: (0 : Matrix m n α) *ᵥ v = 0
  proof: by
  ext
  simp [mulVec]

@[simp]

中文:
定理 zero_mulVec
  条件: [有限类型 n] (v : n -> α)
  结论: (0 : 矩阵 m n α) *ᵥ v = 0
  证明: by
  ext
  simp [mulVec]

@[simp]

Depends on / 依赖: mulVec
-/
theorem zero_mulVec [Fintype n] (v : n -> α) : (0 : Matrix m n α) *ᵥ v = 0 := by
  ext
  simp [mulVec]

@[simp]
/--
theorem `vecMul_zero` / 定理 `vecMul_zero`

English:
theorem vecMul_zero
  given: [Fintype m] (v : m -> α)
  statement: v ᵥ* (0 : Matrix m n α) = 0
  proof: by
  ext
  simp [vecMul]

中文:
定理 vecMul_zero
  条件: [有限类型 m] (v : m -> α)
  结论: v ᵥ* (0 : 矩阵 m n α) = 0
  证明: by
  ext
  simp [vecMul]

Depends on / 依赖: vecMul
-/
theorem vecMul_zero [Fintype m] (v : m -> α) : v ᵥ* (0 : Matrix m n α) = 0 := by
  ext
  simp [vecMul]

/--
theorem `mulVec_add` / 定理 `mulVec_add`

English:
theorem mulVec_add
  given: [Fintype n] (A : Matrix m n α) (x y : n -> α)
  proof: by
  ext
  apply dotProduct_add

中文:
定理 mulVec_add
  条件: [有限类型 n] (A : 矩阵 m n α) (x y : n -> α)
  证明: by
  ext
  apply dotProduct_add

Depends on / 依赖: dotProduct_add
-/
theorem mulVec_add [Fintype n] (A : Matrix m n α) (x y : n -> α) :
    A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y := by
  ext
  apply dotProduct_add

/--
theorem `add_mulVec` / 定理 `add_mulVec`

English:
theorem add_mulVec
  given: [Fintype n] (A B : Matrix m n α) (x : n -> α)
  proof: by
  ext
  apply add_dotProduct

中文:
定理 add_mulVec
  条件: [有限类型 n] (A B : 矩阵 m n α) (x : n -> α)
  证明: by
  ext
  apply add_dotProduct

Depends on / 依赖: add_dotProduct
-/
theorem add_mulVec [Fintype n] (A B : Matrix m n α) (x : n -> α) :
    (A + B) *ᵥ x = A *ᵥ x + B *ᵥ x := by
  ext
  apply add_dotProduct

/--
theorem `vecMul_add` / 定理 `vecMul_add`

English:
theorem vecMul_add
  given: [Fintype m] (A B : Matrix m n α) (x : m -> α)
  proof: by
  ext
  apply dotProduct_add

中文:
定理 vecMul_add
  条件: [有限类型 m] (A B : 矩阵 m n α) (x : m -> α)
  证明: by
  ext
  apply dotProduct_add

Depends on / 依赖: dotProduct_add
-/
theorem vecMul_add [Fintype m] (A B : Matrix m n α) (x : m -> α) :
    x ᵥ* (A + B) = x ᵥ* A + x ᵥ* B := by
  ext
  apply dotProduct_add

/--
theorem `add_vecMul` / 定理 `add_vecMul`

English:
theorem add_vecMul
  given: [Fintype m] (A : Matrix m n α) (x y : m -> α)
  proof: by
  ext
  apply add_dotProduct

中文:
定理 add_vecMul
  条件: [有限类型 m] (A : 矩阵 m n α) (x y : m -> α)
  证明: by
  ext
  apply add_dotProduct

Depends on / 依赖: add_dotProduct
-/
theorem add_vecMul [Fintype m] (A : Matrix m n α) (x y : m -> α) :
    (x + y) ᵥ* A = x ᵥ* A + y ᵥ* A := by
  ext
  apply add_dotProduct

/--
theorem `mulVec_smul` / 定理 `mulVec_smul`

English:
theorem mulVec_smul
  statement: [Fintype n] [DistribSMul R α] [SMulCommClass R α α]
  proof: by
  ext
  exact dotProduct_smul _ _ _

中文:
定理 mulVec_smul
  结论: [有限类型 n] [分配标量乘法 R α] [标量交换类 R α α]
  证明: by
  ext
  exact dotProduct_smul _ _ _

Depends on / 依赖: dotProduct_smul
-/
theorem mulVec_smul [Fintype n] [DistribSMul R α] [SMulCommClass R α α]
    (M : Matrix m n α) (b : R) (v : n -> α) :
    M *ᵥ (b • v) = b • M *ᵥ v := by
  ext
  exact dotProduct_smul _ _ _

/--
theorem `smul_mulVec` / 定理 `smul_mulVec`

English:
theorem smul_mulVec
  statement: [Fintype n] [DistribSMul R α] [IsScalarTower R α α]
  proof: by
  ext
  exact smul_dotProduct _ _ _

中文:
定理 smul_mulVec
  结论: [有限类型 n] [分配标量乘法 R α] [标量塔 R α α]
  证明: by
  ext
  exact smul_dotProduct _ _ _

Depends on / 依赖: smul_dotProduct
-/
theorem smul_mulVec [Fintype n] [DistribSMul R α] [IsScalarTower R α α]
    (b : R) (M : Matrix m n α) (v : n -> α) :
    (b • M) *ᵥ v = b • M *ᵥ v := by
  ext
  exact smul_dotProduct _ _ _

/--
theorem `smul_vecMul` / 定理 `smul_vecMul`

English:
theorem smul_vecMul
  statement: [Fintype m] [DistribSMul R α] [IsScalarTower R α α]
  proof: by
  ext
  exact smul_dotProduct _ _ _

中文:
定理 smul_vecMul
  结论: [有限类型 m] [分配标量乘法 R α] [标量塔 R α α]
  证明: by
  ext
  exact smul_dotProduct _ _ _

Depends on / 依赖: smul_dotProduct
-/
theorem smul_vecMul [Fintype m] [DistribSMul R α] [IsScalarTower R α α]
    (b : R) (v : m -> α) (M : Matrix m n α) :
    (b • v) ᵥ* M = b • v ᵥ* M := by
  ext
  exact smul_dotProduct _ _ _

/--
theorem `vecMul_smul` / 定理 `vecMul_smul`

English:
theorem vecMul_smul
  statement: [Fintype m] [DistribSMul R α] [SMulCommClass R α α]
  proof: by
  ext
  exact dotProduct_smul _ _ _

@[simp]

中文:
定理 vecMul_smul
  结论: [有限类型 m] [分配标量乘法 R α] [标量交换类 R α α]
  证明: by
  ext
  exact dotProduct_smul _ _ _

@[simp]

Depends on / 依赖: dotProduct_smul
-/
theorem vecMul_smul [Fintype m] [DistribSMul R α] [SMulCommClass R α α]
    (v : m -> α) (b : R) (M : Matrix m n α) :
    v ᵥ* (b • M) = b • v ᵥ* M := by
  ext
  exact dotProduct_smul _ _ _

@[simp]
/--
theorem `mulVec_single` / 定理 `mulVec_single`

English:
theorem mulVec_single
  statement: [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
  proof: funext fun _ => dotProduct_single _ _ _

@[simp]

中文:
定理 mulVec_single
  结论: [有限类型 n] [DecidableEq n] [非幺非结合半环 R] (M : 矩阵 m n R)
  证明: funext fun _ => dotProduct_single _ _ _

@[simp]

Depends on / 依赖: dotProduct_single
-/
theorem mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (j : n) (x : R) : M *ᵥ Pi.single j x = MulOpposite.op x • M.col j :=
  funext fun _ => dotProduct_single _ _ _

@[simp]
/--
theorem `single_vecMul` / 定理 `single_vecMul`

English:
theorem single_vecMul
  statement: [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
  proof: funext fun _ => single_dotProduct _ _ _

中文:
定理 single_vecMul
  结论: [有限类型 m] [DecidableEq m] [非幺非结合半环 R] (M : 矩阵 m n R)
  证明: funext fun _ => single_dotProduct _ _ _

Depends on / 依赖: single_dotProduct
-/
theorem single_vecMul [Fintype m] [DecidableEq m] [NonUnitalNonAssocSemiring R] (M : Matrix m n R)
    (i : m) (x : R) : Pi.single i x ᵥ* M = x • M.row i :=
  funext fun _ => single_dotProduct _ _ _

/--
theorem `mulVec_single_one` / 定理 `mulVec_single_one`

English:
theorem mulVec_single_one
  statement: [Fintype n] [DecidableEq n] [NonAssocSemiring R]
  proof: by ext; simp

中文:
定理 mulVec_single_one
  结论: [有限类型 n] [DecidableEq n] [非结合半环 R]
  证明: by ext; simp
-/
theorem mulVec_single_one [Fintype n] [DecidableEq n] [NonAssocSemiring R]
    (M : Matrix m n R) (j : n) :
    M *ᵥ Pi.single j 1 = M.col j := by ext; simp

/--
theorem `single_one_vecMul` / 定理 `single_one_vecMul`

English:
theorem single_one_vecMul
  statement: [Fintype m] [DecidableEq m] [NonAssocSemiring R]
  proof: by ext; simp

中文:
定理 single_one_vecMul
  结论: [有限类型 m] [DecidableEq m] [非结合半环 R]
  证明: by ext; simp
-/
theorem single_one_vecMul [Fintype m] [DecidableEq m] [NonAssocSemiring R]
    (i : m) (M : Matrix m n R) :
    Pi.single i 1 ᵥ* M = M.row i := by ext; simp

/--
theorem `diagonal_mulVec_single` / 定理 `diagonal_mulVec_single`

English:
theorem diagonal_mulVec_single
  statement: [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n -> R)
  proof: by
  ext i
  rw [mulVec_diagonal]
  exact Pi.apply_single (fun i x => v i * x) (fun i => mul_zero _) j x i

中文:
定理 diagonal_mulVec_single
  结论: [有限类型 n] [DecidableEq n] [非幺非结合半环 R] (v : n -> R)
  证明: by
  ext i
  rw [mulVec_diagonal]
  exact Pi.apply_single (fun i x => v i * x) (fun i => mul_zero _) j x i

Depends on / 依赖: Pi.apply_single, apply_single, mulVec_diagonal, mul_zero
-/
theorem diagonal_mulVec_single [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n -> R)
    (j : n) (x : R) : diagonal v *ᵥ Pi.single j x = Pi.single j (v j * x) := by
  ext i
  rw [mulVec_diagonal]
  exact Pi.apply_single (fun i x => v i * x) (fun i => mul_zero _) j x i

/--
theorem `single_vecMul_diagonal` / 定理 `single_vecMul_diagonal`

English:
theorem single_vecMul_diagonal
  statement: [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n -> R)
  proof: by
  ext i
  rw [vecMul_diagonal]
  exact Pi.apply_single (fun i x => x * v i) (fun i => zero_mul _) j x i

中文:
定理 single_vecMul_diagonal
  结论: [有限类型 n] [DecidableEq n] [非幺非结合半环 R] (v : n -> R)
  证明: by
  ext i
  rw [vecMul_diagonal]
  exact Pi.apply_single (fun i x => x * v i) (fun i => zero_mul _) j x i

Depends on / 依赖: Pi.apply_single, apply_single, vecMul_diagonal, zero_mul
-/
theorem single_vecMul_diagonal [Fintype n] [DecidableEq n] [NonUnitalNonAssocSemiring R] (v : n -> R)
    (j : n) (x : R) : (Pi.single j x) ᵥ* (diagonal v) = Pi.single j (x * v j) := by
  ext i
  rw [vecMul_diagonal]
  exact Pi.apply_single (fun i x => x * v i) (fun i => zero_mul _) j x i

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable [NonUnitalSemiring α]

@[simp]
/--
theorem `vecMul_vecMul` / 定理 `vecMul_vecMul`

English:
theorem vecMul_vecMul
  given: [Fintype n] [Fintype m] (v : m -> α) (M : Matrix m n α) (N : Matrix n o α)
  proof: by
  ext
  apply dotProduct_assoc

@[simp]

中文:
定理 vecMul_vecMul
  条件: [有限类型 n] [有限类型 m] (v : m -> α) (M : 矩阵 m n α) (N : 矩阵 n o α)
  证明: by
  ext
  apply dotProduct_assoc

@[simp]

Depends on / 依赖: dotProduct_assoc
-/
theorem vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α) (M : Matrix m n α) (N : Matrix n o α) :
    v ᵥ* M ᵥ* N = v ᵥ* (M * N) := by
  ext
  apply dotProduct_assoc

@[simp]
/--
theorem `mulVec_mulVec` / 定理 `mulVec_mulVec`

English:
theorem mulVec_mulVec
  given: [Fintype n] [Fintype o] (v : o -> α) (M : Matrix m n α) (N : Matrix n o α)
  proof: by
  ext
  symm
  apply dotProduct_assoc

中文:
定理 mulVec_mulVec
  条件: [有限类型 n] [有限类型 o] (v : o -> α) (M : 矩阵 m n α) (N : 矩阵 n o α)
  证明: by
  ext
  symm
  apply dotProduct_assoc

Depends on / 依赖: dotProduct_assoc
-/
theorem mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α) (M : Matrix m n α) (N : Matrix n o α) :
    M *ᵥ N *ᵥ v = (M * N) *ᵥ v := by
  ext
  symm
  apply dotProduct_assoc

/--
theorem `mul_mul_apply` / 定理 `mul_mul_apply`

English:
theorem mul_mul_apply
  given: [Fintype n] (A B C : Matrix n n α) (i j : n)
  proof: by
  rw [Matrix.mul_assoc]
  simp [mul_apply, dotProduct, mulVec]

中文:
定理 mul_mul_apply
  条件: [有限类型 n] (A B C : 矩阵 n n α) (i j : n)
  证明: by
  rw [Matrix.mul_assoc]
  simp [mul_apply, dotProduct, mulVec]

Depends on / 依赖: Matrix, Matrix.mul_assoc, dotProduct, mulVec, mul_apply, mul_assoc
-/
theorem mul_mul_apply [Fintype n] (A B C : Matrix n n α) (i j : n) :
    (A * B * C) i j = A i ⬝ᵥ B *ᵥ (Cᵀ j) := by
  rw [Matrix.mul_assoc]
  simp [mul_apply, dotProduct, mulVec]

/--
theorem `vecMul_vecMulVec` / 定理 `vecMul_vecMulVec`

English:
theorem vecMul_vecMulVec
  given: [Fintype m] (u v : m -> α) (w : n -> α)
  proof: by
  ext i
  simp [vecMul, dotProduct, vecMulVec, Finset.sum_mul, mul_assoc]

中文:
定理 vecMul_vecMulVec
  条件: [有限类型 m] (u v : m -> α) (w : n -> α)
  证明: by
  ext i
  simp [vecMul, dotProduct, vecMulVec, Finset.sum_mul, mul_assoc]

Depends on / 依赖: Finset, Finset.sum_mul, dotProduct, mul_assoc, sum_mul, vecMul, vecMulVec
-/
theorem vecMul_vecMulVec [Fintype m] (u v : m -> α) (w : n -> α) :
    u ᵥ* vecMulVec v w = (u ⬝ᵥ v) • w := by
  ext i
  simp [vecMul, dotProduct, vecMulVec, Finset.sum_mul, mul_assoc]

/--
theorem `vecMulVec_mulVec` / 定理 `vecMulVec_mulVec`

English:
theorem vecMulVec_mulVec
  given: [Fintype n] (u : m -> α) (v w : n -> α)
  proof: by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_assoc]

中文:
定理 vecMulVec_mulVec
  条件: [有限类型 n] (u : m -> α) (v w : n -> α)
  证明: by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, dotProduct, mulVec, mul_assoc, mul_sum, vecMulVec
-/
theorem vecMulVec_mulVec [Fintype n] (u : m -> α) (v w : n -> α) :
    vecMulVec u v *ᵥ w = MulOpposite.op (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_assoc]

/--
theorem `mul_vecMulVec` / 定理 `mul_vecMulVec`

English:
theorem mul_vecMulVec
  given: [Fintype m] (M : Matrix l m α) (x : m -> α) (y : n -> α)
  proof: by
  ext
  simp_rw [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

中文:
定理 mul_vecMulVec
  条件: [有限类型 m] (M : 矩阵 l m α) (x : m -> α) (y : n -> α)
  证明: by
  ext
  simp_rw [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

Depends on / 依赖: Finset, Finset.sum_mul, dotProduct, mulVec, mul_apply, mul_assoc, simp_rw, sum_mul, vecMulVec_apply
-/
theorem mul_vecMulVec [Fintype m] (M : Matrix l m α) (x : m -> α) (y : n -> α) :
    M * vecMulVec x y = vecMulVec (M *ᵥ x) y := by
  ext
  simp_rw [mul_apply, vecMulVec_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/--
theorem `vecMulVec_mul` / 定理 `vecMulVec_mul`

English:
theorem vecMulVec_mul
  given: [Fintype m] (x : l -> α) (y : m -> α) (M : Matrix m n α)
  proof: by
  ext
  simp_rw [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

中文:
定理 vecMulVec_mul
  条件: [有限类型 m] (x : l -> α) (y : m -> α) (M : 矩阵 m n α)
  证明: by
  ext
  simp_rw [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, dotProduct, mul_apply, mul_assoc, mul_sum, simp_rw, vecMul, vecMulVec_apply
-/
theorem vecMulVec_mul [Fintype m] (x : l -> α) (y : m -> α) (M : Matrix m n α) :
    vecMulVec x y * M = vecMulVec x (y ᵥ* M) := by
  ext
  simp_rw [mul_apply, vecMulVec_apply, vecMul, dotProduct, Finset.mul_sum, mul_assoc]

/--
theorem `vecMulVec_mul_vecMulVec` / 定理 `vecMulVec_mul_vecMulVec`

English:
theorem vecMulVec_mul_vecMulVec
  given: [Fintype m] (u : l -> α) (v w : m -> α) (x : n -> α)
  proof: by
  rw [vecMulVec_mul]; rw [vecMul_vecMulVec]

中文:
定理 vecMulVec_mul_vecMulVec
  条件: [有限类型 m] (u : l -> α) (v w : m -> α) (x : n -> α)
  证明: by
  rw [vecMulVec_mul]; rw [vecMul_vecMulVec]

Depends on / 依赖: vecMulVec_mul, vecMul_vecMulVec
-/
theorem vecMulVec_mul_vecMulVec [Fintype m] (u : l -> α) (v w : m -> α) (x : n -> α) :
    vecMulVec u v * vecMulVec w x = vecMulVec u ((v ⬝ᵥ w) • x) := by
  rw [vecMulVec_mul]; rw [vecMul_vecMulVec]

/--
lemma `mul_right_injective_iff_mulVec_injective` / 引理 `mul_right_injective_iff_mulVec_injective`

English:
lemma mul_right_injective_iff_mulVec_injective
  given: [Fintype m] [Nonempty n] {A : Matrix l m α}
  proof: by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_col fun j => ha congr(($hBC).col j)⟩
  inhabit n
  -- `replicateRow` is not available yet
  suffices (of fun i j => v i) = (of fun i j => w i) from
    funext fun i => congrFun₂ this i (default : n)
exact ha ext fun _ _ => congrFun hvw _

中文:
引理 mul_right_injective_iff_mulVec_injective
  条件: [有限类型 m] [非空 n] {A : 矩阵 l m α}
  证明: by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_col fun j => ha congr(($hBC).col j)⟩
  inhabit n
  -- `replicateRow` is not available yet
  suffices (of fun i j => v i) = (of fun i j => w i) from
    funext fun i => congrFun₂ this i (default : n)
exact ha ext fun _ _ => congrFun hvw _

Depends on / 依赖: ext_col, inhabit
-/
lemma mul_right_injective_iff_mulVec_injective [Fintype m] [Nonempty n] {A : Matrix l m α} :
    Function.Injective (fun B : Matrix m n α => A * B) ↔ Function.Injective A.mulVec := by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_col fun j => ha congr(($hBC).col j)⟩
  inhabit n
  -- `replicateRow` is not available yet
  suffices (of fun i j => v i) = (of fun i j => w i) from
    funext fun i => congrFun₂ this i (default : n)
exact ha ext fun _ _ => congrFun hvw _

/--
lemma `mul_left_injective_iff_vecMul_injective` / 引理 `mul_left_injective_iff_vecMul_injective`

English:
lemma mul_left_injective_iff_vecMul_injective
  given: [Nonempty l] [Fintype m] {A : Matrix m n α}
  proof: by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_row fun i => ha congr(($hBC).row i)⟩
  inhabit l
  -- `replicateCol` is not available yet
  suffices (of fun i j => v j) = (of fun i j => w j) from
    funext fun j => congrFun₂ this (default : l) j
exact ha ext fun _ _ => congrFun hvw _

中文:
引理 mul_left_injective_iff_vecMul_injective
  条件: [非空 l] [有限类型 m] {A : 矩阵 m n α}
  证明: by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_row fun i => ha congr(($hBC).row i)⟩
  inhabit l
  -- `replicateCol` is not available yet
  suffices (of fun i j => v j) = (of fun i j => w j) from
    funext fun j => congrFun₂ this (default : l) j
exact ha ext fun _ _ => congrFun hvw _

Depends on / 依赖: ext_row, inhabit
-/
lemma mul_left_injective_iff_vecMul_injective [Nonempty l] [Fintype m] {A : Matrix m n α} :
    Function.Injective (fun B : Matrix l m α => B * A) ↔ Function.Injective A.vecMul := by
  refine ⟨fun ha v w hvw => ?_, fun ha B C hBC => ext_row fun i => ha congr(($hBC).row i)⟩
  inhabit l
  -- `replicateCol` is not available yet
  suffices (of fun i j => v j) = (of fun i j => w j) from
    funext fun j => congrFun₂ this (default : l) j
exact ha ext fun _ _ => congrFun hvw _

/--
lemma `isLeftRegular_iff_mulVec_injective` / 引理 `isLeftRegular_iff_mulVec_injective`

English:
lemma isLeftRegular_iff_mulVec_injective
  given: [Fintype m] {A : Matrix m m α}
  proof: by
  cases isEmpty_or_nonempty m
  · simp [IsLeftRegular, Function.injective_of_subsingleton]
  exact mul_right_injective_iff_mulVec_injective

中文:
引理 isLeftRegular_iff_mulVec_injective
  条件: [有限类型 m] {A : 矩阵 m m α}
  证明: by
  cases isEmpty_or_nonempty m
  · simp [IsLeftRegular, Function.injective_of_subsingleton]
  exact mul_right_injective_iff_mulVec_injective

Depends on / 依赖: Function, Function.injective_of_subsingleton, IsLeftRegular, injective_of_subsingleton, isEmpty_or_nonempty, mul_right_injective_iff_mulVec_injective
-/
lemma isLeftRegular_iff_mulVec_injective [Fintype m] {A : Matrix m m α} :
    IsLeftRegular A ↔ Function.Injective A.mulVec := by
  cases isEmpty_or_nonempty m
  · simp [IsLeftRegular, Function.injective_of_subsingleton]
  exact mul_right_injective_iff_mulVec_injective

/--
lemma `isRightRegular_iff_vecMul_injective` / 引理 `isRightRegular_iff_vecMul_injective`

English:
lemma isRightRegular_iff_vecMul_injective
  given: [Fintype m] {A : Matrix m m α}
  proof: by
  cases isEmpty_or_nonempty m
  · simp [IsRightRegular, Function.injective_of_subsingleton]
  exact mul_left_injective_iff_vecMul_injective

中文:
引理 isRightRegular_iff_vecMul_injective
  条件: [有限类型 m] {A : 矩阵 m m α}
  证明: by
  cases isEmpty_or_nonempty m
  · simp [IsRightRegular, Function.injective_of_subsingleton]
  exact mul_left_injective_iff_vecMul_injective

Depends on / 依赖: Function, Function.injective_of_subsingleton, IsRightRegular, injective_of_subsingleton, isEmpty_or_nonempty, mul_left_injective_iff_vecMul_injective
-/
lemma isRightRegular_iff_vecMul_injective [Fintype m] {A : Matrix m m α} :
    IsRightRegular A ↔ Function.Injective A.vecMul := by
  cases isEmpty_or_nonempty m
  · simp [IsRightRegular, Function.injective_of_subsingleton]
  exact mul_left_injective_iff_vecMul_injective

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring α]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mulVec_one` / 定理 `mulVec_one`

English:
theorem mulVec_one
  given: [Fintype n] (A : Matrix m n α)
  statement: A *ᵥ 1 = ∑ j, Aᵀ j
  proof: by
  ext; simp [mulVec, dotProduct]

中文:
定理 mulVec_one
  条件: [有限类型 n] (A : 矩阵 m n α)
  结论: A *ᵥ 1 = ∑ j, Aᵀ j
  证明: by
  ext; simp [mulVec, dotProduct]

Depends on / 依赖: dotProduct, mulVec
-/
theorem mulVec_one [Fintype n] (A : Matrix m n α) : A *ᵥ 1 = ∑ j, Aᵀ j := by
  ext; simp [mulVec, dotProduct]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `one_vecMul` / 定理 `one_vecMul`

English:
theorem one_vecMul
  given: [Fintype m] (A : Matrix m n α)
  statement: 1 ᵥ* A = ∑ i, A i
  proof: by
  ext; simp [vecMul, dotProduct]

中文:
定理 one_vecMul
  条件: [有限类型 m] (A : 矩阵 m n α)
  结论: 1 ᵥ* A = ∑ i, A i
  证明: by
  ext; simp [vecMul, dotProduct]

Depends on / 依赖: dotProduct, vecMul
-/
theorem one_vecMul [Fintype m] (A : Matrix m n α) : 1 ᵥ* A = ∑ i, A i := by
  ext; simp [vecMul, dotProduct]

/--
lemma `ext_of_mulVec_single` / 引理 `ext_of_mulVec_single`

English:
lemma ext_of_mulVec_single
  statement: [DecidableEq n] [Fintype n] {M N : Matrix m n α}
  proof: by
  ext i j
  simp_rw [mulVec_single_one] at h
  exact congrFun (h j) i

中文:
引理 ext_of_mulVec_single
  结论: [DecidableEq n] [有限类型 n] {M N : 矩阵 m n α}
  证明: by
  ext i j
  simp_rw [mulVec_single_one] at h
  exact congrFun (h j) i

Depends on / 依赖: mulVec_single_one, simp_rw
-/
lemma ext_of_mulVec_single [DecidableEq n] [Fintype n] {M N : Matrix m n α}
    (h : forall i, M *ᵥ Pi.single i 1 = N *ᵥ Pi.single i 1) :
    M = N := by
  ext i j
  simp_rw [mulVec_single_one] at h
  exact congrFun (h j) i

/--
lemma `ext_of_single_vecMul` / 引理 `ext_of_single_vecMul`

English:
lemma ext_of_single_vecMul
  statement: [DecidableEq m] [Fintype m] {M N : Matrix m n α}
  proof: by
  ext i j
  simp_rw [single_one_vecMul] at h
  exact congrFun (h i) j

中文:
引理 ext_of_single_vecMul
  结论: [DecidableEq m] [有限类型 m] {M N : 矩阵 m n α}
  证明: by
  ext i j
  simp_rw [single_one_vecMul] at h
  exact congrFun (h i) j

Depends on / 依赖: simp_rw, single_one_vecMul
-/
lemma ext_of_single_vecMul [DecidableEq m] [Fintype m] {M N : Matrix m n α}
    (h : forall i, Pi.single i 1 ᵥ* M = Pi.single i 1 ᵥ* N) :
    M = N := by
  ext i j
  simp_rw [single_one_vecMul] at h
  exact congrFun (h i) j

/--
theorem `mulVec_injective` / 定理 `mulVec_injective`

English:
theorem mulVec_injective
  given: [Fintype n]
  statement: (mulVec : Matrix m n α -> _).Injective
  proof: by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single j 1) i

中文:
定理 mulVec_injective
  条件: [有限类型 n]
  结论: (mulVec : 矩阵 m n α -> _).单射
  证明: by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single j 1) i

Depends on / 依赖: Pi.single, classical, single
-/
theorem mulVec_injective [Fintype n] : (mulVec : Matrix m n α -> _).Injective := by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single j 1) i

/--
theorem `ext_iff_mulVec` / 定理 `ext_iff_mulVec`

English:
theorem ext_iff_mulVec
  given: [Fintype n] {A B : Matrix m n α}
  statement: A = B ↔ forall v, A *ᵥ v = B *ᵥ v
  proof: mulVec_injective.eq_iff.symm.trans funext_iff

中文:
定理 ext_iff_mulVec
  条件: [有限类型 n] {A B : 矩阵 m n α}
  结论: A = B ↔ 对任意 v, A *ᵥ v = B *ᵥ v
  证明: mulVec_injective.eq_iff.symm.trans funext_iff

Depends on / 依赖: eq_iff, funext_iff, mulVec_injective, mulVec_injective.eq_iff.symm.trans
-/
theorem ext_iff_mulVec [Fintype n] {A B : Matrix m n α} : A = B ↔ forall v, A *ᵥ v = B *ᵥ v :=
  mulVec_injective.eq_iff.symm.trans funext_iff

/--
theorem `vecMul_injective` / 定理 `vecMul_injective`

English:
theorem vecMul_injective
  given: [Fintype m]
  statement: (·.vecMul : Matrix m n α -> _).Injective
  proof: by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single i 1) j

中文:
定理 vecMul_injective
  条件: [有限类型 m]
  结论: (·.vecMul : 矩阵 m n α -> _).单射
  证明: by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single i 1) j

Depends on / 依赖: Pi.single, classical, single
-/
theorem vecMul_injective [Fintype m] : (·.vecMul : Matrix m n α -> _).Injective := by
  intro A B h
  ext i j
  classical
  simpa using congrFun₂ h (Pi.single i 1) j

/--
theorem `ext_iff_vecMul` / 定理 `ext_iff_vecMul`

English:
theorem ext_iff_vecMul
  given: [Fintype m] {A B : Matrix m n α}
  statement: A = B ↔ forall v, v ᵥ* A = v ᵥ* B
  proof: vecMul_injective.eq_iff.symm.trans funext_iff

中文:
定理 ext_iff_vecMul
  条件: [有限类型 m] {A B : 矩阵 m n α}
  结论: A = B ↔ 对任意 v, v ᵥ* A = v ᵥ* B
  证明: vecMul_injective.eq_iff.symm.trans funext_iff

Depends on / 依赖: eq_iff, funext_iff, vecMul_injective, vecMul_injective.eq_iff.symm.trans
-/
theorem ext_iff_vecMul [Fintype m] {A B : Matrix m n α} : A = B ↔ forall v, v ᵥ* A = v ᵥ* B :=
  vecMul_injective.eq_iff.symm.trans funext_iff

variable [Fintype m] [DecidableEq m]

@[simp]
/--
theorem `one_mulVec` / 定理 `one_mulVec`

English:
theorem one_mulVec
  given: (v : m -> α)
  statement: 1 *ᵥ v = v
  proof: by
  ext
  rw [← diagonal_one]; rw [mulVec_diagonal]; rw [one_mul]

@[simp]

中文:
定理 one_mulVec
  条件: (v : m -> α)
  结论: 1 *ᵥ v = v
  证明: by
  ext
  rw [← diagonal_one]; rw [mulVec_diagonal]; rw [one_mul]

@[simp]

Depends on / 依赖: diagonal_one, mulVec_diagonal, one_mul
-/
theorem one_mulVec (v : m -> α) : 1 *ᵥ v = v := by
  ext
  rw [← diagonal_one]; rw [mulVec_diagonal]; rw [one_mul]

@[simp]
/--
theorem `vecMul_one` / 定理 `vecMul_one`

English:
theorem vecMul_one
  given: (v : m -> α)
  statement: v ᵥ* 1 = v
  proof: by
  ext
  rw [← diagonal_one]; rw [vecMul_diagonal]; rw [mul_one]

@[simp]

中文:
定理 vecMul_one
  条件: (v : m -> α)
  结论: v ᵥ* 1 = v
  证明: by
  ext
  rw [← diagonal_one]; rw [vecMul_diagonal]; rw [mul_one]

@[simp]

Depends on / 依赖: diagonal_one, mul_one, vecMul_diagonal
-/
theorem vecMul_one (v : m -> α) : v ᵥ* 1 = v := by
  ext
  rw [← diagonal_one]; rw [vecMul_diagonal]; rw [mul_one]

@[simp]
/--
theorem `diagonal_const_mulVec` / 定理 `diagonal_const_mulVec`

English:
theorem diagonal_const_mulVec
  given: (x : α) (v : m -> α)
  proof: by
  ext; simp [mulVec_diagonal]

@[simp]

中文:
定理 diagonal_const_mulVec
  条件: (x : α) (v : m -> α)
  证明: by
  ext; simp [mulVec_diagonal]

@[simp]

Depends on / 依赖: mulVec_diagonal
-/
theorem diagonal_const_mulVec (x : α) (v : m -> α) :
    (diagonal fun _ => x) *ᵥ v = x • v := by
  ext; simp [mulVec_diagonal]

@[simp]
/--
theorem `vecMul_diagonal_const` / 定理 `vecMul_diagonal_const`

English:
theorem vecMul_diagonal_const
  given: (x : α) (v : m -> α)
  proof: by
  ext; simp [vecMul_diagonal]

@[simp]

中文:
定理 vecMul_diagonal_const
  条件: (x : α) (v : m -> α)
  证明: by
  ext; simp [vecMul_diagonal]

@[simp]

Depends on / 依赖: vecMul_diagonal
-/
theorem vecMul_diagonal_const (x : α) (v : m -> α) :
    v ᵥ* (diagonal fun _ => x) = MulOpposite.op x • v := by
  ext; simp [vecMul_diagonal]

@[simp]
/--
theorem `natCast_mulVec` / 定理 `natCast_mulVec`

English:
theorem natCast_mulVec
  given: (x : Nat) (v : m -> α)
  statement: x *ᵥ v = (x : α) • v
  proof: diagonal_const_mulVec _ _

@[simp]

中文:
定理 natCast_mulVec
  条件: (x : 自然数) (v : m -> α)
  结论: x *ᵥ v = (x : α) • v
  证明: diagonal_const_mulVec _ _

@[simp]

Depends on / 依赖: diagonal_const_mulVec
-/
theorem natCast_mulVec (x : Nat) (v : m -> α) : x *ᵥ v = (x : α) • v :=
  diagonal_const_mulVec _ _

@[simp]
/--
theorem `vecMul_natCast` / 定理 `vecMul_natCast`

English:
theorem vecMul_natCast
  given: (x : Nat) (v : m -> α)
  statement: v ᵥ* x = MulOpposite.op (x : α) • v
  proof: vecMul_diagonal_const _ _


@[simp]

中文:
定理 vecMul_natCast
  条件: (x : 自然数) (v : m -> α)
  结论: v ᵥ* x = MulOpposite.op (x : α) • v
  证明: vecMul_diagonal_const _ _


@[simp]

Depends on / 依赖: vecMul_diagonal_const
-/
theorem vecMul_natCast (x : Nat) (v : m -> α) : v ᵥ* x = MulOpposite.op (x : α) • v :=
  vecMul_diagonal_const _ _


@[simp]
/--
theorem `ofNat_mulVec` / 定理 `ofNat_mulVec`

English:
theorem ofNat_mulVec
  given: (x : Nat) [x.AtLeastTwo] (v : m -> α)
  proof: natCast_mulVec _ _

@[simp]

中文:
定理 of自然数_mulVec
  条件: (x : 自然数) [x.AtLeastTwo] (v : m -> α)
  证明: natCast_mulVec _ _

@[simp]

Depends on / 依赖: natCast_mulVec
-/
theorem ofNat_mulVec (x : Nat) [x.AtLeastTwo] (v : m -> α) :
    ofNat(x) *ᵥ v = (OfNat.ofNat x : α) • v :=
  natCast_mulVec _ _

@[simp]
/--
theorem `vecMul_ofNat` / 定理 `vecMul_ofNat`

English:
theorem vecMul_ofNat
  given: (x : Nat) [x.AtLeastTwo] (v : m -> α)
  proof: vecMul_natCast _ _

中文:
定理 vecMul_of自然数
  条件: (x : 自然数) [x.AtLeastTwo] (v : m -> α)
  证明: vecMul_natCast _ _

Depends on / 依赖: vecMul_natCast
-/
theorem vecMul_ofNat (x : Nat) [x.AtLeastTwo] (v : m -> α) :
    v ᵥ* ofNat(x) = MulOpposite.op (OfNat.ofNat x : α) • v :=
  vecMul_natCast _ _

end NonAssocSemiring

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/--
theorem `neg_vecMul` / 定理 `neg_vecMul`

English:
theorem neg_vecMul
  given: [Fintype m] (v : m -> α) (A : Matrix m n α)
  statement: (-v) ᵥ* A = -(v ᵥ* A)
  proof: by
  ext
  apply neg_dotProduct

中文:
定理 neg_vecMul
  条件: [有限类型 m] (v : m -> α) (A : 矩阵 m n α)
  结论: (-v) ᵥ* A = -(v ᵥ* A)
  证明: by
  ext
  apply neg_dotProduct

Depends on / 依赖: neg_dotProduct
-/
theorem neg_vecMul [Fintype m] (v : m -> α) (A : Matrix m n α) : (-v) ᵥ* A = -(v ᵥ* A) := by
  ext
  apply neg_dotProduct

/--
theorem `vecMul_neg` / 定理 `vecMul_neg`

English:
theorem vecMul_neg
  given: [Fintype m] (v : m -> α) (A : Matrix m n α)
  statement: v ᵥ* (-A) = -(v ᵥ* A)
  proof: by
  ext
  apply dotProduct_neg

中文:
定理 vecMul_neg
  条件: [有限类型 m] (v : m -> α) (A : 矩阵 m n α)
  结论: v ᵥ* (-A) = -(v ᵥ* A)
  证明: by
  ext
  apply dotProduct_neg

Depends on / 依赖: dotProduct_neg
-/
theorem vecMul_neg [Fintype m] (v : m -> α) (A : Matrix m n α) : v ᵥ* (-A) = -(v ᵥ* A) := by
  ext
  apply dotProduct_neg

/--
lemma `neg_vecMul_neg` / 引理 `neg_vecMul_neg`

English:
lemma neg_vecMul_neg
  given: [Fintype m] (v : m -> α) (A : Matrix m n α)
  statement: (-v) ᵥ* (-A) = v ᵥ* A
  proof: by
  rw [vecMul_neg]; rw [neg_vecMul]; rw [neg_neg]

中文:
引理 neg_vecMul_neg
  条件: [有限类型 m] (v : m -> α) (A : 矩阵 m n α)
  结论: (-v) ᵥ* (-A) = v ᵥ* A
  证明: by
  rw [vecMul_neg]; rw [neg_vecMul]; rw [neg_neg]

Depends on / 依赖: neg_neg, neg_vecMul, vecMul_neg
-/
lemma neg_vecMul_neg [Fintype m] (v : m -> α) (A : Matrix m n α) : (-v) ᵥ* (-A) = v ᵥ* A := by
  rw [vecMul_neg]; rw [neg_vecMul]; rw [neg_neg]

/--
theorem `neg_mulVec` / 定理 `neg_mulVec`

English:
theorem neg_mulVec
  given: [Fintype n] (v : n -> α) (A : Matrix m n α)
  statement: (-A) *ᵥ v = -(A *ᵥ v)
  proof: by
  ext
  apply neg_dotProduct

中文:
定理 neg_mulVec
  条件: [有限类型 n] (v : n -> α) (A : 矩阵 m n α)
  结论: (-A) *ᵥ v = -(A *ᵥ v)
  证明: by
  ext
  apply neg_dotProduct

Depends on / 依赖: neg_dotProduct
-/
theorem neg_mulVec [Fintype n] (v : n -> α) (A : Matrix m n α) : (-A) *ᵥ v = -(A *ᵥ v) := by
  ext
  apply neg_dotProduct

/--
theorem `mulVec_neg` / 定理 `mulVec_neg`

English:
theorem mulVec_neg
  given: [Fintype n] (v : n -> α) (A : Matrix m n α)
  statement: A *ᵥ (-v) = -(A *ᵥ v)
  proof: by
  ext
  apply dotProduct_neg

中文:
定理 mulVec_neg
  条件: [有限类型 n] (v : n -> α) (A : 矩阵 m n α)
  结论: A *ᵥ (-v) = -(A *ᵥ v)
  证明: by
  ext
  apply dotProduct_neg

Depends on / 依赖: dotProduct_neg
-/
theorem mulVec_neg [Fintype n] (v : n -> α) (A : Matrix m n α) : A *ᵥ (-v) = -(A *ᵥ v) := by
  ext
  apply dotProduct_neg

/--
lemma `neg_mulVec_neg` / 引理 `neg_mulVec_neg`

English:
lemma neg_mulVec_neg
  given: [Fintype n] (v : n -> α) (A : Matrix m n α)
  statement: (-A) *ᵥ (-v) = A *ᵥ v
  proof: by
  rw [mulVec_neg]; rw [neg_mulVec]; rw [neg_neg]

中文:
引理 neg_mulVec_neg
  条件: [有限类型 n] (v : n -> α) (A : 矩阵 m n α)
  结论: (-A) *ᵥ (-v) = A *ᵥ v
  证明: by
  rw [mulVec_neg]; rw [neg_mulVec]; rw [neg_neg]

Depends on / 依赖: mulVec_neg, neg_mulVec, neg_neg
-/
lemma neg_mulVec_neg [Fintype n] (v : n -> α) (A : Matrix m n α) : (-A) *ᵥ (-v) = A *ᵥ v := by
  rw [mulVec_neg]; rw [neg_mulVec]; rw [neg_neg]

/--
theorem `mulVec_sub` / 定理 `mulVec_sub`

English:
theorem mulVec_sub
  given: [Fintype n] (A : Matrix m n α) (x y : n -> α)
  proof: by
  ext
  apply dotProduct_sub

中文:
定理 mulVec_sub
  条件: [有限类型 n] (A : 矩阵 m n α) (x y : n -> α)
  证明: by
  ext
  apply dotProduct_sub

Depends on / 依赖: dotProduct_sub
-/
theorem mulVec_sub [Fintype n] (A : Matrix m n α) (x y : n -> α) :
    A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y := by
  ext
  apply dotProduct_sub

/--
theorem `sub_mulVec` / 定理 `sub_mulVec`

English:
theorem sub_mulVec
  given: [Fintype n] (A B : Matrix m n α) (x : n -> α)
  proof: by simp [sub_eq_add_neg, add_mulVec, neg_mulVec]

中文:
定理 sub_mulVec
  条件: [有限类型 n] (A B : 矩阵 m n α) (x : n -> α)
  证明: by simp [sub_eq_add_neg, add_mulVec, neg_mulVec]

Depends on / 依赖: add_mulVec, neg_mulVec, sub_eq_add_neg
-/
theorem sub_mulVec [Fintype n] (A B : Matrix m n α) (x : n -> α) :
    (A - B) *ᵥ x = A *ᵥ x - B *ᵥ x := by simp [sub_eq_add_neg, add_mulVec, neg_mulVec]

/--
theorem `vecMul_sub` / 定理 `vecMul_sub`

English:
theorem vecMul_sub
  given: [Fintype m] (A B : Matrix m n α) (x : m -> α)
  proof: by simp [sub_eq_add_neg, vecMul_add, vecMul_neg]

中文:
定理 vecMul_sub
  条件: [有限类型 m] (A B : 矩阵 m n α) (x : m -> α)
  证明: by simp [sub_eq_add_neg, vecMul_add, vecMul_neg]

Depends on / 依赖: sub_eq_add_neg, vecMul_add, vecMul_neg
-/
theorem vecMul_sub [Fintype m] (A B : Matrix m n α) (x : m -> α) :
    x ᵥ* (A - B) = x ᵥ* A - x ᵥ* B := by simp [sub_eq_add_neg, vecMul_add, vecMul_neg]

/--
theorem `sub_vecMul` / 定理 `sub_vecMul`

English:
theorem sub_vecMul
  given: [Fintype m] (A : Matrix m n α) (x y : m -> α)
  proof: by
  ext
  apply sub_dotProduct

中文:
定理 sub_vecMul
  条件: [有限类型 m] (A : 矩阵 m n α) (x y : m -> α)
  证明: by
  ext
  apply sub_dotProduct

Depends on / 依赖: sub_dotProduct
-/
theorem sub_vecMul [Fintype m] (A : Matrix m n α) (x y : m -> α) :
    (x - y) ᵥ* A = x ᵥ* A - y ᵥ* A := by
  ext
  apply sub_dotProduct

/--
theorem `sub_vecMulVec` / 定理 `sub_vecMulVec`

English:
theorem sub_vecMulVec
  given: (w₁ w₂ : m -> α) (v : n -> α)
  proof: ext fun _ _ => sub_mul _ _ _

中文:
定理 sub_vecMulVec
  条件: (w₁ w₂ : m -> α) (v : n -> α)
  证明: ext fun _ _ => sub_mul _ _ _

Depends on / 依赖: sub_mul
-/
theorem sub_vecMulVec (w₁ w₂ : m -> α) (v : n -> α) :
    vecMulVec (w₁ - w₂) v = vecMulVec w₁ v - vecMulVec w₂ v :=
  ext fun _ _ => sub_mul _ _ _

/--
theorem `vecMulVec_sub` / 定理 `vecMulVec_sub`

English:
theorem vecMulVec_sub
  given: (w : m -> α) (v₁ v₂ : n -> α)
  proof: ext fun _ _ => mul_sub _ _ _

中文:
定理 vecMulVec_sub
  条件: (w : m -> α) (v₁ v₂ : n -> α)
  证明: ext fun _ _ => mul_sub _ _ _

Depends on / 依赖: mul_sub
-/
theorem vecMulVec_sub (w : m -> α) (v₁ v₂ : n -> α) :
    vecMulVec w (v₁ - v₂) = vecMulVec w v₁ - vecMulVec w v₂ :=
  ext fun _ _ => mul_sub _ _ _

end NonUnitalNonAssocRing

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

/--
theorem `mulVec_transpose` / 定理 `mulVec_transpose`

English:
theorem mulVec_transpose
  given: [Fintype m] (A : Matrix m n α) (x : m -> α)
  statement: Aᵀ *ᵥ x = x ᵥ* A
  proof: by
  ext
  apply dotProduct_comm

中文:
定理 mulVec_transpose
  条件: [有限类型 m] (A : 矩阵 m n α) (x : m -> α)
  结论: Aᵀ *ᵥ x = x ᵥ* A
  证明: by
  ext
  apply dotProduct_comm

Depends on / 依赖: dotProduct_comm
-/
theorem mulVec_transpose [Fintype m] (A : Matrix m n α) (x : m -> α) : Aᵀ *ᵥ x = x ᵥ* A := by
  ext
  apply dotProduct_comm

/--
theorem `vecMul_transpose` / 定理 `vecMul_transpose`

English:
theorem vecMul_transpose
  given: [Fintype n] (A : Matrix m n α) (x : n -> α)
  statement: x ᵥ* Aᵀ = A *ᵥ x
  proof: by
  ext
  apply dotProduct_comm

中文:
定理 vecMul_transpose
  条件: [有限类型 n] (A : 矩阵 m n α) (x : n -> α)
  结论: x ᵥ* Aᵀ = A *ᵥ x
  证明: by
  ext
  apply dotProduct_comm

Depends on / 依赖: dotProduct_comm
-/
theorem vecMul_transpose [Fintype n] (A : Matrix m n α) (x : n -> α) : x ᵥ* Aᵀ = A *ᵥ x := by
  ext
  apply dotProduct_comm

/--
theorem `dotProduct_transpose_mulVec` / 定理 `dotProduct_transpose_mulVec`

English:
theorem dotProduct_transpose_mulVec
  statement: [Fintype m] [Fintype n] (A : Matrix m n α) (x : n -> α)
  proof: by
  rw [dotProduct_mulVec]; rw [dotProduct_comm]; rw [vecMul_transpose]

中文:
定理 dotProduct_transpose_mulVec
  结论: [有限类型 m] [有限类型 n] (A : 矩阵 m n α) (x : n -> α)
  证明: by
  rw [dotProduct_mulVec]; rw [dotProduct_comm]; rw [vecMul_transpose]

Depends on / 依赖: dotProduct_comm, dotProduct_mulVec, vecMul_transpose
-/
theorem dotProduct_transpose_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (x : n -> α)
    (y : m -> α) : x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  rw [dotProduct_mulVec]; rw [dotProduct_comm]; rw [vecMul_transpose]

/--
theorem `dotProduct_vecMul_transpose` / 定理 `dotProduct_vecMul_transpose`

English:
theorem dotProduct_vecMul_transpose
  statement: [Fintype m] [Fintype n] (A : Matrix m n α) (x : n -> α)
  proof: by
  simpa [dotProduct_mulVec] using dotProduct_transpose_mulVec (A := A) (x := x) (y := y)

中文:
定理 dotProduct_vecMul_transpose
  结论: [有限类型 m] [有限类型 n] (A : 矩阵 m n α) (x : n -> α)
  证明: by
  simpa [dotProduct_mulVec] using dotProduct_transpose_mulVec (A := A) (x := x) (y := y)

Depends on / 依赖: dotProduct_mulVec, dotProduct_transpose_mulVec
-/
theorem dotProduct_vecMul_transpose [Fintype m] [Fintype n] (A : Matrix m n α) (x : n -> α)
    (y : m -> α) : (x ᵥ* Aᵀ) ⬝ᵥ y = (y ᵥ* A) ⬝ᵥ x := by
  simpa [dotProduct_mulVec] using dotProduct_transpose_mulVec (A := A) (x := x) (y := y)

/--
theorem `mulVec_vecMul` / 定理 `mulVec_vecMul`

English:
theorem mulVec_vecMul
  given: [Fintype n] [Fintype o] (A : Matrix m n α) (B : Matrix o n α) (x : o -> α)
  proof: by rw [← mulVec_mulVec, mulVec_transpose]

中文:
定理 mulVec_vecMul
  条件: [有限类型 n] [有限类型 o] (A : 矩阵 m n α) (B : 矩阵 o n α) (x : o -> α)
  证明: by rw [← mulVec_mulVec, mulVec_transpose]

Depends on / 依赖: mulVec_mulVec, mulVec_transpose
-/
theorem mulVec_vecMul [Fintype n] [Fintype o] (A : Matrix m n α) (B : Matrix o n α) (x : o -> α) :
    A *ᵥ (x ᵥ* B) = (A * Bᵀ) *ᵥ x := by rw [← mulVec_mulVec, mulVec_transpose]

/--
theorem `vecMul_mulVec` / 定理 `vecMul_mulVec`

English:
theorem vecMul_mulVec
  given: [Fintype m] [Fintype n] (A : Matrix m n α) (B : Matrix m o α) (x : n -> α)
  proof: by rw [← vecMul_vecMul, vecMul_transpose]

中文:
定理 vecMul_mulVec
  条件: [有限类型 m] [有限类型 n] (A : 矩阵 m n α) (B : 矩阵 m o α) (x : n -> α)
  证明: by rw [← vecMul_vecMul, vecMul_transpose]

Depends on / 依赖: vecMul_transpose, vecMul_vecMul
-/
theorem vecMul_mulVec [Fintype m] [Fintype n] (A : Matrix m n α) (B : Matrix m o α) (x : n -> α) :
    (A *ᵥ x) ᵥ* B = x ᵥ* (Aᵀ * B) := by rw [← vecMul_vecMul, vecMul_transpose]

end NonUnitalCommSemiring

section Semiring

variable [Semiring R]

/--
lemma `mulVec_injective_of_isUnit` / 引理 `mulVec_injective_of_isUnit`

English:
lemma mulVec_injective_of_isUnit
  statement: [Fintype m] [DecidableEq m] {A : Matrix m m R}
  proof: isLeftRegular_iff_mulVec_injective.1 ha.isRegular.left

中文:
引理 mulVec_injective_of_isUnit
  结论: [有限类型 m] [DecidableEq m] {A : 矩阵 m m R}
  证明: isLeftRegular_iff_mulVec_injective.1 ha.isRegular.left

Depends on / 依赖: ha.isRegular.left, isLeftRegular_iff_mulVec_injective, isRegular
-/
lemma mulVec_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R}
    (ha : IsUnit A) : Function.Injective A.mulVec :=
  isLeftRegular_iff_mulVec_injective.1 ha.isRegular.left

/--
lemma `vecMul_injective_of_isUnit` / 引理 `vecMul_injective_of_isUnit`

English:
lemma vecMul_injective_of_isUnit
  statement: [Fintype m] [DecidableEq m] {A : Matrix m m R}
  proof: isRightRegular_iff_vecMul_injective.1 ha.isRegular.right

中文:
引理 vecMul_injective_of_isUnit
  结论: [有限类型 m] [DecidableEq m] {A : 矩阵 m m R}
  证明: isRightRegular_iff_vecMul_injective.1 ha.isRegular.right

Depends on / 依赖: ha.isRegular.right, isRegular, isRightRegular_iff_vecMul_injective
-/
lemma vecMul_injective_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m R}
    (ha : IsUnit A) : Function.Injective A.vecMul :=
  isRightRegular_iff_vecMul_injective.1 ha.isRegular.right

/--
lemma `pow_row_eq_zero_of_le` / 引理 `pow_row_eq_zero_of_le`

English:
lemma pow_row_eq_zero_of_le
  statement: [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : Nat} {i : n}
  proof: by
  replace h' : l = k + (l - k) := by lia
  rw [← single_one_vecMul] at h ⊢
  rw [h']; rw [pow_add]; rw [← vecMul_vecMul]; rw [h]; rw [zero_vecMul]

中文:
引理 pow_row_eq_zero_of_le
  结论: [有限类型 n] [DecidableEq n] {M : 矩阵 n n R} {k l : 自然数} {i : n}
  证明: by
  replace h' : l = k + (l - k) := by lia
  rw [← single_one_vecMul] at h ⊢
  rw [h']; rw [pow_add]; rw [← vecMul_vecMul]; rw [h]; rw [zero_vecMul]

Depends on / 依赖: pow_add, replace, single_one_vecMul, vecMul_vecMul, zero_vecMul
-/
lemma pow_row_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : Nat} {i : n}
    (h : (M ^ k).row i = 0) (h' : k <= l) :
    (M ^ l).row i = 0 := by
  replace h' : l = k + (l - k) := by lia
  rw [← single_one_vecMul] at h ⊢
  rw [h']; rw [pow_add]; rw [← vecMul_vecMul]; rw [h]; rw [zero_vecMul]

/--
lemma `pow_col_eq_zero_of_le` / 引理 `pow_col_eq_zero_of_le`

English:
lemma pow_col_eq_zero_of_le
  statement: [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : Nat} {i : n}
  proof: by
  replace h' : l = (l - k) + k := by lia
  rw [← mulVec_single_one] at h ⊢
  rw [h']; rw [pow_add]; rw [← mulVec_mulVec]; rw [h]; rw [mulVec_zero]

中文:
引理 pow_col_eq_zero_of_le
  结论: [有限类型 n] [DecidableEq n] {M : 矩阵 n n R} {k l : 自然数} {i : n}
  证明: by
  replace h' : l = (l - k) + k := by lia
  rw [← mulVec_single_one] at h ⊢
  rw [h']; rw [pow_add]; rw [← mulVec_mulVec]; rw [h]; rw [mulVec_zero]

Depends on / 依赖: mulVec_mulVec, mulVec_single_one, mulVec_zero, pow_add, replace
-/
lemma pow_col_eq_zero_of_le [Fintype n] [DecidableEq n] {M : Matrix n n R} {k l : Nat} {i : n}
    (h : (M ^ k).col i = 0) (h' : k <= l) :
    (M ^ l).col i = 0 := by
  replace h' : l = (l - k) + k := by lia
  rw [← mulVec_single_one] at h ⊢
  rw [h']; rw [pow_add]; rw [← mulVec_mulVec]; rw [h]; rw [mulVec_zero]

end Semiring

section NonAssocRing

variable [NonAssocRing α]

variable [Fintype m] [DecidableEq m]

@[simp]
/--
theorem `intCast_mulVec` / 定理 `intCast_mulVec`

English:
theorem intCast_mulVec
  given: (x : Int) (v : m -> α)
  statement: x *ᵥ v = (x : α) • v
  proof: diagonal_const_mulVec _ _

@[simp]

中文:
定理 intCast_mulVec
  条件: (x : 整数) (v : m -> α)
  结论: x *ᵥ v = (x : α) • v
  证明: diagonal_const_mulVec _ _

@[simp]

Depends on / 依赖: diagonal_const_mulVec
-/
theorem intCast_mulVec (x : Int) (v : m -> α) : x *ᵥ v = (x : α) • v :=
  diagonal_const_mulVec _ _

@[simp]
/--
theorem `vecMul_intCast` / 定理 `vecMul_intCast`

English:
theorem vecMul_intCast
  given: (x : Int) (v : m -> α)
  statement: v ᵥ* x = MulOpposite.op (x : α) • v
  proof: vecMul_diagonal_const _ _

中文:
定理 vecMul_intCast
  条件: (x : 整数) (v : m -> α)
  结论: v ᵥ* x = MulOpposite.op (x : α) • v
  证明: vecMul_diagonal_const _ _

Depends on / 依赖: vecMul_diagonal_const
-/
theorem vecMul_intCast (x : Int) (v : m -> α) : v ᵥ* x = MulOpposite.op (x : α) • v :=
  vecMul_diagonal_const _ _

end NonAssocRing

section Transpose

open Matrix

@[simp]
/--
theorem `transpose_mul` / 定理 `transpose_mul`

English:
theorem transpose_mul
  statement: [AddCommMonoid α] [CommMagma α] [Fintype n] (M : Matrix m n α)
  proof: by
  ext
  apply dotProduct_comm

中文:
定理 transpose_mul
  结论: [加法交换幺半群 α] [交换原群 α] [有限类型 n] (M : 矩阵 m n α)
  证明: by
  ext
  apply dotProduct_comm

Depends on / 依赖: dotProduct_comm
-/
theorem transpose_mul [AddCommMonoid α] [CommMagma α] [Fintype n] (M : Matrix m n α)
    (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ := by
  ext
  apply dotProduct_comm

end Transpose

/--
theorem `submatrix_mul` / 定理 `submatrix_mul`

English:
theorem submatrix_mul
  statement: [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Type*}
  proof: ext fun _ _ => (he₂.sum_comp _).symm

中文:
定理 submatrix_mul
  结论: [有限类型 n] [有限类型 o] [乘法 α] [加法交换幺半群 α] {p q : 类型}
  证明: ext fun _ _ => (he₂.sum_comp _).symm

Depends on / 依赖: sum_comp
-/
theorem submatrix_mul [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l -> m) (e₂ : o -> n) (e₃ : q -> p)
    (he₂ : Function.Bijective e₂) :
    (M * N).submatrix e₁ e₃ = M.submatrix e₁ e₂ * N.submatrix e₂ e₃ :=
  ext fun _ _ => (he₂.sum_comp _).symm

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/

@[simp]
/--
theorem `submatrix_mul_equiv` / 定理 `submatrix_mul_equiv`

English:
theorem submatrix_mul_equiv
  statement: [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q : Type*}
  proof: (submatrix_mul M N e₁ e₂ e₃ e₂.bijective).symm

中文:
定理 submatrix_mul_equiv
  结论: [有限类型 n] [有限类型 o] [加法交换幺半群 α] [乘法 α] {p q : 类型}
  证明: (submatrix_mul M N e₁ e₂ e₃ e₂.bijective).symm

Depends on / 依赖: bijective, submatrix_mul
-/
theorem submatrix_mul_equiv [Fintype n] [Fintype o] [AddCommMonoid α] [Mul α] {p q : Type*}
    (M : Matrix m n α) (N : Matrix n p α) (e₁ : l -> m) (e₂ : o ≃ n) (e₃ : q -> p) :
    M.submatrix e₁ e₂ * N.submatrix e₂ e₃ = (M * N).submatrix e₁ e₃ :=
  (submatrix_mul M N e₁ e₂ e₃ e₂.bijective).symm

/--
theorem `submatrix_mulVec_equiv` / 定理 `submatrix_mulVec_equiv`

English:
theorem submatrix_mulVec_equiv
  statement: [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
  proof: funext fun _ => Eq.symm (dotProduct_comp_equiv_symm _ _ _)

@[simp]

中文:
定理 submatrix_mulVec_equiv
  结论: [有限类型 n] [有限类型 o] [非幺非结合半环 α]
  证明: funext fun _ => Eq.symm (dotProduct_comp_equiv_symm _ _ _)

@[simp]

Depends on / 依赖: Eq.symm, dotProduct_comp_equiv_symm
-/
theorem submatrix_mulVec_equiv [Fintype n] [Fintype o] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : o -> α) (e₁ : l -> m) (e₂ : o ≃ n) :
    M.submatrix e₁ e₂ *ᵥ v = (M *ᵥ (v ∘ e₂.symm)) ∘ e₁ :=
  funext fun _ => Eq.symm (dotProduct_comp_equiv_symm _ _ _)

@[simp]
/--
theorem `submatrix_id_mul_left` / 定理 `submatrix_id_mul_left`

English:
theorem submatrix_id_mul_left
  statement: [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
  proof: by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

@[simp]

中文:
定理 submatrix_id_mul_left
  结论: [有限类型 n] [有限类型 o] [乘法 α] [加法交换幺半群 α] {p : 类型}
  证明: by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

@[simp]

Depends on / 依赖: bijective, bijective.sum_comp, mul_apply, sum_comp
-/
theorem submatrix_id_mul_left [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
    (M : Matrix m n α) (N : Matrix o p α) (e₁ : l -> m) (e₂ : n ≃ o) :
    M.submatrix e₁ id * N.submatrix e₂ id = M.submatrix e₁ e₂.symm * N := by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

@[simp]
/--
theorem `submatrix_id_mul_right` / 定理 `submatrix_id_mul_right`

English:
theorem submatrix_id_mul_right
  statement: [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
  proof: by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

中文:
定理 submatrix_id_mul_right
  结论: [有限类型 n] [有限类型 o] [乘法 α] [加法交换幺半群 α] {p : 类型}
  证明: by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

Depends on / 依赖: bijective, bijective.sum_comp, mul_apply, sum_comp
-/
theorem submatrix_id_mul_right [Fintype n] [Fintype o] [Mul α] [AddCommMonoid α] {p : Type*}
    (M : Matrix m n α) (N : Matrix o p α) (e₁ : l -> p) (e₂ : o ≃ n) :
    M.submatrix id e₂ * N.submatrix id e₁ = M * N.submatrix e₂.symm e₁ := by
  ext; simp [mul_apply, ← e₂.bijective.sum_comp]

/--
theorem `submatrix_vecMul_equiv` / 定理 `submatrix_vecMul_equiv`

English:
theorem submatrix_vecMul_equiv
  statement: [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α]
  proof: funext fun _ => Eq.symm (comp_equiv_symm_dotProduct _ _ _)

中文:
定理 submatrix_vecMul_equiv
  结论: [有限类型 l] [有限类型 m] [非幺非结合半环 α]
  证明: funext fun _ => Eq.symm (comp_equiv_symm_dotProduct _ _ _)

Depends on / 依赖: Eq.symm, comp_equiv_symm_dotProduct
-/
theorem submatrix_vecMul_equiv [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (M : Matrix m n α) (v : l -> α) (e₁ : l ≃ m) (e₂ : o -> n) :
    v ᵥ* M.submatrix e₁ e₂ = ((v ∘ e₁.symm) ᵥ* M) ∘ e₂ :=
  funext fun _ => Eq.symm (comp_equiv_symm_dotProduct _ _ _)

/--
theorem `mul_submatrix_one` / 定理 `mul_submatrix_one`

English:
theorem mul_submatrix_one
  statement: [Fintype n] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : n ≃ o)
  proof: by
  cases nonempty_fintype o
  let A := M.submatrix id e₁.symm
  have : M = A.submatrix id e₁ := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this]; rw [submatrix_mul_equiv]
  simp only [A, Matrix.mul_one, submatrix_submatrix, Function.com

中文:
定理 mul_submatrix_one
  结论: [有限类型 n] [有限 o] [非结合半环 α] [DecidableEq o] (e₁ : n ≃ o)
  证明: by
  cases nonempty_fintype o
  let A := M.submatrix id e₁.symm
  have : M = A.submatrix id e₁ := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this]; rw [submatrix_mul_equiv]
  simp only [A, Matrix.mul_one, submatrix_submatrix, Function.com

Depends on / 依赖: A.submatrix, Equiv.symm_comp_self, Function, Function.comp_id, M.submatrix, Matrix, Matrix.mul_one, comp_id, mul_one, nonempty_fintype, submatrix, submatrix_id_id, submatrix_mul_equiv, submatrix_submatrix, symm_comp_self
-/
theorem mul_submatrix_one [Fintype n] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : n ≃ o)
    (e₂ : l -> o) (M : Matrix m n α) :
    M * (1 : Matrix o o α).submatrix e₁ e₂ = submatrix M id (e₁.symm ∘ e₂) := by
  cases nonempty_fintype o
  let A := M.submatrix id e₁.symm
  have : M = A.submatrix id e₁ := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this]; rw [submatrix_mul_equiv]
  simp only [A, Matrix.mul_one, submatrix_submatrix, Function.comp_id, submatrix_id_id,
    Equiv.symm_comp_self]

/--
theorem `one_submatrix_mul` / 定理 `one_submatrix_mul`

English:
theorem one_submatrix_mul
  statement: [Fintype m] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : l -> o)
  proof: by
  cases nonempty_fintype o
  let A := M.submatrix e₂.symm id
  have : M = A.submatrix e₂ id := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this]; rw [submatrix_mul_equiv]
  simp only [A, Matrix.one_mul, submatrix_submatrix, Function.com

中文:
定理 one_submatrix_mul
  结论: [有限类型 m] [有限 o] [非结合半环 α] [DecidableEq o] (e₁ : l -> o)
  证明: by
  cases nonempty_fintype o
  let A := M.submatrix e₂.symm id
  have : M = A.submatrix e₂ id := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this]; rw [submatrix_mul_equiv]
  simp only [A, Matrix.one_mul, submatrix_submatrix, Function.com

Depends on / 依赖: A.submatrix, Equiv.symm_comp_self, Function, Function.comp_id, M.submatrix, Matrix, Matrix.one_mul, comp_id, nonempty_fintype, one_mul, submatrix, submatrix_id_id, submatrix_mul_equiv, submatrix_submatrix, symm_comp_self
-/
theorem one_submatrix_mul [Fintype m] [Finite o] [NonAssocSemiring α] [DecidableEq o] (e₁ : l -> o)
    (e₂ : m ≃ o) (M : Matrix m n α) :
    ((1 : Matrix o o α).submatrix e₁ e₂) * M = submatrix M (e₂.symm ∘ e₁) id := by
  cases nonempty_fintype o
  let A := M.submatrix e₂.symm id
  have : M = A.submatrix e₂ id := by
    simp only [A, submatrix_submatrix, Function.comp_id, submatrix_id_id, Equiv.symm_comp_self]
  rw [this]; rw [submatrix_mul_equiv]
  simp only [A, Matrix.one_mul, submatrix_submatrix, Function.comp_id, submatrix_id_id,
    Equiv.symm_comp_self]

/--
theorem `submatrix_mul_transpose_submatrix` / 定理 `submatrix_mul_transpose_submatrix`

English:
theorem submatrix_mul_transpose_submatrix
  statement: [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α]
  proof: by
  rw [submatrix_mul_equiv]; rw [submatrix_id_id]

中文:
定理 submatrix_mul_transpose_submatrix
  结论: [有限类型 m] [有限类型 n] [加法交换幺半群 α] [乘法 α]
  证明: by
  rw [submatrix_mul_equiv]; rw [submatrix_id_id]

Depends on / 依赖: submatrix_id_id, submatrix_mul_equiv
-/
theorem submatrix_mul_transpose_submatrix [Fintype m] [Fintype n] [AddCommMonoid α] [Mul α]
    (e : m ≃ n) (M : Matrix m n α) : M.submatrix id e * Mᵀ.submatrix e id = M * Mᵀ := by
  rw [submatrix_mul_equiv]; rw [submatrix_id_id]

variable (m n R : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [MulOne R] [AddCommMonoid R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStablyFiniteRing
  signature: R] : IsDedekindFiniteMonoid (Matrix n n R)
  body: let e := Fintype.equivFin n
  let f := MonoidHom.mk ⟨reindex (α := R) e e, submatrix_one_equiv _⟩
    fun _ _ => (submatrix_mul_equiv ..).symm
  .of_injective f (reindex e e).injective

中文:
实例 [是StablyFinite环
  签名: R] : 是DedekindFinite幺半群 (矩阵 n n R)
  定义体: let e := Fintype.equivFin n
  let f := MonoidHom.mk ⟨reindex (α := R) e e, submatrix_one_equiv _⟩
    fun _ _ => (submatrix_mul_equiv ..).symm
  .of_injective f (reindex e e).injective

Depends on / 依赖: Fintype, Fintype.equivFin, MonoidHom, MonoidHom.mk, equivFin, injective, of_injective, reindex, submatrix_mul_equiv, submatrix_one_equiv
-/
instance [IsStablyFiniteRing R] : IsDedekindFiniteMonoid (Matrix n n R) :=
  let e := Fintype.equivFin n
  let f := MonoidHom.mk ⟨reindex (α := R) e e, submatrix_one_equiv _⟩
    fun _ _ => (submatrix_mul_equiv ..).symm
  .of_injective f (reindex e e).injective

variable {m n R} in
/--
theorem `mul_eq_one_comm_of_equiv` / 定理 `mul_eq_one_comm_of_equiv`

English:
theorem mul_eq_one_comm_of_equiv
  statement: [IsStablyFiniteRing R] {A : Matrix m n R} {B : Matrix n m R}
  proof: (reindex e e).injective.eq_iff.symm.trans by
    rw [reindex_apply]; rw [reindex_apply]; rw [submatrix_one_equiv]; rw [← submatrix_mul_equiv _ _ _ (.refl _)]; rw [mul_eq_one_comm]; rw [submatrix_mul_equiv]; rw [Equiv.coe_refl]; rw [submatrix_id_id]

中文:
定理 mul_eq_one_comm_of_equiv
  结论: [是StablyFinite环 R] {A : 矩阵 m n R} {B : 矩阵 n m R}
  证明: (reindex e e).injective.eq_iff.symm.trans by
    rw [reindex_apply]; rw [reindex_apply]; rw [submatrix_one_equiv]; rw [← submatrix_mul_equiv _ _ _ (.refl _)]; rw [mul_eq_one_comm]; rw [submatrix_mul_equiv]; rw [Equiv.coe_refl]; rw [submatrix_id_id]

Depends on / 依赖: Equiv.coe_refl, coe_refl, eq_iff, injective, injective.eq_iff.symm.trans, mul_eq_one_comm, reindex, reindex_apply, submatrix_id_id, submatrix_mul_equiv, submatrix_one_equiv
-/
theorem mul_eq_one_comm_of_equiv [IsStablyFiniteRing R] {A : Matrix m n R} {B : Matrix n m R}
    (e : m ≃ n) : A * B = 1 ↔ B * A = 1 :=
(reindex e e).injective.eq_iff.symm.trans by
    rw [reindex_apply]; rw [reindex_apply]; rw [submatrix_one_equiv]; rw [← submatrix_mul_equiv _ _ _ (.refl _)]; rw [mul_eq_one_comm]; rw [submatrix_mul_equiv]; rw [Equiv.coe_refl]; rw [submatrix_id_id]

/--
theorem `mul_eq_one_comm_of_card_eq` / 定理 `mul_eq_one_comm_of_card_eq`

English:
theorem mul_eq_one_comm_of_card_eq
  statement: [IsStablyFiniteRing R] {A : Matrix m n R} {B : Matrix n m R}
  proof: mul_eq_one_comm_of_equiv (Fintype.card_eq.mp eq).some

中文:
定理 mul_eq_one_comm_of_card_eq
  结论: [是StablyFinite环 R] {A : 矩阵 m n R} {B : 矩阵 n m R}
  证明: mul_eq_one_comm_of_equiv (Fintype.card_eq.mp eq).some

Depends on / 依赖: Fintype, Fintype.card_eq.mp, card_eq, mul_eq_one_comm_of_equiv
-/
theorem mul_eq_one_comm_of_card_eq [IsStablyFiniteRing R] {A : Matrix m n R} {B : Matrix n m R}
    (eq : Fintype.card m = Fintype.card n) : A * B = 1 ↔ B * A = 1 :=
  mul_eq_one_comm_of_equiv (Fintype.card_eq.mp eq).some

end Matrix

namespace RingHom

variable [Fintype n] [NonAssocSemiring α] [NonAssocSemiring β]

/--
theorem `map_matrix_mul` / 定理 `map_matrix_mul`

English:
theorem map_matrix_mul
  given: (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α ->+* β)
  proof: by
  simp [Matrix.mul_apply, map_sum]

中文:
定理 map_matrix_mul
  条件: (M : 矩阵 m n α) (N : 矩阵 n o α) (i : m) (j : o) (f : α ->+* β)
  证明: by
  simp [Matrix.mul_apply, map_sum]

Depends on / 依赖: Matrix, Matrix.mul_apply, map_sum, mul_apply
-/
theorem map_matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α ->+* β) :
    f ((M * N) i j) = (M.map f * N.map f) i j := by
  simp [Matrix.mul_apply, map_sum]

/--
theorem `map_dotProduct` / 定理 `map_dotProduct`

English:
theorem map_dotProduct
  given: [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (v w : n -> R)
  proof: by
  simp only [dotProduct, map_sum f, f.map_mul, Function.comp]

中文:
定理 map_dotProduct
  条件: [非结合半环 R] [非结合半环 S] (f : R ->+* S) (v w : n -> R)
  证明: by
  simp only [dotProduct, map_sum f, f.map_mul, Function.comp]

Depends on / 依赖: Function, Function.comp, dotProduct, f.map_mul, map_mul, map_sum
-/
theorem map_dotProduct [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (v w : n -> R) :
    f (v ⬝ᵥ w) = f ∘ v ⬝ᵥ f ∘ w := by
  simp only [dotProduct, map_sum f, f.map_mul, Function.comp]

/--
theorem `map_vecMul` / 定理 `map_vecMul`

English:
theorem map_vecMul
  statement: [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (M : Matrix n m R)
  proof: by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

中文:
定理 map_vecMul
  结论: [非结合半环 R] [非结合半环 S] (f : R ->+* S) (M : 矩阵 n m R)
  证明: by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Matrix, Matrix.map_apply, Matrix.vecMul, RingHom, RingHom.map_dotProduct, comp_def, map_apply, map_dotProduct, vecMul
-/
theorem map_vecMul [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (M : Matrix n m R)
    (v : n -> R) (i : m) : f ((v ᵥ* M) i) = ((f ∘ v) ᵥ* M.map f) i := by
  simp only [Matrix.vecMul, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

/--
theorem `map_mulVec` / 定理 `map_mulVec`

English:
theorem map_mulVec
  statement: [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (M : Matrix m n R)
  proof: by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

中文:
定理 map_mulVec
  结论: [非结合半环 R] [非结合半环 S] (f : R ->+* S) (M : 矩阵 m n R)
  证明: by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Matrix, Matrix.map_apply, Matrix.mulVec, RingHom, RingHom.map_dotProduct, comp_def, map_apply, map_dotProduct, mulVec
-/
theorem map_mulVec [NonAssocSemiring R] [NonAssocSemiring S] (f : R ->+* S) (M : Matrix m n R)
    (v : n -> R) (i : m) : f ((M *ᵥ v) i) = (M.map f *ᵥ (f ∘ v)) i := by
  simp only [Matrix.mulVec, Matrix.map_apply, RingHom.map_dotProduct, Function.comp_def]

end RingHom
