/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Embedding.Basic

/-!
# Diagonal matrices

This file defines diagonal matrices and the `AddCommMonoidWithOne` structure on matrices.

## Main definitions

* `Matrix.diagonal d`: matrix with the vector `d` along the diagonal
* `Matrix.diag M`: the diagonal of a square matrix
* `Matrix.instAddCommMonoidWithOne`: matrices are an additive commutative monoid with one
-/

@[expose] public section

assert_not_exists Algebra TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o -> Type*} {n' : o -> Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Diagonal

variable [DecidableEq n]

/--
Definition of `diagonal` / `diagonal` 的定义

English:
definition diagonal
  signature: [Zero α] (d : n -> α)
  body: of fun i j => if i = j then d i else 0

中文:
定义 diagonal
  签名: [Zero α] (d : n -> α)
  定义体: of fun i j => if i = j then d i else 0
-/
def diagonal [Zero α] (d : n -> α) : Matrix n n α :=
  of fun i j => if i = j then d i else 0

-- TODO: set as an equation lemma for `diagonal`, see https://github.com/leanprover-community/mathlib4/pull/3024
/--
theorem `diagonal_apply` / 定理 `diagonal_apply`

English:
theorem diagonal_apply
  given: [Zero α] (d : n -> α) (i j)
  statement: diagonal d i j = if i = j then d i else 0
  proof: rfl

@[simp]

中文:
定理 diagonal_apply
  条件: [Zero α] (d : n -> α) (i j)
  结论: diagonal d i j = if i = j then d i else 0
  证明: rfl

@[simp]
-/
theorem diagonal_apply [Zero α] (d : n -> α) (i j) : diagonal d i j = if i = j then d i else 0 :=
  rfl

@[simp]
/--
theorem `diagonal_apply_eq` / 定理 `diagonal_apply_eq`

English:
theorem diagonal_apply_eq
  given: [Zero α] (d : n -> α) (i : n)
  statement: (diagonal d) i i = d i
  proof: by
  simp [diagonal]

@[simp]

中文:
定理 diagonal_apply_eq
  条件: [Zero α] (d : n -> α) (i : n)
  结论: (diagonal d) i i = d i
  证明: by
  simp [diagonal]

@[simp]

Depends on / 依赖: diagonal
-/
theorem diagonal_apply_eq [Zero α] (d : n -> α) (i : n) : (diagonal d) i i = d i := by
  simp [diagonal]

@[simp]
/--
theorem `diagonal_apply_ne` / 定理 `diagonal_apply_ne`

English:
theorem diagonal_apply_ne
  given: [Zero α] (d : n -> α) {i j : n} (h : i != j)
  statement: (diagonal d) i j = 0
  proof: by
  simp [diagonal, h]

中文:
定理 diagonal_apply_ne
  条件: [Zero α] (d : n -> α) {i j : n} (h : i != j)
  结论: (diagonal d) i j = 0
  证明: by
  simp [diagonal, h]

Depends on / 依赖: diagonal
-/
theorem diagonal_apply_ne [Zero α] (d : n -> α) {i j : n} (h : i != j) : (diagonal d) i j = 0 := by
  simp [diagonal, h]

/--
theorem `diagonal_apply_ne'` / 定理 `diagonal_apply_ne'`

English:
theorem diagonal_apply_ne'
  given: [Zero α] (d : n -> α) {i j : n} (h : j != i)
  statement: (diagonal d) i j = 0
  proof: diagonal_apply_ne d h.symm

@[simp]

中文:
定理 diagonal_apply_ne'
  条件: [Zero α] (d : n -> α) {i j : n} (h : j != i)
  结论: (diagonal d) i j = 0
  证明: diagonal_apply_ne d h.symm

@[simp]

Depends on / 依赖: diagonal_apply_ne, h.symm
-/
theorem diagonal_apply_ne' [Zero α] (d : n -> α) {i j : n} (h : j != i) : (diagonal d) i j = 0 :=
  diagonal_apply_ne d h.symm

@[simp]
/--
theorem `diagonal_eq_diagonal_iff` / 定理 `diagonal_eq_diagonal_iff`

English:
theorem diagonal_eq_diagonal_iff
  given: [Zero α] {d₁ d₂ : n -> α}
  proof: ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
    rw [show d₁ = d₂ from funext h]⟩

中文:
定理 diagonal_eq_diagonal_iff
  条件: [Zero α] {d₁ d₂ : n -> α}
  证明: ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
    rw [show d₁ = d₂ from funext h]⟩

Depends on / 依赖: Matrix, congr_arg
-/
theorem diagonal_eq_diagonal_iff [Zero α] {d₁ d₂ : n -> α} :
    diagonal d₁ = diagonal d₂ ↔ forall i, d₁ i = d₂ i :=
  ⟨fun h i => by simpa using congr_arg (fun m : Matrix n n α => m i i) h, fun h => by
    rw [show d₁ = d₂ from funext h]⟩

/--
theorem `diagonal_injective` / 定理 `diagonal_injective`

English:
theorem diagonal_injective
  given: [Zero α]
  statement: Function.Injective (diagonal : (n -> α) -> Matrix n n α)
  proof: fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i

@[simp]

中文:
定理 diagonal_injective
  条件: [Zero α]
  结论: Function.Injective (diagonal : (n -> α) -> Matrix n n α)
  证明: fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i

@[simp]

Depends on / 依赖: Matrix, Matrix.ext_iff.mpr, ext_iff
-/
theorem diagonal_injective [Zero α] : Function.Injective (diagonal : (n -> α) -> Matrix n n α) :=
  fun d₁ d₂ h => funext fun i => by simpa using Matrix.ext_iff.mpr h i i

@[simp]
/--
theorem `diagonal_zero` / 定理 `diagonal_zero`

English:
theorem diagonal_zero
  given: [Zero α]
  statement: (diagonal fun _ => 0 : Matrix n n α) = 0
  proof: by
  ext
  simp [diagonal]

@[simp]

中文:
定理 diagonal_zero
  条件: [Zero α]
  结论: (diagonal fun _ => 0 : Matrix n n α) = 0
  证明: by
  ext
  simp [diagonal]

@[simp]

Depends on / 依赖: diagonal
-/
theorem diagonal_zero [Zero α] : (diagonal fun _ => 0 : Matrix n n α) = 0 := by
  ext
  simp [diagonal]

@[simp]
/--
theorem `diagonal_zero'` / 定理 `diagonal_zero'`

English:
theorem diagonal_zero'
  given: [Zero α]
  statement: (diagonal 0 : Matrix n n α) = 0
  proof: diagonal_zero

@[simp]

中文:
定理 diagonal_zero'
  条件: [Zero α]
  结论: (diagonal 0 : Matrix n n α) = 0
  证明: diagonal_zero

@[simp]

Depends on / 依赖: diagonal_zero
-/
theorem diagonal_zero' [Zero α] : (diagonal 0 : Matrix n n α) = 0 := diagonal_zero

@[simp]
/--
theorem `diagonal_eq_zero` / 定理 `diagonal_eq_zero`

English:
theorem diagonal_eq_zero
  given: [Zero α] {d : n -> α}
  statement: diagonal d = 0 ↔ d = 0
  proof: diagonal_injective.eq_iff' diagonal_zero

@[simp]

中文:
定理 diagonal_eq_zero
  条件: [Zero α] {d : n -> α}
  结论: diagonal d = 0 ↔ d = 0
  证明: diagonal_injective.eq_iff' diagonal_zero

@[simp]

Depends on / 依赖: diagonal_injective, diagonal_injective.eq_iff, diagonal_zero, eq_iff
-/
theorem diagonal_eq_zero [Zero α] {d : n -> α} : diagonal d = 0 ↔ d = 0 :=
  diagonal_injective.eq_iff' diagonal_zero

@[simp]
/--
theorem `diagonal_transpose` / 定理 `diagonal_transpose`

English:
theorem diagonal_transpose
  given: [Zero α] (v : n -> α)
  statement: (diagonal v)ᵀ = diagonal v
  proof: by
  ext i j
  by_cases h : i = j <;> simp [h, transpose, eqComm]

@[simp]

中文:
定理 diagonal_transpose
  条件: [Zero α] (v : n -> α)
  结论: (diagonal v)ᵀ = diagonal v
  证明: by
  ext i j
  by_cases h : i = j <;> simp [h, transpose, eqComm]

@[simp]

Depends on / 依赖: eqComm, transpose
-/
theorem diagonal_transpose [Zero α] (v : n -> α) : (diagonal v)ᵀ = diagonal v := by
  ext i j
  by_cases h : i = j <;> simp [h, transpose, eqComm]

@[simp]
/--
theorem `diagonal_add` / 定理 `diagonal_add`

English:
theorem diagonal_add
  given: [AddZeroClass α] (d₁ d₂ : n -> α)
  proof: by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]

中文:
定理 diagonal_add
  条件: [AddZeroClass α] (d₁ d₂ : n -> α)
  证明: by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
-/
theorem diagonal_add [AddZeroClass α] (d₁ d₂ : n -> α) :
    diagonal d₁ + diagonal d₂ = diagonal fun i => d₁ i + d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
/--
theorem `diagonal_smul` / 定理 `diagonal_smul`

English:
theorem diagonal_smul
  given: [Zero α] [SMulZeroClass R α] (r : R) (d : n -> α)
  proof: by
  ext i j
  by_cases h : i = j <;> simp [h]

@[simp]

中文:
定理 diagonal_smul
  条件: [Zero α] [SMulZeroClass R α] (r : R) (d : n -> α)
  证明: by
  ext i j
  by_cases h : i = j <;> simp [h]

@[simp]
-/
theorem diagonal_smul [Zero α] [SMulZeroClass R α] (r : R) (d : n -> α) :
    diagonal (r • d) = r • diagonal d := by
  ext i j
  by_cases h : i = j <;> simp [h]

@[simp]
/--
theorem `diagonal_neg` / 定理 `diagonal_neg`

English:
theorem diagonal_neg
  given: [NegZeroClass α] (d : n -> α)
  proof: by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]

中文:
定理 diagonal_neg
  条件: [NegZeroClass α] (d : n -> α)
  证明: by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
-/
theorem diagonal_neg [NegZeroClass α] (d : n -> α) :
    -diagonal d = diagonal fun i => -d i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

@[simp]
/--
theorem `diagonal_sub` / 定理 `diagonal_sub`

English:
theorem diagonal_sub
  given: [SubNegZeroMonoid α] (d₁ d₂ : n -> α)
  proof: by
  ext i j
  by_cases h : i = j <;>
  simp [h]

中文:
定理 diagonal_sub
  条件: [SubNegZeroMonoid α] (d₁ d₂ : n -> α)
  证明: by
  ext i j
  by_cases h : i = j <;>
  simp [h]
-/
theorem diagonal_sub [SubNegZeroMonoid α] (d₁ d₂ : n -> α) :
    diagonal d₁ - diagonal d₂ = diagonal fun i => d₁ i - d₂ i := by
  ext i j
  by_cases h : i = j <;>
  simp [h]

/--
theorem `diagonal_mem_matrix_iff` / 定理 `diagonal_mem_matrix_iff`

English:
theorem diagonal_mem_matrix_iff
  given: [Zero α] {S : Set α} (hS : 0 in S) {d : n -> α}
  proof: by
  simp only [Set.mem_matrix, diagonal, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]

中文:
定理 diagonal_mem_matrix_iff
  条件: [Zero α] {S : Set α} (hS : 0 in S) {d : n -> α}
  证明: by
  simp only [Set.mem_matrix, diagonal, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]

Depends on / 依赖: Set.mem_matrix, conv_lhs, diagonal, ite_mem, mem_matrix, of_apply
-/
theorem diagonal_mem_matrix_iff [Zero α] {S : Set α} (hS : 0 in S) {d : n -> α} :
    Matrix.diagonal d in S.matrix ↔ forall i, d i in S := by
  simp only [Set.mem_matrix, diagonal, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] [NatCast α] : NatCast (Matrix n n α) where
  body: diagonal fun _ => m

@[norm_cast]

中文:
实例 [Zero
  签名: α] [自然数Cast α] : 自然数Cast (Matrix n n α) where
  定义体: diagonal fun _ => m

@[norm_cast]

Depends on / 依赖: diagonal
-/
instance [Zero α] [NatCast α] : NatCast (Matrix n n α) where
  natCast m := diagonal fun _ => m

@[norm_cast]
/--
theorem `diagonal_natCast` / 定理 `diagonal_natCast`

English:
theorem diagonal_natCast
  given: [Zero α] [NatCast α] (m : Nat)
  statement: diagonal (fun _ : n => (m : α)) = m
  proof: rfl

@[norm_cast]

中文:
定理 diagonal_natCast
  条件: [Zero α] [自然数Cast α] (m : 自然数)
  结论: diagonal (fun _ : n => (m : α)) = m
  证明: rfl

@[norm_cast]
-/
theorem diagonal_natCast [Zero α] [NatCast α] (m : Nat) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
/--
theorem `diagonal_natCast'` / 定理 `diagonal_natCast'`

English:
theorem diagonal_natCast'
  given: [Zero α] [NatCast α] (m : Nat)
  statement: diagonal ((m : n -> α)) = m
  proof: rfl

@[simp]

中文:
定理 diagonal_natCast'
  条件: [Zero α] [自然数Cast α] (m : 自然数)
  结论: diagonal ((m : n -> α)) = m
  证明: rfl

@[simp]
-/
theorem diagonal_natCast' [Zero α] [NatCast α] (m : Nat) : diagonal ((m : n -> α)) = m := rfl

@[simp]
/--
theorem `diagonal_eq_natCast` / 定理 `diagonal_eq_natCast`

English:
theorem diagonal_eq_natCast
  given: [Zero α] [NatCast α] {d : n -> α} {m : Nat}
  proof: diagonal_injective.eq_iff' diagonal_natCast' _

中文:
定理 diagonal_eq_natCast
  条件: [Zero α] [自然数Cast α] {d : n -> α} {m : 自然数}
  证明: diagonal_injective.eq_iff' diagonal_natCast' _

Depends on / 依赖: diagonal_injective, diagonal_injective.eq_iff, diagonal_natCast, eq_iff
-/
theorem diagonal_eq_natCast [Zero α] [NatCast α] {d : n -> α} {m : Nat} :
    diagonal d = m ↔ d = m :=
diagonal_injective.eq_iff' diagonal_natCast' _

/--
theorem `diagonal_ofNat` / 定理 `diagonal_ofNat`

English:
theorem diagonal_ofNat
  given: [Zero α] [NatCast α] (m : Nat) [m.AtLeastTwo]
  proof: rfl

中文:
定理 diagonal_ofNat
  条件: [Zero α] [自然数Cast α] (m : 自然数) [m.AtLeastTwo]
  证明: rfl
-/
theorem diagonal_ofNat [Zero α] [NatCast α] (m : Nat) [m.AtLeastTwo] :
    diagonal (fun _ : n => (ofNat(m) : α)) = ofNat(m) := rfl

/--
theorem `diagonal_ofNat'` / 定理 `diagonal_ofNat'`

English:
theorem diagonal_ofNat'
  given: [Zero α] [NatCast α] (m : Nat) [m.AtLeastTwo]
  proof: rfl

@[simp]

中文:
定理 diagonal_ofNat'
  条件: [Zero α] [自然数Cast α] (m : 自然数) [m.AtLeastTwo]
  证明: rfl

@[simp]
-/
theorem diagonal_ofNat' [Zero α] [NatCast α] (m : Nat) [m.AtLeastTwo] :
    diagonal (ofNat(m) : n -> α) = ofNat(m) := rfl

@[simp]
/--
theorem `diagonal_eq_ofNat` / 定理 `diagonal_eq_ofNat`

English:
theorem diagonal_eq_ofNat
  given: [Zero α] [NatCast α] {d : n -> α} {m : Nat} [m.AtLeastTwo]
  proof: diagonal_injective.eq_iff' diagonal_ofNat' _

中文:
定理 diagonal_eq_ofNat
  条件: [Zero α] [自然数Cast α] {d : n -> α} {m : 自然数} [m.AtLeastTwo]
  证明: diagonal_injective.eq_iff' diagonal_ofNat' _

Depends on / 依赖: Lex.left, Lex.right, diagonal_injective, diagonal_injective.eq_iff, diagonal_ofNat, eq_iff
-/
theorem diagonal_eq_ofNat [Zero α] [NatCast α] {d : n -> α} {m : Nat} [m.AtLeastTwo] :
    diagonal d = ofNat(m) ↔ d = ofNat(m) :=
diagonal_injective.eq_iff' diagonal_ofNat' _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] [IntCast α] : IntCast (Matrix n n α) where
  body: diagonal fun _ => m

@[norm_cast]

中文:
实例 [Zero
  签名: α] [整数Cast α] : 整数Cast (Matrix n n α) where
  定义体: diagonal fun _ => m

@[norm_cast]

Depends on / 依赖: diagonal, h.mono
-/
instance [Zero α] [IntCast α] : IntCast (Matrix n n α) where
  intCast m := diagonal fun _ => m

@[norm_cast]
/--
theorem `diagonal_intCast` / 定理 `diagonal_intCast`

English:
theorem diagonal_intCast
  given: [Zero α] [IntCast α] (m : Int)
  statement: diagonal (fun _ : n => (m : α)) = m
  proof: rfl

@[norm_cast]

中文:
定理 diagonal_intCast
  条件: [Zero α] [整数Cast α] (m : 整数)
  结论: diagonal (fun _ : n => (m : α)) = m
  证明: rfl

@[norm_cast]

Depends on / 依赖: h.mono
-/
theorem diagonal_intCast [Zero α] [IntCast α] (m : Int) : diagonal (fun _ : n => (m : α)) = m := rfl

@[norm_cast]
/--
theorem `diagonal_intCast'` / 定理 `diagonal_intCast'`

English:
theorem diagonal_intCast'
  given: [Zero α] [IntCast α] (m : Int)
  statement: diagonal ((m : n -> α)) = m
  proof: rfl

@[simp]

中文:
定理 diagonal_intCast'
  条件: [Zero α] [整数Cast α] (m : 整数)
  结论: diagonal ((m : n -> α)) = m
  证明: rfl

@[simp]
-/
theorem diagonal_intCast' [Zero α] [IntCast α] (m : Int) : diagonal ((m : n -> α)) = m := rfl

@[simp]
/--
theorem `diagonal_eq_intCast` / 定理 `diagonal_eq_intCast`

English:
theorem diagonal_eq_intCast
  given: [Zero α] [IntCast α] {d : n -> α} {m : Int}
  proof: diagonal_injective.eq_iff' diagonal_intCast' _

@[simp]

中文:
定理 diagonal_eq_intCast
  条件: [Zero α] [整数Cast α] {d : n -> α} {m : 整数}
  证明: diagonal_injective.eq_iff' diagonal_intCast' _

@[simp]

Depends on / 依赖: diagonal_injective, diagonal_injective.eq_iff, diagonal_intCast, eq_iff
-/
theorem diagonal_eq_intCast [Zero α] [IntCast α] {d : n -> α} {m : Int} :
    diagonal d = m ↔ d = m :=
diagonal_injective.eq_iff' diagonal_intCast' _

@[simp]
/--
theorem `diagonal_map` / 定理 `diagonal_map`

English:
theorem diagonal_map
  given: [Zero α] [Zero β] {f : α -> β} (h : f 0 = 0) {d : n -> α}
  proof: by
  ext
  simp only [diagonal_apply, map_apply]
  split_ifs <;> simp [h]

中文:
定理 diagonal_map
  条件: [Zero α] [Zero β] {f : α -> β} (h : f 0 = 0) {d : n -> α}
  证明: by
  ext
  simp only [diagonal_apply, map_apply]
  split_ifs <;> simp [h]

Depends on / 依赖: diagonal_apply, map_apply, split_ifs
-/
theorem diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 0 = 0) {d : n -> α} :
    (diagonal d).map f = diagonal fun m => f (d m) := by
  ext
  simp only [diagonal_apply, map_apply]
  split_ifs <;> simp [h]

/--
theorem `map_natCast` / 定理 `map_natCast`

English:
theorem map_natCast
  statement: [AddMonoidWithOne α] [Zero β]
  proof: diagonal_map h

中文:
定理 map_natCast
  结论: [AddMonoidWithOne α] [Zero β]
  证明: diagonal_map h
-/
protected theorem map_natCast [AddMonoidWithOne α] [Zero β]
    {f : α -> β} (h : f 0 = 0) (d : Nat) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h

/--
theorem `map_ofNat` / 定理 `map_ofNat`

English:
theorem map_ofNat
  statement: [AddMonoidWithOne α] [Zero β]
  proof: diagonal_map h

中文:
定理 map_ofNat
  结论: [AddMonoidWithOne α] [Zero β]
  证明: diagonal_map h
-/
protected theorem map_ofNat [AddMonoidWithOne α] [Zero β]
    {f : α -> β} (h : f 0 = 0) (d : Nat) [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α).map f = diagonal (fun _ => f (OfNat.ofNat d)) :=
  diagonal_map h

/--
theorem `natCast_apply` / 定理 `natCast_apply`

English:
theorem natCast_apply
  given: [AddMonoidWithOne α] {i j} {d : Nat}
  proof: by
  rw [Nat.cast_ite]; rw [Nat.cast_zero]; rw [← diagonal_natCast]; rw [diagonal_apply]

中文:
定理 natCast_apply
  条件: [AddMonoidWithOne α] {i j} {d : 自然数}
  证明: by
  rw [Nat.cast_ite]; rw [Nat.cast_zero]; rw [← diagonal_natCast]; rw [diagonal_apply]

Depends on / 依赖: Nat.cast_ite, Nat.cast_zero, cast_ite, cast_zero, diagonal_apply, diagonal_natCast
-/
theorem natCast_apply [AddMonoidWithOne α] {i j} {d : Nat} :
    (d : Matrix n n α) i j = if i = j then d else 0 := by
  rw [Nat.cast_ite]; rw [Nat.cast_zero]; rw [← diagonal_natCast]; rw [diagonal_apply]

/--
theorem `ofNat_apply` / 定理 `ofNat_apply`

English:
theorem ofNat_apply
  given: [AddMonoidWithOne α] {i j} {d : Nat} [d.AtLeastTwo]
  proof: natCast_apply

中文:
定理 ofNat_apply
  条件: [AddMonoidWithOne α] {i j} {d : 自然数} [d.AtLeastTwo]
  证明: natCast_apply

Depends on / 依赖: natCast_apply
-/
theorem ofNat_apply [AddMonoidWithOne α] {i j} {d : Nat} [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α) i j = if i = j then d else 0 :=
  natCast_apply

/--
theorem `map_intCast` / 定理 `map_intCast`

English:
theorem map_intCast
  statement: [AddGroupWithOne α] [Zero β]
  proof: diagonal_map h

中文:
定理 map_intCast
  结论: [AddGroupWithOne α] [Zero β]
  证明: diagonal_map h
-/
protected theorem map_intCast [AddGroupWithOne α] [Zero β]
    {f : α -> β} (h : f 0 = 0) (d : Int) :
    (d : Matrix n n α).map f = diagonal (fun _ => f d) :=
  diagonal_map h

/--
theorem `intCast_apply` / 定理 `intCast_apply`

English:
theorem intCast_apply
  given: [AddGroupWithOne α] {i j} {d : Int}
  proof: by
  rw [Int.cast_ite]; rw [Int.cast_zero]; rw [← diagonal_intCast]; rw [diagonal_apply]

中文:
定理 intCast_apply
  条件: [AddGroupWithOne α] {i j} {d : 整数}
  证明: by
  rw [Int.cast_ite]; rw [Int.cast_zero]; rw [← diagonal_intCast]; rw [diagonal_apply]

Depends on / 依赖: Int.cast_ite, Int.cast_zero, cast_ite, cast_zero, diagonal_apply, diagonal_intCast
-/
theorem intCast_apply [AddGroupWithOne α] {i j} {d : Int} :
    (d : Matrix n n α) i j = if i = j then d else 0 := by
  rw [Int.cast_ite]; rw [Int.cast_zero]; rw [← diagonal_intCast]; rw [diagonal_apply]

/--
theorem `diagonal_unique` / 定理 `diagonal_unique`

English:
theorem diagonal_unique
  given: [Unique m] [DecidableEq m] [Zero α] (d : m -> α)
  proof: by
  ext i j
  rw [Subsingleton.elim i default]; rw [Subsingleton.elim j default]; rw [diagonal_apply_eq _ _]; rw [of_apply]

@[simp]

中文:
定理 diagonal_unique
  条件: [Unique m] [DecidableEq m] [Zero α] (d : m -> α)
  证明: by
  ext i j
  rw [Subsingleton.elim i default]; rw [Subsingleton.elim j default]; rw [diagonal_apply_eq _ _]; rw [of_apply]

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, diagonal_apply_eq, of_apply
-/
theorem diagonal_unique [Unique m] [DecidableEq m] [Zero α] (d : m -> α) :
    diagonal d = of fun _ _ => d default := by
  ext i j
  rw [Subsingleton.elim i default]; rw [Subsingleton.elim j default]; rw [diagonal_apply_eq _ _]; rw [of_apply]

@[simp]
/--
theorem `col_diagonal` / 定理 `col_diagonal`

English:
theorem col_diagonal
  given: [Zero α] (d : n -> α) (i)
  statement: (diagonal d).col i = Pi.single i (d i)
  proof: by
  ext
  simp +contextual [diagonal, Pi.single_apply]

@[simp]

中文:
定理 col_diagonal
  条件: [Zero α] (d : n -> α) (i)
  结论: (diagonal d).col i = Pi.single i (d i)
  证明: by
  ext
  simp +contextual [diagonal, Pi.single_apply]

@[simp]

Depends on / 依赖: Pi.single_apply, contextual, diagonal, single_apply
-/
theorem col_diagonal [Zero α] (d : n -> α) (i) : (diagonal d).col i = Pi.single i (d i) := by
  ext
  simp +contextual [diagonal, Pi.single_apply]

@[simp]
/--
theorem `row_diagonal` / 定理 `row_diagonal`

English:
theorem row_diagonal
  given: [Zero α] (d : n -> α) (j)
  statement: (diagonal d).row j = Pi.single j (d j)
  proof: by
  ext
  simp +contextual [diagonal, eq_comm, Pi.single_apply]

中文:
定理 row_diagonal
  条件: [Zero α] (d : n -> α) (j)
  结论: (diagonal d).row j = Pi.single j (d j)
  证明: by
  ext
  simp +contextual [diagonal, eq_comm, Pi.single_apply]

Depends on / 依赖: Pi.single_apply, contextual, diagonal, eq_comm, single_apply
-/
theorem row_diagonal [Zero α] (d : n -> α) (j) : (diagonal d).row j = Pi.single j (d j) := by
  ext
  simp +contextual [diagonal, eq_comm, Pi.single_apply]

section One

variable [Zero α] [One α]

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (Matrix n n α)
  body: ⟨diagonal fun _ => 1⟩

@[simp]

中文:
实例 one
  签名: : One (Matrix n n α)
  定义体: ⟨diagonal fun _ => 1⟩

@[simp]

Depends on / 依赖: diagonal
-/
instance one : One (Matrix n n α) :=
  ⟨diagonal fun _ => 1⟩

@[simp]
/--
theorem `diagonal_one` / 定理 `diagonal_one`

English:
theorem diagonal_one
  statement: (diagonal fun _ => 1 : Matrix n n α) = 1
  proof: rfl

@[simp]

中文:
定理 diagonal_one
  结论: (diagonal fun _ => 1 : Matrix n n α) = 1
  证明: rfl

@[simp]
-/
theorem diagonal_one : (diagonal fun _ => 1 : Matrix n n α) = 1 :=
  rfl

@[simp]
/--
theorem `diagonal_one'` / 定理 `diagonal_one'`

English:
theorem diagonal_one'
  statement: (diagonal 1 : Matrix n n α) = 1
  proof: rfl

@[simp]

中文:
定理 diagonal_one'
  结论: (diagonal 1 : Matrix n n α) = 1
  证明: rfl

@[simp]
-/
theorem diagonal_one' : (diagonal 1 : Matrix n n α) = 1 :=
  rfl

@[simp]
/--
theorem `diagonal_eq_one` / 定理 `diagonal_eq_one`

English:
theorem diagonal_eq_one
  given: {d : n -> α}
  statement: diagonal d = 1 ↔ d = 1
  proof: diagonal_injective.eq_iff' diagonal_one

中文:
定理 diagonal_eq_one
  条件: {d : n -> α}
  结论: diagonal d = 1 ↔ d = 1
  证明: diagonal_injective.eq_iff' diagonal_one

Depends on / 依赖: diagonal_injective, diagonal_injective.eq_iff, diagonal_one, eq_iff
-/
theorem diagonal_eq_one {d : n -> α} : diagonal d = 1 ↔ d = 1 :=
  diagonal_injective.eq_iff' diagonal_one

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: {i j}
  statement: (1 : Matrix n n α) i j = if i = j then 1 else 0
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: {i j}
  结论: (1 : Matrix n n α) i j = if i = j then 1 else 0
  证明: rfl

@[simp]
-/
theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
  rfl

@[simp]
/--
theorem `one_apply_eq` / 定理 `one_apply_eq`

English:
theorem one_apply_eq
  given: (i)
  statement: (1 : Matrix n n α) i i = 1
  proof: diagonal_apply_eq _ i

@[simp]

中文:
定理 one_apply_eq
  条件: (i)
  结论: (1 : Matrix n n α) i i = 1
  证明: diagonal_apply_eq _ i

@[simp]

Depends on / 依赖: diagonal_apply_eq
-/
theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 :=
  diagonal_apply_eq _ i

@[simp]
/--
theorem `one_apply_ne` / 定理 `one_apply_ne`

English:
theorem one_apply_ne
  given: {i j}
  statement: i != j -> (1 : Matrix n n α) i j = 0
  proof: diagonal_apply_ne _

中文:
定理 one_apply_ne
  条件: {i j}
  结论: i != j -> (1 : Matrix n n α) i j = 0
  证明: diagonal_apply_ne _

Depends on / 依赖: diagonal_apply_ne
-/
theorem one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne _

/--
theorem `one_apply_ne'` / 定理 `one_apply_ne'`

English:
theorem one_apply_ne'
  given: {i j}
  statement: j != i -> (1 : Matrix n n α) i j = 0
  proof: diagonal_apply_ne' _

@[simp]

中文:
定理 one_apply_ne'
  条件: {i j}
  结论: j != i -> (1 : Matrix n n α) i j = 0
  证明: diagonal_apply_ne' _

@[simp]

Depends on / 依赖: diagonal_apply_ne
-/
theorem one_apply_ne' {i j} : j != i -> (1 : Matrix n n α) i j = 0 :=
  diagonal_apply_ne' _

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: [Zero β] [One β] (f : α -> β) (h₀ : f 0 = 0) (h₁ : f 1 = 1)
  proof: by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]

中文:
定理 map_one
  条件: [Zero β] [One β] (f : α -> β) (h₀ : f 0 = 0) (h₁ : f 1 = 1)
  证明: by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]
-/
protected theorem map_one [Zero β] [One β] (f : α -> β) (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
    (1 : Matrix n n α).map f = (1 : Matrix n n β) := by
  ext
  simp only [one_apply, map_apply]
  split_ifs <;> simp [h₀, h₁]

/--
theorem `one_eq_pi_single` / 定理 `one_eq_pi_single`

English:
theorem one_eq_pi_single
  given: {i j}
  statement: (1 : Matrix n n α) i j = Pi.single (M := fun _ => α) i 1 j
  proof: by
  simp only [one_apply, Pi.single_apply, eq_comm]

中文:
定理 one_eq_pi_single
  条件: {i j}
  结论: (1 : Matrix n n α) i j = Pi.single (M := fun _ => α) i 1 j
  证明: by
  simp only [one_apply, Pi.single_apply, eq_comm]

Depends on / 依赖: Pi.single_apply, eq_comm, one_apply, single_apply
-/
theorem one_eq_pi_single {i j} : (1 : Matrix n n α) i j = Pi.single (M := fun _ => α) i 1 j := by
  simp only [one_apply, Pi.single_apply, eq_comm]

end One

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: [AddMonoidWithOne α]
  body: show diagonal _ = _ by
    rw [Nat.cast_zero]; rw [diagonal_zero]
  natCast_succ n := show diagonal _ = diagonal _ + _ by
    rw [Nat.cast_succ]; rw [← diagonal_add]; rw [diagonal_one]

中文:
实例 instAddMonoidWithOne
  签名: [AddMonoidWithOne α]
  定义体: show diagonal _ = _ by
    rw [Nat.cast_zero]; rw [diagonal_zero]
  natCast_succ n := show diagonal _ = diagonal _ + _ by
    rw [Nat.cast_succ]; rw [← diagonal_add]; rw [diagonal_one]

Depends on / 依赖: Nat.cast_succ, Nat.cast_zero, cast_succ, cast_zero, diagonal, diagonal_add, diagonal_one, diagonal_zero, natCast_succ
-/
instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (Matrix n n α) where
  natCast_zero := show diagonal _ = _ by
    rw [Nat.cast_zero]; rw [diagonal_zero]
  natCast_succ n := show diagonal _ = diagonal _ + _ by
    rw [Nat.cast_succ]; rw [← diagonal_add]; rw [diagonal_one]

/--
Instance `instAddGroupWithOne` / 实例 `instAddGroupWithOne`

English:
instance instAddGroupWithOne
  signature: [AddGroupWithOne α]
  body: show diagonal _ = diagonal _ by
    rw [Int.cast_natCast]
  intCast_negSucc n := show diagonal _ = -(diagonal _) by
    rw [Int.cast_negSucc]; rw [diagonal_neg]
  __ := addGroup
  __ := instAddMonoidWithOne

中文:
实例 instAddGroupWithOne
  签名: [AddGroupWithOne α]
  定义体: show diagonal _ = diagonal _ by
    rw [Int.cast_natCast]
  intCast_negSucc n := show diagonal _ = -(diagonal _) by
    rw [Int.cast_negSucc]; rw [diagonal_neg]
  __ := addGroup
  __ := instAddMonoidWithOne

Depends on / 依赖: Int.cast_natCast, Int.cast_negSucc, addGroup, cast_natCast, cast_negSucc, diagonal, diagonal_neg, instAddMonoidWithOne, intCast_negSucc
-/
instance instAddGroupWithOne [AddGroupWithOne α] : AddGroupWithOne (Matrix n n α) where
  intCast_ofNat n := show diagonal _ = diagonal _ by
    rw [Int.cast_natCast]
  intCast_negSucc n := show diagonal _ = -(diagonal _) by
    rw [Int.cast_negSucc]; rw [diagonal_neg]
  __ := addGroup
  __ := instAddMonoidWithOne

/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: [AddCommMonoidWithOne α]
  body: addCommMonoid
  __ := instAddMonoidWithOne

中文:
实例 instAddCommMonoidWithOne
  签名: [AddCommMonoidWithOne α]
  定义体: addCommMonoid
  __ := instAddMonoidWithOne

Depends on / 依赖: addCommMonoid
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne α] :
    AddCommMonoidWithOne (Matrix n n α) where
  __ := addCommMonoid
  __ := instAddMonoidWithOne

/--
Instance `instAddCommGroupWithOne` / 实例 `instAddCommGroupWithOne`

English:
instance instAddCommGroupWithOne
  signature: [AddCommGroupWithOne α]
  body: addCommGroup
  __ := instAddGroupWithOne

中文:
实例 instAddCommGroupWithOne
  签名: [AddCommGroupWithOne α]
  定义体: addCommGroup
  __ := instAddGroupWithOne

Depends on / 依赖: addCommGroup
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne α] :
    AddCommGroupWithOne (Matrix n n α) where
  __ := addCommGroup
  __ := instAddGroupWithOne

end Diagonal

section Diag

/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: (A : Matrix n n α) (i : n)
  body: A i i

@[simp]

中文:
定义 diag
  签名: (A : Matrix n n α) (i : n)
  定义体: A i i

@[simp]
-/
def diag (A : Matrix n n α) (i : n) : α :=
  A i i

@[simp]
/--
theorem `diag_apply` / 定理 `diag_apply`

English:
theorem diag_apply
  given: (A : Matrix n n α) (i)
  statement: diag A i = A i i
  proof: rfl

@[simp]

中文:
定理 diag_apply
  条件: (A : Matrix n n α) (i)
  结论: diag A i = A i i
  证明: rfl

@[simp]
-/
theorem diag_apply (A : Matrix n n α) (i) : diag A i = A i i :=
  rfl

@[simp]
/--
theorem `diag_diagonal` / 定理 `diag_diagonal`

English:
theorem diag_diagonal
  given: [DecidableEq n] [Zero α] (a : n -> α)
  statement: diag (diagonal a) = a
  proof: funext @diagonal_apply_eq _ _ _ _ a

@[simp]

中文:
定理 diag_diagonal
  条件: [DecidableEq n] [Zero α] (a : n -> α)
  结论: diag (diagonal a) = a
  证明: funext @diagonal_apply_eq _ _ _ _ a

@[simp]

Depends on / 依赖: diagonal_apply_eq
-/
theorem diag_diagonal [DecidableEq n] [Zero α] (a : n -> α) : diag (diagonal a) = a :=
funext @diagonal_apply_eq _ _ _ _ a

@[simp]
/--
theorem `diag_transpose` / 定理 `diag_transpose`

English:
theorem diag_transpose
  given: (A : Matrix n n α)
  statement: diag Aᵀ = diag A
  proof: rfl

@[simp]

中文:
定理 diag_transpose
  条件: (A : Matrix n n α)
  结论: diag Aᵀ = diag A
  证明: rfl

@[simp]
-/
theorem diag_transpose (A : Matrix n n α) : diag Aᵀ = diag A :=
  rfl

@[simp]
/--
theorem `diag_zero` / 定理 `diag_zero`

English:
theorem diag_zero
  given: [Zero α]
  statement: diag (0 : Matrix n n α) = 0
  proof: rfl

@[simp]

中文:
定理 diag_zero
  条件: [Zero α]
  结论: diag (0 : Matrix n n α) = 0
  证明: rfl

@[simp]
-/
theorem diag_zero [Zero α] : diag (0 : Matrix n n α) = 0 :=
  rfl

@[simp]
/--
theorem `diag_add` / 定理 `diag_add`

English:
theorem diag_add
  given: [Add α] (A B : Matrix n n α)
  statement: diag (A + B) = diag A + diag B
  proof: rfl

@[simp]

中文:
定理 diag_add
  条件: [Add α] (A B : Matrix n n α)
  结论: diag (A + B) = diag A + diag B
  证明: rfl

@[simp]
-/
theorem diag_add [Add α] (A B : Matrix n n α) : diag (A + B) = diag A + diag B :=
  rfl

@[simp]
/--
theorem `diag_sub` / 定理 `diag_sub`

English:
theorem diag_sub
  given: [Sub α] (A B : Matrix n n α)
  statement: diag (A - B) = diag A - diag B
  proof: rfl

@[simp]

中文:
定理 diag_sub
  条件: [Sub α] (A B : Matrix n n α)
  结论: diag (A - B) = diag A - diag B
  证明: rfl

@[simp]
-/
theorem diag_sub [Sub α] (A B : Matrix n n α) : diag (A - B) = diag A - diag B :=
  rfl

@[simp]
/--
theorem `diag_neg` / 定理 `diag_neg`

English:
theorem diag_neg
  given: [Neg α] (A : Matrix n n α)
  statement: diag (-A) = -diag A
  proof: rfl

@[simp]

中文:
定理 diag_neg
  条件: [Neg α] (A : Matrix n n α)
  结论: diag (-A) = -diag A
  证明: rfl

@[simp]
-/
theorem diag_neg [Neg α] (A : Matrix n n α) : diag (-A) = -diag A :=
  rfl

@[simp]
/--
theorem `diag_smul` / 定理 `diag_smul`

English:
theorem diag_smul
  given: [SMul R α] (r : R) (A : Matrix n n α)
  statement: diag (r • A) = r • diag A
  proof: rfl

@[simp]

中文:
定理 diag_smul
  条件: [SMul R α] (r : R) (A : Matrix n n α)
  结论: diag (r • A) = r • diag A
  证明: rfl

@[simp]
-/
theorem diag_smul [SMul R α] (r : R) (A : Matrix n n α) : diag (r • A) = r • diag A :=
  rfl

@[simp]
/--
theorem `diag_one` / 定理 `diag_one`

English:
theorem diag_one
  given: [DecidableEq n] [Zero α] [One α]
  statement: diag (1 : Matrix n n α) = 1
  proof: diag_diagonal _

中文:
定理 diag_one
  条件: [DecidableEq n] [Zero α] [One α]
  结论: diag (1 : Matrix n n α) = 1
  证明: diag_diagonal _

Depends on / 依赖: diag_diagonal
-/
theorem diag_one [DecidableEq n] [Zero α] [One α] : diag (1 : Matrix n n α) = 1 :=
  diag_diagonal _

/--
theorem `diag_map` / 定理 `diag_map`

English:
theorem diag_map
  given: {f : α -> β} {A : Matrix n n α}
  statement: diag (A.map f) = f ∘ diag A
  proof: rfl

中文:
定理 diag_map
  条件: {f : α -> β} {A : Matrix n n α}
  结论: diag (A.map f) = f ∘ diag A
  证明: rfl
-/
theorem diag_map {f : α -> β} {A : Matrix n n α} : diag (A.map f) = f ∘ diag A :=
  rfl

end Diag

end Matrix

open Matrix

namespace Matrix

section Transpose

@[simp]
/--
theorem `transpose_eq_diagonal` / 定理 `transpose_eq_diagonal`

English:
theorem transpose_eq_diagonal
  given: [DecidableEq n] [Zero α] {M : Matrix n n α} {v : n -> α}
  proof: (Function.Involutive.eq_iff transpose_transpose).trans
    by rw [diagonal_transpose]

@[simp]

中文:
定理 transpose_eq_diagonal
  条件: [DecidableEq n] [Zero α] {M : Matrix n n α} {v : n -> α}
  证明: (Function.Involutive.eq_iff transpose_transpose).trans
    by rw [diagonal_transpose]

@[simp]

Depends on / 依赖: Function, Function.Involutive.eq_iff, Involutive, diagonal_transpose, eq_iff, transpose_transpose
-/
theorem transpose_eq_diagonal [DecidableEq n] [Zero α] {M : Matrix n n α} {v : n -> α} :
    Mᵀ = diagonal v ↔ M = diagonal v :=
(Function.Involutive.eq_iff transpose_transpose).trans
    by rw [diagonal_transpose]

@[simp]
/--
theorem `transpose_one` / 定理 `transpose_one`

English:
theorem transpose_one
  given: [DecidableEq n] [Zero α] [One α]
  statement: (1 : Matrix n n α)ᵀ = 1
  proof: diagonal_transpose _

@[simp]

中文:
定理 transpose_one
  条件: [DecidableEq n] [Zero α] [One α]
  结论: (1 : Matrix n n α)ᵀ = 1
  证明: diagonal_transpose _

@[simp]

Depends on / 依赖: diagonal_transpose
-/
theorem transpose_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α)ᵀ = 1 :=
  diagonal_transpose _

@[simp]
/--
theorem `transpose_eq_one` / 定理 `transpose_eq_one`

English:
theorem transpose_eq_one
  given: [DecidableEq n] [Zero α] [One α] {M : Matrix n n α}
  statement: Mᵀ = 1 ↔ M = 1
  proof: transpose_eq_diagonal

@[simp]

中文:
定理 transpose_eq_one
  条件: [DecidableEq n] [Zero α] [One α] {M : Matrix n n α}
  结论: Mᵀ = 1 ↔ M = 1
  证明: transpose_eq_diagonal

@[simp]

Depends on / 依赖: transpose_eq_diagonal
-/
theorem transpose_eq_one [DecidableEq n] [Zero α] [One α] {M : Matrix n n α} : Mᵀ = 1 ↔ M = 1 :=
  transpose_eq_diagonal

@[simp]
/--
theorem `transpose_natCast` / 定理 `transpose_natCast`

English:
theorem transpose_natCast
  given: [DecidableEq n] [AddMonoidWithOne α] (d : Nat)
  proof: diagonal_transpose _

@[simp]

中文:
定理 transpose_natCast
  条件: [DecidableEq n] [AddMonoidWithOne α] (d : 自然数)
  证明: diagonal_transpose _

@[simp]

Depends on / 依赖: diagonal_transpose
-/
theorem transpose_natCast [DecidableEq n] [AddMonoidWithOne α] (d : Nat) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
/--
theorem `transpose_eq_natCast` / 定理 `transpose_eq_natCast`

English:
theorem transpose_eq_natCast
  given: [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n α} {d : Nat}
  proof: transpose_eq_diagonal

@[simp]

中文:
定理 transpose_eq_natCast
  条件: [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n α} {d : 自然数}
  证明: transpose_eq_diagonal

@[simp]

Depends on / 依赖: transpose_eq_diagonal
-/
theorem transpose_eq_natCast [DecidableEq n] [AddMonoidWithOne α] {M : Matrix n n α} {d : Nat} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

@[simp]
/--
theorem `transpose_ofNat` / 定理 `transpose_ofNat`

English:
theorem transpose_ofNat
  given: [DecidableEq n] [AddMonoidWithOne α] (d : Nat) [d.AtLeastTwo]
  proof: transpose_natCast _

@[simp]

中文:
定理 transpose_ofNat
  条件: [DecidableEq n] [AddMonoidWithOne α] (d : 自然数) [d.AtLeastTwo]
  证明: transpose_natCast _

@[simp]

Depends on / 依赖: transpose_natCast
-/
theorem transpose_ofNat [DecidableEq n] [AddMonoidWithOne α] (d : Nat) [d.AtLeastTwo] :
    (ofNat(d) : Matrix n n α)ᵀ = OfNat.ofNat d :=
  transpose_natCast _

@[simp]
/--
theorem `transpose_eq_ofNat` / 定理 `transpose_eq_ofNat`

English:
theorem transpose_eq_ofNat
  statement: [DecidableEq n] [AddMonoidWithOne α]
  proof: transpose_eq_diagonal

@[simp]

中文:
定理 transpose_eq_ofNat
  结论: [DecidableEq n] [AddMonoidWithOne α]
  证明: transpose_eq_diagonal

@[simp]

Depends on / 依赖: transpose_eq_diagonal
-/
theorem transpose_eq_ofNat [DecidableEq n] [AddMonoidWithOne α]
    {M : Matrix n n α} {d : Nat} [d.AtLeastTwo] :
    Mᵀ = ofNat(d) ↔ M = OfNat.ofNat d :=
  transpose_eq_diagonal

@[simp]
/--
theorem `transpose_intCast` / 定理 `transpose_intCast`

English:
theorem transpose_intCast
  given: [DecidableEq n] [AddGroupWithOne α] (d : Int)
  proof: diagonal_transpose _

@[simp]

中文:
定理 transpose_intCast
  条件: [DecidableEq n] [AddGroupWithOne α] (d : 整数)
  证明: diagonal_transpose _

@[simp]

Depends on / 依赖: diagonal_transpose
-/
theorem transpose_intCast [DecidableEq n] [AddGroupWithOne α] (d : Int) :
    (d : Matrix n n α)ᵀ = d :=
  diagonal_transpose _

@[simp]
/--
theorem `transpose_eq_intCast` / 定理 `transpose_eq_intCast`

English:
theorem transpose_eq_intCast
  statement: [DecidableEq n] [AddGroupWithOne α]
  proof: transpose_eq_diagonal

中文:
定理 transpose_eq_intCast
  结论: [DecidableEq n] [AddGroupWithOne α]
  证明: transpose_eq_diagonal

Depends on / 依赖: transpose_eq_diagonal
-/
theorem transpose_eq_intCast [DecidableEq n] [AddGroupWithOne α]
    {M : Matrix n n α} {d : Int} :
    Mᵀ = d ↔ M = d :=
  transpose_eq_diagonal

end Transpose

/--
theorem `submatrix_diagonal` / 定理 `submatrix_diagonal`

English:
theorem submatrix_diagonal
  statement: [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α) (e : l -> m)
  proof: ext fun i j => by
    rw [submatrix_apply]
    by_cases h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq, Function.comp_apply]
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]

中文:
定理 submatrix_diagonal
  结论: [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α) (e : l -> m)
  证明: ext fun i j => by
    rw [submatrix_apply]
    by_cases h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq, Function.comp_apply]
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, diagonal_apply_eq, diagonal_apply_ne, he.ne, submatrix_apply
-/
theorem submatrix_diagonal [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α) (e : l -> m)
    (he : Function.Injective e) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  ext fun i j => by
    rw [submatrix_apply]
    by_cases h : i = j
    · rw [h, diagonal_apply_eq, diagonal_apply_eq, Function.comp_apply]
    · rw [diagonal_apply_ne _ h, diagonal_apply_ne _ (he.ne h)]

/--
theorem `submatrix_one` / 定理 `submatrix_one`

English:
theorem submatrix_one
  statement: [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l -> m)
  proof: submatrix_diagonal _ e he

中文:
定理 submatrix_one
  结论: [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l -> m)
  证明: submatrix_diagonal _ e he

Depends on / 依赖: submatrix_diagonal
-/
theorem submatrix_one [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l -> m)
    (he : Function.Injective e) : (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_diagonal _ e he

/--
theorem `diag_submatrix` / 定理 `diag_submatrix`

English:
theorem diag_submatrix
  given: (A : Matrix m m α) (e : l -> m)
  statement: diag (A.submatrix e e) = A.diag ∘ e
  proof: rfl

中文:
定理 diag_submatrix
  条件: (A : Matrix m m α) (e : l -> m)
  结论: diag (A.submatrix e e) = A.diag ∘ e
  证明: rfl
-/
theorem diag_submatrix (A : Matrix m m α) (e : l -> m) : diag (A.submatrix e e) = A.diag ∘ e :=
  rfl

/-! `simp` lemmas for `Matrix.submatrix`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul`
for when the mappings are bundled. -/


@[simp]
/--
theorem `submatrix_diagonal_embedding` / 定理 `submatrix_diagonal_embedding`

English:
theorem submatrix_diagonal_embedding
  statement: [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α)
  proof: submatrix_diagonal d e e.injective

@[simp]

中文:
定理 submatrix_diagonal_embedding
  结论: [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α)
  证明: submatrix_diagonal d e e.injective

@[simp]

Depends on / 依赖: e.injective, injective, submatrix_diagonal
-/
theorem submatrix_diagonal_embedding [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α)
    (e : l ↪ m) : (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
/--
theorem `submatrix_diagonal_equiv` / 定理 `submatrix_diagonal_equiv`

English:
theorem submatrix_diagonal_equiv
  given: [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α) (e : l ≃ m)
  proof: submatrix_diagonal d e e.injective

@[simp]

中文:
定理 submatrix_diagonal_equiv
  条件: [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α) (e : l ≃ m)
  证明: submatrix_diagonal d e e.injective

@[simp]

Depends on / 依赖: e.injective, injective, submatrix_diagonal
-/
theorem submatrix_diagonal_equiv [Zero α] [DecidableEq m] [DecidableEq l] (d : m -> α) (e : l ≃ m) :
    (diagonal d).submatrix e e = diagonal (d ∘ e) :=
  submatrix_diagonal d e e.injective

@[simp]
/--
theorem `submatrix_one_embedding` / 定理 `submatrix_one_embedding`

English:
theorem submatrix_one_embedding
  given: [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m)
  proof: submatrix_one e e.injective

@[simp]

中文:
定理 submatrix_one_embedding
  条件: [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m)
  证明: submatrix_one e e.injective

@[simp]

Depends on / 依赖: e.injective, injective, submatrix_one
-/
theorem submatrix_one_embedding [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ↪ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

@[simp]
/--
theorem `submatrix_one_equiv` / 定理 `submatrix_one_equiv`

English:
theorem submatrix_one_equiv
  given: [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m)
  proof: submatrix_one e e.injective

中文:
定理 submatrix_one_equiv
  条件: [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m)
  证明: submatrix_one e e.injective

Depends on / 依赖: e.injective, injective, submatrix_one
-/
theorem submatrix_one_equiv [Zero α] [One α] [DecidableEq m] [DecidableEq l] (e : l ≃ m) :
    (1 : Matrix m m α).submatrix e e = 1 :=
  submatrix_one e e.injective

end Matrix
