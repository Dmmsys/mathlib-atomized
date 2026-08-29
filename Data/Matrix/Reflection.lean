/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Lemmas for concrete matrices `Matrix (Fin m) (Fin n) α`

This file contains alternative definitions of common operators on matrices that expand
definitionally to the expected expression when evaluated on `!![]` notation.

This allows "proof by reflection", where we prove `A = !![A 0 0, A 0 1; A 1 0, A 1 1]` by defining
`Matrix.etaExpand A` to be equal to the RHS definitionally, and then prove that
`A = eta_expand A`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitions

* `Matrix.transposeᵣ`
* `dotProductᵣ`
* `Matrix.mulᵣ`
* `Matrix.mulVecᵣ`
* `Matrix.vecMulᵣ`
* `Matrix.etaExpand`

-/

@[expose] public section


open Matrix

namespace Matrix

variable {l m n : Nat} {α : Type*}

/--
Definition of `Forall` / `Forall` 的定义

English:
definition Forall
  signature: : forall {m n} (_ : Matrix (Fin m) (Fin n) α -> Prop), Prop

中文:
定义 任意
  签名: : 对任意 {m n} (_ : 矩阵 (有限集 m) (有限集 n) α -> 命题), 命题

Depends on / 依赖: forall_iff
-/
def Forall : forall {m n} (_ : Matrix (Fin m) (Fin n) α -> Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Forall fun r => Forall fun A => P (of (Matrix.vecCons r A))

/--
theorem `forall_iff` / 定理 `forall_iff`

English:
theorem forall_iff
  statement: forall {m n} (P : Matrix (Fin m) (Fin n) α -> Prop), Forall P ↔ forall x, P x
  proof: (forall_iff _).symm

中文:
定理 对任意_iff
  结论: 对任意 {m n} (P : 矩阵 (有限集 m) (有限集 n) α -> 命题), 任意 P ↔ 对任意 x, P x
  证明: (forall_iff _).symm

Depends on / 依赖: forall_iff
-/
theorem forall_iff : forall {m n} (P : Matrix (Fin m) (Fin n) α -> Prop), Forall P ↔ forall x, P x
  | 0, _, _ => Iff.symm Fin.forall_fin_zero_pi
  | m + 1, n, P => by
    simp only [Forall, FinVec.forall_iff, forall_iff]
    exact Iff.symm Fin.forall_fin_succ_pi

example (P : Matrix (Fin 2) (Fin 3) α -> Prop) :
    (forall x, P x) ↔ forall a b c d e f, P !![a, b, c; d, e, f] :=
  (forall_iff _).symm

/--
Definition of `Exists` / `Exists` 的定义

English:
definition Exists
  signature: : forall {m n} (_ : Matrix (Fin m) (Fin n) α -> Prop), Prop

中文:
定义 存在
  签名: : 对任意 {m n} (_ : 矩阵 (有限集 m) (有限集 n) α -> 命题), 命题

Depends on / 依赖: exists_iff
-/
def Exists : forall {m n} (_ : Matrix (Fin m) (Fin n) α -> Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Exists fun r => Exists fun A => P (of (Matrix.vecCons r A))

/--
theorem `exists_iff` / 定理 `exists_iff`

English:
theorem exists_iff
  statement: forall {m n} (P : Matrix (Fin m) (Fin n) α -> Prop), Exists P ↔ exists x, P x
  proof: (exists_iff _).symm

中文:
定理 存在_iff
  结论: 对任意 {m n} (P : 矩阵 (有限集 m) (有限集 n) α -> 命题), 存在 P ↔ 存在 x, P x
  证明: (exists_iff _).symm

Depends on / 依赖: exists_iff
-/
theorem exists_iff : forall {m n} (P : Matrix (Fin m) (Fin n) α -> Prop), Exists P ↔ exists x, P x
  | 0, _, _ => Iff.symm Fin.exists_fin_zero_pi
  | m + 1, n, P => by
    simp only [Exists, FinVec.exists_iff, exists_iff]
    exact Iff.symm Fin.exists_fin_succ_pi

example (P : Matrix (Fin 2) (Fin 3) α -> Prop) :
    (exists x, P x) ↔ exists a b c d e f, P !![a, b, c; d, e, f] :=
  (exists_iff _).symm

/--
Definition of `transposeᵣ` / `transposeᵣ` 的定义

English:
definition transposeᵣ
  signature: : forall {m n}, Matrix (Fin m) (Fin n) α -> Matrix (Fin n) (Fin m) α

中文:
定义 transposeᵣ
  签名: : 对任意 {m n}, 矩阵 (有限集 m) (有限集 n) α -> 矩阵 (有限集 n) (有限集 m) α
-/
def transposeᵣ : forall {m n}, Matrix (Fin m) (Fin n) α -> Matrix (Fin n) (Fin m) α
  | _, 0, _ => of ![]
  | _, _ + 1, A =>
of vecCons (FinVec.map (fun v : Fin _ -> α => v 0) A) (transposeᵣ (A.submatrix id Fin.succ))

set_option backward.isDefEq.respectTransparency false in
/-- This can be used to prove
```lean
example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] := (transposeᵣ_eq _).symm
```
-/
@[simp]
/--
theorem `transposeᵣ_eq` / 定理 `transposeᵣ_eq`

English:
theorem transposeᵣ_eq
  statement: forall {m n} (A : Matrix (Fin m) (Fin n) α), transposeᵣ A = transpose A
  proof: (transposeᵣ_eq _).symm

中文:
定理 transposeᵣ_eq
  结论: 对任意 {m n} (A : 矩阵 (有限集 m) (有限集 n) α), transposeᵣ A = transpose A
  证明: (transposeᵣ_eq _).symm
-/
theorem transposeᵣ_eq : forall {m n} (A : Matrix (Fin m) (Fin n) α), transposeᵣ A = transpose A
  | _, 0, _ => Subsingleton.elim _ _
  | m, n + 1, A =>
    Matrix.ext fun i j => by
      simp_rw [transposeᵣ, transposeᵣ_eq]
      refine i.cases ?_ fun i => ?_
      · dsimp
        rw [FinVec.map_eq]; rw [Function.comp_apply]
      · simp only [of_apply, Matrix.cons_val_succ]
        rfl

example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] :=
  (transposeᵣ_eq _).symm

/--
Definition of `dotProductᵣ` / `dotProductᵣ` 的定义

English:
definition dotProductᵣ
  signature: [Mul α] [Add α] [Zero α] {m} (a b : Fin m -> α)
  body: FinVec.sum FinVec.seq (FinVec.map (· * ·) a) b

中文:
定义 dotProductᵣ
  签名: [乘法 α] [加法 α] [零 α] {m} (a b : 有限集 m -> α)
  定义体: FinVec.sum FinVec.seq (FinVec.map (· * ·) a) b

Depends on / 依赖: FinVec, FinVec.map, FinVec.seq, FinVec.sum
-/
def dotProductᵣ [Mul α] [Add α] [Zero α] {m} (a b : Fin m -> α) : α :=
FinVec.sum FinVec.seq (FinVec.map (· * ·) a) b

/-- This can be used to prove
```lean
example (a b c d : α) [Mul α] [AddCommMonoid α] :
  dot_product ![a, b] ![c, d] = a * c + b * d :=
(dot_productᵣ_eq _ _).symm
```
-/
@[simp]
/--
theorem `dotProductᵣ_eq` / 定理 `dotProductᵣ_eq`

English:
theorem dotProductᵣ_eq
  given: [Mul α] [AddCommMonoid α] {m} (a b : Fin m -> α)
  proof: by
  simp_rw [dotProductᵣ, dotProduct, FinVec.sum_eq, FinVec.seq_eq, FinVec.map_eq,
      Function.comp_apply]

example (a b c d : α) [Mul α] [AddCommMonoid α] : ![a, b] ⬝ᵥ ![c, d] = a * c + b * d :=
  (dotProductᵣ_eq _ _).symm

中文:
定理 dotProductᵣ_eq
  条件: [乘法 α] [加法交换幺半群 α] {m} (a b : 有限集 m -> α)
  证明: by
  simp_rw [dotProductᵣ, dotProduct, FinVec.sum_eq, FinVec.seq_eq, FinVec.map_eq,
      Function.comp_apply]

example (a b c d : α) [Mul α] [AddCommMonoid α] : ![a, b] ⬝ᵥ ![c, d] = a * c + b * d :=
  (dotProductᵣ_eq _ _).symm

Depends on / 依赖: FinVec, FinVec.map_eq, FinVec.seq_eq, FinVec.sum_eq, Function, Function.comp_apply, comp_apply, dotProduct, map_eq, seq_eq, simp_rw, sum_eq
-/
theorem dotProductᵣ_eq [Mul α] [AddCommMonoid α] {m} (a b : Fin m -> α) :
    dotProductᵣ a b = a ⬝ᵥ b := by
  simp_rw [dotProductᵣ, dotProduct, FinVec.sum_eq, FinVec.seq_eq, FinVec.map_eq,
      Function.comp_apply]

example (a b c d : α) [Mul α] [AddCommMonoid α] : ![a, b] ⬝ᵥ ![c, d] = a * c + b * d :=
  (dotProductᵣ_eq _ _).symm

/--
Definition of `mulᵣ` / `mulᵣ` 的定义

English:
definition mulᵣ
  signature: [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (B : Matrix (Fin m) (Fin n) α)
  body: of FinVec.map (fun v₁ => FinVec.map (fun v₂ => dotProductᵣ v₁ v₂) Bᵀ) A

中文:
定义 mulᵣ
  签名: [乘法 α] [加法 α] [零 α] (A : 矩阵 (有限集 l) (有限集 m) α) (B : 矩阵 (有限集 m) (有限集 n) α)
  定义体: of FinVec.map (fun v₁ => FinVec.map (fun v₂ => dotProductᵣ v₁ v₂) Bᵀ) A

Depends on / 依赖: FinVec, FinVec.map
-/
def mulᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (B : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin l) (Fin n) α :=
of FinVec.map (fun v₁ => FinVec.map (fun v₂ => dotProductᵣ v₁ v₂) Bᵀ) A

set_option backward.isDefEq.respectTransparency false in
/-- This can be used to prove
```lean
example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] * !![b₁₁, b₁₂;
                    b₂₁, b₂₂] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁, a₁₁*b₁₂ + a₁₂*b₂₂;
     a₂₁*b₁₁ + a₂₂*b₂₁, a₂₁*b₁₂ + a₂₂*b₂₂] :=
(mulᵣ_eq _ _).symm
```
-/
@[simp]
/--
theorem `mulᵣ_eq` / 定理 `mulᵣ_eq`

English:
theorem mulᵣ_eq
  statement: [Mul α] [AddCommMonoid α] (A : Matrix (Fin l) (Fin m) α)
  proof: by
  simp [mulᵣ, Matrix.transpose]
  rfl

example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
        a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  (mulᵣ_eq _ _).symm

中文:
定理 mulᵣ_eq
  结论: [乘法 α] [加法交换幺半群 α] (A : 矩阵 (有限集 l) (有限集 m) α)
  证明: by
  simp [mulᵣ, Matrix.transpose]
  rfl

example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
        a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  (mulᵣ_eq _ _).symm

Depends on / 依赖: Matrix, Matrix.transpose, transpose
-/
theorem mulᵣ_eq [Mul α] [AddCommMonoid α] (A : Matrix (Fin l) (Fin m) α)
    (B : Matrix (Fin m) (Fin n) α) : mulᵣ A B = A * B := by
  simp [mulᵣ, Matrix.transpose]
  rfl

example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
        a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  (mulᵣ_eq _ _).symm

/--
Definition of `mulVecᵣ` / `mulVecᵣ` 的定义

English:
definition mulVecᵣ
  signature: [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m -> α)
  body: FinVec.map (fun a => dotProductᵣ a v) A

中文:
定义 mulVecᵣ
  签名: [乘法 α] [加法 α] [零 α] (A : 矩阵 (有限集 l) (有限集 m) α) (v : 有限集 m -> α)
  定义体: FinVec.map (fun a => dotProductᵣ a v) A

Depends on / 依赖: FinVec, FinVec.map
-/
def mulVecᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m -> α) : Fin l -> α :=
  FinVec.map (fun a => dotProductᵣ a v) A

set_option backward.isDefEq.respectTransparency false in
/-- This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁*b₁ + a₁₂*b₂, a₂₁*b₁ + a₂₂*b₂] :=
(mulVecᵣ_eq _ _).symm
```
-/
@[simp]
/--
theorem `mulVecᵣ_eq` / 定理 `mulVecᵣ_eq`

English:
theorem mulVecᵣ_eq
  given: [NonUnitalNonAssocSemiring α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m -> α)
  proof: by
  simp [mulVecᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁ * b₁ + a₁₂ * b₂, a₂₁ * b₁ + a₂₂ * b₂] :=
  (mulVecᵣ_eq _ _).symm

中文:
定理 mulVecᵣ_eq
  条件: [非幺非结合半环 α] (A : 矩阵 (有限集 l) (有限集 m) α) (v : 有限集 m -> α)
  证明: by
  simp [mulVecᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁ * b₁ + a₁₂ * b₂, a₂₁ * b₁ + a₂₂ * b₂] :=
  (mulVecᵣ_eq _ _).symm
-/
theorem mulVecᵣ_eq [NonUnitalNonAssocSemiring α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m -> α) :
    mulVecᵣ A v = A *ᵥ v := by
  simp [mulVecᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁ * b₁ + a₁₂ * b₂, a₂₁ * b₁ + a₂₂ * b₂] :=
  (mulVecᵣ_eq _ _).symm

/--
Definition of `vecMulᵣ` / `vecMulᵣ` 的定义

English:
definition vecMulᵣ
  signature: [Mul α] [Add α] [Zero α] (v : Fin l -> α) (A : Matrix (Fin l) (Fin m) α)
  body: FinVec.map (fun a => dotProductᵣ v a) Aᵀ

中文:
定义 vecMulᵣ
  签名: [乘法 α] [加法 α] [零 α] (v : 有限集 l -> α) (A : 矩阵 (有限集 l) (有限集 m) α)
  定义体: FinVec.map (fun a => dotProductᵣ v a) Aᵀ

Depends on / 依赖: FinVec, FinVec.map
-/
def vecMulᵣ [Mul α] [Add α] [Zero α] (v : Fin l -> α) (A : Matrix (Fin l) (Fin m) α) : Fin m -> α :=
  FinVec.map (fun a => dotProductᵣ v a) Aᵀ

set_option backward.isDefEq.respectTransparency false in
/-- This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  ![b₁, b₂] ᵥ* !![a₁₁, a₁₂;
                       a₂₁, a₂₂] = ![b₁*a₁₁ + b₂*a₂₁, b₁*a₁₂ + b₂*a₂₂] :=
(vecMulᵣ_eq _ _).symm
```
-/
@[simp]
/--
theorem `vecMulᵣ_eq` / 定理 `vecMulᵣ_eq`

English:
theorem vecMulᵣ_eq
  given: [NonUnitalNonAssocSemiring α] (v : Fin l -> α) (A : Matrix (Fin l) (Fin m) α)
  proof: by
  simp [vecMulᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    ![b₁, b₂] ᵥ* !![a₁₁, a₁₂; a₂₁, a₂₂] = ![b₁ * a₁₁ + b₂ * a₂₁, b₁ * a₁₂ + b₂ * a₂₂] :=
  (vecMulᵣ_eq _ _).symm

中文:
定理 vecMulᵣ_eq
  条件: [非幺非结合半环 α] (v : 有限集 l -> α) (A : 矩阵 (有限集 l) (有限集 m) α)
  证明: by
  simp [vecMulᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    ![b₁, b₂] ᵥ* !![a₁₁, a₁₂; a₂₁, a₂₂] = ![b₁ * a₁₁ + b₂ * a₂₁, b₁ * a₁₂ + b₂ * a₂₂] :=
  (vecMulᵣ_eq _ _).symm
-/
theorem vecMulᵣ_eq [NonUnitalNonAssocSemiring α] (v : Fin l -> α) (A : Matrix (Fin l) (Fin m) α) :
    vecMulᵣ v A = v ᵥ* A := by
  simp [vecMulᵣ]
  rfl

example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    ![b₁, b₂] ᵥ* !![a₁₁, a₁₂; a₂₁, a₂₂] = ![b₁ * a₁₁ + b₂ * a₂₁, b₁ * a₁₂ + b₂ * a₂₂] :=
  (vecMulᵣ_eq _ _).symm

/--
Definition of `etaExpand` / `etaExpand` 的定义

English:
definition etaExpand
  signature: {m n} (A : Matrix (Fin m) (Fin n) α)
  body: Matrix.of (FinVec.etaExpand fun i => FinVec.etaExpand fun j => A i j)

中文:
定义 etaExpand
  签名: {m n} (A : 矩阵 (有限集 m) (有限集 n) α)
  定义体: Matrix.of (FinVec.etaExpand fun i => FinVec.etaExpand fun j => A i j)

Depends on / 依赖: FinVec, FinVec.etaExpand, Matrix, Matrix.of, etaExpand
-/
def etaExpand {m n} (A : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  Matrix.of (FinVec.etaExpand fun i => FinVec.etaExpand fun j => A i j)

/--
theorem `etaExpand_eq` / 定理 `etaExpand_eq`

English:
theorem etaExpand_eq
  given: {m n} (A : Matrix (Fin m) (Fin n) α)
  statement: etaExpand A = A
  proof: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  simp_rw [etaExpand, FinVec.etaExpand_eq, Matrix.of]
  rfl

example (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
  (etaExpand_eq _).symm

中文:
定理 etaExpand_eq
  条件: {m n} (A : 矩阵 (有限集 m) (有限集 n) α)
  结论: etaExpand A = A
  证明: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  simp_rw [etaExpand, FinVec.etaExpand_eq, Matrix.of]
  rfl

example (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
  (etaExpand_eq _).symm

Depends on / 依赖: Before, FinVec, FinVec.etaExpand_eq, Mathlib, Matrix, Matrix.of, adaptation_note, canonicalizer, closed, directed, etaExpand, etaExpand_eq, github, github.com, leanprover, minimization, normalizer, original, problem, replacing
-/
theorem etaExpand_eq {m n} (A : Matrix (Fin m) (Fin n) α) : etaExpand A = A := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  simp_rw [etaExpand, FinVec.etaExpand_eq, Matrix.of]
  rfl

example (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
  (etaExpand_eq _).symm

end Matrix
