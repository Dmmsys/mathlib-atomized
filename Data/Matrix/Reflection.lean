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

This allows "proof by reflection", where we prove `A = !![A 0 0, A 0 1;  A 1 0, A 1 1]` by defining
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

variable {l m n : ℕ} {α : Type*}

/-- `∀` with better defeq for `∀ x : Matrix (Fin m) (Fin n) α, P x`. -/
/-
**Matrix.Forall** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：Forall : forall {m n} (_ : Matrix (Fin m) (Fin n) α -> Prop), Prop | 0, _,
 P => P (of ![]) | _ + 1, _, P => FinVec.Forall fun r => Forall fun A => P (of (
Matrix.vecCons r A))  /-- This can be used to prove ```lean example (P : Matrix 
(Fin 2) (Fin 3) α → Prop) : (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f]
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`∀` with better defeq for `∀ x : Matrix (Fin m) (Fin n) α, P x`. -/
-/
def Forall : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Forall fun r => Forall fun A => P (of (Matrix.vecCons r A))

/-- This can be used to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
(forall_iff _).symm
```
-/
/-
**Matrix.forall_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：forall_iff : forall {m n} (P : Matrix (Fin m) (Fin n) α -> Prop), Forall P
 ↔ forall x, P x | 0, _, _ => Iff.symm Fin.forall_fin_zero_pi | m + 1, n, P => b
y simp only [Forall, FinVec.forall_iff, forall_iff] exact Iff.symm Fin.forall_fi
n_succ_pi  example (P : Matrix (Fin 2) (Fin 3) α -> Prop) : (forall x, P x) ↔ fo
rall a b c d e f, P !![a, b, c; d, e, f]
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
(forall_iff _).symm
```
-/
theorem forall_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Forall P ↔ ∀ x, P x
  | 0, _, _ => Iff.symm Fin.forall_fin_zero_pi
  | m + 1, n, P => by
    simp only [Forall, FinVec.forall_iff, forall_iff]
    exact Iff.symm Fin.forall_fin_succ_pi
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
    (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
  (forall_iff _).symm

/-- `∃` with better defeq for `∃ x : Matrix (Fin m) (Fin n) α, P x`. -/
/-
**Matrix.Exists** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：Exists : forall {m n} (_ : Matrix (Fin m) (Fin n) α -> Prop), Prop | 0, _,
 P => P (of ![]) | _ + 1, _, P => FinVec.Exists fun r => Exists fun A => P (of (
Matrix.vecCons r A))  /-- This can be used to prove ```lean example (P : Matrix 
(Fin 2) (Fin 3) α → Prop) : (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f]
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`∃` with better defeq for `∃ x : Matrix (Fin m) (Fin n) α, P x`. -/
-/
def Exists : ∀ {m n} (_ : Matrix (Fin m) (Fin n) α → Prop), Prop
  | 0, _, P => P (of ![])
  | _ + 1, _, P => FinVec.Exists fun r => Exists fun A => P (of (Matrix.vecCons r A))

/-- This can be used to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
(exists_iff _).symm
```
-/
/-
**Matrix.exists_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exists_iff : forall {m n} (P : Matrix (Fin m) (Fin n) α -> Prop), Exists P
 ↔ exists x, P x | 0, _, _ => Iff.symm Fin.exists_fin_zero_pi | m + 1, n, P => b
y simp only [Exists, FinVec.exists_iff, exists_iff] exact Iff.symm Fin.exists_fi
n_succ_pi  example (P : Matrix (Fin 2) (Fin 3) α -> Prop) : (exists x, P x) ↔ ex
ists a b c d e f, P !![a, b, c; d, e, f]
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used to prove
```lean
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
  (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
(exists_iff _).symm
```
-/
theorem exists_iff : ∀ {m n} (P : Matrix (Fin m) (Fin n) α → Prop), Exists P ↔ ∃ x, P x
  | 0, _, _ => Iff.symm Fin.exists_fin_zero_pi
  | m + 1, n, P => by
    simp only [Exists, FinVec.exists_iff, exists_iff]
    exact Iff.symm Fin.exists_fin_succ_pi
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (P : Matrix (Fin 2) (Fin 3) α → Prop) :
    (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
  (exists_iff _).symm

/-- `Matrix.transpose` with better defeq for `Fin` -/
/-
**Matrix.transpose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transpose (M : Matrix m n α) : Matrix n m α
参数：M : Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.transpose` with better defeq for `Fin`
-/
def transposeᵣ : ∀ {m n}, Matrix (Fin m) (Fin n) α → Matrix (Fin n) (Fin m) α
  | _, 0, _ => of ![]
  | _, _ + 1, A =>
    of <| vecCons (FinVec.map (fun v : Fin _ → α => v 0) A) (transposeᵣ (A.submatrix id Fin.succ))

set_option backward.isDefEq.respectTransparency false in
/-- This can be used to prove
```lean
example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] := (transposeᵣ_eq _).symm
```
-/
@[simp]
/-
**Matrix.transpose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transpose (M : Matrix m n α) : Matrix n m α
参数：M : Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used to prove
```lean
example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] := (transposeᵣ
_eq _).symm
```
-/
theorem transposeᵣ_eq : ∀ {m n} (A : Matrix (Fin m) (Fin n) α), transposeᵣ A = transpose A
  | _, 0, _ => Subsingleton.elim _ _
  | m, n + 1, A =>
    Matrix.ext fun i j => by
      simp_rw [transposeᵣ, transposeᵣ_eq]
      refine i.cases ?_ fun i => ?_
      · dsimp
        rw [FinVec.map_eq, Function.comp_apply]
      · simp only [of_apply, Matrix.cons_val_succ]
        rfl
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] :=
  (transposeᵣ_eq _).symm

/-- `dotProduct` with better defeq for `Fin` -/
/-
**Matrix.dotProduct** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dotProduct` with better defeq for `Fin`
-/
def dotProductᵣ [Mul α] [Add α] [Zero α] {m} (a b : Fin m → α) : α :=
  FinVec.sum <| FinVec.seq (FinVec.map (· * ·) a) b

/-- This can be used to prove
```lean
example (a b c d : α) [Mul α] [AddCommMonoid α] :
  dot_product ![a, b] ![c, d] = a * c + b * d :=
(dot_productᵣ_eq _ _).symm
```
-/
@[simp]
/-
**Matrix.dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used to prove
```lean
example (a b c d : α) [Mul α] [AddCommMonoid α] :
  dot_product ![a, b] ![c, d] = a * c + b * d :=
(dot_productᵣ_eq _ _).symm
```
-/
theorem dotProductᵣ_eq [Mul α] [AddCommMonoid α] {m} (a b : Fin m → α) :
    dotProductᵣ a b = a ⬝ᵥ b := by
  simp_rw [dotProductᵣ, dotProduct, FinVec.sum_eq, FinVec.seq_eq, FinVec.map_eq,
      Function.comp_apply]
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (a b c d : α) [Mul α] [AddCommMonoid α] : ![a, b] ⬝ᵥ ![c, d] = a * c + b * d :=
  (dotProductᵣ_eq _ _).symm

/-- `Matrix.mul` with better defeq for `Fin` -/
/-
**Matrix.mul** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.mul` with better defeq for `Fin`
-/
def mulᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (B : Matrix (Fin m) (Fin n) α) :
    Matrix (Fin l) (Fin n) α :=
  of <| FinVec.map (fun v₁ => FinVec.map (fun v₂ => dotProductᵣ v₁ v₂) Bᵀ) A

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
/-
**Matrix.mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used to prove
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
theorem mulᵣ_eq [Mul α] [AddCommMonoid α] (A : Matrix (Fin l) (Fin m) α)
    (B : Matrix (Fin m) (Fin n) α) : mulᵣ A B = A * B := by
  simp [mulᵣ, Matrix.transpose]
  rfl
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [AddCommMonoid α] [Mul α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁₁ b₁₂ b₂₁ b₂₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![b₁₁, b₁₂; b₂₁, b₂₂] =
      !![a₁₁ * b₁₁ + a₁₂ * b₂₁, a₁₁ * b₁₂ + a₁₂ * b₂₂;
        a₂₁ * b₁₁ + a₂₂ * b₂₁, a₂₁ * b₁₂ + a₂₂ * b₂₂] :=
  (mulᵣ_eq _ _).symm

/-- `Matrix.mulVec` with better defeq for `Fin` -/
/-
**Matrix.mulVec** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemir
ing α] → [Fintype n] → Matrix m n α → (n → α) → m → α
参数：n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.mulVec` with better defeq for `Fin`
-/
def mulVecᵣ [Mul α] [Add α] [Zero α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m → α) : Fin l → α :=
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
/-
**Matrix.mulVec** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemir
ing α] → [Fintype n] → Matrix m n α → (n → α) → m → α
参数：n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁*b₁ + a₁₂*b₂, a₂₁*b₁ + a₂₂*b₂] :=
(mulVecᵣ_eq _ _).symm
```
-/
theorem mulVecᵣ_eq [NonUnitalNonAssocSemiring α] (A : Matrix (Fin l) (Fin m) α) (v : Fin m → α) :
    mulVecᵣ A v = A *ᵥ v := by
  simp [mulVecᵣ]
  rfl
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] *ᵥ ![b₁, b₂] = ![a₁₁ * b₁ + a₁₂ * b₂, a₂₁ * b₁ + a₂₂ * b₂] :=
  (mulVecᵣ_eq _ _).symm

/-- `Matrix.vecMul` with better defeq for `Fin` -/
/-
**Matrix.vecMul** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemir
ing α] → [Fintype m] → (m → α) → Matrix m n α → n → α
参数：m → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix.vecMul` with better defeq for `Fin`
-/
def vecMulᵣ [Mul α] [Add α] [Zero α] (v : Fin l → α) (A : Matrix (Fin l) (Fin m) α) : Fin m → α :=
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
/-
**Matrix.vecMul** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_2} →   {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemir
ing α] → [Fintype m] → (m → α) → Matrix m n α → n → α
参数：m → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This can be used to prove
```lean
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
  ![b₁, b₂] ᵥ* !![a₁₁, a₁₂;
                       a₂₁, a₂₂] = ![b₁*a₁₁ + b₂*a₂₁, b₁*a₁₂ + b₂*a₂₂] :=
(vecMulᵣ_eq _ _).symm
```
-/
theorem vecMulᵣ_eq [NonUnitalNonAssocSemiring α] (v : Fin l → α) (A : Matrix (Fin l) (Fin m) α) :
    vecMulᵣ v A = v ᵥ* A := by
  simp [vecMulᵣ]
  rfl
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [NonUnitalNonAssocSemiring α] (a₁₁ a₁₂ a₂₁ a₂₂ b₁ b₂ : α) :
    ![b₁, b₂] ᵥ* !![a₁₁, a₁₂; a₂₁, a₂₂] = ![b₁ * a₁₁ + b₂ * a₂₁, b₁ * a₁₂ + b₂ * a₂₂] :=
  (vecMulᵣ_eq _ _).symm

/-- Expand `A` to `!![A 0 0, ...; ..., A m n]` -/
/-
**Matrix.etaExpand** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：etaExpand {m n} (A : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α
参数：A : Matrix (Fin m) (Fin n) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Expand `A` to `!![A 0 0, ...; ..., A m n]`
-/
def etaExpand {m n} (A : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  Matrix.of (FinVec.etaExpand fun i => FinVec.etaExpand fun j => A i j)

/-- This can be used to prove
```lean
example (A : Matrix (Fin 2) (Fin 2) α) :
  A = !![A 0 0, A 0 1;
         A 1 0, A 1 1] :=
(etaExpand_eq _).symm
```
-/
/-
**Matrix.etaExpand_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：etaExpand_eq {m n} (A : Matrix (Fin m) (Fin n) α) : etaExpand A = A
参数：A : Matrix (Fin m) (Fin n) α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FinVec.etaExpand_eq`：etaExpand_eq {m} (v : Fin m -> α) : etaExpand v = v
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
This can be used to prove
```lean
example (A : Matrix (Fin 2) (Fin 2) α) :
  A = !![A 0 0, A 0 1;
         A 1 0, A 1 1] :=
(etaExpand_eq _).symm
```
-/
theorem etaExpand_eq {m n} (A : Matrix (Fin m) (Fin n) α) : etaExpand A = A := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  simp_rw [etaExpand, FinVec.etaExpand_eq, Matrix.of]
  rfl
/-
**Matrix.** 是 Mathlib 中的一个示例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (A : Matrix (Fin 2) (Fin 2) α) : A = !![A 0 0, A 0 1; A 1 0, A 1 1] :=
  (etaExpand_eq _).symm

end Matrix

