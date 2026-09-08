/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Peter Nelson
-/
module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Factorial.SuperFactorial
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.
For each `CommRing R`, and function `v : Fin n → R` the matrix `vandermonde v`
is defined to be `Fin n` by `Fin n` matrix `V` whose `i`th row is `[1, (v i), (v i)^2, ...]`.
This matrix has determinant equal to the product of `v i - v j` over all unordered pairs `i,j`,
and therefore is nonsingular if and only if `v` is injective.

`vandermonde v` is a special case of two more general matrices we also define.
For a type `α` and functions `v w : α → R`, we write `rectVandermonde v w n` for
the `α × Fin n` matrix with `i`th row `[(w i) ^ (n-1), (v i) * (w i)^(n-2), ..., (v i)^(n-1)]`.
`projVandermonde v w = rectVandermonde v w n` is the square matrix case, where `α = Fin n`.
The determinant of `projVandermonde v w` is the product of `v j * w i - v i * w j`,
taken over all pairs `i,j` with `i < j`, which gives a similar characterization of
when it is nonsingular. Since `vandermonde v w = projVandermonde v 1`,
we can derive most of the API for the former in terms of the latter.

These extensions of Vandermonde matrices arise in the study of complete arcs in finite geometry,
coding theory, and representations of uniform matroids over finite fields.

## Main definitions

* `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.
* `rectVandermonde v w n`: an `α × Fin n` matrix whose
  `i, j`-th entry is `(v i) ^ j * (w i) ^ (n-1-j)`.
* `projVandermonde v w`: a square matrix whose `i, j`-th entry is `(v i) ^ j * (w i) ^ (n-1-j)`.

## Main results

* `det_vandermonde`: `det (vandermonde v)` is the product of `v j - v i`, where
  `(i, j)` ranges over the set of pairs with `i < j`.
* `det_projVandermonde`: `det (projVandermonde v w)` is the product of `v j * w i - v i * w j`,
  taken over all pairs with `i < j`.

## Implementation notes

We derive the `det_vandermonde` formula from `det_projVandermonde`,
which is proved using an induction argument involving row operations and division.
To circumvent issues with non-invertible elements while still maintaining the generality of rings,
we first prove it for fields using the private lemma `det_projVandermonde_of_field`,
and then use an algebraic workaround to generalize to the ring case,
stating the strictly more general form as `det_projVandermonde`.

## TODO

Characterize when `rectVandermonde v w n` has linearly independent rows.
-/

@[expose] public section

variable {R K : Type*} [CommRing R] [Field K] {n : ℕ}

open Equiv Finset

open Matrix Fin

namespace Matrix

/-- A matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (n-1)]` -/
/-
**Matrix.rectVandermonde** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：rectVandermonde {α : Type*} (v w : α -> R) (n : Nat) : Matrix α (Fin n) R
参数：v w : α -> R；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (n-1)]`
-/
def rectVandermonde {α : Type*} (v w : α → R) (n : ℕ) : Matrix α (Fin n) R :=
  .of fun i j ↦ (v i) ^ j.1 * (w i) ^ j.rev.1

/-- A square matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (n-1)]` -/
/-
**Matrix.projVandermonde** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：projVandermonde (v w : Fin n -> R) : Matrix (Fin n) (Fin n) R
参数：v w : Fin n -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square matrix with rows all having the form `[b^(n-1), a * b^(n-2), ..., a ^ (
n-1)]`
-/
def projVandermonde (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  rectVandermonde v w n

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`. -/
/-
**Matrix.vandermonde** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vandermonde (v : Fin n -> R) : Matrix (Fin n) (Fin n) R
参数：v : Fin n -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v
 i ^ 3, ...`.
-/
def vandermonde (v : Fin n → R) : Matrix (Fin n) (Fin n) R := .of fun i j ↦ (v i) ^ j.1
/-
**Matrix.vandermonde_eq_projVandermonde** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：vandermonde_eq_projVandermonde (v : Fin n -> R) : vandermonde v = projVand
ermonde v 1
参数：v : Fin n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vandermonde_eq_projVandermonde (v : Fin n → R) : vandermonde v = projVandermonde v 1 := by
  simp [projVandermonde, rectVandermonde, vandermonde]

/-- We don't mark this as `@[simp]` because the RHS is not simp-nf,
and simplifying the RHS gives a bothersome `Nat` subtraction. -/
/-
**Matrix.projVandermonde_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：projVandermonde_apply {v w : Fin n -> R} {i j : Fin n} : projVandermonde v
 w i j = (v i) ^ j.1 * (w i) ^ j.rev.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We don't mark this as `@[simp]` because the RHS is not simp-nf,
and simplifying the RHS gives a bothersome `Nat` subtraction.
-/
theorem projVandermonde_apply {v w : Fin n → R} {i j : Fin n} :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl
/-
**Matrix.rectVandermonde_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rectVandermonde_apply {α : Type*} {v w : α -> R} {i : α} {j : Fin n} : rec
tVandermonde v w n i j = (v i) ^ j.1 * (w i) ^ j.rev.1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rectVandermonde_apply {α : Type*} {v w : α → R} {i : α} {j : Fin n} :
    rectVandermonde v w n i j = (v i) ^ j.1 * (w i) ^ j.rev.1 := rfl

@[simp]
/-
**Matrix.vandermonde_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vandermonde_apply (v : Fin n -> R) (i j) : vandermonde v i j = v i ^ (j : 
Nat)
参数：v : Fin n -> R；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vandermonde_apply (v : Fin n → R) (i j) : vandermonde v i j = v i ^ (j : ℕ) := rfl

@[simp]
/-
**Matrix.vandermonde_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vandermonde_cons (v0 : R) (v : Fin n -> R) : vandermonde (Fin.cons v0 v : 
Fin n.succ -> R) = Fin.cons (fun (j : Fin n.succ) => v0 ^ (j : Nat)) fun i => Fi
n.cons 1 fun j => v i * vandermonde v i j
参数：v0 : R；v : Fin n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem vandermonde_cons (v0 : R) (v : Fin n → R) :
    vandermonde (Fin.cons v0 v : Fin n.succ → R) =
      Fin.cons (fun (j : Fin n.succ) => v0 ^ (j : ℕ)) fun i => Fin.cons 1
      fun j => v i * vandermonde v i j := by
  ext i j
  refine Fin.cases (by simp) (fun i => ?_) i
  refine Fin.cases (by simp) (fun j => ?_) j
  simp [pow_succ']
/-
**Matrix.vandermonde_succ** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vandermonde_succ (v : Fin n.succ -> R) : vandermonde v = .of Fin.cons (fun
 (j : Fin n.succ) => v 0 ^ (j : Nat)) fun i => Fin.cons 1 fun j => v i.succ * va
ndermonde (Fin.tail v) i j
参数：v : Fin n.succ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
· 使用定理 `Matrix.vandermonde_cons`：vandermonde_cons (v0 : R) (v : Fin n -> R) : va
ndermonde (Fin.cons v0 v : Fin n.succ -> R) = Fin.cons (fun (j : Fin n.succ) => 
v0 ^ (j : Nat…
-/
theorem vandermonde_succ (v : Fin n.succ → R) :
    vandermonde v = .of
      Fin.cons (fun (j : Fin n.succ) => v 0 ^ (j : ℕ)) fun i =>
        Fin.cons 1 fun j => v i.succ * vandermonde (Fin.tail v) i j := by
  conv_lhs => rw [← Fin.cons_self_tail v, vandermonde_cons]
  rfl
/-
**Matrix.vandermonde_mul_vandermonde_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：vandermonde_mul_vandermonde_transpose (v w : Fin n -> R) (i j) : (vandermo
nde v * (vandermonde w)ᵀ) i j = ∑ k : Fin n, (v i * w j) ^ (k : Nat)
参数：v w : Fin n -> R；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vandermonde_mul_vandermonde_transpose (v w : Fin n → R) (i j) :
    (vandermonde v * (vandermonde w)ᵀ) i j = ∑ k : Fin n, (v i * w j) ^ (k : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_pow]
/-
**Matrix.vandermonde_transpose_mul_vandermonde** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
`。
形式化陈述：vandermonde_transpose_mul_vandermonde (v : Fin n -> R) (i j) : ((vandermon
de v)ᵀ * vandermonde v) i j = ∑ k : Fin n, v k ^ (i + j : Nat)
参数：v : Fin n -> R；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vandermonde_transpose_mul_vandermonde (v : Fin n → R) (i j) :
    ((vandermonde v)ᵀ * vandermonde v) i j = ∑ k : Fin n, v k ^ (i + j : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_add]
/-
**Matrix.rectVandermonde_apply_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：rectVandermonde_apply_zero_right {α : Type*} {v w : α -> R} {i : α} (hw : 
w i = 0) : rectVandermonde v w (n + 1) i = Pi.single (Fin.last n) ((v i) ^ n)
参数：hw : w i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.rev_last`：∀ (n : ℕ), (Fin.last n).rev = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.rectVandermonde_apply`：rectVandermonde_apply {α : Type*} {v w : α
 -> R} {i : α} {j : Fin n} : rectVandermonde v w n i j = (v i) ^ j.1 * (w i) ^ j
.rev.1
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem rectVandermonde_apply_zero_right {α : Type*} {v w : α → R} {i : α} (hw : w i = 0) :
    rectVandermonde v w (n + 1) i = Pi.single (Fin.last n) ((v i) ^ n) := by
  ext j
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [rectVandermonde_apply]
  rw [rectVandermonde_apply, Pi.single_eq_of_ne hlt.ne, hw, zero_pow, mul_zero]
  simpa [Nat.sub_eq_zero_iff_le] using! hlt
/-
**Matrix.projVandermonde_apply_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：projVandermonde_apply_of_ne_zero {v w : Fin (n + 1) -> K} {i j : Fin (n + 
1)} (hw : w i != 0) : projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ n / (w i) 
^ j.1
参数：n + 1；n + 1；hw : w i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.projVandermonde_apply`：projVandermonde_apply {v w : Fin n -> R} {
i j : Fin n} : projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ j.rev.1
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `Fin.rev_add_cast`：rev_add_cast (j : Fin (n + 1)) : j.rev.1 + j.1 = n
-/
theorem projVandermonde_apply_of_ne_zero
    {v w : Fin (n + 1) → K} {i j : Fin (n + 1)} (hw : w i ≠ 0) :
    projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ n / (w i) ^ j.1 := by
  rw [projVandermonde_apply, eq_div_iff (by simp [hw]), mul_assoc, ← pow_add, rev_add_cast]
/-
**Matrix.projVandermonde_apply_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：projVandermonde_apply_zero_right {v w : Fin (n + 1) -> R} {i : Fin (n + 1)
} (hw : w i = 0) : projVandermonde v w i = Pi.single (Fin.last n) ((v i) ^ n)
参数：n + 1；n + 1；hw : w i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.rev_last`：∀ (n : ℕ), (Fin.last n).rev = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.projVandermonde_apply`：projVandermonde_apply {v w : Fin n -> R} {
i j : Fin n} : projVandermonde v w i j = (v i) ^ j.1 * (w i) ^ j.rev.1
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem projVandermonde_apply_zero_right {v w : Fin (n + 1) → R} {i : Fin (n + 1)} (hw : w i = 0) :
    projVandermonde v w i = Pi.single (Fin.last n) ((v i) ^ n) := by
  ext j
  obtain rfl | hlt := j.le_last.eq_or_lt
  · simp [projVandermonde_apply]
  rw [projVandermonde_apply, Pi.single_eq_of_ne hlt.ne, hw, zero_pow, mul_zero]
  simpa [Nat.sub_eq_zero_iff_le] using! hlt
/-
**Matrix.projVandermonde_comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：projVandermonde_comp {v w : Fin n -> R} (f : Fin n -> Fin n) : projVanderm
onde (v ∘ f) (w ∘ f) = (projVandermonde v w).submatrix f id
参数：f : Fin n -> Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem projVandermonde_comp {v w : Fin n → R} (f : Fin n → Fin n) :
    projVandermonde (v ∘ f) (w ∘ f) = (projVandermonde v w).submatrix f id := rfl
/-
**Matrix.projVandermonde_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：projVandermonde_map {R' : Type*} [CommRing R'] (φ : R ->+* R') (v w : Fin 
n -> R) : projVandermonde (fun i => φ (v i)) (fun i => φ (w i)) = φ.mapMatrix (p
rojVandermonde v w)
参数：φ : R ->+* R'；v w : Fin n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projVandermonde_map {R' : Type*} [CommRing R'] (φ : R →+* R') (v w : Fin n → R) :
    projVandermonde (fun i ↦ φ (v i)) (fun i ↦ φ (w i)) = φ.mapMatrix (projVandermonde v w) := by
  ext i j
  simp [projVandermonde_apply]
/-
**Matrix.det_projVandermonde_of_field** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem det_projVandermonde_of_field (v w : Fin n → K) :
    (projVandermonde v w).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j * w i - v i * w j) := by
  induction n with
  | zero => simp
  | succ n ih =>
  /- We can assume not all `w i` are zero, and therefore that `w 0 ≠ 0`,
  since otherwise we can swap row `0` with another nonzero row. -/
  wlog h0 : w 0 ≠ 0 generalizing v w with aux
  · obtain h0' | ⟨i₀, hi₀ : w i₀ ≠ 0⟩ := forall_or_exists_not (w · = 0)
    · obtain rfl | hne := eq_or_ne n 0
      · simp [projVandermonde_apply]
      rw [det_eq_zero_of_column_eq_zero 0 (fun i ↦ by simpa [projVandermonde_apply, h0']),
        Finset.prod_sigma', Finset.prod_eq_zero (i := ⟨0, Fin.last n⟩) (by simpa) (by simp [h0'])]
    rw [← mul_right_inj' (a := ((Equiv.swap 0 i₀).sign : K))
      (by simp [show 0 ≠ i₀ by rintro rfl; contradiction]), ← det_permute, ← projVandermonde_comp,
      aux _ _ (by simpa), ← (Equiv.swap 0 i₀).prod_Ioi_comp_eq_sign_mul_prod (by simp)]
    rfl
  /- Let `W` be obtained from the matrix by subtracting `r = (v 0) / (w 0)` times each column
  from the next column, starting from the penultimate column. This doesn't change the determinant.-/
  set r := v 0 / w 0 with hr
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) K := .of fun i ↦ (cons (projVandermonde v w i 0)
    (fun j ↦ projVandermonde v w i j.succ - r * projVandermonde v w i j.castSucc))
  -- deleting the first row and column of `W` gives a row-scaling of a Vandermonde matrix.
  have hW_eq : (W.submatrix succ succ) = .of fun i j ↦ (v (succ i) - r * w (succ i)) *
      projVandermonde (v ∘ succ) (w ∘ succ) i j := by
    ext i j
    simp only [projVandermonde_apply, val_zero, rev_zero, val_last, val_succ,
      val_castSucc, submatrix_apply, Function.comp_apply, rev_succ,
      W, r, rev_castSucc]
    simp
    ring
  /- The first row of `W` is `[(w 0)^n, 0, ..., 0]` - take a cofactor expansion along this row,
  and apply induction. -/
  rw [det_eq_of_forall_col_eq_smul_add_pred (B := W) (c := fun _ ↦ r) (by simp [W])
    (fun i j ↦ by simp [W, r, projVandermonde_apply]), det_succ_row_zero,
    Finset.sum_eq_single 0 _ (by simp)]
  · rw [succAbove_zero, hW_eq, det_mul_column, ih]
    simp only [Nat.succ_eq_add_one, coe_ofNat_eq_mod, Nat.zero_mod,
      pow_zero, show W 0 0 = w 0 ^ n by simp [W, projVandermonde_apply], one_mul, hr]
    field_simp
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin, Function.comp_apply]
    field_simp
    simp only [prod_univ_succ, Ioi_zero_eq_map, Finset.prod_map, coe_succEmb, prod_Ioi_succ]
  intro j _ hj0
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero hj0
  rw [mul_eq_zero, mul_eq_zero]
  refine .inl (.inr ?_)
  simp only [of_apply, projVandermonde_apply_of_ne_zero h0, val_succ, val_castSucc, cons_succ, W, r]
  ring

/-- The formula for the determinant of a projective Vandermonde matrix. -/
/-
**Matrix.det_projVandermonde** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_projVandermonde (v w : Fin n -> R) : (projVandermonde v w).det = ∏ i :
 Fin n, ∏ j in Finset.Ioi i, (v j * w i - v i * w j)
参数：v w : Fin n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} {σ : Type u_1} [i
nst : CommSemiring R] [IsCancelAdd R] [IsDomain R], IsDomain (MvPolynomial σ R)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `_private.Mathlib.LinearAlgebra.Vandermonde.0.Matrix.det_projVandermonde_
of_field`：∀ {K : Type u_2} [inst : Field K] {n : ℕ} (v w : Fin n → K),   (Matrix
.projVandermonde v w).det = ∏ i, ∏ j > i, (v j * w i - v i * w j)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.eval₂_mul`：eval₂_mul : forall {p}, (p * q).eval₂ f g = p.ev
al₂ f g * q.eval₂ f g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.eval₂_pow`：∀ {R : Type u} {S₁ : Type v} {σ : Type u_1} [ins
t : CommSemiring R] [inst_1 : CommSemiring S₁] (f : R →+* S₁)   (g : σ → S₁) {p 
: MvPolynomi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.eval₂_X`：eval₂_X (n) : (X n).eval₂ f g = g n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.eval₂_sub`：eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.
eval₂ f g
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The formula for the determinant of a projective Vandermonde matrix.
-/
theorem det_projVandermonde (v w : Fin n → R) : (projVandermonde v w).det =
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j * w i - v i * w j) := by
  let u (b : Bool) (i : Fin n) := (algebraMap (MvPolynomial (Fin n × Bool) ℤ)
    (FractionRing (MvPolynomial (Fin n × Bool) ℤ))) (MvPolynomial.X ⟨i, b⟩)
  have hdet := det_projVandermonde_of_field (u true) (u false)
  simp only [u] at hdet
  norm_cast at hdet
  rw [projVandermonde_map, ← RingHom.map_det, IsFractionRing.coe_inj] at hdet
  apply_fun MvPolynomial.eval₂Hom (Int.castRingHom R) (fun x ↦ (if x.2 then v else w) x.1) at hdet
  rw [RingHom.map_det] at hdet
  convert! hdet <;>
  simp [← Matrix.ext_iff, projVandermonde_apply]

/-- The formula for the determinant of a Vandermonde matrix. -/
/-
**Matrix.det_vandermonde** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_vandermonde (v : Fin n -> R) : det (vandermonde v) = ∏ i : Fin n, ∏ j 
in Ioi i, (v j - v i)
参数：v : Fin n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用引理 `Matrix.vandermonde_eq_projVandermonde`：vandermonde_eq_projVandermonde (v
 : Fin n -> R) : vandermonde v = projVandermonde v 1
· 使用定理 `Matrix.det_projVandermonde`：det_projVandermonde (v w : Fin n -> R) : (pr
ojVandermonde v w).det = ∏ i : Fin n, ∏ j in Finset.Ioi i, (v j * w i - v i * w 
j)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The formula for the determinant of a Vandermonde matrix.
-/
theorem det_vandermonde (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i) := by
  simp [vandermonde_eq_projVandermonde, det_projVandermonde]
/-
**Matrix.det_vandermonde_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_vandermonde_eq_zero_iff [IsDomain R] {v : Fin n -> R} : det (vandermon
de v) = 0 ↔ exists i j : Fin n, v i = v j ∧ i != j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_vandermonde`：det_vandermonde (v : Fin n -> R) : det (vandermo
nde v) = ∏ i : Fin n, ∏ j in Ioi i, (v j - v i)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ioi`：mem_Ioi : x in Ioi a ↔ a < x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.det_zero_of_row_eq`：det_zero_of_row_eq (i_ne_j : i != j) (hij : M
 i = M j) : M.det = 0
· 使用定理 `Matrix.vandermonde_apply`：vandermonde_apply (v : Fin n -> R) (i j) : van
dermonde v i j = v i ^ (j : Nat)
-/
theorem det_vandermonde_eq_zero_iff [IsDomain R] {v : Fin n → R} :
    det (vandermonde v) = 0 ↔ ∃ i j : Fin n, v i = v j ∧ i ≠ j := by
  constructor
  · simp only [det_vandermonde v, Finset.prod_eq_zero_iff, sub_eq_zero, forall_exists_index]
    rintro i ⟨_, j, h₁, h₂⟩
    exact ⟨j, i, h₂, (mem_Ioi.mp h₁).ne'⟩
  · simp only [Ne, forall_exists_index, and_imp]
    refine fun i j h₁ h₂ => Matrix.det_zero_of_row_eq h₂ (funext fun k => ?_)
    rw [vandermonde_apply, vandermonde_apply, h₁]
/-
**Matrix.det_vandermonde_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_vandermonde_ne_zero_iff [IsDomain R] {v : Fin n -> R} : det (vandermon
de v) != 0 ↔ Function.Injective v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem det_vandermonde_ne_zero_iff [IsDomain R] {v : Fin n → R} :
    det (vandermonde v) ≠ 0 ↔ Function.Injective v := by
  unfold Function.Injective
  simp only [det_vandermonde_eq_zero_iff, Ne, not_exists, not_and, Classical.not_not]

@[simp]
/-
**Matrix.det_vandermonde_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_vandermonde_add (v : Fin n -> R) (a : R) : (Matrix.vandermonde fun i =
> v i + a).det = (Matrix.vandermonde v).det
参数：v : Fin n -> R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_vandermonde`：det_vandermonde (v : Fin n -> R) : det (vandermo
nde v) = ∏ i : Fin n, ∏ j in Ioi i, (v j - v i)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_vandermonde_add (v : Fin n → R) (a : R) :
    (Matrix.vandermonde fun i ↦ v i + a).det = (Matrix.vandermonde v).det := by
  simp [Matrix.det_vandermonde]

@[simp]
/-
**Matrix.det_vandermonde_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_vandermonde_sub (v : Fin n -> R) (a : R) : (Matrix.vandermonde fun i =
> v i - a).det = (Matrix.vandermonde v).det
参数：v : Fin n -> R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_vandermonde_add`：det_vandermonde_add (v : Fin n -> R) (a : R)
 : (Matrix.vandermonde fun i => v i + a).det = (Matrix.vandermonde v).det
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_vandermonde_sub (v : Fin n → R) (a : R) :
    (Matrix.vandermonde fun i ↦ v i - a).det = (Matrix.vandermonde v).det := by
  rw [← det_vandermonde_add v (-a)]
  simp only [← sub_eq_add_neg]
/-
**Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix`。
形式化陈述：eq_zero_of_forall_index_sum_pow_mul_eq_zero [IsDomain R] {f v : Fin n -> R
} (hf : Function.Injective f) (hfv : forall j, (∑ i : Fin n, f j ^ (i : Nat) * v
 i) = 0) : v = 0
参数：hf : Function.Injective f；hfv : forall j, (∑ i : Fin n, f j ^ (i : Nat) * v i
) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.eq_zero_of_mulVec_eq_zero`：eq_zero_of_mulVec_eq_zero [NoZeroDivis
ors R] (hM : M.det != 0) {v : m -> R} (hv : M *ᵥ v = 0) : v = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.det_vandermonde_ne_zero_iff`：det_vandermonde_ne_zero_iff [IsDomai
n R] {v : Fin n -> R} : det (vandermonde v) != 0 ↔ Function.Injective v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem eq_zero_of_forall_index_sum_pow_mul_eq_zero [IsDomain R] {f v : Fin n → R}
    (hf : Function.Injective f) (hfv : ∀ j, (∑ i : Fin n, f j ^ (i : ℕ) * v i) = 0) : v = 0 :=
  eq_zero_of_mulVec_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)
/-
**Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Matrix`。
形式化陈述：eq_zero_of_forall_index_sum_mul_pow_eq_zero [IsDomain R] {f v : Fin n -> R
} (hf : Function.Injective f) (hfv : forall j, (∑ i, v i * f j ^ (i : Nat)) = 0)
 : v = 0
参数：hf : Function.Injective f；hfv : forall j, (∑ i, v i * f j ^ (i : Nat)) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero`：eq_zero_of_forall_in
dex_sum_pow_mul_eq_zero [IsDomain R] {f v : Fin n -> R} (hf : Function.Injective
 f) (hfv : forall j, (∑ i : Fin n, f j ^…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem eq_zero_of_forall_index_sum_mul_pow_eq_zero [IsDomain R] {f v : Fin n → R}
    (hf : Function.Injective f) (hfv : ∀ j, (∑ i, v i * f j ^ (i : ℕ)) = 0) : v = 0 := by
  apply eq_zero_of_forall_index_sum_pow_mul_eq_zero hf
  simp_rw [mul_comm]
  exact hfv
/-
**Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix`。
形式化陈述：eq_zero_of_forall_pow_sum_mul_pow_eq_zero [IsDomain R] {f v : Fin n -> R} 
(hf : Function.Injective f) (hfv : forall i : Fin n, (∑ j : Fin n, v j * f j ^ (
i : Nat)) = 0) : v = 0
参数：hf : Function.Injective f；hfv : forall i : Fin n, (∑ j : Fin n, v j * f j ^ (
i : Nat)) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.eq_zero_of_vecMul_eq_zero`：eq_zero_of_vecMul_eq_zero [NoZeroDivis
ors R] (hM : M.det != 0) {v : m -> R} (hv : v ᵥ* M = 0) : v = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.det_vandermonde_ne_zero_iff`：det_vandermonde_ne_zero_iff [IsDomai
n R] {v : Fin n -> R} : det (vandermonde v) != 0 ↔ Function.Injective v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem eq_zero_of_forall_pow_sum_mul_pow_eq_zero [IsDomain R] {f v : Fin n → R}
    (hf : Function.Injective f) (hfv : ∀ i : Fin n, (∑ j : Fin n, v j * f j ^ (i : ℕ)) = 0) :
    v = 0 :=
  eq_zero_of_vecMul_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)

open Polynomial
/-
**Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials** 是 Mat
hlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials (v : Fin n
 -> R) (p : Fin n -> R[X]) (h_deg : forall i, (p i).natDegree <= i) : Matrix.of 
(fun i j => ((p j).eval (v i))) = (Matrix.vandermonde v) * (Matrix.of (fun (i j 
: Fin n) => (p j).coeff i))
参数：v : Fin n -> R；p : Fin n -> R[X]；h_deg : forall i, (p i).natDegree <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_eq_sum`：eval₂_eq_sum {f : R ->+* S} {x : S} : p.eval₂ f
 x = p.sum fun e a => f a * x ^ e
· 使用定理 `Polynomial.supp_subset_range`：supp_subset_range (h : natDegree p < m) : 
p.support subseteq Finset.range m
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Polynomial.sum_eq_of_subset`：sum_eq_of_subset {S : Type*} [AddCommMonoid
 S] {p : R[X]} (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {s : Finset Nat} (
hs : p.support su…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.sum_univ_eq_sum_range`：∀ {α : Type u_1} [inst : AddCommMonoid α] (f 
: ℕ → α) (n : ℕ), ∑ i, f ↑i = ∑ i ∈ Finset.range n, f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Matrix.of_apply`：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
-/
theorem eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials (v : Fin n → R)
    (p : Fin n → R[X]) (h_deg : ∀ i, (p i).natDegree ≤ i) :
    Matrix.of (fun i j => ((p j).eval (v i))) =
    (Matrix.vandermonde v) * (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) := by
  ext i j
  simp_rw [Matrix.mul_apply, eval, Matrix.of_apply, eval₂_eq_sum]
  simp only [Matrix.vandermonde]
  have : (p j).support ⊆ range n := supp_subset_range <| Nat.lt_of_le_of_lt (h_deg j) <| Fin.prop j
  rw [sum_eq_of_subset _ (fun j => zero_mul ((v i) ^ j)) this, ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]
/-
**Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde** 是 Mathlib 中的一个定理，位于命名
空间 `Matrix`。
形式化陈述：det_eval_matrixOfPolynomials_eq_det_vandermonde (v : Fin n -> R) (p : Fin 
n -> R[X]) (h_deg : forall i, (p i).natDegree = i) (h_monic : forall i, Monic <|
 p i) : (Matrix.vandermonde v).det = (Matrix.of (fun i j => ((p j).eval (v i))))
.det
参数：v : Fin n -> R；p : Fin n -> R[X]；h_deg : forall i, (p i).natDegree = i；h_moni
c : forall i, Monic <| p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials`：
eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials (v : Fin n -> R)
 (p : Fin n -> R[X]) (h_deg : forall i, (p i).natDegree <= i…
· 使用定理 `Nat.le_of_eq`：∀ {n m : ℕ}, n = m → n ≤ m
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `Matrix.det_matrixOfPolynomials`：det_matrixOfPolynomials {n : Nat} (p : F
in n -> R[X]) (h_deg : forall i, (p i).natDegree = i) (h_monic : forall i, Monic
 <| p i) : (Matrix.o…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem det_eval_matrixOfPolynomials_eq_det_vandermonde (v : Fin n → R) (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree = i) (h_monic : ∀ i, Monic <| p i) :
    (Matrix.vandermonde v).det = (Matrix.of (fun i j => ((p j).eval (v i)))).det := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials v p (fun i ↦
      Nat.le_of_eq (h_deg i)), Matrix.det_mul,
      Matrix.det_matrixOfPolynomials p h_deg h_monic, mul_one]
/-
**Matrix.det_vandermonde_id_eq_superFactorial** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`
。
形式化陈述：det_vandermonde_id_eq_superFactorial (n : Nat) : (vandermonde fun i : Fin 
(n + 1) => (i : R)).det = n.superFactorial
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.superFactorial.eq_2`：∀ (n : ℕ), n.succ.superFactorial = n.succ.facto
rial * n.superFactorial
· 使用定理 `Matrix.det_vandermonde`：det_vandermonde (v : Fin n -> R) : det (vandermo
nde v) = ∏ i : Fin n, ∏ j in Ioi i, (v j - v i)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.prod_univ_succAbove`：prod_univ_succAbove (f : Fin (n + 1) -> M) (x :
 Fin (n + 1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Finset.prod_natCast`：prod_natCast (s : Finset ι) (f : ι -> Nat) : ↑(∏ i 
in s, f i : Nat) = ∏ i in s, (f i : R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.Ioi_zero_eq_map`：Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (
Fin.succEmb _)
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Fin.prod_univ_eq_prod_range`：Fin.prod_univ_eq_prod_range [CommMonoid α] 
(f : Nat -> α) (n : Nat) : ∏ i : Fin n, f i = ∏ i in range n, f i
· 使用定理 `Finset.prod_range_add_one_eq_factorial`：∀ (n : ℕ), ∏ i ∈ Finset.range n,
 (i + 1) = n.factorial
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Fin.prod_Ioi_succ`：prod_Ioi_succ (f : Fin (n + 1) -> M) (a : Fin n) : ∏ 
i > a.succ, f i = ∏ i > a, f i.succ
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
-/
lemma det_vandermonde_id_eq_superFactorial (n : ℕ) :
    (vandermonde fun i : Fin (n + 1) ↦ (i : R)).det = n.superFactorial := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Nat.superFactorial, det_vandermonde, Fin.prod_univ_succAbove _ 0]
    push_cast
    congr
    · simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
      norm_cast
      simp [Fin.prod_univ_eq_prod_range (fun i ↦ (↑i + 1)) (n + 1)]
    · rw [det_vandermonde] at hn
      simp [hn]
/-
**Matrix.of_eval_descPochhammer_eq_mul_of_choose** 是 Mathlib 中的一个引理，位于命名空间 `Matr
ix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma of_eval_descPochhammer_eq_mul_of_choose {n : ℕ} (v : Fin n → ℕ) :
    (of fun i j : Fin n => (descPochhammer ℤ j).eval (v i : ℤ)).det =
    (∏ i : Fin n, Nat.factorial i) *
      (of fun i j : Fin n => (Nat.choose (v i) j : ℤ)).det := by
  convert! det_mul_row (fun (i : Fin n) => ((Nat.factorial (i : ℕ)) : ℤ)) _
  · rw [of_apply, descPochhammer_eval_eq_descFactorial ℤ _ _]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _
  · rw [Nat.cast_prod]
/-
**Matrix.superFactorial_dvd_vandermonde_det** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：superFactorial_dvd_vandermonde_det {n : Nat} (v : Fin (n + 1) -> Int) : ↑n
.superFactorial ∣ (vandermonde v).det
参数：v : Fin (n + 1) -> Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Int.toNat_sub_of_le`：∀ {a b : ℤ}, b ≤ a → ↑(a - b).toNat = a - b
· 使用定理 `Finset.inf'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α
] {s : Finset β} (f : β → α) {b : β} (h : b ∈ s),   s.inf' ⋯ f ≤ f b
· 使用定理 `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde`：det_eval_matrixO
fPolynomials_eq_det_vandermonde (v : Fin n -> R) (p : Fin n -> R[X]) (h_deg : fo
rall i, (p i).natDegree = i) (h_monic : fora…
· 使用定理 `descPochhammer_natDegree`：descPochhammer_natDegree (n : Nat) [NoZeroDivi
sors R] [Nontrivial R] : (descPochhammer R n).natDegree = n
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `monic_descPochhammer`：monic_descPochhammer (n : Nat) [Nontrivial R] [NoZ
eroDivisors R] : Monic descPochhammer R n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det_vandermonde_sub`：det_vandermonde_sub (v : Fin n -> R) (a : R)
 : (Matrix.vandermonde fun i => v i - a).det = (Matrix.vandermonde v).det
· 使用定理 `_private.Mathlib.LinearAlgebra.Vandermonde.0.Matrix.of_eval_descPochhamm
er_eq_mul_of_choose`：∀ {n : ℕ} (v : Fin n → ℕ),   (Matrix.of fun i j => Polynomi
al.eval (↑(v i)) (descPochhammer ℤ ↑j)).det =     ↑(∏ i, (↑i).factorial) * (Matr
i…
· 使用定理 `Fin.prod_univ_eq_prod_range`：Fin.prod_univ_eq_prod_range [CommMonoid α] 
(f : Nat -> α) (n : Nat) : ∏ i : Fin n, f i = ∏ i in range n, f i
· 使用定理 `Nat.prod_range_succ_factorial`：∀ (n : ℕ), ∏ x ∈ Finset.range (n + 1), x.
factorial = n.superFactorial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma superFactorial_dvd_vandermonde_det {n : ℕ} (v : Fin (n + 1) → ℤ) :
    ↑n.superFactorial ∣ (vandermonde v).det := by
  let m := inf' univ ⟨0, mem_univ _⟩ v
  let w' := fun i ↦ (v i - m).toNat
  have hw' : ∀ i, (w' i : ℤ) = v i - m := fun i ↦ Int.toNat_sub_of_le (inf'_le _ (mem_univ _))
  have h := det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i ↦ ↑(w' i))
      (fun i => descPochhammer ℤ i)
      (fun i => descPochhammer_natDegree ℤ i)
      (fun i => monic_descPochhammer ℤ i)
  conv_lhs at h => simp only [hw', det_vandermonde_sub]
  use (of (fun (i j : Fin (n + 1)) => (Nat.choose (w' i) (j : ℕ) : ℤ))).det
  simp [h, of_eval_descPochhammer_eq_mul_of_choose w', Fin.prod_univ_eq_prod_range]

end Matrix

