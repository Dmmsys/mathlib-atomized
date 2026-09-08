/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Iterate

/-!

# A division-free determinant algorithm

This file defines `birdDet`and `Spec.birdDet`, implementations of an
division-free algorithm for computing determinants. The algorithm runs in O(n^4)
for an n-by-n matrix.

This determinant algorithm comes from
[Richard S. Bird, *A simple division-free algorithm for computing determinants*][bird2011].

## Main definitions

- `BirdDet.birdDet`: The entrypoint for the determinant calculation.
- `BirdDet.get`: matrix entry lookup.
- `BirdDet.sumFrom`: The sum `f lo + ... + f (n - 1)`.
- `BirdDet.stepEntry`: One scalar recurrence step.
- `BirdDet.Spec.birdDet`: An implementation of Bird's algorithm using `Matrix`.

## Main lemmas

The lemmas in this file are unfolding equations.

-/

public section

namespace BirdDet

variable {R : Type*} [CommRing R]

/--
`get n A i j` returns the (i, j)th entry of the `n × n` matrix whose entries are
stored in `A` in row-major order.

The function does not check the matrix index bounds.
-/
/-
**BirdDet.get** 是 Mathlib 中的一个定义，位于命名空间 `BirdDet`。
形式化陈述：{R : Type u_1} → [CommRing R] → ℕ → Array R → ℕ → ℕ → R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`get n A i j` returns the (i, j)th entry of the `n × n` matrix whose entries are
stored in `A` in row-major order.

The function does not check the matrix index bounds.
-/
protected def get (n : ℕ) (A : Array R) (i j : ℕ) : R :=
  A.getD (n * i + j) 0

/-- Sum `f lo + ... + f (n - 1)`. Returns zero when `n <= lo`. -/
/-
**BirdDet.sumFrom** 是 Mathlib 中的一个定义，位于命名空间 `BirdDet`。
形式化陈述：{R : Type u_1} → [CommRing R] → ℕ → ℕ → (ℕ → R) → R
参数：ℕ → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sum `f lo + ... + f (n - 1)`. Returns zero when `n <= lo`.
-/
protected def sumFrom (n lo : ℕ) (f : ℕ → R) : R :=
  if lo < n then f lo + BirdDet.sumFrom n (lo + 1) f else 0

/--
One entry of one scalar Bird recurrence step.

Bird's paper defines a matrix recursion for an `n × n` matrix `A`:

```
F_0 = A
F_{t+1} = μ(F_t) * A
```

where `μ(F_t)` is obtained from `F_t` by replacing each diagonal entry
`F_t k k` with the negative sum of the diagonal entries below it, setting the
entries in the lower triangular part to 0, and leaving all other entries
unchanged:

```
μ(F_t) =
  0                                   if i >= j
  - ∑ k from i+1 to n-1, F_t k k      if i = j
  F_t i j                             if i < j
```

If we write out the entry-wise matrix multiplication `F_{t+1} i j = (μ(F_t) * A) i j`
we obtain:

```
F_{t+1} i j =
  - (∑ k from i+1 to n-1, F_t k k) * (A i j)
  + ∑ k from i+1 to n-1, (F_t i k) * (A k j)
```
-/
/-
**BirdDet.stepEntry** 是 Mathlib 中的一个定义，位于命名空间 `BirdDet`。
形式化陈述：stepEntry (n : Nat) (A : Array R) (F : Nat -> Nat -> R) (i j : Nat) : R
参数：n : Nat；A : Array R；F : Nat -> Nat -> R；i j : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One entry of one scalar Bird recurrence step.

Bird's paper defines a matrix recursion for an `n × n` matrix `A`:

```
F_0 = A
F_{t+1} = μ(F_t) * A
```

where `μ(F_t)` is obtained from `F_t` by replacing each diagonal entry
`F_t k k` with the negative sum of the diagonal entries below it, setting the
entries in the lower triangular part to 0, and leaving all other entries
unchanged:

```
μ(F_t) =
  0                                   if i >= j
  - ∑ k from i+1 to n-1, F_t k k      if i = j
  F_t i j                             if i < j
```

If we write out the entry-wise matrix multiplication `F_{t+1} i j = (μ(F_t) * A)
 i j`
we obtain:

```
F_{t+1} i j =
  - (∑ k from i+1 to n-1, F_t k k) * (A i j)
  + ∑ k from i+1 to n-1, (F_t i k) * (A k j)
```
-/
def stepEntry (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) : R :=
  -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j +
    BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j

/--
`birdDet n A` computes the determinant of the `n × n` matrix whose entries are
stored in `A` in row-major order.
-/
/-
**BirdDet.birdDet** 是 Mathlib 中的一个定义，位于命名空间 `BirdDet`。
形式化陈述：birdDet (n : Nat) (A : Array R) : R
参数：n : Nat；A : Array R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`birdDet n A` computes the determinant of the `n × n` matrix whose entries are
stored in `A` in row-major order.
-/
def birdDet (n : ℕ) (A : Array R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0

/- Unfolding lemmas -/

/-- Unfold a row-major matrix entry lookup. -/
/-
**BirdDet.get_eq** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：get_eq (n : Nat) (A : Array R) (i j : Nat) : BirdDet.get n A i j = A.getD 
(n * i + j) 0
参数：n : Nat；A : Array R；i j : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfold a row-major matrix entry lookup.
-/
theorem get_eq (n : ℕ) (A : Array R) (i j : ℕ) :
    BirdDet.get n A i j = A.getD (n * i + j) 0 := by
  rfl
/-
**BirdDet.sumFrom_step** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：sumFrom_step (n lo : Nat) (f : Nat -> R) (h : lo < n) : BirdDet.sumFrom n 
lo f = f lo + BirdDet.sumFrom n (lo + 1) f
参数：n lo : Nat；f : Nat -> R；h : lo < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs.0.BirdDet.su
mFrom.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (n lo : ℕ) (f : ℕ → R),   BirdD
et.sumFrom n lo f = if lo < n then f lo + BirdDet.sumFrom n (lo + 1) f e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumFrom_step (n lo : ℕ) (f : ℕ → R) (h : lo < n) :
    BirdDet.sumFrom n lo f = f lo + BirdDet.sumFrom n (lo + 1) f := by
  rw [BirdDet.sumFrom]
  simp [h]
/-
**BirdDet.sumFrom_stop** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：sumFrom_stop (n lo : Nat) (f : Nat -> R) (h : ¬ lo < n) : BirdDet.sumFrom 
n lo f = 0
参数：n lo : Nat；f : Nat -> R；h : ¬ lo < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs.0.BirdDet.su
mFrom.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (n lo : ℕ) (f : ℕ → R),   BirdD
et.sumFrom n lo f = if lo < n then f lo + BirdDet.sumFrom n (lo + 1) f e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumFrom_stop (n lo : ℕ) (f : ℕ → R) (h : ¬ lo < n) :
    BirdDet.sumFrom n lo f = 0 := by
  rw [BirdDet.sumFrom]
  simp [h]

/-- Induction following the recursive structure of `sumFrom`. -/
@[elab_as_elim]
/-
**BirdDet.sumFrom_induct** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：sumFrom_induct (n : Nat) (motive : Nat -> Prop) (step : forall lo, lo < n 
-> motive (lo + 1) -> motive lo) (stop : forall lo, ¬lo < n -> motive lo) (lo : 
Nat) : motive lo
参数：n : Nat；motive : Nat -> Prop；step : forall lo, lo < n -> motive (lo + 1) -> m
otive lo；stop : forall lo, ¬lo < n -> motive lo；lo : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BirdDet.sumFrom.induct`：∀ (n : ℕ) (motive : ℕ → Prop),   (∀ x < n, motiv
e (x + 1) → motive x) → (∀ (x : ℕ), ¬x < n → motive x) → ∀ (lo : ℕ), motive lo

--- 原说明 ---
Induction following the recursive structure of `sumFrom`.
-/
theorem sumFrom_induct (n : ℕ) (motive : ℕ → Prop)
    (step : ∀ lo, lo < n → motive (lo + 1) → motive lo)
    (stop : ∀ lo, ¬lo < n → motive lo) (lo : ℕ) : motive lo :=
  BirdDet.sumFrom.induct n motive step stop lo

/-- Unfold one scalar Bird recurrence step to the entry-wise formula. -/
/-
**BirdDet.stepEntry_eq** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：stepEntry_eq (n : Nat) (A : Array R) (F : Nat -> Nat -> R) (i j : Nat) : s
tepEntry n A F i j = -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n
 A i j + BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j
参数：n : Nat；A : Array R；F : Nat -> Nat -> R；i j : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfold one scalar Bird recurrence step to the entry-wise formula.
-/
theorem stepEntry_eq (n : ℕ) (A : Array R) (F : ℕ → ℕ → R) (i j : ℕ) :
    stepEntry n A F i j =
      -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j
        + BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j := by
  rfl
/-
**BirdDet.birdDet_zero** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：birdDet_zero (A : Array R) : birdDet 0 A = 1
参数：A : Array R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem birdDet_zero (A : Array R) : birdDet 0 A = 1 := by
  rfl

/-- Unfold `birdDet` at a successor dimension. -/
/-
**BirdDet.birdDet_succ** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：birdDet_succ (k : Nat) (A : Array R) : birdDet (k + 1) A = (-1 : R) ^ k * 
(stepEntry (k + 1) A)^[k] (BirdDet.get (k + 1) A) 0 0
参数：k : Nat；A : Array R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs.0.BirdDet.bi
rdDet.eq_2`：∀ {R : Type u_1} [inst : CommRing R] (A : Array R) (k : ℕ),   BirdDe
t.birdDet k.succ A = (-1) ^ k * (BirdDet.stepEntry k.succ A)^[k] (BirdDe…

--- 原说明 ---
Unfold `birdDet` at a successor dimension.
-/
theorem birdDet_succ (k : ℕ) (A : Array R) :
    birdDet (k + 1) A =
      (-1 : R) ^ k * (stepEntry (k + 1) A)^[k] (BirdDet.get (k + 1) A) 0 0 :=
  by rw [birdDet]
/-
**BirdDet.birdDet_eq** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet`。
形式化陈述：birdDet_eq (n k : Nat) (A : Array R) (hn : n = k + 1) : birdDet n A = (-1 
: R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0
参数：n k : Nat；A : Array R；hn : n = k + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BirdDet.birdDet_succ`：birdDet_succ (k : Nat) (A : Array R) : birdDet (k 
+ 1) A = (-1 : R) ^ k * (stepEntry (k + 1) A)^[k] (BirdDet.get (k + 1) A) 0 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem birdDet_eq (n k : ℕ) (A : Array R) (hn : n = k + 1) :
    birdDet n A = (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0 := by
  subst hn
  exact birdDet_succ k A

namespace Spec

open scoped BigOperators

/-- One entry of one Matrix/Fin Bird recurrence step. -/
/-
**BirdDet.Spec.stepEntry** 是 Mathlib 中的一个定义，位于命名空间 `BirdDet.Spec`。
形式化陈述：stepEntry {n : Nat} (A F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin
 n) R
参数：A F : Matrix (Fin n) (Fin n) R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One entry of one Matrix/Fin Bird recurrence step.
-/
def stepEntry {n : ℕ} (A F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j ↦ (-∑ k ∈ Finset.Ioi i, F k k) * A i j +
    ∑ k ∈ Finset.Ioi i, F i k * A k j

/-- A version of the Bird determinant algorithm that is stated in terms of `Matrix`. -/
/-
**BirdDet.Spec.birdDet** 是 Mathlib 中的一个定义，位于命名空间 `BirdDet.Spec`。
形式化陈述：birdDet {n : Nat} (A : Matrix (Fin n) (Fin n) R) : R
参数：A : Matrix (Fin n) (Fin n) R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of the Bird determinant algorithm that is stated in terms of `Matrix`.
-/
def birdDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry A)^[k] A 0 0
/-
**BirdDet.Spec.stepEntry_eq** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet.Spec`。
形式化陈述：stepEntry_eq {n : Nat} (A F : Matrix (Fin n) (Fin n) R) : stepEntry A F = 
.of fun i j => (-∑ k in Finset.Ioi i, F k k) * A i j + ∑ k in Finset.Ioi i, F i 
k * A k j
参数：A F : Matrix (Fin n) (Fin n) R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stepEntry_eq {n : ℕ} (A F : Matrix (Fin n) (Fin n) R) :
    stepEntry A F =
      .of fun i j ↦ (-∑ k ∈ Finset.Ioi i, F k k) * A i j
        + ∑ k ∈ Finset.Ioi i, F i k * A k j := by
  rfl
/-
**BirdDet.Spec.birdDetSpec_zero** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet.Spec`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (A : Matrix (Fin 0) (Fin 0) R), BirdD
et.Spec.birdDet A = 1
参数：A : Matrix (Fin 0) (Fin 0) R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem birdDetSpec_zero (A : Matrix (Fin 0) (Fin 0) R) :
    birdDet A = 1 := by
  rfl
/-
**BirdDet.Spec.birdDetSpec_succ** 是 Mathlib 中的一个定理，位于命名空间 `BirdDet.Spec`。
形式化陈述：birdDetSpec_succ {k : Nat} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) : bi
rdDet A = (-1 : R) ^ k * (stepEntry A)^[k] A 0 0
参数：A : Matrix (Fin (k + 1)) (Fin (k + 1)) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs.0.BirdDet.Sp
ec.birdDet.eq_2`：∀ {R : Type u_1} [inst : CommRing R] (k : ℕ) (A_2 : Matrix (Fin
 (k + 1)) (Fin (k + 1)) R),   BirdDet.Spec.birdDet A_2 = (-1) ^ k * (BirdDet.…
-/
theorem birdDetSpec_succ {k : ℕ} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    birdDet A = (-1 : R) ^ k * (stepEntry A)^[k] A 0 0 := by
  rw [birdDet]

end Spec

end BirdDet

end

