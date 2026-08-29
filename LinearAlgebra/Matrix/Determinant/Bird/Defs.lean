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
Definition of `get` / `get` 的定义

English:
definition get
  signature: (n : Nat) (A : Array R) (i j : Nat)
  body: A.getD (n * i + j) 0

中文:
定义 get
  签名: (n : 自然数) (A : Array R) (i j : 自然数)
  定义体: A.getD (n * i + j) 0
-/
protected def get (n : Nat) (A : Array R) (i j : Nat) : R :=
  A.getD (n * i + j) 0

/--
Definition of `sumFrom` / `sumFrom` 的定义

English:
definition sumFrom
  signature: (n lo : Nat) (f : Nat -> R)
  body: if lo < n then f lo + BirdDet.sumFrom n (lo + 1) f else 0

中文:
定义 sumFrom
  签名: (n lo : 自然数) (f : 自然数 -> R)
  定义体: if lo < n then f lo + BirdDet.sumFrom n (lo + 1) f else 0
-/
protected def sumFrom (n lo : Nat) (f : Nat -> R) : R :=
  if lo < n then f lo + BirdDet.sumFrom n (lo + 1) f else 0

/--
Definition of `stepEntry` / `stepEntry` 的定义

English:
definition stepEntry
  signature: (n : Nat) (A : Array R) (F : Nat -> Nat -> R) (i j : Nat)
  body: -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j +
    BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j

中文:
定义 stepEntry
  签名: (n : 自然数) (A : Array R) (F : 自然数 -> 自然数 -> R) (i j : 自然数)
  定义体: -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j +
    BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j

Depends on / 依赖: BirdDet, BirdDet.get, BirdDet.sumFrom, sumFrom
-/
def stepEntry (n : Nat) (A : Array R) (F : Nat -> Nat -> R) (i j : Nat) : R :=
  -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j +
    BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j

/--
Definition of `birdDet` / `birdDet` 的定义

English:
definition birdDet
  signature: (n : Nat) (A : Array R)
  body: match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0

中文:
定义 birdDet
  签名: (n : 自然数) (A : Array R)
  定义体: match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0

Depends on / 依赖: BirdDet, BirdDet.get, stepEntry
-/
def birdDet (n : Nat) (A : Array R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0

/- Unfolding lemmas -/

/--
theorem `get_eq` / 定理 `get_eq`

English:
theorem get_eq
  given: (n : Nat) (A : Array R) (i j : Nat)
  proof: by
  rfl

中文:
定理 get_eq
  条件: (n : 自然数) (A : Array R) (i j : 自然数)
  证明: by
  rfl
-/
theorem get_eq (n : Nat) (A : Array R) (i j : Nat) :
    BirdDet.get n A i j = A.getD (n * i + j) 0 := by
  rfl

/--
theorem `sumFrom_step` / 定理 `sumFrom_step`

English:
theorem sumFrom_step
  given: (n lo : Nat) (f : Nat -> R) (h : lo < n)
  proof: by
  rw [BirdDet.sumFrom]
  simp [h]

中文:
定理 sumFrom_step
  条件: (n lo : 自然数) (f : 自然数 -> R) (h : lo < n)
  证明: by
  rw [BirdDet.sumFrom]
  simp [h]

Depends on / 依赖: BirdDet, BirdDet.sumFrom, sumFrom
-/
theorem sumFrom_step (n lo : Nat) (f : Nat -> R) (h : lo < n) :
    BirdDet.sumFrom n lo f = f lo + BirdDet.sumFrom n (lo + 1) f := by
  rw [BirdDet.sumFrom]
  simp [h]

/--
theorem `sumFrom_stop` / 定理 `sumFrom_stop`

English:
theorem sumFrom_stop
  given: (n lo : Nat) (f : Nat -> R) (h : ¬ lo < n)
  proof: by
  rw [BirdDet.sumFrom]
  simp [h]

中文:
定理 sumFrom_stop
  条件: (n lo : 自然数) (f : 自然数 -> R) (h : ¬ lo < n)
  证明: by
  rw [BirdDet.sumFrom]
  simp [h]

Depends on / 依赖: BirdDet, BirdDet.sumFrom, sumFrom
-/
theorem sumFrom_stop (n lo : Nat) (f : Nat -> R) (h : ¬ lo < n) :
    BirdDet.sumFrom n lo f = 0 := by
  rw [BirdDet.sumFrom]
  simp [h]

/-- Induction following the recursive structure of `sumFrom`. -/
@[elab_as_elim]
/--
theorem `sumFrom_induct` / 定理 `sumFrom_induct`

English:
theorem sumFrom_induct
  statement: (n : Nat) (motive : Nat -> Prop)
  proof: BirdDet.sumFrom.induct n motive step stop lo

中文:
定理 sumFrom_induct
  结论: (n : 自然数) (motive : 自然数 -> 命题)
  证明: BirdDet.sumFrom.induct n motive step stop lo

Depends on / 依赖: BirdDet, BirdDet.sumFrom.induct, induct, motive, sumFrom
-/
theorem sumFrom_induct (n : Nat) (motive : Nat -> Prop)
    (step : forall lo, lo < n -> motive (lo + 1) -> motive lo)
    (stop : forall lo, ¬lo < n -> motive lo) (lo : Nat) : motive lo :=
  BirdDet.sumFrom.induct n motive step stop lo

/--
theorem `stepEntry_eq` / 定理 `stepEntry_eq`

English:
theorem stepEntry_eq
  given: (n : Nat) (A : Array R) (F : Nat -> Nat -> R) (i j : Nat)
  proof: by
  rfl

中文:
定理 stepEntry_eq
  条件: (n : 自然数) (A : Array R) (F : 自然数 -> 自然数 -> R) (i j : 自然数)
  证明: by
  rfl
-/
theorem stepEntry_eq (n : Nat) (A : Array R) (F : Nat -> Nat -> R) (i j : Nat) :
    stepEntry n A F i j =
      -(BirdDet.sumFrom n (i + 1) fun k => F k k) * BirdDet.get n A i j
        + BirdDet.sumFrom n (i + 1) fun k => F i k * BirdDet.get n A k j := by
  rfl

/--
theorem `birdDet_zero` / 定理 `birdDet_zero`

English:
theorem birdDet_zero
  given: (A : Array R)
  statement: birdDet 0 A = 1
  proof: by
  rfl

中文:
定理 birdDet_zero
  条件: (A : Array R)
  结论: birdDet 0 A = 1
  证明: by
  rfl
-/
theorem birdDet_zero (A : Array R) : birdDet 0 A = 1 := by
  rfl

/--
theorem `birdDet_succ` / 定理 `birdDet_succ`

English:
theorem birdDet_succ
  given: (k : Nat) (A : Array R)
  proof: by rw [birdDet]

中文:
定理 birdDet_succ
  条件: (k : 自然数) (A : Array R)
  证明: by rw [birdDet]

Depends on / 依赖: birdDet
-/
theorem birdDet_succ (k : Nat) (A : Array R) :
    birdDet (k + 1) A =
      (-1 : R) ^ k * (stepEntry (k + 1) A)^[k] (BirdDet.get (k + 1) A) 0 0 :=
  by rw [birdDet]

/--
theorem `birdDet_eq` / 定理 `birdDet_eq`

English:
theorem birdDet_eq
  given: (n k : Nat) (A : Array R) (hn : n = k + 1)
  proof: by
  subst hn
  exact birdDet_succ k A

中文:
定理 birdDet_eq
  条件: (n k : 自然数) (A : Array R) (hn : n = k + 1)
  证明: by
  subst hn
  exact birdDet_succ k A

Depends on / 依赖: birdDet_succ
-/
theorem birdDet_eq (n k : Nat) (A : Array R) (hn : n = k + 1) :
    birdDet n A = (-1 : R) ^ k * (stepEntry n A)^[k] (BirdDet.get n A) 0 0 := by
  subst hn
  exact birdDet_succ k A

namespace Spec

open scoped BigOperators

/--
Definition of `stepEntry` / `stepEntry` 的定义

English:
definition stepEntry
  signature: {n : Nat} (A F : Matrix (Fin n) (Fin n) R)
  body: .of fun i j => (-∑ k in Finset.Ioi i, F k k) * A i j +
    ∑ k in Finset.Ioi i, F i k * A k j

中文:
定义 stepEntry
  签名: {n : 自然数} (A F : Matrix (Fin n) (Fin n) R)
  定义体: .of fun i j => (-∑ k in Finset.Ioi i, F k k) * A i j +
    ∑ k in Finset.Ioi i, F i k * A k j

Depends on / 依赖: Finset, Finset.Ioi
-/
def stepEntry {n : Nat} (A F : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  .of fun i j => (-∑ k in Finset.Ioi i, F k k) * A i j +
    ∑ k in Finset.Ioi i, F i k * A k j

/--
Definition of `birdDet` / `birdDet` 的定义

English:
definition birdDet
  signature: {n : Nat} (A : Matrix (Fin n) (Fin n) R)
  body: match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry A)^[k] A 0 0

中文:
定义 birdDet
  签名: {n : 自然数} (A : Matrix (Fin n) (Fin n) R)
  定义体: match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry A)^[k] A 0 0

Depends on / 依赖: stepEntry
-/
def birdDet {n : Nat} (A : Matrix (Fin n) (Fin n) R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * (stepEntry A)^[k] A 0 0

/--
theorem `stepEntry_eq` / 定理 `stepEntry_eq`

English:
theorem stepEntry_eq
  given: {n : Nat} (A F : Matrix (Fin n) (Fin n) R)
  proof: by
  rfl

中文:
定理 stepEntry_eq
  条件: {n : 自然数} (A F : Matrix (Fin n) (Fin n) R)
  证明: by
  rfl
-/
theorem stepEntry_eq {n : Nat} (A F : Matrix (Fin n) (Fin n) R) :
    stepEntry A F =
      .of fun i j => (-∑ k in Finset.Ioi i, F k k) * A i j
        + ∑ k in Finset.Ioi i, F i k * A k j := by
  rfl

/--
theorem `birdDetSpec_zero` / 定理 `birdDetSpec_zero`

English:
theorem birdDetSpec_zero
  given: (A : Matrix (Fin 0) (Fin 0) R)
  proof: by
  rfl

中文:
定理 birdDetSpec_zero
  条件: (A : Matrix (Fin 0) (Fin 0) R)
  证明: by
  rfl
-/
@[simp] theorem birdDetSpec_zero (A : Matrix (Fin 0) (Fin 0) R) :
    birdDet A = 1 := by
  rfl

/--
theorem `birdDetSpec_succ` / 定理 `birdDetSpec_succ`

English:
theorem birdDetSpec_succ
  given: {k : Nat} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
  proof: by
  rw [birdDet]

中文:
定理 birdDetSpec_succ
  条件: {k : 自然数} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R)
  证明: by
  rw [birdDet]

Depends on / 依赖: birdDet
-/
theorem birdDetSpec_succ {k : Nat} (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    birdDet A = (-1 : R) ^ k * (stepEntry A)^[k] A 0 0 := by
  rw [birdDet]

end Spec

end BirdDet

end
