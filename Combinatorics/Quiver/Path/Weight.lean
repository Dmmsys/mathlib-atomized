/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Algebra.Order.Ring.Defs


/-!
# Path weights in a Quiver

This file defines the weight of a path in a quiver. The weight of a path is the product of the
weights of its edges, where weights are taken from a monoid.

## Main definitions

* `Quiver.Path.weight`: The weight of a path, defined as the multiplicative product of the
  weights of its constituent edges.
* `Quiver.Path.weightOfEPs`: A convenience version of `weight` where the weight of an edge
  is determined by a function of its source and target vertices.

## Main results

* `Quiver.Path.weight_comp`: The weight of a composition of paths is the product of their weights.
* `Quiver.Path.weight_pos`: If all edge weights are positive, the path weight is positive.
* `Quiver.Path.weightOfEPs_nonneg`: If all edge weights are non-negative, so is the path weight.
-/

@[expose] public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

/--
Definition of `weight` / `weight` 的定义

English:
definition weight
  signature: (w : forall {i j : V}, (i ⟶ j) -> R)

中文:
定义 weight
  签名: (w : 对任意 {i j : V}, (i ⟶ j) -> R)
-/
def weight (w : forall {i j : V}, (i ⟶ j) -> R) : forall {i j : V}, Path i j -> R
  | _, _, Path.nil => 1
  | _, _, Path.cons p e => weight w p * w e

/--
Definition of `addWeight` / `addWeight` 的定义

English:
definition addWeight
  signature: {R : Type*} [AddMonoid R] (w : forall {i j : V}, (i ⟶ j) -> R)

中文:
定义 addWeight
  签名: {R : 类型} [AddMonoid R] (w : 对任意 {i j : V}, (i ⟶ j) -> R)
-/
def addWeight {R : Type*} [AddMonoid R] (w : forall {i j : V}, (i ⟶ j) -> R) : forall {i j : V}, Path i j -> R
  | _, _, Path.nil => 0
  | _, _, Path.cons p e => addWeight w p + w e

attribute [to_additive existing addWeight] weight

/-- The weight of a path, where the weight of an edge is defined by a function on its endpoints. -/
@[to_additive addWeightOfEPs /-- The additive weight of a path, where the weight of an edge is
defined by a function on its endpoints. -/]
/--
Definition of `weightOfEPs` / `weightOfEPs` 的定义

English:
definition weightOfEPs
  signature: (w : V -> V -> R)
  body: weight (fun {i j} (_ : i ⟶ j) => w i j)

@[to_additive (attr := simp) addWeight_nil]

中文:
定义 weightOfEPs
  签名: (w : V -> V -> R)
  定义体: weight (fun {i j} (_ : i ⟶ j) => w i j)

@[to_additive (attr := simp) addWeight_nil]

Depends on / 依赖: weight
-/
def weightOfEPs (w : V -> V -> R) : forall {i j : V}, Path i j -> R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

@[to_additive (attr := simp) addWeight_nil]
/--
lemma `weight_nil` / 引理 `weight_nil`

English:
lemma weight_nil
  given: (w : forall {i j : V}, (i ⟶ j) -> R) (a : V)
  proof: by
  simp [weight]

@[to_additive (attr := simp) addWeight_cons]

中文:
引理 weight_nil
  条件: (w : 对任意 {i j : V}, (i ⟶ j) -> R) (a : V)
  证明: by
  simp [weight]

@[to_additive (attr := simp) addWeight_cons]

Depends on / 依赖: weight
-/
lemma weight_nil (w : forall {i j : V}, (i ⟶ j) -> R) (a : V) :
    weight w (Path.nil : Path a a) = 1 := by
  simp [weight]

@[to_additive (attr := simp) addWeight_cons]
/--
lemma `weight_cons` / 引理 `weight_cons`

English:
lemma weight_cons
  given: (w : forall {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b) (e : b ⟶ c)
  proof: by
  simp [weight]

@[to_additive addWeightOfEPs_nil]

中文:
引理 weight_cons
  条件: (w : 对任意 {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b) (e : b ⟶ c)
  证明: by
  simp [weight]

@[to_additive addWeightOfEPs_nil]

Depends on / 依赖: weight
-/
lemma weight_cons (w : forall {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weight w (p.cons e) = weight w p * w e := by
  simp [weight]

@[to_additive addWeightOfEPs_nil]
/--
lemma `weightOfEPs_nil` / 引理 `weightOfEPs_nil`

English:
lemma weightOfEPs_nil
  given: (w : V -> V -> R) (a : V)
  proof: by simp [weightOfEPs]

@[to_additive addWeightOfEPs_cons]

中文:
引理 weightOfEPs_nil
  条件: (w : V -> V -> R) (a : V)
  证明: by simp [weightOfEPs]

@[to_additive addWeightOfEPs_cons]

Depends on / 依赖: weightOfEPs
-/
lemma weightOfEPs_nil (w : V -> V -> R) (a : V) :
    weightOfEPs w (Path.nil : Path a a) = 1 := by simp [weightOfEPs]

@[to_additive addWeightOfEPs_cons]
/--
lemma `weightOfEPs_cons` / 引理 `weightOfEPs_cons`

English:
lemma weightOfEPs_cons
  given: (w : V -> V -> R) {a b c : V} (p : Path a b) (e : b ⟶ c)
  proof: by unfold weightOfEPs; simp

@[to_additive (attr := simp) addWeight_comp]

中文:
引理 weightOfEPs_cons
  条件: (w : V -> V -> R) {a b c : V} (p : Path a b) (e : b ⟶ c)
  证明: by unfold weightOfEPs; simp

@[to_additive (attr := simp) addWeight_comp]

Depends on / 依赖: weightOfEPs
-/
lemma weightOfEPs_cons (w : V -> V -> R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weightOfEPs w (p.cons e) = weightOfEPs w p * w b c := by unfold weightOfEPs; simp

@[to_additive (attr := simp) addWeight_comp]
/--
lemma `weight_comp` / 引理 `weight_comp`

English:
lemma weight_comp
  given: (w : forall {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b) (q : Path b c)
  proof: by
  induction q with
  | nil => simp
  | cons _ _ ih => simp [ih, mul_assoc]

@[to_additive addWeightOfEPs_comp]

中文:
引理 weight_comp
  条件: (w : 对任意 {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b) (q : Path b c)
  证明: by
  induction q with
  | nil => simp
  | cons _ _ ih => simp [ih, mul_assoc]

@[to_additive addWeightOfEPs_comp]

Depends on / 依赖: mul_assoc
-/
lemma weight_comp (w : forall {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b) (q : Path b c) :
    weight w (p.comp q) = weight w p * weight w q := by
  induction q with
  | nil => simp
  | cons _ _ ih => simp [ih, mul_assoc]

@[to_additive addWeightOfEPs_comp]
/--
lemma `weightOfEPs_comp` / 引理 `weightOfEPs_comp`

English:
lemma weightOfEPs_comp
  given: (w : V -> V -> R) {a b c : V} (p : Path a b) (q : Path b c)
  proof: by
  simp [weightOfEPs, weight_comp]

中文:
引理 weightOfEPs_comp
  条件: (w : V -> V -> R) {a b c : V} (p : Path a b) (q : Path b c)
  证明: by
  simp [weightOfEPs, weight_comp]

Depends on / 依赖: weightOfEPs, weight_comp
-/
lemma weightOfEPs_comp (w : V -> V -> R) {a b c : V} (p : Path a b) (q : Path b c) :
    weightOfEPs w (p.comp q) = weightOfEPs w p * weightOfEPs w q := by
  simp [weightOfEPs, weight_comp]

end Weight

section OrderedWeight

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/--
lemma `weight_pos` / 引理 `weight_pos`

English:
lemma weight_pos
  statement: {w : forall {i j : V}, (i ⟶ j) -> R}
  proof: by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 < w e := hw e
      simpa [weight_cons] using mul_pos ih he

中文:
引理 weight_pos
  结论: {w : 对任意 {i j : V}, (i ⟶ j) -> R}
  证明: by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 < w e := hw e
      simpa [weight_cons] using mul_pos ih he

Depends on / 依赖: mul_pos, weight_cons
-/
lemma weight_pos {w : forall {i j : V}, (i ⟶ j) -> R}
    (hw : forall {i j : V} (e : i ⟶ j), 0 < w e) {i j : V} (p : Path i j) :
    0 < weight w p := by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 < w e := hw e
      simpa [weight_cons] using mul_pos ih he

/--
lemma `weight_nonneg` / 引理 `weight_nonneg`

English:
lemma weight_nonneg
  statement: {w : forall {i j : V}, (i ⟶ j) -> R}
  proof: by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 <= w e := hw e
      simpa [weight_cons] using mul_nonneg ih he

中文:
引理 weight_nonneg
  结论: {w : 对任意 {i j : V}, (i ⟶ j) -> R}
  证明: by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 <= w e := hw e
      simpa [weight_cons] using mul_nonneg ih he

Depends on / 依赖: mul_nonneg, weight_cons
-/
lemma weight_nonneg {w : forall {i j : V}, (i ⟶ j) -> R}
    (hw : forall {i j : V} (e : i ⟶ j), 0 <= w e) {i j : V} (p : Path i j) :
    0 <= weight w p := by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 <= w e := hw e
      simpa [weight_cons] using mul_nonneg ih he

/--
lemma `weightOfEPs_pos` / 引理 `weightOfEPs_pos`

English:
lemma weightOfEPs_pos
  statement: {w : V -> V -> R}
  proof: by
  apply weight_pos
  intro i j e
  exact hw _ _

中文:
引理 weightOfEPs_pos
  结论: {w : V -> V -> R}
  证明: by
  apply weight_pos
  intro i j e
  exact hw _ _

Depends on / 依赖: weight_pos
-/
lemma weightOfEPs_pos {w : V -> V -> R}
    (hw : forall i j : V, 0 < w i j) {i j : V} (p : Path i j) :
    0 < weightOfEPs w p := by
  apply weight_pos
  intro i j e
  exact hw _ _

/--
lemma `weightOfEPs_nonneg` / 引理 `weightOfEPs_nonneg`

English:
lemma weightOfEPs_nonneg
  statement: {w : V -> V -> R}
  proof: by
  apply weight_nonneg
  intro i j e
  exact hw _ _

中文:
引理 weightOfEPs_nonneg
  结论: {w : V -> V -> R}
  证明: by
  apply weight_nonneg
  intro i j e
  exact hw _ _

Depends on / 依赖: weight_nonneg
-/
lemma weightOfEPs_nonneg {w : V -> V -> R}
    (hw : forall i j : V, 0 <= w i j) {i j : V} (p : Path i j) :
    0 <= weightOfEPs w p := by
  apply weight_nonneg
  intro i j e
  exact hw _ _

end OrderedWeight

end Quiver.Path
