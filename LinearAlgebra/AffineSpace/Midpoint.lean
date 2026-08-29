/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `AddMonoidHom.ofMapMidpoint`: construct an `AddMonoidHom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `pointReflection_midpoint_left`, `pointReflection_midpoint_right`:
  `Equiv.pointReflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, AddMonoidHom
-/

@[expose] public section

open AffineMap AffineEquiv

section

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `midpoint` / `midpoint` 的定义

English:
definition midpoint
  signature: (x y : P)
  body: lineMap x y (⅟2 : R)

中文:
定义 midpoint
  签名: (x y : P)
  定义体: lineMap x y (⅟2 : R)

Depends on / 依赖: lineMap
-/
def midpoint (x y : P) : P :=
  lineMap x y (⅟2 : R)

variable {R} {x y z : P}

@[simp]
/--
theorem `AffineMap.map_midpoint` / 定理 `AffineMap.map_midpoint`

English:
theorem AffineMap.map_midpoint
  given: (f : P ->ᵃ[R] P') (a b : P)
  proof: f.apply_lineMap a b _

@[simp]

中文:
定理 仿射映射.map_midpoint
  条件: (f : P ->ᵃ[R] P') (a b : P)
  证明: f.apply_lineMap a b _

@[simp]

Depends on / 依赖: apply_lineMap, f.apply_lineMap
-/
theorem AffineMap.map_midpoint (f : P ->ᵃ[R] P') (a b : P) :
    f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_lineMap a b _

@[simp]
/--
theorem `AffineEquiv.map_midpoint` / 定理 `AffineEquiv.map_midpoint`

English:
theorem AffineEquiv.map_midpoint
  given: (f : P ≃ᵃ[R] P') (a b : P)
  proof: f.apply_lineMap a b _

中文:
定理 仿射等价.map_midpoint
  条件: (f : P ≃ᵃ[R] P') (a b : P)
  证明: f.apply_lineMap a b _

Depends on / 依赖: apply_lineMap, f.apply_lineMap
-/
theorem AffineEquiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) :
    f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_lineMap a b _

/--
theorem `AffineEquiv.pointReflection_midpoint_left` / 定理 `AffineEquiv.pointReflection_midpoint_left`

English:
theorem AffineEquiv.pointReflection_midpoint_left
  given: (x y : P)
  proof: by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]

@[simp]

中文:
定理 仿射等价.pointReflection_midpoint_left
  条件: (x y : P)
  证明: by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]

@[simp]

Depends on / 依赖: add_smul, lineMap_apply, midpoint, mul_invOf_self, one_smul, pointReflection_apply, two_mul, vadd_vadd, vadd_vsub, vsub_vadd
-/
theorem AffineEquiv.pointReflection_midpoint_left (x y : P) :
    pointReflection R (midpoint R x y) x = y := by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]

@[simp]
/--
theorem `Equiv.pointReflection_midpoint_left` / 定理 `Equiv.pointReflection_midpoint_left`

English:
theorem Equiv.pointReflection_midpoint_left
  given: (x y : P)
  proof: by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]

中文:
定理 等价.pointReflection_midpoint_left
  条件: (x y : P)
  证明: by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]

Depends on / 依赖: add_smul, lineMap_apply, midpoint, mul_invOf_self, one_smul, pointReflection_apply, two_mul, vadd_vadd, vadd_vsub, vsub_vadd
-/
theorem Equiv.pointReflection_midpoint_left (x y : P) :
    (Equiv.pointReflection (midpoint R x y)) x = y := by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]

/--
theorem `midpoint_comm` / 定理 `midpoint_comm`

English:
theorem midpoint_comm
  given: (x y : P)
  statement: midpoint R x y = midpoint R y x
  proof: by
  rw [midpoint]; rw [← lineMap_apply_one_sub]; rw [one_sub_invOf_two]; rw [midpoint]

中文:
定理 midpoint_comm
  条件: (x y : P)
  结论: midpoint R x y = midpoint R y x
  证明: by
  rw [midpoint]; rw [← lineMap_apply_one_sub]; rw [one_sub_invOf_two]; rw [midpoint]

Depends on / 依赖: lineMap_apply_one_sub, midpoint, one_sub_invOf_two
-/
theorem midpoint_comm (x y : P) : midpoint R x y = midpoint R y x := by
  rw [midpoint]; rw [← lineMap_apply_one_sub]; rw [one_sub_invOf_two]; rw [midpoint]

/--
theorem `AffineEquiv.pointReflection_midpoint_right` / 定理 `AffineEquiv.pointReflection_midpoint_right`

English:
theorem AffineEquiv.pointReflection_midpoint_right
  given: (x y : P)
  proof: by
  rw [midpoint_comm]; rw [AffineEquiv.pointReflection_midpoint_left]

@[simp]

中文:
定理 仿射等价.pointReflection_midpoint_right
  条件: (x y : P)
  证明: by
  rw [midpoint_comm]; rw [AffineEquiv.pointReflection_midpoint_left]

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_midpoint_left, midpoint_comm, pointReflection_midpoint_left
-/
theorem AffineEquiv.pointReflection_midpoint_right (x y : P) :
    pointReflection R (midpoint R x y) y = x := by
  rw [midpoint_comm]; rw [AffineEquiv.pointReflection_midpoint_left]

@[simp]
/--
theorem `Equiv.pointReflection_midpoint_right` / 定理 `Equiv.pointReflection_midpoint_right`

English:
theorem Equiv.pointReflection_midpoint_right
  given: (x y : P)
  proof: by
  rw [midpoint_comm]; rw [Equiv.pointReflection_midpoint_left]

中文:
定理 等价.pointReflection_midpoint_right
  条件: (x y : P)
  证明: by
  rw [midpoint_comm]; rw [Equiv.pointReflection_midpoint_left]

Depends on / 依赖: Equiv.pointReflection_midpoint_left, midpoint_comm, pointReflection_midpoint_left
-/
theorem Equiv.pointReflection_midpoint_right (x y : P) :
    (Equiv.pointReflection (midpoint R x y)) y = x := by
  rw [midpoint_comm]; rw [Equiv.pointReflection_midpoint_left]

/--
theorem `midpoint_vsub_midpoint` / 定理 `midpoint_vsub_midpoint`

English:
theorem midpoint_vsub_midpoint
  given: (p₁ p₂ p₃ p₄ : P)
  proof: lineMap_vsub_lineMap _ _ _ _ _

中文:
定理 midpoint_vsub_midpoint
  条件: (p₁ p₂ p₃ p₄ : P)
  证明: lineMap_vsub_lineMap _ _ _ _ _

Depends on / 依赖: lineMap_vsub_lineMap
-/
theorem midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) :
    midpoint R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) :=
  lineMap_vsub_lineMap _ _ _ _ _

/--
theorem `midpoint_vadd_midpoint` / 定理 `midpoint_vadd_midpoint`

English:
theorem midpoint_vadd_midpoint
  given: (v v' : V) (p p' : P)
  proof: lineMap_vadd_lineMap _ _ _ _ _

中文:
定理 midpoint_vadd_midpoint
  条件: (v v' : V) (p p' : P)
  证明: lineMap_vadd_lineMap _ _ _ _ _

Depends on / 依赖: lineMap_vadd_lineMap
-/
theorem midpoint_vadd_midpoint (v v' : V) (p p' : P) :
    midpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p') :=
  lineMap_vadd_lineMap _ _ _ _ _

/--
theorem `midpoint_eq_iff` / 定理 `midpoint_eq_iff`

English:
theorem midpoint_eq_iff
  given: {x y z : P}
  statement: midpoint R x y = z ↔ pointReflection R z x = y
  proof: eq_comm.trans
    ((injective_pointReflection_left_of_module R x).eq_iff'
        (AffineEquiv.pointReflection_midpoint_left x y)).symm

@[simp]

中文:
定理 midpoint_eq_iff
  条件: {x y z : P}
  结论: midpoint R x y = z ↔ pointReflection R z x = y
  证明: eq_comm.trans
    ((injective_pointReflection_left_of_module R x).eq_iff'
        (AffineEquiv.pointReflection_midpoint_left x y)).symm

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_midpoint_left, eq_comm, eq_comm.trans, eq_iff, injective_pointReflection_left_of_module, pointReflection_midpoint_left
-/
theorem midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ pointReflection R z x = y :=
  eq_comm.trans
    ((injective_pointReflection_left_of_module R x).eq_iff'
        (AffineEquiv.pointReflection_midpoint_left x y)).symm

@[simp]
/--
theorem `midpoint_pointReflection_left` / 定理 `midpoint_pointReflection_left`

English:
theorem midpoint_pointReflection_left
  given: (x y : P)
  proof: midpoint_eq_iff.2 Equiv.pointReflection_involutive _ _

@[simp]

中文:
定理 midpoint_pointReflection_left
  条件: (x y : P)
  证明: midpoint_eq_iff.2 Equiv.pointReflection_involutive _ _

@[simp]

Depends on / 依赖: Equiv.pointReflection_involutive, midpoint_eq_iff, pointReflection_involutive
-/
theorem midpoint_pointReflection_left (x y : P) :
    midpoint R (Equiv.pointReflection x y) y = x :=
midpoint_eq_iff.2 Equiv.pointReflection_involutive _ _

@[simp]
/--
theorem `midpoint_pointReflection_right` / 定理 `midpoint_pointReflection_right`

English:
theorem midpoint_pointReflection_right
  given: (x y : P)
  proof: midpoint_eq_iff.2 rfl

nonrec lemma AffineEquiv.midpoint_pointReflection_left (x y : P) :
    midpoint R (pointReflection R x y) y = x :=
  midpoint_pointReflection_left x y

nonrec lemma AffineEquiv.midpoint_pointReflection_right (x y : P) :
    midpoint R y (pointReflection R x y) = x :=
  midpoin

中文:
定理 midpoint_pointReflection_right
  条件: (x y : P)
  证明: midpoint_eq_iff.2 rfl

nonrec lemma AffineEquiv.midpoint_pointReflection_left (x y : P) :
    midpoint R (pointReflection R x y) y = x :=
  midpoint_pointReflection_left x y

nonrec lemma AffineEquiv.midpoint_pointReflection_right (x y : P) :
    midpoint R y (pointReflection R x y) = x :=
  midpoin

Depends on / 依赖: midpoint_eq_iff
-/
theorem midpoint_pointReflection_right (x y : P) :
    midpoint R y (Equiv.pointReflection x y) = x :=
  midpoint_eq_iff.2 rfl

nonrec lemma AffineEquiv.midpoint_pointReflection_left (x y : P) :
    midpoint R (pointReflection R x y) y = x :=
  midpoint_pointReflection_left x y

nonrec lemma AffineEquiv.midpoint_pointReflection_right (x y : P) :
    midpoint R y (pointReflection R x y) = x :=
  midpoint_pointReflection_right x y

@[simp]
/--
theorem `midpoint_vsub_left` / 定理 `midpoint_vsub_left`

English:
theorem midpoint_vsub_left
  given: (p₁ p₂ : P)
  statement: midpoint R p₁ p₂ -ᵥ p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
  proof: lineMap_vsub_left _ _ _

@[simp]

中文:
定理 midpoint_vsub_left
  条件: (p₁ p₂ : P)
  结论: midpoint R p₁ p₂ -ᵥ p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
  证明: lineMap_vsub_left _ _ _

@[simp]

Depends on / 依赖: lineMap_vsub_left
-/
theorem midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = (⅟2 : R) • (p₂ -ᵥ p₁) :=
  lineMap_vsub_left _ _ _

@[simp]
/--
theorem `midpoint_vsub_right` / 定理 `midpoint_vsub_right`

English:
theorem midpoint_vsub_right
  given: (p₁ p₂ : P)
  statement: midpoint R p₁ p₂ -ᵥ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
  proof: by
  rw [midpoint_comm]; rw [midpoint_vsub_left]

@[simp]

中文:
定理 midpoint_vsub_right
  条件: (p₁ p₂ : P)
  结论: midpoint R p₁ p₂ -ᵥ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
  证明: by
  rw [midpoint_comm]; rw [midpoint_vsub_left]

@[simp]

Depends on / 依赖: midpoint_comm, midpoint_vsub_left
-/
theorem midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂) := by
  rw [midpoint_comm]; rw [midpoint_vsub_left]

@[simp]
/--
theorem `left_vsub_midpoint` / 定理 `left_vsub_midpoint`

English:
theorem left_vsub_midpoint
  given: (p₁ p₂ : P)
  statement: p₁ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
  proof: left_vsub_lineMap _ _ _

@[simp]

中文:
定理 left_vsub_midpoint
  条件: (p₁ p₂ : P)
  结论: p₁ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
  证明: left_vsub_lineMap _ _ _

@[simp]

Depends on / 依赖: left_vsub_lineMap
-/
theorem left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂) :=
  left_vsub_lineMap _ _ _

@[simp]
/--
theorem `right_vsub_midpoint` / 定理 `right_vsub_midpoint`

English:
theorem right_vsub_midpoint
  given: (p₁ p₂ : P)
  statement: p₂ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁)
  proof: by
  rw [midpoint_comm]; rw [left_vsub_midpoint]

中文:
定理 right_vsub_midpoint
  条件: (p₁ p₂ : P)
  结论: p₂ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁)
  证明: by
  rw [midpoint_comm]; rw [left_vsub_midpoint]

Depends on / 依赖: left_vsub_midpoint, midpoint_comm
-/
theorem right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁) := by
  rw [midpoint_comm]; rw [left_vsub_midpoint]

/--
theorem `midpoint_vsub` / 定理 `midpoint_vsub`

English:
theorem midpoint_vsub
  given: (p₁ p₂ p : P)
  proof: by
  rw [← vsub_sub_vsub_cancel_right p₁ p p₂]; rw [smul_sub]; rw [sub_eq_add_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [add_assoc]; rw [invOf_two_smul_add_invOf_two_smul]; rw [← vadd_vsub_assoc]; rw [midpoint_comm]; rw [midpoint]; rw [lineMap_apply]

中文:
定理 midpoint_vsub
  条件: (p₁ p₂ p : P)
  证明: by
  rw [← vsub_sub_vsub_cancel_right p₁ p p₂]; rw [smul_sub]; rw [sub_eq_add_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [add_assoc]; rw [invOf_two_smul_add_invOf_two_smul]; rw [← vadd_vsub_assoc]; rw [midpoint_comm]; rw [midpoint]; rw [lineMap_apply]

Depends on / 依赖: add_assoc, invOf_two_smul_add_invOf_two_smul, lineMap_apply, midpoint, midpoint_comm, neg_vsub_eq_vsub_rev, smul_neg, smul_sub, sub_eq_add_neg, vadd_vsub_assoc, vsub_sub_vsub_cancel_right
-/
theorem midpoint_vsub (p₁ p₂ p : P) :
    midpoint R p₁ p₂ -ᵥ p = (⅟2 : R) • (p₁ -ᵥ p) + (⅟2 : R) • (p₂ -ᵥ p) := by
  rw [← vsub_sub_vsub_cancel_right p₁ p p₂]; rw [smul_sub]; rw [sub_eq_add_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [add_assoc]; rw [invOf_two_smul_add_invOf_two_smul]; rw [← vadd_vsub_assoc]; rw [midpoint_comm]; rw [midpoint]; rw [lineMap_apply]

/--
theorem `vsub_midpoint` / 定理 `vsub_midpoint`

English:
theorem vsub_midpoint
  given: (p₁ p₂ p : P)
  proof: by
  rw [← neg_vsub_eq_vsub_rev]; rw [midpoint_vsub]; rw [neg_add]; rw [← smul_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]

@[simp]

中文:
定理 vsub_midpoint
  条件: (p₁ p₂ p : P)
  证明: by
  rw [← neg_vsub_eq_vsub_rev]; rw [midpoint_vsub]; rw [neg_add]; rw [← smul_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]

@[simp]

Depends on / 依赖: midpoint_vsub, neg_add, neg_vsub_eq_vsub_rev, smul_neg
-/
theorem vsub_midpoint (p₁ p₂ p : P) :
    p -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p -ᵥ p₁) + (⅟2 : R) • (p -ᵥ p₂) := by
  rw [← neg_vsub_eq_vsub_rev]; rw [midpoint_vsub]; rw [neg_add]; rw [← smul_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]

@[simp]
/--
theorem `midpoint_sub_left` / 定理 `midpoint_sub_left`

English:
theorem midpoint_sub_left
  given: (v₁ v₂ : V)
  statement: midpoint R v₁ v₂ - v₁ = (⅟2 : R) • (v₂ - v₁)
  proof: midpoint_vsub_left v₁ v₂

@[simp]

中文:
定理 midpoint_sub_left
  条件: (v₁ v₂ : V)
  结论: midpoint R v₁ v₂ - v₁ = (⅟2 : R) • (v₂ - v₁)
  证明: midpoint_vsub_left v₁ v₂

@[simp]

Depends on / 依赖: midpoint_vsub_left
-/
theorem midpoint_sub_left (v₁ v₂ : V) : midpoint R v₁ v₂ - v₁ = (⅟2 : R) • (v₂ - v₁) :=
  midpoint_vsub_left v₁ v₂

@[simp]
/--
theorem `midpoint_sub_right` / 定理 `midpoint_sub_right`

English:
theorem midpoint_sub_right
  given: (v₁ v₂ : V)
  statement: midpoint R v₁ v₂ - v₂ = (⅟2 : R) • (v₁ - v₂)
  proof: midpoint_vsub_right v₁ v₂

@[simp]

中文:
定理 midpoint_sub_right
  条件: (v₁ v₂ : V)
  结论: midpoint R v₁ v₂ - v₂ = (⅟2 : R) • (v₁ - v₂)
  证明: midpoint_vsub_right v₁ v₂

@[simp]

Depends on / 依赖: midpoint_vsub_right
-/
theorem midpoint_sub_right (v₁ v₂ : V) : midpoint R v₁ v₂ - v₂ = (⅟2 : R) • (v₁ - v₂) :=
  midpoint_vsub_right v₁ v₂

@[simp]
/--
theorem `left_sub_midpoint` / 定理 `left_sub_midpoint`

English:
theorem left_sub_midpoint
  given: (v₁ v₂ : V)
  statement: v₁ - midpoint R v₁ v₂ = (⅟2 : R) • (v₁ - v₂)
  proof: left_vsub_midpoint v₁ v₂

@[simp]

中文:
定理 left_sub_midpoint
  条件: (v₁ v₂ : V)
  结论: v₁ - midpoint R v₁ v₂ = (⅟2 : R) • (v₁ - v₂)
  证明: left_vsub_midpoint v₁ v₂

@[simp]

Depends on / 依赖: left_vsub_midpoint
-/
theorem left_sub_midpoint (v₁ v₂ : V) : v₁ - midpoint R v₁ v₂ = (⅟2 : R) • (v₁ - v₂) :=
  left_vsub_midpoint v₁ v₂

@[simp]
/--
theorem `right_sub_midpoint` / 定理 `right_sub_midpoint`

English:
theorem right_sub_midpoint
  given: (v₁ v₂ : V)
  statement: v₂ - midpoint R v₁ v₂ = (⅟2 : R) • (v₂ - v₁)
  proof: right_vsub_midpoint v₁ v₂

中文:
定理 right_sub_midpoint
  条件: (v₁ v₂ : V)
  结论: v₂ - midpoint R v₁ v₂ = (⅟2 : R) • (v₂ - v₁)
  证明: right_vsub_midpoint v₁ v₂

Depends on / 依赖: right_vsub_midpoint
-/
theorem right_sub_midpoint (v₁ v₂ : V) : v₂ - midpoint R v₁ v₂ = (⅟2 : R) • (v₂ - v₁) :=
  right_vsub_midpoint v₁ v₂

variable (R)

@[simp]
/--
theorem `midpoint_eq_left_iff` / 定理 `midpoint_eq_left_iff`

English:
theorem midpoint_eq_left_iff
  given: {x y : P}
  statement: midpoint R x y = x ↔ x = y
  proof: by
  rw [midpoint_eq_iff]; rw [pointReflection_self]

@[simp]

中文:
定理 midpoint_eq_left_iff
  条件: {x y : P}
  结论: midpoint R x y = x ↔ x = y
  证明: by
  rw [midpoint_eq_iff]; rw [pointReflection_self]

@[simp]

Depends on / 依赖: midpoint_eq_iff, pointReflection_self
-/
theorem midpoint_eq_left_iff {x y : P} : midpoint R x y = x ↔ x = y := by
  rw [midpoint_eq_iff]; rw [pointReflection_self]

@[simp]
/--
theorem `left_eq_midpoint_iff` / 定理 `left_eq_midpoint_iff`

English:
theorem left_eq_midpoint_iff
  given: {x y : P}
  statement: x = midpoint R x y ↔ x = y
  proof: by
  rw [eq_comm]; rw [midpoint_eq_left_iff]

@[simp]

中文:
定理 left_eq_midpoint_iff
  条件: {x y : P}
  结论: x = midpoint R x y ↔ x = y
  证明: by
  rw [eq_comm]; rw [midpoint_eq_left_iff]

@[simp]

Depends on / 依赖: eq_comm, midpoint_eq_left_iff
-/
theorem left_eq_midpoint_iff {x y : P} : x = midpoint R x y ↔ x = y := by
  rw [eq_comm]; rw [midpoint_eq_left_iff]

@[simp]
/--
theorem `midpoint_eq_right_iff` / 定理 `midpoint_eq_right_iff`

English:
theorem midpoint_eq_right_iff
  given: {x y : P}
  statement: midpoint R x y = y ↔ x = y
  proof: by
  rw [midpoint_comm]; rw [midpoint_eq_left_iff]; rw [eq_comm]

@[simp]

中文:
定理 midpoint_eq_right_iff
  条件: {x y : P}
  结论: midpoint R x y = y ↔ x = y
  证明: by
  rw [midpoint_comm]; rw [midpoint_eq_left_iff]; rw [eq_comm]

@[simp]

Depends on / 依赖: eq_comm, midpoint_comm, midpoint_eq_left_iff
-/
theorem midpoint_eq_right_iff {x y : P} : midpoint R x y = y ↔ x = y := by
  rw [midpoint_comm]; rw [midpoint_eq_left_iff]; rw [eq_comm]

@[simp]
/--
theorem `right_eq_midpoint_iff` / 定理 `right_eq_midpoint_iff`

English:
theorem right_eq_midpoint_iff
  given: {x y : P}
  statement: y = midpoint R x y ↔ x = y
  proof: by
  rw [eq_comm]; rw [midpoint_eq_right_iff]

中文:
定理 right_eq_midpoint_iff
  条件: {x y : P}
  结论: y = midpoint R x y ↔ x = y
  证明: by
  rw [eq_comm]; rw [midpoint_eq_right_iff]

Depends on / 依赖: eq_comm, midpoint_eq_right_iff
-/
theorem right_eq_midpoint_iff {x y : P} : y = midpoint R x y ↔ x = y := by
  rw [eq_comm]; rw [midpoint_eq_right_iff]

/--
theorem `midpoint_eq_midpoint_iff_vsub_eq_vsub` / 定理 `midpoint_eq_midpoint_iff_vsub_eq_vsub`

English:
theorem midpoint_eq_midpoint_iff_vsub_eq_vsub
  given: {x x' y y' : P}
  proof: by
  rw [← @vsub_eq_zero_iff_eq V]; rw [midpoint_vsub_midpoint]; rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [zero_sub]; rw [vadd_eq_add]; rw [add_zero]; rw [neg_eq_iff_eq_neg]; rw [neg_vsub_eq_vsub_rev]

中文:
定理 midpoint_eq_midpoint_iff_vsub_eq_vsub
  条件: {x x' y y' : P}
  证明: by
  rw [← @vsub_eq_zero_iff_eq V]; rw [midpoint_vsub_midpoint]; rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [zero_sub]; rw [vadd_eq_add]; rw [add_zero]; rw [neg_eq_iff_eq_neg]; rw [neg_vsub_eq_vsub_rev]

Depends on / 依赖: add_zero, midpoint_eq_iff, midpoint_vsub_midpoint, neg_eq_iff_eq_neg, neg_vsub_eq_vsub_rev, pointReflection_apply, vadd_eq_add, vsub_eq_sub, vsub_eq_zero_iff_eq, zero_sub
-/
theorem midpoint_eq_midpoint_iff_vsub_eq_vsub {x x' y y' : P} :
    midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y := by
  rw [← @vsub_eq_zero_iff_eq V]; rw [midpoint_vsub_midpoint]; rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [zero_sub]; rw [vadd_eq_add]; rw [add_zero]; rw [neg_eq_iff_eq_neg]; rw [neg_vsub_eq_vsub_rev]

/--
theorem `midpoint_eq_iff'` / 定理 `midpoint_eq_iff'`

English:
theorem midpoint_eq_iff'
  given: {x y z : P}
  statement: midpoint R x y = z ↔ Equiv.pointReflection z x = y
  proof: midpoint_eq_iff

中文:
定理 midpoint_eq_iff'
  条件: {x y z : P}
  结论: midpoint R x y = z ↔ 等价.pointReflection z x = y
  证明: midpoint_eq_iff

Depends on / 依赖: midpoint_eq_iff
-/
theorem midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ Equiv.pointReflection z x = y :=
  midpoint_eq_iff

/--
theorem `midpoint_unique` / 定理 `midpoint_unique`

English:
theorem midpoint_unique
  given: (R' : Type*) [Ring R'] [Invertible (2 : R')] [Module R' V] (x y : P)
  proof: (midpoint_eq_iff' R).2 (midpoint_eq_iff' R').1 rfl

@[simp]

中文:
定理 midpoint_unique
  条件: (R' : 类型) [环 R'] [可逆 (2 : R')] [模 R' V] (x y : P)
  证明: (midpoint_eq_iff' R).2 (midpoint_eq_iff' R').1 rfl

@[simp]

Depends on / 依赖: midpoint_eq_iff
-/
theorem midpoint_unique (R' : Type*) [Ring R'] [Invertible (2 : R')] [Module R' V] (x y : P) :
    midpoint R x y = midpoint R' x y :=
(midpoint_eq_iff' R).2 (midpoint_eq_iff' R').1 rfl

@[simp]
/--
theorem `midpoint_self` / 定理 `midpoint_self`

English:
theorem midpoint_self
  given: (x : P)
  statement: midpoint R x x = x
  proof: lineMap_same_apply _ _

@[simp]

中文:
定理 midpoint_self
  条件: (x : P)
  结论: midpoint R x x = x
  证明: lineMap_same_apply _ _

@[simp]

Depends on / 依赖: lineMap_same_apply
-/
theorem midpoint_self (x : P) : midpoint R x x = x :=
  lineMap_same_apply _ _

@[simp]
/--
theorem `midpoint_add_self` / 定理 `midpoint_add_self`

English:
theorem midpoint_add_self
  given: (x y : V)
  statement: midpoint R x y + midpoint R x y = x + y
  proof: calc
    midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x := by rw [midpoint_comm]
    _ = x + y := by rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_comm, midpoint_self]

中文:
定理 midpoint_add_self
  条件: (x y : V)
  结论: midpoint R x y + midpoint R x y = x + y
  证明: calc
    midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x := by rw [midpoint_comm]
    _ = x + y := by rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_comm, midpoint_self]

Depends on / 依赖: add_comm, midpoint, midpoint_comm, midpoint_self, midpoint_vadd_midpoint, vadd_eq_add
-/
theorem midpoint_add_self (x y : V) : midpoint R x y + midpoint R x y = x + y :=
  calc
    midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x := by rw [midpoint_comm]
    _ = x + y := by rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_comm, midpoint_self]

/--
theorem `midpoint_zero_add` / 定理 `midpoint_zero_add`

English:
theorem midpoint_zero_add
  given: (x y : V)
  statement: midpoint R 0 (x + y) = midpoint R x y
  proof: (midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 by simp

中文:
定理 midpoint_zero_add
  条件: (x y : V)
  结论: midpoint R 0 (x + y) = midpoint R x y
  证明: (midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 by simp

Depends on / 依赖: midpoint_eq_midpoint_iff_vsub_eq_vsub
-/
theorem midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y :=
(midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 by simp

/--
theorem `midpoint_eq_smul_add` / 定理 `midpoint_eq_smul_add`

English:
theorem midpoint_eq_smul_add
  given: (x y : V)
  statement: midpoint R x y = (⅟2 : R) • (x + y)
  proof: by
  rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [vadd_eq_add]; rw [sub_add_eq_add_sub]; rw [←
    two_smul R]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [add_sub_cancel_left]

@[simp]

中文:
定理 midpoint_eq_smul_add
  条件: (x y : V)
  结论: midpoint R x y = (⅟2 : R) • (x + y)
  证明: by
  rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [vadd_eq_add]; rw [sub_add_eq_add_sub]; rw [←
    two_smul R]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [add_sub_cancel_left]

@[simp]

Depends on / 依赖: add_sub_cancel_left, midpoint_eq_iff, mul_invOf_self, one_smul, pointReflection_apply, smul_smul, sub_add_eq_add_sub, two_smul, vadd_eq_add, vsub_eq_sub
-/
theorem midpoint_eq_smul_add (x y : V) : midpoint R x y = (⅟2 : R) • (x + y) := by
  rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [vadd_eq_add]; rw [sub_add_eq_add_sub]; rw [←
    two_smul R]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [add_sub_cancel_left]

@[simp]
/--
theorem `midpoint_self_neg` / 定理 `midpoint_self_neg`

English:
theorem midpoint_self_neg
  given: (x : V)
  statement: midpoint R x (-x) = 0
  proof: by
  rw [midpoint_eq_smul_add]; rw [add_neg_cancel]; rw [smul_zero]

@[simp]

中文:
定理 midpoint_self_neg
  条件: (x : V)
  结论: midpoint R x (-x) = 0
  证明: by
  rw [midpoint_eq_smul_add]; rw [add_neg_cancel]; rw [smul_zero]

@[simp]

Depends on / 依赖: add_neg_cancel, midpoint_eq_smul_add, smul_zero
-/
theorem midpoint_self_neg (x : V) : midpoint R x (-x) = 0 := by
  rw [midpoint_eq_smul_add]; rw [add_neg_cancel]; rw [smul_zero]

@[simp]
/--
theorem `midpoint_neg_self` / 定理 `midpoint_neg_self`

English:
theorem midpoint_neg_self
  given: (x : V)
  statement: midpoint R (-x) x = 0
  proof: by simpa using midpoint_self_neg R (-x)

@[simp]

中文:
定理 midpoint_neg_self
  条件: (x : V)
  结论: midpoint R (-x) x = 0
  证明: by simpa using midpoint_self_neg R (-x)

@[simp]

Depends on / 依赖: midpoint_self_neg
-/
theorem midpoint_neg_self (x : V) : midpoint R (-x) x = 0 := by simpa using midpoint_self_neg R (-x)

@[simp]
/--
theorem `midpoint_sub_add` / 定理 `midpoint_sub_add`

English:
theorem midpoint_sub_add
  given: (x y : V)
  statement: midpoint R (x - y) (x + y) = x
  proof: by
  rw [sub_eq_add_neg]; rw [← vadd_eq_add]; rw [← vadd_eq_add]; rw [← midpoint_vadd_midpoint]; simp

@[simp]

中文:
定理 midpoint_sub_add
  条件: (x y : V)
  结论: midpoint R (x - y) (x + y) = x
  证明: by
  rw [sub_eq_add_neg]; rw [← vadd_eq_add]; rw [← vadd_eq_add]; rw [← midpoint_vadd_midpoint]; simp

@[simp]

Depends on / 依赖: midpoint_vadd_midpoint, sub_eq_add_neg, vadd_eq_add
-/
theorem midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y) = x := by
  rw [sub_eq_add_neg]; rw [← vadd_eq_add]; rw [← vadd_eq_add]; rw [← midpoint_vadd_midpoint]; simp

@[simp]
/--
theorem `midpoint_add_sub` / 定理 `midpoint_add_sub`

English:
theorem midpoint_add_sub
  given: (x y : V)
  statement: midpoint R (x + y) (x - y) = x
  proof: by
  rw [midpoint_comm]; simp

中文:
定理 midpoint_add_sub
  条件: (x y : V)
  结论: midpoint R (x + y) (x - y) = x
  证明: by
  rw [midpoint_comm]; simp

Depends on / 依赖: midpoint_comm
-/
theorem midpoint_add_sub (x y : V) : midpoint R (x + y) (x - y) = x := by
  rw [midpoint_comm]; simp

/--
theorem `midpoint_vsub_midpoint_same_left` / 定理 `midpoint_vsub_midpoint_same_left`

English:
theorem midpoint_vsub_midpoint_same_left
  given: (p₁ p₂ p₃ : P)
  proof: by
  rw [midpoint_vsub_midpoint]; rw [vsub_self]; rw [midpoint_eq_smul_add]; rw [zero_add]

中文:
定理 midpoint_vsub_midpoint_same_left
  条件: (p₁ p₂ p₃ : P)
  证明: by
  rw [midpoint_vsub_midpoint]; rw [vsub_self]; rw [midpoint_eq_smul_add]; rw [zero_add]

Depends on / 依赖: midpoint_eq_smul_add, midpoint_vsub_midpoint, vsub_self, zero_add
-/
theorem midpoint_vsub_midpoint_same_left (p₁ p₂ p₃ : P) :
    midpoint R p₁ p₂ -ᵥ midpoint R p₁ p₃ = (⅟2 : R) • (p₂ -ᵥ p₃) := by
  rw [midpoint_vsub_midpoint]; rw [vsub_self]; rw [midpoint_eq_smul_add]; rw [zero_add]

/--
theorem `midpoint_vsub_midpoint_same_right` / 定理 `midpoint_vsub_midpoint_same_right`

English:
theorem midpoint_vsub_midpoint_same_right
  given: (p₁ p₂ p₃ : P)
  proof: by
  rw [midpoint_vsub_midpoint]; rw [vsub_self]; rw [midpoint_eq_smul_add]; rw [add_zero]

中文:
定理 midpoint_vsub_midpoint_same_right
  条件: (p₁ p₂ p₃ : P)
  证明: by
  rw [midpoint_vsub_midpoint]; rw [vsub_self]; rw [midpoint_eq_smul_add]; rw [add_zero]

Depends on / 依赖: add_zero, midpoint_eq_smul_add, midpoint_vsub_midpoint, vsub_self
-/
theorem midpoint_vsub_midpoint_same_right (p₁ p₂ p₃ : P) :
    midpoint R p₁ p₃ -ᵥ midpoint R p₂ p₃ = (⅟2 : R) • (p₁ -ᵥ p₂) := by
  rw [midpoint_vsub_midpoint]; rw [vsub_self]; rw [midpoint_eq_smul_add]; rw [add_zero]

end

namespace AddMonoidHom

variable (R R' : Type*) {E F : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup E] [Module R E]
  [Ring R'] [Invertible (2 : R')] [AddCommGroup F] [Module R' F]

/--
Definition of `ofMapMidpoint` / `ofMapMidpoint` 的定义

English:
definition ofMapMidpoint
  signature: (f : E -> F) (h0 : f 0 = 0)
  body: f
  map_zero' := h0
  map_add' x y :=
    calc
      f (x + y) = f 0 + f (x + y) := by rw [h0, zero_add]
      _ = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :=
        (midpoint_add_self _ _ _).symm
      _ = f (midpoint R x y) + f (midpoint R x y) := by rw [← hm, midpoint_zero_a

中文:
定义 ofMapMidpoint
  签名: (f : E -> F) (h0 : f 0 = 0)
  定义体: f
  map_zero' := h0
  map_add' x y :=
    calc
      f (x + y) = f 0 + f (x + y) := by rw [h0, zero_add]
      _ = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :=
        (midpoint_add_self _ _ _).symm
      _ = f (midpoint R x y) + f (midpoint R x y) := by rw [← hm, midpoint_zero_a
-/
def ofMapMidpoint (f : E -> F) (h0 : f 0 = 0)
    (hm : forall x y, f (midpoint R x y) = midpoint R' (f x) (f y)) : E ->+ F where
  toFun := f
  map_zero' := h0
  map_add' x y :=
    calc
      f (x + y) = f 0 + f (x + y) := by rw [h0, zero_add]
      _ = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :=
        (midpoint_add_self _ _ _).symm
      _ = f (midpoint R x y) + f (midpoint R x y) := by rw [← hm, midpoint_zero_add]
      _ = f x + f y := by rw [hm, midpoint_add_self]

@[simp]
/--
theorem `coe_ofMapMidpoint` / 定理 `coe_ofMapMidpoint`

English:
theorem coe_ofMapMidpoint
  statement: (f : E -> F) (h0 : f 0 = 0)
  proof: rfl

中文:
定理 coe_ofMapMidpoint
  结论: (f : E -> F) (h0 : f 0 = 0)
  证明: rfl
-/
theorem coe_ofMapMidpoint (f : E -> F) (h0 : f 0 = 0)
    (hm : forall x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
    ⇑(ofMapMidpoint R R' f h0 hm) = f :=
  rfl

end AddMonoidHom
