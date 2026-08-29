/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Star structure on `CliffordAlgebra`

This file defines the "clifford conjugation", equal to `reverse (involute x)`, and assigns it the
`star` notation.

This choice is somewhat non-canonical; a star structure is also possible under `reverse` alone.
However, defining it gives us access to constructions like `unitary`.

Most results about `star` can be obtained by unfolding it via `CliffordAlgebra.star_def`.

## Main definitions

* `CliffordAlgebra.instStarRing`

-/

@[expose] public section


variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

/--
Instance `instStarRing` / 实例 `instStarRing`

English:
instance instStarRing
  signature: : StarRing (CliffordAlgebra Q) where
  body: reverse (involute x)
  star_involutive x := by
    simp only [reverse_involute_commute.eq, reverse_reverse, involute_involute]
  star_mul x y := by simp only [map_mul, reverse.map_mul]
  star_add x y := by simp only [map_add]

中文:
实例 instStarRing
  签名: : 对合环 (CliffordAlgebra Q) where
  定义体: reverse (involute x)
  star_involutive x := by
    simp only [reverse_involute_commute.eq, reverse_reverse, involute_involute]
  star_mul x y := by simp only [map_mul, reverse.map_mul]
  star_add x y := by simp only [map_add]

Depends on / 依赖: involute, reverse
-/
instance instStarRing : StarRing (CliffordAlgebra Q) where
  star x := reverse (involute x)
  star_involutive x := by
    simp only [reverse_involute_commute.eq, reverse_reverse, involute_involute]
  star_mul x y := by simp only [map_mul, reverse.map_mul]
  star_add x y := by simp only [map_add]

/--
theorem `star_def` / 定理 `star_def`

English:
theorem star_def
  given: (x : CliffordAlgebra Q)
  statement: star x = reverse (involute x)
  proof: rfl

中文:
定理 star_def
  条件: (x : CliffordAlgebra Q)
  结论: star x = reverse (involute x)
  证明: rfl
-/
theorem star_def (x : CliffordAlgebra Q) : star x = reverse (involute x) :=
  rfl

/--
theorem `star_def'` / 定理 `star_def'`

English:
theorem star_def'
  given: (x : CliffordAlgebra Q)
  statement: star x = involute (reverse x)
  proof: reverse_involute _

@[simp]

中文:
定理 star_def'
  条件: (x : CliffordAlgebra Q)
  结论: star x = involute (reverse x)
  证明: reverse_involute _

@[simp]

Depends on / 依赖: reverse_involute
-/
theorem star_def' (x : CliffordAlgebra Q) : star x = involute (reverse x) :=
  reverse_involute _

@[simp]
/--
theorem `star_ι` / 定理 `star_ι`

English:
theorem star_ι
  given: (m : M)
  statement: star (ι Q m) = -ι Q m
  proof: by rw [star_def, involute_ι, map_neg, reverse_ι]

中文:
定理 star_ι
  条件: (m : M)
  结论: star (ι Q m) = -ι Q m
  证明: by rw [star_def, involute_ι, map_neg, reverse_ι]

Depends on / 依赖: map_neg, star_def
-/
theorem star_ι (m : M) : star (ι Q m) = -ι Q m := by rw [star_def, involute_ι, map_neg, reverse_ι]

/-- Note that this not match the `star_smul` implied by `StarModule`; it certainly could if we
also conjugated all the scalars, but there appears to be nothing in the literature that advocates
doing this. -/
@[simp]
/--
theorem `star_smul` / 定理 `star_smul`

English:
theorem star_smul
  given: (r : R) (x : CliffordAlgebra Q)
  statement: star (r • x) = r • star x
  proof: by
  rw [star_def]; rw [star_def]; rw [map_smul]; rw [map_smul]

@[simp]

中文:
定理 star_smul
  条件: (r : R) (x : CliffordAlgebra Q)
  结论: star (r • x) = r • star x
  证明: by
  rw [star_def]; rw [star_def]; rw [map_smul]; rw [map_smul]

@[simp]

Depends on / 依赖: map_smul, star_def
-/
theorem star_smul (r : R) (x : CliffordAlgebra Q) : star (r • x) = r • star x := by
  rw [star_def]; rw [star_def]; rw [map_smul]; rw [map_smul]

@[simp]
/--
theorem `star_algebraMap` / 定理 `star_algebraMap`

English:
theorem star_algebraMap
  given: (r : R)
  proof: by
  rw [star_def]; rw [involute.commutes]; rw [reverse.commutes]

中文:
定理 star_algebraMap
  条件: (r : R)
  证明: by
  rw [star_def]; rw [involute.commutes]; rw [reverse.commutes]

Depends on / 依赖: commutes, involute, involute.commutes, reverse, reverse.commutes, star_def
-/
theorem star_algebraMap (r : R) :
    star (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (CliffordAlgebra Q) r := by
  rw [star_def]; rw [involute.commutes]; rw [reverse.commutes]

end CliffordAlgebra
