/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Indexed unions and intersections of pointwise operations of sets

This file contains lemmas on taking the union and intersection over pointwise algebraic operations
on sets.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

public section

assert_not_exists MulAction MonoidWithZero

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### Set negation/inversion -/

open scoped Pointwise

section Inv

variable {ι : Sort*} [Inv α]

@[to_additive (attr := simp)]
/--
theorem `iInter_inv` / 定理 `iInter_inv`

English:
theorem iInter_inv
  given: (s : ι -> Set α)
  statement: (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹
  proof: preimage_iInter

@[to_additive (attr := simp)]

中文:
定理 iInter_inv
  条件: (s : ι -> Set α)
  结论: (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹
  证明: preimage_iInter

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_iInter
-/
theorem iInter_inv (s : ι -> Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_iInter

@[to_additive (attr := simp)]
/--
theorem `sInter_inv` / 定理 `sInter_inv`

English:
theorem sInter_inv
  given: (S : Set (Set α))
  statement: (⋂₀ S)⁻¹ = ⋂ s in S, s⁻¹
  proof: preimage_sInter

@[to_additive (attr := simp)]

中文:
定理 sInter_inv
  条件: (S : Set (Set α))
  结论: (⋂₀ S)⁻¹ = ⋂ s in S, s⁻¹
  证明: preimage_sInter

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_sInter
-/
theorem sInter_inv (S : Set (Set α)) : (⋂₀ S)⁻¹ = ⋂ s in S, s⁻¹ :=
  preimage_sInter

@[to_additive (attr := simp)]
/--
theorem `iUnion_inv` / 定理 `iUnion_inv`

English:
theorem iUnion_inv
  given: (s : ι -> Set α)
  statement: (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹
  proof: preimage_iUnion

@[to_additive (attr := simp)]

中文:
定理 iUnion_inv
  条件: (s : ι -> Set α)
  结论: (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹
  证明: preimage_iUnion

@[to_additive (attr := simp)]

Depends on / 依赖: preimage_iUnion
-/
theorem iUnion_inv (s : ι -> Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_iUnion

@[to_additive (attr := simp)]
/--
theorem `sUnion_inv` / 定理 `sUnion_inv`

English:
theorem sUnion_inv
  given: (S : Set (Set α))
  statement: (⋃₀ S)⁻¹ = ⋃ s in S, s⁻¹
  proof: preimage_sUnion

中文:
定理 sUnion_inv
  条件: (S : Set (Set α))
  结论: (⋃₀ S)⁻¹ = ⋃ s in S, s⁻¹
  证明: preimage_sUnion

Depends on / 依赖: preimage_sUnion
-/
theorem sUnion_inv (S : Set (Set α)) : (⋃₀ S)⁻¹ = ⋃ s in S, s⁻¹ :=
  preimage_sUnion

end Inv

/-! ### Set addition/multiplication -/
section Mul

variable {ι : Sort*} {κ : ι -> Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

@[to_additive]
/--
theorem `iUnion_mul_left_image` / 定理 `iUnion_mul_left_image`

English:
theorem iUnion_mul_left_image
  statement: ⋃ a in s, (a * ·) '' t = s * t
  proof: iUnion_image_left _

@[to_additive]

中文:
定理 iUnion_mul_left_image
  结论: ⋃ a in s, (a * ·) '' t = s * t
  证明: iUnion_image_left _

@[to_additive]

Depends on / 依赖: iUnion_image_left
-/
theorem iUnion_mul_left_image : ⋃ a in s, (a * ·) '' t = s * t :=
  iUnion_image_left _

@[to_additive]
/--
theorem `iUnion_mul_right_image` / 定理 `iUnion_mul_right_image`

English:
theorem iUnion_mul_right_image
  statement: ⋃ a in t, (· * a) '' s = s * t
  proof: iUnion_image_right _

@[to_additive]

中文:
定理 iUnion_mul_right_image
  结论: ⋃ a in t, (· * a) '' s = s * t
  证明: iUnion_image_right _

@[to_additive]

Depends on / 依赖: iUnion_image_right
-/
theorem iUnion_mul_right_image : ⋃ a in t, (· * a) '' s = s * t :=
  iUnion_image_right _

@[to_additive]
/--
theorem `iUnion_mul` / 定理 `iUnion_mul`

English:
theorem iUnion_mul
  given: (s : ι -> Set α) (t : Set α)
  statement: (⋃ i, s i) * t = ⋃ i, s i * t
  proof: image2_iUnion_left ..

@[to_additive]

中文:
定理 iUnion_mul
  条件: (s : ι -> Set α) (t : Set α)
  结论: (⋃ i, s i) * t = ⋃ i, s i * t
  证明: image2_iUnion_left ..

@[to_additive]

Depends on / 依赖: image2_iUnion_left
-/
theorem iUnion_mul (s : ι -> Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_iUnion_left ..

@[to_additive]
/--
theorem `mul_iUnion` / 定理 `mul_iUnion`

English:
theorem mul_iUnion
  given: (s : Set α) (t : ι -> Set α)
  statement: (s * ⋃ i, t i) = ⋃ i, s * t i
  proof: image2_iUnion_right ..

@[to_additive]

中文:
定理 mul_iUnion
  条件: (s : Set α) (t : ι -> Set α)
  结论: (s * ⋃ i, t i) = ⋃ i, s * t i
  证明: image2_iUnion_right ..

@[to_additive]

Depends on / 依赖: image2_iUnion_right
-/
theorem mul_iUnion (s : Set α) (t : ι -> Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_iUnion_right ..

@[to_additive]
/--
theorem `sUnion_mul` / 定理 `sUnion_mul`

English:
theorem sUnion_mul
  given: (S : Set (Set α)) (t : Set α)
  statement: ⋃₀ S * t = ⋃ s in S, s * t
  proof: image2_sUnion_left ..

@[to_additive]

中文:
定理 sUnion_mul
  条件: (S : Set (Set α)) (t : Set α)
  结论: ⋃₀ S * t = ⋃ s in S, s * t
  证明: image2_sUnion_left ..

@[to_additive]

Depends on / 依赖: image2_sUnion_left
-/
theorem sUnion_mul (S : Set (Set α)) (t : Set α) : ⋃₀ S * t = ⋃ s in S, s * t :=
  image2_sUnion_left ..

@[to_additive]
/--
theorem `mul_sUnion` / 定理 `mul_sUnion`

English:
theorem mul_sUnion
  given: (s : Set α) (T : Set (Set α))
  statement: s * ⋃₀ T = ⋃ t in T, s * t
  proof: image2_sUnion_right ..

@[to_additive]

中文:
定理 mul_sUnion
  条件: (s : Set α) (T : Set (Set α))
  结论: s * ⋃₀ T = ⋃ t in T, s * t
  证明: image2_sUnion_right ..

@[to_additive]

Depends on / 依赖: image2_sUnion_right
-/
theorem mul_sUnion (s : Set α) (T : Set (Set α)) : s * ⋃₀ T = ⋃ t in T, s * t :=
  image2_sUnion_right ..

@[to_additive]
/--
theorem `iUnion₂_mul` / 定理 `iUnion₂_mul`

English:
theorem iUnion₂_mul
  given: (s : forall i, κ i -> Set α) (t : Set α)
  proof: image2_iUnion₂_left ..

@[to_additive]

中文:
定理 iUnion₂_mul
  条件: (s : 对任意 i, κ i -> Set α) (t : Set α)
  证明: image2_iUnion₂_left ..

@[to_additive]
-/
theorem iUnion₂_mul (s : forall i, κ i -> Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_iUnion₂_left ..

@[to_additive]
/--
theorem `mul_iUnion₂` / 定理 `mul_iUnion₂`

English:
theorem mul_iUnion₂
  given: (s : Set α) (t : forall i, κ i -> Set α)
  proof: image2_iUnion₂_right ..

@[to_additive]

中文:
定理 mul_iUnion₂
  条件: (s : Set α) (t : 对任意 i, κ i -> Set α)
  证明: image2_iUnion₂_right ..

@[to_additive]
-/
theorem mul_iUnion₂ (s : Set α) (t : forall i, κ i -> Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_iUnion₂_right ..

@[to_additive]
/--
theorem `iInter_mul_subset` / 定理 `iInter_mul_subset`

English:
theorem iInter_mul_subset
  given: (s : ι -> Set α) (t : Set α)
  statement: (⋂ i, s i) * t subseteq ⋂ i, s i * t
  proof: Set.image2_iInter_subset_left ..

@[to_additive]

中文:
定理 iInter_mul_subset
  条件: (s : ι -> Set α) (t : Set α)
  结论: (⋂ i, s i) * t subseteq ⋂ i, s i * t
  证明: Set.image2_iInter_subset_left ..

@[to_additive]

Depends on / 依赖: Set.image2_iInter_subset_left, image2_iInter_subset_left
-/
theorem iInter_mul_subset (s : ι -> Set α) (t : Set α) : (⋂ i, s i) * t subseteq ⋂ i, s i * t :=
  Set.image2_iInter_subset_left ..

@[to_additive]
/--
theorem `mul_iInter_subset` / 定理 `mul_iInter_subset`

English:
theorem mul_iInter_subset
  given: (s : Set α) (t : ι -> Set α)
  statement: (s * ⋂ i, t i) subseteq ⋂ i, s * t i
  proof: image2_iInter_subset_right ..

@[to_additive]

中文:
定理 mul_iInter_subset
  条件: (s : Set α) (t : ι -> Set α)
  结论: (s * ⋂ i, t i) subseteq ⋂ i, s * t i
  证明: image2_iInter_subset_right ..

@[to_additive]

Depends on / 依赖: image2_iInter_subset_right
-/
theorem mul_iInter_subset (s : Set α) (t : ι -> Set α) : (s * ⋂ i, t i) subseteq ⋂ i, s * t i :=
  image2_iInter_subset_right ..

@[to_additive]
/--
lemma `mul_sInter_subset` / 引理 `mul_sInter_subset`

English:
lemma mul_sInter_subset
  given: (s : Set α) (T : Set (Set α))
  proof: image2_sInter_right_subset s T (fun a b => a * b)

@[to_additive]

中文:
引理 mul_sInter_subset
  条件: (s : Set α) (T : Set (Set α))
  证明: image2_sInter_right_subset s T (fun a b => a * b)

@[to_additive]

Depends on / 依赖: image2_sInter_right_subset
-/
lemma mul_sInter_subset (s : Set α) (T : Set (Set α)) :
    s * ⋂₀ T subseteq ⋂ t in T, s * t := image2_sInter_right_subset s T (fun a b => a * b)

@[to_additive]
/--
lemma `sInter_mul_subset` / 引理 `sInter_mul_subset`

English:
lemma sInter_mul_subset
  given: (S : Set (Set α)) (t : Set α)
  proof: image2_sInter_left_subset S t (fun a b => a * b)

@[to_additive]

中文:
引理 sInter_mul_subset
  条件: (S : Set (Set α)) (t : Set α)
  证明: image2_sInter_left_subset S t (fun a b => a * b)

@[to_additive]

Depends on / 依赖: image2_sInter_left_subset
-/
lemma sInter_mul_subset (S : Set (Set α)) (t : Set α) :
    ⋂₀ S * t subseteq ⋂ s in S, s * t := image2_sInter_left_subset S t (fun a b => a * b)

@[to_additive]
/--
theorem `iInter₂_mul_subset` / 定理 `iInter₂_mul_subset`

English:
theorem iInter₂_mul_subset
  given: (s : forall i, κ i -> Set α) (t : Set α)
  proof: image2_iInter₂_subset_left ..

@[to_additive]

中文:
定理 iInter₂_mul_subset
  条件: (s : 对任意 i, κ i -> Set α) (t : Set α)
  证明: image2_iInter₂_subset_left ..

@[to_additive]
-/
theorem iInter₂_mul_subset (s : forall i, κ i -> Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t subseteq ⋂ (i) (j), s i j * t :=
  image2_iInter₂_subset_left ..

@[to_additive]
/--
theorem `mul_iInter₂_subset` / 定理 `mul_iInter₂_subset`

English:
theorem mul_iInter₂_subset
  given: (s : Set α) (t : forall i, κ i -> Set α)
  proof: image2_iInter₂_subset_right ..

中文:
定理 mul_iInter₂_subset
  条件: (s : Set α) (t : 对任意 i, κ i -> Set α)
  证明: image2_iInter₂_subset_right ..
-/
theorem mul_iInter₂_subset (s : Set α) (t : forall i, κ i -> Set α) :
    (s * ⋂ (i) (j), t i j) subseteq ⋂ (i) (j), s * t i j :=
  image2_iInter₂_subset_right ..

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort*} {κ : ι -> Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

@[to_additive]
/--
theorem `iUnion_div_left_image` / 定理 `iUnion_div_left_image`

English:
theorem iUnion_div_left_image
  statement: ⋃ a in s, (a / ·) '' t = s / t
  proof: iUnion_image_left _

@[to_additive]

中文:
定理 iUnion_div_left_image
  结论: ⋃ a in s, (a / ·) '' t = s / t
  证明: iUnion_image_left _

@[to_additive]

Depends on / 依赖: iUnion_image_left
-/
theorem iUnion_div_left_image : ⋃ a in s, (a / ·) '' t = s / t :=
  iUnion_image_left _

@[to_additive]
/--
theorem `iUnion_div_right_image` / 定理 `iUnion_div_right_image`

English:
theorem iUnion_div_right_image
  statement: ⋃ a in t, (· / a) '' s = s / t
  proof: iUnion_image_right _

@[to_additive]

中文:
定理 iUnion_div_right_image
  结论: ⋃ a in t, (· / a) '' s = s / t
  证明: iUnion_image_right _

@[to_additive]

Depends on / 依赖: iUnion_image_right
-/
theorem iUnion_div_right_image : ⋃ a in t, (· / a) '' s = s / t :=
  iUnion_image_right _

@[to_additive]
/--
theorem `iUnion_div` / 定理 `iUnion_div`

English:
theorem iUnion_div
  given: (s : ι -> Set α) (t : Set α)
  statement: (⋃ i, s i) / t = ⋃ i, s i / t
  proof: image2_iUnion_left ..

@[to_additive]

中文:
定理 iUnion_div
  条件: (s : ι -> Set α) (t : Set α)
  结论: (⋃ i, s i) / t = ⋃ i, s i / t
  证明: image2_iUnion_left ..

@[to_additive]

Depends on / 依赖: image2_iUnion_left
-/
theorem iUnion_div (s : ι -> Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_iUnion_left ..

@[to_additive]
/--
theorem `div_iUnion` / 定理 `div_iUnion`

English:
theorem div_iUnion
  given: (s : Set α) (t : ι -> Set α)
  statement: (s / ⋃ i, t i) = ⋃ i, s / t i
  proof: image2_iUnion_right ..

@[to_additive]

中文:
定理 div_iUnion
  条件: (s : Set α) (t : ι -> Set α)
  结论: (s / ⋃ i, t i) = ⋃ i, s / t i
  证明: image2_iUnion_right ..

@[to_additive]

Depends on / 依赖: image2_iUnion_right
-/
theorem div_iUnion (s : Set α) (t : ι -> Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_iUnion_right ..

@[to_additive]
/--
theorem `sUnion_div` / 定理 `sUnion_div`

English:
theorem sUnion_div
  given: (S : Set (Set α)) (t : Set α)
  statement: ⋃₀ S / t = ⋃ s in S, s / t
  proof: image2_sUnion_left ..

@[to_additive]

中文:
定理 sUnion_div
  条件: (S : Set (Set α)) (t : Set α)
  结论: ⋃₀ S / t = ⋃ s in S, s / t
  证明: image2_sUnion_left ..

@[to_additive]

Depends on / 依赖: image2_sUnion_left
-/
theorem sUnion_div (S : Set (Set α)) (t : Set α) : ⋃₀ S / t = ⋃ s in S, s / t :=
  image2_sUnion_left ..

@[to_additive]
/--
theorem `div_sUnion` / 定理 `div_sUnion`

English:
theorem div_sUnion
  given: (s : Set α) (T : Set (Set α))
  statement: s / ⋃₀ T = ⋃ t in T, s / t
  proof: image2_sUnion_right ..

@[to_additive]

中文:
定理 div_sUnion
  条件: (s : Set α) (T : Set (Set α))
  结论: s / ⋃₀ T = ⋃ t in T, s / t
  证明: image2_sUnion_right ..

@[to_additive]

Depends on / 依赖: image2_sUnion_right
-/
theorem div_sUnion (s : Set α) (T : Set (Set α)) : s / ⋃₀ T = ⋃ t in T, s / t :=
  image2_sUnion_right ..

@[to_additive]
/--
theorem `iUnion₂_div` / 定理 `iUnion₂_div`

English:
theorem iUnion₂_div
  given: (s : forall i, κ i -> Set α) (t : Set α)
  proof: image2_iUnion₂_left ..

@[to_additive]

中文:
定理 iUnion₂_div
  条件: (s : 对任意 i, κ i -> Set α) (t : Set α)
  证明: image2_iUnion₂_left ..

@[to_additive]
-/
theorem iUnion₂_div (s : forall i, κ i -> Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_iUnion₂_left ..

@[to_additive]
/--
theorem `div_iUnion₂` / 定理 `div_iUnion₂`

English:
theorem div_iUnion₂
  given: (s : Set α) (t : forall i, κ i -> Set α)
  proof: image2_iUnion₂_right ..

@[to_additive]

中文:
定理 div_iUnion₂
  条件: (s : Set α) (t : 对任意 i, κ i -> Set α)
  证明: image2_iUnion₂_right ..

@[to_additive]
-/
theorem div_iUnion₂ (s : Set α) (t : forall i, κ i -> Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_iUnion₂_right ..

@[to_additive]
/--
theorem `iInter_div_subset` / 定理 `iInter_div_subset`

English:
theorem iInter_div_subset
  given: (s : ι -> Set α) (t : Set α)
  statement: (⋂ i, s i) / t subseteq ⋂ i, s i / t
  proof: image2_iInter_subset_left ..

@[to_additive]

中文:
定理 iInter_div_subset
  条件: (s : ι -> Set α) (t : Set α)
  结论: (⋂ i, s i) / t subseteq ⋂ i, s i / t
  证明: image2_iInter_subset_left ..

@[to_additive]

Depends on / 依赖: image2_iInter_subset_left
-/
theorem iInter_div_subset (s : ι -> Set α) (t : Set α) : (⋂ i, s i) / t subseteq ⋂ i, s i / t :=
  image2_iInter_subset_left ..

@[to_additive]
/--
theorem `div_iInter_subset` / 定理 `div_iInter_subset`

English:
theorem div_iInter_subset
  given: (s : Set α) (t : ι -> Set α)
  statement: (s / ⋂ i, t i) subseteq ⋂ i, s / t i
  proof: image2_iInter_subset_right ..

@[to_additive]

中文:
定理 div_iInter_subset
  条件: (s : Set α) (t : ι -> Set α)
  结论: (s / ⋂ i, t i) subseteq ⋂ i, s / t i
  证明: image2_iInter_subset_right ..

@[to_additive]

Depends on / 依赖: image2_iInter_subset_right
-/
theorem div_iInter_subset (s : Set α) (t : ι -> Set α) : (s / ⋂ i, t i) subseteq ⋂ i, s / t i :=
  image2_iInter_subset_right ..

@[to_additive]
/--
theorem `sInter_div_subset` / 定理 `sInter_div_subset`

English:
theorem sInter_div_subset
  given: (S : Set (Set α)) (t : Set α)
  statement: ⋂₀ S / t subseteq ⋂ s in S, s / t
  proof: image2_sInter_subset_left ..

@[to_additive]

中文:
定理 sInter_div_subset
  条件: (S : Set (Set α)) (t : Set α)
  结论: ⋂₀ S / t subseteq ⋂ s in S, s / t
  证明: image2_sInter_subset_left ..

@[to_additive]

Depends on / 依赖: image2_sInter_subset_left
-/
theorem sInter_div_subset (S : Set (Set α)) (t : Set α) : ⋂₀ S / t subseteq ⋂ s in S, s / t :=
  image2_sInter_subset_left ..

@[to_additive]
/--
theorem `div_sInter_subset` / 定理 `div_sInter_subset`

English:
theorem div_sInter_subset
  given: (s : Set α) (T : Set (Set α))
  statement: s / ⋂₀ T subseteq ⋂ t in T, s / t
  proof: image2_sInter_subset_right ..

@[to_additive]

中文:
定理 div_sInter_subset
  条件: (s : Set α) (T : Set (Set α))
  结论: s / ⋂₀ T subseteq ⋂ t in T, s / t
  证明: image2_sInter_subset_right ..

@[to_additive]

Depends on / 依赖: image2_sInter_subset_right
-/
theorem div_sInter_subset (s : Set α) (T : Set (Set α)) : s / ⋂₀ T subseteq ⋂ t in T, s / t :=
  image2_sInter_subset_right ..

@[to_additive]
/--
theorem `iInter₂_div_subset` / 定理 `iInter₂_div_subset`

English:
theorem iInter₂_div_subset
  given: (s : forall i, κ i -> Set α) (t : Set α)
  proof: image2_iInter₂_subset_left ..

@[to_additive]

中文:
定理 iInter₂_div_subset
  条件: (s : 对任意 i, κ i -> Set α) (t : Set α)
  证明: image2_iInter₂_subset_left ..

@[to_additive]
-/
theorem iInter₂_div_subset (s : forall i, κ i -> Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t subseteq ⋂ (i) (j), s i j / t :=
  image2_iInter₂_subset_left ..

@[to_additive]
/--
theorem `div_iInter₂_subset` / 定理 `div_iInter₂_subset`

English:
theorem div_iInter₂_subset
  given: (s : Set α) (t : forall i, κ i -> Set α)
  proof: image2_iInter₂_subset_right ..

中文:
定理 div_iInter₂_subset
  条件: (s : Set α) (t : 对任意 i, κ i -> Set α)
  证明: image2_iInter₂_subset_right ..
-/
theorem div_iInter₂_subset (s : Set α) (t : forall i, κ i -> Set α) :
    (s / ⋂ (i) (j), t i j) subseteq ⋂ (i) (j), s / t i j :=
  image2_iInter₂_subset_right ..

end Div

/-! ### Translation/scaling of sets -/

section SMul

variable {ι : Sort*} {κ : ι -> Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

/--
lemma `iUnion_smul_left_image` / 引理 `iUnion_smul_left_image`

English:
lemma iUnion_smul_left_image
  statement: ⋃ a in s, a • t = s • t
  proof: iUnion_image_left _

@[to_additive]

中文:
引理 iUnion_smul_left_image
  结论: ⋃ a in s, a • t = s • t
  证明: iUnion_image_left _

@[to_additive]
-/
@[to_additive] lemma iUnion_smul_left_image : ⋃ a in s, a • t = s • t := iUnion_image_left _

@[to_additive]
/--
lemma `iUnion_smul_right_image` / 引理 `iUnion_smul_right_image`

English:
lemma iUnion_smul_right_image
  statement: ⋃ a in t, (· • a) '' s = s • t
  proof: iUnion_image_right _

@[to_additive]

中文:
引理 iUnion_smul_right_image
  结论: ⋃ a in t, (· • a) '' s = s • t
  证明: iUnion_image_right _

@[to_additive]

Depends on / 依赖: iUnion_image_right
-/
lemma iUnion_smul_right_image : ⋃ a in t, (· • a) '' s = s • t := iUnion_image_right _

@[to_additive]
/--
lemma `iUnion_smul` / 引理 `iUnion_smul`

English:
lemma iUnion_smul
  given: (s : ι -> Set α) (t : Set β)
  statement: (⋃ i, s i) • t = ⋃ i, s i • t
  proof: image2_iUnion_left ..

@[to_additive]

中文:
引理 iUnion_smul
  条件: (s : ι -> Set α) (t : Set β)
  结论: (⋃ i, s i) • t = ⋃ i, s i • t
  证明: image2_iUnion_left ..

@[to_additive]

Depends on / 依赖: image2_iUnion_left
-/
lemma iUnion_smul (s : ι -> Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_iUnion_left ..

@[to_additive]
/--
lemma `smul_iUnion` / 引理 `smul_iUnion`

English:
lemma smul_iUnion
  given: (s : Set α) (t : ι -> Set β)
  statement: (s • ⋃ i, t i) = ⋃ i, s • t i
  proof: image2_iUnion_right ..

@[to_additive]

中文:
引理 smul_iUnion
  条件: (s : Set α) (t : ι -> Set β)
  结论: (s • ⋃ i, t i) = ⋃ i, s • t i
  证明: image2_iUnion_right ..

@[to_additive]

Depends on / 依赖: image2_iUnion_right
-/
lemma smul_iUnion (s : Set α) (t : ι -> Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_iUnion_right ..

@[to_additive]
/--
lemma `sUnion_smul` / 引理 `sUnion_smul`

English:
lemma sUnion_smul
  given: (S : Set (Set α)) (t : Set β)
  statement: ⋃₀ S • t = ⋃ s in S, s • t
  proof: image2_sUnion_left ..

@[to_additive]

中文:
引理 sUnion_smul
  条件: (S : Set (Set α)) (t : Set β)
  结论: ⋃₀ S • t = ⋃ s in S, s • t
  证明: image2_sUnion_left ..

@[to_additive]

Depends on / 依赖: image2_sUnion_left
-/
lemma sUnion_smul (S : Set (Set α)) (t : Set β) : ⋃₀ S • t = ⋃ s in S, s • t :=
  image2_sUnion_left ..

@[to_additive]
/--
lemma `smul_sUnion` / 引理 `smul_sUnion`

English:
lemma smul_sUnion
  given: (s : Set α) (T : Set (Set β))
  statement: s • ⋃₀ T = ⋃ t in T, s • t
  proof: image2_sUnion_right ..

@[to_additive]

中文:
引理 smul_sUnion
  条件: (s : Set α) (T : Set (Set β))
  结论: s • ⋃₀ T = ⋃ t in T, s • t
  证明: image2_sUnion_right ..

@[to_additive]

Depends on / 依赖: image2_sUnion_right
-/
lemma smul_sUnion (s : Set α) (T : Set (Set β)) : s • ⋃₀ T = ⋃ t in T, s • t :=
  image2_sUnion_right ..

@[to_additive]
/--
lemma `iUnion₂_smul` / 引理 `iUnion₂_smul`

English:
lemma iUnion₂_smul
  given: (s : forall i, κ i -> Set α) (t : Set β)
  proof: image2_iUnion₂_left ..

@[to_additive]

中文:
引理 iUnion₂_smul
  条件: (s : 对任意 i, κ i -> Set α) (t : Set β)
  证明: image2_iUnion₂_left ..

@[to_additive]
-/
lemma iUnion₂_smul (s : forall i, κ i -> Set α) (t : Set β) :
    (⋃ i, ⋃ j, s i j) • t = ⋃ i, ⋃ j, s i j • t := image2_iUnion₂_left ..

@[to_additive]
/--
lemma `smul_iUnion₂` / 引理 `smul_iUnion₂`

English:
lemma smul_iUnion₂
  given: (s : Set α) (t : forall i, κ i -> Set β)
  proof: image2_iUnion₂_right ..

@[to_additive]

中文:
引理 smul_iUnion₂
  条件: (s : Set α) (t : 对任意 i, κ i -> Set β)
  证明: image2_iUnion₂_right ..

@[to_additive]
-/
lemma smul_iUnion₂ (s : Set α) (t : forall i, κ i -> Set β) :
    (s • ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s • t i j := image2_iUnion₂_right ..

@[to_additive]
/--
lemma `iInter_smul_subset` / 引理 `iInter_smul_subset`

English:
lemma iInter_smul_subset
  given: (s : ι -> Set α) (t : Set β)
  statement: (⋂ i, s i) • t subseteq ⋂ i, s i • t
  proof: image2_iInter_subset_left ..

@[to_additive]

中文:
引理 iInter_smul_subset
  条件: (s : ι -> Set α) (t : Set β)
  结论: (⋂ i, s i) • t subseteq ⋂ i, s i • t
  证明: image2_iInter_subset_left ..

@[to_additive]

Depends on / 依赖: image2_iInter_subset_left
-/
lemma iInter_smul_subset (s : ι -> Set α) (t : Set β) : (⋂ i, s i) • t subseteq ⋂ i, s i • t :=
  image2_iInter_subset_left ..

@[to_additive]
/--
lemma `smul_iInter_subset` / 引理 `smul_iInter_subset`

English:
lemma smul_iInter_subset
  given: (s : Set α) (t : ι -> Set β)
  statement: (s • ⋂ i, t i) subseteq ⋂ i, s • t i
  proof: image2_iInter_subset_right ..

@[to_additive]

中文:
引理 smul_iInter_subset
  条件: (s : Set α) (t : ι -> Set β)
  结论: (s • ⋂ i, t i) subseteq ⋂ i, s • t i
  证明: image2_iInter_subset_right ..

@[to_additive]

Depends on / 依赖: image2_iInter_subset_right
-/
lemma smul_iInter_subset (s : Set α) (t : ι -> Set β) : (s • ⋂ i, t i) subseteq ⋂ i, s • t i :=
  image2_iInter_subset_right ..

@[to_additive]
/--
lemma `sInter_smul_subset` / 引理 `sInter_smul_subset`

English:
lemma sInter_smul_subset
  given: (S : Set (Set α)) (t : Set β)
  statement: ⋂₀ S • t subseteq ⋂ s in S, s • t
  proof: image2_sInter_left_subset S t (fun a x => a • x)

@[to_additive]

中文:
引理 sInter_smul_subset
  条件: (S : Set (Set α)) (t : Set β)
  结论: ⋂₀ S • t subseteq ⋂ s in S, s • t
  证明: image2_sInter_left_subset S t (fun a x => a • x)

@[to_additive]

Depends on / 依赖: image2_sInter_left_subset
-/
lemma sInter_smul_subset (S : Set (Set α)) (t : Set β) : ⋂₀ S • t subseteq ⋂ s in S, s • t :=
  image2_sInter_left_subset S t (fun a x => a • x)

@[to_additive]
/--
lemma `smul_sInter_subset` / 引理 `smul_sInter_subset`

English:
lemma smul_sInter_subset
  given: (s : Set α) (T : Set (Set β))
  statement: s • ⋂₀ T subseteq ⋂ t in T, s • t
  proof: image2_sInter_right_subset s T (fun a x => a • x)

@[to_additive]

中文:
引理 smul_sInter_subset
  条件: (s : Set α) (T : Set (Set β))
  结论: s • ⋂₀ T subseteq ⋂ t in T, s • t
  证明: image2_sInter_right_subset s T (fun a x => a • x)

@[to_additive]

Depends on / 依赖: image2_sInter_right_subset
-/
lemma smul_sInter_subset (s : Set α) (T : Set (Set β)) : s • ⋂₀ T subseteq ⋂ t in T, s • t :=
  image2_sInter_right_subset s T (fun a x => a • x)

@[to_additive]
/--
lemma `iInter₂_smul_subset` / 引理 `iInter₂_smul_subset`

English:
lemma iInter₂_smul_subset
  given: (s : forall i, κ i -> Set α) (t : Set β)
  proof: image2_iInter₂_subset_left ..

@[to_additive]

中文:
引理 iInter₂_smul_subset
  条件: (s : 对任意 i, κ i -> Set α) (t : Set β)
  证明: image2_iInter₂_subset_left ..

@[to_additive]
-/
lemma iInter₂_smul_subset (s : forall i, κ i -> Set α) (t : Set β) :
    (⋂ i, ⋂ j, s i j) • t subseteq ⋂ i, ⋂ j, s i j • t := image2_iInter₂_subset_left ..

@[to_additive]
/--
lemma `smul_iInter₂_subset` / 引理 `smul_iInter₂_subset`

English:
lemma smul_iInter₂_subset
  given: (s : Set α) (t : forall i, κ i -> Set β)
  proof: image2_iInter₂_subset_right ..

@[to_additive (attr := simp)]

中文:
引理 smul_iInter₂_subset
  条件: (s : Set α) (t : 对任意 i, κ i -> Set β)
  证明: image2_iInter₂_subset_right ..

@[to_additive (attr := simp)]
-/
lemma smul_iInter₂_subset (s : Set α) (t : forall i, κ i -> Set β) :
    (s • ⋂ i, ⋂ j, t i j) subseteq ⋂ i, ⋂ j, s • t i j := image2_iInter₂_subset_right ..

@[to_additive (attr := simp)]
/--
lemma `iUnion_smul_set` / 引理 `iUnion_smul_set`

English:
lemma iUnion_smul_set
  given: (s : Set α) (t : Set β)
  statement: ⋃ a in s, a • t = s • t
  proof: iUnion_image_left _

中文:
引理 iUnion_smul_set
  条件: (s : Set α) (t : Set β)
  结论: ⋃ a in s, a • t = s • t
  证明: iUnion_image_left _

Depends on / 依赖: iUnion_image_left
-/
lemma iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a in s, a • t = s • t := iUnion_image_left _

end SMul

section SMulSet
variable {ι : Sort*} {κ : ι -> Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[to_additive]
/--
lemma `smul_set_iUnion` / 引理 `smul_set_iUnion`

English:
lemma smul_set_iUnion
  given: (a : α) (s : ι -> Set β)
  statement: a • ⋃ i, s i = ⋃ i, a • s i
  proof: image_iUnion

@[to_additive]

中文:
引理 smul_set_iUnion
  条件: (a : α) (s : ι -> Set β)
  结论: a • ⋃ i, s i = ⋃ i, a • s i
  证明: image_iUnion

@[to_additive]

Depends on / 依赖: image_iUnion
-/
lemma smul_set_iUnion (a : α) (s : ι -> Set β) : a • ⋃ i, s i = ⋃ i, a • s i :=
  image_iUnion

@[to_additive]
/--
lemma `smul_set_iUnion₂` / 引理 `smul_set_iUnion₂`

English:
lemma smul_set_iUnion₂
  given: (a : α) (s : forall i, κ i -> Set β)
  proof: image_iUnion₂ ..

@[to_additive]

中文:
引理 smul_set_iUnion₂
  条件: (a : α) (s : 对任意 i, κ i -> Set β)
  证明: image_iUnion₂ ..

@[to_additive]
-/
lemma smul_set_iUnion₂ (a : α) (s : forall i, κ i -> Set β) :
    a • ⋃ i, ⋃ j, s i j = ⋃ i, ⋃ j, a • s i j := image_iUnion₂ ..

@[to_additive]
/--
lemma `smul_set_sUnion` / 引理 `smul_set_sUnion`

English:
lemma smul_set_sUnion
  given: (a : α) (S : Set (Set β))
  statement: a • ⋃₀ S = ⋃ s in S, a • s
  proof: by
  rw [sUnion_eq_biUnion]; rw [smul_set_iUnion₂]

@[to_additive]

中文:
引理 smul_set_sUnion
  条件: (a : α) (S : Set (Set β))
  结论: a • ⋃₀ S = ⋃ s in S, a • s
  证明: by
  rw [sUnion_eq_biUnion]; rw [smul_set_iUnion₂]

@[to_additive]

Depends on / 依赖: sUnion_eq_biUnion
-/
lemma smul_set_sUnion (a : α) (S : Set (Set β)) : a • ⋃₀ S = ⋃ s in S, a • s := by
  rw [sUnion_eq_biUnion]; rw [smul_set_iUnion₂]

@[to_additive]
/--
lemma `smul_set_iInter_subset` / 引理 `smul_set_iInter_subset`

English:
lemma smul_set_iInter_subset
  given: (a : α) (t : ι -> Set β)
  statement: a • ⋂ i, t i subseteq ⋂ i, a • t i
  proof: image_iInter_subset ..

@[to_additive]

中文:
引理 smul_set_iInter_subset
  条件: (a : α) (t : ι -> Set β)
  结论: a • ⋂ i, t i subseteq ⋂ i, a • t i
  证明: image_iInter_subset ..

@[to_additive]

Depends on / 依赖: image_iInter_subset
-/
lemma smul_set_iInter_subset (a : α) (t : ι -> Set β) : a • ⋂ i, t i subseteq ⋂ i, a • t i :=
  image_iInter_subset ..

@[to_additive]
/--
lemma `smul_set_sInter_subset` / 引理 `smul_set_sInter_subset`

English:
lemma smul_set_sInter_subset
  given: (a : α) (S : Set (Set β))
  proof: image_sInter_subset ..

@[to_additive]

中文:
引理 smul_set_sInter_subset
  条件: (a : α) (S : Set (Set β))
  证明: image_sInter_subset ..

@[to_additive]

Depends on / 依赖: image_sInter_subset
-/
lemma smul_set_sInter_subset (a : α) (S : Set (Set β)) :
    a • ⋂₀ S subseteq ⋂ s in S, a • s := image_sInter_subset ..

@[to_additive]
/--
lemma `smul_set_iInter₂_subset` / 引理 `smul_set_iInter₂_subset`

English:
lemma smul_set_iInter₂_subset
  given: (a : α) (t : forall i, κ i -> Set β)
  proof: image_iInter₂_subset ..

中文:
引理 smul_set_iInter₂_subset
  条件: (a : α) (t : 对任意 i, κ i -> Set β)
  证明: image_iInter₂_subset ..
-/
lemma smul_set_iInter₂_subset (a : α) (t : forall i, κ i -> Set β) :
    a • ⋂ i, ⋂ j, t i j subseteq ⋂ i, ⋂ j, a • t i j := image_iInter₂_subset ..

end SMulSet
variable {s : Set α} {t : Set β} {a : α} {b : β}

section VSub
variable {ι : Sort*} {κ : ι -> Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

/--
lemma `iUnion_vsub_left_image` / 引理 `iUnion_vsub_left_image`

English:
lemma iUnion_vsub_left_image
  statement: ⋃ a in s, (a -ᵥ ·) '' t = s -ᵥ t
  proof: iUnion_image_left _

中文:
引理 iUnion_vsub_left_image
  结论: ⋃ a in s, (a -ᵥ ·) '' t = s -ᵥ t
  证明: iUnion_image_left _

Depends on / 依赖: iUnion_image_left
-/
lemma iUnion_vsub_left_image : ⋃ a in s, (a -ᵥ ·) '' t = s -ᵥ t := iUnion_image_left _
/--
lemma `iUnion_vsub_right_image` / 引理 `iUnion_vsub_right_image`

English:
lemma iUnion_vsub_right_image
  statement: ⋃ a in t, (· -ᵥ a) '' s = s -ᵥ t
  proof: iUnion_image_right _

中文:
引理 iUnion_vsub_right_image
  结论: ⋃ a in t, (· -ᵥ a) '' s = s -ᵥ t
  证明: iUnion_image_right _

Depends on / 依赖: iUnion_image_right
-/
lemma iUnion_vsub_right_image : ⋃ a in t, (· -ᵥ a) '' s = s -ᵥ t := iUnion_image_right _

/--
lemma `iUnion_vsub` / 引理 `iUnion_vsub`

English:
lemma iUnion_vsub
  given: (s : ι -> Set β) (t : Set β)
  statement: (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t
  proof: image2_iUnion_left ..

中文:
引理 iUnion_vsub
  条件: (s : ι -> Set β) (t : Set β)
  结论: (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t
  证明: image2_iUnion_left ..

Depends on / 依赖: image2_iUnion_left
-/
lemma iUnion_vsub (s : ι -> Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_iUnion_left ..

/--
lemma `vsub_iUnion` / 引理 `vsub_iUnion`

English:
lemma vsub_iUnion
  given: (s : Set β) (t : ι -> Set β)
  statement: (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i
  proof: image2_iUnion_right ..

中文:
引理 vsub_iUnion
  条件: (s : Set β) (t : ι -> Set β)
  结论: (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i
  证明: image2_iUnion_right ..

Depends on / 依赖: image2_iUnion_right
-/
lemma vsub_iUnion (s : Set β) (t : ι -> Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_iUnion_right ..

/--
lemma `sUnion_vsub` / 引理 `sUnion_vsub`

English:
lemma sUnion_vsub
  given: (S : Set (Set β)) (t : Set β)
  statement: ⋃₀ S -ᵥ t = ⋃ s in S, s -ᵥ t
  proof: image2_sUnion_left ..

中文:
引理 sUnion_vsub
  条件: (S : Set (Set β)) (t : Set β)
  结论: ⋃₀ S -ᵥ t = ⋃ s in S, s -ᵥ t
  证明: image2_sUnion_left ..

Depends on / 依赖: image2_sUnion_left
-/
lemma sUnion_vsub (S : Set (Set β)) (t : Set β) : ⋃₀ S -ᵥ t = ⋃ s in S, s -ᵥ t :=
  image2_sUnion_left ..

/--
lemma `vsub_sUnion` / 引理 `vsub_sUnion`

English:
lemma vsub_sUnion
  given: (s : Set β) (T : Set (Set β))
  statement: s -ᵥ ⋃₀ T = ⋃ t in T, s -ᵥ t
  proof: image2_sUnion_right ..

中文:
引理 vsub_sUnion
  条件: (s : Set β) (T : Set (Set β))
  结论: s -ᵥ ⋃₀ T = ⋃ t in T, s -ᵥ t
  证明: image2_sUnion_right ..

Depends on / 依赖: image2_sUnion_right
-/
lemma vsub_sUnion (s : Set β) (T : Set (Set β)) : s -ᵥ ⋃₀ T = ⋃ t in T, s -ᵥ t :=
  image2_sUnion_right ..

/--
lemma `iUnion₂_vsub` / 引理 `iUnion₂_vsub`

English:
lemma iUnion₂_vsub
  given: (s : forall i, κ i -> Set β) (t : Set β)
  proof: image2_iUnion₂_left ..

中文:
引理 iUnion₂_vsub
  条件: (s : 对任意 i, κ i -> Set β) (t : Set β)
  证明: image2_iUnion₂_left ..
-/
lemma iUnion₂_vsub (s : forall i, κ i -> Set β) (t : Set β) :
    (⋃ i, ⋃ j, s i j) -ᵥ t = ⋃ i, ⋃ j, s i j -ᵥ t := image2_iUnion₂_left ..

/--
lemma `vsub_iUnion₂` / 引理 `vsub_iUnion₂`

English:
lemma vsub_iUnion₂
  given: (s : Set β) (t : forall i, κ i -> Set β)
  proof: image2_iUnion₂_right ..

中文:
引理 vsub_iUnion₂
  条件: (s : Set β) (t : 对任意 i, κ i -> Set β)
  证明: image2_iUnion₂_right ..
-/
lemma vsub_iUnion₂ (s : Set β) (t : forall i, κ i -> Set β) :
    (s -ᵥ ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s -ᵥ t i j := image2_iUnion₂_right ..

/--
lemma `iInter_vsub_subset` / 引理 `iInter_vsub_subset`

English:
lemma iInter_vsub_subset
  given: (s : ι -> Set β) (t : Set β)
  statement: (⋂ i, s i) -ᵥ t subseteq ⋂ i, s i -ᵥ t
  proof: image2_iInter_subset_left ..

中文:
引理 iInter_vsub_subset
  条件: (s : ι -> Set β) (t : Set β)
  结论: (⋂ i, s i) -ᵥ t subseteq ⋂ i, s i -ᵥ t
  证明: image2_iInter_subset_left ..

Depends on / 依赖: AddSubgroup, AddSubgroup.closure_le, AddSubgroup.subset_closure, Multiplicative, Subgroup, Subgroup.subset_closure, closure_le, image2_iInter_subset_left, l_le, le_antisymm, subset_closure, toAddSubgroup, to_galoisConnection, to_galoisConnection.l_le
-/
lemma iInter_vsub_subset (s : ι -> Set β) (t : Set β) : (⋂ i, s i) -ᵥ t subseteq ⋂ i, s i -ᵥ t :=
  image2_iInter_subset_left ..

/--
lemma `vsub_iInter_subset` / 引理 `vsub_iInter_subset`

English:
lemma vsub_iInter_subset
  given: (s : Set β) (t : ι -> Set β)
  statement: (s -ᵥ ⋂ i, t i) subseteq ⋂ i, s -ᵥ t i
  proof: image2_iInter_subset_right ..

中文:
引理 vsub_iInter_subset
  条件: (s : Set β) (t : ι -> Set β)
  结论: (s -ᵥ ⋂ i, t i) subseteq ⋂ i, s -ᵥ t i
  证明: image2_iInter_subset_right ..

Depends on / 依赖: image2_iInter_subset_right
-/
lemma vsub_iInter_subset (s : Set β) (t : ι -> Set β) : (s -ᵥ ⋂ i, t i) subseteq ⋂ i, s -ᵥ t i :=
  image2_iInter_subset_right ..

/--
lemma `sInter_vsub_subset` / 引理 `sInter_vsub_subset`

English:
lemma sInter_vsub_subset
  given: (S : Set (Set β)) (t : Set β)
  statement: ⋂₀ S -ᵥ t subseteq ⋂ s in S, s -ᵥ t
  proof: image2_sInter_subset_left ..

中文:
引理 sInter_vsub_subset
  条件: (S : Set (Set β)) (t : Set β)
  结论: ⋂₀ S -ᵥ t subseteq ⋂ s in S, s -ᵥ t
  证明: image2_sInter_subset_left ..

Depends on / 依赖: image2_sInter_subset_left
-/
lemma sInter_vsub_subset (S : Set (Set β)) (t : Set β) : ⋂₀ S -ᵥ t subseteq ⋂ s in S, s -ᵥ t :=
  image2_sInter_subset_left ..

/--
lemma `vsub_sInter_subset` / 引理 `vsub_sInter_subset`

English:
lemma vsub_sInter_subset
  given: (s : Set β) (T : Set (Set β))
  statement: s -ᵥ ⋂₀ T subseteq ⋂ t in T, s -ᵥ t
  proof: image2_sInter_subset_right ..

中文:
引理 vsub_sInter_subset
  条件: (s : Set β) (T : Set (Set β))
  结论: s -ᵥ ⋂₀ T subseteq ⋂ t in T, s -ᵥ t
  证明: image2_sInter_subset_right ..

Depends on / 依赖: image2_sInter_subset_right
-/
lemma vsub_sInter_subset (s : Set β) (T : Set (Set β)) : s -ᵥ ⋂₀ T subseteq ⋂ t in T, s -ᵥ t :=
  image2_sInter_subset_right ..

/--
lemma `iInter₂_vsub_subset` / 引理 `iInter₂_vsub_subset`

English:
lemma iInter₂_vsub_subset
  given: (s : forall i, κ i -> Set β) (t : Set β)
  proof: image2_iInter₂_subset_left ..

中文:
引理 iInter₂_vsub_subset
  条件: (s : 对任意 i, κ i -> Set β) (t : Set β)
  证明: image2_iInter₂_subset_left ..
-/
lemma iInter₂_vsub_subset (s : forall i, κ i -> Set β) (t : Set β) :
    (⋂ i, ⋂ j, s i j) -ᵥ t subseteq ⋂ i, ⋂ j, s i j -ᵥ t := image2_iInter₂_subset_left ..

/--
lemma `vsub_iInter₂_subset` / 引理 `vsub_iInter₂_subset`

English:
lemma vsub_iInter₂_subset
  given: (s : Set β) (t : forall i, κ i -> Set β)
  proof: image2_iInter₂_subset_right ..

中文:
引理 vsub_iInter₂_subset
  条件: (s : Set β) (t : 对任意 i, κ i -> Set β)
  证明: image2_iInter₂_subset_right ..
-/
lemma vsub_iInter₂_subset (s : Set β) (t : forall i, κ i -> Set β) :
    s -ᵥ ⋂ i, ⋂ j, t i j subseteq ⋂ i, ⋂ j, s -ᵥ t i j := image2_iInter₂_subset_right ..

end VSub

end Set
