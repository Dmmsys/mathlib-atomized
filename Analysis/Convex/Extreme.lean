/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Hull

/-!
# Extreme sets

This file defines extreme sets and extreme points for sets in a module.

An extreme set of `A` is a subset of `A` that is as far as it can get in any outward direction: If
point `x` is in it and point `y ∈ A`, then the line passing through `x` and `y` leaves `A` at `x`.
This is an analytic notion of "being on the side of". It is weaker than being exposed (see
`IsExposed.isExtreme`).

## Main declarations

* `IsExtreme 𝕜 A B`: States that `B` is an extreme set of `A` (in the literature, `A` is often
  implicit).
* `Set.extremePoints 𝕜 A`: Set of extreme points of `A` (corresponding to extreme singletons).
* `Convex.mem_extremePoints_iff_convex_sdiff`: A useful equivalent condition to being an extreme
  point: `x` is an extreme point iff `A \ {x}` is convex.

## Implementation notes

The exact definition of extremeness has been carefully chosen so as to make as many lemmas
unconditional (in particular, the Krein-Milman theorem doesn't need the set to be convex!).
In practice, `A` is often assumed to be a convex set.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Prove lemmas relating extreme sets and points to the intrinsic frontier.
-/

@[expose] public section


open Function Module Set Affine

variable {𝕜 E F ι : Type*} {M : ι -> Type*}

section SMul

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

/-- A set `B` is an extreme subset of `A` if `B ⊆ A` and all points of `B` only belong to open
segments whose ends are in `B`.

Our definition only requires that the left endpoint of the segment lies in `B`,
but by symmetry of open segments, the right endpoint must also lie in `B`.
See `IsExtreme.right_mem_of_mem_openSegment`. -/
@[mk_iff]
/--
Definition of `IsExtreme` / `IsExtreme` 的定义

English:
structure IsExtreme
  parameters: (A B : Set E)
  axioms and operations (2):
    - subset : B subseteq A
    - left_mem_of_mem_openSegment : forall ⦃x⦄, x in A -> forall ⦃y⦄, y in A -> forall ⦃z⦄, z in B -> z in openSegment 𝕜 x y -> x in B

中文:
结构 IsExtreme
  参数: (A B : Set E)
  公理与运算 (2 个):
    - subset : B subseteq A
    - left_mem_of_mem_openSegment : 对任意 ⦃x⦄, x in A -> 对任意 ⦃y⦄, y in A -> 对任意 ⦃z⦄, z in B -> z in openSegment 𝕜 x y -> x in B
-/
structure IsExtreme (A B : Set E) : Prop where
  subset : B subseteq A
  left_mem_of_mem_openSegment : forall ⦃x⦄, x in A -> forall ⦃y⦄, y in A ->
    forall ⦃z⦄, z in B -> z in openSegment 𝕜 x y -> x in B

/--
Definition of `Set.extremePoints` / `Set.extremePoints` 的定义

English:
definition Set.extremePoints
  signature: (A : Set E)
  body: {x in A | forall ⦃x₁⦄, x₁ in A -> forall ⦃x₂⦄, x₂ in A -> x in openSegment 𝕜 x₁ x₂ -> x₁ = x}

@[refl]

中文:
定义 Set.extremePoints
  签名: (A : Set E)
  定义体: {x in A | forall ⦃x₁⦄, x₁ in A -> forall ⦃x₂⦄, x₂ in A -> x in openSegment 𝕜 x₁ x₂ -> x₁ = x}

@[refl]

Depends on / 依赖: openSegment
-/
def Set.extremePoints (A : Set E) : Set E :=
  {x in A | forall ⦃x₁⦄, x₁ in A -> forall ⦃x₂⦄, x₂ in A -> x in openSegment 𝕜 x₁ x₂ -> x₁ = x}

@[refl]
/--
theorem `IsExtreme.refl` / 定理 `IsExtreme.refl`

English:
theorem IsExtreme.refl
  given: (A : Set E)
  statement: IsExtreme 𝕜 A A
  proof: ⟨Subset.rfl, fun _ hx₁A _ _ _ _ _ => hx₁A⟩

中文:
定理 IsExtreme.refl
  条件: (A : Set E)
  结论: IsExtreme 𝕜 A A
  证明: ⟨Subset.rfl, fun _ hx₁A _ _ _ _ _ => hx₁A⟩
-/
protected theorem IsExtreme.refl (A : Set E) : IsExtreme 𝕜 A A :=
  ⟨Subset.rfl, fun _ hx₁A _ _ _ _ _ => hx₁A⟩

variable {𝕜} {A B C : Set E} {x : E}

/--
theorem `IsExtreme.rfl` / 定理 `IsExtreme.rfl`

English:
theorem IsExtreme.rfl
  statement: IsExtreme 𝕜 A A
  proof: IsExtreme.refl 𝕜 A

中文:
定理 IsExtreme.rfl
  结论: IsExtreme 𝕜 A A
  证明: IsExtreme.refl 𝕜 A
-/
protected theorem IsExtreme.rfl : IsExtreme 𝕜 A A :=
  IsExtreme.refl 𝕜 A

/--
theorem `IsExtreme.right_mem_of_mem_openSegment` / 定理 `IsExtreme.right_mem_of_mem_openSegment`

English:
theorem IsExtreme.right_mem_of_mem_openSegment
  statement: (h : IsExtreme 𝕜 A B) {y z : E} (hx : x in A)
  proof: h.left_mem_of_mem_openSegment hy hx hz by rwa [openSegment_symm]

@[trans]

中文:
定理 IsExtreme.right_mem_of_mem_openSegment
  结论: (h : IsExtreme 𝕜 A B) {y z : E} (hx : x in A)
  证明: h.left_mem_of_mem_openSegment hy hx hz by rwa [openSegment_symm]

@[trans]

Depends on / 依赖: h.left_mem_of_mem_openSegment, left_mem_of_mem_openSegment, openSegment_symm
-/
theorem IsExtreme.right_mem_of_mem_openSegment (h : IsExtreme 𝕜 A B) {y z : E} (hx : x in A)
    (hy : y in A) (hz : z in B) (hzxy : z in openSegment 𝕜 x y) : y in B :=
h.left_mem_of_mem_openSegment hy hx hz by rwa [openSegment_symm]

@[trans]
/--
theorem `IsExtreme.trans` / 定理 `IsExtreme.trans`

English:
theorem IsExtreme.trans
  given: (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C)
  proof: by
  refine ⟨hBC.subset.trans hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxC hx => ?_⟩
  exact hBC.left_mem_of_mem_openSegment
    (hAB.left_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx)
    (hAB.right_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx) hxC hx

中文:
定理 IsExtreme.trans
  条件: (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C)
  证明: by
  refine ⟨hBC.subset.trans hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxC hx => ?_⟩
  exact hBC.left_mem_of_mem_openSegment
    (hAB.left_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx)
    (hAB.right_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx) hxC hx
-/
protected theorem IsExtreme.trans (hAB : IsExtreme 𝕜 A B) (hBC : IsExtreme 𝕜 B C) :
    IsExtreme 𝕜 A C := by
  refine ⟨hBC.subset.trans hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxC hx => ?_⟩
  exact hBC.left_mem_of_mem_openSegment
    (hAB.left_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx)
    (hAB.right_mem_of_mem_openSegment hx₁A hx₂A (hBC.subset hxC) hx) hxC hx

/--
theorem `IsExtreme.antisymm` / 定理 `IsExtreme.antisymm`

English:
theorem IsExtreme.antisymm
  statement: Std.Antisymm (IsExtreme 𝕜 : Set E -> Set E -> Prop)
  proof: ⟨fun _ _ hAB hBA => Subset.antisymm hBA.1 hAB.1⟩

中文:
定理 IsExtreme.antisymm
  结论: Std.Antisymm (IsExtreme 𝕜 : Set E -> Set E -> 命题)
  证明: ⟨fun _ _ hAB hBA => Subset.antisymm hBA.1 hAB.1⟩
-/
protected theorem IsExtreme.antisymm : Std.Antisymm (IsExtreme 𝕜 : Set E -> Set E -> Prop) :=
  ⟨fun _ _ hAB hBA => Subset.antisymm hBA.1 hAB.1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder (Set E) (IsExtreme 𝕜)
  body: IsExtreme.refl 𝕜
  trans _ _ _ := IsExtreme.trans
  __ := IsExtreme.antisymm

中文:
实例 :
  签名: IsPartialOrder (Set E) (IsExtreme 𝕜)
  定义体: IsExtreme.refl 𝕜
  trans _ _ _ := IsExtreme.trans
  __ := IsExtreme.antisymm

Depends on / 依赖: IsExtreme, IsExtreme.refl
-/
instance : IsPartialOrder (Set E) (IsExtreme 𝕜) where
  refl := IsExtreme.refl 𝕜
  trans _ _ _ := IsExtreme.trans
  __ := IsExtreme.antisymm

/--
theorem `IsExtreme.inter` / 定理 `IsExtreme.inter`

English:
theorem IsExtreme.inter
  given: (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C)
  proof: by
  use Subset.trans inter_subset_left hAB.1
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx
  exact ⟨hAB.left_mem_of_mem_openSegment hx₁A hx₂A hxB hx,
    hAC.left_mem_of_mem_openSegment hx₁A hx₂A hxC hx⟩

中文:
定理 IsExtreme.inter
  条件: (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C)
  证明: by
  use Subset.trans inter_subset_left hAB.1
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx
  exact ⟨hAB.left_mem_of_mem_openSegment hx₁A hx₂A hxB hx,
    hAC.left_mem_of_mem_openSegment hx₁A hx₂A hxC hx⟩

Depends on / 依赖: Subset, Subset.trans, hAB.left_mem_of_mem_openSegment, hAC.left_mem_of_mem_openSegment, inter_subset_left, left_mem_of_mem_openSegment
-/
theorem IsExtreme.inter (hAB : IsExtreme 𝕜 A B) (hAC : IsExtreme 𝕜 A C) :
    IsExtreme 𝕜 A (B inter C) := by
  use Subset.trans inter_subset_left hAB.1
  rintro x₁ hx₁A x₂ hx₂A x ⟨hxB, hxC⟩ hx
  exact ⟨hAB.left_mem_of_mem_openSegment hx₁A hx₂A hxB hx,
    hAC.left_mem_of_mem_openSegment hx₁A hx₂A hxC hx⟩

/--
theorem `IsExtreme.mono` / 定理 `IsExtreme.mono`

English:
theorem IsExtreme.mono
  given: (hAC : IsExtreme 𝕜 A C) (hBA : B subseteq A) (hCB : C subseteq B)
  proof: ⟨hCB, fun _ hx₁B _ hx₂B _ hxC hx => hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩

中文:
定理 IsExtreme.mono
  条件: (hAC : IsExtreme 𝕜 A C) (hBA : B subseteq A) (hCB : C subseteq B)
  证明: ⟨hCB, fun _ hx₁B _ hx₂B _ hxC hx => hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩
-/
protected theorem IsExtreme.mono (hAC : IsExtreme 𝕜 A C) (hBA : B subseteq A) (hCB : C subseteq B) :
    IsExtreme 𝕜 B C :=
  ⟨hCB, fun _ hx₁B _ hx₂B _ hxC hx => hAC.2 (hBA hx₁B) (hBA hx₂B) hxC hx⟩

/--
theorem `isExtreme_iInter` / 定理 `isExtreme_iInter`

English:
theorem isExtreme_iInter
  statement: {ι : Sort*} [Nonempty ι] {F : ι -> Set E}
  proof: by
  inhabit ι
  refine ⟨iInter_subset_of_subset default (hAF default).1, fun x₁ hx₁A x₂ hx₂A x hxF hx => ?_⟩
  rw [mem_iInter] at hxF ⊢
  exact fun i => (hAF i).2 hx₁A hx₂A (hxF i) hx

中文:
定理 isExtreme_iInter
  结论: {ι : Sort*} [Nonempty ι] {F : ι -> Set E}
  证明: by
  inhabit ι
  refine ⟨iInter_subset_of_subset default (hAF default).1, fun x₁ hx₁A x₂ hx₂A x hxF hx => ?_⟩
  rw [mem_iInter] at hxF ⊢
  exact fun i => (hAF i).2 hx₁A hx₂A (hxF i) hx

Depends on / 依赖: iInter_subset_of_subset, inhabit, mem_iInter
-/
theorem isExtreme_iInter {ι : Sort*} [Nonempty ι] {F : ι -> Set E}
    (hAF : forall i : ι, IsExtreme 𝕜 A (F i)) : IsExtreme 𝕜 A (⋂ i : ι, F i) := by
  inhabit ι
  refine ⟨iInter_subset_of_subset default (hAF default).1, fun x₁ hx₁A x₂ hx₂A x hxF hx => ?_⟩
  rw [mem_iInter] at hxF ⊢
  exact fun i => (hAF i).2 hx₁A hx₂A (hxF i) hx

/--
theorem `isExtreme_biInter` / 定理 `isExtreme_biInter`

English:
theorem isExtreme_biInter
  given: {F : Set (Set E)} (hF : F.Nonempty) (hA : forall B in F, IsExtreme 𝕜 A B)
  proof: by
  have := hF.to_subtype
  simpa only [iInter_subtype] using isExtreme_iInter fun i : F => hA _ i.2

中文:
定理 isExtreme_biInter
  条件: {F : Set (Set E)} (hF : F.Nonempty) (hA : 对任意 B in F, IsExtreme 𝕜 A B)
  证明: by
  have := hF.to_subtype
  simpa only [iInter_subtype] using isExtreme_iInter fun i : F => hA _ i.2

Depends on / 依赖: hF.to_subtype, iInter_subtype, isExtreme_iInter, to_subtype
-/
theorem isExtreme_biInter {F : Set (Set E)} (hF : F.Nonempty) (hA : forall B in F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂ B in F, B) := by
  have := hF.to_subtype
  simpa only [iInter_subtype] using isExtreme_iInter fun i : F => hA _ i.2

/--
theorem `isExtreme_sInter` / 定理 `isExtreme_sInter`

English:
theorem isExtreme_sInter
  given: {F : Set (Set E)} (hF : F.Nonempty) (hAF : forall B in F, IsExtreme 𝕜 A B)
  proof: by simpa [sInter_eq_biInter] using isExtreme_biInter hF hAF

中文:
定理 isExtreme_sInter
  条件: {F : Set (Set E)} (hF : F.Nonempty) (hAF : 对任意 B in F, IsExtreme 𝕜 A B)
  证明: by simpa [sInter_eq_biInter] using isExtreme_biInter hF hAF

Depends on / 依赖: isExtreme_biInter, sInter_eq_biInter
-/
theorem isExtreme_sInter {F : Set (Set E)} (hF : F.Nonempty) (hAF : forall B in F, IsExtreme 𝕜 A B) :
    IsExtreme 𝕜 A (⋂₀ F) := by simpa [sInter_eq_biInter] using isExtreme_biInter hF hAF

/--
theorem `mem_extremePoints` / 定理 `mem_extremePoints`

English:
theorem mem_extremePoints
  statement: x in A.extremePoints 𝕜 ↔
  proof: by
  refine ⟨fun h => ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx => ⟨h.2 hx₁ hx₂ hx, ?_⟩⟩,
    fun h => ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx => (h.2 x₁ hx₁ x₂ hx₂ hx).1⟩⟩
  apply h.2 hx₂ hx₁
  rwa [openSegment_symm]

中文:
定理 mem_extremePoints
  结论: x in A.extremePoints 𝕜 ↔
  证明: by
  refine ⟨fun h => ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx => ⟨h.2 hx₁ hx₂ hx, ?_⟩⟩,
    fun h => ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx => (h.2 x₁ hx₁ x₂ hx₂ hx).1⟩⟩
  apply h.2 hx₂ hx₁
  rwa [openSegment_symm]

Depends on / 依赖: openSegment_symm
-/
theorem mem_extremePoints : x in A.extremePoints 𝕜 ↔
    x in A ∧ forallᵉ (x₁ in A) (x₂ in A), x in openSegment 𝕜 x₁ x₂ -> x₁ = x ∧ x₂ = x := by
  refine ⟨fun h => ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx => ⟨h.2 hx₁ hx₂ hx, ?_⟩⟩,
    fun h => ⟨h.1, fun x₁ hx₁ x₂ hx₂ hx => (h.2 x₁ hx₁ x₂ hx₂ hx).1⟩⟩
  apply h.2 hx₂ hx₁
  rwa [openSegment_symm]

/--
theorem `mem_extremePoints_iff_left` / 定理 `mem_extremePoints_iff_left`

English:
theorem mem_extremePoints_iff_left
  statement: x in A.extremePoints 𝕜 ↔
  proof: .rfl

中文:
定理 mem_extremePoints_iff_left
  结论: x in A.extremePoints 𝕜 ↔
  证明: .rfl
-/
theorem mem_extremePoints_iff_left : x in A.extremePoints 𝕜 ↔
    x in A ∧ forall x₁ in A, forall x₂ in A, x in openSegment 𝕜 x₁ x₂ -> x₁ = x :=
  .rfl

/--
lemma `isExtreme_singleton` / 引理 `isExtreme_singleton`

English:
lemma isExtreme_singleton
  statement: IsExtreme 𝕜 A {x} ↔ x in A.extremePoints 𝕜
  proof: by
  simp [isExtreme_iff, extremePoints]

alias ⟨IsExtreme.mem_extremePoints, _⟩ := isExtreme_singleton

中文:
引理 isExtreme_singleton
  结论: IsExtreme 𝕜 A {x} ↔ x in A.extremePoints 𝕜
  证明: by
  simp [isExtreme_iff, extremePoints]

alias ⟨IsExtreme.mem_extremePoints, _⟩ := isExtreme_singleton
-/
@[simp] lemma isExtreme_singleton : IsExtreme 𝕜 A {x} ↔ x in A.extremePoints 𝕜 := by
  simp [isExtreme_iff, extremePoints]

alias ⟨IsExtreme.mem_extremePoints, _⟩ := isExtreme_singleton

/--
theorem `extremePoints_subset` / 定理 `extremePoints_subset`

English:
theorem extremePoints_subset
  statement: A.extremePoints 𝕜 subseteq A
  proof: fun _ hx => hx.1

@[simp]

中文:
定理 extremePoints_subset
  结论: A.extremePoints 𝕜 subseteq A
  证明: fun _ hx => hx.1

@[simp]
-/
theorem extremePoints_subset : A.extremePoints 𝕜 subseteq A :=
  fun _ hx => hx.1

@[simp]
/--
theorem `extremePoints_empty` / 定理 `extremePoints_empty`

English:
theorem extremePoints_empty
  statement: (∅ : Set E).extremePoints 𝕜 = ∅
  proof: subset_empty_iff.1 extremePoints_subset

@[simp]

中文:
定理 extremePoints_empty
  结论: (∅ : Set E).extremePoints 𝕜 = ∅
  证明: subset_empty_iff.1 extremePoints_subset

@[simp]

Depends on / 依赖: extremePoints_subset, subset_empty_iff
-/
theorem extremePoints_empty : (∅ : Set E).extremePoints 𝕜 = ∅ :=
  subset_empty_iff.1 extremePoints_subset

@[simp]
/--
theorem `extremePoints_singleton` / 定理 `extremePoints_singleton`

English:
theorem extremePoints_singleton
  statement: ({x} : Set E).extremePoints 𝕜 = {x}
  proof: extremePoints_subset.antisymm singleton_subset_iff.2 ⟨mem_singleton x, fun _ hx₁ _ _ _ => hx₁⟩

中文:
定理 extremePoints_singleton
  结论: ({x} : Set E).extremePoints 𝕜 = {x}
  证明: extremePoints_subset.antisymm singleton_subset_iff.2 ⟨mem_singleton x, fun _ hx₁ _ _ _ => hx₁⟩

Depends on / 依赖: antisymm, extremePoints_subset, extremePoints_subset.antisymm, mem_singleton, singleton_subset_iff
-/
theorem extremePoints_singleton : ({x} : Set E).extremePoints 𝕜 = {x} :=
extremePoints_subset.antisymm singleton_subset_iff.2 ⟨mem_singleton x, fun _ hx₁ _ _ _ => hx₁⟩

/--
theorem `inter_extremePoints_subset_extremePoints_of_subset` / 定理 `inter_extremePoints_subset_extremePoints_of_subset`

English:
theorem inter_extremePoints_subset_extremePoints_of_subset
  given: (hBA : B subseteq A)
  proof: fun _ ⟨hxB, hxA⟩ => ⟨hxB, fun _ hx₁ _ hx₂ hx => hxA.2 (hBA hx₁) (hBA hx₂) hx⟩

中文:
定理 inter_extremePoints_subset_extremePoints_of_subset
  条件: (hBA : B subseteq A)
  证明: fun _ ⟨hxB, hxA⟩ => ⟨hxB, fun _ hx₁ _ hx₂ hx => hxA.2 (hBA hx₁) (hBA hx₂) hx⟩
-/
theorem inter_extremePoints_subset_extremePoints_of_subset (hBA : B subseteq A) :
    B inter A.extremePoints 𝕜 subseteq B.extremePoints 𝕜 :=
  fun _ ⟨hxB, hxA⟩ => ⟨hxB, fun _ hx₁ _ hx₂ hx => hxA.2 (hBA hx₁) (hBA hx₂) hx⟩

/--
theorem `IsExtreme.extremePoints_subset_extremePoints` / 定理 `IsExtreme.extremePoints_subset_extremePoints`

English:
theorem IsExtreme.extremePoints_subset_extremePoints
  given: (hAB : IsExtreme 𝕜 A B)
  proof: fun _ => by simpa only [← isExtreme_singleton] using hAB.trans

中文:
定理 IsExtreme.extremePoints_subset_extremePoints
  条件: (hAB : IsExtreme 𝕜 A B)
  证明: fun _ => by simpa only [← isExtreme_singleton] using hAB.trans

Depends on / 依赖: hAB.trans, isExtreme_singleton
-/
theorem IsExtreme.extremePoints_subset_extremePoints (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 subseteq A.extremePoints 𝕜 :=
  fun _ => by simpa only [← isExtreme_singleton] using hAB.trans

/--
theorem `IsExtreme.extremePoints_eq` / 定理 `IsExtreme.extremePoints_eq`

English:
theorem IsExtreme.extremePoints_eq
  given: (hAB : IsExtreme 𝕜 A B)
  proof: Subset.antisymm (fun _ hx => ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.1)

@[nontriviality]

中文:
定理 IsExtreme.extremePoints_eq
  条件: (hAB : IsExtreme 𝕜 A B)
  证明: Subset.antisymm (fun _ hx => ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.1)

@[nontriviality]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, extremePoints_subset_extremePoints, hAB.extremePoints_subset_extremePoints, inter_extremePoints_subset_extremePoints_of_subset
-/
theorem IsExtreme.extremePoints_eq (hAB : IsExtreme 𝕜 A B) :
    B.extremePoints 𝕜 = B inter A.extremePoints 𝕜 :=
  Subset.antisymm (fun _ hx => ⟨hx.1, hAB.extremePoints_subset_extremePoints hx⟩)
    (inter_extremePoints_subset_extremePoints_of_subset hAB.1)

@[nontriviality]
/--
lemma `Set.extremePoints_eq_self` / 引理 `Set.extremePoints_eq_self`

English:
lemma Set.extremePoints_eq_self
  given: [Subsingleton E] (A : Set E)
  statement: Set.extremePoints 𝕜 A = A
  proof: subset_antisymm extremePoints_subset fun _ h => ⟨h, fun _ _ _ _ _ => Subsingleton.elim ..⟩

中文:
引理 Set.extremePoints_eq_self
  条件: [Subsingleton E] (A : Set E)
  结论: Set.extremePoints 𝕜 A = A
  证明: subset_antisymm extremePoints_subset fun _ h => ⟨h, fun _ _ _ _ _ => Subsingleton.elim ..⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, extremePoints_subset, subset_antisymm
-/
lemma Set.extremePoints_eq_self [Subsingleton E] (A : Set E) : Set.extremePoints 𝕜 A = A :=
  subset_antisymm extremePoints_subset fun _ h => ⟨h, fun _ _ _ _ _ => Subsingleton.elim ..⟩

end SMul

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [AddCommGroup F] [forall i, AddCommGroup (M i)]
  [Module 𝕜 E] [Module 𝕜 F] [forall i, Module 𝕜 (M i)] {A B : Set E}

/--
theorem `IsExtreme.convex_sdiff` / 定理 `IsExtreme.convex_sdiff`

English:
theorem IsExtreme.convex_sdiff
  given: [IsOrderedRing 𝕜] (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B)
  proof: convex_iff_openSegment_subset.2 fun _ ⟨hx₁A, hx₁B⟩ _ ⟨hx₂A, _⟩ _ hx =>
    ⟨hA.openSegment_subset hx₁A hx₂A hx, fun hxB => hx₁B (hAB.2 hx₁A hx₂A hxB hx)⟩

@[deprecated (since := "2026-06-03")] alias IsExtreme.convex_diff := IsExtreme.convex_sdiff

@[simp]

中文:
定理 IsExtreme.convex_sdiff
  条件: [IsOrderedRing 𝕜] (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B)
  证明: convex_iff_openSegment_subset.2 fun _ ⟨hx₁A, hx₁B⟩ _ ⟨hx₂A, _⟩ _ hx =>
    ⟨hA.openSegment_subset hx₁A hx₂A hx, fun hxB => hx₁B (hAB.2 hx₁A hx₂A hxB hx)⟩

@[deprecated (since := "2026-06-03")] alias IsExtreme.convex_diff := IsExtreme.convex_sdiff

@[simp]

Depends on / 依赖: convex_iff_openSegment_subset, hA.openSegment_subset, openSegment_subset
-/
theorem IsExtreme.convex_sdiff [IsOrderedRing 𝕜] (hA : Convex 𝕜 A) (hAB : IsExtreme 𝕜 A B) :
    Convex 𝕜 (A \ B) :=
  convex_iff_openSegment_subset.2 fun _ ⟨hx₁A, hx₁B⟩ _ ⟨hx₂A, _⟩ _ hx =>
    ⟨hA.openSegment_subset hx₁A hx₂A hx, fun hxB => hx₁B (hAB.2 hx₁A hx₂A hxB hx)⟩

@[deprecated (since := "2026-06-03")] alias IsExtreme.convex_diff := IsExtreme.convex_sdiff

@[simp]
/--
theorem `extremePoints_prod` / 定理 `extremePoints_prod`

English:
theorem extremePoints_prod
  given: (s : Set E) (t : Set F)
  proof: by
  ext ⟨x, y⟩
  refine (and_congr_right fun hx => ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩).trans and_and_and_comm
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    ext
    · exact h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congrArg Prod.fst hx'⟩
    · exact h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congrArg Prod.

中文:
定理 extremePoints_prod
  条件: (s : Set E) (t : Set F)
  证明: by
  ext ⟨x, y⟩
  refine (and_congr_right fun hx => ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩).trans and_and_and_comm
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    ext
    · exact h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congrArg Prod.fst hx'⟩
    · exact h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congrArg Prod.

Depends on / 依赖: Prod.fst, Prod.image_mk_openSegment_left, Prod.snd, and_and_and_comm, and_congr_right, hx_fst, hx_snd, image_mk_openSegment_left, mem_image_of_mem, mk_mem_prod
-/
theorem extremePoints_prod (s : Set E) (t : Set F) :
    (s ×ˢ t).extremePoints 𝕜 = s.extremePoints 𝕜 ×ˢ t.extremePoints 𝕜 := by
  ext ⟨x, y⟩
  refine (and_congr_right fun hx => ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩).trans and_and_and_comm
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, hx'⟩
    ext
    · exact h.1 hx₁.1 hx₂.1 ⟨a, b, ha, hb, hab, congrArg Prod.fst hx'⟩
    · exact h.2 hx₁.2 hx₂.2 ⟨a, b, ha, hb, hab, congrArg Prod.snd hx'⟩
  · rintro x₁ hx₁ x₂ hx₂ hx_fst
    refine congrArg Prod.fst (h (mk_mem_prod hx₁ hx.2) (mk_mem_prod hx₂ hx.2) ?_)
    rw [← Prod.image_mk_openSegment_left]
    exact mem_image_of_mem _ hx_fst
  · rintro x₁ hx₁ x₂ hx₂ hx_snd
    refine congrArg Prod.snd (h (mk_mem_prod hx.1 hx₁) (mk_mem_prod hx.1 hx₂) ?_)
    rw [← Prod.image_mk_openSegment_right]
    exact mem_image_of_mem _ hx_snd

@[simp]
/--
theorem `extremePoints_pi` / 定理 `extremePoints_pi`

English:
theorem extremePoints_pi
  given: (s : forall i, Set (M i))
  proof: by
  classical
  ext x
  simp only [mem_extremePoints_iff_left, mem_univ_pi, @forall_and ι]
  refine and_congr_right fun hx => ⟨fun h i => ?_, fun h => ?_⟩
  · rintro x₁ hx₁ x₂ hx₂ hi
    rw [← update_self i x₁ x]; rw [h (update x i x₁) _ (update x i x₂)]
    · rintro j
      obtain rfl | hji := eq_

中文:
定理 extremePoints_pi
  条件: (s : 对任意 i, Set (M i))
  证明: by
  classical
  ext x
  simp only [mem_extremePoints_iff_left, mem_univ_pi, @forall_and ι]
  refine and_congr_right fun hx => ⟨fun h i => ?_, fun h => ?_⟩
  · rintro x₁ hx₁ x₂ hx₂ hi
    rw [← update_self i x₁ x]; rw [h (update x i x₁) _ (update x i x₂)]
    · rintro j
      obtain rfl | hji := eq_

Depends on / 依赖: Pi.image_update_openSegment, and_congr_right, classical, eq_or_ne, forall_and, image_update_openSegment, mem_extremePoints_iff_left, mem_univ_pi, update, update_eq_self, update_self
-/
theorem extremePoints_pi (s : forall i, Set (M i)) :
    (univ.pi s).extremePoints 𝕜 = univ.pi fun i => (s i).extremePoints 𝕜 := by
  classical
  ext x
  simp only [mem_extremePoints_iff_left, mem_univ_pi, @forall_and ι]
  refine and_congr_right fun hx => ⟨fun h i => ?_, fun h => ?_⟩
  · rintro x₁ hx₁ x₂ hx₂ hi
    rw [← update_self i x₁ x]; rw [h (update x i x₁) _ (update x i x₂)]
    · rintro j
      obtain rfl | hji := eq_or_ne j i <;> simp [*]
    · rw [← Pi.image_update_openSegment]
      exact ⟨_, hi, update_eq_self _ _⟩
    · rintro j
      obtain rfl | hji := eq_or_ne j i <;> simp [*]
  · rintro x₁ hx₁ x₂ hx₂ ⟨a, b, ha, hb, hab, rfl⟩
    ext i
    exact h _ _ (hx₁ _) _ (hx₂ _) ⟨a, b, ha, hb, hab, rfl⟩

end OrderedSemiring

section OrderedRing
variable {L : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [EquivLike L E F] [LinearEquivClass L 𝕜 E F]

/--
lemma `image_extremePoints` / 引理 `image_extremePoints`

English:
lemma image_extremePoints
  given: (f : L) (s : Set E)
  proof: by
  ext b
  obtain ⟨a, rfl⟩ := EquivLike.surjective f b
  have : forall x y, f '' openSegment 𝕜 x y = openSegment 𝕜 (f x) (f y) :=
    image_openSegment _ (LinearMapClass.linearMap f).toAffineMap
  simp only [mem_extremePoints, (EquivLike.surjective f).forall,
    (EquivLike.injective f).mem_set_im

中文:
引理 image_extremePoints
  条件: (f : L) (s : Set E)
  证明: by
  ext b
  obtain ⟨a, rfl⟩ := EquivLike.surjective f b
  have : forall x y, f '' openSegment 𝕜 x y = openSegment 𝕜 (f x) (f y) :=
    image_openSegment _ (LinearMapClass.linearMap f).toAffineMap
  simp only [mem_extremePoints, (EquivLike.surjective f).forall,
    (EquivLike.injective f).mem_set_im

Depends on / 依赖: EquivLike, EquivLike.injective, EquivLike.surjective, LinearMapClass, LinearMapClass.linearMap, eq_iff, image_openSegment, injective, linearMap, mem_extremePoints, mem_set_image, openSegment, surjective, toAffineMap
-/
lemma image_extremePoints (f : L) (s : Set E) :
    f '' extremePoints 𝕜 s = extremePoints 𝕜 (f '' s) := by
  ext b
  obtain ⟨a, rfl⟩ := EquivLike.surjective f b
  have : forall x y, f '' openSegment 𝕜 x y = openSegment 𝕜 (f x) (f y) :=
    image_openSegment _ (LinearMapClass.linearMap f).toAffineMap
  simp only [mem_extremePoints, (EquivLike.surjective f).forall,
    (EquivLike.injective f).mem_set_image, (EquivLike.injective f).eq_iff, ← this]

end OrderedRing

section LinearOrderedRing

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [DenselyOrdered 𝕜] [IsTorsionFree 𝕜 E] {A : Set E} {x : E}

/--
theorem `mem_extremePoints_iff_forall_segment` / 定理 `mem_extremePoints_iff_forall_segment`

English:
theorem mem_extremePoints_iff_forall_segment
  statement: x in A.extremePoints 𝕜 ↔
  proof: by
  rw [mem_extremePoints]
  refine and_congr_right fun hxA => forall₄_congr fun x₁ h₁ x₂ h₂ => ?_
  constructor
  · rw [← insert_endpoints_openSegment]
    rintro H (rfl | rfl | hx)
    exacts [Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
  · intro H hx
    rcases H (openSegment_subset_segment _ _ 

中文:
定理 mem_extremePoints_iff_forall_segment
  结论: x in A.extremePoints 𝕜 ↔
  证明: by
  rw [mem_extremePoints]
  refine and_congr_right fun hxA => forall₄_congr fun x₁ h₁ x₂ h₂ => ?_
  constructor
  · rw [← insert_endpoints_openSegment]
    rintro H (rfl | rfl | hx)
    exacts [Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
  · intro H hx
    rcases H (openSegment_subset_segment _ _ 

Depends on / 依赖: Or.inl, Or.inr, and_congr_right, exacts, insert_endpoints_openSegment, left_mem_openSegment_iff, mem_extremePoints, openSegment_subset_segment, right_mem_openSegment_iff
-/
theorem mem_extremePoints_iff_forall_segment : x in A.extremePoints 𝕜 ↔
    x in A ∧ forallᵉ (x₁ in A) (x₂ in A), x in segment 𝕜 x₁ x₂ -> x₁ = x ∨ x₂ = x := by
  rw [mem_extremePoints]
  refine and_congr_right fun hxA => forall₄_congr fun x₁ h₁ x₂ h₂ => ?_
  constructor
  · rw [← insert_endpoints_openSegment]
    rintro H (rfl | rfl | hx)
    exacts [Or.inl rfl, Or.inr rfl, Or.inl <| (H hx).1]
  · intro H hx
    rcases H (openSegment_subset_segment _ _ _ hx) with (rfl | rfl)
    exacts [⟨rfl, (left_mem_openSegment_iff.1 hx).symm⟩, ⟨right_mem_openSegment_iff.1 hx, rfl⟩]

/--
theorem `Convex.mem_extremePoints_iff_convex_sdiff` / 定理 `Convex.mem_extremePoints_iff_convex_sdiff`

English:
theorem Convex.mem_extremePoints_iff_convex_sdiff
  given: (hA : Convex 𝕜 A)
  proof: by
  use fun hx => ⟨hx.1, (isExtreme_singleton.2 hx).convex_sdiff hA⟩
  rintro ⟨hxA, hAx⟩
  refine mem_extremePoints_iff_forall_segment.2 ⟨hxA, fun x₁ hx₁ x₂ hx₂ hx => ?_⟩
  rw [convex_iff_segment_subset] at hAx
  by_contra! h
  exact (hAx ⟨hx₁, fun hx₁ => h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂, 

中文:
定理 Convex.mem_extremePoints_iff_convex_sdiff
  条件: (hA : Convex 𝕜 A)
  证明: by
  use fun hx => ⟨hx.1, (isExtreme_singleton.2 hx).convex_sdiff hA⟩
  rintro ⟨hxA, hAx⟩
  refine mem_extremePoints_iff_forall_segment.2 ⟨hxA, fun x₁ hx₁ x₂ hx₂ hx => ?_⟩
  rw [convex_iff_segment_subset] at hAx
  by_contra! h
  exact (hAx ⟨hx₁, fun hx₁ => h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂, 

Depends on / 依赖: convex_iff_segment_subset, convex_sdiff, isExtreme_singleton, mem_extremePoints_iff_forall_segment, mem_singleton_iff
-/
theorem Convex.mem_extremePoints_iff_convex_sdiff (hA : Convex 𝕜 A) :
    x in A.extremePoints 𝕜 ↔ x in A ∧ Convex 𝕜 (A \ {x}) := by
  use fun hx => ⟨hx.1, (isExtreme_singleton.2 hx).convex_sdiff hA⟩
  rintro ⟨hxA, hAx⟩
  refine mem_extremePoints_iff_forall_segment.2 ⟨hxA, fun x₁ hx₁ x₂ hx₂ hx => ?_⟩
  rw [convex_iff_segment_subset] at hAx
  by_contra! h
  exact (hAx ⟨hx₁, fun hx₁ => h.1 (mem_singleton_iff.2 hx₁)⟩
      ⟨hx₂, fun hx₂ => h.2 (mem_singleton_iff.2 hx₂)⟩ hx).2 rfl

@[deprecated (since := "2026-06-03")]
alias Convex.mem_extremePoints_iff_convex_diff := Convex.mem_extremePoints_iff_convex_sdiff

/--
theorem `Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff` / 定理 `Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff`

English:
theorem Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff
  given: (hA : Convex 𝕜 A)
  proof: by
  rw [hA.mem_extremePoints_iff_convex_sdiff]; rw [hA.convex_remove_iff_notMem_convexHull_remove]; rw [mem_sdiff]

@[deprecated (since := "2026-06-03")]
alias Convex.mem_extremePoints_iff_mem_diff_convexHull_diff :=
  Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff

中文:
定理 Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff
  条件: (hA : Convex 𝕜 A)
  证明: by
  rw [hA.mem_extremePoints_iff_convex_sdiff]; rw [hA.convex_remove_iff_notMem_convexHull_remove]; rw [mem_sdiff]

@[deprecated (since := "2026-06-03")]
alias Convex.mem_extremePoints_iff_mem_diff_convexHull_diff :=
  Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff

Depends on / 依赖: convex_remove_iff_notMem_convexHull_remove, hA.convex_remove_iff_notMem_convexHull_remove, hA.mem_extremePoints_iff_convex_sdiff, mem_extremePoints_iff_convex_sdiff, mem_sdiff
-/
theorem Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff (hA : Convex 𝕜 A) :
    x in A.extremePoints 𝕜 ↔ x in A \ convexHull 𝕜 (A \ {x}) := by
  rw [hA.mem_extremePoints_iff_convex_sdiff]; rw [hA.convex_remove_iff_notMem_convexHull_remove]; rw [mem_sdiff]

@[deprecated (since := "2026-06-03")]
alias Convex.mem_extremePoints_iff_mem_diff_convexHull_diff :=
  Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff

/--
theorem `extremePoints_convexHull_subset` / 定理 `extremePoints_convexHull_subset`

English:
theorem extremePoints_convexHull_subset
  statement: (convexHull 𝕜 A).extremePoints 𝕜 subseteq A
  proof: by
  rintro x hx
  rw [(convex_convexHull 𝕜 _).mem_extremePoints_iff_convex_sdiff] at hx
  by_contra h
  exact (convexHull_min (subset_sdiff.2 ⟨subset_convexHull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl

中文:
定理 extremePoints_convexHull_subset
  结论: (convexHull 𝕜 A).extremePoints 𝕜 subseteq A
  证明: by
  rintro x hx
  rw [(convex_convexHull 𝕜 _).mem_extremePoints_iff_convex_sdiff] at hx
  by_contra h
  exact (convexHull_min (subset_sdiff.2 ⟨subset_convexHull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl

Depends on / 依赖: convexHull_min, convex_convexHull, disjoint_singleton_right, mem_extremePoints_iff_convex_sdiff, subset_convexHull, subset_sdiff
-/
theorem extremePoints_convexHull_subset : (convexHull 𝕜 A).extremePoints 𝕜 subseteq A := by
  rintro x hx
  rw [(convex_convexHull 𝕜 _).mem_extremePoints_iff_convex_sdiff] at hx
  by_contra h
  exact (convexHull_min (subset_sdiff.2 ⟨subset_convexHull 𝕜 _, disjoint_singleton_right.2 h⟩) hx.2
    hx.1).2 rfl

end LinearOrderedRing
