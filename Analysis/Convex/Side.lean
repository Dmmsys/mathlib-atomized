/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Sides of affine subspaces

This file defines notions of two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `s.WSameSide x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.SSameSide x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.WOppSide x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.SOppSide x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/

@[expose] public section


variable {R V V' P P' : Type*}

open AffineEquiv AffineMap

namespace AffineSubspace

section StrictOrderedCommRing

variable [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

/--
Definition of `WSameSide` / `WSameSide` 的定义

English:
definition WSameSide
  signature: (s : AffineSubspace R P) (x y : P)
  body: existsᵉ (p₁ in s) (p₂ in s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)

中文:
定义 WSameSide
  签名: (s : AffineSubspace R P) (x y : P)
  定义体: existsᵉ (p₁ in s) (p₂ in s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)

Depends on / 依赖: SameRay
-/
def WSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  existsᵉ (p₁ in s) (p₂ in s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)

/--
Definition of `SSameSide` / `SSameSide` 的定义

English:
definition SSameSide
  signature: (s : AffineSubspace R P) (x y : P)
  body: s.WSameSide x y ∧ x ∉ s ∧ y ∉ s

中文:
定义 SSameSide
  签名: (s : AffineSubspace R P) (x y : P)
  定义体: s.WSameSide x y ∧ x ∉ s ∧ y ∉ s

Depends on / 依赖: WSameSide, s.WSameSide
-/
def SSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WSameSide x y ∧ x ∉ s ∧ y ∉ s

/--
Definition of `WOppSide` / `WOppSide` 的定义

English:
definition WOppSide
  signature: (s : AffineSubspace R P) (x y : P)
  body: existsᵉ (p₁ in s) (p₂ in s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)

中文:
定义 WOppSide
  签名: (s : AffineSubspace R P) (x y : P)
  定义体: existsᵉ (p₁ in s) (p₂ in s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)

Depends on / 依赖: SameRay
-/
def WOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  existsᵉ (p₁ in s) (p₂ in s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)

/--
Definition of `SOppSide` / `SOppSide` 的定义

English:
definition SOppSide
  signature: (s : AffineSubspace R P) (x y : P)
  body: s.WOppSide x y ∧ x ∉ s ∧ y ∉ s

中文:
定义 SOppSide
  签名: (s : AffineSubspace R P) (x y : P)
  定义体: s.WOppSide x y ∧ x ∉ s ∧ y ∉ s

Depends on / 依赖: WOppSide, s.WOppSide
-/
def SOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WOppSide x y ∧ x ∉ s ∧ y ∉ s

/--
theorem `WSameSide.map` / 定理 `WSameSide.map`

English:
theorem WSameSide.map
  given: {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P ->ᵃ[R] P')
  proof: by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear

中文:
定理 WSameSide.map
  条件: {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P ->ᵃ[R] P')
  证明: by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear

Depends on / 依赖: f.linear, h.map, linear, linearMap_vsub, mem_map_of_mem, simp_rw
-/
theorem WSameSide.map {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P ->ᵃ[R] P') :
    (s.map f).WSameSide (f x) (f y) := by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear

/--
theorem `_root_.Function.Injective.wSameSide_map_iff` / 定理 `_root_.Function.Injective.wSameSide_map_iff`

English:
theorem _root_.Function.Injective.wSameSide_map_iff
  statement: {s : AffineSubspace R P} {x y : P}
  proof: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exa

中文:
定理 _root_.Function.Injective.wSameSide_map_iff
  结论: {s : AffineSubspace R P} {x y : P}
  证明: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exa

Depends on / 依赖: f.linear_injective_iff, h.map, linearMap_vsub, linear_injective_iff, mem_map, sameRay_map_iff, simp_rw
-/
theorem _root_.Function.Injective.wSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P ->ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).WSameSide (f x) (f y) ↔ s.WSameSide x y := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exact h

/--
theorem `_root_.Function.Injective.sSameSide_map_iff` / 定理 `_root_.Function.Injective.sSameSide_map_iff`

English:
theorem _root_.Function.Injective.sSameSide_map_iff
  statement: {s : AffineSubspace R P} {x y : P}
  proof: by
  simp_rw [SSameSide, hf.wSameSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]

中文:
定理 _root_.Function.Injective.sSameSide_map_iff
  结论: {s : AffineSubspace R P} {x y : P}
  证明: by
  simp_rw [SSameSide, hf.wSameSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]

Depends on / 依赖: SSameSide, hf.wSameSide_map_iff, mem_map_iff_mem_of_injective, simp_rw, wSameSide_map_iff
-/
theorem _root_.Function.Injective.sSameSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P ->ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).SSameSide (f x) (f y) ↔ s.SSameSide x y := by
  simp_rw [SSameSide, hf.wSameSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]
/--
theorem `_root_.AffineEquiv.wSameSide_map_iff` / 定理 `_root_.AffineEquiv.wSameSide_map_iff`

English:
theorem _root_.AffineEquiv.wSameSide_map_iff
  given: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  proof: (show Function.Injective f.toAffineMap from f.injective).wSameSide_map_iff

@[simp]

中文:
定理 _root_.AffineEquiv.wSameSide_map_iff
  条件: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  证明: (show Function.Injective f.toAffineMap from f.injective).wSameSide_map_iff

@[simp]

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, injective, toAffineMap, wSameSide_map_iff
-/
theorem _root_.AffineEquiv.wSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WSameSide (f x) (f y) ↔ s.WSameSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).wSameSide_map_iff

@[simp]
/--
theorem `_root_.AffineEquiv.sSameSide_map_iff` / 定理 `_root_.AffineEquiv.sSameSide_map_iff`

English:
theorem _root_.AffineEquiv.sSameSide_map_iff
  given: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  proof: (show Function.Injective f.toAffineMap from f.injective).sSameSide_map_iff

中文:
定理 _root_.AffineEquiv.sSameSide_map_iff
  条件: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  证明: (show Function.Injective f.toAffineMap from f.injective).sSameSide_map_iff

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, injective, sSameSide_map_iff, toAffineMap
-/
theorem _root_.AffineEquiv.sSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SSameSide (f x) (f y) ↔ s.SSameSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).sSameSide_map_iff

/--
theorem `WOppSide.map` / 定理 `WOppSide.map`

English:
theorem WOppSide.map
  given: {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) (f : P ->ᵃ[R] P')
  proof: by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear

中文:
定理 WOppSide.map
  条件: {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) (f : P ->ᵃ[R] P')
  证明: by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear

Depends on / 依赖: f.linear, h.map, linear, linearMap_vsub, mem_map_of_mem, simp_rw
-/
theorem WOppSide.map {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) (f : P ->ᵃ[R] P') :
    (s.map f).WOppSide (f x) (f y) := by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, ?_⟩
  simp_rw [← linearMap_vsub]
  exact h.map f.linear

/--
theorem `_root_.Function.Injective.wOppSide_map_iff` / 定理 `_root_.Function.Injective.wOppSide_map_iff`

English:
theorem _root_.Function.Injective.wOppSide_map_iff
  statement: {s : AffineSubspace R P} {x y : P}
  proof: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exa

中文:
定理 _root_.Function.Injective.wOppSide_map_iff
  结论: {s : AffineSubspace R P} {x y : P}
  证明: by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exa

Depends on / 依赖: f.linear_injective_iff, h.map, linearMap_vsub, linear_injective_iff, mem_map, sameRay_map_iff, simp_rw
-/
theorem _root_.Function.Injective.wOppSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P ->ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).WOppSide (f x) (f y) ↔ s.WOppSide x y := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  simp_rw [← linearMap_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exact h

/--
theorem `_root_.Function.Injective.sOppSide_map_iff` / 定理 `_root_.Function.Injective.sOppSide_map_iff`

English:
theorem _root_.Function.Injective.sOppSide_map_iff
  statement: {s : AffineSubspace R P} {x y : P}
  proof: by
  simp_rw [SOppSide, hf.wOppSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]

中文:
定理 _root_.Function.Injective.sOppSide_map_iff
  结论: {s : AffineSubspace R P} {x y : P}
  证明: by
  simp_rw [SOppSide, hf.wOppSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]

Depends on / 依赖: SOppSide, hf.wOppSide_map_iff, mem_map_iff_mem_of_injective, simp_rw, wOppSide_map_iff
-/
theorem _root_.Function.Injective.sOppSide_map_iff {s : AffineSubspace R P} {x y : P}
    {f : P ->ᵃ[R] P'} (hf : Function.Injective f) :
    (s.map f).SOppSide (f x) (f y) ↔ s.SOppSide x y := by
  simp_rw [SOppSide, hf.wOppSide_map_iff, mem_map_iff_mem_of_injective hf]

@[simp]
/--
theorem `_root_.AffineEquiv.wOppSide_map_iff` / 定理 `_root_.AffineEquiv.wOppSide_map_iff`

English:
theorem _root_.AffineEquiv.wOppSide_map_iff
  given: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  proof: (show Function.Injective f.toAffineMap from f.injective).wOppSide_map_iff

@[simp]

中文:
定理 _root_.AffineEquiv.wOppSide_map_iff
  条件: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  证明: (show Function.Injective f.toAffineMap from f.injective).wOppSide_map_iff

@[simp]

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, injective, toAffineMap, wOppSide_map_iff
-/
theorem _root_.AffineEquiv.wOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WOppSide (f x) (f y) ↔ s.WOppSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).wOppSide_map_iff

@[simp]
/--
theorem `_root_.AffineEquiv.sOppSide_map_iff` / 定理 `_root_.AffineEquiv.sOppSide_map_iff`

English:
theorem _root_.AffineEquiv.sOppSide_map_iff
  given: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  proof: (show Function.Injective f.toAffineMap from f.injective).sOppSide_map_iff

中文:
定理 _root_.AffineEquiv.sOppSide_map_iff
  条件: {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P')
  证明: (show Function.Injective f.toAffineMap from f.injective).sOppSide_map_iff

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, injective, sOppSide_map_iff, toAffineMap
-/
theorem _root_.AffineEquiv.sOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SOppSide (f x) (f y) ↔ s.SOppSide x y :=
  (show Function.Injective f.toAffineMap from f.injective).sOppSide_map_iff

/--
theorem `WSameSide.nonempty` / 定理 `WSameSide.nonempty`

English:
theorem WSameSide.nonempty
  given: {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y)
  proof: ⟨h.choose, h.choose_spec.left⟩

中文:
定理 WSameSide.nonempty
  条件: {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y)
  证明: ⟨h.choose, h.choose_spec.left⟩

Depends on / 依赖: choose_spec, h.choose, h.choose_spec.left
-/
theorem WSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.choose, h.choose_spec.left⟩

/--
theorem `SSameSide.nonempty` / 定理 `SSameSide.nonempty`

English:
theorem SSameSide.nonempty
  given: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  proof: ⟨h.1.choose, h.1.choose_spec.left⟩

中文:
定理 SSameSide.nonempty
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  证明: ⟨h.1.choose, h.1.choose_spec.left⟩

Depends on / 依赖: choose_spec, choose_spec.left
-/
theorem SSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.choose, h.1.choose_spec.left⟩

/--
theorem `WOppSide.nonempty` / 定理 `WOppSide.nonempty`

English:
theorem WOppSide.nonempty
  given: {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y)
  proof: ⟨h.choose, h.choose_spec.left⟩

中文:
定理 WOppSide.nonempty
  条件: {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y)
  证明: ⟨h.choose, h.choose_spec.left⟩

Depends on / 依赖: choose_spec, h.choose, h.choose_spec.left
-/
theorem WOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.choose, h.choose_spec.left⟩

/--
theorem `SOppSide.nonempty` / 定理 `SOppSide.nonempty`

English:
theorem SOppSide.nonempty
  given: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  proof: ⟨h.1.choose, h.1.choose_spec.left⟩

中文:
定理 SOppSide.nonempty
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  证明: ⟨h.1.choose, h.1.choose_spec.left⟩

Depends on / 依赖: choose_spec, choose_spec.left
-/
theorem SOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.choose, h.1.choose_spec.left⟩

/--
theorem `SSameSide.wSameSide` / 定理 `SSameSide.wSameSide`

English:
theorem SSameSide.wSameSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  proof: h.1

中文:
定理 SSameSide.wSameSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  证明: h.1
-/
theorem SSameSide.wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    s.WSameSide x y :=
  h.1

/--
theorem `SSameSide.left_notMem` / 定理 `SSameSide.left_notMem`

English:
theorem SSameSide.left_notMem
  given: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  statement: x ∉ s
  proof: h.2.1

中文:
定理 SSameSide.left_notMem
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  结论: x ∉ s
  证明: h.2.1
-/
theorem SSameSide.left_notMem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : x ∉ s :=
  h.2.1

/--
theorem `SSameSide.right_notMem` / 定理 `SSameSide.right_notMem`

English:
theorem SSameSide.right_notMem
  given: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  statement: y ∉ s
  proof: h.2.2

中文:
定理 SSameSide.right_notMem
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  结论: y ∉ s
  证明: h.2.2
-/
theorem SSameSide.right_notMem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : y ∉ s :=
  h.2.2

/--
theorem `SOppSide.wOppSide` / 定理 `SOppSide.wOppSide`

English:
theorem SOppSide.wOppSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  proof: h.1

中文:
定理 SOppSide.wOppSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  证明: h.1
-/
theorem SOppSide.wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    s.WOppSide x y :=
  h.1

/--
theorem `SOppSide.left_notMem` / 定理 `SOppSide.left_notMem`

English:
theorem SOppSide.left_notMem
  given: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  statement: x ∉ s
  proof: h.2.1

中文:
定理 SOppSide.left_notMem
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  结论: x ∉ s
  证明: h.2.1
-/
theorem SOppSide.left_notMem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : x ∉ s :=
  h.2.1

/--
theorem `SOppSide.right_notMem` / 定理 `SOppSide.right_notMem`

English:
theorem SOppSide.right_notMem
  given: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  statement: y ∉ s
  proof: h.2.2

中文:
定理 SOppSide.right_notMem
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  结论: y ∉ s
  证明: h.2.2
-/
theorem SOppSide.right_notMem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : y ∉ s :=
  h.2.2

/--
theorem `wSameSide_comm` / 定理 `wSameSide_comm`

English:
theorem wSameSide_comm
  given: {s : AffineSubspace R P} {x y : P}
  statement: s.WSameSide x y ↔ s.WSameSide y x
  proof: ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩,
    fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩

alias ⟨WSameSide.symm, _⟩ := wSameSide_comm

中文:
定理 wSameSide_comm
  条件: {s : AffineSubspace R P} {x y : P}
  结论: s.WSameSide x y ↔ s.WSameSide y x
  证明: ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩,
    fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩

alias ⟨WSameSide.symm, _⟩ := wSameSide_comm

Depends on / 依赖: h.symm
-/
theorem wSameSide_comm {s : AffineSubspace R P} {x y : P} : s.WSameSide x y ↔ s.WSameSide y x :=
  ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩,
    fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩

alias ⟨WSameSide.symm, _⟩ := wSameSide_comm

/--
theorem `sSameSide_comm` / 定理 `sSameSide_comm`

English:
theorem sSameSide_comm
  given: {s : AffineSubspace R P} {x y : P}
  statement: s.SSameSide x y ↔ s.SSameSide y x
  proof: by
  rw [SSameSide]; rw [SSameSide]; rw [wSameSide_comm]; rw [and_comm (b := x ∉ s)]

alias ⟨SSameSide.symm, _⟩ := sSameSide_comm

中文:
定理 sSameSide_comm
  条件: {s : AffineSubspace R P} {x y : P}
  结论: s.SSameSide x y ↔ s.SSameSide y x
  证明: by
  rw [SSameSide]; rw [SSameSide]; rw [wSameSide_comm]; rw [and_comm (b := x ∉ s)]

alias ⟨SSameSide.symm, _⟩ := sSameSide_comm

Depends on / 依赖: SSameSide, and_comm, wSameSide_comm
-/
theorem sSameSide_comm {s : AffineSubspace R P} {x y : P} : s.SSameSide x y ↔ s.SSameSide y x := by
  rw [SSameSide]; rw [SSameSide]; rw [wSameSide_comm]; rw [and_comm (b := x ∉ s)]

alias ⟨SSameSide.symm, _⟩ := sSameSide_comm

/--
theorem `wOppSide_comm` / 定理 `wOppSide_comm`

English:
theorem wOppSide_comm
  given: {s : AffineSubspace R P} {x y : P}
  statement: s.WOppSide x y ↔ s.WOppSide y x
  proof: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_v

中文:
定理 wOppSide_comm
  条件: {s : AffineSubspace R P} {x y : P}
  结论: s.WOppSide x y ↔ s.WOppSide y x
  证明: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_v

Depends on / 依赖: SameRay, SameRay.sameRay_comm, neg_vsub_eq_vsub_rev, sameRay_comm, sameRay_neg_iff
-/
theorem wOppSide_comm {s : AffineSubspace R P} {x y : P} : s.WOppSide x y ↔ s.WOppSide y x := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]

alias ⟨WOppSide.symm, _⟩ := wOppSide_comm

/--
theorem `sOppSide_comm` / 定理 `sOppSide_comm`

English:
theorem sOppSide_comm
  given: {s : AffineSubspace R P} {x y : P}
  statement: s.SOppSide x y ↔ s.SOppSide y x
  proof: by
  rw [SOppSide]; rw [SOppSide]; rw [wOppSide_comm]; rw [and_comm (b := x ∉ s)]

alias ⟨SOppSide.symm, _⟩ := sOppSide_comm

中文:
定理 sOppSide_comm
  条件: {s : AffineSubspace R P} {x y : P}
  结论: s.SOppSide x y ↔ s.SOppSide y x
  证明: by
  rw [SOppSide]; rw [SOppSide]; rw [wOppSide_comm]; rw [and_comm (b := x ∉ s)]

alias ⟨SOppSide.symm, _⟩ := sOppSide_comm

Depends on / 依赖: SOppSide, and_comm, wOppSide_comm
-/
theorem sOppSide_comm {s : AffineSubspace R P} {x y : P} : s.SOppSide x y ↔ s.SOppSide y x := by
  rw [SOppSide]; rw [SOppSide]; rw [wOppSide_comm]; rw [and_comm (b := x ∉ s)]

alias ⟨SOppSide.symm, _⟩ := sOppSide_comm

/--
theorem `not_wSameSide_bot` / 定理 `not_wSameSide_bot`

English:
theorem not_wSameSide_bot
  given: (x y : P)
  statement: ¬(⊥ : AffineSubspace R P).WSameSide x y
  proof: fun ⟨_, h, _⟩ => h.elim

中文:
定理 not_wSameSide_bot
  条件: (x y : P)
  结论: ¬(⊥ : AffineSubspace R P).WSameSide x y
  证明: fun ⟨_, h, _⟩ => h.elim

Depends on / 依赖: h.elim
-/
theorem not_wSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WSameSide x y :=
  fun ⟨_, h, _⟩ => h.elim

/--
theorem `not_sSameSide_bot` / 定理 `not_sSameSide_bot`

English:
theorem not_sSameSide_bot
  given: (x y : P)
  statement: ¬(⊥ : AffineSubspace R P).SSameSide x y
  proof: fun h => not_wSameSide_bot x y h.wSameSide

中文:
定理 not_sSameSide_bot
  条件: (x y : P)
  结论: ¬(⊥ : AffineSubspace R P).SSameSide x y
  证明: fun h => not_wSameSide_bot x y h.wSameSide

Depends on / 依赖: h.wSameSide, not_wSameSide_bot, wSameSide
-/
theorem not_sSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SSameSide x y :=
  fun h => not_wSameSide_bot x y h.wSameSide

/--
theorem `not_wOppSide_bot` / 定理 `not_wOppSide_bot`

English:
theorem not_wOppSide_bot
  given: (x y : P)
  statement: ¬(⊥ : AffineSubspace R P).WOppSide x y
  proof: fun ⟨_, h, _⟩ => h.elim

中文:
定理 not_wOppSide_bot
  条件: (x y : P)
  结论: ¬(⊥ : AffineSubspace R P).WOppSide x y
  证明: fun ⟨_, h, _⟩ => h.elim

Depends on / 依赖: h.elim
-/
theorem not_wOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WOppSide x y :=
  fun ⟨_, h, _⟩ => h.elim

/--
theorem `not_sOppSide_bot` / 定理 `not_sOppSide_bot`

English:
theorem not_sOppSide_bot
  given: (x y : P)
  statement: ¬(⊥ : AffineSubspace R P).SOppSide x y
  proof: fun h => not_wOppSide_bot x y h.wOppSide

@[simp]

中文:
定理 not_sOppSide_bot
  条件: (x y : P)
  结论: ¬(⊥ : AffineSubspace R P).SOppSide x y
  证明: fun h => not_wOppSide_bot x y h.wOppSide

@[simp]

Depends on / 依赖: h.wOppSide, not_wOppSide_bot, wOppSide
-/
theorem not_sOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SOppSide x y :=
  fun h => not_wOppSide_bot x y h.wOppSide

@[simp]
/--
theorem `wSameSide_self_iff` / 定理 `wSameSide_self_iff`

English:
theorem wSameSide_self_iff
  given: {s : AffineSubspace R P} {x : P}
  proof: ⟨fun h => h.nonempty, fun ⟨p, hp⟩ => ⟨p, hp, p, hp, SameRay.rfl⟩⟩

中文:
定理 wSameSide_self_iff
  条件: {s : AffineSubspace R P} {x : P}
  证明: ⟨fun h => h.nonempty, fun ⟨p, hp⟩ => ⟨p, hp, p, hp, SameRay.rfl⟩⟩

Depends on / 依赖: SameRay, SameRay.rfl, h.nonempty, nonempty
-/
theorem wSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.WSameSide x x ↔ (s : Set P).Nonempty :=
  ⟨fun h => h.nonempty, fun ⟨p, hp⟩ => ⟨p, hp, p, hp, SameRay.rfl⟩⟩

/--
theorem `sSameSide_self_iff` / 定理 `sSameSide_self_iff`

English:
theorem sSameSide_self_iff
  given: {s : AffineSubspace R P} {x : P}
  proof: ⟨fun ⟨h, hx, _⟩ => ⟨wSameSide_self_iff.1 h, hx⟩, fun ⟨h, hx⟩ => ⟨wSameSide_self_iff.2 h, hx, hx⟩⟩

中文:
定理 sSameSide_self_iff
  条件: {s : AffineSubspace R P} {x : P}
  证明: ⟨fun ⟨h, hx, _⟩ => ⟨wSameSide_self_iff.1 h, hx⟩, fun ⟨h, hx⟩ => ⟨wSameSide_self_iff.2 h, hx, hx⟩⟩

Depends on / 依赖: wSameSide_self_iff
-/
theorem sSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.SSameSide x x ↔ (s : Set P).Nonempty ∧ x ∉ s :=
  ⟨fun ⟨h, hx, _⟩ => ⟨wSameSide_self_iff.1 h, hx⟩, fun ⟨h, hx⟩ => ⟨wSameSide_self_iff.2 h, hx, hx⟩⟩

/--
theorem `wSameSide_of_left_mem` / 定理 `wSameSide_of_left_mem`

English:
theorem wSameSide_of_left_mem
  given: {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s)
  proof: by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left

中文:
定理 wSameSide_of_left_mem
  条件: {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s)
  证明: by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left

Depends on / 依赖: SameRay, SameRay.zero_left, vsub_self, zero_left
-/
theorem wSameSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s) :
    s.WSameSide x y := by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left

/--
theorem `wSameSide_of_right_mem` / 定理 `wSameSide_of_right_mem`

English:
theorem wSameSide_of_right_mem
  given: {s : AffineSubspace R P} (x : P) {y : P} (hy : y in s)
  proof: (wSameSide_of_left_mem x hy).symm

中文:
定理 wSameSide_of_right_mem
  条件: {s : AffineSubspace R P} (x : P) {y : P} (hy : y in s)
  证明: (wSameSide_of_left_mem x hy).symm

Depends on / 依赖: wSameSide_of_left_mem
-/
theorem wSameSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y in s) :
    s.WSameSide x y :=
  (wSameSide_of_left_mem x hy).symm

/--
theorem `wOppSide_of_left_mem` / 定理 `wOppSide_of_left_mem`

English:
theorem wOppSide_of_left_mem
  given: {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s)
  proof: by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left

中文:
定理 wOppSide_of_left_mem
  条件: {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s)
  证明: by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left

Depends on / 依赖: SameRay, SameRay.zero_left, vsub_self, zero_left
-/
theorem wOppSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s) :
    s.WOppSide x y := by
  refine ⟨x, hx, x, hx, ?_⟩
  rw [vsub_self]
  apply SameRay.zero_left

/--
theorem `wOppSide_of_right_mem` / 定理 `wOppSide_of_right_mem`

English:
theorem wOppSide_of_right_mem
  given: {s : AffineSubspace R P} (x : P) {y : P} (hy : y in s)
  proof: (wOppSide_of_left_mem x hy).symm

中文:
定理 wOppSide_of_right_mem
  条件: {s : AffineSubspace R P} (x : P) {y : P} (hy : y in s)
  证明: (wOppSide_of_left_mem x hy).symm

Depends on / 依赖: wOppSide_of_left_mem
-/
theorem wOppSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y in s) :
    s.WOppSide x y :=
  (wOppSide_of_left_mem x hy).symm

/--
theorem `wSameSide_vadd_left_iff` / 定理 `wSameSide_vadd_left_iff`

English:
theorem wSameSide_vadd_left_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineS

中文:
定理 wSameSide_vadd_left_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineS

Depends on / 依赖: AffineSubspace, AffineSubspace.vadd_mem_of_mem_direction, Submodule, Submodule.neg_mem, add_comm, neg_mem, sub_neg_eq_add, vadd_mem_of_mem_direction, vadd_vsub_assoc, vadd_vsub_vadd_cancel_left, vsub_vadd_eq_vsub_sub
-/
theorem wSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.WSameSide (v +ᵥ x) y ↔ s.WSameSide x y := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, ?_⟩
    rwa [vadd_vsub_vadd_cancel_left]

/--
theorem `wSameSide_vadd_right_iff` / 定理 `wSameSide_vadd_right_iff`

English:
theorem wSameSide_vadd_right_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  rw [wSameSide_comm]; rw [wSameSide_vadd_left_iff hv]; rw [wSameSide_comm]

中文:
定理 wSameSide_vadd_right_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  rw [wSameSide_comm]; rw [wSameSide_vadd_left_iff hv]; rw [wSameSide_comm]

Depends on / 依赖: wSameSide_comm, wSameSide_vadd_left_iff
-/
theorem wSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.WSameSide x (v +ᵥ y) ↔ s.WSameSide x y := by
  rw [wSameSide_comm]; rw [wSameSide_vadd_left_iff hv]; rw [wSameSide_comm]

/--
theorem `sSameSide_vadd_left_iff` / 定理 `sSameSide_vadd_left_iff`

English:
theorem sSameSide_vadd_left_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  rw [SSameSide]; rw [SSameSide]; rw [wSameSide_vadd_left_iff hv]; rw [vadd_mem_iff_mem_of_mem_direction hv]

中文:
定理 sSameSide_vadd_left_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  rw [SSameSide]; rw [SSameSide]; rw [wSameSide_vadd_left_iff hv]; rw [vadd_mem_iff_mem_of_mem_direction hv]

Depends on / 依赖: SSameSide, vadd_mem_iff_mem_of_mem_direction, wSameSide_vadd_left_iff
-/
theorem sSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.SSameSide (v +ᵥ x) y ↔ s.SSameSide x y := by
  rw [SSameSide]; rw [SSameSide]; rw [wSameSide_vadd_left_iff hv]; rw [vadd_mem_iff_mem_of_mem_direction hv]

/--
theorem `sSameSide_vadd_right_iff` / 定理 `sSameSide_vadd_right_iff`

English:
theorem sSameSide_vadd_right_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  rw [sSameSide_comm]; rw [sSameSide_vadd_left_iff hv]; rw [sSameSide_comm]

中文:
定理 sSameSide_vadd_right_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  rw [sSameSide_comm]; rw [sSameSide_vadd_left_iff hv]; rw [sSameSide_comm]

Depends on / 依赖: sSameSide_comm, sSameSide_vadd_left_iff
-/
theorem sSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.SSameSide x (v +ᵥ y) ↔ s.SSameSide x y := by
  rw [sSameSide_comm]; rw [sSameSide_vadd_left_iff hv]; rw [sSameSide_comm]

/--
theorem `wOppSide_vadd_left_iff` / 定理 `wOppSide_vadd_left_iff`

English:
theorem wOppSide_vadd_left_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineS

中文:
定理 wOppSide_vadd_left_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineS

Depends on / 依赖: AffineSubspace, AffineSubspace.vadd_mem_of_mem_direction, Submodule, Submodule.neg_mem, add_comm, neg_mem, sub_neg_eq_add, vadd_mem_of_mem_direction, vadd_vsub_assoc, vadd_vsub_vadd_cancel_left, vsub_vadd_eq_vsub_sub
-/
theorem wOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.WOppSide (v +ᵥ x) y ↔ s.WOppSide x y := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, ?_⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, ?_⟩
    rwa [vadd_vsub_vadd_cancel_left]

/--
theorem `wOppSide_vadd_right_iff` / 定理 `wOppSide_vadd_right_iff`

English:
theorem wOppSide_vadd_right_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  rw [wOppSide_comm]; rw [wOppSide_vadd_left_iff hv]; rw [wOppSide_comm]

中文:
定理 wOppSide_vadd_right_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  rw [wOppSide_comm]; rw [wOppSide_vadd_left_iff hv]; rw [wOppSide_comm]

Depends on / 依赖: wOppSide_comm, wOppSide_vadd_left_iff
-/
theorem wOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.WOppSide x (v +ᵥ y) ↔ s.WOppSide x y := by
  rw [wOppSide_comm]; rw [wOppSide_vadd_left_iff hv]; rw [wOppSide_comm]

/--
theorem `sOppSide_vadd_left_iff` / 定理 `sOppSide_vadd_left_iff`

English:
theorem sOppSide_vadd_left_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  rw [SOppSide]; rw [SOppSide]; rw [wOppSide_vadd_left_iff hv]; rw [vadd_mem_iff_mem_of_mem_direction hv]

中文:
定理 sOppSide_vadd_left_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  rw [SOppSide]; rw [SOppSide]; rw [wOppSide_vadd_left_iff hv]; rw [vadd_mem_iff_mem_of_mem_direction hv]

Depends on / 依赖: SOppSide, vadd_mem_iff_mem_of_mem_direction, wOppSide_vadd_left_iff
-/
theorem sOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.SOppSide (v +ᵥ x) y ↔ s.SOppSide x y := by
  rw [SOppSide]; rw [SOppSide]; rw [wOppSide_vadd_left_iff hv]; rw [vadd_mem_iff_mem_of_mem_direction hv]

/--
theorem `sOppSide_vadd_right_iff` / 定理 `sOppSide_vadd_right_iff`

English:
theorem sOppSide_vadd_right_iff
  given: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  proof: by
  rw [sOppSide_comm]; rw [sOppSide_vadd_left_iff hv]; rw [sOppSide_comm]

中文:
定理 sOppSide_vadd_right_iff
  条件: {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction)
  证明: by
  rw [sOppSide_comm]; rw [sOppSide_vadd_left_iff hv]; rw [sOppSide_comm]

Depends on / 依赖: sOppSide_comm, sOppSide_vadd_left_iff
-/
theorem sOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v in s.direction) :
    s.SOppSide x (v +ᵥ y) ↔ s.SOppSide x y := by
  rw [sOppSide_comm]; rw [sOppSide_vadd_left_iff hv]; rw [sOppSide_comm]

/--
theorem `wSameSide_smul_vsub_vadd_left` / 定理 `wSameSide_smul_vsub_vadd_left`

English:
theorem wSameSide_smul_vsub_vadd_left
  statement: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  proof: by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub]
  exact SameRay.sameRay_nonneg_smul_left _ ht

中文:
定理 wSameSide_smul_vsub_vadd_left
  结论: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  证明: by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub]
  exact SameRay.sameRay_nonneg_smul_left _ ht

Depends on / 依赖: SameRay, SameRay.sameRay_nonneg_smul_left, sameRay_nonneg_smul_left, vadd_vsub
-/
theorem wSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) {t : R} (ht : 0 <= t) : s.WSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub]
  exact SameRay.sameRay_nonneg_smul_left _ ht

/--
theorem `wSameSide_smul_vsub_vadd_right` / 定理 `wSameSide_smul_vsub_vadd_right`

English:
theorem wSameSide_smul_vsub_vadd_right
  statement: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  proof: (wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

中文:
定理 wSameSide_smul_vsub_vadd_right
  结论: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  证明: (wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

Depends on / 依赖: wSameSide_smul_vsub_vadd_left
-/
theorem wSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) {t : R} (ht : 0 <= t) : s.WSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wSameSide_lineMap_left` / 定理 `wSameSide_lineMap_left`

English:
theorem wSameSide_lineMap_left
  statement: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  proof: wSameSide_smul_vsub_vadd_left y h h ht

中文:
定理 wSameSide_lineMap_left
  结论: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  证明: wSameSide_smul_vsub_vadd_left y h h ht

Depends on / 依赖: wSameSide_smul_vsub_vadd_left
-/
theorem wSameSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
    (ht : 0 <= t) : s.WSameSide (lineMap x y t) y :=
  wSameSide_smul_vsub_vadd_left y h h ht

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wSameSide_lineMap_right` / 定理 `wSameSide_lineMap_right`

English:
theorem wSameSide_lineMap_right
  statement: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  proof: (wSameSide_lineMap_left y h ht).symm

中文:
定理 wSameSide_lineMap_right
  结论: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  证明: (wSameSide_lineMap_left y h ht).symm

Depends on / 依赖: wSameSide_lineMap_left
-/
theorem wSameSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
    (ht : 0 <= t) : s.WSameSide y (lineMap x y t) :=
  (wSameSide_lineMap_left y h ht).symm

/--
theorem `wOppSide_smul_vsub_vadd_left` / 定理 `wOppSide_smul_vsub_vadd_left`

English:
theorem wOppSide_smul_vsub_vadd_left
  statement: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  proof: by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub]; rw [← neg_neg t]; rw [neg_smul]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]
  exact SameRay.sameRay_nonneg_smul_left _ (neg_nonneg.2 ht)

中文:
定理 wOppSide_smul_vsub_vadd_left
  结论: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  证明: by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub]; rw [← neg_neg t]; rw [neg_smul]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]
  exact SameRay.sameRay_nonneg_smul_left _ (neg_nonneg.2 ht)

Depends on / 依赖: SameRay, SameRay.sameRay_nonneg_smul_left, neg_neg, neg_nonneg, neg_smul, neg_vsub_eq_vsub_rev, sameRay_nonneg_smul_left, smul_neg, vadd_vsub
-/
theorem wOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) {t : R} (ht : t <= 0) : s.WOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨p₂, hp₂, p₁, hp₁, ?_⟩
  rw [vadd_vsub]; rw [← neg_neg t]; rw [neg_smul]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]
  exact SameRay.sameRay_nonneg_smul_left _ (neg_nonneg.2 ht)

/--
theorem `wOppSide_smul_vsub_vadd_right` / 定理 `wOppSide_smul_vsub_vadd_right`

English:
theorem wOppSide_smul_vsub_vadd_right
  statement: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  proof: (wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

中文:
定理 wOppSide_smul_vsub_vadd_right
  结论: {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
  证明: (wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

Depends on / 依赖: wOppSide_smul_vsub_vadd_left
-/
theorem wOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ in s)
    (hp₂ : p₂ in s) {t : R} (ht : t <= 0) : s.WOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wOppSide_lineMap_left` / 定理 `wOppSide_lineMap_left`

English:
theorem wOppSide_lineMap_left
  statement: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  proof: wOppSide_smul_vsub_vadd_left y h h ht

中文:
定理 wOppSide_lineMap_left
  结论: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  证明: wOppSide_smul_vsub_vadd_left y h h ht

Depends on / 依赖: wOppSide_smul_vsub_vadd_left
-/
theorem wOppSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
    (ht : t <= 0) : s.WOppSide (lineMap x y t) y :=
  wOppSide_smul_vsub_vadd_left y h h ht

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wOppSide_lineMap_right` / 定理 `wOppSide_lineMap_right`

English:
theorem wOppSide_lineMap_right
  statement: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  proof: (wOppSide_lineMap_left y h ht).symm

中文:
定理 wOppSide_lineMap_right
  结论: {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
  证明: (wOppSide_lineMap_left y h ht).symm

Depends on / 依赖: wOppSide_lineMap_left
-/
theorem wOppSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x in s) {t : R}
    (ht : t <= 0) : s.WOppSide y (lineMap x y t) :=
  (wOppSide_lineMap_left y h ht).symm

/--
theorem `_root_.Wbtw.wSameSide₂₃` / 定理 `_root_.Wbtw.wSameSide₂₃`

English:
theorem _root_.Wbtw.wSameSide₂₃
  statement: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  proof: by
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩
  exact wSameSide_lineMap_left z hx ht0

中文:
定理 _root_.Wbtw.wSameSide₂₃
  结论: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  证明: by
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩
  exact wSameSide_lineMap_left z hx ht0

Depends on / 依赖: wSameSide_lineMap_left
-/
theorem _root_.Wbtw.wSameSide₂₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hx : x in s) : s.WSameSide y z := by
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩
  exact wSameSide_lineMap_left z hx ht0

/--
theorem `_root_.Wbtw.wSameSide₃₂` / 定理 `_root_.Wbtw.wSameSide₃₂`

English:
theorem _root_.Wbtw.wSameSide₃₂
  statement: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  proof: (h.wSameSide₂₃ hx).symm

中文:
定理 _root_.Wbtw.wSameSide₃₂
  结论: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  证明: (h.wSameSide₂₃ hx).symm

Depends on / 依赖: h.wSameSide
-/
theorem _root_.Wbtw.wSameSide₃₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hx : x in s) : s.WSameSide z y :=
  (h.wSameSide₂₃ hx).symm

/--
theorem `_root_.Wbtw.wSameSide₁₂` / 定理 `_root_.Wbtw.wSameSide₁₂`

English:
theorem _root_.Wbtw.wSameSide₁₂
  statement: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  proof: h.symm.wSameSide₃₂ hz

中文:
定理 _root_.Wbtw.wSameSide₁₂
  结论: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  证明: h.symm.wSameSide₃₂ hz

Depends on / 依赖: h.symm.wSameSide
-/
theorem _root_.Wbtw.wSameSide₁₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hz : z in s) : s.WSameSide x y :=
  h.symm.wSameSide₃₂ hz

/--
theorem `_root_.Wbtw.wSameSide₂₁` / 定理 `_root_.Wbtw.wSameSide₂₁`

English:
theorem _root_.Wbtw.wSameSide₂₁
  statement: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  proof: h.symm.wSameSide₂₃ hz

中文:
定理 _root_.Wbtw.wSameSide₂₁
  结论: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  证明: h.symm.wSameSide₂₃ hz

Depends on / 依赖: h.symm.wSameSide
-/
theorem _root_.Wbtw.wSameSide₂₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hz : z in s) : s.WSameSide y x :=
  h.symm.wSameSide₂₃ hz

/--
theorem `_root_.Wbtw.wOppSide₁₃` / 定理 `_root_.Wbtw.wOppSide₁₃`

English:
theorem _root_.Wbtw.wOppSide₁₃
  statement: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  proof: by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine ⟨_, hy, _, hy, ?_⟩
  rcases ht1.lt_or_eq with (ht1' | rfl); swap
  · simp
  rcases ht0.lt_or_eq with (ht0' | rfl); swap
  · simp
  refine Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', ?_⟩)
  rw [lineMap_apply]; rw [vadd_vsub_assoc]; rw [vsub_vadd_eq

中文:
定理 _root_.Wbtw.wOppSide₁₃
  结论: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  证明: by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine ⟨_, hy, _, hy, ?_⟩
  rcases ht1.lt_or_eq with (ht1' | rfl); swap
  · simp
  rcases ht0.lt_or_eq with (ht0' | rfl); swap
  · simp
  refine Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', ?_⟩)
  rw [lineMap_apply]; rw [vadd_vsub_assoc]; rw [vsub_vadd_eq

Depends on / 依赖: Or.inr, ht0.lt_or_eq, ht1.lt_or_eq, lineMap_apply, lt_or_eq, module, neg_vsub_eq_vsub_rev, sub_pos, vadd_vsub_assoc, vsub_self, vsub_vadd_eq_vsub_sub
-/
theorem _root_.Wbtw.wOppSide₁₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hy : y in s) : s.WOppSide x z := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine ⟨_, hy, _, hy, ?_⟩
  rcases ht1.lt_or_eq with (ht1' | rfl); swap
  · simp
  rcases ht0.lt_or_eq with (ht0' | rfl); swap
  · simp
  refine Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', ?_⟩)
  rw [lineMap_apply]; rw [vadd_vsub_assoc]; rw [vsub_vadd_eq_vsub_sub]; rw [← neg_vsub_eq_vsub_rev z]; rw [vsub_self]
  module

/--
theorem `_root_.Wbtw.wOppSide₃₁` / 定理 `_root_.Wbtw.wOppSide₃₁`

English:
theorem _root_.Wbtw.wOppSide₃₁
  statement: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  proof: h.symm.wOppSide₁₃ hy

中文:
定理 _root_.Wbtw.wOppSide₃₁
  结论: {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
  证明: h.symm.wOppSide₁₃ hy

Depends on / 依赖: h.symm.wOppSide
-/
theorem _root_.Wbtw.wOppSide₃₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z)
    (hy : y in s) : s.WOppSide z x :=
  h.symm.wOppSide₁₃ hy

end StrictOrderedCommRing

section LinearOrderedCommRing

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

/--
theorem `wSameSide_of_vsub_eq_smul` / 定理 `wSameSide_of_vsub_eq_smul`

English:
theorem wSameSide_of_vsub_eq_smul
  statement: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  proof: by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  rw [h₁]; rw [h₂]
  exact sameRay_smul_smul_of_mul_nonneg hc

中文:
定理 wSameSide_of_vsub_eq_smul
  结论: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  证明: by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  rw [h₁]; rw [h₂]
  exact sameRay_smul_smul_of_mul_nonneg hc

Depends on / 依赖: sameRay_smul_smul_of_mul_nonneg
-/
theorem wSameSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : 0 <= c₁ * c₂) : s.WSameSide x y := by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  rw [h₁]; rw [h₂]
  exact sameRay_smul_smul_of_mul_nonneg hc

/--
theorem `wOppSide_of_vsub_eq_smul` / 定理 `wOppSide_of_vsub_eq_smul`

English:
theorem wOppSide_of_vsub_eq_smul
  statement: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  proof: by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  have h₂' : p₂ -ᵥ y = (-c₂) • m := by rw [← neg_vsub_eq_vsub_rev, h₂, neg_smul]
  rw [h₁]; rw [h₂']
  exact sameRay_smul_smul_of_mul_nonneg (by rw [mul_neg]; exact neg_nonneg.2 hc)

中文:
定理 wOppSide_of_vsub_eq_smul
  结论: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  证明: by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  have h₂' : p₂ -ᵥ y = (-c₂) • m := by rw [← neg_vsub_eq_vsub_rev, h₂, neg_smul]
  rw [h₁]; rw [h₂']
  exact sameRay_smul_smul_of_mul_nonneg (by rw [mul_neg]; exact neg_nonneg.2 hc)

Depends on / 依赖: mul_neg, neg_nonneg, neg_smul, neg_vsub_eq_vsub_rev, sameRay_smul_smul_of_mul_nonneg
-/
theorem wOppSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : c₁ * c₂ <= 0) : s.WOppSide x y := by
  refine ⟨p₁, hp₁, p₂, hp₂, ?_⟩
  have h₂' : p₂ -ᵥ y = (-c₂) • m := by rw [← neg_vsub_eq_vsub_rev, h₂, neg_smul]
  rw [h₁]; rw [h₂']
  exact sameRay_smul_smul_of_mul_nonneg (by rw [mul_neg]; exact neg_nonneg.2 hc)

/--
theorem `sSameSide_of_vsub_eq_smul` / 定理 `sSameSide_of_vsub_eq_smul`

English:
theorem sSameSide_of_vsub_eq_smul
  statement: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  proof: ⟨wSameSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

中文:
定理 sSameSide_of_vsub_eq_smul
  结论: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  证明: ⟨wSameSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

Depends on / 依赖: wSameSide_of_vsub_eq_smul
-/
theorem sSameSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : 0 <= c₁ * c₂) (hx : x ∉ s) (hy : y ∉ s) : s.SSameSide x y :=
  ⟨wSameSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

/--
theorem `sOppSide_of_vsub_eq_smul` / 定理 `sOppSide_of_vsub_eq_smul`

English:
theorem sOppSide_of_vsub_eq_smul
  statement: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  proof: ⟨wOppSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

中文:
定理 sOppSide_of_vsub_eq_smul
  结论: {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
  证明: ⟨wOppSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

Depends on / 依赖: wOppSide_of_vsub_eq_smul
-/
theorem sOppSide_of_vsub_eq_smul {s : AffineSubspace R P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : R}
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m)
    (hc : c₁ * c₂ <= 0) (hx : x ∉ s) (hy : y ∉ s) : s.SOppSide x y :=
  ⟨wOppSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

end LinearOrderedCommRing

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P]

@[simp]
/--
theorem `wOppSide_self_iff` / 定理 `wOppSide_self_iff`

English:
theorem wOppSide_self_iff
  given: {s : AffineSubspace R P} {x : P}
  statement: s.WOppSide x x ↔ x in s
  proof: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add
    rw [add_comm]; rw [vsub_add_vsub_cancel]; rw [← eq_vadd_iff_vsub_eq] at h₁
    rw [h₁]
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁
  · exact fun h => ⟨x, h, x, h, SameRay.rfl⟩

中文:
定理 wOppSide_self_iff
  条件: {s : AffineSubspace R P} {x : P}
  结论: s.WOppSide x x ↔ x in s
  证明: by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add
    rw [add_comm]; rw [vsub_add_vsub_cancel]; rw [← eq_vadd_iff_vsub_eq] at h₁
    rw [h₁]
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁
  · exact fun h => ⟨x, h, x, h, SameRay.rfl⟩

Depends on / 依赖: SameRay, SameRay.rfl, add_comm, eq_vadd_iff_vsub_eq, exists_eq_smul_add, h.exists_eq_smul_add, s.smul_vsub_vadd_mem, smul_vsub_vadd_mem, vsub_add_vsub_cancel
-/
theorem wOppSide_self_iff {s : AffineSubspace R P} {x : P} : s.WOppSide x x ↔ x in s := by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add
    rw [add_comm]; rw [vsub_add_vsub_cancel]; rw [← eq_vadd_iff_vsub_eq] at h₁
    rw [h₁]
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁
  · exact fun h => ⟨x, h, x, h, SameRay.rfl⟩

/--
theorem `not_sOppSide_self` / 定理 `not_sOppSide_self`

English:
theorem not_sOppSide_self
  given: (s : AffineSubspace R P) (x : P)
  statement: ¬s.SOppSide x x
  proof: by
  rw [SOppSide]
  simp

中文:
定理 not_sOppSide_self
  条件: (s : AffineSubspace R P) (x : P)
  结论: ¬s.SOppSide x x
  证明: by
  rw [SOppSide]
  simp

Depends on / 依赖: SOppSide
-/
theorem not_sOppSide_self (s : AffineSubspace R P) (x : P) : ¬s.SOppSide x x := by
  rw [SOppSide]
  simp

/--
theorem `wSameSide_iff_exists_left` / 定理 `wSameSide_iff_exists_left`

English:
theorem wSameSide_iff_exists_left
  given: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  proof: by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.sm

中文:
定理 wSameSide_iff_exists_left
  条件: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  证明: by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.sm

Depends on / 依赖: Or.inl, Or.inr, SameRay, SameRay.zero_right, ne.symm, s.smul_vsub_vadd_mem, smul_smul, smul_sub, smul_vsub_vadd_mem, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right, vsub_vadd_eq_vsub_sub, zero_right
-/
theorem wSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) :
    s.WSameSide x y ↔ x in s ∨ exists p₂ in s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
        Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, ?_⟩)⟩
      rw [vsub_vadd_eq_vsub_sub]; rw [smul_sub]; rw [← hr]; rw [smul_smul]; rw [mul_div_cancel₀ _ hr₂.ne.symm]; rw [← smul_sub]; rw [vsub_sub_vsub_cancel_right]
  · rintro (h' | ⟨h₁, h₂, h₃⟩)
    · exact wSameSide_of_left_mem y h'
    · exact ⟨p₁, h, h₁, h₂, h₃⟩

/--
theorem `wSameSide_iff_exists_right` / 定理 `wSameSide_iff_exists_right`

English:
theorem wSameSide_iff_exists_right
  given: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  proof: by
  rw [wSameSide_comm]; rw [wSameSide_iff_exists_left h]
  simp_rw [SameRay.sameRay_comm]

中文:
定理 wSameSide_iff_exists_right
  条件: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  证明: by
  rw [wSameSide_comm]; rw [wSameSide_iff_exists_left h]
  simp_rw [SameRay.sameRay_comm]

Depends on / 依赖: SameRay, SameRay.sameRay_comm, sameRay_comm, simp_rw, wSameSide_comm, wSameSide_iff_exists_left
-/
theorem wSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s) :
    s.WSameSide x y ↔ y in s ∨ exists p₁ in s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [wSameSide_comm]; rw [wSameSide_iff_exists_left h]
  simp_rw [SameRay.sameRay_comm]

/--
theorem `sSameSide_iff_exists_left` / 定理 `sSameSide_iff_exists_left`

English:
theorem sSameSide_iff_exists_left
  given: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  proof: by
  rw [SSameSide]; rw [and_comm]; rw [wSameSide_iff_exists_left h]; rw [and_assoc]; rw [and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]

中文:
定理 sSameSide_iff_exists_left
  条件: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  证明: by
  rw [SSameSide]; rw [and_comm]; rw [wSameSide_iff_exists_left h]; rw [and_assoc]; rw [and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]

Depends on / 依赖: SSameSide, and_assoc, and_comm, and_congr_right_iff, or_iff_right, wSameSide_iff_exists_left
-/
theorem sSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₂ in s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [SSameSide]; rw [and_comm]; rw [wSameSide_iff_exists_left h]; rw [and_assoc]; rw [and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]

/--
theorem `sSameSide_iff_exists_right` / 定理 `sSameSide_iff_exists_right`

English:
theorem sSameSide_iff_exists_right
  given: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  proof: by
  rw [sSameSide_comm]; rw [sSameSide_iff_exists_left h]; rw [← and_assoc]; rw [and_comm (a := y ∉ s)]; rw [and_assoc]
  simp_rw [SameRay.sameRay_comm]

中文:
定理 sSameSide_iff_exists_right
  条件: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  证明: by
  rw [sSameSide_comm]; rw [sSameSide_iff_exists_left h]; rw [← and_assoc]; rw [and_comm (a := y ∉ s)]; rw [and_assoc]
  simp_rw [SameRay.sameRay_comm]

Depends on / 依赖: SameRay, SameRay.sameRay_comm, and_assoc, and_comm, sSameSide_comm, sSameSide_iff_exists_left, sameRay_comm, simp_rw
-/
theorem sSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₁ in s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) := by
  rw [sSameSide_comm]; rw [sSameSide_iff_exists_left h]; rw [← and_assoc]; rw [and_comm (a := y ∉ s)]; rw [and_assoc]
  simp_rw [SameRay.sameRay_comm]

/--
theorem `wOppSide_iff_exists_left` / 定理 `wOppSide_iff_exists_left`

English:
theorem wOppSide_iff_exists_left
  given: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  proof: by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.s

中文:
定理 wOppSide_iff_exists_left
  条件: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  证明: by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.s

Depends on / 依赖: Or.inl, Or.inr, SameRay, SameRay.zero_right, linear_combination, match_scalars, s.smul_vsub_vadd_mem, smul_vsub_vadd_mem, vadd_vsub_assoc, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right, wOppSide_, zero_right
-/
theorem wOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) :
    s.WOppSide x y ↔ x in s ∨ exists p₂ in s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine Or.inr ⟨p₂', hp₂', ?_⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine Or.inr ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
        Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, ?_⟩)⟩
      rw [vadd_vsub_assoc]; rw [← vsub_sub_vsub_cancel_right x p₁ p₁']
      linear_combination (norm := match_scalars <;> field) hr
  · rintro (h' | ⟨h₁, h₂, h₃⟩)
    · exact wOppSide_of_left_mem y h'
    · exact ⟨p₁, h, h₁, h₂, h₃⟩

/--
theorem `wOppSide_iff_exists_right` / 定理 `wOppSide_iff_exists_right`

English:
theorem wOppSide_iff_exists_right
  given: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  proof: by
  rw [wOppSide_comm]; rw [wOppSide_iff_exists_left h]
  constructor
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine Or.inr ⟨p, hp, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
 

中文:
定理 wOppSide_iff_exists_right
  条件: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  证明: by
  rw [wOppSide_comm]; rw [wOppSide_iff_exists_left h]
  constructor
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine Or.inr ⟨p, hp, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
 

Depends on / 依赖: Or.inl, Or.inr, SameRay, SameRay.sameRay_comm, neg_vsub_eq_vsub_rev, sameRay_comm, sameRay_neg_iff, wOppSide_comm, wOppSide_iff_exists_left
-/
theorem wOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s) :
    s.WOppSide x y ↔ y in s ∨ exists p₁ in s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [wOppSide_comm]; rw [wOppSide_iff_exists_left h]
  constructor
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine Or.inr ⟨p, hp, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro (hy | ⟨p, hp, hr⟩)
    · exact Or.inl hy
    refine Or.inr ⟨p, hp, ?_⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]

/--
theorem `sOppSide_iff_exists_left` / 定理 `sOppSide_iff_exists_left`

English:
theorem sOppSide_iff_exists_left
  given: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  proof: by
  rw [SOppSide]; rw [and_comm]; rw [wOppSide_iff_exists_left h]; rw [and_assoc]; rw [and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]

中文:
定理 sOppSide_iff_exists_left
  条件: {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s)
  证明: by
  rw [SOppSide]; rw [and_comm]; rw [wOppSide_iff_exists_left h]; rw [and_assoc]; rw [and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]

Depends on / 依赖: SOppSide, and_assoc, and_comm, and_congr_right_iff, or_iff_right, wOppSide_iff_exists_left
-/
theorem sOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ in s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₂ in s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [SOppSide]; rw [and_comm]; rw [wOppSide_iff_exists_left h]; rw [and_assoc]; rw [and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]

/--
theorem `sOppSide_iff_exists_right` / 定理 `sOppSide_iff_exists_right`

English:
theorem sOppSide_iff_exists_right
  given: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  proof: by
  rw [SOppSide]; rw [and_comm]; rw [wOppSide_iff_exists_right h]; rw [and_assoc]; rw [and_congr_right_iff]; rw [and_congr_right_iff]
  rintro _ hy
  rw [or_iff_right hy]

中文:
定理 sOppSide_iff_exists_right
  条件: {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s)
  证明: by
  rw [SOppSide]; rw [and_comm]; rw [wOppSide_iff_exists_right h]; rw [and_assoc]; rw [and_congr_right_iff]; rw [and_congr_right_iff]
  rintro _ hy
  rw [or_iff_right hy]

Depends on / 依赖: SOppSide, and_assoc, and_comm, and_congr_right_iff, or_iff_right, wOppSide_iff_exists_right
-/
theorem sOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ in s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ exists p₁ in s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) := by
  rw [SOppSide]; rw [and_comm]; rw [wOppSide_iff_exists_right h]; rw [and_assoc]; rw [and_congr_right_iff]; rw [and_congr_right_iff]
  rintro _ hy
  rw [or_iff_right hy]

/--
theorem `WSameSide.trans` / 定理 `WSameSide.trans`

English:
theorem WSameSide.trans
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  proof: by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wSameSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)

中文:
定理 WSameSide.trans
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  证明: by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wSameSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)

Depends on / 依赖: False.elim, h.symm, hxy.trans, or_iff_right, vsub_eq_zero_iff_eq, wSameSide_iff_exists_left
-/
theorem WSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WSameSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wSameSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)

/--
theorem `WSameSide.trans_sSameSide` / 定理 `WSameSide.trans_sSameSide`

English:
theorem WSameSide.trans_sSameSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  proof: hxy.trans hyz.1 hyz.2.1

中文:
定理 WSameSide.trans_sSameSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  证明: hxy.trans hyz.1 hyz.2.1

Depends on / 依赖: hxy.trans
-/
theorem WSameSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SSameSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1

/--
theorem `WSameSide.trans_wOppSide` / 定理 `WSameSide.trans_wOppSide`

English:
theorem WSameSide.trans_wOppSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  proof: by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)

中文:
定理 WSameSide.trans_wOppSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  证明: by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)

Depends on / 依赖: False.elim, h.symm, hxy.trans, or_iff_right, vsub_eq_zero_iff_eq, wOppSide_iff_exists_left
-/
theorem WSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WOppSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)

/--
theorem `WSameSide.trans_sOppSide` / 定理 `WSameSide.trans_sOppSide`

English:
theorem WSameSide.trans_sOppSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  proof: hxy.trans_wOppSide hyz.1 hyz.2.1

中文:
定理 WSameSide.trans_sOppSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
  证明: hxy.trans_wOppSide hyz.1 hyz.2.1

Depends on / 依赖: hxy.trans_wOppSide, trans_wOppSide
-/
theorem WSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SOppSide y z) : s.WOppSide x z :=
  hxy.trans_wOppSide hyz.1 hyz.2.1

/--
theorem `SSameSide.trans_wSameSide` / 定理 `SSameSide.trans_wSameSide`

English:
theorem SSameSide.trans_wSameSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  proof: (hyz.symm.trans_sSameSide hxy.symm).symm

中文:
定理 SSameSide.trans_wSameSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  证明: (hyz.symm.trans_sSameSide hxy.symm).symm

Depends on / 依赖: hxy.symm, hyz.symm.trans_sSameSide, trans_sSameSide
-/
theorem SSameSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WSameSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sSameSide hxy.symm).symm

/--
theorem `SSameSide.trans` / 定理 `SSameSide.trans`

English:
theorem SSameSide.trans
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  proof: ⟨hxy.wSameSide.trans_sSameSide hyz, hxy.2.1, hyz.2.2⟩

中文:
定理 SSameSide.trans
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  证明: ⟨hxy.wSameSide.trans_sSameSide hyz, hxy.2.1, hyz.2.2⟩

Depends on / 依赖: hxy.wSameSide.trans_sSameSide, trans_sSameSide, wSameSide
-/
theorem SSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SSameSide y z) : s.SSameSide x z :=
  ⟨hxy.wSameSide.trans_sSameSide hyz, hxy.2.1, hyz.2.2⟩

/--
theorem `SSameSide.trans_wOppSide` / 定理 `SSameSide.trans_wOppSide`

English:
theorem SSameSide.trans_wOppSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  proof: hxy.wSameSide.trans_wOppSide hyz hxy.2.2

中文:
定理 SSameSide.trans_wOppSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  证明: hxy.wSameSide.trans_wOppSide hyz hxy.2.2

Depends on / 依赖: hxy.wSameSide.trans_wOppSide, trans_wOppSide, wSameSide
-/
theorem SSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WOppSide y z) : s.WOppSide x z :=
  hxy.wSameSide.trans_wOppSide hyz hxy.2.2

/--
theorem `SSameSide.trans_sOppSide` / 定理 `SSameSide.trans_sOppSide`

English:
theorem SSameSide.trans_sOppSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  proof: ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩

中文:
定理 SSameSide.trans_sOppSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
  证明: ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩

Depends on / 依赖: hxy.trans_wOppSide, trans_wOppSide
-/
theorem SSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SOppSide y z) : s.SOppSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩

/--
theorem `WOppSide.trans_wSameSide` / 定理 `WOppSide.trans_wSameSide`

English:
theorem WOppSide.trans_wSameSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  proof: (hyz.symm.trans_wOppSide hxy.symm hy).symm

中文:
定理 WOppSide.trans_wSameSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  证明: (hyz.symm.trans_wOppSide hxy.symm hy).symm

Depends on / 依赖: hxy.symm, hyz.symm.trans_wOppSide, trans_wOppSide
-/
theorem WOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WOppSide x z :=
  (hyz.symm.trans_wOppSide hxy.symm hy).symm

/--
theorem `WOppSide.trans_sSameSide` / 定理 `WOppSide.trans_sSameSide`

English:
theorem WOppSide.trans_sSameSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  proof: hxy.trans_wSameSide hyz.1 hyz.2.1

中文:
定理 WOppSide.trans_sSameSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  证明: hxy.trans_wSameSide hyz.1 hyz.2.1

Depends on / 依赖: hxy.trans_wSameSide, trans_wSameSide
-/
theorem WOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SSameSide y z) : s.WOppSide x z :=
  hxy.trans_wSameSide hyz.1 hyz.2.1

/--
theorem `WOppSide.trans` / 定理 `WOppSide.trans`

English:
theorem WOppSide.trans
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  proof: by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  rw [← sameRay_neg_iff]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev] at hyz
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.e

中文:
定理 WOppSide.trans
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  证明: by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  rw [← sameRay_neg_iff]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev] at hyz
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.e

Depends on / 依赖: False.elim, hxy.trans, neg_vsub_eq_vsub_rev, or_iff_right, sameRay_neg_iff, vsub_eq_zero_iff_eq, wOppSide_iff_exists_left
-/
theorem WOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WSameSide x z := by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [wOppSide_iff_exists_left hp₂]; rw [or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  rw [← sameRay_neg_iff]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev] at hyz
  refine ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz ?_⟩
  refine fun h => False.elim ?_
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h ▸ hp₂)

/--
theorem `WOppSide.trans_sOppSide` / 定理 `WOppSide.trans_sOppSide`

English:
theorem WOppSide.trans_sOppSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  proof: hxy.trans hyz.1 hyz.2.1

中文:
定理 WOppSide.trans_sOppSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
  证明: hxy.trans hyz.1 hyz.2.1

Depends on / 依赖: hxy.trans
-/
theorem WOppSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SOppSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1

/--
theorem `SOppSide.trans_wSameSide` / 定理 `SOppSide.trans_wSameSide`

English:
theorem SOppSide.trans_wSameSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  proof: (hyz.symm.trans_sOppSide hxy.symm).symm

中文:
定理 SOppSide.trans_wSameSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  证明: (hyz.symm.trans_sOppSide hxy.symm).symm

Depends on / 依赖: hxy.symm, hyz.symm.trans_sOppSide, trans_sOppSide
-/
theorem SOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WSameSide y z) : s.WOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm

/--
theorem `SOppSide.trans_sSameSide` / 定理 `SOppSide.trans_sSameSide`

English:
theorem SOppSide.trans_sSameSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  proof: (hyz.symm.trans_sOppSide hxy.symm).symm

中文:
定理 SOppSide.trans_sSameSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  证明: (hyz.symm.trans_sOppSide hxy.symm).symm

Depends on / 依赖: hxy.symm, hyz.symm.trans_sOppSide, trans_sOppSide
-/
theorem SOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SSameSide y z) : s.SOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm

/--
theorem `SOppSide.trans_wOppSide` / 定理 `SOppSide.trans_wOppSide`

English:
theorem SOppSide.trans_wOppSide
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  proof: (hyz.symm.trans_sOppSide hxy.symm).symm

中文:
定理 SOppSide.trans_wOppSide
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  证明: (hyz.symm.trans_sOppSide hxy.symm).symm

Depends on / 依赖: hxy.symm, hyz.symm.trans_sOppSide, trans_sOppSide
-/
theorem SOppSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WOppSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm

/--
theorem `SOppSide.trans` / 定理 `SOppSide.trans`

English:
theorem SOppSide.trans
  statement: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  proof: ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩

中文:
定理 SOppSide.trans
  结论: {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
  证明: ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩

Depends on / 依赖: hxy.trans_wOppSide, trans_wOppSide
-/
theorem SOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SOppSide y z) : s.SSameSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩

/--
theorem `wSameSide_and_wOppSide_iff` / 定理 `wSameSide_and_wOppSide_iff`

English:
theorem wSameSide_and_wOppSide_iff
  given: {s : AffineSubspace R P} {x y : P}
  proof: by
  constructor
  · rintro ⟨hs, ho⟩
    rw [wOppSide_comm] at ho
    by_contra h
    rw [not_or] at h
    exact h.1 (wOppSide_self_iff.1 (hs.trans_wOppSide ho h.2))
  · rintro (h | h)
    · exact ⟨wSameSide_of_left_mem y h, wOppSide_of_left_mem y h⟩
    · exact ⟨wSameSide_of_right_mem x h, wOppSide

中文:
定理 wSameSide_and_wOppSide_iff
  条件: {s : AffineSubspace R P} {x y : P}
  证明: by
  constructor
  · rintro ⟨hs, ho⟩
    rw [wOppSide_comm] at ho
    by_contra h
    rw [not_or] at h
    exact h.1 (wOppSide_self_iff.1 (hs.trans_wOppSide ho h.2))
  · rintro (h | h)
    · exact ⟨wSameSide_of_left_mem y h, wOppSide_of_left_mem y h⟩
    · exact ⟨wSameSide_of_right_mem x h, wOppSide

Depends on / 依赖: hs.trans_wOppSide, not_or, trans_wOppSide, wOppSide_comm, wOppSide_of_left_mem, wOppSide_of_right_mem, wOppSide_self_iff, wSameSide_of_left_mem, wSameSide_of_right_mem
-/
theorem wSameSide_and_wOppSide_iff {s : AffineSubspace R P} {x y : P} :
    s.WSameSide x y ∧ s.WOppSide x y ↔ x in s ∨ y in s := by
  constructor
  · rintro ⟨hs, ho⟩
    rw [wOppSide_comm] at ho
    by_contra h
    rw [not_or] at h
    exact h.1 (wOppSide_self_iff.1 (hs.trans_wOppSide ho h.2))
  · rintro (h | h)
    · exact ⟨wSameSide_of_left_mem y h, wOppSide_of_left_mem y h⟩
    · exact ⟨wSameSide_of_right_mem x h, wOppSide_of_right_mem x h⟩

/--
theorem `WSameSide.not_sOppSide` / 定理 `WSameSide.not_sOppSide`

English:
theorem WSameSide.not_sOppSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y)
  proof: by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h, ho.1⟩
  rcases hxy with (hx | hy)
  · exact ho.2.1 hx
  · exact ho.2.2 hy

中文:
定理 WSameSide.not_sOppSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y)
  证明: by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h, ho.1⟩
  rcases hxy with (hx | hy)
  · exact ho.2.1 hx
  · exact ho.2.2 hy

Depends on / 依赖: wSameSide_and_wOppSide_iff
-/
theorem WSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    ¬s.SOppSide x y := by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h, ho.1⟩
  rcases hxy with (hx | hy)
  · exact ho.2.1 hx
  · exact ho.2.2 hy

/--
theorem `SSameSide.not_wOppSide` / 定理 `SSameSide.not_wOppSide`

English:
theorem SSameSide.not_wOppSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  proof: by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h.1, ho⟩
  rcases hxy with (hx | hy)
  · exact h.2.1 hx
  · exact h.2.2 hy

中文:
定理 SSameSide.not_wOppSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  证明: by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h.1, ho⟩
  rcases hxy with (hx | hy)
  · exact h.2.1 hx
  · exact h.2.2 hy

Depends on / 依赖: wSameSide_and_wOppSide_iff
-/
theorem SSameSide.not_wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.WOppSide x y := by
  intro ho
  have hxy := wSameSide_and_wOppSide_iff.1 ⟨h.1, ho⟩
  rcases hxy with (hx | hy)
  · exact h.2.1 hx
  · exact h.2.2 hy

/--
theorem `SSameSide.not_sOppSide` / 定理 `SSameSide.not_sOppSide`

English:
theorem SSameSide.not_sOppSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  proof: fun ho => h.not_wOppSide ho.1

中文:
定理 SSameSide.not_sOppSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y)
  证明: fun ho => h.not_wOppSide ho.1

Depends on / 依赖: h.not_wOppSide, not_wOppSide
-/
theorem SSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.SOppSide x y :=
  fun ho => h.not_wOppSide ho.1

/--
theorem `WOppSide.not_sSameSide` / 定理 `WOppSide.not_sSameSide`

English:
theorem WOppSide.not_sSameSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y)
  proof: fun hs => hs.not_wOppSide h

中文:
定理 WOppSide.not_sSameSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y)
  证明: fun hs => hs.not_wOppSide h

Depends on / 依赖: hs.not_wOppSide, not_wOppSide
-/
theorem WOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    ¬s.SSameSide x y :=
  fun hs => hs.not_wOppSide h

/--
theorem `SOppSide.not_wSameSide` / 定理 `SOppSide.not_wSameSide`

English:
theorem SOppSide.not_wSameSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  proof: fun hs => hs.not_sOppSide h

中文:
定理 SOppSide.not_wSameSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  证明: fun hs => hs.not_sOppSide h

Depends on / 依赖: hs.not_sOppSide, not_sOppSide
-/
theorem SOppSide.not_wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.WSameSide x y :=
  fun hs => hs.not_sOppSide h

/--
theorem `SOppSide.not_sSameSide` / 定理 `SOppSide.not_sSameSide`

English:
theorem SOppSide.not_sSameSide
  given: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  proof: fun hs => h.not_wSameSide hs.1

中文:
定理 SOppSide.not_sSameSide
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  证明: fun hs => h.not_wSameSide hs.1

Depends on / 依赖: h.not_wSameSide, not_wSameSide
-/
theorem SOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.SSameSide x y :=
  fun hs => h.not_wSameSide hs.1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wOppSide_iff_exists_wbtw` / 定理 `wOppSide_iff_exists_wbtw`

English:
theorem wOppSide_iff_exists_wbtw
  given: {s : AffineSubspace R P} {x y : P}
  proof: by
  refine ⟨fun h => ?_, fun ⟨p, hp, h⟩ => h.wOppSide₁₃ hp⟩
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [h]
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [← h]
    exact ⟨p₂, hp₂, wbtw_self_right _ _

中文:
定理 wOppSide_iff_exists_wbtw
  条件: {s : AffineSubspace R P} {x y : P}
  证明: by
  refine ⟨fun h => ?_, fun ⟨p, hp, h⟩ => h.wOppSide₁₃ hp⟩
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [h]
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [← h]
    exact ⟨p₂, hp₂, wbtw_self_right _ _

Depends on / 依赖: h.wOppSide, lineMap, linear_combination, neg_vsub_eq_vsub_rev, vsub_eq_zero_iff_eq, wbtw_self_left, wbtw_self_right
-/
theorem wOppSide_iff_exists_wbtw {s : AffineSubspace R P} {x y : P} :
    s.WOppSide x y ↔ exists p in s, Wbtw R x p y := by
  refine ⟨fun h => ?_, fun ⟨p, hp, h⟩ => h.wOppSide₁₃ hp⟩
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [h]
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [← h]
    exact ⟨p₂, hp₂, wbtw_self_right _ _ _⟩
  · refine ⟨lineMap x y (r₂ / (r₁ + r₂)), ?_, ?_⟩
    · have : (r₂ / (r₁ + r₂)) • (y -ᵥ p₂ + (p₂ -ᵥ p₁) - (x -ᵥ p₁)) + (x -ᵥ p₁) =
          (r₂ / (r₁ + r₂)) • (p₂ -ᵥ p₁) := by
        rw [← neg_vsub_eq_vsub_rev p₂ y]
        linear_combination (norm := match_scalars <;> field) (r₁ + r₂)⁻¹ • h
      rw [lineMap_apply]; rw [← vsub_vadd x p₁]; rw [← vsub_vadd y p₂]; rw [vsub_vadd_eq_vsub_sub]; rw [vadd_vsub_assoc]; rw [← vadd_assoc]; rw [vadd_eq_add]; rw [this]
      exact s.smul_vsub_vadd_mem (r₂ / (r₁ + r₂)) hp₂ hp₁ hp₁
    · exact Set.mem_image_of_mem _
        ⟨by positivity,
          div_le_one_of_le₀ (le_add_of_nonneg_left hr₁.le) (Left.add_pos hr₁ hr₂).le⟩

/--
theorem `SOppSide.exists_sbtw` / 定理 `SOppSide.exists_sbtw`

English:
theorem SOppSide.exists_sbtw
  given: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  proof: by
  obtain ⟨p, hp, hw⟩ := wOppSide_iff_exists_wbtw.1 h.wOppSide
  refine ⟨p, hp, hw, ?_, ?_⟩
  · rintro rfl
    exact h.2.1 hp
  · rintro rfl
    exact h.2.2 hp

中文:
定理 SOppSide.exists_sbtw
  条件: {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y)
  证明: by
  obtain ⟨p, hp, hw⟩ := wOppSide_iff_exists_wbtw.1 h.wOppSide
  refine ⟨p, hp, hw, ?_, ?_⟩
  · rintro rfl
    exact h.2.1 hp
  · rintro rfl
    exact h.2.2 hp

Depends on / 依赖: h.wOppSide, wOppSide, wOppSide_iff_exists_wbtw
-/
theorem SOppSide.exists_sbtw {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    exists p in s, Sbtw R x p y := by
  obtain ⟨p, hp, hw⟩ := wOppSide_iff_exists_wbtw.1 h.wOppSide
  refine ⟨p, hp, hw, ?_, ?_⟩
  · rintro rfl
    exact h.2.1 hp
  · rintro rfl
    exact h.2.2 hp

/--
theorem `_root_.Sbtw.sOppSide_of_notMem_of_mem` / 定理 `_root_.Sbtw.sOppSide_of_notMem_of_mem`

English:
theorem _root_.Sbtw.sOppSide_of_notMem_of_mem
  statement: {s : AffineSubspace R P} {x y z : P}
  proof: by
  refine ⟨h.wbtw.wOppSide₁₃ hy, hx, fun hz => hx ?_⟩
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩
  rw [lineMap_apply] at hy
  have ht : t != 1 := by
    rintro rfl
    simp [lineMap_apply] at hyz
  have hy' := vsub_mem_direction hy hz
  rw [vadd_vsub_assoc]; rw [← neg_vsub_eq_vsub_rev z]; rw

中文:
定理 _root_.Sbtw.sOppSide_of_notMem_of_mem
  结论: {s : AffineSubspace R P} {x y z : P}
  证明: by
  refine ⟨h.wbtw.wOppSide₁₃ hy, hx, fun hz => hx ?_⟩
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩
  rw [lineMap_apply] at hy
  have ht : t != 1 := by
    rintro rfl
    simp [lineMap_apply] at hyz
  have hy' := vsub_mem_direction hy hz
  rw [vadd_vsub_assoc]; rw [← neg_vsub_eq_vsub_rev z]; rw

Depends on / 依赖: Submodule, Submodule.smul_mem, add_smul, direction, h.wbtw.wOppSide, lineMap_apply, neg_one_smul, neg_vsub_eq_vsub_rev, s.direction.smul_mem_iff, smul_mem, smul_mem_iff, sub_eq_add_neg, sub_ne_zero_of_ne, vadd_mem_iff_mem_of_mem_direction, vadd_vsub_assoc, vsub_mem_direction
-/
theorem _root_.Sbtw.sOppSide_of_notMem_of_mem {s : AffineSubspace R P} {x y z : P}
    (h : Sbtw R x y z) (hx : x ∉ s) (hy : y in s) : s.SOppSide x z := by
  refine ⟨h.wbtw.wOppSide₁₃ hy, hx, fun hz => hx ?_⟩
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩
  rw [lineMap_apply] at hy
  have ht : t != 1 := by
    rintro rfl
    simp [lineMap_apply] at hyz
  have hy' := vsub_mem_direction hy hz
  rw [vadd_vsub_assoc]; rw [← neg_vsub_eq_vsub_rev z]; rw [← neg_one_smul R (z -ᵥ x)]; rw [← add_smul]; rw [← sub_eq_add_neg]; rw [s.direction.smul_mem_iff (sub_ne_zero_of_ne ht)] at hy'
  rwa [vadd_mem_iff_mem_of_mem_direction (Submodule.smul_mem _ _ hy')] at hy

/--
theorem `sSameSide_smul_vsub_vadd_left` / 定理 `sSameSide_smul_vsub_vadd_left`

English:
theorem sSameSide_smul_vsub_vadd_left
  statement: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  proof: by
  refine ⟨wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
    vsub_right_mem_direction_iff_mem hp₁] at h

中文:
定理 sSameSide_smul_vsub_vadd_left
  结论: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  证明: by
  refine ⟨wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
    vsub_right_mem_direction_iff_mem hp₁] at h

Depends on / 依赖: direction, ht.le, ht.ne.symm, s.direction.smul_mem_iff, smul_mem_iff, vadd_mem_iff_mem_direction, vsub_right_mem_direction_iff_mem, wSameSide_smul_vsub_vadd_left
-/
theorem sSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : 0 < t) : s.SSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
    vsub_right_mem_direction_iff_mem hp₁] at h

/--
theorem `sSameSide_smul_vsub_vadd_right` / 定理 `sSameSide_smul_vsub_vadd_right`

English:
theorem sSameSide_smul_vsub_vadd_right
  statement: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  proof: (sSameSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

中文:
定理 sSameSide_smul_vsub_vadd_right
  结论: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  证明: (sSameSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

Depends on / 依赖: sSameSide_smul_vsub_vadd_left
-/
theorem sSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : 0 < t) : s.SSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sSameSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sSameSide_lineMap_left` / 定理 `sSameSide_lineMap_left`

English:
theorem sSameSide_lineMap_left
  statement: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  proof: sSameSide_smul_vsub_vadd_left hy hx hx ht

中文:
定理 sSameSide_lineMap_left
  结论: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  证明: sSameSide_smul_vsub_vadd_left hy hx hx ht

Depends on / 依赖: sSameSide_smul_vsub_vadd_left
-/
theorem sSameSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide (lineMap x y t) y :=
  sSameSide_smul_vsub_vadd_left hy hx hx ht

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sSameSide_lineMap_right` / 定理 `sSameSide_lineMap_right`

English:
theorem sSameSide_lineMap_right
  statement: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  proof: (sSameSide_lineMap_left hx hy ht).symm

中文:
定理 sSameSide_lineMap_right
  结论: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  证明: (sSameSide_lineMap_left hx hy ht).symm

Depends on / 依赖: sSameSide_lineMap_left
-/
theorem sSameSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide y (lineMap x y t) :=
  (sSameSide_lineMap_left hx hy ht).symm

/--
theorem `sOppSide_smul_vsub_vadd_left` / 定理 `sOppSide_smul_vsub_vadd_left`

English:
theorem sOppSide_smul_vsub_vadd_left
  statement: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  proof: by
  refine ⟨wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
    vsub_right_mem_direction_iff_mem hp₁] at h

中文:
定理 sOppSide_smul_vsub_vadd_left
  结论: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  证明: by
  refine ⟨wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
    vsub_right_mem_direction_iff_mem hp₁] at h

Depends on / 依赖: direction, ht.le, ht.ne, s.direction.smul_mem_iff, smul_mem_iff, vadd_mem_iff_mem_direction, vsub_right_mem_direction_iff_mem, wOppSide_smul_vsub_vadd_left
-/
theorem sOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : t < 0) : s.SOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x := by
  refine ⟨wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx ?_, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
    vsub_right_mem_direction_iff_mem hp₁] at h

/--
theorem `sOppSide_smul_vsub_vadd_right` / 定理 `sOppSide_smul_vsub_vadd_right`

English:
theorem sOppSide_smul_vsub_vadd_right
  statement: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  proof: (sOppSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

中文:
定理 sOppSide_smul_vsub_vadd_right
  结论: {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
  证明: (sOppSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

Depends on / 依赖: sOppSide_smul_vsub_vadd_left
-/
theorem sOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ in s) (hp₂ : p₂ in s) {t : R} (ht : t < 0) : s.SOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sOppSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sOppSide_lineMap_left` / 定理 `sOppSide_lineMap_left`

English:
theorem sOppSide_lineMap_left
  statement: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  proof: sOppSide_smul_vsub_vadd_left hy hx hx ht

中文:
定理 sOppSide_lineMap_left
  结论: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  证明: sOppSide_smul_vsub_vadd_left hy hx hx ht

Depends on / 依赖: sOppSide_smul_vsub_vadd_left
-/
theorem sOppSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide (lineMap x y t) y :=
  sOppSide_smul_vsub_vadd_left hy hx hx ht

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sOppSide_lineMap_right` / 定理 `sOppSide_lineMap_right`

English:
theorem sOppSide_lineMap_right
  statement: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  proof: (sOppSide_lineMap_left hx hy ht).symm

中文:
定理 sOppSide_lineMap_right
  结论: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
  证明: (sOppSide_lineMap_left hx hy ht).symm

Depends on / 依赖: sOppSide_lineMap_left
-/
theorem sOppSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide y (lineMap x y t) :=
  (sOppSide_lineMap_left hx hy ht).symm

/--
theorem `setOfPred_wSameSide_eq_image2` / 定理 `setOfPred_wSameSide_eq_image2`

English:
theorem setOfPred_wSameSide_eq_image2
  given: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  proof: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ici]
  constructor
  · rw [wSameSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at 

中文:
定理 setOfPred_wSameSide_eq_image2
  条件: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  证明: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ici]
  constructor
  · rw [wSameSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at 

Depends on / 依赖: False.elim, Set.mem_Ici, Set.mem_image2, Set.mem_ofPred, div_eq_inv_mul, div_pos, h.symm, le_rfl, mem_Ici, mem_image2, mem_ofPred, ne.symm, one_smul, or_iff_right, simp_rw, smul_smul, vsub_eq_zero_iff_eq, vsub_vadd, wSameSide_iff_exists_left
-/
theorem setOfPred_wSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) :
    { y | s.WSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ici 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ici]
  constructor
  · rw [wSameSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine ⟨0, le_rfl, p₂, hp₂, ?_⟩
      simp [h]
    · refine ⟨r₁ / r₂, (div_pos hr₁ hr₂).le, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul]; rw [← smul_smul]; rw [h]; rw [smul_smul]; rw [inv_mul_cancel₀ hr₂.ne.symm]; rw [one_smul]; rw [vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact wSameSide_smul_vsub_vadd_right x hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_wSameSide_eq_image2 := setOfPred_wSameSide_eq_image2

/--
theorem `setOfPred_sSameSide_eq_image2` / 定理 `setOfPred_sSameSide_eq_image2`

English:
theorem setOfPred_sSameSide_eq_image2
  given: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  proof: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ioi]
  constructor
  · rw [sSameSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      ex

中文:
定理 setOfPred_sSameSide_eq_image2
  条件: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  证明: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ioi]
  constructor
  · rw [sSameSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      ex

Depends on / 依赖: False.elim, Set.mem_Ioi, Set.mem_image2, Set.mem_ofPred, div_eq_inv_mul, div_pos, h.symm, mem_Ioi, mem_image2, mem_ofPred, ne.symm, one_smul, sSameSide_iff_exists_left, simp_rw, smul_smul, vsub_eq_zero_iff_eq, vsub_vadd
-/
theorem setOfPred_sSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) :
    { y | s.SSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ioi 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Ioi]
  constructor
  · rw [sSameSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h.symm ▸ hp₂))
    · refine ⟨r₁ / r₂, div_pos hr₁ hr₂, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul]; rw [← smul_smul]; rw [h]; rw [smul_smul]; rw [inv_mul_cancel₀ hr₂.ne.symm]; rw [one_smul]; rw [vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact sSameSide_smul_vsub_vadd_right hx hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_sSameSide_eq_image2 := setOfPred_sSameSide_eq_image2

/--
theorem `setOfPred_wOppSide_eq_image2` / 定理 `setOfPred_wOppSide_eq_image2`

English:
theorem setOfPred_wOppSide_eq_image2
  given: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  proof: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iic]
  constructor
  · rw [wOppSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h

中文:
定理 setOfPred_wOppSide_eq_image2
  条件: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  证明: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iic]
  constructor
  · rw [wOppSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h

Depends on / 依赖: False.elim, Left.neg_neg_iff, Set.mem_Iic, Set.mem_image2, Set.mem_ofPred, div_eq_inv_mul, div_neg_of_neg_of_pos, h.symm, le_rfl, mem_Iic, mem_image2, mem_ofPred, neg_neg_iff, neg_smul, or_iff_right, simp_rw, smul_neg, smul_smul, vsub_eq_zero_iff_eq, wOppSide_iff_exists_left
-/
theorem setOfPred_wOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) :
    { y | s.WOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iic 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iic]
  constructor
  · rw [wOppSide_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine ⟨0, le_rfl, p₂, hp₂, ?_⟩
      simp [h]
    · refine ⟨-r₁ / r₂, (div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂).le, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul]; rw [← smul_smul]; rw [neg_smul]; rw [h]; rw [smul_neg]; rw [smul_smul]; rw [inv_mul_cancel₀ hr₂.ne.symm]; rw [one_smul]; rw [neg_vsub_eq_vsub_rev]; rw [vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact wOppSide_smul_vsub_vadd_right x hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_wOppSide_eq_image2 := setOfPred_wOppSide_eq_image2

/--
theorem `setOfPred_sOppSide_eq_image2` / 定理 `setOfPred_sOppSide_eq_image2`

English:
theorem setOfPred_sOppSide_eq_image2
  given: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  proof: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iio]
  constructor
  · rw [sOppSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exa

中文:
定理 setOfPred_sOppSide_eq_image2
  条件: {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s)
  证明: by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iio]
  constructor
  · rw [sOppSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exa

Depends on / 依赖: False.elim, Left.neg_neg_iff, Set.mem_Iio, Set.mem_image2, Set.mem_ofPred, div_eq_inv_mul, div_neg_of_neg_of_pos, h.symm, mem_Iio, mem_image2, mem_ofPred, neg_neg_iff, neg_smul, sOppSide_iff_exists_left, simp_rw, smul_neg, smul_smul, vsub_eq_zero_iff_eq
-/
theorem setOfPred_sOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p in s) :
    { y | s.SOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iio 0) s := by
  ext y
  simp_rw [Set.mem_ofPred, Set.mem_image2, Set.mem_Iio]
  constructor
  · rw [sOppSide_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h ▸ hp₂))
    · refine ⟨-r₁ / r₂, div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂, p₂, hp₂, ?_⟩
      rw [div_eq_inv_mul]; rw [← smul_smul]; rw [neg_smul]; rw [h]; rw [smul_neg]; rw [smul_smul]; rw [inv_mul_cancel₀ hr₂.ne.symm]; rw [one_smul]; rw [neg_vsub_eq_vsub_rev]; rw [vsub_vadd]
  · rintro ⟨t, ht, p', hp', rfl⟩
    exact sOppSide_smul_vsub_vadd_right hx hp hp' ht

@[deprecated (since := "2026-07-09")]
alias setOf_sOppSide_eq_image2 := setOfPred_sOppSide_eq_image2

/--
theorem `wOppSide_pointReflection` / 定理 `wOppSide_pointReflection`

English:
theorem wOppSide_pointReflection
  given: {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s)
  proof: (wbtw_pointReflection R _ _).wOppSide₁₃ hx

中文:
定理 wOppSide_pointReflection
  条件: {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s)
  证明: (wbtw_pointReflection R _ _).wOppSide₁₃ hx

Depends on / 依赖: wbtw_pointReflection
-/
theorem wOppSide_pointReflection {s : AffineSubspace R P} {x : P} (y : P) (hx : x in s) :
    s.WOppSide y (pointReflection R x y) :=
  (wbtw_pointReflection R _ _).wOppSide₁₃ hx

/--
theorem `sOppSide_pointReflection` / 定理 `sOppSide_pointReflection`

English:
theorem sOppSide_pointReflection
  given: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s)
  proof: by
  refine (sbtw_pointReflection_of_ne R fun h => hy ?_).sOppSide_of_notMem_of_mem hy hx
  rwa [← h]

中文:
定理 sOppSide_pointReflection
  条件: {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s)
  证明: by
  refine (sbtw_pointReflection_of_ne R fun h => hy ?_).sOppSide_of_notMem_of_mem hy hx
  rwa [← h]

Depends on / 依赖: sOppSide_of_notMem_of_mem, sbtw_pointReflection_of_ne
-/
theorem sOppSide_pointReflection {s : AffineSubspace R P} {x y : P} (hx : x in s) (hy : y ∉ s) :
    s.SOppSide y (pointReflection R x y) := by
  refine (sbtw_pointReflection_of_ne R fun h => hy ?_).sOppSide_of_notMem_of_mem hy hx
  rwa [← h]

end LinearOrderedField

section Normed

variable [SeminormedAddCommGroup V] [NormedSpace Real V] [PseudoMetricSpace P]
variable [NormedAddTorsor V P]

/--
theorem `isConnected_setOfPred_wSameSide` / 定理 `isConnected_setOfPred_wSameSide`

English:
theorem isConnected_setOfPred_wSameSide
  statement: {s : AffineSubspace Real P} (x : P)
  proof: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x in s
  · simp only [wSameSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wSameSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Ici.prod (isConnected_

中文:
定理 isConnected_setOfPred_wSameSide
  结论: {s : AffineSubspace 实数 P} (x : P)
  证明: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x in s
  · simp only [wSameSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wSameSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Ici.prod (isConnected_

Depends on / 依赖: AddTorsor, AddTorsor.connectedSpace, Nonempty, Set.image_prod, connectedSpace, continuousOn, continuous_const, continuous_fst, continuous_fst.smul, continuous_snd, convert, direction, image_prod, isConnected_Ici, isConnected_Ici.prod, isConnected_iff_connectedSpace, isConnected_univ, s.direction, setOfPred_wSameSide_eq_image2, wSameSide_of_left_mem
-/
theorem isConnected_setOfPred_wSameSide {s : AffineSubspace Real P} (x : P)
    (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WSameSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x in s
  · simp only [wSameSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wSameSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Ici.prod (isConnected_iff_connectedSpace.2 ?_)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
    convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_wSameSide := isConnected_setOfPred_wSameSide

/--
theorem `isPreconnected_setOfPred_wSameSide` / 定理 `isPreconnected_setOfPred_wSameSide`

English:
theorem isPreconnected_setOfPred_wSameSide
  given: (s : AffineSubspace Real P) (x : P)
  proof: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wSameSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wSameSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wSameSide :=

中文:
定理 isPreconnected_setOfPred_wSameSide
  条件: (s : AffineSubspace 实数 P) (x : P)
  证明: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wSameSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wSameSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wSameSide :=

Depends on / 依赖: Set.eq_empty_or_nonempty, coe_eq_bot_iff, eq_empty_or_nonempty, isConnected_setOfPred_wSameSide, isPreconnected, isPreconnected_empty, not_wSameSide_bot
-/
theorem isPreconnected_setOfPred_wSameSide (s : AffineSubspace Real P) (x : P) :
    IsPreconnected { y | s.WSameSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wSameSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wSameSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wSameSide := isPreconnected_setOfPred_wSameSide

/--
theorem `isConnected_setOfPred_sSameSide` / 定理 `isConnected_setOfPred_sSameSide`

English:
theorem isConnected_setOfPred_sSameSide
  statement: {s : AffineSubspace Real P} {x : P} (hx : x ∉ s)
  proof: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sSameSide_eq_image2 hx hp]; rw [← Set.image_prod]
  refine (isConnected_Ioi.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor

中文:
定理 isConnected_setOfPred_sSameSide
  结论: {s : AffineSubspace 实数 P} {x : P} (hx : x ∉ s)
  证明: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sSameSide_eq_image2 hx hp]; rw [← Set.image_prod]
  refine (isConnected_Ioi.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor

Depends on / 依赖: AddTorsor, AddTorsor.connectedSpace, Nonempty, Set.image_prod, connectedSpace, continuousOn, continuous_const, continuous_fst, continuous_fst.smul, continuous_snd, convert, direction, image_prod, isConnected_Ioi, isConnected_Ioi.prod, isConnected_iff_connectedSpace, s.direction, setOfPred_sSameSide_eq_image2
-/
theorem isConnected_setOfPred_sSameSide {s : AffineSubspace Real P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SSameSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sSameSide_eq_image2 hx hp]; rw [← Set.image_prod]
  refine (isConnected_Ioi.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sSameSide := isConnected_setOfPred_sSameSide

/--
theorem `isPreconnected_setOfPred_sSameSide` / 定理 `isPreconnected_setOfPred_sSameSide`

English:
theorem isPreconnected_setOfPred_sSameSide
  given: (s : AffineSubspace Real P) (x : P)
  proof: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sSameSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x in s
    · simp only [hx, SSameSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConn

中文:
定理 isPreconnected_setOfPred_sSameSide
  条件: (s : AffineSubspace 实数 P) (x : P)
  证明: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sSameSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x in s
    · simp only [hx, SSameSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConn

Depends on / 依赖: SSameSide, Set.eq_empty_or_nonempty, and_false, coe_eq_bot_iff, eq_empty_or_nonempty, false_and, isConnected_setOfPred_sSameSide, isPreconnected, isPreconnected_empty, not_sSameSide_bot, not_true
-/
theorem isPreconnected_setOfPred_sSameSide (s : AffineSubspace Real P) (x : P) :
    IsPreconnected { y | s.SSameSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sSameSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x in s
    · simp only [hx, SSameSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConnected_setOfPred_sSameSide hx h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_sSameSide := isPreconnected_setOfPred_sSameSide

/--
theorem `isConnected_setOfPred_wOppSide` / 定理 `isConnected_setOfPred_wOppSide`

English:
theorem isConnected_setOfPred_wOppSide
  given: {s : AffineSubspace Real P} (x : P) (h : (s : Set P).Nonempty)
  proof: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x in s
  · simp only [wOppSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wOppSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Iic.prod (isConnected_if

中文:
定理 isConnected_setOfPred_wOppSide
  条件: {s : AffineSubspace 实数 P} (x : P) (h : (s : Set P).Nonempty)
  证明: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x in s
  · simp only [wOppSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wOppSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Iic.prod (isConnected_if

Depends on / 依赖: AddTorsor, AddTorsor.connectedSpace, Nonempty, Set.image_prod, connectedSpace, continuousOn, continuous_const, continuous_fst, continuous_fst.smul, continuous_snd, convert, direction, image_prod, isConnected_Iic, isConnected_Iic.prod, isConnected_iff_connectedSpace, isConnected_univ, s.direction, setOfPred_wOppSide_eq_image2, wOppSide_of_left_mem
-/
theorem isConnected_setOfPred_wOppSide {s : AffineSubspace Real P} (x : P) (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WOppSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x in s
  · simp only [wOppSide_of_left_mem, hx]
    have := AddTorsor.connectedSpace V P
    exact isConnected_univ
  · rw [setOfPred_wOppSide_eq_image2 hx hp, ← Set.image_prod]
    refine (isConnected_Iic.prod (isConnected_iff_connectedSpace.2 ?_)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
    convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_wOppSide := isConnected_setOfPred_wOppSide

/--
theorem `isPreconnected_setOfPred_wOppSide` / 定理 `isPreconnected_setOfPred_wOppSide`

English:
theorem isPreconnected_setOfPred_wOppSide
  given: (s : AffineSubspace Real P) (x : P)
  proof: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wOppSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wOppSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wOppSide := is

中文:
定理 isPreconnected_setOfPred_wOppSide
  条件: (s : AffineSubspace 实数 P) (x : P)
  证明: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wOppSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wOppSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wOppSide := is

Depends on / 依赖: Set.eq_empty_or_nonempty, coe_eq_bot_iff, eq_empty_or_nonempty, isConnected_setOfPred_wOppSide, isPreconnected, isPreconnected_empty, not_wOppSide_bot
-/
theorem isPreconnected_setOfPred_wOppSide (s : AffineSubspace Real P) (x : P) :
    IsPreconnected { y | s.WOppSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_wOppSide_bot]
    exact isPreconnected_empty
  · exact (isConnected_setOfPred_wOppSide x h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_wOppSide := isPreconnected_setOfPred_wOppSide

/--
theorem `isConnected_setOfPred_sOppSide` / 定理 `isConnected_setOfPred_sOppSide`

English:
theorem isConnected_setOfPred_sOppSide
  statement: {s : AffineSubspace Real P} {x : P} (hx : x ∉ s)
  proof: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sOppSide_eq_image2 hx hp]; rw [← Set.image_prod]
  refine (isConnected_Iio.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor.

中文:
定理 isConnected_setOfPred_sOppSide
  结论: {s : AffineSubspace 实数 P} {x : P} (hx : x ∉ s)
  证明: by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sOppSide_eq_image2 hx hp]; rw [← Set.image_prod]
  refine (isConnected_Iio.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor.

Depends on / 依赖: AddTorsor, AddTorsor.connectedSpace, Nonempty, Set.image_prod, connectedSpace, continuousOn, continuous_const, continuous_fst, continuous_fst.smul, continuous_snd, convert, direction, image_prod, isConnected_Iio, isConnected_Iio.prod, isConnected_iff_connectedSpace, s.direction, setOfPred_sOppSide_eq_image2
-/
theorem isConnected_setOfPred_sOppSide {s : AffineSubspace Real P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SOppSide x y } := by
  obtain ⟨p, hp⟩ := h
  have : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [setOfPred_sOppSide_eq_image2 hx hp]; rw [← Set.image_prod]
  refine (isConnected_Iio.prod (isConnected_iff_connectedSpace.2 ?_)).image _
    ((continuous_fst.smul continuous_const).vadd continuous_snd).continuousOn
  convert! AddTorsor.connectedSpace s.direction s

@[deprecated (since := "2026-07-09")]
alias isConnected_setOf_sOppSide := isConnected_setOfPred_sOppSide

/--
theorem `isPreconnected_setOfPred_sOppSide` / 定理 `isPreconnected_setOfPred_sOppSide`

English:
theorem isPreconnected_setOfPred_sOppSide
  given: (s : AffineSubspace Real P) (x : P)
  proof: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sOppSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x in s
    · simp only [hx, SOppSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConnec

中文:
定理 isPreconnected_setOfPred_sOppSide
  条件: (s : AffineSubspace 实数 P) (x : P)
  证明: by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sOppSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x in s
    · simp only [hx, SOppSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConnec

Depends on / 依赖: SOppSide, Set.eq_empty_or_nonempty, and_false, coe_eq_bot_iff, eq_empty_or_nonempty, false_and, isConnected_setOfPred_sOppSide, isPreconnected, isPreconnected_empty, not_sOppSide_bot, not_true
-/
theorem isPreconnected_setOfPred_sOppSide (s : AffineSubspace Real P) (x : P) :
    IsPreconnected { y | s.SOppSide x y } := by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · rw [coe_eq_bot_iff] at h
    simp only [h, not_sOppSide_bot]
    exact isPreconnected_empty
  · by_cases hx : x in s
    · simp only [hx, SOppSide, not_true, false_and, and_false]
      exact isPreconnected_empty
    · exact (isConnected_setOfPred_sOppSide hx h).isPreconnected

@[deprecated (since := "2026-07-09")]
alias isPreconnected_setOf_sOppSide := isPreconnected_setOfPred_sOppSide

end Normed

end AffineSubspace

namespace Affine.Simplex

open AffineSubspace

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V]
variable [AddTorsor V P] {n : Nat} [NeZero n] (s : Simplex R P n)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sSameSide_affineSpan_faceOpposite_of_sign_eq` / 引理 `sSameSide_affineSpan_faceOpposite_of_sign_eq`

English:
lemma sSameSide_affineSpan_faceOpposite_of_sign_eq
  statement: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  proof: by
  have h0' : w₂ i != 0 := by intro h; simp_all
  refine ⟨?_, (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩
  obtain ⟨j, hj⟩ : exists j, j != i := exists_ne _
  have hj' : s.points j in affineSpan R (Set

中文:
引理 sSameSide_affineSpan_faceOpposite_of_sign_eq
  结论: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  证明: by
  have h0' : w₂ i != 0 := by intro h; simp_all
  refine ⟨?_, (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩
  obtain ⟨j, hj⟩ : exists j, j != i := exists_ne _
  have hj' : s.points j in affineSpan R (Set

Depends on / 依赖: Finset, Finset.affineCombination, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Set.range, affineCombination, affineCombination_mem_affineSpan_faceOpposite_iff, affineCombination_piSingle, affineSpan, exists_ne, faceOpposite, mem_univ, points, s.affineCombination_mem_affineSpan_faceOpposite_iff, s.faceOpposite, s.points, wSameSide_iff_exists_left
-/
lemma sSameSide_affineSpan_faceOpposite_of_sign_eq {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs : SignType.sign (w₁ i) = SignType.sign (w₂ i))
    (h0 : w₁ i != 0) :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) := by
  have h0' : w₂ i != 0 := by intro h; simp_all
  refine ⟨?_, (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩
  obtain ⟨j, hj⟩ : exists j, j != i := exists_ne _
  have hj' : s.points j in affineSpan R (Set.range (s.faceOpposite i).points) := by
    simpa using hj
  refine (wSameSide_iff_exists_left hj').2 (.inr ?_)
  rw [← Finset.univ.affineCombination_piSingle R s.points
    (Finset.mem_univ j)]; rw [Finset.affineCombination_vsub]
  let w₃ : Fin (n + 1) -> R :=
    w₂ - w₂ i • (w₁ i)⁻¹ • (w₁ - Pi.single j 1)
  have hw₃1 : ∑ k, w₃ k = 1 := by simp [w₃, hw₂, ← Finset.mul_sum, hw₁]
  have hw₃i : w₃ i = 0 := by simp [w₃, hj.symm, h0]
  refine ⟨Finset.univ.affineCombination R s.points w₃,
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₃1).2 hw₃i, ?_⟩
  simp only [w₃, Finset.affineCombination_vsub, sub_sub_cancel, smul_smul, map_smul,
    sameRay_smul_right_iff]
  left
  rcases h0.lt_or_gt with h | h
  · rw [sign_neg h, eq_comm, sign_eq_neg_one_iff] at hs
    exact (mul_pos_of_neg_of_neg hs (inv_neg''.2 h)).le
  · rw [sign_pos h, eq_comm, sign_eq_one_iff] at hs
    positivity

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sOppSide_affineSpan_faceOpposite_of_pos_of_neg` / 引理 `sOppSide_affineSpan_faceOpposite_of_pos_of_neg`

English:
lemma sOppSide_affineSpan_faceOpposite_of_pos_of_neg
  statement: {w₁ w₂ : Fin (n + 1) -> R}
  proof: by
  let w₃ : Fin (n + 1) -> R := lineMap w₁ w₂ (w₁ i / (w₁ i - w₂ i))
  have hp : 0 < w₁ i - w₂ i := by grind
  have hw₃ : ∑ j, w₃ j = 1 := by
    simp [w₃, lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum, hw₁, hw₂]
  have h : Sbtw R w₁ w₃ w₂ := sbtw_lineMap_iff.2
    ⟨(by grind), div_pos h

中文:
引理 sOppSide_affineSpan_faceOpposite_of_pos_of_neg
  结论: {w₁ w₂ : Fin (n + 1) -> R}
  证明: by
  let w₃ : Fin (n + 1) -> R := lineMap w₁ w₂ (w₁ i / (w₁ i - w₂ i))
  have hp : 0 < w₁ i - w₂ i := by grind
  have hw₃ : ∑ j, w₃ j = 1 := by
    simp [w₃, lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum, hw₁, hw₂]
  have h : Sbtw R w₁ w₃ w₂ := sbtw_lineMap_iff.2
    ⟨(by grind), div_pos h

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_add_distrib, Finset.univ.affineCombination, affineCombination, div_lt_one, div_pos, independent, lineMap, lineMap_apply, mul_sum, points, s.independent, s.points, sbtw_lineMap_iff, sum_add_distrib
-/
lemma sOppSide_affineSpan_faceOpposite_of_pos_of_neg {w₁ w₂ : Fin (n + 1) -> R}
    (hw₁ : ∑ j, w₁ j = 1) (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} (hs₁ : 0 < w₁ i)
    (hs₂ : w₂ i < 0) :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) := by
  let w₃ : Fin (n + 1) -> R := lineMap w₁ w₂ (w₁ i / (w₁ i - w₂ i))
  have hp : 0 < w₁ i - w₂ i := by grind
  have hw₃ : ∑ j, w₃ j = 1 := by
    simp [w₃, lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum, hw₁, hw₂]
  have h : Sbtw R w₁ w₃ w₂ := sbtw_lineMap_iff.2
    ⟨(by grind), div_pos hs₁ hp, (div_lt_one hp).2 (by grind)⟩
  have h' : Sbtw R (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₃)
      (Finset.univ.affineCombination R s.points w₂) := by
    rwa [s.independent.injOn_affineCombination_fintypeAffineCoords.sbtw_map_iff
     (mem_fintypeAffineCoords_iff_sum.2 hw₁) (mem_fintypeAffineCoords_iff_sum.2 hw₃)
     (mem_fintypeAffineCoords_iff_sum.2 hw₂)]
  refine h'.sOppSide_of_notMem_of_mem
    ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 hs₁.ne')
    ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₃).2 ?_)
  simp only [lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, w₃]
  rw [← neg_sub (w₁ i) (w₂ i)]; rw [mul_neg]; rw [div_mul_cancel₀ _ hp.ne']
  simp

/--
lemma `sSameSide_affineSpan_faceOpposite_iff` / 引理 `sSameSide_affineSpan_faceOpposite_iff`

English:
lemma sSameSide_affineSpan_faceOpposite_iff
  statement: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  proof: by
  refine ⟨fun h => ?_, fun ⟨hs, h0⟩ => s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ hs h0⟩
  have h0 : w₁ i != 0 :=
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
  refine ⟨?_, h0⟩
  have h0' : w₂ i != 0 :=
    (s.affineCombination_mem_affineSpan_faceO

中文:
引理 sSameSide_affineSpan_faceOpposite_iff
  结论: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  证明: by
  refine ⟨fun h => ?_, fun ⟨hs, h0⟩ => s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ hs h0⟩
  have h0 : w₁ i != 0 :=
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
  refine ⟨?_, h0⟩
  have h0' : w₂ i != 0 :=
    (s.affineCombination_mem_affineSpan_faceO

Depends on / 依赖: Ne.lt_or_gt, affineCombination_mem_affineSpan_faceOpposite_iff, eq_comm, h.left_notMem, h.right_notMem, left_notMem, lt_or_gt, neg_inj, right_notMem, s.affineCombination_mem_affineSpan_faceOpposite_iff, s.sOp, s.sSameSide_affineSpan_faceOpposite_of_sign_eq, sSameSide_affineSpan_faceOpposite_of_sign_eq, sign_eq_one_iff, sign_eq_sign_or_eq_neg, sign_neg
-/
lemma sSameSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = SignType.sign (w₂ i) ∧ w₁ i != 0 := by
  refine ⟨fun h => ?_, fun ⟨hs, h0⟩ => s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ hs h0⟩
  have h0 : w₁ i != 0 :=
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
  refine ⟨?_, h0⟩
  have h0' : w₂ i != 0 :=
    (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.1 h.right_notMem
  rcases sign_eq_sign_or_eq_neg h0 h0' with hs | hs
  · exact hs
  · exfalso
    rcases Ne.lt_or_gt h0 with h' | h'
    · rw [sign_neg h', neg_inj, eq_comm, sign_eq_one_iff] at hs
      exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg
        hw₂ hw₁ hs h').symm.wOppSide.not_sSameSide h
    · rw [sign_pos h', eq_comm, neg_eq_iff_eq_neg, sign_eq_neg_one_iff] at hs
      exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg
        hw₁ hw₂ h' hs).wOppSide.not_sSameSide h

/--
lemma `sOppSide_affineSpan_faceOpposite_iff` / 引理 `sOppSide_affineSpan_faceOpposite_iff`

English:
lemma sOppSide_affineSpan_faceOpposite_iff
  statement: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  proof: by
  refine ⟨fun h => ?_, fun ⟨hs, h0⟩ => ?_⟩
  · have h0 : w₁ i != 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
    refine ⟨?_, h0⟩
    have h0' : w₂ i != 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.1 h.right_notMem
    rcases

中文:
引理 sOppSide_affineSpan_faceOpposite_iff
  结论: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  证明: by
  refine ⟨fun h => ?_, fun ⟨hs, h0⟩ => ?_⟩
  · have h0 : w₁ i != 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
    refine ⟨?_, h0⟩
    have h0' : w₂ i != 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.1 h.right_notMem
    rcases

Depends on / 依赖: affineCombination_mem_affineSpan_faceOpposite_iff, eq_comm, h.left_notMem, h.right_notMem, h0.lt_or_gt, left_notMem, lt_or_gt, neg_inj, not_sOppSide, right_notMem, s.affineCombination_mem_affineSpan_faceOpposite_iff, s.sSameSide_affineSpan_faceOpposite_of_sign_eq, sSameSide_affineSpan_faceOpposite_of_sign_eq, sign_eq_sign_or_eq_neg, sign_neg, wSameSide, wSameSide.not_sOppSide
-/
lemma sOppSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = -SignType.sign (w₂ i) ∧ w₁ i != 0 := by
  refine ⟨fun h => ?_, fun ⟨hs, h0⟩ => ?_⟩
  · have h0 : w₁ i != 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.1 h.left_notMem
    refine ⟨?_, h0⟩
    have h0' : w₂ i != 0 :=
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.1 h.right_notMem
    rcases sign_eq_sign_or_eq_neg h0 h0' with hs | hs
    · exfalso
      exact (s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ hs h0).wSameSide.not_sOppSide h
    · exact hs
  · rcases h0.lt_or_gt with h' | h'
    · rw [sign_neg h', neg_inj, eq_comm, sign_eq_one_iff] at hs
      exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₂ hw₁ hs h').symm
    · rw [sign_pos h', eq_comm, neg_eq_iff_eq_neg, sign_eq_neg_one_iff] at hs
      exact s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₁ hw₂ h' hs

/--
lemma `wSameSide_affineSpan_faceOpposite_iff` / 引理 `wSameSide_affineSpan_faceOpposite_iff`

English:
lemma wSameSide_affineSpan_faceOpposite_iff
  statement: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sSameSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_

中文:
引理 wSameSide_affineSpan_faceOpposite_iff
  结论: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sSameSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_

Depends on / 依赖: affineCombination_mem_affineSpan_faceOpposite_iff, s.affineCombination_mem_affineSpan_faceOpposite_iff, s.sSameSide_affineSpan_faceOpposite_iff, sSameSide_affineSpan_faceOpposite_iff, wSameSide_of_left_mem, wSameSide_of_right_mem
-/
lemma wSameSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WSameSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = SignType.sign (w₂ i) ∨ w₁ i = 0 ∨ w₂ i = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sSameSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩).1
  · by_cases h0 : w₁ i = 0
    · exact wSameSide_of_left_mem _ ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).2 h0)
    · by_cases h0' : w₂ i = 0
      · exact wSameSide_of_right_mem _
          ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).2 h0')
      simp only [h0, h0', or_self, or_false] at h
      exact (s.sSameSide_affineSpan_faceOpposite_of_sign_eq hw₁ hw₂ h h0).wSameSide

/--
lemma `wOppSide_affineSpan_faceOpposite_iff` / 引理 `wOppSide_affineSpan_faceOpposite_iff`

English:
lemma wOppSide_affineSpan_faceOpposite_iff
  statement: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sOppSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_m

中文:
引理 wOppSide_affineSpan_faceOpposite_iff
  结论: {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sOppSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_m

Depends on / 依赖: affineCombination_mem_affineSpan_faceOpposite_iff, s.affineCombination_mem_affineSpan_faceOpposite_iff, s.sOppSide_affineSpan_faceOpposite_iff, sOppSide_affineSpan_faceOpposite_iff, wOppSide_of_left_mem, wOppSide_of_right_mem
-/
lemma wOppSide_affineSpan_faceOpposite_iff {w₁ w₂ : Fin (n + 1) -> R} (hw₁ : ∑ j, w₁ j = 1)
    (hw₂ : ∑ j, w₂ j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WOppSide
      (Finset.univ.affineCombination R s.points w₁)
      (Finset.univ.affineCombination R s.points w₂) ↔
        SignType.sign (w₁ i) = -SignType.sign (w₂ i) ∨ w₁ i = 0 ∨ w₂ i = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases h0 : w₁ i = 0
    · simp [h0]
    by_cases h0' : w₂ i = 0
    · simp [h0']
    exact .inl ((s.sOppSide_affineSpan_faceOpposite_iff hw₁ hw₂).1 ⟨h,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).not.2 h0,
      (s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).not.2 h0'⟩).1
  · by_cases h0 : w₁ i = 0
    · exact wOppSide_of_left_mem _ ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₁).2 h0)
    · by_cases h0' : w₂ i = 0
      · exact wOppSide_of_right_mem _
          ((s.affineCombination_mem_affineSpan_faceOpposite_iff hw₂).2 h0')
      simp only [h0, h0', or_self, or_false] at h
      rcases Ne.lt_or_gt h0 with h' | h'
      · rw [sign_neg h', neg_inj, eq_comm, sign_eq_one_iff] at h
        exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₂ hw₁ h h').symm.wOppSide
      · rw [sign_pos h', eq_comm, neg_eq_iff_eq_neg, sign_eq_neg_one_iff] at h
        exact (s.sOppSide_affineSpan_faceOpposite_of_pos_of_neg hw₁ hw₂ h' h).wOppSide

/--
lemma `sSameSide_affineSpan_faceOpposite_point_left_iff` / 引理 `sSameSide_affineSpan_faceOpposite_point_left_iff`

English:
lemma sSameSide_affineSpan_faceOpposite_point_left_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.sSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]
  simp [sign_eq_one_iff]

中文:
引理 sSameSide_affineSpan_faceOpposite_point_left_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.sSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]
  simp [sign_eq_one_iff]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Fintype, Fintype.sum_pi_single, affineCombination_piSingle, eq_comm, mem_univ, points, s.points, s.sSameSide_affineSpan_faceOpposite_iff, sSameSide_affineSpan_faceOpposite_iff, sign_eq_one_iff, sum_pi_single
-/
lemma sSameSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ 0 < w i := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.sSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]
  simp [sign_eq_one_iff]

/--
lemma `sSameSide_affineSpan_faceOpposite_point_right_iff` / 引理 `sSameSide_affineSpan_faceOpposite_point_right_iff`

English:
lemma sSameSide_affineSpan_faceOpposite_point_right_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [sSameSide_comm]; rw [s.sSameSide_affineSpan_faceOpposite_point_left_iff hw]

中文:
引理 sSameSide_affineSpan_faceOpposite_point_right_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [sSameSide_comm]; rw [s.sSameSide_affineSpan_faceOpposite_point_left_iff hw]

Depends on / 依赖: s.sSameSide_affineSpan_faceOpposite_point_left_iff, sSameSide_affineSpan_faceOpposite_point_left_iff, sSameSide_comm
-/
lemma sSameSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SSameSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ 0 < w i := by
  rw [sSameSide_comm]; rw [s.sSameSide_affineSpan_faceOpposite_point_left_iff hw]

/--
lemma `sOppSide_affineSpan_faceOpposite_point_left_iff` / 引理 `sOppSide_affineSpan_faceOpposite_point_left_iff`

English:
lemma sOppSide_affineSpan_faceOpposite_point_left_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.sOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]; rw [neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff]

中文:
引理 sOppSide_affineSpan_faceOpposite_point_left_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.sOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]; rw [neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Fintype, Fintype.sum_pi_single, affineCombination_piSingle, eq_comm, mem_univ, neg_eq_iff_eq_neg, points, s.points, s.sOppSide_affineSpan_faceOpposite_iff, sOppSide_affineSpan_faceOpposite_iff, sign_eq_neg_one_iff, sum_pi_single
-/
lemma sOppSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ w i < 0 := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.sOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]; rw [neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff]

/--
lemma `sOppSide_affineSpan_faceOpposite_point_right_iff` / 引理 `sOppSide_affineSpan_faceOpposite_point_right_iff`

English:
lemma sOppSide_affineSpan_faceOpposite_point_right_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [sOppSide_comm]; rw [s.sOppSide_affineSpan_faceOpposite_point_left_iff hw]

中文:
引理 sOppSide_affineSpan_faceOpposite_point_right_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [sOppSide_comm]; rw [s.sOppSide_affineSpan_faceOpposite_point_left_iff hw]

Depends on / 依赖: s.sOppSide_affineSpan_faceOpposite_point_left_iff, sOppSide_affineSpan_faceOpposite_point_left_iff, sOppSide_comm
-/
lemma sOppSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).SOppSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ w i < 0 := by
  rw [sOppSide_comm]; rw [s.sOppSide_affineSpan_faceOpposite_point_left_iff hw]

/--
lemma `wSameSide_affineSpan_faceOpposite_point_left_iff` / 引理 `wSameSide_affineSpan_faceOpposite_point_left_iff`

English:
lemma wSameSide_affineSpan_faceOpposite_point_left_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.wSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]
  simp [sign_eq_one_iff, le_iff_eq_or_lt', or_comm]

中文:
引理 wSameSide_affineSpan_faceOpposite_point_left_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.wSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]
  simp [sign_eq_one_iff, le_iff_eq_or_lt', or_comm]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Fintype, Fintype.sum_pi_single, affineCombination_piSingle, eq_comm, le_iff_eq_or_lt, mem_univ, or_comm, points, s.points, s.wSameSide_affineSpan_faceOpposite_iff, sign_eq_one_iff, sum_pi_single, wSameSide_affineSpan_faceOpposite_iff
-/
lemma wSameSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WSameSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ 0 <= w i := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.wSameSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]
  simp [sign_eq_one_iff, le_iff_eq_or_lt', or_comm]

/--
lemma `wSameSide_affineSpan_faceOpposite_point_right_iff` / 引理 `wSameSide_affineSpan_faceOpposite_point_right_iff`

English:
lemma wSameSide_affineSpan_faceOpposite_point_right_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [wSameSide_comm]; rw [s.wSameSide_affineSpan_faceOpposite_point_left_iff hw]

中文:
引理 wSameSide_affineSpan_faceOpposite_point_right_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [wSameSide_comm]; rw [s.wSameSide_affineSpan_faceOpposite_point_left_iff hw]

Depends on / 依赖: s.wSameSide_affineSpan_faceOpposite_point_left_iff, wSameSide_affineSpan_faceOpposite_point_left_iff, wSameSide_comm
-/
lemma wSameSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WSameSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ 0 <= w i := by
  rw [wSameSide_comm]; rw [s.wSameSide_affineSpan_faceOpposite_point_left_iff hw]

/--
lemma `wOppSide_affineSpan_faceOpposite_point_left_iff` / 引理 `wOppSide_affineSpan_faceOpposite_point_left_iff`

English:
lemma wOppSide_affineSpan_faceOpposite_point_left_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.wOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]; rw [neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff, le_iff_eq_or_lt, or_comm]

中文:
引理 wOppSide_affineSpan_faceOpposite_point_left_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.wOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]; rw [neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff, le_iff_eq_or_lt, or_comm]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Fintype, Fintype.sum_pi_single, affineCombination_piSingle, eq_comm, le_iff_eq_or_lt, mem_univ, neg_eq_iff_eq_neg, or_comm, points, s.points, s.wOppSide_affineSpan_faceOpposite_iff, sign_eq_neg_one_iff, sum_pi_single, wOppSide_affineSpan_faceOpposite_iff
-/
lemma wOppSide_affineSpan_faceOpposite_point_left_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WOppSide (s.points i)
      (Finset.univ.affineCombination R s.points w) ↔ w i <= 0 := by
  rw [← Finset.univ.affineCombination_piSingle R s.points (Finset.mem_univ i)]; rw [s.wOppSide_affineSpan_faceOpposite_iff (Fintype.sum_pi_single' _ _) hw]; rw [eq_comm]; rw [neg_eq_iff_eq_neg]
  simp [sign_eq_neg_one_iff, le_iff_eq_or_lt, or_comm]

/--
lemma `wOppSide_affineSpan_faceOpposite_point_right_iff` / 引理 `wOppSide_affineSpan_faceOpposite_point_right_iff`

English:
lemma wOppSide_affineSpan_faceOpposite_point_right_iff
  statement: {w : Fin (n + 1) -> R}
  proof: by
  rw [wOppSide_comm]; rw [s.wOppSide_affineSpan_faceOpposite_point_left_iff hw]

中文:
引理 wOppSide_affineSpan_faceOpposite_point_right_iff
  结论: {w : Fin (n + 1) -> R}
  证明: by
  rw [wOppSide_comm]; rw [s.wOppSide_affineSpan_faceOpposite_point_left_iff hw]

Depends on / 依赖: s.wOppSide_affineSpan_faceOpposite_point_left_iff, wOppSide_affineSpan_faceOpposite_point_left_iff, wOppSide_comm
-/
lemma wOppSide_affineSpan_faceOpposite_point_right_iff {w : Fin (n + 1) -> R}
    (hw : ∑ j, w j = 1) {i : Fin (n + 1)} :
    (affineSpan R (Set.range (s.faceOpposite i).points)).WOppSide
      (Finset.univ.affineCombination R s.points w) (s.points i) ↔ w i <= 0 := by
  rw [wOppSide_comm]; rw [s.wOppSide_affineSpan_faceOpposite_point_left_iff hw]

end Affine.Simplex
