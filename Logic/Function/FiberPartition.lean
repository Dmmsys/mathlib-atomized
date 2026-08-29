/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Data.Set.Insert
/-!

This file defines the type `f.Fiber` of fibers of a function `f : Y → Z`, and provides some API
to work with and construct terms of this type.

Note: this API is designed to be useful when defining the counit of the adjunction between
the functor which takes a set to the condensed set corresponding to locally constant maps to that
set, and the forgetful functor from the category of condensed sets to the category of sets
(see PR https://github.com/leanprover-community/mathlib4/pull/14027).
-/

@[expose] public section

assert_not_exists RelIso

variable {X Y Z : Type*}

namespace Function

/--
Definition of `Fiber` / `Fiber` 的定义

English:
definition Fiber
  signature: (f : Y -> Z)
  body: Set.range (fun (x : Set.range f) => f ⁻¹' {x.val})

中文:
定义 Fiber
  签名: (f : Y -> Z)
  定义体: Set.range (fun (x : Set.range f) => f ⁻¹' {x.val})

Depends on / 依赖: Set.range, x.val
-/
def Fiber (f : Y -> Z) : Type _ := Set.range (fun (x : Set.range f) => f ⁻¹' {x.val})

namespace Fiber

/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: (f : Y -> Z) (a : Fiber f)
  body: a.2.choose.1

中文:
定义 image
  签名: (f : Y -> Z) (a : Fiber f)
  定义体: a.2.choose.1
-/
noncomputable def image (f : Y -> Z) (a : Fiber f) : Z := a.2.choose.1

/--
lemma `eq_fiber_image` / 引理 `eq_fiber_image`

English:
lemma eq_fiber_image
  given: (f : Y -> Z) (a : Fiber f)
  statement: a.1 = f ⁻¹' {a.image}
  proof: a.2.choose_spec.symm

中文:
引理 eq_fiber_image
  条件: (f : Y -> Z) (a : Fiber f)
  结论: a.1 = f ⁻¹' {a.image}
  证明: a.2.choose_spec.symm

Depends on / 依赖: choose_spec, choose_spec.symm
-/
lemma eq_fiber_image (f : Y -> Z) (a : Fiber f) : a.1 = f ⁻¹' {a.image} := a.2.choose_spec.symm

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (f : Y -> Z) (y : Y)
  body: ⟨f ⁻¹' {f y}, by simp⟩

中文:
定义 mk
  签名: (f : Y -> Z) (y : Y)
  定义体: ⟨f ⁻¹' {f y}, by simp⟩
-/
def mk (f : Y -> Z) (y : Y) : Fiber f := ⟨f ⁻¹' {f y}, by simp⟩

/--
Definition of `mkSelf` / `mkSelf` 的定义

English:
definition mkSelf
  signature: (f : Y -> Z) (y : Y)
  body: ⟨y, rfl⟩

中文:
定义 mkSelf
  签名: (f : Y -> Z) (y : Y)
  定义体: ⟨y, rfl⟩
-/
def mkSelf (f : Y -> Z) (y : Y) : (mk f y).val := ⟨y, rfl⟩

/--
lemma `map_eq_image` / 引理 `map_eq_image`

English:
lemma map_eq_image
  given: (f : Y -> Z) (a : Fiber f) (x : a.1)
  statement: f x = a.image
  proof: by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff]; rw [← Set.mem_preimage]
  convert! x.prop

中文:
引理 map_eq_image
  条件: (f : Y -> Z) (a : Fiber f) (x : a.1)
  结论: f x = a.image
  证明: by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff]; rw [← Set.mem_preimage]
  convert! x.prop

Depends on / 依赖: Set.mem_preimage, Set.mem_singleton_iff, choose_spec, convert, mem_preimage, mem_singleton_iff, x.prop
-/
lemma map_eq_image (f : Y -> Z) (a : Fiber f) (x : a.1) : f x = a.image := by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff]; rw [← Set.mem_preimage]
  convert! x.prop

/--
lemma `mk_image` / 引理 `mk_image`

English:
lemma mk_image
  given: (f : Y -> Z) (y : Y)
  statement: (Fiber.mk f y).image = f y
  proof: (map_eq_image (x := mkSelf f y)).symm

中文:
引理 mk_image
  条件: (f : Y -> Z) (y : Y)
  结论: (Fiber.mk f y).image = f y
  证明: (map_eq_image (x := mkSelf f y)).symm

Depends on / 依赖: map_eq_image, mkSelf
-/
lemma mk_image (f : Y -> Z) (y : Y) : (Fiber.mk f y).image = f y :=
  (map_eq_image (x := mkSelf f y)).symm

/--
lemma `mem_iff_eq_image` / 引理 `mem_iff_eq_image`

English:
lemma mem_iff_eq_image
  given: (f : Y -> Z) (y : Y) (a : Fiber f)
  statement: y in a.val ↔ f y = a.image
  proof: ⟨fun h => a.map_eq_image _ ⟨y, h⟩, fun h => by rw [a.eq_fiber_image]; exact h⟩

中文:
引理 mem_iff_eq_image
  条件: (f : Y -> Z) (y : Y) (a : Fiber f)
  结论: y in a.val ↔ f y = a.image
  证明: ⟨fun h => a.map_eq_image _ ⟨y, h⟩, fun h => by rw [a.eq_fiber_image]; exact h⟩

Depends on / 依赖: a.eq_fiber_image, a.map_eq_image, eq_fiber_image, map_eq_image
-/
lemma mem_iff_eq_image (f : Y -> Z) (y : Y) (a : Fiber f) : y in a.val ↔ f y = a.image :=
  ⟨fun h => a.map_eq_image _ ⟨y, h⟩, fun h => by rw [a.eq_fiber_image]; exact h⟩

/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (f : Y -> Z) (a : Fiber f)
  body: a.2.choose.2.choose

中文:
定义 preimage
  签名: (f : Y -> Z) (a : Fiber f)
  定义体: a.2.choose.2.choose
-/
noncomputable def preimage (f : Y -> Z) (a : Fiber f) : Y := a.2.choose.2.choose

/--
lemma `map_preimage_eq_image` / 引理 `map_preimage_eq_image`

English:
lemma map_preimage_eq_image
  given: (f : Y -> Z) (a : Fiber f)
  statement: f a.preimage = a.image
  proof: a.2.choose.2.choose_spec

中文:
引理 map_preimage_eq_image
  条件: (f : Y -> Z) (a : Fiber f)
  结论: f a.preimage = a.image
  证明: a.2.choose.2.choose_spec

Depends on / 依赖: choose_spec
-/
lemma map_preimage_eq_image (f : Y -> Z) (a : Fiber f) : f a.preimage = a.image :=
  a.2.choose.2.choose_spec

/--
lemma `fiber_nonempty` / 引理 `fiber_nonempty`

English:
lemma fiber_nonempty
  given: (f : Y -> Z) (a : Fiber f)
  statement: Set.Nonempty a.val
  proof: by
  refine ⟨preimage f a, ?_⟩
  rw [mem_iff_eq_image]; rw [← map_preimage_eq_image]

中文:
引理 fiber_nonempty
  条件: (f : Y -> Z) (a : Fiber f)
  结论: Set.Nonempty a.val
  证明: by
  refine ⟨preimage f a, ?_⟩
  rw [mem_iff_eq_image]; rw [← map_preimage_eq_image]

Depends on / 依赖: map_preimage_eq_image, mem_iff_eq_image, preimage
-/
lemma fiber_nonempty (f : Y -> Z) (a : Fiber f) : Set.Nonempty a.val := by
  refine ⟨preimage f a, ?_⟩
  rw [mem_iff_eq_image]; rw [← map_preimage_eq_image]

/--
lemma `map_preimage_eq_image_map` / 引理 `map_preimage_eq_image_map`

English:
lemma map_preimage_eq_image_map
  given: {W : Type*} (f : Y -> Z) (g : Z -> W) (a : Fiber (g ∘ f))
  proof: by rw [← map_preimage_eq_image, comp_apply]

中文:
引理 map_preimage_eq_image_map
  条件: {W : 类型} (f : Y -> Z) (g : Z -> W) (a : Fiber (g ∘ f))
  证明: by rw [← map_preimage_eq_image, comp_apply]

Depends on / 依赖: comp_apply, map_preimage_eq_image
-/
lemma map_preimage_eq_image_map {W : Type*} (f : Y -> Z) (g : Z -> W) (a : Fiber (g ∘ f)) :
    g (f a.preimage) = a.image := by rw [← map_preimage_eq_image, comp_apply]

/--
lemma `image_eq_image_mk` / 引理 `image_eq_image_mk`

English:
lemma image_eq_image_mk
  given: (f : Y -> Z) (g : X -> Y) (a : Fiber (f ∘ g))
  proof: by
  rw [← map_preimage_eq_image_map _ _ a]; rw [mk_image]

中文:
引理 image_eq_image_mk
  条件: (f : Y -> Z) (g : X -> Y) (a : Fiber (f ∘ g))
  证明: by
  rw [← map_preimage_eq_image_map _ _ a]; rw [mk_image]

Depends on / 依赖: map_preimage_eq_image_map, mk_image
-/
lemma image_eq_image_mk (f : Y -> Z) (g : X -> Y) (a : Fiber (f ∘ g)) :
    a.image = (Fiber.mk f (g (a.preimage _))).image := by
  rw [← map_preimage_eq_image_map _ _ a]; rw [mk_image]

end Function.Fiber
