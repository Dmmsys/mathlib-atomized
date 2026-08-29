/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Logic.Function.FiberPartition
/-!

This file provides some API surrounding `Function.Fiber` (see
`Mathlib/Logic/Function/FiberPartition.lean`) in the presence of a topology on the domain of the
function.

Note: this API is designed to be useful when defining the counit of the adjunction between
the functor which takes a set to the condensed set corresponding to locally constant maps to that
set, and the forgetful functor from the category of condensed sets to the category of sets
(see PR https://github.com/leanprover-community/mathlib4/pull/14027).
-/

@[expose] public section


open Function

variable {S Y : Type*} (f : S -> Y)

namespace TopologicalSpace.Fiber

variable [TopologicalSpace S]

/-- The canonical map from the disjoint union induced by `f` to `S`. -/
@[simps apply]
/--
Definition of `sigmaIsoHom` / `sigmaIsoHom` 的定义

English:
definition sigmaIsoHom
  signature: : C((x : Fiber f) × x.val, S) where
  body: continuous_sigma (by fun_prop)

中文:
定义 sigmaIsoHom
  签名: : C((x : Fiber f) × x.val, S) where
  定义体: continuous_sigma (by fun_prop)

Depends on / 依赖: continuous_sigma, fun_prop
-/
def sigmaIsoHom : C((x : Fiber f) × x.val, S) where
  toFun | ⟨a, x⟩ => x.val
  continuous_toFun := continuous_sigma (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sigmaIsoHom_inj` / 引理 `sigmaIsoHom_inj`

English:
lemma sigmaIsoHom_inj
  statement: Function.Injective (sigmaIsoHom f)
  proof: by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaIsoHom_apply] at h
  rw [Set.mem_preimage]; rw [Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]

中文:
引理 sigmaIsoHom_inj
  结论: 函数.单射 (sigmaIsoHom f)
  证明: by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaIsoHom_apply] at h
  rw [Set.mem_preimage]; rw [Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]

Depends on / 依赖: Set.mem_preimage, Set.mem_singleton_iff, Sigma.subtype_ext, mem_preimage, mem_singleton_iff, sigmaIsoHom_apply, subtype_ext
-/
lemma sigmaIsoHom_inj : Function.Injective (sigmaIsoHom f) := by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaIsoHom_apply] at h
  rw [Set.mem_preimage]; rw [Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]

/--
lemma `sigmaIsoHom_surj` / 引理 `sigmaIsoHom_surj`

English:
lemma sigmaIsoHom_surj
  statement: Function.Surjective (sigmaIsoHom f)
  proof: fun _ => ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

中文:
引理 sigmaIsoHom_surj
  结论: 函数.满射 (sigmaIsoHom f)
  证明: fun _ => ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

Depends on / 依赖: Set.mem_range_self, mem_range_self
-/
lemma sigmaIsoHom_surj : Function.Surjective (sigmaIsoHom f) :=
  fun _ => ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

/--
Definition of `sigmaIncl` / `sigmaIncl` 的定义

English:
definition sigmaIncl
  signature: (a : Fiber f)
  body: x.val

中文:
定义 sigmaIncl
  签名: (a : Fiber f)
  定义体: x.val

Depends on / 依赖: x.val
-/
def sigmaIncl (a : Fiber f) : C(a.val, S) where
  toFun x := x.val

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sigmaInclIncl` / `sigmaInclIncl` 的定义

English:
definition sigmaInclIncl
  signature: {X : Type*} (g : Y -> X) (a : Fiber (g ∘ f))
  body: ⟨x.val.val, by
    have := x.prop
    simp only [sigmaIncl, ContinuousMap.coe_mk, Fiber.mem_iff_eq_image, comp_apply] at this
    rw [Fiber.mem_iff_eq_image]; rw [Fiber.mk_image]; rw [this]; rw [← Fiber.map_preimage_eq_image]
    simp [sigmaIncl]⟩

中文:
定义 sigmaInclIncl
  签名: {X : 类型} (g : Y -> X) (a : Fiber (g ∘ f))
  定义体: ⟨x.val.val, by
    have := x.prop
    simp only [sigmaIncl, ContinuousMap.coe_mk, Fiber.mem_iff_eq_image, comp_apply] at this
    rw [Fiber.mem_iff_eq_image]; rw [Fiber.mk_image]; rw [this]; rw [← Fiber.map_preimage_eq_image]
    simp [sigmaIncl]⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Fiber.map_preimage_eq_image, Fiber.mem_iff_eq_image, Fiber.mk_image, coe_mk, comp_apply, map_preimage_eq_image, mem_iff_eq_image, mk_image, sigmaIncl, x.prop, x.val.val
-/
def sigmaInclIncl {X : Type*} (g : Y -> X) (a : Fiber (g ∘ f))
    (b : Fiber (f ∘ (sigmaIncl (g ∘ f) a))) :
    C(b.val, (Fiber.mk f (b.preimage).val).val) where
  toFun x := ⟨x.val.val, by
    have := x.prop
    simp only [sigmaIncl, ContinuousMap.coe_mk, Fiber.mem_iff_eq_image, comp_apply] at this
    rw [Fiber.mem_iff_eq_image]; rw [Fiber.mk_image]; rw [this]; rw [← Fiber.map_preimage_eq_image]
    simp [sigmaIncl]⟩

variable (l : LocallyConstant S Y) [CompactSpace S]

instance (x : Fiber l) : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  rw [← isCompact_iff_compactSpace]; rw [← hy]
  exact (l.2.isClosed_fiber _).isCompact

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite (Fiber l)
  body: have : Finite (Set.range l) := l.range_finite
  Finite.Set.finite_range _

中文:
实例 :
  签名: 有限 (Fiber l)
  定义体: have : Finite (Set.range l) := l.range_finite
  Finite.Set.finite_range _

Depends on / 依赖: Finite, Finite.Set.finite_range, Set.range, finite_range, l.range_finite, range_finite
-/
instance : Finite (Fiber l) :=
  have : Finite (Set.range l) := l.range_finite
  Finite.Set.finite_range _

end TopologicalSpace.Fiber
