/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.WellPowered

/-!
# `Type u` is well-powered

By building a categorical equivalence `MonoOver α ≌ Set α` for any `α : Type u`,
we deduce that `Subobject α ≃o Set α` and that `Type u` is well-powered.

One would hope that for a particular concrete category `C` (`AddCommGroup`, etc)
it's viable to prove `[WellPowered C]` without explicitly aligning `Subobject X`
with the "hand-rolled" definition of subobjects.

This may be possible using Lawvere theories,
but it remains to be seen whether this just pushes lumps around in the carpet.
-/

@[expose] public section


universe u

open CategoryTheory ConcreteCategory

open CategoryTheory.Subobject

/--
theorem `subtype_val_mono` / 定理 `subtype_val_mono`

English:
theorem subtype_val_mono
  given: {α : Type u} (s : Set α)
  statement: Mono (↾(Subtype.val : s -> α))
  proof: (mono_iff_injective _).mpr Subtype.val_injective

中文:
定理 subtype_val_mono
  条件: {α : 类型u} (s : 集合 α)
  结论: 单态射 (↾(子类型.val : s -> α))
  证明: (mono_iff_injective _).mpr Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val_injective, mono_iff_injective, val_injective
-/
theorem subtype_val_mono {α : Type u} (s : Set α) : Mono (↾(Subtype.val : s -> α)) :=
  (mono_iff_injective _).mpr Subtype.val_injective

attribute [local instance] subtype_val_mono

/-- The category of `MonoOver α`, for `α : Type u`, is equivalent to the partial order `Set α`.
-/
@[simps]
/--
Definition of `Types.monoOverEquivalenceSet` / `Types.monoOverEquivalenceSet` 的定义

English:
definition Types.monoOverEquivalenceSet
  signature: (α : Type u)
  body: { obj := fun f => Set.range f.1.hom
      map := fun {f g} t =>
        homOfLE
          (by
            rintro a ⟨x, rfl⟩
            exact ⟨t.hom.1 x, congr_hom t.hom.w x⟩) }
  inverse :=
    { obj := fun s => MonoOver.mk <| ↾(Subtype.val : s -> α)
      map := fun {s t} b => MonoOver.homMk (↾
  

中文:
定义 Types.monoOverEquivalenceSet
  签名: (α : 类型u)
  定义体: { obj := fun f => Set.range f.1.hom
      map := fun {f g} t =>
        homOfLE
          (by
            rintro a ⟨x, rfl⟩
            exact ⟨t.hom.1 x, congr_hom t.hom.w x⟩) }
  inverse :=
    { obj := fun s => MonoOver.mk <| ↾(Subtype.val : s -> α)
      map := fun {s t} b => MonoOver.homMk (↾
  

Depends on / 依赖: Equiv.ofInjective, MonoOver, MonoOver.homMk, MonoOver.isoMk, MonoOver.mk, NatIso, NatIso.ofComponents, Set.mem_of_mem_of_subset, Set.range, Subtype, Subtype.range_val, Subtype.val, b.le, congr_hom, counitIso, eqToIso, homOfLE, inverse, mem_of_mem_of_subset, mono_iff_injective
-/
noncomputable def Types.monoOverEquivalenceSet (α : Type u) : MonoOver α ≌ Set α where
  functor :=
    { obj := fun f => Set.range f.1.hom
      map := fun {f g} t =>
        homOfLE
          (by
            rintro a ⟨x, rfl⟩
            exact ⟨t.hom.1 x, congr_hom t.hom.w x⟩) }
  inverse :=
    { obj := fun s => MonoOver.mk <| ↾(Subtype.val : s -> α)
      map := fun {s t} b => MonoOver.homMk (↾
        fun w => ⟨w.1, Set.mem_of_mem_of_subset w.2 b.le⟩) }
  unitIso :=
    NatIso.ofComponents fun f =>
      MonoOver.isoMk (Equiv.ofInjective f.1.hom ((mono_iff_injective _).mp f.2)).toIso
  counitIso := NatIso.ofComponents fun _ => eqToIso Subtype.range_val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellPowered.{u} (Type u)
  body: wellPowered_of_essentiallySmall_monoOver fun α =>
    EssentiallySmall.mk' (Types.monoOverEquivalenceSet α)

中文:
实例 :
  签名: 良幂.{u} (类型u)
  定义体: wellPowered_of_essentiallySmall_monoOver fun α =>
    EssentiallySmall.mk' (Types.monoOverEquivalenceSet α)

Depends on / 依赖: EssentiallySmall, EssentiallySmall.mk, Types.monoOverEquivalenceSet, monoOverEquivalenceSet, wellPowered_of_essentiallySmall_monoOver
-/
instance : WellPowered.{u} (Type u) :=
  wellPowered_of_essentiallySmall_monoOver fun α =>
    EssentiallySmall.mk' (Types.monoOverEquivalenceSet α)

/--
Definition of `Types.subobjectEquivSet` / `Types.subobjectEquivSet` 的定义

English:
definition Types.subobjectEquivSet
  signature: (α : Type u)
  body: (Types.monoOverEquivalenceSet α).thinSkeletonOrderIso

中文:
定义 Types.subobjectEquivSet
  签名: (α : 类型u)
  定义体: (Types.monoOverEquivalenceSet α).thinSkeletonOrderIso

Depends on / 依赖: Types.monoOverEquivalenceSet, monoOverEquivalenceSet, thinSkeletonOrderIso
-/
noncomputable def Types.subobjectEquivSet (α : Type u) : Subobject α ≃o Set α :=
  (Types.monoOverEquivalenceSet α).thinSkeletonOrderIso
