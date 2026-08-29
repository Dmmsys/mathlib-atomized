/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.MultiequalizerPullback
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Types.Set
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram

/-!
# Multicoequalizers in the category of types

Given `J : MultispanShape`, `d : MultispanIndex J (Type u)` and
`c : d.multispan.CoconeTypes`, we obtain a lemma `isMulticoequalizer_iff`
which gives a criteria for `c` to be a colimit (i.e. a multicoequalizer):
it restates in a more explicit manner the injectivity and surjectivity
conditions for the map `d.multispan.descColimitType c : d.multispan.ColimitType → c.pt`.

We deduce a definition `Set.isColimitOfMulticoequalizerDiagram` which shows
that given `X : Type u`, a `MulticoequalizerDiagram` in `Set X` gives
a multicoequalizer in the category of types.

-/

@[expose] public section

universe w w' u

namespace CategoryTheory.Functor.CoconeTypes

open Limits

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isMulticoequalizer_iff` / 引理 `isMulticoequalizer_iff`

English:
lemma isMulticoequalizer_iff
  statement: {J : MultispanShape.{w, w'}} {d : MultispanIndex J (Type u)}
  proof: by
  have (x : d.multispan.ColimitType) :
      exists (i : J.R) (a : d.right i), d.multispan.ιColimitType (.right i) a = x := by
    obtain ⟨(l | r), z, rfl⟩ := d.multispan.ιColimitType_jointly_surjective x
    · exact ⟨J.fst l, d.multispan.map (WalkingMultispan.Hom.fst l) z, by rw [ιColimitType_ma

中文:
引理 isMulticoequalizer_iff
  结论: {J : MultispanShape.{w, w'}} {d : MultispanIndex J (类型u)}
  证明: by
  have (x : d.multispan.ColimitType) :
      exists (i : J.R) (a : d.right i), d.multispan.ιColimitType (.right i) a = x := by
    obtain ⟨(l | r), z, rfl⟩ := d.multispan.ιColimitType_jointly_surjective x
    · exact ⟨J.fst l, d.multispan.map (WalkingMultispan.Hom.fst l) z, by rw [ιColimitType_ma

Depends on / 依赖: ColimitType, J.fst, WalkingMultispan, WalkingMultispan.Hom.fst, bijective, d.multispan, d.multispan.ColimitType, d.multispan.map, d.right, hc.bijective, multispan
-/
lemma isMulticoequalizer_iff {J : MultispanShape.{w, w'}} {d : MultispanIndex J (Type u)}
    (c : d.multispan.CoconeTypes) :
    c.IsColimit ↔
      (forall (i₁ i₂ : J.R) (x₁ : d.right i₁) (x₂ : d.right i₂),
        c.ι (.right i₁) x₁ = c.ι (.right i₂) x₂ ->
          d.multispan.ιColimitType (.right i₁) x₁ = d.multispan.ιColimitType (.right i₂) x₂) ∧
      (forall (x : c.pt), exists (i : J.R) (a : d.right i), c.ι (.right i) a = x) := by
  have (x : d.multispan.ColimitType) :
      exists (i : J.R) (a : d.right i), d.multispan.ιColimitType (.right i) a = x := by
    obtain ⟨(l | r), z, rfl⟩ := d.multispan.ιColimitType_jointly_surjective x
    · exact ⟨J.fst l, d.multispan.map (WalkingMultispan.Hom.fst l) z, by rw [ιColimitType_map]⟩
    · exact ⟨r, z, by simp⟩
  constructor
  · intro hc
    refine ⟨fun i₁ i₂ x₁ x₂ h => ?_, ?_⟩
    · simp only [← descColimitType_ιColimitType_apply] at h
      exact hc.bijective.1 h
    · intro x
      obtain ⟨y, rfl⟩ := hc.bijective.2 x
      obtain ⟨i, z, rfl⟩ := this y
      exact ⟨i, z, by simp⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun x₁ x₂ h => ?_, fun x => ?_⟩
    · obtain ⟨i₁, a₁, rfl⟩ := this x₁
      obtain ⟨i₂, a₂, rfl⟩ := this x₂
      exact h₁ _ _ _ _ h
    · obtain ⟨i, y, rfl⟩ := h₂ x
      exact ⟨d.multispan.ιColimitType (.right i) y, rfl⟩

end CategoryTheory.Functor.CoconeTypes

open CompleteLattice CategoryTheory Limits

namespace CategoryTheory.Limits.Types

variable {X : Type u} {ι : Type w} {A : Set X} {U : ι -> Set X} {V : ι -> ι -> Set X}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitOfMulticoequalizerDiagram` / `isColimitOfMulticoequalizerDiagram` 的定义

English:
definition isColimitOfMulticoequalizerDiagram
  body: by
  let e := (c.multispanIndex.map Set.functorToTypes).multispan
  apply _root_.Nonempty.some
  rw [Types.isColimit_iff_coconeTypesIsColimit]; rw [Functor.CoconeTypes.isMulticoequalizer_iff]
  refine ⟨fun i₁ i₂ ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h => ?_, fun ⟨x, hx⟩ => ?_⟩
  · dsimp at i₁ i₂ h₁ h₂
    obtain rfl : 

中文:
定义 isColimitOfMulticoequalizerDiagram
  定义体: by
  let e := (c.multispanIndex.map Set.functorToTypes).multispan
  apply _root_.Nonempty.some
  rw [Types.isColimit_iff_coconeTypesIsColimit]; rw [Functor.CoconeTypes.isMulticoequalizer_iff]
  refine ⟨fun i₁ i₂ ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h => ?_, fun ⟨x, hx⟩ => ?_⟩
  · dsimp at i₁ i₂ h₁ h₂
    obtain rfl : 

Depends on / 依赖: CoconeTypes, Functor, Functor.CoconeTypes.isMulticoequalizer_iff, Nonempty, Set.functorToTypes, Types.isColimit_iff_coconeTypesIsColimit, WalkingMultispan, WalkingMultispan.Hom.fst, WalkingMultispan.Hom.snd, _root_, _root_.Nonempty.some, c.eq_inf, c.multispanIndex.map, eq_inf, functorToTypes, isColimit_iff_coconeTypesIsColimit, isMulticoequalizer_iff, multispan, multispanIndex
-/
noncomputable def isColimitOfMulticoequalizerDiagram
    (c : MulticoequalizerDiagram A U V) :
    IsColimit (c.multicofork.map Set.functorToTypes) := by
  let e := (c.multispanIndex.map Set.functorToTypes).multispan
  apply _root_.Nonempty.some
  rw [Types.isColimit_iff_coconeTypesIsColimit]; rw [Functor.CoconeTypes.isMulticoequalizer_iff]
  refine ⟨fun i₁ i₂ ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h => ?_, fun ⟨x, hx⟩ => ?_⟩
  · dsimp at i₁ i₂ h₁ h₂
    obtain rfl : x₁ = x₂ := by simpa using h
    have eq₁ := e.ιColimitType_map (WalkingMultispan.Hom.fst (J := .prod ι) ⟨i₁, i₂⟩)
      ⟨x₁, by dsimp; rw [c.eq_inf]; exact ⟨h₁, h₂⟩⟩
    have eq₂ := e.ιColimitType_map (WalkingMultispan.Hom.snd (J := .prod ι) ⟨i₁, i₂⟩)
      ⟨x₁, by dsimp; rw [c.eq_inf]; exact ⟨h₁, h₂⟩⟩
    dsimp [e] at eq₁ eq₂
    rw [eq₁]; rw [eq₂]
  · simp only [MulticoequalizerDiagram.multicofork_pt, ← c.iSup_eq,
      Set.iSup_eq_iUnion, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitOfMulticoequalizerDiagram'` / `isColimitOfMulticoequalizerDiagram'` 的定义

English:
definition isColimitOfMulticoequalizerDiagram'
  signature: [LinearOrder ι]
  body: Multicofork.isColimitToLinearOrder _ (isColimitOfMulticoequalizerDiagram c)
    { iso i j := Set.functorToTypes.mapIso (eqToIso (by
        dsimp
        rw [c.eq_inf]; rw [c.eq_inf]; rw [inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

中文:
定义 isColimitOfMulticoequalizerDiagram'
  签名: [LinearOrder ι]
  定义体: Multicofork.isColimitToLinearOrder _ (isColimitOfMulticoequalizerDiagram c)
    { iso i j := Set.functorToTypes.mapIso (eqToIso (by
        dsimp
        rw [c.eq_inf]; rw [c.eq_inf]; rw [inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

Depends on / 依赖: Multicofork, Multicofork.isColimitToLinearOrder, Set.functorToTypes.mapIso, c.eq_inf, eqToIso, eq_inf, fst_eq_snd, functorToTypes, inf_comm, isColimitOfMulticoequalizerDiagram, isColimitToLinearOrder, iso_hom_fst, iso_hom_snd, mapIso
-/
noncomputable def isColimitOfMulticoequalizerDiagram' [LinearOrder ι]
    (c : MulticoequalizerDiagram A U V) :
    IsColimit (c.multicofork.toLinearOrder.map Set.functorToTypes) :=
  Multicofork.isColimitToLinearOrder _ (isColimitOfMulticoequalizerDiagram c)
    { iso i j := Set.functorToTypes.mapIso (eqToIso (by
        dsimp
        rw [c.eq_inf]; rw [c.eq_inf]; rw [inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

/--
lemma `isPushout_of_bicartSq` / 引理 `isPushout_of_bicartSq`

English:
lemma isPushout_of_bicartSq
  given: {S₁ S₂ S₃ S₄ : Set X} (h : Lattice.BicartSq S₁ S₂ S₃ S₄)
  proof: Multicofork.IsColimit.isPushout _ (by ext (_ | _) <;> tauto) (by tauto)
    (isColimitOfMulticoequalizerDiagram' h.multicoequalizerDiagram)

中文:
引理 isPushout_of_bicartSq
  条件: {S₁ S₂ S₃ S₄ : Set X} (h : Lattice.BicartSq S₁ S₂ S₃ S₄)
  证明: Multicofork.IsColimit.isPushout _ (by ext (_ | _) <;> tauto) (by tauto)
    (isColimitOfMulticoequalizerDiagram' h.multicoequalizerDiagram)

Depends on / 依赖: IsColimit, Multicofork, Multicofork.IsColimit.isPushout, h.multicoequalizerDiagram, isColimitOfMulticoequalizerDiagram, isPushout, multicoequalizerDiagram
-/
lemma isPushout_of_bicartSq {S₁ S₂ S₃ S₄ : Set X} (h : Lattice.BicartSq S₁ S₂ S₃ S₄) :
    IsPushout (Set.functorToTypes.map (homOfLE h.le₁₂))
      (Set.functorToTypes.map (homOfLE h.le₁₃))
      (Set.functorToTypes.map (homOfLE h.le₂₄))
      (Set.functorToTypes.map (homOfLE h.le₃₄)) :=
  Multicofork.IsColimit.isPushout _ (by ext (_ | _) <;> tauto) (by tauto)
    (isColimitOfMulticoequalizerDiagram' h.multicoequalizerDiagram)

end CategoryTheory.Limits.Types
