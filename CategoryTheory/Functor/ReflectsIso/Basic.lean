/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Functors which reflect isomorphisms

A functor `F` reflects isomorphisms if whenever `F.map f` is an isomorphism, `f` was too.

It is formalized as a `Prop`-valued typeclass `ReflectsIsomorphisms F`.

Any fully faithful functor reflects isomorphisms.
-/

public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type*} [Category* C]
  {D : Type*} [Category* D]
  {E : Type*} [Category* E]

section ReflectsIso

/--
Definition of `Functor.ReflectsIsomorphisms` / `Functor.ReflectsIsomorphisms` 的定义

English:
class Functor.ReflectsIsomorphisms
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - reflects : forall {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f

中文:
类 函子.反映同构
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - reflects : 对任意 {A B : C} (f : A ⟶ B) [是同构 (F.map f)], 是同构 f
-/
class Functor.ReflectsIsomorphisms (F : C ⥤ D) : Prop where
  /-- For any `f`, if `F.map f` is an iso, then so was `f`. -/
  reflects : forall {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f

attribute [to_dual self] Functor.ReflectsIsomorphisms.reflects Functor.ReflectsIsomorphisms.mk

/--
theorem `isIso_of_reflects_iso` / 定理 `isIso_of_reflects_iso`

English:
theorem isIso_of_reflects_iso
  statement: {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)]
  proof: ReflectsIsomorphisms.reflects F f

中文:
定理 isIso_of_reflects_iso
  结论: {A B : C} (f : A ⟶ B) (F : C ⥤ D) [是同构 (F.map f)]
  证明: ReflectsIsomorphisms.reflects F f

Depends on / 依赖: ReflectsIsomorphisms, ReflectsIsomorphisms.reflects, reflects
-/
theorem isIso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)]
    [F.ReflectsIsomorphisms] : IsIso f :=
  ReflectsIsomorphisms.reflects F f

/--
lemma `isIso_iff_of_reflects_iso` / 引理 `isIso_iff_of_reflects_iso`

English:
lemma isIso_iff_of_reflects_iso
  given: {A B : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms]
  proof: ⟨fun _ => isIso_of_reflects_iso f F, fun _ => inferInstance⟩

中文:
引理 isIso_iff_of_reflects_iso
  条件: {A B : C} (f : A ⟶ B) (F : C ⥤ D) [F.反映同构]
  证明: ⟨fun _ => isIso_of_reflects_iso f F, fun _ => inferInstance⟩

Depends on / 依赖: isIso_of_reflects_iso
-/
lemma isIso_iff_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] :
    IsIso (F.map f) ↔ IsIso f :=
  ⟨fun _ => isIso_of_reflects_iso f F, fun _ => inferInstance⟩

/--
lemma `Functor.FullyFaithful.reflectsIsomorphisms` / 引理 `Functor.FullyFaithful.reflectsIsomorphisms`

English:
lemma Functor.FullyFaithful.reflectsIsomorphisms
  given: {F : C ⥤ D} (hF : F.FullyFaithful)
  proof: hF.isIso_of_isIso_map _

中文:
引理 函子.满忠实.reflectsIsomorphisms
  条件: {F : C ⥤ D} (hF : F.满忠实)
  证明: hF.isIso_of_isIso_map _

Depends on / 依赖: hF.isIso_of_isIso_map, isIso_of_isIso_map
-/
lemma Functor.FullyFaithful.reflectsIsomorphisms {F : C ⥤ D} (hF : F.FullyFaithful) :
    F.ReflectsIsomorphisms where
  reflects _ _ := hF.isIso_of_isIso_map _

instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful] :
    F.ReflectsIsomorphisms :=
  (Functor.FullyFaithful.ofFullyFaithful F).reflectsIsomorphisms

/--
Instance `reflectsIsomorphisms_comp` / 实例 `reflectsIsomorphisms_comp`

English:
instance reflectsIsomorphisms_comp
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: ⟨fun f (hf : IsIso (G.map _)) => by
    have := isIso_of_reflects_iso (F.map f) G
    exact isIso_of_reflects_iso f F⟩

中文:
实例 reflectsIsomorphisms_comp
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: ⟨fun f (hf : IsIso (G.map _)) => by
    have := isIso_of_reflects_iso (F.map f) G
    exact isIso_of_reflects_iso f F⟩

Depends on / 依赖: F.map, G.map, isIso_of_reflects_iso
-/
instance reflectsIsomorphisms_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.ReflectsIsomorphisms] [G.ReflectsIsomorphisms] :
    (F ⋙ G).ReflectsIsomorphisms :=
  ⟨fun f (hf : IsIso (G.map _)) => by
    have := isIso_of_reflects_iso (F.map f) G
    exact isIso_of_reflects_iso f F⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `reflectsIsomorphisms_of_comp` / 引理 `reflectsIsomorphisms_of_comp`

English:
lemma reflectsIsomorphisms_of_comp
  statement: (F : C ⥤ D) (G : D ⥤ E)
  proof: by
    rw [← isIso_iff_of_reflects_iso _ (F ⋙ G)]
    dsimp
    infer_instance

中文:
引理 reflectsIsomorphisms_of_comp
  结论: (F : C ⥤ D) (G : D ⥤ E)
  证明: by
    rw [← isIso_iff_of_reflects_iso _ (F ⋙ G)]
    dsimp
    infer_instance

Depends on / 依赖: infer_instance, isIso_iff_of_reflects_iso
-/
lemma reflectsIsomorphisms_of_comp (F : C ⥤ D) (G : D ⥤ E)
    [(F ⋙ G).ReflectsIsomorphisms] : F.ReflectsIsomorphisms where
  reflects f _ := by
    rw [← isIso_iff_of_reflects_iso _ (F ⋙ G)]
    dsimp
    infer_instance

instance (F : D ⥤ E) [F.ReflectsIsomorphisms] :
    ((whiskeringRight C D E).obj F).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    rw [← isIso_iff_of_reflects_iso _ F]
    change IsIso ((((whiskeringRight C D E).obj F).map f).app Z)
    infer_instance

/--
lemma `reflectsIsomorphisms_of_iso` / 引理 `reflectsIsomorphisms_of_iso`

English:
lemma reflectsIsomorphisms_of_iso
  given: {F G : C ⥤ D} (α : F ≅ G) [F.ReflectsIsomorphisms]
  proof: by
    rw [← isIso_iff_of_reflects_iso _ F]; rw [← NatIso.naturality_2 α f]
    infer_instance

中文:
引理 reflectsIsomorphisms_of_iso
  条件: {F G : C ⥤ D} (α : F ≅ G) [F.反映同构]
  证明: by
    rw [← isIso_iff_of_reflects_iso _ F]; rw [← NatIso.naturality_2 α f]
    infer_instance

Depends on / 依赖: NatIso, NatIso.naturality_2, infer_instance, isIso_iff_of_reflects_iso, naturality_2
-/
lemma reflectsIsomorphisms_of_iso {F G : C ⥤ D} (α : F ≅ G) [F.ReflectsIsomorphisms] :
    G.ReflectsIsomorphisms where
  reflects f _ := by
    rw [← isIso_iff_of_reflects_iso _ F]; rw [← NatIso.naturality_2 α f]
    infer_instance

/--
lemma `reflectsIsomorphisms_iso_iff` / 引理 `reflectsIsomorphisms_iso_iff`

English:
lemma reflectsIsomorphisms_iso_iff
  given: {F G : C ⥤ D} (α : F ≅ G)
  proof: ⟨fun _ => reflectsIsomorphisms_of_iso α,
  fun _ => reflectsIsomorphisms_of_iso α.symm⟩

中文:
引理 reflectsIsomorphisms_iso_iff
  条件: {F G : C ⥤ D} (α : F ≅ G)
  证明: ⟨fun _ => reflectsIsomorphisms_of_iso α,
  fun _ => reflectsIsomorphisms_of_iso α.symm⟩

Depends on / 依赖: reflectsIsomorphisms_of_iso
-/
lemma reflectsIsomorphisms_iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    F.ReflectsIsomorphisms ↔ G.ReflectsIsomorphisms :=
  ⟨fun _ => reflectsIsomorphisms_of_iso α,
  fun _ => reflectsIsomorphisms_of_iso α.symm⟩

end ReflectsIso

end CategoryTheory
