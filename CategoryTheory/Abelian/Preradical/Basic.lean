/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Preradicals

A **preradical** on an abelian category `C` is a monomorphism in the functor category `C ⥤ C`
with codomain `𝟭 C`, i.e. an element of `MonoOver (𝟭 C)`.

## Main definitions

* `Preradical C`: The type of preradicals on `C`.
* `Preradical.r`: The underlying endofunctor of a `Preradical`.
* `Preradical.ι`: The structure morphism of a `Preradical`.
* `Preradical.IsIdempotent`: The predicate expressing idempotence.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

public section

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (C) in
/--
Definition of `Preradical` / `Preradical` 的定义

English:
abbreviation Preradical
  body: MonoOver (𝟭 C)

中文:
缩写 Preradical
  定义体: MonoOver (𝟭 C)

Depends on / 依赖: MonoOver
-/
abbrev Preradical := MonoOver (𝟭 C)

namespace Preradical

variable (Φ : Preradical C)

/--
Definition of `r` / `r` 的定义

English:
abbreviation r
  signature: : C ⥤ C
  body: Φ.obj.left

中文:
缩写 r
  签名: : C ⥤ C
  定义体: Φ.obj.left

Depends on / 依赖: obj.left
-/
abbrev r : C ⥤ C := Φ.obj.left

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : Φ.r ⟶ 𝟭 C
  body: Φ.obj.hom

@[simp]

中文:
缩写 ι
  签名: : Φ.r ⟶ 𝟭 C
  定义体: Φ.obj.hom

@[simp]

Depends on / 依赖: obj.hom
-/
abbrev ι : Φ.r ⟶ 𝟭 C := Φ.obj.hom

@[simp]
/--
lemma `r_map_ι_app` / 引理 `r_map_ι_app`

English:
lemma r_map_ι_app
  given: (X : C)
  statement: Φ.r.map (Φ.ι.app X) = Φ.ι.app (Φ.r.obj X)
  proof: by
  rw [← cancel_mono (Φ.ι.app X)]
  exact Φ.ι.naturality (Φ.ι.app X)

中文:
引理 r_map_ι_app
  条件: (X : C)
  结论: Φ.r.map (Φ.ι.app X) = Φ.ι.app (Φ.r.obj X)
  证明: by
  rw [← cancel_mono (Φ.ι.app X)]
  exact Φ.ι.naturality (Φ.ι.app X)

Depends on / 依赖: cancel_mono, naturality
-/
lemma r_map_ι_app (X : C) : Φ.r.map (Φ.ι.app X) = Φ.ι.app (Φ.r.obj X) := by
  rw [← cancel_mono (Φ.ι.app X)]
  exact Φ.ι.naturality (Φ.ι.app X)

/--
Definition of `IsIdempotent` / `IsIdempotent` 的定义

English:
class IsIdempotent
  parameters: : Prop where
  axioms and operations (1):
    - isIso_whiskerLeft_r_ι : IsIso (Functor.whiskerLeft Φ.r Φ.ι)

中文:
类 IsIdempotent
  参数: : 命题 where
  公理与运算 (1 个):
    - isIso_whiskerLeft_r_ι : IsIso (Functor.whiskerLeft Φ.r Φ.ι)
-/
class IsIdempotent : Prop where
  isIso_whiskerLeft_r_ι : IsIso (Functor.whiskerLeft Φ.r Φ.ι)

attribute [instance] IsIdempotent.isIso_whiskerLeft_r_ι

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsIdempotent]
  signature: (X : C)
  body: inferInstanceAs (IsIso ((Functor.whiskerLeft Φ.r Φ.ι).app X))

中文:
实例 [Φ.IsIdempotent]
  签名: (X : C)
  定义体: inferInstanceAs (IsIso ((Functor.whiskerLeft Φ.r Φ.ι).app X))

Depends on / 依赖: Functor, Functor.whiskerLeft, whiskerLeft
-/
instance [Φ.IsIdempotent] (X : C) :
    IsIso (Φ.ι.app (Φ.r.obj X)) :=
  inferInstanceAs (IsIso ((Functor.whiskerLeft Φ.r Φ.ι).app X))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsIdempotent]
  signature: (X : C)
  body: by
  rw [r_map_ι_app]
  infer_instance

中文:
实例 [Φ.IsIdempotent]
  签名: (X : C)
  定义体: by
  rw [r_map_ι_app]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [Φ.IsIdempotent] (X : C) :
    IsIso (Φ.r.map (Φ.ι.app X)) := by
  rw [r_map_ι_app]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance {D : Type*} [Category* D] (F : D ⥤ C) :
    Mono (Functor.whiskerLeft F Φ.ι) := by
  rw [NatTrans.mono_iff_mono_app]
  intro
  dsimp
  infer_instance

end Preradical

end CategoryTheory.Abelian
