/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Properties of objects which hold for a zero object

Given a category `C` and `P : ObjectProperty C`, we define a type class `P.ContainsZero`
expressing that there exists a zero object for which `P` holds. (We do not require
that `P` holds for all zero objects, as in some applications (e.g. triangulated categories),
`P` may not necessarily be closed under isomorphisms.)

-/

public section

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P Q : ObjectProperty C)

/--
Definition of `ContainsZero` / `ContainsZero` 的定义

English:
class ContainsZero
  parameters: : Prop where
  axioms and operations (1):
    - exists_zero : exists (Z : C), IsZero Z ∧ P Z

中文:
类 余ntainsZero
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_zero : 存在 (Z : C), 是零 Z ∧ P Z
-/
class ContainsZero : Prop where
  exists_zero : exists (Z : C), IsZero Z ∧ P Z

/--
lemma `exists_prop_of_containsZero` / 引理 `exists_prop_of_containsZero`

English:
lemma exists_prop_of_containsZero
  given: [P.ContainsZero]
  proof: ContainsZero.exists_zero

中文:
引理 存在_prop_of_containsZero
  条件: [P.余ntainsZero]
  证明: ContainsZero.exists_zero

Depends on / 依赖: ContainsZero, ContainsZero.exists_zero, exists_zero
-/
lemma exists_prop_of_containsZero [P.ContainsZero] :
    exists (Z : C), IsZero Z ∧ P Z :=
  ContainsZero.exists_zero

-- see Note [lower instance priority]
instance (priority := 100) [P.ContainsZero] : P.Nonempty :=
  nonempty_of_prop P.exists_prop_of_containsZero.choose_spec.2

/--
lemma `prop_of_isZero` / 引理 `prop_of_isZero`

English:
lemma prop_of_isZero
  statement: [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  proof: by
  obtain ⟨Z₀, hZ₀, h₀⟩ := P.exists_prop_of_containsZero
  exact P.prop_of_iso (hZ₀.iso hZ) h₀

中文:
引理 prop_of_isZero
  结论: [P.余ntainsZero] [P.在同构下封闭]
  证明: by
  obtain ⟨Z₀, hZ₀, h₀⟩ := P.exists_prop_of_containsZero
  exact P.prop_of_iso (hZ₀.iso hZ) h₀

Depends on / 依赖: P.exists_prop_of_containsZero, P.prop_of_iso, exists_prop_of_containsZero, prop_of_iso
-/
lemma prop_of_isZero [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {Z : C} (hZ : IsZero Z) :
    P Z := by
  obtain ⟨Z₀, hZ₀, h₀⟩ := P.exists_prop_of_containsZero
  exact P.prop_of_iso (hZ₀.iso hZ) h₀

/--
lemma `prop_zero` / 引理 `prop_zero`

English:
lemma prop_zero
  given: [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [HasZeroObject C]
  proof: P.prop_of_isZero (isZero_zero C)

中文:
引理 prop_zero
  条件: [P.余ntainsZero] [P.在同构下封闭] [有ZeroObject C]
  证明: P.prop_of_isZero (isZero_zero C)

Depends on / 依赖: P.prop_of_isZero, isZero_zero, prop_of_isZero
-/
lemma prop_zero [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [HasZeroObject C] :
    P 0 :=
  P.prop_of_isZero (isZero_zero C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : (⊤
  body: ⟨0, isZero_zero C, by simp⟩

中文:
实例 [有ZeroObject
  签名: C] : (⊤
  定义体: ⟨0, isZero_zero C, by simp⟩

Depends on / 依赖: isZero_zero
-/
instance [HasZeroObject C] : (⊤ : ObjectProperty C).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : ContainsZero (IsZero (C := C)) where
  body: ⟨0, isZero_zero C, isZero_zero C⟩

中文:
实例 [有ZeroObject
  签名: C] : 余ntainsZero (是零 (C := C)) where
  定义体: ⟨0, isZero_zero C, isZero_zero C⟩
-/
instance [HasZeroObject C] : ContainsZero (IsZero (C := C)) where
  exists_zero := ⟨0, isZero_zero C, isZero_zero C⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: [HasZeroMorphisms C] [HasZeroMorphisms D]
  body: by
    obtain ⟨Z, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨F.obj Z, F.map_isZero h₁, P.prop_map_obj F h₂⟩

中文:
实例 [P.余ntainsZero]
  签名: [有ZeroMorphisms C] [有ZeroMorphisms D]
  定义体: by
    obtain ⟨Z, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨F.obj Z, F.map_isZero h₁, P.prop_map_obj F h₂⟩

Depends on / 依赖: F.map_isZero, F.obj, P.exists_prop_of_containsZero, P.prop_map_obj, exists_prop_of_containsZero, map_isZero, prop_map_obj
-/
instance [P.ContainsZero] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] : (P.map F).ContainsZero where
  exists_zero := by
    obtain ⟨Z, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨F.obj Z, F.map_isZero h₁, P.prop_map_obj F h₂⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: [P.IsClosedUnderIsomorphisms]
  body: ⟨0, isZero_zero D, P.prop_of_isZero (F.map_isZero (isZero_zero D))⟩

中文:
实例 [P.余ntainsZero]
  签名: [P.在同构下封闭]
  定义体: ⟨0, isZero_zero D, P.prop_of_isZero (F.map_isZero (isZero_zero D))⟩

Depends on / 依赖: F.map_isZero, P.prop_of_isZero, isZero_zero, map_isZero, prop_of_isZero
-/
instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : D ⥤ C) [F.PreservesZeroMorphisms] [HasZeroObject D] :
    (P.inverseImage F).ContainsZero where
  exists_zero :=
    ⟨0, isZero_zero D, P.prop_of_isZero (F.map_isZero (isZero_zero D))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: : P.isoClosure.ContainsZero where
  body: by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.le_isoClosure _ hP⟩

中文:
实例 [P.余ntainsZero]
  签名: : P.isoClosure.余ntainsZero where
  定义体: by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.le_isoClosure _ hP⟩

Depends on / 依赖: P.exists_prop_of_containsZero, P.le_isoClosure, exists_prop_of_containsZero, le_isoClosure
-/
instance [P.ContainsZero] : P.isoClosure.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.le_isoClosure _ hP⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: [P.IsClosedUnderIsomorphisms] [Q.ContainsZero]
  body: by
    obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.prop_of_isZero hZ, hQ⟩

中文:
实例 [P.余ntainsZero]
  签名: [P.在同构下封闭] [Q.余ntainsZero]
  定义体: by
    obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.prop_of_isZero hZ, hQ⟩

Depends on / 依赖: P.prop_of_isZero, Q.exists_prop_of_containsZero, exists_prop_of_containsZero, prop_of_isZero
-/
instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [Q.ContainsZero] :
    (P ⊓ Q).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
    exact ⟨Z, hZ, P.prop_of_isZero hZ, hQ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: : P.op.ContainsZero where
  body: by
    obtain ⟨Z, hZ, mem⟩ := P.exists_prop_of_containsZero
    exact ⟨op Z, hZ.op, mem⟩

中文:
实例 [P.余ntainsZero]
  签名: : P.op.余ntainsZero where
  定义体: by
    obtain ⟨Z, hZ, mem⟩ := P.exists_prop_of_containsZero
    exact ⟨op Z, hZ.op, mem⟩

Depends on / 依赖: P.exists_prop_of_containsZero, exists_prop_of_containsZero, hZ.op
-/
instance [P.ContainsZero] : P.op.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, mem⟩ := P.exists_prop_of_containsZero
    exact ⟨op Z, hZ.op, mem⟩

instance (P : ObjectProperty Cᵒᵖ) [P.ContainsZero] : P.unop.ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, mem⟩ := P.exists_prop_of_containsZero
    exact ⟨Z.unop, hZ.unop, mem⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: : HasZeroObject P.FullSubcategory where
  body: by
    obtain ⟨X, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨_, IsZero.of_full_of_faithful_of_isZero P.ι ⟨X, h₂⟩ h₁⟩

中文:
实例 [P.余ntainsZero]
  签名: : 有ZeroObject P.满子范畴 where
  定义体: by
    obtain ⟨X, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨_, IsZero.of_full_of_faithful_of_isZero P.ι ⟨X, h₂⟩ h₁⟩

Depends on / 依赖: IsZero, IsZero.of_full_of_faithful_of_isZero, P.exists_prop_of_containsZero, exists_prop_of_containsZero, of_full_of_faithful_of_isZero
-/
instance [P.ContainsZero] : HasZeroObject P.FullSubcategory where
  zero := by
    obtain ⟨X, h₁, h₂⟩ := P.exists_prop_of_containsZero
    exact ⟨_, IsZero.of_full_of_faithful_of_isZero P.ι ⟨X, h₂⟩ h₁⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  body: by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, hP, Q.prop_of_isZero hZ⟩

中文:
实例 [P.余ntainsZero]
  签名: [Q.余ntainsZero] [Q.在同构下封闭]
  定义体: by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, hP, Q.prop_of_isZero hZ⟩

Depends on / 依赖: P.exists_prop_of_containsZero, Q.prop_of_isZero, exists_prop_of_containsZero, prop_of_isZero
-/
instance [P.ContainsZero] [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] :
    (P ⊓ Q).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
    exact ⟨Z, hZ, hP, Q.prop_of_isZero hZ⟩

end ObjectProperty

/--
Definition of `Functor.kernel` / `Functor.kernel` 的定义

English:
abbreviation Functor.kernel
  signature: (F : C ⥤ D)
  body: ObjectProperty.inverseImage IsZero F

中文:
缩写 函子.kernel
  签名: (F : C ⥤ D)
  定义体: ObjectProperty.inverseImage IsZero F

Depends on / 依赖: IsZero, ObjectProperty, ObjectProperty.inverseImage, inverseImage
-/
abbrev Functor.kernel (F : C ⥤ D) : ObjectProperty C :=
  ObjectProperty.inverseImage IsZero F

end CategoryTheory
