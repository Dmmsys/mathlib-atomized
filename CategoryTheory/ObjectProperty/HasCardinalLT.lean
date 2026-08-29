/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Properties of objects that are bounded by a cardinal

Given `P : ObjectProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `Subtype P` is `< κ`.

-/

public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

/--
Definition of `HasCardinalLT` / `HasCardinalLT` 的定义

English:
abbreviation HasCardinalLT
  signature: (P : ObjectProperty C) (κ : Cardinal.{w})
  body: _root_.HasCardinalLT (Subtype P) κ

中文:
缩写 HasCardinalLT
  签名: (P : Object命题erty C) (κ : Cardinal.{w})
  定义体: _root_.HasCardinalLT (Subtype P) κ
-/
protected abbrev HasCardinalLT (P : ObjectProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT (Subtype P) κ

/--
lemma `hasCardinalLT_subtype_ofObj` / 引理 `hasCardinalLT_subtype_ofObj`

English:
lemma hasCardinalLT_subtype_ofObj
  proof: h.of_surjective (fun i => ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; exact ⟨i, rfl⟩)

中文:
引理 hasCardinalLT_subtype_ofObj
  证明: h.of_surjective (fun i => ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; exact ⟨i, rfl⟩)

Depends on / 依赖: h.of_surjective, of_surjective
-/
lemma hasCardinalLT_subtype_ofObj
    {ι : Type*} (X : ι -> C) {κ : Cardinal.{w}}
    (h : HasCardinalLT ι κ) : (ObjectProperty.ofObj X).HasCardinalLT κ :=
  h.of_surjective (fun i => ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; exact ⟨i, rfl⟩)

/--
lemma `HasCardinalLT.iSup` / 引理 `HasCardinalLT.iSup`

English:
lemma HasCardinalLT.iSup
  proof: hasCardinalLT_subtype_iSup _ hι hP

中文:
引理 HasCardinalLT.iSup
  证明: hasCardinalLT_subtype_iSup _ hι hP
-/
lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι -> ObjectProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : forall i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ :=
  hasCardinalLT_subtype_iSup _ hι hP

/--
lemma `HasCardinalLT.sup` / 引理 `HasCardinalLT.sup`

English:
lemma HasCardinalLT.sup
  proof: hasCardinalLT_union hκ h₁ h₂

中文:
引理 HasCardinalLT.sup
  证明: hasCardinalLT_union hκ h₁ h₂
-/
lemma HasCardinalLT.sup
    {P₁ P₂ : ObjectProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 <= κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ :=
  hasCardinalLT_union hκ h₁ h₂

end ObjectProperty

end CategoryTheory
