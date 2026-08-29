/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Properties of morphisms that are bounded by a cardinal

Given `P : MorphismProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `P.toSet` is `< κ`.

-/

public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/--
Definition of `HasCardinalLT` / `HasCardinalLT` 的定义

English:
abbreviation HasCardinalLT
  signature: (P : MorphismProperty C) (κ : Cardinal.{w})
  body: _root_.HasCardinalLT P.toSet κ

中文:
缩写 HasCardinalLT
  签名: (P : MorphismProperty C) (κ : 基数.{w})
  定义体: _root_.HasCardinalLT P.toSet κ
-/
protected abbrev HasCardinalLT (P : MorphismProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT P.toSet κ

/--
lemma `hasCardinalLT_ofHoms` / 引理 `hasCardinalLT_ofHoms`

English:
lemma hasCardinalLT_ofHoms
  statement: {C : Type*} [Category* C]
  proof: h.of_surjective (fun i => ⟨Arrow.mk (f i), ⟨i⟩⟩) (by
    rintro ⟨f, hf⟩
    rw [MorphismProperty.mem_toSet_iff]; rw [MorphismProperty.ofHoms_iff] at hf
    obtain ⟨i, hf⟩ := hf
    obtain rfl : f = _ := hf
    exact ⟨i, rfl⟩)

中文:
引理 hasCardinalLT_ofHoms
  结论: {C : 类型} [范畴* C]
  证明: h.of_surjective (fun i => ⟨Arrow.mk (f i), ⟨i⟩⟩) (by
    rintro ⟨f, hf⟩
    rw [MorphismProperty.mem_toSet_iff]; rw [MorphismProperty.ofHoms_iff] at hf
    obtain ⟨i, hf⟩ := hf
    obtain rfl : f = _ := hf
    exact ⟨i, rfl⟩)

Depends on / 依赖: Arrow.mk, MorphismProperty, MorphismProperty.mem_toSet_iff, MorphismProperty.ofHoms_iff, h.of_surjective, mem_toSet_iff, ofHoms_iff, of_surjective
-/
lemma hasCardinalLT_ofHoms {C : Type*} [Category* C]
    {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) {κ : Cardinal}
    (h : HasCardinalLT ι κ) : (MorphismProperty.ofHoms f).HasCardinalLT κ :=
  h.of_surjective (fun i => ⟨Arrow.mk (f i), ⟨i⟩⟩) (by
    rintro ⟨f, hf⟩
    rw [MorphismProperty.mem_toSet_iff]; rw [MorphismProperty.ofHoms_iff] at hf
    obtain ⟨i, hf⟩ := hf
    obtain rfl : f = _ := hf
    exact ⟨i, rfl⟩)

/--
lemma `HasCardinalLT.iSup` / 引理 `HasCardinalLT.iSup`

English:
lemma HasCardinalLT.iSup
  proof: by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [toSet_iSup]
  exact hasCardinalLT_iUnion _ hι hP

中文:
引理 HasCardinalLT.iSup
  证明: by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [toSet_iSup]
  exact hasCardinalLT_iUnion _ hι hP

Depends on / 依赖: HasCardinalLT, IsVerdierLeftLocalizing, IsVerdierLeftLocalizing.fac, MorphismProperty, MorphismProperty.HasCardinalLT, Quiver, Quiver.Hom.unop_inj, a.op, b.op, f.unop, hasCardinalLT_iUnion, toSet_iSup, unop_inj
-/
lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι -> MorphismProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : forall i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [toSet_iSup]
  exact hasCardinalLT_iUnion _ hι hP

/--
lemma `HasCardinalLT.sup` / 引理 `HasCardinalLT.sup`

English:
lemma HasCardinalLT.sup
  proof: by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [MorphismProperty.toSet_max]
  exact hasCardinalLT_union hκ h₁ h₂

中文:
引理 HasCardinalLT.上确界
  证明: by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [MorphismProperty.toSet_max]
  exact hasCardinalLT_union hκ h₁ h₂

Depends on / 依赖: HasCardinalLT, IsVerdierLeftLocalizing, IsVerdierLeftLocalizing.fac, MorphismProperty, MorphismProperty.HasCardinalLT, MorphismProperty.toSet_max, Quiver, Quiver.Hom.op_inj, a.unop, b.unop, f.op, hasCardinalLT_union, op_inj, toSet_max
-/
lemma HasCardinalLT.sup
    {P₁ P₂ : MorphismProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 <= κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [MorphismProperty.toSet_max]
  exact hasCardinalLT_union hκ h₁ h₂

end MorphismProperty

end CategoryTheory
