/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Finite colimits of finite simplicial sets are finite

-/

public section

universe u v

open CategoryTheory Limits

namespace SSet

variable {J : Type*} [Category J] [HasColimitsOfShape J (Type u)]
  {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)

section

include hc

/--
lemma `iSup_range_eq_top_of_isColimit` / 引理 `iSup_range_eq_top_of_isColimit`

English:
lemma iSup_range_eq_top_of_isColimit
  proof: by
  ext n x
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion, Set.mem_range,
    Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj n) hc) x

中文:
引理 iSup_range_eq_top_of_isColimit
  证明: by
  ext n x
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion, Set.mem_range,
    Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj n) hc) x

Depends on / 依赖: Set.mem_iUnion, Set.mem_range, Set.mem_univ, Set.top_eq_univ, Subfunctor, Subfunctor.iSup_obj, Subfunctor.range_obj, Subfunctor.top_obj, Types.jointly_surjective_of_isColimit, evaluation, iSup_obj, iff_true, isColimitOfPreserves, jointly_surjective_of_isColimit, mem_iUnion, mem_range, mem_univ, range_obj, top_eq_univ, top_obj
-/
lemma iSup_range_eq_top_of_isColimit :
    ⨆ (j : J), Subcomplex.range (c.ι.app j) = ⊤ := by
  ext n x
  simp only [Subfunctor.iSup_obj, Subfunctor.range_obj, Set.mem_iUnion, Set.mem_range,
    Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj n) hc) x

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_eq_iSup_of_isColimit` / 引理 `range_eq_iSup_of_isColimit`

English:
lemma range_eq_iSup_of_isColimit
  given: {X : SSet.{u}} (φ : c.pt ⟶ X)
  proof: by
  conv_lhs => rw [← Category.id_comp φ]
  simp_rw [Subcomplex.range_comp, Subcomplex.range_eq_top, ← iSup_range_eq_top_of_isColimit hc,
    Subcomplex.image_iSup]

中文:
引理 range_eq_iSup_of_isColimit
  条件: {X : SSet.{u}} (φ : c.pt ⟶ X)
  证明: by
  conv_lhs => rw [← Category.id_comp φ]
  simp_rw [Subcomplex.range_comp, Subcomplex.range_eq_top, ← iSup_range_eq_top_of_isColimit hc,
    Subcomplex.image_iSup]

Depends on / 依赖: Category, Category.id_comp, Subcomplex, Subcomplex.image_iSup, Subcomplex.range_comp, Subcomplex.range_eq_top, conv_lhs, iSup_range_eq_top_of_isColimit, id_comp, image_iSup, range_comp, range_eq_top, simp_rw
-/
lemma range_eq_iSup_of_isColimit {X : SSet.{u}} (φ : c.pt ⟶ X) :
    Subcomplex.range φ = ⨆ (j : J), Subcomplex.range (c.ι.app j ≫ φ) := by
  conv_lhs => rw [← Category.id_comp φ]
  simp_rw [Subcomplex.range_comp, Subcomplex.range_eq_top, ← iSup_range_eq_top_of_isColimit hc,
    Subcomplex.image_iSup]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasDimensionLT_of_isColimit` / 引理 `hasDimensionLT_of_isColimit`

English:
lemma hasDimensionLT_of_isColimit
  statement: {n : Nat}
  proof: by
  rw [← hasDimensionLT_subcomplex_top_iff]; rw [← iSup_range_eq_top_of_isColimit hc]; rw [hasDimensionLT_iSup_iff]
  infer_instance

中文:
引理 hasDimensionLT_of_isColimit
  结论: {n : 自然数}
  证明: by
  rw [← hasDimensionLT_subcomplex_top_iff]; rw [← iSup_range_eq_top_of_isColimit hc]; rw [hasDimensionLT_iSup_iff]
  infer_instance

Depends on / 依赖: hasDimensionLT_iSup_iff, hasDimensionLT_subcomplex_top_iff, iSup_range_eq_top_of_isColimit, infer_instance
-/
lemma hasDimensionLT_of_isColimit {n : Nat}
    (h : forall (j : J), HasDimensionLT (F.obj j) n) : HasDimensionLT c.pt n := by
  rw [← hasDimensionLT_subcomplex_top_iff]; rw [← iSup_range_eq_top_of_isColimit hc]; rw [hasDimensionLT_iSup_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `finite_of_isColimit` / 引理 `finite_of_isColimit`

English:
lemma finite_of_isColimit
  given: [Finite J] (h : forall (j : J), (F.obj j).Finite)
  proof: by
  rw [← finite_subcomplex_top_iff]; rw [← iSup_range_eq_top_of_isColimit hc]; rw [finite_iSup_iff]
  infer_instance

中文:
引理 finite_of_isColimit
  条件: [有限 J] (h : 对任意 (j : J), (F.obj j).有限)
  证明: by
  rw [← finite_subcomplex_top_iff]; rw [← iSup_range_eq_top_of_isColimit hc]; rw [finite_iSup_iff]
  infer_instance

Depends on / 依赖: finite_iSup_iff, finite_subcomplex_top_iff, iSup_range_eq_top_of_isColimit, infer_instance
-/
lemma finite_of_isColimit [Finite J] (h : forall (j : J), (F.obj j).Finite) :
    c.pt.Finite := by
  rw [← finite_subcomplex_top_iff]; rw [← iSup_range_eq_top_of_isColimit hc]; rw [finite_iSup_iff]
  infer_instance

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊥_ SSet.{u}).Finite
  body: by
  apply finite_of_isColimit (initialIsInitial (C := SSet.{u}))
  rintro ⟨⟨⟩⟩

中文:
实例 :
  签名: (⊥_ SSet.{u}).有限
  定义体: by
  apply finite_of_isColimit (initialIsInitial (C := SSet.{u}))
  rintro ⟨⟨⟩⟩

Depends on / 依赖: finite_of_isColimit, initialIsInitial
-/
instance : (⊥_ SSet.{u}).Finite := by
  apply finite_of_isColimit (initialIsInitial (C := SSet.{u}))
  rintro ⟨⟨⟩⟩

instance (X Y : SSet.{u}) [X.Finite] [Y.Finite] :
    (X ⨿ Y).Finite := by
  apply finite_of_isColimit (coprodIsCoprod X Y)
  rintro ⟨_ | _⟩ <;> dsimp <;> infer_instance

instance {ι : Type v} [Finite ι] (X : ι -> SSet.{u}) [HasCoproduct X]
    [forall j, (X j).Finite] :
    (∐ X).Finite := by
  have : HasColimitsOfShape (Discrete ι) (Type u) := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)
  exact finite_of_isColimit (coproductIsCoproduct X) (fun ⟨j⟩ => by dsimp; infer_instance)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_eq_iSup_sigma_ι` / 引理 `range_eq_iSup_sigma_ι`

English:
lemma range_eq_iSup_sigma_ι
  proof: by
  rw [range_eq_iSup_of_isColimit (coproductIsCoproduct X) f]
  refine le_antisymm ?_ ?_
  · simp only [iSup_le_iff, Discrete.forall]
    intro i
    exact le_trans (by rfl) (le_iSup _ i)
  · simp only [iSup_le_iff]
    intro i
    exact le_trans (by rfl) (le_iSup _ ⟨i⟩)

中文:
引理 range_eq_iSup_sigma_ι
  证明: by
  rw [range_eq_iSup_of_isColimit (coproductIsCoproduct X) f]
  refine le_antisymm ?_ ?_
  · simp only [iSup_le_iff, Discrete.forall]
    intro i
    exact le_trans (by rfl) (le_iSup _ i)
  · simp only [iSup_le_iff]
    intro i
    exact le_trans (by rfl) (le_iSup _ ⟨i⟩)

Depends on / 依赖: Discrete, Discrete.forall, coproductIsCoproduct, iSup_le_iff, le_antisymm, le_iSup, le_trans, range_eq_iSup_of_isColimit
-/
lemma range_eq_iSup_sigma_ι
    {ι : Type v} [HasColimitsOfShape (Discrete ι) (Type u)]
    {X : ι -> SSet.{u}} {Y : SSet.{u}} [HasCoproduct X]
    (f : ∐ X ⟶ Y) :
    Subcomplex.range f = ⨆ (i : ι), Subcomplex.range (Sigma.ι X i ≫ f) := by
  rw [range_eq_iSup_of_isColimit (coproductIsCoproduct X) f]
  refine le_antisymm ?_ ?_
  · simp only [iSup_le_iff, Discrete.forall]
    intro i
    exact le_trans (by rfl) (le_iSup _ i)
  · simp only [iSup_le_iff]
    intro i
    exact le_trans (by rfl) (le_iSup _ ⟨i⟩)

end SSet
