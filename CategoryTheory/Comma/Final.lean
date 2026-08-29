/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.StructuredArrow.CommaMap

/-!
# Finality of Projections in Comma Categories

We show that `fst L R` is final if `R` is and that `snd L R` is initial if `L` is.
As a corollary, we show that `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is
final and `A` is connected.

We then use this in a proof that derives finality of `map` between two comma categories
on a quasi-commutative diagram of functors, some of which need to be final.

Finally we prove filteredness of a `Comma L R` and finality of `snd L R`, given that `R` is final
and `A` and `B` are filtered.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 3.4.3 -- 3.4.5
-/

public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

namespace Comma

open Limits CategoryTheory.Functor CostructuredArrow

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

section Relative

/--
lemma `isCofiltered_of_isCofiltered_costructuredArrow` / 引理 `isCofiltered_of_isCofiltered_costructuredArrow`

English:
lemma isCofiltered_of_isCofiltered_costructuredArrow
  statement: [IsCofiltered A] [IsCofiltered B]
  proof: by
    obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨X.left, b, X.hom⟩⟩
  toIsCofilteredOrEmpty := by
    refine ⟨fun j₁ j₂ => ?_, fun j₁ j₂ u v => ?_⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.min j₁.right j₂.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToLeft j₁.right j₂.right)) j₁.hom
      obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToRight j₁.right j₂.right)) j₂.hom
      obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
      exact ⟨⟨i₀, IsCofiltered.min j₁.right j₂.right, L.map (il₀ ≫ va₁) ≫ Q.hom⟩,
        ⟨il₀ ≫ va₂, IsCofiltered.minToLeft _ _, by simp [← heqa]⟩,
        ⟨ir₀ ≫ vb₂, IsCofiltered.minToRight _ _, by cat_disch⟩, trivial⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.eq u.right v.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.eqHom u.right v.right)) j₁.hom
      obtain ⟨i₀, α, β, hα, hβ⟩ := IsCofiltered.bowtie u.left (va₂ ≫ v.left) (𝟙 _) va₂
      have := IsCofiltered.eq_condition u.right v.right
      exact ⟨⟨i₀, IsCofiltered.eq u.right v.right, L.map (β ≫ va₁) ≫ Q.hom⟩,
        ⟨β ≫ va₂, IsCofiltered.eqHom u.right v.right, by cat_disch⟩, by cat_disch⟩

中文:
引理 isCofiltered_of_isCofiltered_costructuredArrow
  结论: [是余filtered A] [是余filtered B]
  证明: by
    obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨X.left, b, X.hom⟩⟩
  toIsCofilteredOrEmpty := by
    refine ⟨fun j₁ j₂ => ?_, fun j₁ j₂ u v => ?_⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.min j₁.right j₂.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToLeft j₁.right j₂.right)) j₁.hom
      obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToRight j₁.right j₂.right)) j₂.hom
      obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
      exact ⟨⟨i₀, IsCofiltered.min j₁.right j₂.right, L.map (il₀ ≫ va₁) ≫ Q.hom⟩,
        ⟨il₀ ≫ va₂, IsCofiltered.minToLeft _ _, by simp [← heqa]⟩,
        ⟨ir₀ ≫ vb₂, IsCofiltered.minToRight _ _, by cat_disch⟩, trivial⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.eq u.right v.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.eqHom u.right v.right)) j₁.hom
      obtain ⟨i₀, α, β, hα, hβ⟩ := IsCofiltered.bowtie u.left (va₂ ≫ v.left) (𝟙 _) va₂
      have := IsCofiltered.eq_condition u.right v.right
      exact ⟨⟨i₀, IsCofiltered.eq u.right v.right, L.map (β ≫ va₁) ≫ Q.hom⟩,
        ⟨β ≫ va₂, IsCofiltered.eqHom u.right v.right, by cat_disch⟩, by cat_disch⟩

Depends on / 依赖: CostructuredArrow, IsCofiltered, IsCofiltered.min, IsCofiltered.minToLeft, IsCofiltered.nonempty, Nonempty, Q.hom, R.map, R.obj, X.hom, X.left, exists_eq_of_isCofiltered_costructuredArrow, minToLeft, nonempty, toIsCofilteredOrEmpty
-/
lemma isCofiltered_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B]
    [forall b, IsCofiltered (CostructuredArrow L (R.obj b))] : IsCofiltered (Comma L R) where
  nonempty := by
    obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨X.left, b, X.hom⟩⟩
  toIsCofilteredOrEmpty := by
    refine ⟨fun j₁ j₂ => ?_, fun j₁ j₂ u v => ?_⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.min j₁.right j₂.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToLeft j₁.right j₂.right)) j₁.hom
      obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.minToRight j₁.right j₂.right)) j₂.hom
      obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
      exact ⟨⟨i₀, IsCofiltered.min j₁.right j₂.right, L.map (il₀ ≫ va₁) ≫ Q.hom⟩,
        ⟨il₀ ≫ va₂, IsCofiltered.minToLeft _ _, by simp [← heqa]⟩,
        ⟨ir₀ ≫ vb₂, IsCofiltered.minToRight _ _, by cat_disch⟩, trivial⟩
    · obtain ⟨Q⟩ : Nonempty (CostructuredArrow L (R.obj (IsCofiltered.eq u.right v.right))) :=
        IsCofiltered.nonempty
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_isCofiltered_costructuredArrow L
        (Q.hom ≫ R.map (IsCofiltered.eqHom u.right v.right)) j₁.hom
      obtain ⟨i₀, α, β, hα, hβ⟩ := IsCofiltered.bowtie u.left (va₂ ≫ v.left) (𝟙 _) va₂
      have := IsCofiltered.eq_condition u.right v.right
      exact ⟨⟨i₀, IsCofiltered.eq u.right v.right, L.map (β ≫ va₁) ≫ Q.hom⟩,
        ⟨β ≫ va₂, IsCofiltered.eqHom u.right v.right, by cat_disch⟩, by cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `initial_fst_of_isCofiltered_costructuredArrow` / 引理 `initial_fst_of_isCofiltered_costructuredArrow`

English:
lemma initial_fst_of_isCofiltered_costructuredArrow
  statement: [IsCofiltered A] [IsCofiltered B]
  proof: by
  have := isCofiltered_of_isCofiltered_costructuredArrow L R
  rw [Functor.initial_iff_of_isCofiltered]
  refine ⟨fun a => ?_, fun {a} A' s s' => ?_⟩
  · obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨IsCofiltered.min a X.left, b, L.map (IsCofiltered.minToRight a X.left) ≫ X.hom⟩,
      ⟨IsCofiltered.minToLeft a X.left⟩⟩
  · exact ⟨⟨_, A'.right, L.map (IsCofiltered.eqHom s s') ≫ A'.hom⟩,
      ⟨IsCofiltered.eqHom s s', 𝟙 A'.right, by simp⟩, IsCofiltered.eq_condition s s'⟩

中文:
引理 initial_fst_of_isCofiltered_costructuredArrow
  结论: [是余filtered A] [是余filtered B]
  证明: by
  have := isCofiltered_of_isCofiltered_costructuredArrow L R
  rw [Functor.initial_iff_of_isCofiltered]
  refine ⟨fun a => ?_, fun {a} A' s s' => ?_⟩
  · obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨IsCofiltered.min a X.left, b, L.map (IsCofiltered.minToRight a X.left) ≫ X.hom⟩,
      ⟨IsCofiltered.minToLeft a X.left⟩⟩
  · exact ⟨⟨_, A'.right, L.map (IsCofiltered.eqHom s s') ≫ A'.hom⟩,
      ⟨IsCofiltered.eqHom s s', 𝟙 A'.right, by simp⟩, IsCofiltered.eq_condition s s'⟩

Depends on / 依赖: CostructuredArrow, Functor, Functor.initial_iff_of_isCofiltered, IsCofiltered, IsCofiltered.eqHom, IsCofiltered.min, IsCofiltered.minToLeft, IsCofiltered.minToRight, IsCofiltered.nonempty, L.map, Nonempty, R.obj, X.hom, X.left, initial_iff_of_isCofiltered, isCofiltered_of_isCofiltered_costructuredArrow, minToLeft, minToRight, nonempty
-/
lemma initial_fst_of_isCofiltered_costructuredArrow [IsCofiltered A] [IsCofiltered B]
    [forall b, IsCofiltered (CostructuredArrow L (R.obj b))] : (fst L R).Initial := by
  have := isCofiltered_of_isCofiltered_costructuredArrow L R
  rw [Functor.initial_iff_of_isCofiltered]
  refine ⟨fun a => ?_, fun {a} A' s s' => ?_⟩
  · obtain ⟨b⟩ := IsCofiltered.nonempty (C := B)
    obtain ⟨X⟩ : Nonempty (CostructuredArrow L (R.obj b)) := IsCofiltered.nonempty
    exact ⟨⟨IsCofiltered.min a X.left, b, L.map (IsCofiltered.minToRight a X.left) ≫ X.hom⟩,
      ⟨IsCofiltered.minToLeft a X.left⟩⟩
  · exact ⟨⟨_, A'.right, L.map (IsCofiltered.eqHom s s') ≫ A'.hom⟩,
      ⟨IsCofiltered.eqHom s s', 𝟙 A'.right, by simp⟩, IsCofiltered.eq_condition s s'⟩

/--
lemma `initial_snd_of_isConnected_costructuredArrow` / 引理 `initial_snd_of_isConnected_costructuredArrow`

English:
lemma initial_snd_of_isConnected_costructuredArrow
  proof: by
    have := final_of_adjunction (costructuredArrowSndAdjunction L R b)
    rw [← isConnected_iff_of_final (costructuredArrowSndInclusion L R b)]
    infer_instance

中文:
引理 initial_snd_of_isConnected_costructuredArrow
  证明: by
    have := final_of_adjunction (costructuredArrowSndAdjunction L R b)
    rw [← isConnected_iff_of_final (costructuredArrowSndInclusion L R b)]
    infer_instance

Depends on / 依赖: costructuredArrowSndAdjunction, costructuredArrowSndInclusion, final_of_adjunction, infer_instance, isConnected_iff_of_final
-/
lemma initial_snd_of_isConnected_costructuredArrow
    [forall b, IsConnected (CostructuredArrow L (R.obj b))] : (snd L R).Initial where
  out b := by
    have := final_of_adjunction (costructuredArrowSndAdjunction L R b)
    rw [← isConnected_iff_of_final (costructuredArrowSndInclusion L R b)]
    infer_instance

/--
lemma `isFiltered_of_isFiltered_structuredArrow` / 引理 `isFiltered_of_isFiltered_structuredArrow`

English:
lemma isFiltered_of_isFiltered_structuredArrow
  statement: [IsFiltered A] [IsFiltered B]
  proof: by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : IsCofiltered (Comma R.op L.op) := isCofiltered_of_isCofiltered_costructuredArrow _ _
  exact IsFiltered.of_equivalence (opEquiv L R).symm

中文:
引理 isFiltered_of_isFiltered_structuredArrow
  结论: [是Filtered A] [是Filtered B]
  证明: by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : IsCofiltered (Comma R.op L.op) := isCofiltered_of_isCofiltered_costructuredArrow _ _
  exact IsFiltered.of_equivalence (opEquiv L R).symm

Depends on / 依赖: CostructuredArrow, IsCofiltered, IsCofiltered.of_equivalence, IsFiltered, IsFiltered.of_equivalence, L.obj, L.op, L.op.obj, R.op, a.unop, isCofiltered_of_isCofiltered_costructuredArrow, of_equivalence, opEquiv, structuredArrowOpEquivalence
-/
lemma isFiltered_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [forall a, IsFiltered (StructuredArrow (L.obj a) R)] : IsFiltered (Comma L R) := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : IsCofiltered (Comma R.op L.op) := isCofiltered_of_isCofiltered_costructuredArrow _ _
  exact IsFiltered.of_equivalence (opEquiv L R).symm

/--
lemma `final_fst_of_isConnected_structuredArrow` / 引理 `final_fst_of_isConnected_structuredArrow`

English:
lemma final_fst_of_isConnected_structuredArrow
  proof: by
  have (a : Aᵒᵖ) : IsConnected (CostructuredArrow R.op (L.op.obj a)) :=
    (isConnected_iff_of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))).mp
      inferInstance
  have : (snd R.op L.op).Initial := initial_snd_of_isConnected_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ snd R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
have : (fst L R).op.Initial := initial_of_natIso opFunctorCompSnd _ _
  apply final_of_initial_op

中文:
引理 final_fst_of_isConnected_structuredArrow
  证明: by
  have (a : Aᵒᵖ) : IsConnected (CostructuredArrow R.op (L.op.obj a)) :=
    (isConnected_iff_of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))).mp
      inferInstance
  have : (snd R.op L.op).Initial := initial_snd_of_isConnected_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ snd R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
have : (fst L R).op.Initial := initial_of_natIso opFunctorCompSnd _ _
  apply final_of_initial_op

Depends on / 依赖: CostructuredArrow, Initial, IsConnected, L.obj, L.op, L.op.obj, R.op, a.unop, final_of_initial_op, functor, functor.leftOp, initial_equivalence_comp, initial_of_natIso, initial_snd_of_isConnected_costructuredArrow, isConnected_iff_of_equivalence, leftOp, op.Initial, opEquiv, opFunctor, opFunctorCompSnd
-/
lemma final_fst_of_isConnected_structuredArrow
    [forall a, IsConnected (StructuredArrow (L.obj a) R)] : (fst L R).Final := by
  have (a : Aᵒᵖ) : IsConnected (CostructuredArrow R.op (L.op.obj a)) :=
    (isConnected_iff_of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))).mp
      inferInstance
  have : (snd R.op L.op).Initial := initial_snd_of_isConnected_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ snd R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
have : (fst L R).op.Initial := initial_of_natIso opFunctorCompSnd _ _
  apply final_of_initial_op

/--
lemma `final_snd_of_isFiltered_structuredArrow` / 引理 `final_snd_of_isFiltered_structuredArrow`

English:
lemma final_snd_of_isFiltered_structuredArrow
  statement: [IsFiltered A] [IsFiltered B]
  proof: by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : (fst R.op L.op).Initial := initial_fst_of_isCofiltered_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ fst R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
have : (snd L R).op.Initial := initial_of_natIso opFunctorCompFst _ _
  apply final_of_initial_op

中文:
引理 final_snd_of_isFiltered_structuredArrow
  结论: [是Filtered A] [是Filtered B]
  证明: by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : (fst R.op L.op).Initial := initial_fst_of_isCofiltered_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ fst R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
have : (snd L R).op.Initial := initial_of_natIso opFunctorCompFst _ _
  apply final_of_initial_op

Depends on / 依赖: CostructuredArrow, Initial, IsCofiltered, IsCofiltered.of_equivalence, L.obj, L.op, L.op.obj, R.op, a.unop, final_of_initial_op, functor, functor.leftOp, initial_equivalence_comp, initial_fst_of_isCofiltered_costructuredArrow, initial_of_natIso, leftOp, of_equivalence, op.Initial, opEquiv, opFunctor
-/
lemma final_snd_of_isFiltered_structuredArrow [IsFiltered A] [IsFiltered B]
    [forall a, IsFiltered (StructuredArrow (L.obj a) R)] : (snd L R).Final := by
  have (a : Aᵒᵖ) : IsCofiltered (CostructuredArrow R.op (L.op.obj a)) :=
    IsCofiltered.of_equivalence (structuredArrowOpEquivalence R (L.obj a.unop))
  have : (fst R.op L.op).Initial := initial_fst_of_isCofiltered_costructuredArrow _ _
  have : ((opFunctor L R).leftOp ⋙ fst R.op L.op).Initial :=
    initial_equivalence_comp (opEquiv L R).functor.leftOp _
have : (snd L R).op.Initial := initial_of_natIso opFunctorCompFst _ _
  apply final_of_initial_op

end Relative

/--
Instance `initial_snd` / 实例 `initial_snd`

English:
instance initial_snd
  signature: [L.Initial]
  body: initial_snd_of_isConnected_costructuredArrow L R

中文:
实例 initial_snd
  签名: [L.初始]
  定义体: initial_snd_of_isConnected_costructuredArrow L R

Depends on / 依赖: initial_snd_of_isConnected_costructuredArrow
-/
instance initial_snd [L.Initial] : (snd L R).Initial :=
  initial_snd_of_isConnected_costructuredArrow L R

/--
Instance `final_fst` / 实例 `final_fst`

English:
instance final_fst
  signature: [R.Final]
  body: final_fst_of_isConnected_structuredArrow L R

中文:
实例 final_fst
  签名: [R.终]
  定义体: final_fst_of_isConnected_structuredArrow L R

Depends on / 依赖: final_fst_of_isConnected_structuredArrow
-/
instance final_fst [R.Final] : (fst L R).Final :=
  final_fst_of_isConnected_structuredArrow L R

/--
Instance `isConnected_comma_of_final` / 实例 `isConnected_comma_of_final`

English:
instance isConnected_comma_of_final
  signature: [IsConnected A] [R.Final]
  body: by
  rwa [isConnected_iff_of_final (fst L R)]

中文:
实例 isConnected_comma_of_final
  签名: [是连通 A] [R.终]
  定义体: by
  rwa [isConnected_iff_of_final (fst L R)]

Depends on / 依赖: isConnected_iff_of_final
-/
instance isConnected_comma_of_final [IsConnected A] [R.Final] : IsConnected (Comma L R) := by
  rwa [isConnected_iff_of_final (fst L R)]

/--
Instance `isConnected_comma_of_initial` / 实例 `isConnected_comma_of_initial`

English:
instance isConnected_comma_of_initial
  signature: [IsConnected B] [L.Initial]
  body: by
  rwa [isConnected_iff_of_initial (snd L R)]

中文:
实例 isConnected_comma_of_initial
  签名: [是连通 B] [L.初始]
  定义体: by
  rwa [isConnected_iff_of_initial (snd L R)]

Depends on / 依赖: isConnected_iff_of_initial
-/
instance isConnected_comma_of_initial [IsConnected B] [L.Initial] : IsConnected (Comma L R) := by
  rwa [isConnected_iff_of_initial (snd L R)]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_final` / 引理 `map_final`

English:
lemma map_final
  statement: {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {T : Type u₃}
  proof: ⟨fun ⟨i₂, j₂, u₂⟩ => by
  have := final_of_natIso iR
  rw [isConnected_iff_of_equivalence (StructuredArrow.commaMapEquivalence iL.hom iR.inv _)]
  have : StructuredArrow.map₂ u₂ iR.hom ≅ StructuredArrow.post j₂ G R' ⋙
      StructuredArrow.map₂ (G := 𝟭 _) (F := 𝟭 _) (R' := R ⋙ H) u₂ iR.hom ⋙
      StructuredArrow.pre _ R H :=
    eqToIso (by
      congr
      · simp
      · ext; simp) ≪≫
    (StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
    isoWhiskerLeft _ ((StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
      isoWhiskerLeft _ (StructuredArrow.preIsoMap₂ _ _ _).symm) ≪≫
    isoWhiskerRight (StructuredArrow.postIsoMap₂ j₂ G R').symm _
  have := final_of_natIso this.symm
  rw [IsIso.Iso.inv_inv]
  infer_instance⟩

中文:
引理 map_final
  结论: {A : 类型u₁} [范畴.{v₁} A] {B : 类型u₂} [范畴.{v₂} B] {T : 类型u₃}
  证明: ⟨fun ⟨i₂, j₂, u₂⟩ => by
  have := final_of_natIso iR
  rw [isConnected_iff_of_equivalence (StructuredArrow.commaMapEquivalence iL.hom iR.inv _)]
  have : StructuredArrow.map₂ u₂ iR.hom ≅ StructuredArrow.post j₂ G R' ⋙
      StructuredArrow.map₂ (G := 𝟭 _) (F := 𝟭 _) (R' := R ⋙ H) u₂ iR.hom ⋙
      StructuredArrow.pre _ R H :=
    eqToIso (by
      congr
      · simp
      · ext; simp) ≪≫
    (StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
    isoWhiskerLeft _ ((StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
      isoWhiskerLeft _ (StructuredArrow.preIsoMap₂ _ _ _).symm) ≪≫
    isoWhiskerRight (StructuredArrow.postIsoMap₂ j₂ G R').symm _
  have := final_of_natIso this.symm
  rw [IsIso.Iso.inv_inv]
  infer_instance⟩

Depends on / 依赖: StructuredArr, StructuredArrow, StructuredArrow.commaMapEquivalence, StructuredArrow.map, StructuredArrow.post, StructuredArrow.pre, commaMapEquivalence, eqToIso, final_of_natIso, iL.hom, iR.hom, iR.inv, isConnected_iff_of_equivalence, isoWhiskerLeft
-/
lemma map_final {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {T : Type u₃}
    [Category.{v₃} T] {L : A ⥤ T} {R : B ⥤ T} {A' : Type u₄} [Category.{v₄} A'] {B' : Type u₅}
    [Category.{v₅} B'] {T' : Type u₆} [Category.{v₆} T'] {L' : A' ⥤ T'} {R' : B' ⥤ T'} {F : A ⥤ A'}
    {G : B ⥤ B'} {H : T ⥤ T'} (iL : F ⋙ L' ≅ L ⋙ H) (iR : G ⋙ R' ≅ R ⋙ H) [IsFiltered B]
    [R.Final] [R'.Final] [F.Final] [G.Final] :
    (Comma.map iL.hom iR.inv).Final := ⟨fun ⟨i₂, j₂, u₂⟩ => by
  have := final_of_natIso iR
  rw [isConnected_iff_of_equivalence (StructuredArrow.commaMapEquivalence iL.hom iR.inv _)]
  have : StructuredArrow.map₂ u₂ iR.hom ≅ StructuredArrow.post j₂ G R' ⋙
      StructuredArrow.map₂ (G := 𝟭 _) (F := 𝟭 _) (R' := R ⋙ H) u₂ iR.hom ⋙
      StructuredArrow.pre _ R H :=
    eqToIso (by
      congr
      · simp
      · ext; simp) ≪≫
    (StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
    isoWhiskerLeft _ ((StructuredArrow.map₂CompMap₂Iso _ _ _ _).symm ≪≫
      isoWhiskerLeft _ (StructuredArrow.preIsoMap₂ _ _ _).symm) ≪≫
    isoWhiskerRight (StructuredArrow.postIsoMap₂ j₂ G R').symm _
  have := final_of_natIso this.symm
  rw [IsIso.Iso.inv_inv]
  infer_instance⟩

section Filtered

/--
Instance `isFiltered_of_final` / 实例 `isFiltered_of_final`

English:
instance isFiltered_of_final
  signature: [IsFiltered A] [IsFiltered B] [R.Final]
  body: by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact isFiltered_of_isFiltered_structuredArrow L R

中文:
实例 isFiltered_of_final
  签名: [是Filtered A] [是Filtered B] [R.终]
  定义体: by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact isFiltered_of_isFiltered_structuredArrow L R

Depends on / 依赖: R.final_iff_isFiltered_structuredArrow.mp, final_iff_isFiltered_structuredArrow, isFiltered_of_isFiltered_structuredArrow
-/
instance isFiltered_of_final [IsFiltered A] [IsFiltered B] [R.Final] : IsFiltered (Comma L R) := by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact isFiltered_of_isFiltered_structuredArrow L R

/--
lemma `isCofiltered_of_initial` / 引理 `isCofiltered_of_initial`

English:
lemma isCofiltered_of_initial
  given: [IsCofiltered A] [IsCofiltered B] [L.Initial]
  proof: by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact isCofiltered_of_isCofiltered_costructuredArrow L R

中文:
引理 isCofiltered_of_initial
  条件: [是余filtered A] [是余filtered B] [L.初始]
  证明: by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact isCofiltered_of_isCofiltered_costructuredArrow L R

Depends on / 依赖: L.initial_iff_isCofiltered_costructuredArrow.mp, initial_iff_isCofiltered_costructuredArrow, isCofiltered_of_isCofiltered_costructuredArrow
-/
lemma isCofiltered_of_initial [IsCofiltered A] [IsCofiltered B] [L.Initial] :
    IsCofiltered (Comma L R) := by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact isCofiltered_of_isCofiltered_costructuredArrow L R

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `final_snd` / 实例 `final_snd`

English:
instance final_snd
  signature: [IsFiltered A] [IsFiltered B] [R.Final]
  body: by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact final_snd_of_isFiltered_structuredArrow L R

中文:
实例 final_snd
  签名: [是Filtered A] [是Filtered B] [R.终]
  定义体: by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact final_snd_of_isFiltered_structuredArrow L R

Depends on / 依赖: R.final_iff_isFiltered_structuredArrow.mp, final_iff_isFiltered_structuredArrow, final_snd_of_isFiltered_structuredArrow
-/
instance final_snd [IsFiltered A] [IsFiltered B] [R.Final] : (snd L R).Final := by
  have := R.final_iff_isFiltered_structuredArrow.mp inferInstance
  exact final_snd_of_isFiltered_structuredArrow L R

/--
Instance `initial_fst` / 实例 `initial_fst`

English:
instance initial_fst
  signature: [IsCofiltered A] [IsCofiltered B] [L.Initial]
  body: by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact initial_fst_of_isCofiltered_costructuredArrow L R

中文:
实例 initial_fst
  签名: [是余filtered A] [是余filtered B] [L.初始]
  定义体: by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact initial_fst_of_isCofiltered_costructuredArrow L R

Depends on / 依赖: L.initial_iff_isCofiltered_costructuredArrow.mp, initial_fst_of_isCofiltered_costructuredArrow, initial_iff_isCofiltered_costructuredArrow
-/
instance initial_fst [IsCofiltered A] [IsCofiltered B] [L.Initial] : (fst L R).Initial := by
  have := L.initial_iff_isCofiltered_costructuredArrow.mp inferInstance
  exact initial_fst_of_isCofiltered_costructuredArrow L R

end Filtered

end Comma

end CategoryTheory
