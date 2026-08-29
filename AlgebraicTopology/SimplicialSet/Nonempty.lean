/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Nonempty simplicial sets

-/

@[expose] public section

universe u

open Simplicial CategoryTheory Limits

namespace SSet

variable (X : SSet.{u})

/--
Definition of `Nonempty` / `Nonempty` 的定义

English:
abbreviation Nonempty
  signature: : Prop
  body: _root_.Nonempty (X _⦋0⦌)

中文:
缩写 非空
  签名: : 命题
  定义体: _root_.Nonempty (X _⦋0⦌)
-/
protected abbrev Nonempty : Prop := _root_.Nonempty (X _⦋0⦌)

instance (n : SimplexCategoryᵒᵖ) [X.Nonempty] : Nonempty (X.obj n) :=
  ⟨X.map (SimplexCategory.const n.unop ⦋0⦌ 0).op (Classical.arbitrary _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Nonempty]
  signature: : Nonempty X.N
  body: ⟨N.mk (n := 0) (Classical.arbitrary _) (by simp)⟩

中文:
实例 [X.非空]
  签名: : 非空 X.N
  定义体: ⟨N.mk (n := 0) (Classical.arbitrary _) (by simp)⟩

Depends on / 依赖: Classical, Classical.arbitrary, N.mk, arbitrary
-/
instance [X.Nonempty] : Nonempty X.N := ⟨N.mk (n := 0) (Classical.arbitrary _) (by simp)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Nonempty]
  signature: : Nonempty X.S
  body: ⟨S.mk (dim := 0) (Classical.arbitrary _)⟩

中文:
实例 [X.非空]
  签名: : 非空 X.S
  定义体: ⟨S.mk (dim := 0) (Classical.arbitrary _)⟩

Depends on / 依赖: Classical, Classical.arbitrary, S.mk, arbitrary
-/
instance [X.Nonempty] : Nonempty X.S := ⟨S.mk (dim := 0) (Classical.arbitrary _)⟩

instance (T : Type u) [Preorder T] [Nonempty T] : (nerve T).Nonempty :=
  ⟨.mk₀ (Classical.arbitrary _)⟩

instance (n : SimplexCategory) : (stdSimplex.obj n).Nonempty :=
  ⟨stdSimplex.objEquiv.symm (SimplexCategory.const _ _ 0)⟩

variable {X} in
/--
lemma `nonempty_of_hom` / 引理 `nonempty_of_hom`

English:
lemma nonempty_of_hom
  given: {Y : SSet.{u}} (f : Y ⟶ X) [Y.Nonempty]
  statement: X.Nonempty
  proof: ⟨f.app _ (Classical.arbitrary _)⟩

中文:
引理 nonempty_of_hom
  条件: {Y : SSet.{u}} (f : Y ⟶ X) [Y.非空]
  结论: X.非空
  证明: ⟨f.app _ (Classical.arbitrary _)⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, f.app
-/
lemma nonempty_of_hom {Y : SSet.{u}} (f : Y ⟶ X) [Y.Nonempty] : X.Nonempty :=
  ⟨f.app _ (Classical.arbitrary _)⟩

/--
lemma `notNonempty_iff_hasDimensionLT_zero` / 引理 `notNonempty_iff_hasDimensionLT_zero`

English:
lemma notNonempty_iff_hasDimensionLT_zero
  proof: by
  simp only [not_nonempty_iff]
  refine ⟨fun _ => ⟨fun n hn => ?_⟩, fun _ => ⟨fun x => ?_⟩⟩
  · have := Function.isEmpty (X.map (⦋0⦌.const ⦋n⦌ 0).op)
    subsingleton
  · exact (lt_self_iff_false _).1 (X.dim_lt_of_nonDegenerate ⟨x, by simp⟩ 0)

中文:
引理 notNonempty_iff_hasDimensionLT_zero
  证明: by
  simp only [not_nonempty_iff]
  refine ⟨fun _ => ⟨fun n hn => ?_⟩, fun _ => ⟨fun x => ?_⟩⟩
  · have := Function.isEmpty (X.map (⦋0⦌.const ⦋n⦌ 0).op)
    subsingleton
  · exact (lt_self_iff_false _).1 (X.dim_lt_of_nonDegenerate ⟨x, by simp⟩ 0)

Depends on / 依赖: Function, Function.isEmpty, X.dim_lt_of_nonDegenerate, X.map, dim_lt_of_nonDegenerate, isEmpty, lt_self_iff_false, not_nonempty_iff, subsingleton
-/
lemma notNonempty_iff_hasDimensionLT_zero :
    ¬ X.Nonempty ↔ X.HasDimensionLT 0 := by
  simp only [not_nonempty_iff]
  refine ⟨fun _ => ⟨fun n hn => ?_⟩, fun _ => ⟨fun x => ?_⟩⟩
  · have := Function.isEmpty (X.map (⦋0⦌.const ⦋n⦌ 0).op)
    subsingleton
  · exact (lt_self_iff_false _).1 (X.dim_lt_of_nonDegenerate ⟨x, by simp⟩ 0)

variable {X} in
/--
Definition of `isInitialOfNotNonempty` / `isInitialOfNotNonempty` 的定义

English:
definition isInitialOfNotNonempty
  signature: (hX : ¬ X.Nonempty)
  body: by
  simp only [not_nonempty_iff] at hX
  have (n : SimplexCategoryᵒᵖ) : IsEmpty (X.obj n) :=
    Function.isEmpty (X.map (⦋0⦌.const n.unop 0).op)
  exact IsInitial.ofUniqueHom (fun _ =>
    { app _ := ↾fun x => isEmptyElim x
      naturality _ _ _ := by ext x; exact isEmptyElim x })
    (fun _ _ => by ext _ x; exact isEmptyElim x)

中文:
定义 isInitialOfNotNonempty
  签名: (hX : ¬ X.非空)
  定义体: by
  simp only [not_nonempty_iff] at hX
  have (n : SimplexCategoryᵒᵖ) : IsEmpty (X.obj n) :=
    Function.isEmpty (X.map (⦋0⦌.const n.unop 0).op)
  exact IsInitial.ofUniqueHom (fun _ =>
    { app _ := ↾fun x => isEmptyElim x
      naturality _ _ _ := by ext x; exact isEmptyElim x })
    (fun _ _ => by ext _ x; exact isEmptyElim x)

Depends on / 依赖: Function, Function.isEmpty, IsEmpty, IsInitial, IsInitial.ofUniqueHom, X.map, X.obj, isEmpty, isEmptyElim, n.unop, naturality, not_nonempty_iff, ofUniqueHom
-/
def isInitialOfNotNonempty (hX : ¬ X.Nonempty) : IsInitial X := by
  simp only [not_nonempty_iff] at hX
  have (n : SimplexCategoryᵒᵖ) : IsEmpty (X.obj n) :=
    Function.isEmpty (X.map (⦋0⦌.const n.unop 0).op)
  exact IsInitial.ofUniqueHom (fun _ =>
    { app _ := ↾fun x => isEmptyElim x
      naturality _ _ _ := by ext x; exact isEmptyElim x })
    (fun _ _ => by ext _ x; exact isEmptyElim x)

end SSet
