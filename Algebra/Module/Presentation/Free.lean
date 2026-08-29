/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Logic.UnivLE

/-!
# Presentation of free modules

A module is free iff it admits a presentation with generators but no relation,
see `Module.free_iff_exists_presentation`.

-/

@[expose] public section

assert_not_exists Cardinal

universe w w₀ w₁ v u

namespace Module

variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]

namespace Relations

variable [IsEmpty relations.R]

/-- If `relations : Relations A` involved no relation, then it has an obvious
solution in the module `relations.G →₀ A`. -/
@[simps]
/--
Definition of `solutionFinsupp` / `solutionFinsupp` 的定义

English:
definition solutionFinsupp
  signature: : relations.Solution (relations.G ->₀ A) where
  body: Finsupp.single g 1
  linearCombination_var_relation r := by exfalso; exact IsEmpty.false r

中文:
定义 solutionFinsupp
  签名: : relations.解 (relations.G ->₀ A) where
  定义体: Finsupp.single g 1
  linearCombination_var_relation r := by exfalso; exact IsEmpty.false r

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
noncomputable def solutionFinsupp : relations.Solution (relations.G ->₀ A) where
  var g := Finsupp.single g 1
  linearCombination_var_relation r := by exfalso; exact IsEmpty.false r

/--
Definition of `solutionFinsupp.isPresentationCore` / `solutionFinsupp.isPresentationCore` 的定义

English:
definition solutionFinsupp.isPresentationCore
  signature: :
  body: Finsupp.linearCombination _ s.var
  postcomp_desc := by aesop
  postcomp_injective h := by ext; apply Solution.congr_var h

中文:
定义 solutionFinsupp.isPresentationCore
  签名: :
  定义体: Finsupp.linearCombination _ s.var
  postcomp_desc := by aesop
  postcomp_injective h := by ext; apply Solution.congr_var h

Depends on / 依赖: Finsupp, Finsupp.linearCombination, linearCombination, s.var
-/
noncomputable def solutionFinsupp.isPresentationCore :
    Solution.IsPresentationCore.{w} relations.solutionFinsupp where
  desc s := Finsupp.linearCombination _ s.var
  postcomp_desc := by aesop
  postcomp_injective h := by ext; apply Solution.congr_var h

/--
lemma `solutionFinsupp_isPresentation` / 引理 `solutionFinsupp_isPresentation`

English:
lemma solutionFinsupp_isPresentation
  proof: (solutionFinsupp.isPresentationCore relations).isPresentation

中文:
引理 solutionFinsupp_isPresentation
  证明: (solutionFinsupp.isPresentationCore relations).isPresentation

Depends on / 依赖: isPresentation, isPresentationCore, relations, solutionFinsupp, solutionFinsupp.isPresentationCore
-/
lemma solutionFinsupp_isPresentation :
    relations.solutionFinsupp.IsPresentation :=
  (solutionFinsupp.isPresentationCore relations).isPresentation

variable {relations}

/--
lemma `Solution.IsPresentation.free` / 引理 `Solution.IsPresentation.free`

English:
lemma Solution.IsPresentation.free
  statement: {solution : relations.Solution M}
  proof: Free.of_equiv ((solutionFinsupp_isPresentation relations).uniq h)

中文:
引理 解.是呈现.free
  结论: {solution : relations.解 M}
  证明: Free.of_equiv ((solutionFinsupp_isPresentation relations).uniq h)

Depends on / 依赖: Free.of_equiv, of_equiv, relations, solutionFinsupp_isPresentation
-/
lemma Solution.IsPresentation.free {solution : relations.Solution M}
    (h : solution.IsPresentation) :
    Module.Free A M :=
  Free.of_equiv ((solutionFinsupp_isPresentation relations).uniq h)

end Relations

variable (A)

/-- The presentation of the `A`-module `G →₀ A` with generators indexed by `G`,
and no relation. (Note that there is an auxiliary universe parameter `w₁` for the
empty type `R`.) -/
@[simps! G R var]
/--
Definition of `presentationFinsupp` / `presentationFinsupp` 的定义

English:
definition presentationFinsupp
  signature: (G : Type w₀)
  body: G
  R := PEmpty.{w₁ + 1}
  relation := by rintro ⟨⟩
  toSolution := Relations.solutionFinsupp _
  toIsPresentation := by exact Relations.solutionFinsupp_isPresentation _

中文:
定义 presentationFinsupp
  签名: (G : 类型 w₀)
  定义体: G
  R := PEmpty.{w₁ + 1}
  relation := by rintro ⟨⟩
  toSolution := Relations.solutionFinsupp _
  toIsPresentation := by exact Relations.solutionFinsupp_isPresentation _
-/
noncomputable def presentationFinsupp (G : Type w₀) :
    Presentation.{w₀, w₁} A (G ->₀ A) where
  G := G
  R := PEmpty.{w₁ + 1}
  relation := by rintro ⟨⟩
  toSolution := Relations.solutionFinsupp _
  toIsPresentation := by exact Relations.solutionFinsupp_isPresentation _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `free_iff_exists_presentation` / 引理 `free_iff_exists_presentation`

English:
lemma free_iff_exists_presentation
  proof: by
  constructor
  · rw [free_def.{_, _, v}]
    rintro ⟨G, ⟨⟨e⟩⟩⟩
    exact ⟨(presentationFinsupp A G).ofLinearEquiv e.symm, by dsimp; infer_instance⟩
  · rintro ⟨p, h⟩
    exact p.toIsPresentation.free

中文:
引理 free_iff_存在_presentation
  证明: by
  constructor
  · rw [free_def.{_, _, v}]
    rintro ⟨G, ⟨⟨e⟩⟩⟩
    exact ⟨(presentationFinsupp A G).ofLinearEquiv e.symm, by dsimp; infer_instance⟩
  · rintro ⟨p, h⟩
    exact p.toIsPresentation.free

Depends on / 依赖: e.symm, free_def, infer_instance, ofLinearEquiv, p.toIsPresentation.free, presentationFinsupp, toIsPresentation
-/
lemma free_iff_exists_presentation :
    Free A M ↔ exists (p : Presentation.{v, w₁} A M), IsEmpty p.R := by
  constructor
  · rw [free_def.{_, _, v}]
    rintro ⟨G, ⟨⟨e⟩⟩⟩
    exact ⟨(presentationFinsupp A G).ofLinearEquiv e.symm, by dsimp; infer_instance⟩
  · rintro ⟨p, h⟩
    exact p.toIsPresentation.free

end Module
