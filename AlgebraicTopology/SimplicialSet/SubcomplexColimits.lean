/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer

/-!
# Colimits involving subcomplexes of a simplicial set

If `X` is a simplicial set, and we have subcomplexes `A`, `U i` (for `i : ι`) and
`V i j` which satisfy `Subcomplex.MulticoequalizerDiagram A U V` (an abbreviation
for `CompleteLattice.MulticoequalizerDiagram`), we
show that the simplicial sset corresponding to `A` is the multicoequalizer of
the `U i` along the `V i j`.

Similarly, bicartesian squares in the lattice `Subcomplex X` give pushout
squares in the category of simplicial sets.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}}

section

variable {A : X.Subcomplex} {ι : Type*}
  {U : ι -> X.Subcomplex} {V : ι -> ι -> X.Subcomplex}

variable (A U V) in
/--
Definition of `MulticoequalizerDiagram` / `MulticoequalizerDiagram` 的定义

English:
abbreviation MulticoequalizerDiagram
  body: CompleteLattice.MulticoequalizerDiagram A U V

中文:
缩写 MulticoequalizerDiagram
  定义体: CompleteLattice.MulticoequalizerDiagram A U V

Depends on / 依赖: CompleteLattice, CompleteLattice.MulticoequalizerDiagram, MulticoequalizerDiagram
-/
abbrev MulticoequalizerDiagram := CompleteLattice.MulticoequalizerDiagram A U V

namespace MulticoequalizerDiagram

variable (h : MulticoequalizerDiagram A U V)

/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: :
  body: evaluationJointlyReflectsColimits _ (fun n => by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i => (U i).obj n)
        (fun i j => (V i j).obj n) :=
      { eq_inf := by simp [h.eq_inf]
        iSup_eq := by simp [← h.iSup_eq] }
    exact (Multicofork.isColimitMapEquiv _ _).2
      (Types.isColimitOfMulticoequalizerDiagram h'))

中文:
定义 isColimit
  签名: :
  定义体: evaluationJointlyReflectsColimits _ (fun n => by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i => (U i).obj n)
        (fun i j => (V i j).obj n) :=
      { eq_inf := by simp [h.eq_inf]
        iSup_eq := by simp [← h.iSup_eq] }
    exact (Multicofork.isColimitMapEquiv _ _).2
      (Types.isColimitOfMulticoequalizerDiagram h'))

Depends on / 依赖: A.obj, CompleteLattice, CompleteLattice.MulticoequalizerDiagram, MulticoequalizerDiagram, Multicofork, Multicofork.isColimitMapEquiv, Types.isColimitOfMulticoequalizerDiagram, eq_inf, evaluationJointlyReflectsColimits, h.eq_inf, h.iSup_eq, iSup_eq, isColimitMapEquiv, isColimitOfMulticoequalizerDiagram
-/
noncomputable def isColimit :
    IsColimit (h.multicofork.map toSSetFunctor) :=
  evaluationJointlyReflectsColimits _ (fun n => by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i => (U i).obj n)
        (fun i j => (V i j).obj n) :=
      { eq_inf := by simp [h.eq_inf]
        iSup_eq := by simp [← h.iSup_eq] }
    exact (Multicofork.isColimitMapEquiv _ _).2
      (Types.isColimitOfMulticoequalizerDiagram h'))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimit'` / `isColimit'` 的定义

English:
definition isColimit'
  signature: [LinearOrder ι]
  body: Multicofork.isColimitToLinearOrder _ h.isColimit
    { iso i j := toSSetFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf]; rw [h.eq_inf]; rw [inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

中文:
定义 isColimit'
  签名: [线性序 ι]
  定义体: Multicofork.isColimitToLinearOrder _ h.isColimit
    { iso i j := toSSetFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf]; rw [h.eq_inf]; rw [inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

Depends on / 依赖: Multicofork, Multicofork.isColimitToLinearOrder, eqToIso, eq_inf, fst_eq_snd, h.eq_inf, h.isColimit, inf_comm, isColimit, isColimitToLinearOrder, iso_hom_fst, iso_hom_snd, mapIso, toSSetFunctor, toSSetFunctor.mapIso
-/
noncomputable def isColimit' [LinearOrder ι] :
    IsColimit (h.multicofork.toLinearOrder.map toSSetFunctor) :=
  Multicofork.isColimitToLinearOrder _ h.isColimit
    { iso i j := toSSetFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf]; rw [h.eq_inf]; rw [inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

end MulticoequalizerDiagram

end

/--
Definition of `BicartSq` / `BicartSq` 的定义

English:
abbreviation BicartSq
  signature: (A₁ A₂ A₃ A₄ : X.Subcomplex)
  body: Lattice.BicartSq A₁ A₂ A₃ A₄

中文:
缩写 BicartSq
  签名: (A₁ A₂ A₃ A₄ : X.子复形)
  定义体: Lattice.BicartSq A₁ A₂ A₃ A₄

Depends on / 依赖: BicartSq, Lattice, Lattice.BicartSq
-/
abbrev BicartSq (A₁ A₂ A₃ A₄ : X.Subcomplex) := Lattice.BicartSq A₁ A₂ A₃ A₄

/--
lemma `BicartSq.isPushout` / 引理 `BicartSq.isPushout`

English:
lemma BicartSq.isPushout
  given: {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : BicartSq A₁ A₂ A₃ A₄)
  proof: rfl
  isColimit' :=
    ⟨evaluationJointlyReflectsColimits _
      (fun n => (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (by
        have h : Lattice.BicartSq (A₁.obj n) (A₂.obj n) (A₃.obj n) (A₄.obj n) :=
          { sup_eq := by
              rw [← sq.sup_eq]
              rfl
            inf_eq := by
              rw [← sq.inf_eq]
              rfl }
        exact (Types.isPushout_of_bicartSq h).isColimit))⟩

中文:
引理 BicartSq.isPushout
  条件: {A₁ A₂ A₃ A₄ : X.子复形} (sq : BicartSq A₁ A₂ A₃ A₄)
  证明: rfl
  isColimit' :=
    ⟨evaluationJointlyReflectsColimits _
      (fun n => (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (by
        have h : Lattice.BicartSq (A₁.obj n) (A₂.obj n) (A₃.obj n) (A₄.obj n) :=
          { sup_eq := by
              rw [← sq.sup_eq]
              rfl
            inf_eq := by
              rw [← sq.inf_eq]
              rfl }
        exact (Types.isPushout_of_bicartSq h).isColimit))⟩
-/
lemma BicartSq.isPushout {A₁ A₂ A₃ A₄ : X.Subcomplex} (sq : BicartSq A₁ A₂ A₃ A₄) :
    IsPushout (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) where
  w := rfl
  isColimit' :=
    ⟨evaluationJointlyReflectsColimits _
      (fun n => (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (by
        have h : Lattice.BicartSq (A₁.obj n) (A₂.obj n) (A₃.obj n) (A₄.obj n) :=
          { sup_eq := by
              rw [← sq.sup_eq]
              rfl
            inf_eq := by
              rw [← sq.inf_eq]
              rfl }
        exact (Types.isPushout_of_bicartSq h).isColimit))⟩

end Subcomplex

end SSet
