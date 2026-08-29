/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Kan complexes

In this file, the abbreviation `KanComplex` is introduced for
fibrant objects in the category `SSet` which is equipped with
Kan fibrations.

In `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean`
we show that every Kan complex is a quasicategory.

## TODO

- Show that the singular simplicial set of a topological space is a Kan complex.

-/

public section

universe u

namespace SSet

open CategoryTheory Simplicial Limits HomotopicalAlgebra

open modelCategoryQuillen in
/--
Definition of `KanComplex` / `KanComplex` 的定义

English:
abbreviation KanComplex
  signature: (S : SSet.{u})
  body: HomotopicalAlgebra.IsFibrant S

中文:
缩写 KanComplex
  签名: (S : SSet.{u})
  定义体: HomotopicalAlgebra.IsFibrant S

Depends on / 依赖: HomotopicalAlgebra, HomotopicalAlgebra.IsFibrant, IsFibrant
-/
abbrev KanComplex (S : SSet.{u}) : Prop := HomotopicalAlgebra.IsFibrant S

/--
lemma `KanComplex.hornFilling` / 引理 `KanComplex.hornFilling`

English:
lemma KanComplex.hornFilling
  statement: {S : SSet.{u}} [KanComplex S]
  proof: by
  have sq' : CommSq σ₀ Λ[n + 1, i].ι (terminal.from S) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq'.lift, by simp⟩

中文:
引理 KanComplex.hornFilling
  结论: {S : SSet.{u}} [KanComplex S]
  证明: by
  have sq' : CommSq σ₀ Λ[n + 1, i].ι (terminal.from S) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq'.lift, by simp⟩

Depends on / 依赖: CommSq, terminal, terminal.from
-/
lemma KanComplex.hornFilling {S : SSet.{u}} [KanComplex S]
    {n : Nat} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    exists σ : Δ[n + 1] ⟶ S, σ₀ = Λ[n + 1, i].ι ≫ σ := by
  have sq' : CommSq σ₀ Λ[n + 1, i].ι (terminal.from S) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq'.lift, by simp⟩

namespace horn.IsCompatible

variable {X : SSet.{u}} {n : Nat}
  {i : Fin (n + 2)} {f : forall (j : Fin (n + 2)) (_ : j != i), Δ[n] ⟶ X}

/--
lemma `exists_lift_of_kanComplex` / 引理 `exists_lift_of_kanComplex`

English:
lemma exists_lift_of_kanComplex
  statement: [KanComplex X]
  proof: by
  obtain ⟨φ, hφ, _⟩ := hf.exists_lift (terminal.from _) (terminal.from _) (by simp)
  exact ⟨φ, hφ⟩

中文:
引理 exists_lift_of_kanComplex
  结论: [KanComplex X]
  证明: by
  obtain ⟨φ, hφ, _⟩ := hf.exists_lift (terminal.from _) (terminal.from _) (by simp)
  exact ⟨φ, hφ⟩

Depends on / 依赖: exists_lift, hf.exists_lift, terminal, terminal.from
-/
lemma exists_lift_of_kanComplex [KanComplex X]
    (hf : horn.IsCompatible f) :
    exists (φ : Δ[n + 1] ⟶ X),
      forall (j : Fin (n + 2)) (hj : j != i), stdSimplex.δ j ≫ φ = f j hj := by
  obtain ⟨φ, hφ, _⟩ := hf.exists_lift (terminal.from _) (terminal.from _) (by simp)
  exact ⟨φ, hφ⟩

/--
Definition of `liftOfKanComplex` / `liftOfKanComplex` 的定义

English:
definition liftOfKanComplex
  signature: [KanComplex X] (hf : horn.IsCompatible f)
  body: hf.exists_lift_of_kanComplex.choose

@[reassoc]

中文:
定义 liftOfKanComplex
  签名: [KanComplex X] (hf : horn.IsCompatible f)
  定义体: hf.exists_lift_of_kanComplex.choose

@[reassoc]

Depends on / 依赖: exists_lift_of_kanComplex, hf.exists_lift_of_kanComplex.choose
-/
noncomputable def liftOfKanComplex [KanComplex X] (hf : horn.IsCompatible f) :
    Δ[n + 1] ⟶ X :=
  hf.exists_lift_of_kanComplex.choose

@[reassoc]
/--
lemma `δ_liftOfKanComplex` / 引理 `δ_liftOfKanComplex`

English:
lemma δ_liftOfKanComplex
  statement: [KanComplex X] (hf : horn.IsCompatible f)
  proof: hf.exists_lift_of_kanComplex.choose_spec j hj

中文:
引理 δ_liftOfKanComplex
  结论: [KanComplex X] (hf : horn.IsCompatible f)
  证明: hf.exists_lift_of_kanComplex.choose_spec j hj

Depends on / 依赖: choose_spec, exists_lift_of_kanComplex, hf.exists_lift_of_kanComplex.choose_spec, hf.liftOfKanComplex, liftOfKanComplex, stdSimplex
-/
lemma δ_liftOfKanComplex [KanComplex X] (hf : horn.IsCompatible f)
    (j : Fin (n + 2)) (hj : j != i := by grind) :
    stdSimplex.δ j ≫ hf.liftOfKanComplex = f j hj :=
  hf.exists_lift_of_kanComplex.choose_spec j hj

end horn.IsCompatible

open modelCategoryQuillen in
/--
lemma `KanComplex.iff` / 引理 `KanComplex.iff`

English:
lemma KanComplex.iff
  given: {Z : SSet.{u}}
  proof: by
  refine ⟨fun _ n i f hf => hf.exists_lift_of_kanComplex,
    fun h => (isFibrant_iff _).2 ⟨?_⟩⟩
  rw [fibrations_eq]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  refine ⟨fun {t _} _ => ?_⟩
  obtain ⟨φ, hφ⟩ := h _ (horn.IsCompatible.of_hom t)
  exact

中文:
引理 KanComplex.iff
  条件: {Z : SSet.{u}}
  证明: by
  refine ⟨fun _ n i f hf => hf.exists_lift_of_kanComplex,
    fun h => (isFibrant_iff _).2 ⟨?_⟩⟩
  rw [fibrations_eq]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  refine ⟨fun {t _} _ => ?_⟩
  obtain ⟨φ, hφ⟩ := h _ (horn.IsCompatible.of_hom t)
  exact

Depends on / 依赖: IsCompatible, MorphismProperty, MorphismProperty.iSup_iff, exists_lift_of_kanComplex, fac_left, fac_right, fibrations_eq, hf.exists_lift_of_kanComplex, hom_ext, horn.IsCompatible.of_hom, horn.hom_ext, iSup_iff, isFibrant_iff, of_hom, subsingleton
-/
lemma KanComplex.iff {Z : SSet.{u}} :
    KanComplex Z ↔
      forall ⦃n : Nat⦄ ⦃i : Fin (n + 2)⦄ (f : forall (j : Fin (n + 2)) (_ : j != i), Δ[n] ⟶ Z)
        (_ : horn.IsCompatible f),
        exists (φ : Δ[n + 1] ⟶ Z),
          forall (j : Fin (n + 2)) (hj : j != i), stdSimplex.δ j ≫ φ = f j hj := by
  refine ⟨fun _ n i f hf => hf.exists_lift_of_kanComplex,
    fun h => (isFibrant_iff _).2 ⟨?_⟩⟩
  rw [fibrations_eq]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  refine ⟨fun {t _} _ => ?_⟩
  obtain ⟨φ, hφ⟩ := h _ (horn.IsCompatible.of_hom t)
  exact ⟨⟨{
    l := φ
    fac_left := horn.hom_ext' (by simpa using hφ)
    fac_right := by subsingleton }⟩⟩

end SSet
