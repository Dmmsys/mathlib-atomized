/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Finitely presented algebras and finitely presented modules

In this file we establish relations between finitely presented as an algebra and
finitely presented as a module.

## Main results:

- `Algebra.FinitePresentation.of_finitePresentation`: If `S` is finitely presented as a
  module over `R`, then it is finitely presented as an algebra over `R`.
- `Module.FinitePresentation.of_finite_of_finitePresentation`: If `S` is finite as a module over `R`
  and finitely presented as an algebra over `R`, then it is finitely presented as a module over `R`.

## References

- [Grothendieck, EGA IV₁ 1.4.7][ega-iv-1]
-/

public section

universe u

variable (R : Type u) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/--
lemma `Module.Finite.exists_free_surjective` / 引理 `Module.Finite.exists_free_surjective`

English:
lemma Module.Finite.exists_free_surjective
  given: [Module.Finite R S]
  proof: by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  suffices h : exists (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' ->ₐ[R] S), (s : Set S) sub

中文:
引理 Module.Finite.exists_free_surjective
  条件: [Module.Finite R S]
  证明: by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  suffices h : exists (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' ->ₐ[R] S), (s : Set S) sub

Depends on / 依赖: AlgHom, AlgHom.range, Algebra, Algebra.FinitePresentation, CommRing, Finite, FinitePresentation, Function, Function.Surjective, LinearMap, LinearMap.range, LinearMap.range_eq_top, Module, Module.Finite, Module.Free, Module.finite_def.mp, Submodule, Submodule.span_le, Surjective, classical
-/
lemma Module.Finite.exists_free_surjective [Module.Finite R S] :
    exists (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' ->ₐ[R] S), Function.Surjective f := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  suffices h : exists (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Module.Finite R S')
      (_ : Module.Free R S') (_ : Algebra.FinitePresentation R S')
      (f : S' ->ₐ[R] S), (s : Set S) subseteq AlgHom.range f by
    obtain ⟨S', _, _, _, _, _, f, hsf⟩ := h
    have hf : Function.Surjective f := by
      have := (Submodule.span_le (p := LinearMap.range f.toLinearMap)).mpr hsf
      rwa [hs, top_le_iff, LinearMap.range_eq_top] at this
    use S', ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, f
  clear hs
  induction s using Finset.induction with
  | empty =>
    exact ⟨R, _, _, inferInstance, inferInstance, inferInstance, Algebra.ofId R S, by simp⟩
  | insert a s has IH =>
    obtain ⟨S', _, _, _, _, _, f, hsf⟩ := IH
    have ha := Algebra.IsIntegral.isIntegral (R := R) a
    have := ((minpoly.monic ha).map (algebraMap R S')).finite_adjoinRoot
    have := ((minpoly.monic ha).map (algebraMap R S')).free_adjoinRoot
    algebraize [f.toRingHom]
    refine ⟨AdjoinRoot ((minpoly R a).map (algebraMap R S')), inferInstance, inferInstance,
      .trans S' _, .trans (S := S'), .trans _ S' _,
      (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) a
        (by simp [← Polynomial.aeval_def])).restrictScalars R, ?_⟩
    simp only [Finset.coe_insert, AlgHom.coe_range, AlgHom.coe_restrictScalars',
      Set.insert_subset_iff, Set.mem_range]
    exact ⟨⟨.root _, by simp⟩, hsf.trans fun y ⟨x, hx⟩ => ⟨.of _ x, by simpa⟩⟩

/--
Instance `Algebra.FinitePresentation.of_finitePresentation` / 实例 `Algebra.FinitePresentation.of_finitePresentation`

English:
instance Algebra.FinitePresentation.of_finitePresentation
  body: by
  obtain ⟨S', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  refine .of_surjective hf ?_
  apply Submodule.FG.of_restrictScalars R
  exact Module.FinitePresentation.fg_ker f.toLinearMap hf

中文:
实例 Algebra.FinitePresentation.of_finitePresentation
  定义体: by
  obtain ⟨S', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  refine .of_surjective hf ?_
  apply Submodule.FG.of_restrictScalars R
  exact Module.FinitePresentation.fg_ker f.toLinearMap hf

Depends on / 依赖: Finite, FinitePresentation, Module, Module.Finite.exists_free_surjective, Module.FinitePresentation.fg_ker, Submodule, Submodule.FG.of_restrictScalars, exists_free_surjective, f.toLinearMap, fg_ker, of_restrictScalars, of_surjective, toLinearMap
-/
instance Algebra.FinitePresentation.of_finitePresentation
    [Module.FinitePresentation R S] : Algebra.FinitePresentation R S := by
  obtain ⟨S', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  refine .of_surjective hf ?_
  apply Submodule.FG.of_restrictScalars R
  exact Module.FinitePresentation.fg_ker f.toLinearMap hf

/-- If `S` is finite as a module over `R` and finitely presented as an algebra over `R`, then
it is finitely presented as a module over `R`. -/
@[stacks 0564 "The case M = S"]
/--
lemma `Module.FinitePresentation.of_finite_of_finitePresentation` / 引理 `Module.FinitePresentation.of_finite_of_finitePresentation`

English:
lemma Module.FinitePresentation.of_finite_of_finitePresentation
  proof: by
  obtain ⟨R', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R R' S := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.FinitePresentation R R' :=
    Module.finitePresentation_of_projective R R'
  have : Module.Fin

中文:
引理 Module.FinitePresentation.of_finite_of_finitePresentation
  证明: by
  obtain ⟨R', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R R' S := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.FinitePresentation R R' :=
    Module.finitePresentation_of_projective R R'
  have : Module.Fin

Depends on / 依赖: Algebra, Algebra.FinitePresentation.ker_fG_of_surjective, Algebra.linearMap, Finite, FinitePresentation, IsScalarTower, Module, Module.Finite.exists_free_surjective, Module.FinitePresentation, Module.finitePresentation_of_projective, Module.finitePresentation_of_surjective, comp_algebraMap, exists_free_surjective, f.comp_algebraMap.symm, f.toRingHom.toAlgebra, finitePresentation_of_projective, finitePresentation_of_surjective, ker_fG_of_surjective, linearMap, of_algebraMap_eq
-/
lemma Module.FinitePresentation.of_finite_of_finitePresentation
    [Module.Finite R S] [Algebra.FinitePresentation R S] :
    Module.FinitePresentation R S := by
  obtain ⟨R', _, _, _, _, _, f, hf⟩ := Module.Finite.exists_free_surjective R S
  let := f.toRingHom.toAlgebra
  have : IsScalarTower R R' S := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.FinitePresentation R R' :=
    Module.finitePresentation_of_projective R R'
  have : Module.FinitePresentation R' S :=
    Module.finitePresentation_of_surjective (Algebra.linearMap R' S) hf
      (Algebra.FinitePresentation.ker_fG_of_surjective f hf)
  exact .trans R S R'

/--
lemma `Module.FinitePresentation.iff_finitePresentation_of_finite` / 引理 `Module.FinitePresentation.iff_finitePresentation_of_finite`

English:
lemma Module.FinitePresentation.iff_finitePresentation_of_finite
  given: [Module.Finite R S]
  proof: ⟨fun _ => .of_finitePresentation R S, fun _ => .of_finite_of_finitePresentation R S⟩

中文:
引理 Module.FinitePresentation.iff_finitePresentation_of_finite
  条件: [Module.Finite R S]
  证明: ⟨fun _ => .of_finitePresentation R S, fun _ => .of_finite_of_finitePresentation R S⟩

Depends on / 依赖: of_finitePresentation, of_finite_of_finitePresentation
-/
lemma Module.FinitePresentation.iff_finitePresentation_of_finite [Module.Finite R S] :
    Module.FinitePresentation R S ↔ Algebra.FinitePresentation R S :=
  ⟨fun _ => .of_finitePresentation R S, fun _ => .of_finite_of_finitePresentation R S⟩
