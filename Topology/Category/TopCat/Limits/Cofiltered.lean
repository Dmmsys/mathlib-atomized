/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Cofiltered limits in the category of topological spaces

Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `Set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/

public section


open TopologicalSpace Topology

open CategoryTheory

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace TopCat

section CofilteredLimit

variable {J : Type v} [Category.{w} J] [IsCofiltered J] (F : J ⥤ TopCat.{max v u}) (C : Cone F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `isTopologicalBasis_cofiltered_limit` / 定理 `isTopologicalBasis_cofiltered_limit`

English:
theorem isTopologicalBasis_cofiltered_limit
  statement: (hC : IsLimit C) (T : forall j, Set (Set (F.obj j)))
  proof: by
  classical
  convert! IsTopologicalBasis.iInf_induced hT fun j (x : C.pt) => C.π.app j x using 1
  · exact induced_of_isLimit C hC
  ext U0
  constructor
  · rintro ⟨j, V, hV, rfl⟩
    let U : forall i, Set (F.obj i) := fun i => if h : i = j then by rw [h]; exact V else Set.univ
    refine ⟨U, {

中文:
定理 isTopologicalBasis_cofiltered_limit
  结论: (hC : IsLimit C) (T : 对任意 j, Set (Set (F.obj j)))
  证明: by
  classical
  convert! IsTopologicalBasis.iInf_induced hT fun j (x : C.pt) => C.π.app j x using 1
  · exact induced_of_isLimit C hC
  ext U0
  constructor
  · rintro ⟨j, V, hV, rfl⟩
    let U : forall i, Set (F.obj i) := fun i => if h : i = j then by rw [h]; exact V else Set.univ
    refine ⟨U, {

Depends on / 依赖: C.pt, F.obj, Finset, Finset.mem_singleton, IsCofiltered, IsCofiltered.inf_objs_exists, IsTopologicalBasis, IsTopologicalBasis.iInf_induced, Set.univ, classical, convert, iInf_induced, induced_of_isLimit, inf_objs_exists, mem_singleton
-/
theorem isTopologicalBasis_cofiltered_limit (hC : IsLimit C) (T : forall j, Set (Set (F.obj j)))
    (hT : forall j, IsTopologicalBasis (T j)) (univ : forall i : J, Set.univ in T i)
    (inter : forall (i) (U1 U2 : Set (F.obj i)), U1 in T i -> U2 in T i -> U1 inter U2 in T i)
    (compat : forall (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (_hV : V in T j), F.map f ⁻¹' V in T i) :
    IsTopologicalBasis
      {U : Set C.pt | exists (j : _) (V : Set (F.obj j)), V in T j ∧ U = C.π.app j ⁻¹' V} := by
  classical
  convert! IsTopologicalBasis.iInf_induced hT fun j (x : C.pt) => C.π.app j x using 1
  · exact induced_of_isLimit C hC
  ext U0
  constructor
  · rintro ⟨j, V, hV, rfl⟩
    let U : forall i, Set (F.obj i) := fun i => if h : i = j then by rw [h]; exact V else Set.univ
    refine ⟨U, {j}, ?_, ?_⟩
    · simp only [Finset.mem_singleton]
      rintro i rfl
      simpa [U]
    · simp [U]
  · rintro ⟨U, G, h1, h2⟩
    obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists G
    let g : forall e in G, j ⟶ e := fun _ he => (hj he).some
    let Vs : J -> Set (F.obj j) := fun e => if h : e in G then F.map (g e h) ⁻¹' U e else Set.univ
    let V : Set (F.obj j) := ⋂ (e : J) (_he : e in G), Vs e
    refine ⟨j, V, ?_, ?_⟩
    · -- An intermediate claim used to apply induction along `G : Finset J` later on.
      have :
        forall (S : Set (Set (F.obj j))) (E : Finset J) (P : J -> Set (F.obj j)) (_univ : Set.univ in S)
          (_inter : forall A B : Set (F.obj j), A in S -> B in S -> A inter B in S)
          (_cond : forall (e : J) (_he : e in E), P e in S), (⋂ (e) (_he : e in E), P e) in S := by
        intro S E
        induction E using Finset.induction_on with
        | empty =>
          intro P he _hh
          simpa
        | insert a E _ha hh1 =>
          intro hh2 hh3 hh4 hh5
          rw [Finset.set_biInter_insert]
          refine hh4 _ _ (hh5 _ (Finset.mem_insert_self _ _)) (hh1 _ hh3 hh4 ?_)
          intro e he
          exact hh5 e (Finset.mem_insert_of_mem he)
      -- use the intermediate claim to finish off the goal using `univ` and `inter`.
      refine this _ _ _ (univ _) (inter _) ?_
      intro e he
      dsimp [Vs]
      rw [dif_pos he]
      exact compat j e (g e he) (U e) (h1 e he)
    · -- conclude...
      rw [h2]
      change _ = (C.π.app j) ⁻¹' ⋂ (e : J) (_ : e in G), Vs e
      rw [Set.preimage_iInter]
      apply congrArg
      ext1 e
      rw [Set.preimage_iInter]
      apply congrArg
      ext1 he
      simp [Vs, dif_pos he, ← Set.preimage_comp, ← coe_comp]

end CofilteredLimit

end TopCat
