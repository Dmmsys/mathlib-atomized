/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Topological Kőnig's lemma

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty. (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limitCone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [Preorder J] [IsDirectedOrder J]` and
`F : Jᵒᵖ ⥤ TopCat`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in lemmas `nonempty_sections_of_finite_cofiltered_system` and
`nonempty_sections_of_finite_inverse_system` in `Mathlib/CategoryTheory/CofilteredSystem.lean`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/

@[expose] public section

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

section TopologicalKonig

variable {J : Type u} [SmallCategory J]

variable (F : J ⥤ TopCat.{v})

set_option backward.privateInPublic true in
/--
Definition of `FiniteDiagramArrow` / `FiniteDiagramArrow` 的定义

English:
abbreviation FiniteDiagramArrow
  signature: {J : Type u} [SmallCategory J] (G : Finset J)
  body: Σ' (X Y : J) (_ : X in G) (_ : Y in G), X ⟶ Y

中文:
缩写 FiniteDiagramArrow
  签名: {J : 类型u} [小范畴 J] (G : 有限集 J)
  定义体: Σ' (X Y : J) (_ : X in G) (_ : Y in G), X ⟶ Y
-/
private abbrev FiniteDiagramArrow {J : Type u} [SmallCategory J] (G : Finset J) :=
  Σ' (X Y : J) (_ : X in G) (_ : Y in G), X ⟶ Y

set_option backward.privateInPublic true in
/--
Definition of `FiniteDiagram` / `FiniteDiagram` 的定义

English:
abbreviation FiniteDiagram
  signature: (J : Type u) [SmallCategory J]
  body: Σ G : Finset J, Finset (FiniteDiagramArrow G)

中文:
缩写 FiniteDiagram
  签名: (J : 类型u) [小范畴 J]
  定义体: Σ G : Finset J, Finset (FiniteDiagramArrow G)
-/
private abbrev FiniteDiagram (J : Type u) [SmallCategory J] :=
  Σ G : Finset J, Finset (FiniteDiagramArrow G)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `partialSections` / `partialSections` 的定义

English:
definition partialSections
  signature: {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{v}) {G : Finset J}
  body: {u | forall {f : FiniteDiagramArrow G} (_ : f in H), F.map f.2.2.2.2 (u f.1) = u f.2.1}

中文:
定义 partialSections
  签名: {J : 类型u} [小范畴 J] (F : J ⥤ 顶元素范畴.{v}) {G : 有限集 J}
  定义体: {u | forall {f : FiniteDiagramArrow G} (_ : f in H), F.map f.2.2.2.2 (u f.1) = u f.2.1}

Depends on / 依赖: F.map, FiniteDiagramArrow
-/
def partialSections {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{v}) {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : Set (forall j, F.obj j) :=
  {u | forall {f : FiniteDiagramArrow G} (_ : f in H), F.map f.2.2.2.2 (u f.1) = u f.2.1}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `partialSections.nonempty` / 定理 `partialSections.nonempty`

English:
theorem partialSections.nonempty
  statement: [IsCofilteredOrEmpty J] [h : forall j : J, Nonempty (F.obj j)]
  proof: by
  classical
  cases isEmpty_or_nonempty J
  · exact ⟨isEmptyElim, fun {j} => IsEmpty.elim' inferInstance j.1⟩
  have : IsCofiltered J := ⟨⟩
  use fun j : J =>
    if hj : j in G then F.map (IsCofiltered.infTo G H hj) (h (IsCofiltered.inf G H)).some
    else (h _).some
  rintro ⟨X, Y, hX, hY, f⟩ h

中文:
定理 partialSections.nonempty
  结论: [是余filteredOrEmpty J] [h : 对任意 j : J, 非空 (F.obj j)]
  证明: by
  classical
  cases isEmpty_or_nonempty J
  · exact ⟨isEmptyElim, fun {j} => IsEmpty.elim' inferInstance j.1⟩
  have : IsCofiltered J := ⟨⟩
  use fun j : J =>
    if hj : j in G then F.map (IsCofiltered.infTo G H hj) (h (IsCofiltered.inf G H)).some
    else (h _).some
  rintro ⟨X, Y, hX, hY, f⟩ h

Depends on / 依赖: F.map, F.map_comp, IsCofiltered, IsCofiltered.inf, IsCofiltered.infTo, IsCofiltered.infTo_commutes, IsEmpty, IsEmpty.elim, classical, comp_app, dif_pos, infTo_commutes, isEmptyElim, isEmpty_or_nonempty, map_comp
-/
theorem partialSections.nonempty [IsCofilteredOrEmpty J] [h : forall j : J, Nonempty (F.obj j)]
    {G : Finset J} (H : Finset (FiniteDiagramArrow G)) : (partialSections F H).Nonempty := by
  classical
  cases isEmpty_or_nonempty J
  · exact ⟨isEmptyElim, fun {j} => IsEmpty.elim' inferInstance j.1⟩
  have : IsCofiltered J := ⟨⟩
  use fun j : J =>
    if hj : j in G then F.map (IsCofiltered.infTo G H hj) (h (IsCofiltered.inf G H)).some
    else (h _).some
  rintro ⟨X, Y, hX, hY, f⟩ hf
  dsimp only
  rwa [dif_pos hX, dif_pos hY, ← comp_app, ← F.map_comp, @IsCofiltered.infTo_commutes _ _ _ G H]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `partialSections.directed` / 定理 `partialSections.directed`

English:
theorem partialSections.directed
  proof: by
  classical
  intro A B
  let ιA : FiniteDiagramArrow A.1 -> FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : FiniteDiagramArrow B.1 -> FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, 

中文:
定理 partialSections.directed
  证明: by
  classical
  intro A B
  let ιA : FiniteDiagramArrow A.1 -> FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : FiniteDiagramArrow B.1 -> FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, 

Depends on / 依赖: FiniteDiagramArrow, Finset, Finset.mem_union_left, Finset.mem_union_right, classical, mem_union_left, mem_union_right
-/
theorem partialSections.directed :
    Directed GE.ge fun G : FiniteDiagram J => partialSections F G.2 := by
  classical
  intro A B
  let ιA : FiniteDiagramArrow A.1 -> FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : FiniteDiagramArrow B.1 -> FiniteDiagramArrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1, Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
  refine ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, ?_, ?_⟩
  · rintro u hu f hf
    have : ιA f in A.2.image ιA ⊔ B.2.image ιB := by
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    exact hu this
  · rintro u hu f hf
    have : ιB f in A.2.image ιA ⊔ B.2.image ιB := by
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    exact hu this

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `partialSections.closed` / 定理 `partialSections.closed`

English:
theorem partialSections.closed
  statement: [forall j : J, T2Space (F.obj j)] {G : Finset J}
  proof: by
  have :
    partialSections F H =
      ⋂ (f : FiniteDiagramArrow G) (_ : f in H), {u | F.map f.2.2.2.2 (u f.1) = u f.2.1} := by
    ext1
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [this]
  apply isClosed_biInter
  intro f _
  apply isClosed_eq <;> fun_prop

中文:
定理 partialSections.closed
  结论: [对任意 j : J, T2空间 (F.obj j)] {G : 有限集 J}
  证明: by
  have :
    partialSections F H =
      ⋂ (f : FiniteDiagramArrow G) (_ : f in H), {u | F.map f.2.2.2.2 (u f.1) = u f.2.1} := by
    ext1
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [this]
  apply isClosed_biInter
  intro f _
  apply isClosed_eq <;> fun_prop

Depends on / 依赖: F.map, FiniteDiagramArrow, Set.mem_iInter, Set.mem_ofPred_eq, fun_prop, isClosed_biInter, isClosed_eq, mem_iInter, mem_ofPred_eq, partialSections
-/
theorem partialSections.closed [forall j : J, T2Space (F.obj j)] {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : IsClosed (partialSections F H) := by
  have :
    partialSections F H =
      ⋂ (f : FiniteDiagramArrow G) (_ : f in H), {u | F.map f.2.2.2.2 (u f.1) = u f.2.1} := by
    ext1
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [this]
  apply isClosed_biInter
  intro f _
  apply isClosed_eq <;> fun_prop

/--
theorem `nonempty_limitCone_of_compact_t2_cofiltered_system` / 定理 `nonempty_limitCone_of_compact_t2_cofiltered_system`

English:
theorem nonempty_limitCone_of_compact_t2_cofiltered_system
  statement: (F : J ⥤ TopCat.{max v u})
  proof: by
  classical
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun G => partialSections F _)
      (partialSections.directed F) (fun G => partialSections.nonempty F _)
      (fun G => IsClosed.isCompact (partialSections.closed F _)) fun G =>
      partialSe

中文:
定理 nonempty_limitCone_of_compact_t2_cofiltered_system
  结论: (F : J ⥤ 顶元素范畴.{最大值 v u})
  证明: by
  classical
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun G => partialSections F _)
      (partialSections.directed F) (fun G => partialSections.nonempty F _)
      (fun G => IsClosed.isCompact (partialSections.closed F _)) fun G =>
      partialSe

Depends on / 依赖: FiniteDiagram, Finset, Finset.mem_singleton_self, IsClosed, IsClosed.isCompact, IsCompact, IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed, classical, closed, directed, isCompact, mem_singleton_self, nonempty, nonempty_iInter_of_directed_nonempty_isCompact_isClosed, partialSections, partialSections.closed, partialSections.directed, partialSections.nonempty
-/
theorem nonempty_limitCone_of_compact_t2_cofiltered_system (F : J ⥤ TopCat.{max v u})
    [IsCofilteredOrEmpty J]
    [forall j : J, Nonempty (F.obj j)] [forall j : J, CompactSpace (F.obj j)] [forall j : J, T2Space (F.obj j)] :
    Nonempty (TopCat.limitCone F).pt := by
  classical
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun G => partialSections F _)
      (partialSections.directed F) (fun G => partialSections.nonempty F _)
      (fun G => IsClosed.isCompact (partialSections.closed F _)) fun G =>
      partialSections.closed F _
  use u
  intro X Y f
  let G : FiniteDiagram J := ⟨{X, Y}, {⟨X, Y, by grind, by grind, f⟩}⟩
  exact hu _ ⟨G, rfl⟩ (Finset.mem_singleton_self _)

end TopologicalKonig

end TopCat
