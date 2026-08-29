/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Final.Connected
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Final functors with filtered (co)domain

If `C` is a filtered category, then the usual equivalent conditions for a functor `F : C ⥤ D` to be
final can be restated. We show:

* `final_iff_of_isFiltered`: a concrete description of finality which is sometimes a convenient way
  to show that a functor is final.
* `final_iff_isFiltered_structuredArrow`: `F` is final if and only if `StructuredArrow d F` is
  filtered for all `d : D`, which strengthens the usual statement that `F` is final if and only
  if `StructuredArrow d F` is connected for all `d : D`.
* Under categories of objects of filtered categories are filtered and their forgetful functors
  are final.
* If `D` is a filtered category and `F : C ⥤ D` is fully faithful and satisfies the additional
  condition that for every `d : D` there is an object `c : D` and a morphism `d ⟶ F.obj c`, then
  `C` is filtered and `F` is final.
* Finality and initiality of diagonal functors `diag : C ⥤ C × C` and of projection functors
  of (co)structured arrow categories.
* Finality of `StructuredArrow.post`, given the finality of its arguments.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 3.2

-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/--
theorem `Functor.final_of_isFiltered_structuredArrow` / 定理 `Functor.final_of_isFiltered_structuredArrow`

English:
theorem Functor.final_of_isFiltered_structuredArrow
  given: [forall d, IsFiltered (StructuredArrow d F)]
  proof: IsFiltered.isConnected _

中文:
定理 Functor.final_of_isFiltered_structuredArrow
  条件: [对任意 d, IsFiltered (StructuredArrow d F)]
  证明: IsFiltered.isConnected _

Depends on / 依赖: IsFiltered, IsFiltered.isConnected, isConnected
-/
theorem Functor.final_of_isFiltered_structuredArrow [forall d, IsFiltered (StructuredArrow d F)] :
    Final F where
  out _ := IsFiltered.isConnected _

/--
theorem `Functor.initial_of_isCofiltered_costructuredArrow` / 定理 `Functor.initial_of_isCofiltered_costructuredArrow`

English:
theorem Functor.initial_of_isCofiltered_costructuredArrow
  proof: IsCofiltered.isConnected _

中文:
定理 Functor.initial_of_isCofiltered_costructuredArrow
  证明: IsCofiltered.isConnected _

Depends on / 依赖: IsCofiltered, IsCofiltered.isConnected, isConnected
-/
theorem Functor.initial_of_isCofiltered_costructuredArrow
    [forall d, IsCofiltered (CostructuredArrow F d)] : Initial F where
  out _ := IsCofiltered.isConnected _

/--
theorem `isFiltered_structuredArrow_of_isFiltered_of_exists` / 定理 `isFiltered_structuredArrow_of_isFiltered_of_exists`

English:
theorem isFiltered_structuredArrow_of_isFiltered_of_exists
  statement: [IsFilteredOrEmpty C] (d : D)
  proof: by
  have : Nonempty (StructuredArrow d F) := by
    obtain ⟨c, ⟨f⟩⟩ := h₁
    exact ⟨.mk f⟩
  suffices IsFilteredOrEmpty (StructuredArrow d F) from IsFiltered.mk
  refine ⟨fun f g => ?_, fun f g η μ => ?_⟩
  · obtain ⟨c, ⟨t, ht⟩⟩ := h₂ (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right))
        

中文:
定理 isFiltered_structuredArrow_of_isFiltered_of_exists
  结论: [IsFilteredOrEmpty C] (d : D)
  证明: by
  have : Nonempty (StructuredArrow d F) := by
    obtain ⟨c, ⟨f⟩⟩ := h₁
    exact ⟨.mk f⟩
  suffices IsFilteredOrEmpty (StructuredArrow d F) from IsFiltered.mk
  refine ⟨fun f g => ?_, fun f g η μ => ?_⟩
  · obtain ⟨c, ⟨t, ht⟩⟩ := h₂ (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right))
        

Depends on / 依赖: F.map, IsFiltered, IsFiltered.leftToMax, IsFiltered.mk, IsFiltered.rightToMax, IsFilteredOrEmpty, Nonempty, Struct, StructuredArrow, StructuredArrow.homMk, f.hom, f.right, g.hom, g.right, leftToMax, rightToMax
-/
theorem isFiltered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C] (d : D)
    (h₁ : exists c, Nonempty (d ⟶ F.obj c)) (h₂ : forall {c : C} (s s' : d ⟶ F.obj c),
      exists (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) :
    IsFiltered (StructuredArrow d F) := by
  have : Nonempty (StructuredArrow d F) := by
    obtain ⟨c, ⟨f⟩⟩ := h₁
    exact ⟨.mk f⟩
  suffices IsFilteredOrEmpty (StructuredArrow d F) from IsFiltered.mk
  refine ⟨fun f g => ?_, fun f g η μ => ?_⟩
  · obtain ⟨c, ⟨t, ht⟩⟩ := h₂ (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right))
        (g.hom ≫ F.map (IsFiltered.rightToMax f.right g.right))
    refine ⟨.mk (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right ≫ t)), ?_, ?_, trivial⟩
    · exact StructuredArrow.homMk (IsFiltered.leftToMax _ _ ≫ t) rfl
    · exact StructuredArrow.homMk (IsFiltered.rightToMax _ _ ≫ t) (by simpa using ht.symm)
  · refine ⟨.mk (f.hom ≫ F.map (η.right ≫ IsFiltered.coeqHom η.right μ.right)),
      StructuredArrow.homMk (IsFiltered.coeqHom η.right μ.right) (by simp), ?_⟩
    simpa using IsFiltered.coeq_condition _ _

/--
theorem `isCofiltered_costructuredArrow_of_isCofiltered_of_exists` / 定理 `isCofiltered_costructuredArrow_of_isCofiltered_of_exists`

English:
theorem isCofiltered_costructuredArrow_of_isCofiltered_of_exists
  statement: [IsCofilteredOrEmpty C] (d : D)
  proof: by
  suffices IsFiltered (CostructuredArrow F d)ᵒᵖ from isCofiltered_of_isFiltered_op _
  suffices IsFiltered (StructuredArrow (op d) F.op) from
    IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  apply isFiltered_structuredArrow_of_isFiltered_of_exists
  · obtain ⟨c, ⟨t⟩⟩ := h

中文:
定理 isCofiltered_costructuredArrow_of_isCofiltered_of_exists
  结论: [IsCofilteredOrEmpty C] (d : D)
  证明: by
  suffices IsFiltered (CostructuredArrow F d)ᵒᵖ from isCofiltered_of_isFiltered_op _
  suffices IsFiltered (StructuredArrow (op d) F.op) from
    IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  apply isFiltered_structuredArrow_of_isFiltered_of_exists
  · obtain ⟨c, ⟨t⟩⟩ := h

Depends on / 依赖: CostructuredArrow, F.op, IsFiltered, IsFiltered.of_equivalence, Quiver, Quiver.Hom.op, Quiver.Hom.unop_inj, StructuredArrow, costructuredArrowOpEquivalence, isCofiltered_of_isFiltered_op, isFiltered_structuredArrow_of_isFiltered_of_exists, of_equivalence, s.unop, unop_inj
-/
theorem isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEmpty C] (d : D)
    (h₁ : exists c, Nonempty (F.obj c ⟶ d)) (h₂ : forall {c : C} (s s' : F.obj c ⟶ d),
      exists (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') :
    IsCofiltered (CostructuredArrow F d) := by
  suffices IsFiltered (CostructuredArrow F d)ᵒᵖ from isCofiltered_of_isFiltered_op _
  suffices IsFiltered (StructuredArrow (op d) F.op) from
    IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  apply isFiltered_structuredArrow_of_isFiltered_of_exists
  · obtain ⟨c, ⟨t⟩⟩ := h₁
    exact ⟨op c, ⟨Quiver.Hom.op t⟩⟩
  · intro c s s'
    obtain ⟨c', t, ht⟩ := h₂ s.unop s'.unop
    exact ⟨op c', Quiver.Hom.op t, Quiver.Hom.unop_inj ht⟩

/--
theorem `exists_eq_of_isCofiltered_costructuredArrow` / 定理 `exists_eq_of_isCofiltered_costructuredArrow`

English:
theorem exists_eq_of_isCofiltered_costructuredArrow
  statement: {d : D}
  proof: by
  obtain ⟨W, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs
    (CostructuredArrow.mk s₁) (CostructuredArrow.mk s₂)
  exact ⟨W.left, p₁.left, p₂.left, (CostructuredArrow.w p₁).trans (CostructuredArrow.w p₂).symm⟩

中文:
定理 exists_eq_of_isCofiltered_costructuredArrow
  结论: {d : D}
  证明: by
  obtain ⟨W, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs
    (CostructuredArrow.mk s₁) (CostructuredArrow.mk s₂)
  exact ⟨W.left, p₁.left, p₂.left, (CostructuredArrow.w p₁).trans (CostructuredArrow.w p₂).symm⟩

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, CostructuredArrow.w, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, W.left, cone_objs
-/
theorem exists_eq_of_isCofiltered_costructuredArrow {d : D}
    [IsCofiltered (CostructuredArrow F d)] {c₁ c₂ : C}
    (s₁ : F.obj c₁ ⟶ d) (s₂ : F.obj c₂ ⟶ d) :
    exists (c : C) (t₁ : c ⟶ c₁) (t₂ : c ⟶ c₂), F.map t₁ ≫ s₁ = F.map t₂ ≫ s₂ := by
  obtain ⟨W, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs
    (CostructuredArrow.mk s₁) (CostructuredArrow.mk s₂)
  exact ⟨W.left, p₁.left, p₂.left, (CostructuredArrow.w p₁).trans (CostructuredArrow.w p₂).symm⟩

/--
theorem `Functor.final_of_exists_of_isFiltered` / 定理 `Functor.final_of_exists_of_isFiltered`

English:
theorem Functor.final_of_exists_of_isFiltered
  statement: [IsFilteredOrEmpty C]
  proof: by
  suffices forall d, IsFiltered (StructuredArrow d F) from final_of_isFiltered_structuredArrow F
  exact fun d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h₁ d) h₂

中文:
定理 Functor.final_of_exists_of_isFiltered
  结论: [IsFilteredOrEmpty C]
  证明: by
  suffices forall d, IsFiltered (StructuredArrow d F) from final_of_isFiltered_structuredArrow F
  exact fun d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h₁ d) h₂

Depends on / 依赖: IsFiltered, StructuredArrow, final_of_isFiltered_structuredArrow, isFiltered_structuredArrow_of_isFiltered_of_exists
-/
theorem Functor.final_of_exists_of_isFiltered [IsFilteredOrEmpty C]
    (h₁ : forall d, exists c, Nonempty (d ⟶ F.obj c)) (h₂ : forall {d : D} {c : C} (s s' : d ⟶ F.obj c),
      exists (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) : Functor.Final F := by
  suffices forall d, IsFiltered (StructuredArrow d F) from final_of_isFiltered_structuredArrow F
  exact fun d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h₁ d) h₂

/--
theorem `Functor.final_const_of_isTerminal` / 定理 `Functor.final_const_of_isTerminal`

English:
theorem Functor.final_const_of_isTerminal
  given: [IsFiltered C] {X : D} (hX : IsTerminal X)
  proof: Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨IsFiltered.nonempty.some, ⟨hX.from _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

中文:
定理 Functor.final_const_of_isTerminal
  条件: [IsFiltered C] {X : D} (hX : IsTerminal X)
  证明: Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨IsFiltered.nonempty.some, ⟨hX.from _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

Depends on / 依赖: Functor, Functor.final_of_exists_of_isFiltered, IsFiltered, IsFiltered.nonempty.some, final_of_exists_of_isFiltered, hX.from, hX.hom_ext, hom_ext, nonempty
-/
theorem Functor.final_const_of_isTerminal [IsFiltered C] {X : D} (hX : IsTerminal X) :
    ((Functor.const C).obj X).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨IsFiltered.nonempty.some, ⟨hX.from _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

/--
theorem `Functor.final_const_terminal` / 定理 `Functor.final_const_terminal`

English:
theorem Functor.final_const_terminal
  given: [IsFiltered C] [HasTerminal D]
  proof: Functor.final_const_of_isTerminal terminalIsTerminal

中文:
定理 Functor.final_const_terminal
  条件: [IsFiltered C] [HasTerminal D]
  证明: Functor.final_const_of_isTerminal terminalIsTerminal

Depends on / 依赖: Functor, Functor.final_const_of_isTerminal, final_const_of_isTerminal, terminalIsTerminal
-/
theorem Functor.final_const_terminal [IsFiltered C] [HasTerminal D] :
    ((Functor.const C).obj (⊤_ D)).Final :=
  Functor.final_const_of_isTerminal terminalIsTerminal

/--
theorem `Functor.initial_of_exists_of_isCofiltered` / 定理 `Functor.initial_of_exists_of_isCofiltered`

English:
theorem Functor.initial_of_exists_of_isCofiltered
  statement: [IsCofilteredOrEmpty C]
  proof: by
  suffices forall d, IsCofiltered (CostructuredArrow F d) from
    initial_of_isCofiltered_costructuredArrow F
  exact fun d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h₁ d) h₂

中文:
定理 Functor.initial_of_exists_of_isCofiltered
  结论: [IsCofilteredOrEmpty C]
  证明: by
  suffices forall d, IsCofiltered (CostructuredArrow F d) from
    initial_of_isCofiltered_costructuredArrow F
  exact fun d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h₁ d) h₂

Depends on / 依赖: CostructuredArrow, IsCofiltered, initial_of_isCofiltered_costructuredArrow, isCofiltered_costructuredArrow_of_isCofiltered_of_exists
-/
theorem Functor.initial_of_exists_of_isCofiltered [IsCofilteredOrEmpty C]
    (h₁ : forall d, exists c, Nonempty (F.obj c ⟶ d)) (h₂ : forall {d : D} {c : C} (s s' : F.obj c ⟶ d),
      exists (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') : Functor.Initial F := by
  suffices forall d, IsCofiltered (CostructuredArrow F d) from
    initial_of_isCofiltered_costructuredArrow F
  exact fun d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h₁ d) h₂

/--
theorem `Functor.initial_const_of_isInitial` / 定理 `Functor.initial_const_of_isInitial`

English:
theorem Functor.initial_const_of_isInitial
  given: [IsCofiltered C] {X : D} (hX : IsInitial X)
  proof: Functor.initial_of_exists_of_isCofiltered _ (fun _ => ⟨IsCofiltered.nonempty.some, ⟨hX.to _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

中文:
定理 Functor.initial_const_of_isInitial
  条件: [IsCofiltered C] {X : D} (hX : IsInitial X)
  证明: Functor.initial_of_exists_of_isCofiltered _ (fun _ => ⟨IsCofiltered.nonempty.some, ⟨hX.to _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

Depends on / 依赖: Functor, Functor.initial_of_exists_of_isCofiltered, IsCofiltered, IsCofiltered.nonempty.some, hX.hom_ext, hX.to, hom_ext, initial_of_exists_of_isCofiltered, nonempty
-/
theorem Functor.initial_const_of_isInitial [IsCofiltered C] {X : D} (hX : IsInitial X) :
    ((Functor.const C).obj X).Initial :=
  Functor.initial_of_exists_of_isCofiltered _ (fun _ => ⟨IsCofiltered.nonempty.some, ⟨hX.to _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

/--
theorem `Functor.initial_const_initial` / 定理 `Functor.initial_const_initial`

English:
theorem Functor.initial_const_initial
  given: [IsCofiltered C] [HasInitial D]
  proof: Functor.initial_const_of_isInitial initialIsInitial

中文:
定理 Functor.initial_const_initial
  条件: [IsCofiltered C] [HasInitial D]
  证明: Functor.initial_const_of_isInitial initialIsInitial

Depends on / 依赖: Functor, Functor.initial_const_of_isInitial, initialIsInitial, initial_const_of_isInitial
-/
theorem Functor.initial_const_initial [IsCofiltered C] [HasInitial D] :
    ((Functor.const C).obj (⊥_ D)).Initial :=
  Functor.initial_const_of_isInitial initialIsInitial

/--
theorem `IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful` / 定理 `IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful`

English:
theorem IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful
  statement: [IsFilteredOrEmpty D] [F.Full]
  proof: by
    obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.max (F.obj c) (F.obj c'))
    exact ⟨c₀, F.preimage (IsFiltered.leftToMax _ _ ≫ f),
      F.preimage (IsFiltered.rightToMax _ _ ≫ f), trivial⟩
  cocone_maps {c c'} f g := by
    obtain ⟨c₀, ⟨f₀⟩⟩ := h (IsFiltered.coeq (F.map f) (F.map g))
    refine ⟨_, F.pre

中文:
定理 IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful
  结论: [IsFilteredOrEmpty D] [F.Full]
  证明: by
    obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.max (F.obj c) (F.obj c'))
    exact ⟨c₀, F.preimage (IsFiltered.leftToMax _ _ ≫ f),
      F.preimage (IsFiltered.rightToMax _ _ ≫ f), trivial⟩
  cocone_maps {c c'} f g := by
    obtain ⟨c₀, ⟨f₀⟩⟩ := h (IsFiltered.coeq (F.map f) (F.map g))
    refine ⟨_, F.pre

Depends on / 依赖: F.map, F.map_injective, F.obj, F.preimage, IsFiltered, IsFiltered.coeq, IsFiltered.coeqHom, IsFiltered.coeq_condition, IsFiltered.leftToMax, IsFiltered.max, IsFiltered.rightToMax, cocone_maps, coeqHom, coeq_condition, leftToMax, map_injective, preimage, reassoc_of, rightToMax
-/
theorem IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : forall d, exists c, Nonempty (d ⟶ F.obj c)) : IsFilteredOrEmpty C where
  cocone_objs c c' := by
    obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.max (F.obj c) (F.obj c'))
    exact ⟨c₀, F.preimage (IsFiltered.leftToMax _ _ ≫ f),
      F.preimage (IsFiltered.rightToMax _ _ ≫ f), trivial⟩
  cocone_maps {c c'} f g := by
    obtain ⟨c₀, ⟨f₀⟩⟩ := h (IsFiltered.coeq (F.map f) (F.map g))
    refine ⟨_, F.preimage (IsFiltered.coeqHom (F.map f) (F.map g) ≫ f₀), F.map_injective ?_⟩
    simp [reassoc_of% (IsFiltered.coeq_condition (F.map f) (F.map g))]

/--
theorem `IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful` / 定理 `IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful`

English:
theorem IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful
  statement: [IsCofilteredOrEmpty D]
  proof: by
  suffices IsFilteredOrEmpty Cᵒᵖ from isCofilteredOrEmpty_of_isFilteredOrEmpty_op _
  refine IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

中文:
定理 IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful
  结论: [IsCofilteredOrEmpty D]
  证明: by
  suffices IsFilteredOrEmpty Cᵒᵖ from isCofilteredOrEmpty_of_isFilteredOrEmpty_op _
  refine IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

Depends on / 依赖: F.op, IsFilteredOrEmpty, IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful, d.unop, f.op, isCofilteredOrEmpty_of_isFilteredOrEmpty_op, of_exists_of_isFiltered_of_fullyFaithful
-/
theorem IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D]
    [F.Full] [F.Faithful] (h : forall d, exists c, Nonempty (F.obj c ⟶ d)) : IsCofilteredOrEmpty C := by
  suffices IsFilteredOrEmpty Cᵒᵖ from isCofilteredOrEmpty_of_isFilteredOrEmpty_op _
  refine IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

/--
theorem `IsFiltered.of_exists_of_isFiltered_of_fullyFaithful` / 定理 `IsFiltered.of_exists_of_isFiltered_of_fullyFaithful`

English:
theorem IsFiltered.of_exists_of_isFiltered_of_fullyFaithful
  statement: [IsFiltered D] [F.Full] [F.Faithful]
  proof: { IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsFiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

中文:
定理 IsFiltered.of_exists_of_isFiltered_of_fullyFaithful
  结论: [IsFiltered D] [F.Full] [F.Faithful]
  证明: { IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsFiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

Depends on / 依赖: Classical, Classical.arbitrary, IsFiltered, IsFiltered.nonempty, IsFilteredOrEmpty, IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful, Nonempty, arbitrary, nonempty, of_exists_of_isFiltered_of_fullyFaithful
-/
theorem IsFiltered.of_exists_of_isFiltered_of_fullyFaithful [IsFiltered D] [F.Full] [F.Faithful]
    (h : forall d, exists c, Nonempty (d ⟶ F.obj c)) : IsFiltered C :=
  { IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsFiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

/--
theorem `IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful` / 定理 `IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful`

English:
theorem IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
  statement: [IsCofiltered D] [F.Full]
  proof: { IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsCofiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

中文:
定理 IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
  结论: [IsCofiltered D] [F.Full]
  证明: { IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsCofiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

Depends on / 依赖: Classical, Classical.arbitrary, IsCofiltered, IsCofiltered.nonempty, IsCofilteredOrEmpty, IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful, Nonempty, arbitrary, nonempty, of_exists_of_isCofiltered_of_fullyFaithful
-/
theorem IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful [IsCofiltered D] [F.Full]
    [F.Faithful] (h : forall d, exists c, Nonempty (F.obj c ⟶ d)) : IsCofiltered C :=
  { IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsCofiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

/--
theorem `Functor.final_of_exists_of_isFiltered_of_fullyFaithful` / 定理 `Functor.final_of_exists_of_isFiltered_of_fullyFaithful`

English:
theorem Functor.final_of_exists_of_isFiltered_of_fullyFaithful
  statement: [IsFilteredOrEmpty D] [F.Full]
  proof: by
  have := IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h
  refine Functor.final_of_exists_of_isFiltered F h (fun {d c} s s' => ?_)
  obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.coeq s s')
  refine ⟨c₀, F.preimage (IsFiltered.coeqHom s s' ≫ f), ?_⟩
  simp [reassoc_of% (IsFiltered.coeq_condit

中文:
定理 Functor.final_of_exists_of_isFiltered_of_fullyFaithful
  结论: [IsFilteredOrEmpty D] [F.Full]
  证明: by
  have := IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h
  refine Functor.final_of_exists_of_isFiltered F h (fun {d c} s s' => ?_)
  obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.coeq s s')
  refine ⟨c₀, F.preimage (IsFiltered.coeqHom s s' ≫ f), ?_⟩
  simp [reassoc_of% (IsFiltered.coeq_condit

Depends on / 依赖: F.preimage, Functor, Functor.final_of_exists_of_isFiltered, IsFiltered, IsFiltered.coeq, IsFiltered.coeqHom, IsFiltered.coeq_condition, IsFilteredOrEmpty, IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful, coeqHom, coeq_condition, final_of_exists_of_isFiltered, of_exists_of_isFiltered_of_fullyFaithful, preimage, reassoc_of
-/
theorem Functor.final_of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : forall d, exists c, Nonempty (d ⟶ F.obj c)) : Final F := by
  have := IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h
  refine Functor.final_of_exists_of_isFiltered F h (fun {d c} s s' => ?_)
  obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.coeq s s')
  refine ⟨c₀, F.preimage (IsFiltered.coeqHom s s' ≫ f), ?_⟩
  simp [reassoc_of% (IsFiltered.coeq_condition s s')]

/--
theorem `Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful` / 定理 `Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful`

English:
theorem Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  statement: [IsCofilteredOrEmpty D] [F.Full]
  proof: by
  suffices Final F.op from initial_of_final_op _
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

中文:
定理 Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  结论: [IsCofilteredOrEmpty D] [F.Full]
  证明: by
  suffices Final F.op from initial_of_final_op _
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

Depends on / 依赖: F.op, Functor, Functor.final_of_exists_of_isFiltered_of_fullyFaithful, d.unop, f.op, final_of_exists_of_isFiltered_of_fullyFaithful, initial_of_final_op
-/
theorem Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D] [F.Full]
    [Faithful F] (h : forall d, exists c, Nonempty (F.obj c ⟶ d)) : Initial F := by
  suffices Final F.op from initial_of_final_op _
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

/--
Instance `IsFiltered.under` / 实例 `IsFiltered.under`

English:
instance IsFiltered.under
  signature: [IsFilteredOrEmpty C] (c : C)
  body: isFiltered_structuredArrow_of_isFiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsFilteredOrEmpty.cocone_maps s s')

中文:
实例 IsFiltered.under
  签名: [IsFilteredOrEmpty C] (c : C)
  定义体: isFiltered_structuredArrow_of_isFiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsFilteredOrEmpty.cocone_maps s s')

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_maps, cocone_maps, isFiltered_structuredArrow_of_isFiltered_of_exists
-/
instance IsFiltered.under [IsFilteredOrEmpty C] (c : C) : IsFiltered (Under c) :=
  isFiltered_structuredArrow_of_isFiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsFilteredOrEmpty.cocone_maps s s')

/--
Instance `IsCofiltered.over` / 实例 `IsCofiltered.over`

English:
instance IsCofiltered.over
  signature: [IsCofilteredOrEmpty C] (c : C)
  body: isCofiltered_costructuredArrow_of_isCofiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsCofilteredOrEmpty.cone_maps s s')

中文:
实例 IsCofiltered.over
  签名: [IsCofilteredOrEmpty C] (c : C)
  定义体: isCofiltered_costructuredArrow_of_isCofiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsCofilteredOrEmpty.cone_maps s s')

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_maps, cone_maps, isCofiltered_costructuredArrow_of_isCofiltered_of_exists
-/
instance IsCofiltered.over [IsCofilteredOrEmpty C] (c : C) : IsCofiltered (Over c) :=
  isCofiltered_costructuredArrow_of_isCofiltered_of_exists _ c ⟨c, ⟨𝟙 _⟩⟩
    (fun s s' => IsCofilteredOrEmpty.cone_maps s s')

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `Under.final_forget` / 实例 `Under.final_forget`

English:
instance Under.final_forget
  signature: [IsFilteredOrEmpty C] (c : C)
  body: final_of_exists_of_isFiltered _
    (fun c' => ⟨mk (IsFiltered.leftToMax c c'), ⟨IsFiltered.rightToMax c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (x.hom ≫ IsFiltered.coeqHom s s')
      use homMk (IsFiltered.coeqHom s s') (by simp)
      simp only [forget_obj, mk_right, forget_map, homMk_right

中文:
实例 Under.final_forget
  签名: [IsFilteredOrEmpty C] (c : C)
  定义体: final_of_exists_of_isFiltered _
    (fun c' => ⟨mk (IsFiltered.leftToMax c c'), ⟨IsFiltered.rightToMax c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (x.hom ≫ IsFiltered.coeqHom s s')
      use homMk (IsFiltered.coeqHom s s') (by simp)
      simp only [forget_obj, mk_right, forget_map, homMk_right

Depends on / 依赖: IsFiltered, IsFiltered.coeqHom, IsFiltered.coeq_condition, IsFiltered.leftToMax, IsFiltered.rightToMax, coeqHom, coeq_condition, final_of_exists_of_isFiltered, forget_map, forget_obj, homMk_right, leftToMax, mk_right, rightToMax, x.hom
-/
instance Under.final_forget [IsFilteredOrEmpty C] (c : C) : Final (Under.forget c) :=
  final_of_exists_of_isFiltered _
    (fun c' => ⟨mk (IsFiltered.leftToMax c c'), ⟨IsFiltered.rightToMax c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (x.hom ≫ IsFiltered.coeqHom s s')
      use homMk (IsFiltered.coeqHom s s') (by simp)
      simp only [forget_obj, mk_right, forget_map, homMk_right]
      rw [IsFiltered.coeq_condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `Over.initial_forget` / 实例 `Over.initial_forget`

English:
instance Over.initial_forget
  signature: [IsCofilteredOrEmpty C] (c : C)
  body: initial_of_exists_of_isCofiltered _
    (fun c' => ⟨mk (IsCofiltered.minToLeft c c'), ⟨IsCofiltered.minToRight c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (IsCofiltered.eqHom s s' ≫ x.hom)
      use homMk (IsCofiltered.eqHom s s') (by simp)
      simp only [forget_obj, mk_left, forget_map, homM

中文:
实例 Over.initial_forget
  签名: [IsCofilteredOrEmpty C] (c : C)
  定义体: initial_of_exists_of_isCofiltered _
    (fun c' => ⟨mk (IsCofiltered.minToLeft c c'), ⟨IsCofiltered.minToRight c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (IsCofiltered.eqHom s s' ≫ x.hom)
      use homMk (IsCofiltered.eqHom s s') (by simp)
      simp only [forget_obj, mk_left, forget_map, homM

Depends on / 依赖: IsCofiltered, IsCofiltered.eqHom, IsCofiltered.eq_condition, IsCofiltered.minToLeft, IsCofiltered.minToRight, eq_condition, forget_map, forget_obj, homMk_left, initial_of_exists_of_isCofiltered, minToLeft, minToRight, mk_left, x.hom
-/
instance Over.initial_forget [IsCofilteredOrEmpty C] (c : C) : Initial (Over.forget c) :=
  initial_of_exists_of_isCofiltered _
    (fun c' => ⟨mk (IsCofiltered.minToLeft c c'), ⟨IsCofiltered.minToRight c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (IsCofiltered.eqHom s s' ≫ x.hom)
      use homMk (IsCofiltered.eqHom s s') (by simp)
      simp only [forget_obj, mk_left, forget_map, homMk_left]
      rw [IsCofiltered.eq_condition])

section LocallySmall

variable {C : Type v₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `Functor.Final.exists_coeq_of_locally_small` / 定理 `Functor.Final.exists_coeq_of_locally_small`

English:
theorem Functor.Final.exists_coeq_of_locally_small
  statement: [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
  proof: by
  have : colimit.ι (F ⋙ coyoneda.obj (op d)) c s = colimit.ι (F ⋙ coyoneda.obj (op d)) c s' := by
    apply (Final.colimitCompCoyonedaIso F d).toEquiv.injective
    subsingleton
  obtain ⟨c', t₁, t₂, h⟩ := (Types.FilteredColimit.colimit_eq_iff.{v₁, v₁, v₁} _).mp this
  refine ⟨IsFiltered.coeq t₁ 

中文:
定理 Functor.Final.exists_coeq_of_locally_small
  结论: [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
  证明: by
  have : colimit.ι (F ⋙ coyoneda.obj (op d)) c s = colimit.ι (F ⋙ coyoneda.obj (op d)) c s' := by
    apply (Final.colimitCompCoyonedaIso F d).toEquiv.injective
    subsingleton
  obtain ⟨c', t₁, t₂, h⟩ := (Types.FilteredColimit.colimit_eq_iff.{v₁, v₁, v₁} _).mp this
  refine ⟨IsFiltered.coeq t₁ 

Depends on / 依赖: FilteredColimit, Final.colimitCompCoyonedaIso, IsFiltered, IsFiltered.coeq, IsFiltered.coeqHom, IsFiltered.coeq_condition, Types.FilteredColimit.colimit_eq_iff, coeqHom, coeq_condition, colimit, colimitCompCoyonedaIso, colimit_eq_iff, conv_rhs, coyoneda, coyoneda.obj, injective, reassoc_of, subsingleton, toEquiv, toEquiv.injective
-/
theorem Functor.Final.exists_coeq_of_locally_small [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
    (s s' : d ⟶ F.obj c) : exists (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t := by
  have : colimit.ι (F ⋙ coyoneda.obj (op d)) c s = colimit.ι (F ⋙ coyoneda.obj (op d)) c s' := by
    apply (Final.colimitCompCoyonedaIso F d).toEquiv.injective
    subsingleton
  obtain ⟨c', t₁, t₂, h⟩ := (Types.FilteredColimit.colimit_eq_iff.{v₁, v₁, v₁} _).mp this
  refine ⟨IsFiltered.coeq t₁ t₂, t₁ ≫ IsFiltered.coeqHom t₁ t₂, ?_⟩
  conv_rhs => rw [IsFiltered.coeq_condition t₁ t₂]
  dsimp at h
  simp [reassoc_of% h]

end LocallySmall

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `Functor.final_iff_of_isFiltered` / 定理 `Functor.final_iff_of_isFiltered`

English:
theorem Functor.final_iff_of_isFiltered
  given: [IsFilteredOrEmpty C]
  proof: by
  refine ⟨fun hF => ⟨?_, ?_⟩, fun h => final_of_exists_of_isFiltered F h.1 h.2⟩
  · intro d
    obtain ⟨f⟩ : Nonempty (StructuredArrow d F) := IsConnected.is_nonempty
    exact ⟨_, ⟨f.hom⟩⟩
  · let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.equiv
    let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂} D 

中文:
定理 Functor.final_iff_of_isFiltered
  条件: [IsFilteredOrEmpty C]
  证明: by
  refine ⟨fun hF => ⟨?_, ?_⟩, fun h => final_of_exists_of_isFiltered F h.1 h.2⟩
  · intro d
    obtain ⟨f⟩ : Nonempty (StructuredArrow d F) := IsConnected.is_nonempty
    exact ⟨_, ⟨f.hom⟩⟩
  · let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.equiv
    let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂} D 

Depends on / 依赖: AsSmall, AsSmall.equiv, AsSmall.up.ma, Functor, Functor.Final.exists_coeq_of_locally_small, IsConnected, IsConnected.is_nonempty, IsFilteredOrEmpty, Nonempty, StructuredArrow, exists_coeq_of_locally_small, f.hom, final_of_exists_of_isFiltered, functor, inverse, is_nonempty, of_equivalence
-/
theorem Functor.final_iff_of_isFiltered [IsFilteredOrEmpty C] :
    Final F ↔ (forall d, exists c, Nonempty (d ⟶ F.obj c)) ∧ (forall {d : D} {c : C} (s s' : d ⟶ F.obj c),
      exists (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) := by
  refine ⟨fun hF => ⟨?_, ?_⟩, fun h => final_of_exists_of_isFiltered F h.1 h.2⟩
  · intro d
    obtain ⟨f⟩ : Nonempty (StructuredArrow d F) := IsConnected.is_nonempty
    exact ⟨_, ⟨f.hom⟩⟩
  · let s₁ : C ≌ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.equiv
    let s₂ : D ≌ AsSmall.{max u₁ v₁ u₂ v₂} D := AsSmall.equiv
    have : IsFilteredOrEmpty (AsSmall.{max u₁ v₁ u₂ v₂} C) := .of_equivalence s₁
    intro d c s s'
    obtain ⟨c', t, ht⟩ := Functor.Final.exists_coeq_of_locally_small (s₁.inverse ⋙ F ⋙ s₂.functor)
      (AsSmall.up.map s) (AsSmall.up.map s')
    exact ⟨AsSmall.down.obj c', AsSmall.down.map t, s₂.functor.map_injective (by simp_all [s₁, s₂])⟩

/--
theorem `Functor.initial_iff_of_isCofiltered` / 定理 `Functor.initial_iff_of_isCofiltered`

English:
theorem Functor.initial_iff_of_isCofiltered
  given: [IsCofilteredOrEmpty C]
  proof: by
  refine ⟨fun hF => ?_, fun h => initial_of_exists_of_isCofiltered F h.1 h.2⟩
  obtain ⟨h₁, h₂⟩ := F.op.final_iff_of_isFiltered.mp inferInstance
  refine ⟨?_, ?_⟩
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ (op d)
    exact ⟨c.unop, ⟨t.unop⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ (Quiver.Hom.

中文:
定理 Functor.initial_iff_of_isCofiltered
  条件: [IsCofilteredOrEmpty C]
  证明: by
  refine ⟨fun hF => ?_, fun h => initial_of_exists_of_isCofiltered F h.1 h.2⟩
  obtain ⟨h₁, h₂⟩ := F.op.final_iff_of_isFiltered.mp inferInstance
  refine ⟨?_, ?_⟩
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ (op d)
    exact ⟨c.unop, ⟨t.unop⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ (Quiver.Hom.

Depends on / 依赖: F.op.final_iff_of_isFiltered.mp, Quiver, Quiver.Hom.op, Quiver.Hom.op_inj, c.unop, final_iff_of_isFiltered, initial_of_exists_of_isCofiltered, op_inj, t.unop
-/
theorem Functor.initial_iff_of_isCofiltered [IsCofilteredOrEmpty C] :
    Initial F ↔ (forall d, exists c, Nonempty (F.obj c ⟶ d)) ∧ (forall {d : D} {c : C} (s s' : F.obj c ⟶ d),
      exists (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') := by
  refine ⟨fun hF => ?_, fun h => initial_of_exists_of_isCofiltered F h.1 h.2⟩
  obtain ⟨h₁, h₂⟩ := F.op.final_iff_of_isFiltered.mp inferInstance
  refine ⟨?_, ?_⟩
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ (op d)
    exact ⟨c.unop, ⟨t.unop⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ (Quiver.Hom.op s) (Quiver.Hom.op s')
    exact ⟨c'.unop, t.unop, Quiver.Hom.op_inj ht⟩

/--
theorem `Functor.Final.exists_coeq` / 定理 `Functor.Final.exists_coeq`

English:
theorem Functor.Final.exists_coeq
  statement: [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
  proof: ((final_iff_of_isFiltered F).1 inferInstance).2 s s'

中文:
定理 Functor.Final.exists_coeq
  结论: [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
  证明: ((final_iff_of_isFiltered F).1 inferInstance).2 s s'

Depends on / 依赖: final_iff_of_isFiltered
-/
theorem Functor.Final.exists_coeq [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
    (s s' : d ⟶ F.obj c) : exists (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t :=
  ((final_iff_of_isFiltered F).1 inferInstance).2 s s'

/--
theorem `Functor.Initial.exists_eq` / 定理 `Functor.Initial.exists_eq`

English:
theorem Functor.Initial.exists_eq
  statement: [IsCofilteredOrEmpty C] [Initial F] {d : D} {c : C}
  proof: ((initial_iff_of_isCofiltered F).1 inferInstance).2 s s'

中文:
定理 Functor.Initial.exists_eq
  结论: [IsCofilteredOrEmpty C] [Initial F] {d : D} {c : C}
  证明: ((initial_iff_of_isCofiltered F).1 inferInstance).2 s s'

Depends on / 依赖: initial_iff_of_isCofiltered
-/
theorem Functor.Initial.exists_eq [IsCofilteredOrEmpty C] [Initial F] {d : D} {c : C}
    (s s' : F.obj c ⟶ d) : exists (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s' :=
  ((initial_iff_of_isCofiltered F).1 inferInstance).2 s s'

/--
theorem `Functor.final_iff_isFiltered_structuredArrow` / 定理 `Functor.final_iff_isFiltered_structuredArrow`

English:
theorem Functor.final_iff_isFiltered_structuredArrow
  given: [IsFilteredOrEmpty C]
  proof: by
  refine ⟨?_, fun h => final_of_isFiltered_structuredArrow F⟩
  rw [final_iff_of_isFiltered]
  exact fun h d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h.1 d) h.2

中文:
定理 Functor.final_iff_isFiltered_structuredArrow
  条件: [IsFilteredOrEmpty C]
  证明: by
  refine ⟨?_, fun h => final_of_isFiltered_structuredArrow F⟩
  rw [final_iff_of_isFiltered]
  exact fun h d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h.1 d) h.2

Depends on / 依赖: final_iff_of_isFiltered, final_of_isFiltered_structuredArrow, isFiltered_structuredArrow_of_isFiltered_of_exists
-/
theorem Functor.final_iff_isFiltered_structuredArrow [IsFilteredOrEmpty C] :
    Final F ↔ forall d, IsFiltered (StructuredArrow d F) := by
  refine ⟨?_, fun h => final_of_isFiltered_structuredArrow F⟩
  rw [final_iff_of_isFiltered]
  exact fun h d => isFiltered_structuredArrow_of_isFiltered_of_exists F d (h.1 d) h.2

/--
theorem `Functor.initial_iff_isCofiltered_costructuredArrow` / 定理 `Functor.initial_iff_isCofiltered_costructuredArrow`

English:
theorem Functor.initial_iff_isCofiltered_costructuredArrow
  given: [IsCofilteredOrEmpty C]
  proof: by
  refine ⟨?_, fun h => initial_of_isCofiltered_costructuredArrow F⟩
  rw [initial_iff_of_isCofiltered]
  exact fun h d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h.1 d) h.2

中文:
定理 Functor.initial_iff_isCofiltered_costructuredArrow
  条件: [IsCofilteredOrEmpty C]
  证明: by
  refine ⟨?_, fun h => initial_of_isCofiltered_costructuredArrow F⟩
  rw [initial_iff_of_isCofiltered]
  exact fun h d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h.1 d) h.2

Depends on / 依赖: initial_iff_of_isCofiltered, initial_of_isCofiltered_costructuredArrow, isCofiltered_costructuredArrow_of_isCofiltered_of_exists
-/
theorem Functor.initial_iff_isCofiltered_costructuredArrow [IsCofilteredOrEmpty C] :
    Initial F ↔ forall d, IsCofiltered (CostructuredArrow F d) := by
  refine ⟨?_, fun h => initial_of_isCofiltered_costructuredArrow F⟩
  rw [initial_iff_of_isCofiltered]
  exact fun h d => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F d (h.1 d) h.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFilteredOrEmpty
  signature: C] (X
  body: by
  have : forall Y, IsFiltered (StructuredArrow Y (Under.forget X.1)) := by
    rw [← final_iff_isFiltered_structuredArrow (Under.forget X.1)]
    infer_instance
  apply IsFiltered.of_equivalence (StructuredArrow.ofDiagEquivalence X).symm

中文:
实例 [IsFilteredOrEmpty
  签名: C] (X
  定义体: by
  have : forall Y, IsFiltered (StructuredArrow Y (Under.forget X.1)) := by
    rw [← final_iff_isFiltered_structuredArrow (Under.forget X.1)]
    infer_instance
  apply IsFiltered.of_equivalence (StructuredArrow.ofDiagEquivalence X).symm

Depends on / 依赖: IsFiltered, IsFiltered.of_equivalence, StructuredArrow, StructuredArrow.ofDiagEquivalence, Under.forget, final_iff_isFiltered_structuredArrow, forget, infer_instance, ofDiagEquivalence, of_equivalence
-/
instance [IsFilteredOrEmpty C] (X : C × C) : IsFiltered (StructuredArrow X (diag C)) := by
  have : forall Y, IsFiltered (StructuredArrow Y (Under.forget X.1)) := by
    rw [← final_iff_isFiltered_structuredArrow (Under.forget X.1)]
    infer_instance
  apply IsFiltered.of_equivalence (StructuredArrow.ofDiagEquivalence X).symm

/--
Instance `Functor.final_diag_of_isFiltered` / 实例 `Functor.final_diag_of_isFiltered`

English:
instance Functor.final_diag_of_isFiltered
  signature: [IsFilteredOrEmpty C]
  body: final_of_isFiltered_structuredArrow _

中文:
实例 Functor.final_diag_of_isFiltered
  签名: [IsFilteredOrEmpty C]
  定义体: final_of_isFiltered_structuredArrow _

Depends on / 依赖: final_of_isFiltered_structuredArrow
-/
instance Functor.final_diag_of_isFiltered [IsFilteredOrEmpty C] : Final (Functor.diag C) :=
  final_of_isFiltered_structuredArrow _

-- Adding this instance causes performance problems elsewhere, even with low priority
/--
theorem `IsFilteredOrEmpty.isSiftedOrEmpty` / 定理 `IsFilteredOrEmpty.isSiftedOrEmpty`

English:
theorem IsFilteredOrEmpty.isSiftedOrEmpty
  given: [IsFilteredOrEmpty C]
  statement: IsSiftedOrEmpty C
  proof: Functor.final_diag_of_isFiltered

中文:
定理 IsFilteredOrEmpty.isSiftedOrEmpty
  条件: [IsFilteredOrEmpty C]
  结论: IsSiftedOrEmpty C
  证明: Functor.final_diag_of_isFiltered

Depends on / 依赖: Functor, Functor.final_diag_of_isFiltered, final_diag_of_isFiltered
-/
theorem IsFilteredOrEmpty.isSiftedOrEmpty [IsFilteredOrEmpty C] : IsSiftedOrEmpty C :=
  Functor.final_diag_of_isFiltered

-- Adding this instance causes performance problems elsewhere, even with low priority
attribute [local instance] IsFiltered.nonempty in
/--
theorem `IsFiltered.isSifted` / 定理 `IsFiltered.isSifted`

English:
theorem IsFiltered.isSifted
  given: [IsFiltered C]
  statement: IsSifted C where

中文:
定理 IsFiltered.isSifted
  条件: [IsFiltered C]
  结论: IsSifted C where
-/
theorem IsFiltered.isSifted [IsFiltered C] : IsSifted C where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofilteredOrEmpty
  signature: C] (X
  body: by
  have : forall Y, IsCofiltered (CostructuredArrow (Over.forget X.1) Y) := by
    rw [← initial_iff_isCofiltered_costructuredArrow (Over.forget X.1)]
    infer_instance
  apply IsCofiltered.of_equivalence (CostructuredArrow.ofDiagEquivalence X).symm

中文:
实例 [IsCofilteredOrEmpty
  签名: C] (X
  定义体: by
  have : forall Y, IsCofiltered (CostructuredArrow (Over.forget X.1) Y) := by
    rw [← initial_iff_isCofiltered_costructuredArrow (Over.forget X.1)]
    infer_instance
  apply IsCofiltered.of_equivalence (CostructuredArrow.ofDiagEquivalence X).symm

Depends on / 依赖: CostructuredArrow, CostructuredArrow.ofDiagEquivalence, IsCofiltered, IsCofiltered.of_equivalence, Over.forget, forget, infer_instance, initial_iff_isCofiltered_costructuredArrow, ofDiagEquivalence, of_equivalence
-/
instance [IsCofilteredOrEmpty C] (X : C × C) : IsCofiltered (CostructuredArrow (diag C) X) := by
  have : forall Y, IsCofiltered (CostructuredArrow (Over.forget X.1) Y) := by
    rw [← initial_iff_isCofiltered_costructuredArrow (Over.forget X.1)]
    infer_instance
  apply IsCofiltered.of_equivalence (CostructuredArrow.ofDiagEquivalence X).symm

/--
Instance `Functor.initial_diag_of_isFiltered` / 实例 `Functor.initial_diag_of_isFiltered`

English:
instance Functor.initial_diag_of_isFiltered
  signature: [IsCofilteredOrEmpty C]
  body: initial_of_isCofiltered_costructuredArrow _

中文:
实例 Functor.initial_diag_of_isFiltered
  签名: [IsCofilteredOrEmpty C]
  定义体: initial_of_isCofiltered_costructuredArrow _

Depends on / 依赖: initial_of_isCofiltered_costructuredArrow
-/
instance Functor.initial_diag_of_isFiltered [IsCofilteredOrEmpty C] : Initial (Functor.diag C) :=
  initial_of_isCofiltered_costructuredArrow _

/--
theorem `Functor.final_of_isFiltered_of_pUnit` / 定理 `Functor.final_of_isFiltered_of_pUnit`

English:
theorem Functor.final_of_isFiltered_of_pUnit
  given: [IsFiltered C] (F : C ⥤ Discrete PUnit)
  proof: by
  refine final_of_exists_of_isFiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsFiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

中文:
定理 Functor.final_of_isFiltered_of_pUnit
  条件: [IsFiltered C] (F : C ⥤ Discrete PUnit)
  证明: by
  refine final_of_exists_of_isFiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsFiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

Depends on / 依赖: Classical, Classical.choice, Discrete, Discrete.eqToHom, IsFiltered, IsFiltered.nonempty, Subsingleton, Subsingleton.elim, choice, eqToHom, final_of_exists_of_isFiltered, nonempty
-/
theorem Functor.final_of_isFiltered_of_pUnit [IsFiltered C] (F : C ⥤ Discrete PUnit) :
    Final F := by
  refine final_of_exists_of_isFiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsFiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

/--
theorem `Functor.initial_of_isCofiltered_pUnit` / 定理 `Functor.initial_of_isCofiltered_pUnit`

English:
theorem Functor.initial_of_isCofiltered_pUnit
  given: [IsCofiltered C] (F : C ⥤ Discrete PUnit)
  proof: by
  refine initial_of_exists_of_isCofiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsCofiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

中文:
定理 Functor.initial_of_isCofiltered_pUnit
  条件: [IsCofiltered C] (F : C ⥤ Discrete PUnit)
  证明: by
  refine initial_of_exists_of_isCofiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsCofiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

Depends on / 依赖: Classical, Classical.choice, Discrete, Discrete.eqToHom, IsCofiltered, IsCofiltered.nonempty, Subsingleton, Subsingleton.elim, choice, eqToHom, initial_of_exists_of_isCofiltered, nonempty
-/
theorem Functor.initial_of_isCofiltered_pUnit [IsCofiltered C] (F : C ⥤ Discrete PUnit) :
    Initial F := by
  refine initial_of_exists_of_isCofiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsCofiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

/--
Instance `StructuredArrow.final_proj_of_isFiltered` / 实例 `StructuredArrow.final_proj_of_isFiltered`

English:
instance StructuredArrow.final_proj_of_isFiltered
  signature: [IsFilteredOrEmpty C]
  body: by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofStructuredArrowProjEquivalence T Y X)]
  exact (final_comp (Under.forget X) T).out _

中文:
实例 StructuredArrow.final_proj_of_isFiltered
  签名: [IsFilteredOrEmpty C]
  定义体: by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofStructuredArrowProjEquivalence T Y X)]
  exact (final_comp (Under.forget X) T).out _

Depends on / 依赖: Under.forget, final_comp, forget, isConnected_iff_of_equivalence, ofStructuredArrowProjEquivalence
-/
instance StructuredArrow.final_proj_of_isFiltered [IsFilteredOrEmpty C]
    (T : C ⥤ D) [Final T] (Y : D) : Final (StructuredArrow.proj Y T) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofStructuredArrowProjEquivalence T Y X)]
  exact (final_comp (Under.forget X) T).out _

/--
Instance `CostructuredArrow.initial_proj_of_isCofiltered` / 实例 `CostructuredArrow.initial_proj_of_isCofiltered`

English:
instance CostructuredArrow.initial_proj_of_isCofiltered
  signature: [IsCofilteredOrEmpty C]
  body: by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofCostructuredArrowProjEquivalence T Y X)]
  exact (initial_comp (Over.forget X) T).out _

中文:
实例 CostructuredArrow.initial_proj_of_isCofiltered
  签名: [IsCofilteredOrEmpty C]
  定义体: by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofCostructuredArrowProjEquivalence T Y X)]
  exact (initial_comp (Over.forget X) T).out _

Depends on / 依赖: Over.forget, forget, initial_comp, isConnected_iff_of_equivalence, ofCostructuredArrowProjEquivalence
-/
instance CostructuredArrow.initial_proj_of_isCofiltered [IsCofilteredOrEmpty C]
    (T : C ⥤ D) [Initial T] (Y : D) : Initial (CostructuredArrow.proj T Y) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofCostructuredArrowProjEquivalence T Y X)]
  exact (initial_comp (Over.forget X) T).out _

/--
Instance `StructuredArrow.final_map₂_id` / 实例 `StructuredArrow.final_map₂_id`

English:
instance StructuredArrow.final_map₂_id
  signature: [IsFiltered C] {E : Type u₃} [Category.{v₃} E]
  body: by
  have : IsFiltered (StructuredArrow e (T ⋙ S)) :=
    (T ⋙ S).final_iff_isFiltered_structuredArrow.mp inferInstance e
  apply final_of_natIso (map₂IsoPreEquivalenceInverseCompProj d e u α).symm

中文:
实例 StructuredArrow.final_map₂_id
  签名: [IsFiltered C] {E : 类型u₃} [Category.{v₃} E]
  定义体: by
  have : IsFiltered (StructuredArrow e (T ⋙ S)) :=
    (T ⋙ S).final_iff_isFiltered_structuredArrow.mp inferInstance e
  apply final_of_natIso (map₂IsoPreEquivalenceInverseCompProj d e u α).symm

Depends on / 依赖: IsFiltered, StructuredArrow, final_iff_isFiltered_structuredArrow, final_iff_isFiltered_structuredArrow.mp, final_of_natIso
-/
instance StructuredArrow.final_map₂_id [IsFiltered C] {E : Type u₃} [Category.{v₃} E]
    {T : C ⥤ D} [T.Final] {S : D ⥤ E} [S.Final] {T' : C ⥤ E}
    {d : D} {e : E} (u : e ⟶ S.obj d) (α : T ⋙ S ⟶ T') [IsIso α] :
    Final (map₂ (F := 𝟭 _) u α) := by
  have : IsFiltered (StructuredArrow e (T ⋙ S)) :=
    (T ⋙ S).final_iff_isFiltered_structuredArrow.mp inferInstance e
  apply final_of_natIso (map₂IsoPreEquivalenceInverseCompProj d e u α).symm

/--
Instance `StructuredArrow.final_map` / 实例 `StructuredArrow.final_map`

English:
instance StructuredArrow.final_map
  signature: [IsFiltered C] {S S' : D} (f : S ⟶ S') (T : C ⥤ D) [T.Final]
  body: by
  have := NatIso.isIso_of_isIso_app (𝟙 T)
  have : (map₂ (F := 𝟭 C) (G := 𝟭 D) f (𝟙 T)).Final := by
    apply StructuredArrow.final_map₂_id (S := 𝟭 D) (T := T) (T' := T) f (𝟙 T)
  apply final_of_natIso (mapIsoMap₂ f).symm

中文:
实例 StructuredArrow.final_map
  签名: [IsFiltered C] {S S' : D} (f : S ⟶ S') (T : C ⥤ D) [T.Final]
  定义体: by
  have := NatIso.isIso_of_isIso_app (𝟙 T)
  have : (map₂ (F := 𝟭 C) (G := 𝟭 D) f (𝟙 T)).Final := by
    apply StructuredArrow.final_map₂_id (S := 𝟭 D) (T := T) (T' := T) f (𝟙 T)
  apply final_of_natIso (mapIsoMap₂ f).symm

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, StructuredArrow, StructuredArrow.final_map, final_of_natIso, isIso_of_isIso_app
-/
instance StructuredArrow.final_map [IsFiltered C] {S S' : D} (f : S ⟶ S') (T : C ⥤ D) [T.Final] :
    Final (map (T := T) f) := by
  have := NatIso.isIso_of_isIso_app (𝟙 T)
  have : (map₂ (F := 𝟭 C) (G := 𝟭 D) f (𝟙 T)).Final := by
    apply StructuredArrow.final_map₂_id (S := 𝟭 D) (T := T) (T' := T) f (𝟙 T)
  apply final_of_natIso (mapIsoMap₂ f).symm

/--
Instance `StructuredArrow.final_post` / 实例 `StructuredArrow.final_post`

English:
instance StructuredArrow.final_post
  signature: [IsFiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
  body: by
  apply final_of_natIso (postIsoMap₂ X T S).symm

中文:
实例 StructuredArrow.final_post
  签名: [IsFiltered C] {E : 类型u₃} [Category.{v₃} E] (X : D)
  定义体: by
  apply final_of_natIso (postIsoMap₂ X T S).symm

Depends on / 依赖: final_of_natIso
-/
instance StructuredArrow.final_post [IsFiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
    (T : C ⥤ D) [T.Final] (S : D ⥤ E) [S.Final] : Final (post X T S) := by
  apply final_of_natIso (postIsoMap₂ X T S).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `CostructuredArrow.initial_map₂_id` / 实例 `CostructuredArrow.initial_map₂_id`

English:
instance CostructuredArrow.initial_map₂_id
  signature: [IsCofiltered C] {E : Type u₃} [Category.{v₃} E]
  body: by
  have := (T ⋙ S).initial_iff_isCofiltered_costructuredArrow.mp inferInstance e
  apply initial_of_natIso (map₂IsoPreEquivalenceInverseCompProj T S d e u).symm

中文:
实例 CostructuredArrow.initial_map₂_id
  签名: [IsCofiltered C] {E : 类型u₃} [Category.{v₃} E]
  定义体: by
  have := (T ⋙ S).initial_iff_isCofiltered_costructuredArrow.mp inferInstance e
  apply initial_of_natIso (map₂IsoPreEquivalenceInverseCompProj T S d e u).symm

Depends on / 依赖: initial_iff_isCofiltered_costructuredArrow, initial_iff_isCofiltered_costructuredArrow.mp, initial_of_natIso
-/
instance CostructuredArrow.initial_map₂_id [IsCofiltered C] {E : Type u₃} [Category.{v₃} E]
    (T : C ⥤ D) [T.Initial] (S : D ⥤ E) [S.Initial] (d : D) (e : E)
    (u : S.obj d ⟶ e) : Initial (map₂ (F := 𝟭 _) (U := T ⋙ S) (𝟙 (T ⋙ S)) u) := by
  have := (T ⋙ S).initial_iff_isCofiltered_costructuredArrow.mp inferInstance e
  apply initial_of_natIso (map₂IsoPreEquivalenceInverseCompProj T S d e u).symm

/--
Instance `CostructuredArrow.initial_post` / 实例 `CostructuredArrow.initial_post`

English:
instance CostructuredArrow.initial_post
  signature: [IsCofiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
  body: by
  apply initial_of_natIso (postIsoMap₂ X T S).symm

中文:
实例 CostructuredArrow.initial_post
  签名: [IsCofiltered C] {E : 类型u₃} [Category.{v₃} E] (X : D)
  定义体: by
  apply initial_of_natIso (postIsoMap₂ X T S).symm

Depends on / 依赖: initial_of_natIso
-/
instance CostructuredArrow.initial_post [IsCofiltered C] {E : Type u₃} [Category.{v₃} E] (X : D)
    (T : C ⥤ D) [T.Initial] (S : D ⥤ E) [S.Initial] : Initial (post T S X) := by
  apply initial_of_natIso (postIsoMap₂ X T S).symm

section Pi

variable {α : Type u₁} {I : α -> Type u₂} [forall s, Category.{v₂} (I s)]

set_option backward.defeqAttrib.useBackward true in
open IsFiltered in
/--
Instance `final_eval` / 实例 `final_eval`

English:
instance final_eval
  signature: [forall s, IsFiltered (I s)] (s : α)
  body: by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (forall s, (c' : I s) × (c s ⟶ c')) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨coeq f g, coeqHom f g⟩
    re

中文:
实例 final_eval
  签名: [对任意 s, IsFiltered (I s)] (s : α)
  定义体: by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (forall s, (c' : I s) × (c s ⟶ c')) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨coeq f g, coeqHom f g⟩
    re

Depends on / 依赖: Function, Function.update, Function.update_self, Functor, Functor.final_of_exists_of_isFiltered, Pi.eval_map, Pi.eval_obj, classical, coeqHom, coeq_condition, eval_map, eval_obj, final_of_exists_of_isFiltered, nonempty, nonempty.some, update, update_self
-/
instance final_eval [forall s, IsFiltered (I s)] (s : α) : (Pi.eval I s).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (forall s, (c' : I s) × (c s ⟶ c')) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨coeq f g, coeqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_self]
    simpa using coeq_condition _ _

set_option backward.defeqAttrib.useBackward true in
open IsCofiltered in
/--
Instance `initial_eval` / 实例 `initial_eval`

English:
instance initial_eval
  signature: [forall s, IsCofiltered (I s)] (s : α)
  body: by
  classical
  apply Functor.initial_of_exists_of_isCofiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (forall s, (c' : I s) × (c' ⟶ c s)) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨eq f g, eqHom f g⟩
    re

中文:
实例 initial_eval
  签名: [对任意 s, IsCofiltered (I s)] (s : α)
  定义体: by
  classical
  apply Functor.initial_of_exists_of_isCofiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (forall s, (c' : I s) × (c' ⟶ c s)) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨eq f g, eqHom f g⟩
    re

Depends on / 依赖: Function, Function.update, Function.update_self, Functor, Functor.initial_of_exists_of_isCofiltered, Pi.eval_map, Pi.eval_obj, classical, eq_condition, eval_map, eval_obj, initial_of_exists_of_isCofiltered, nonempty, nonempty.some, update, update_self
-/
instance initial_eval [forall s, IsCofiltered (I s)] (s : α) : (Pi.eval I s).Initial := by
  classical
  apply Functor.initial_of_exists_of_isCofiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (forall s, (c' : I s) × (c' ⟶ c s)) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨eq f g, eqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_self]
    simpa using eq_condition _ _

end Pi

section Prod

namespace IsFiltered

attribute [local instance] IsFiltered.isConnected IsCofiltered.isConnected

/--
Instance `final_fst` / 实例 `final_fst`

English:
instance final_fst
  signature: [IsFiltered D]
  body: inferInstance

中文:
实例 final_fst
  签名: [IsFiltered D]
  定义体: inferInstance
-/
instance final_fst [IsFiltered D] : (Prod.fst C D).Final := inferInstance

/--
Instance `final_snd` / 实例 `final_snd`

English:
instance final_snd
  signature: [IsFiltered C]
  body: inferInstance

中文:
实例 final_snd
  签名: [IsFiltered C]
  定义体: inferInstance
-/
instance final_snd [IsFiltered C] : (Prod.snd C D).Final := inferInstance

/--
Instance `initial_fst` / 实例 `initial_fst`

English:
instance initial_fst
  signature: [IsCofiltered D]
  body: inferInstance

中文:
实例 initial_fst
  签名: [IsCofiltered D]
  定义体: inferInstance
-/
instance initial_fst [IsCofiltered D] : (Prod.fst C D).Initial := inferInstance

/--
Instance `initial_snd` / 实例 `initial_snd`

English:
instance initial_snd
  signature: [IsCofiltered C]
  body: inferInstance

中文:
实例 initial_snd
  签名: [IsCofiltered C]
  定义体: inferInstance
-/
instance initial_snd [IsCofiltered C] : (Prod.snd C D).Initial := inferInstance

end IsFiltered

end Prod

end CategoryTheory

open CategoryTheory

/--
lemma `Monotone.final_functor_iff` / 引理 `Monotone.final_functor_iff`

English:
lemma Monotone.final_functor_iff
  statement: {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂]
  proof: by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁, leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨c, 𝟙 _, rfl⟩

中文:
引理 Monotone.final_functor_iff
  结论: {J₁ J₂ : 类型} [Preorder J₁] [Preorder J₂]
  证明: by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁, leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨c, 𝟙 _, rfl⟩

Depends on / 依赖: Functor, Functor.final_iff_of_isFiltered, final_iff_of_isFiltered, homOfLE, leOfHom
-/
lemma Monotone.final_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂]
    [IsDirectedOrder J₁] {f : J₁ -> J₂} (hf : Monotone f) :
    hf.functor.Final ↔ forall (j₂ : J₂), exists (j₁ : J₁), j₂ <= f j₁ := by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁, leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨c, 𝟙 _, rfl⟩

/--
lemma `Monotone.initial_functor_iff` / 引理 `Monotone.initial_functor_iff`

English:
lemma Monotone.initial_functor_iff
  statement: {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂]
  proof: by
  rw [Functor.initial_iff_of_isCofiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁,leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨ c, 𝟙 _, rfl⟩

中文:
引理 Monotone.initial_functor_iff
  结论: {J₁ J₂ : 类型} [Preorder J₁] [Preorder J₂]
  证明: by
  rw [Functor.initial_iff_of_isCofiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁,leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨ c, 𝟙 _, rfl⟩

Depends on / 依赖: Functor, Functor.initial_iff_of_isCofiltered, homOfLE, initial_iff_of_isCofiltered, leOfHom
-/
lemma Monotone.initial_functor_iff {J₁ J₂ : Type*} [Preorder J₁] [Preorder J₂]
    [IsCodirectedOrder J₁] {f : J₁ -> J₂} (hf : Monotone f) :
    hf.functor.Initial ↔ ( forall j₁,exists j₂, f j₂ <= j₁) := by
  rw [Functor.initial_iff_of_isCofiltered]
  constructor
  · rintro ⟨h, _⟩ j₂
    obtain ⟨j₁, ⟨φ⟩⟩ := h j₂
    exact ⟨j₁,leOfHom φ⟩
  · intro h
    constructor
    · intro j₂
      obtain ⟨j₁, h₁⟩ := h j₂
      exact ⟨j₁, ⟨homOfLE h₁⟩⟩
    · intro _ c _ _
      exact ⟨ c, 𝟙 _, rfl⟩
