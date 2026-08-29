/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Ultraproducts
public import Mathlib.ModelTheory.Bundled
public import Mathlib.ModelTheory.Skolem
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# First-Order Satisfiability

This file deals with the satisfiability of first-order theories, as well as equivalence over them.

## Main Definitions

- `FirstOrder.Language.Theory.IsSatisfiable`: `T.IsSatisfiable` indicates that `T` has a nonempty
  model.
- `FirstOrder.Language.Theory.IsFinitelySatisfiable`: `T.IsFinitelySatisfiable` indicates that
  every finite subset of `T` is satisfiable.
- `FirstOrder.Language.Theory.IsComplete`: `T.IsComplete` indicates that `T` is satisfiable and
  models each sentence or its negation.
- `Cardinal.Categorical`: A theory is `κ`-categorical if all models of size `κ` are isomorphic.

## Main Results

- The Compactness Theorem, `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`,
  shows that a theory is satisfiable iff it is finitely satisfiable.
- `FirstOrder.Language.completeTheory.isComplete`: The complete theory of a structure is
  complete.
- `FirstOrder.Language.Theory.exists_large_model_of_infinite_model` shows that any theory with an
  infinite model has arbitrarily large models.
- `FirstOrder.Language.Theory.exists_elementaryEmbedding_card_eq`: The Upward Löwenheim–Skolem
  Theorem: If `κ` is a cardinal greater than the cardinalities of `L` and an infinite `L`-structure
  `M`, then `M` has an elementary extension of cardinality `κ`.

## Implementation Details

- Satisfiability of an `L.Theory` `T` is defined in the minimal universe containing all the symbols
  of `L`. By Löwenheim-Skolem, this is equivalent to satisfiability in any universe.
-/

@[expose] public section



universe u v w w'

open Cardinal CategoryTheory

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : Nat}

namespace Theory

variable (T)

/--
Definition of `IsSatisfiable` / `IsSatisfiable` 的定义

English:
definition IsSatisfiable
  signature: : Prop
  body: Nonempty (ModelType.{u, v, max u v} T)

中文:
定义 IsSatisfiable
  签名: : 命题
  定义体: Nonempty (ModelType.{u, v, max u v} T)

Depends on / 依赖: ModelType, Nonempty
-/
def IsSatisfiable : Prop :=
  Nonempty (ModelType.{u, v, max u v} T)

/--
Definition of `IsFinitelySatisfiable` / `IsFinitelySatisfiable` 的定义

English:
definition IsFinitelySatisfiable
  signature: : Prop
  body: forall T0 : Finset L.Sentence, (T0 : L.Theory) subseteq T -> IsSatisfiable (T0 : L.Theory)

中文:
定义 IsFinitelySatisfiable
  签名: : 命题
  定义体: forall T0 : Finset L.Sentence, (T0 : L.Theory) subseteq T -> IsSatisfiable (T0 : L.Theory)

Depends on / 依赖: Finset, IsSatisfiable, L.Sentence, L.Theory, Sentence, Theory, subseteq
-/
def IsFinitelySatisfiable : Prop :=
  forall T0 : Finset L.Sentence, (T0 : L.Theory) subseteq T -> IsSatisfiable (T0 : L.Theory)

variable {T} {T' : L.Theory}

/--
theorem `Model.isSatisfiable` / 定理 `Model.isSatisfiable`

English:
theorem Model.isSatisfiable
  given: (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T]
  proof: ⟨((⊥ : Substructure _ (ModelType.of T M)).elementarySkolem₁Reduct.toModel T).shrink⟩

中文:
定理 Model.isSatisfiable
  条件: (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T]
  证明: ⟨((⊥ : Substructure _ (ModelType.of T M)).elementarySkolem₁Reduct.toModel T).shrink⟩

Depends on / 依赖: ModelType, ModelType.of, Reduct.toModel, Substructure, shrink, toModel
-/
theorem Model.isSatisfiable (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] :
    T.IsSatisfiable :=
  ⟨((⊥ : Substructure _ (ModelType.of T M)).elementarySkolem₁Reduct.toModel T).shrink⟩

/--
theorem `IsSatisfiable.mono` / 定理 `IsSatisfiable.mono`

English:
theorem IsSatisfiable.mono
  given: (h : T'.IsSatisfiable) (hs : T subseteq T')
  statement: T.IsSatisfiable
  proof: ⟨(Theory.Model.mono (ModelType.is_model h.some) hs).bundled⟩

中文:
定理 IsSatisfiable.mono
  条件: (h : T'.IsSatisfiable) (hs : T subseteq T')
  结论: T.IsSatisfiable
  证明: ⟨(Theory.Model.mono (ModelType.is_model h.some) hs).bundled⟩

Depends on / 依赖: ModelType, ModelType.is_model, Theory, Theory.Model.mono, bundled, h.some, is_model
-/
theorem IsSatisfiable.mono (h : T'.IsSatisfiable) (hs : T subseteq T') : T.IsSatisfiable :=
  ⟨(Theory.Model.mono (ModelType.is_model h.some) hs).bundled⟩

/--
theorem `isSatisfiable_empty` / 定理 `isSatisfiable_empty`

English:
theorem isSatisfiable_empty
  given: (L : Language.{u, v})
  statement: IsSatisfiable (∅ : L.Theory)
  proof: ⟨default⟩

中文:
定理 isSatisfiable_empty
  条件: (L : Language.{u, v})
  结论: IsSatisfiable (∅ : L.Theory)
  证明: ⟨default⟩
-/
theorem isSatisfiable_empty (L : Language.{u, v}) : IsSatisfiable (∅ : L.Theory) :=
  ⟨default⟩

/--
theorem `isSatisfiable_of_isSatisfiable_onTheory` / 定理 `isSatisfiable_of_isSatisfiable_onTheory`

English:
theorem isSatisfiable_of_isSatisfiable_onTheory
  statement: {L' : Language.{w, w'}} (φ : L ->ᴸ L')
  proof: Model.isSatisfiable (h.some.reduct φ)

中文:
定理 isSatisfiable_of_isSatisfiable_onTheory
  结论: {L' : Language.{w, w'}} (φ : L ->ᴸ L')
  证明: Model.isSatisfiable (h.some.reduct φ)

Depends on / 依赖: Model.isSatisfiable, h.some.reduct, isSatisfiable, reduct
-/
theorem isSatisfiable_of_isSatisfiable_onTheory {L' : Language.{w, w'}} (φ : L ->ᴸ L')
    (h : (φ.onTheory T).IsSatisfiable) : T.IsSatisfiable :=
  Model.isSatisfiable (h.some.reduct φ)

/--
theorem `isSatisfiable_onTheory_iff` / 定理 `isSatisfiable_onTheory_iff`

English:
theorem isSatisfiable_onTheory_iff
  given: {L' : Language.{w, w'}} {φ : L ->ᴸ L'} (h : φ.Injective)
  proof: by
  classical
    refine ⟨isSatisfiable_of_isSatisfiable_onTheory φ, fun h' => ?_⟩
    have : Inhabited h'.some := Classical.inhabited_of_nonempty'
    exact Model.isSatisfiable (h'.some.defaultExpansion h)

中文:
定理 isSatisfiable_onTheory_iff
  条件: {L' : Language.{w, w'}} {φ : L ->ᴸ L'} (h : φ.Injective)
  证明: by
  classical
    refine ⟨isSatisfiable_of_isSatisfiable_onTheory φ, fun h' => ?_⟩
    have : Inhabited h'.some := Classical.inhabited_of_nonempty'
    exact Model.isSatisfiable (h'.some.defaultExpansion h)

Depends on / 依赖: Classical, Classical.inhabited_of_nonempty, Inhabited, Model.isSatisfiable, classical, defaultExpansion, inhabited_of_nonempty, isSatisfiable, isSatisfiable_of_isSatisfiable_onTheory, some.defaultExpansion
-/
theorem isSatisfiable_onTheory_iff {L' : Language.{w, w'}} {φ : L ->ᴸ L'} (h : φ.Injective) :
    (φ.onTheory T).IsSatisfiable ↔ T.IsSatisfiable := by
  classical
    refine ⟨isSatisfiable_of_isSatisfiable_onTheory φ, fun h' => ?_⟩
    have : Inhabited h'.some := Classical.inhabited_of_nonempty'
    exact Model.isSatisfiable (h'.some.defaultExpansion h)

/--
theorem `IsSatisfiable.isFinitelySatisfiable` / 定理 `IsSatisfiable.isFinitelySatisfiable`

English:
theorem IsSatisfiable.isFinitelySatisfiable
  given: (h : T.IsSatisfiable)
  statement: T.IsFinitelySatisfiable
  proof: fun _ => h.mono

中文:
定理 IsSatisfiable.isFinitelySatisfiable
  条件: (h : T.IsSatisfiable)
  结论: T.IsFinitelySatisfiable
  证明: fun _ => h.mono

Depends on / 依赖: h.mono
-/
theorem IsSatisfiable.isFinitelySatisfiable (h : T.IsSatisfiable) : T.IsFinitelySatisfiable :=
  fun _ => h.mono

/--
theorem `isSatisfiable_iff_isFinitelySatisfiable` / 定理 `isSatisfiable_iff_isFinitelySatisfiable`

English:
theorem isSatisfiable_iff_isFinitelySatisfiable
  given: {T : L.Theory}
  proof: ⟨Theory.IsSatisfiable.isFinitelySatisfiable, fun h => by
    set M : Finset T -> Type max u v := fun T0 : Finset T =>
      (h (T0.map (Function.Embedding.subtype fun x => x in T)) T0.map_subtype_subset).some.Carrier
    let M' := Filter.Product (Ultrafilter.of (Filter.atTop : Filter (Finset T))) M


中文:
定理 isSatisfiable_iff_isFinitelySatisfiable
  条件: {T : L.Theory}
  证明: ⟨Theory.IsSatisfiable.isFinitelySatisfiable, fun h => by
    set M : Finset T -> Type max u v := fun T0 : Finset T =>
      (h (T0.map (Function.Embedding.subtype fun x => x in T)) T0.map_subtype_subset).some.Carrier
    let M' := Filter.Product (Ultrafilter.of (Filter.atTop : Filter (Finset T))) M


Depends on / 依赖: Carrier, Embedding, Eventually, Filter, Filter.Eventually.filter_mono, Filter.Product, Filter.atTop, Filter.eventually_atTop, Finset, Function, Function.Embedding.subtype, IsSatisfiable, Product, T0.map, T0.map_subtype_subset, Theory, Theory.IsSatisfiable.isFinitelySatisfiable, Theory.realize_sentenc, Ultrafilter, Ultrafilter.of
-/
theorem isSatisfiable_iff_isFinitelySatisfiable {T : L.Theory} :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable :=
  ⟨Theory.IsSatisfiable.isFinitelySatisfiable, fun h => by
    set M : Finset T -> Type max u v := fun T0 : Finset T =>
      (h (T0.map (Function.Embedding.subtype fun x => x in T)) T0.map_subtype_subset).some.Carrier
    let M' := Filter.Product (Ultrafilter.of (Filter.atTop : Filter (Finset T))) M
    have h' : M' ⊨ T := by
      refine ⟨fun φ hφ => ?_⟩
      rw [Ultraproduct.sentence_realize]
      refine
        Filter.Eventually.filter_mono (Ultrafilter.of_le _)
          (Filter.eventually_atTop.2
            ⟨{⟨φ, hφ⟩}, fun s h' =>
              Theory.realize_sentence_of_mem (s.map (Function.Embedding.subtype fun x => x in T))
                ?_⟩)
      simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe,
        Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨hφ, h' (Finset.mem_singleton_self _)⟩
    exact ⟨ModelType.of T M'⟩⟩

/--
theorem `isSatisfiable_directed_union_iff` / 定理 `isSatisfiable_directed_union_iff`

English:
theorem isSatisfiable_directed_union_iff
  statement: {ι : Type*} [Nonempty ι] {T : ι -> L.Theory}
  proof: by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable]; rw [IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi

中文:
定理 isSatisfiable_directed_union_iff
  结论: {ι : 类型} [Nonempty ι] {T : ι -> L.Theory}
  证明: by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable]; rw [IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi

Depends on / 依赖: IsFinitelySatisfiable, Set.subset_iUnion, exists_mem_subset_of_finset_subset_biUnion, h.exists_mem_subset_of_finset_subset_biUnion, isSatisfiable_iff_isFinitelySatisfiable, subset_iUnion
-/
theorem isSatisfiable_directed_union_iff {ι : Type*} [Nonempty ι] {T : ι -> L.Theory}
    (h : Directed (· subseteq ·) T) : Theory.IsSatisfiable (⋃ i, T i) ↔ forall i, (T i).IsSatisfiable := by
  refine ⟨fun h' i => h'.mono (Set.subset_iUnion _ _), fun h' => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable]; rw [IsFinitelySatisfiable]
  intro T0 hT0
  obtain ⟨i, hi⟩ := h.exists_mem_subset_of_finset_subset_biUnion hT0
  exact (h' i).mono hi

/--
theorem `isSatisfiable_union_distinctConstantsTheory_of_card_le` / 定理 `isSatisfiable_union_distinctConstantsTheory_of_card_le`

English:
theorem isSatisfiable_union_distinctConstantsTheory_of_card_le
  statement: (T : L.Theory) (s : Set α)
  proof: by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  rw [Cardinal.lift_mk_le'] at h
  let : (constantsOn α).Structure M := constantsOn.structure (Function.extend (↑) h.some default)
  have : M ⊨ (L.lhomWithConstants α).onTheory T union L.distinctConstantsTheory s := by
    refi

中文:
定理 isSatisfiable_union_distinctConstantsTheory_of_card_le
  结论: (T : L.Theory) (s : Set α)
  证明: by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  rw [Cardinal.lift_mk_le'] at h
  let : (constantsOn α).Structure M := constantsOn.structure (Function.extend (↑) h.some default)
  have : M ⊨ (L.lhomWithConstants α).onTheory T union L.distinctConstantsTheory s := by
    refi

Depends on / 依赖: Cardinal, Cardinal.lift_mk_le, Classical, Classical.inhabited_of_nonempty, Function, Function.extend, Inhabited, L.distinctConstantsTheory, L.lhomWithConstants, LHom.onTheory_model, Structure, Subtype, Subtype.coe_mk, Subtype.ext_iff, coe_mk, constantsOn, constantsOn.structure, distinctConstantsTheory, ext_iff, extend
-/
theorem isSatisfiable_union_distinctConstantsTheory_of_card_le (T : L.Theory) (s : Set α)
    (M : Type w') [Nonempty M] [L.Structure M] [M ⊨ T]
    (h : Cardinal.lift.{w'} #s <= Cardinal.lift.{w} #M) :
    ((L.lhomWithConstants α).onTheory T union L.distinctConstantsTheory s).IsSatisfiable := by
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  rw [Cardinal.lift_mk_le'] at h
  let : (constantsOn α).Structure M := constantsOn.structure (Function.extend (↑) h.some default)
  have : M ⊨ (L.lhomWithConstants α).onTheory T union L.distinctConstantsTheory s := by
    refine ((LHom.onTheory_model _ _).2 inferInstance).union ?_
    rw [model_distinctConstantsTheory]
    intro a as b bs ab
    rw [← Subtype.coe_mk a as]; rw [← Subtype.coe_mk b bs]; rw [← Subtype.ext_iff]
    exact
      h.some.injective
        ((Subtype.coe_injective.extend_apply h.some default ⟨a, as⟩).symm.trans
          (ab.trans (Subtype.coe_injective.extend_apply h.some default ⟨b, bs⟩)))
  exact Model.isSatisfiable M

/--
theorem `isSatisfiable_union_distinctConstantsTheory_of_infinite` / 定理 `isSatisfiable_union_distinctConstantsTheory_of_infinite`

English:
theorem isSatisfiable_union_distinctConstantsTheory_of_infinite
  statement: (T : L.Theory) (s : Set α)
  proof: by
  rw [distinctConstantsTheory_eq_iUnion]; rw [Set.union_iUnion]; rw [isSatisfiable_directed_union_iff]
  · exact fun t =>
      isSatisfiable_union_distinctConstantsTheory_of_card_le T _ M
        ((lift_le_aleph0.2 (finset_card_lt_aleph0 _).le).trans
          (aleph0_le_lift.2 (aleph0_le_mk M))

中文:
定理 isSatisfiable_union_distinctConstantsTheory_of_infinite
  结论: (T : L.Theory) (s : Set α)
  证明: by
  rw [distinctConstantsTheory_eq_iUnion]; rw [Set.union_iUnion]; rw [isSatisfiable_directed_union_iff]
  · exact fun t =>
      isSatisfiable_union_distinctConstantsTheory_of_card_le T _ M
        ((lift_le_aleph0.2 (finset_card_lt_aleph0 _).le).trans
          (aleph0_le_lift.2 (aleph0_le_mk M))

Depends on / 依赖: Embedding, Finset, Finset.coe_map, Function, Function.Embedding.coe_subtype, Monotone, Monotone.comp, Monotone.directed_le, Set.image, Set.union_iUnion, aleph0_le_lift, aleph0_le_mk, coe_map, coe_subtype, directed_le, distinctConstantsTheory_eq_iUnion, finset_card_lt_aleph0, isSatisfiable_directed_union_iff, isSatisfiable_union_distinctConstantsTheory_of_card_le, lift_le_aleph0
-/
theorem isSatisfiable_union_distinctConstantsTheory_of_infinite (T : L.Theory) (s : Set α)
    (M : Type w') [L.Structure M] [M ⊨ T] [Infinite M] :
    ((L.lhomWithConstants α).onTheory T union L.distinctConstantsTheory s).IsSatisfiable := by
  rw [distinctConstantsTheory_eq_iUnion]; rw [Set.union_iUnion]; rw [isSatisfiable_directed_union_iff]
  · exact fun t =>
      isSatisfiable_union_distinctConstantsTheory_of_card_le T _ M
        ((lift_le_aleph0.2 (finset_card_lt_aleph0 _).le).trans
          (aleph0_le_lift.2 (aleph0_le_mk M)))
  · apply Monotone.directed_le
    refine monotone_const.union (monotone_distinctConstantsTheory.comp ?_)
    simp only [Finset.coe_map, Function.Embedding.coe_subtype]
    exact Monotone.comp (g := Set.image ((↑) : s -> α)) (f := ((↑) : Finset s -> Set s))
      Set.monotone_image fun _ _ => Finset.coe_subset.2

/--
theorem `exists_large_model_of_infinite_model` / 定理 `exists_large_model_of_infinite_model`

English:
theorem exists_large_model_of_infinite_model
  statement: (T : L.Theory) (κ : Cardinal.{w}) (M : Type w')
  proof: by
  obtain ⟨N⟩ :=
    isSatisfiable_union_distinctConstantsTheory_of_infinite T (Set.univ : Set κ.out) M
  refine ⟨(N.is_model.mono Set.subset_union_left).bundled.reduct _, ?_⟩
  have : N ⊨ distinctConstantsTheory _ _ := N.is_model.mono Set.subset_union_right
  rw [ModelType.reduct_Carrier]; rw [co

中文:
定理 exists_large_model_of_infinite_model
  结论: (T : L.Theory) (κ : Cardinal.{w}) (M : Type w')
  证明: by
  obtain ⟨N⟩ :=
    isSatisfiable_union_distinctConstantsTheory_of_infinite T (Set.univ : Set κ.out) M
  refine ⟨(N.is_model.mono Set.subset_union_left).bundled.reduct _, ?_⟩
  have : N ⊨ distinctConstantsTheory _ _ := N.is_model.mono Set.subset_union_right
  rw [ModelType.reduct_Carrier]; rw [co

Depends on / 依赖: Cardinal, Cardinal.mk_out, ModelType, ModelType.reduct_Carrier, N.is_model.mono, Set.subset_union_left, Set.subset_union_right, Set.univ, _root_, _root_.trans, bundled, bundled.reduct, card_le_of_model_distinctConstantsTheory, coe_of, distinctConstantsTheory, isSatisfiable_union_distinctConstantsTheory_of_infinite, is_model, le_of_eq, lift_le, lift_lift
-/
theorem exists_large_model_of_infinite_model (T : L.Theory) (κ : Cardinal.{w}) (M : Type w')
    [L.Structure M] [M ⊨ T] [Infinite M] :
    exists N : ModelType.{_, _, max u v w} T, Cardinal.lift.{max u v w} κ <= #N := by
  obtain ⟨N⟩ :=
    isSatisfiable_union_distinctConstantsTheory_of_infinite T (Set.univ : Set κ.out) M
  refine ⟨(N.is_model.mono Set.subset_union_left).bundled.reduct _, ?_⟩
  have : N ⊨ distinctConstantsTheory _ _ := N.is_model.mono Set.subset_union_right
  rw [ModelType.reduct_Carrier]; rw [coe_of]
  refine _root_.trans (lift_le.2 (le_of_eq (Cardinal.mk_out κ).symm)) ?_
  rw [← mk_univ]
  refine
    (card_le_of_model_distinctConstantsTheory L Set.univ N).trans (lift_le.{max u v w}.1 ?_)
  rw [lift_lift]

/--
theorem `isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset` / 定理 `isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset`

English:
theorem isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset
  given: {ι : Type*} (T : ι -> L.Theory)
  proof: by
  refine
    ⟨fun h s => h.mono (Set.iUnion_mono fun _ => Set.iUnion_subset_iff.2 fun _ => refl _),
      fun h => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable]
  intro s hs
  rw [Set.iUnion_eq_iUnion_finset] at hs
  obtain ⟨t, ht⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion (by
 

中文:
定理 isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset
  条件: {ι : 类型} (T : ι -> L.Theory)
  证明: by
  refine
    ⟨fun h s => h.mono (Set.iUnion_mono fun _ => Set.iUnion_subset_iff.2 fun _ => refl _),
      fun h => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable]
  intro s hs
  rw [Set.iUnion_eq_iUnion_finset] at hs
  obtain ⟨t, ht⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion (by
 

Depends on / 依赖: Directed, Directed.exists_mem_subset_of_finset_subset_biUnion, Monotone, Monotone.directed_le, Set.iUnion_eq_iUnion_finset, Set.iUnion_mono, Set.iUnion_subset_iff, directed_le, exists_mem_subset_of_finset_subset_biUnion, h.mono, iUnion_eq_iUnion_finset, iUnion_mono, iUnion_subset_iff, isSatisfiable_iff_isFinitelySatisfiable
-/
theorem isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset {ι : Type*} (T : ι -> L.Theory) :
    IsSatisfiable (⋃ i, T i) ↔ forall s : Finset ι, IsSatisfiable (⋃ i in s, T i) := by
  refine
    ⟨fun h s => h.mono (Set.iUnion_mono fun _ => Set.iUnion_subset_iff.2 fun _ => refl _),
      fun h => ?_⟩
  rw [isSatisfiable_iff_isFinitelySatisfiable]
  intro s hs
  rw [Set.iUnion_eq_iUnion_finset] at hs
  obtain ⟨t, ht⟩ := Directed.exists_mem_subset_of_finset_subset_biUnion (by
    exact Monotone.directed_le fun t1 t2 (h : forall ⦃x⦄, x in t1 -> x in t2) =>
      Set.iUnion_mono fun _ => Set.iUnion_mono' fun h1 => ⟨h h1, refl _⟩) hs
  exact (h t).mono ht

end Theory

variable (L)

/--
theorem `exists_elementaryEmbedding_card_eq_of_le` / 定理 `exists_elementaryEmbedding_card_eq_of_le`

English:
theorem exists_elementaryEmbedding_card_eq_of_le
  statement: (M : Type w') [L.Structure M]
  proof: by
  obtain ⟨S, _, hS⟩ := exists_elementarySubstructure_card_eq L ∅ κ h1 (by simp) h2 h3
  have : Small.{w} S := by
    rw [← lift_inj.{_]; rw [w + 1}]; rw [lift_lift]; rw [lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  refine
    ⟨(equivShrink S).bundle

中文:
定理 exists_elementaryEmbedding_card_eq_of_le
  结论: (M : Type w') [L.Structure M]
  证明: by
  obtain ⟨S, _, hS⟩ := exists_elementarySubstructure_card_eq L ∅ κ h1 (by simp) h2 h3
  have : Small.{w} S := by
    rw [← lift_inj.{_]; rw [w + 1}]; rw [lift_lift]; rw [lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  refine
    ⟨(equivShrink S).bundle

Depends on / 依赖: Equiv.bundledInducedEquiv, Equiv.bundledInduced_, S.subtype.comp, _root_, _root_.trans, bundledInduced, bundledInducedEquiv, equivShrink, exists_elementarySubstructure_card_eq, lift_inj, lift_lift, lift_lt_univ, lift_mk_shrink, lt_of_eq_of_lt, small_iff_lift_mk_lt_univ, subtype, symm.toElementaryEmbedding, toElementaryEmbedding
-/
theorem exists_elementaryEmbedding_card_eq_of_le (M : Type w') [L.Structure M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.lift.{max u v} κ)
    (h3 : lift.{w'} κ <= Cardinal.lift.{w} #M) :
    exists N : Bundled L.Structure, Nonempty (N ↪ₑ[L] M) ∧ #N = κ := by
  obtain ⟨S, _, hS⟩ := exists_elementarySubstructure_card_eq L ∅ κ h1 (by simp) h2 h3
  have : Small.{w} S := by
    rw [← lift_inj.{_]; rw [w + 1}]; rw [lift_lift]; rw [lift_lift] at hS
    exact small_iff_lift_mk_lt_univ.2 (lt_of_eq_of_lt hS κ.lift_lt_univ')
  refine
    ⟨(equivShrink S).bundledInduced L,
      ⟨S.subtype.comp (Equiv.bundledInducedEquiv L _).symm.toElementaryEmbedding⟩,
      lift_inj.1 (_root_.trans ?_ hS)⟩
  simp only [Equiv.bundledInduced_α, lift_mk_shrink']

section

/--
theorem `exists_elementaryEmbedding_card_eq_of_ge` / 定理 `exists_elementaryEmbedding_card_eq_of_ge`

English:
theorem exists_elementaryEmbedding_card_eq_of_ge
  statement: (M : Type w') [L.Structure M] [iM : Infinite M]
  proof: by
  obtain ⟨N0, hN0⟩ := (L.elementaryDiagram M).exists_large_model_of_infinite_model κ M
  rw [← lift_le.{max u v}]; rw [lift_lift]; rw [lift_lift] at h2
  obtain ⟨N, ⟨NN0⟩, hN⟩ :=
    exists_elementaryEmbedding_card_eq_of_le L[[M]] N0 κ
      (aleph0_le_lift.1 ((aleph0_le_lift.2 (aleph0_le_mk M)).

中文:
定理 exists_elementaryEmbedding_card_eq_of_ge
  结论: (M : Type w') [L.Structure M] [iM : Infinite M]
  证明: by
  obtain ⟨N0, hN0⟩ := (L.elementaryDiagram M).exists_large_model_of_infinite_model κ M
  rw [← lift_le.{max u v}]; rw [lift_lift]; rw [lift_lift] at h2
  obtain ⟨N, ⟨NN0⟩, hN⟩ :=
    exists_elementaryEmbedding_card_eq_of_le L[[M]] N0 κ
      (aleph0_le_lift.1 ((aleph0_le_lift.2 (aleph0_le_mk M)).

Depends on / 依赖: L.elementaryDiagram, add_comm, add_eq_max, aleph0_le_lift, aleph0_le_mk, card_withConstants, elementaryDiagram, exists_elementaryEmbedding_card_eq_of_le, exists_large_model_of_infinite_model, infinite_iff, lift_add, lift_le, lift_lift, max_le_iff
-/
theorem exists_elementaryEmbedding_card_eq_of_ge (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : Cardinal.lift.{w} L.card <= Cardinal.lift.{max u v} κ)
    (h2 : Cardinal.lift.{w} #M <= Cardinal.lift.{w'} κ) :
    exists N : Bundled L.Structure, Nonempty (M ↪ₑ[L] N) ∧ #N = κ := by
  obtain ⟨N0, hN0⟩ := (L.elementaryDiagram M).exists_large_model_of_infinite_model κ M
  rw [← lift_le.{max u v}]; rw [lift_lift]; rw [lift_lift] at h2
  obtain ⟨N, ⟨NN0⟩, hN⟩ :=
    exists_elementaryEmbedding_card_eq_of_le L[[M]] N0 κ
      (aleph0_le_lift.1 ((aleph0_le_lift.2 (aleph0_le_mk M)).trans h2))
      (by
        simp only [card_withConstants, lift_add, lift_lift]
        rw [add_comm]; rw [add_eq_max (aleph0_le_lift.2 (infinite_iff.1 iM))]; rw [max_le_iff]
        rw [← lift_le.{w'}]; rw [lift_lift]; rw [lift_lift] at h1
        exact ⟨h2, h1⟩)
      (hN0.trans (by rw [← lift_umax, lift_id]))
  let := (lhomWithConstants L M).reduct N
  have h : N ⊨ L.elementaryDiagram M :=
    (NN0.theory_model_iff (L.elementaryDiagram M)).2 inferInstance
  refine ⟨Bundled.of N, ⟨?_⟩, hN⟩
  apply ElementaryEmbedding.ofModelsElementaryDiagram L M N

end

/--
theorem `exists_elementaryEmbedding_card_eq` / 定理 `exists_elementaryEmbedding_card_eq`

English:
theorem exists_elementaryEmbedding_card_eq
  statement: (M : Type w') [L.Structure M] [iM : Infinite M]
  proof: by
  cases le_or_gt (lift.{w'} κ) (Cardinal.lift.{w} #M) with
  | inl h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, Or.inl hN1, hN2⟩
  | inr h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_ge L M κ h2 (le_of_lt h)
    exa

中文:
定理 exists_elementaryEmbedding_card_eq
  结论: (M : Type w') [L.Structure M] [iM : Infinite M]
  证明: by
  cases le_or_gt (lift.{w'} κ) (Cardinal.lift.{w} #M) with
  | inl h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, Or.inl hN1, hN2⟩
  | inr h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_ge L M κ h2 (le_of_lt h)
    exa

Depends on / 依赖: Cardinal, Cardinal.lift, Or.inl, Or.inr, exists_elementaryEmbedding_card_eq_of_ge, exists_elementaryEmbedding_card_eq_of_le, le_of_lt, le_or_gt
-/
theorem exists_elementaryEmbedding_card_eq (M : Type w') [L.Structure M] [iM : Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.lift.{max u v} κ) :
    exists N : Bundled L.Structure, (Nonempty (N ↪ₑ[L] M) ∨ Nonempty (M ↪ₑ[L] N)) ∧ #N = κ := by
  cases le_or_gt (lift.{w'} κ) (Cardinal.lift.{w} #M) with
  | inl h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_le L M κ h1 h2 h
    exact ⟨N, Or.inl hN1, hN2⟩
  | inr h =>
    obtain ⟨N, hN1, hN2⟩ := exists_elementaryEmbedding_card_eq_of_ge L M κ h2 (le_of_lt h)
    exact ⟨N, Or.inr hN1, hN2⟩

/--
theorem `exists_elementarilyEquivalent_card_eq` / 定理 `exists_elementarilyEquivalent_card_eq`

English:
theorem exists_elementarilyEquivalent_card_eq
  statement: (M : Type w') [L.Structure M] [Infinite M]
  proof: by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementaryEmbedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, MN.some.elementarilyEquivalent, hNκ⟩

中文:
定理 exists_elementarilyEquivalent_card_eq
  结论: (M : Type w') [L.Structure M] [Infinite M]
  证明: by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementaryEmbedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, MN.some.elementarilyEquivalent, hNκ⟩

Depends on / 依赖: MN.some.elementarilyEquivalent, NM.some.elementarilyEquivalent.symm, elementarilyEquivalent, exists_elementaryEmbedding_card_eq
-/
theorem exists_elementarilyEquivalent_card_eq (M : Type w') [L.Structure M] [Infinite M]
    (κ : Cardinal.{w}) (h1 : ℵ₀ <= κ) (h2 : lift.{w} L.card <= Cardinal.lift.{max u v} κ) :
    exists N : CategoryTheory.Bundled L.Structure, (M ≅[L] N) ∧ #N = κ := by
  obtain ⟨N, NM | MN, hNκ⟩ := exists_elementaryEmbedding_card_eq L M κ h1 h2
  · exact ⟨N, NM.some.elementarilyEquivalent.symm, hNκ⟩
  · exact ⟨N, MN.some.elementarilyEquivalent, hNκ⟩

variable {L}

namespace Theory

/--
theorem `exists_model_card_eq` / 定理 `exists_model_card_eq`

English:
theorem exists_model_card_eq
  statement: (h : exists M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
  proof: by
  cases h with
  | intro M MI =>
    obtain ⟨N, hN, rfl⟩ := exists_elementarilyEquivalent_card_eq L M κ h1 h2
    have : Nonempty N := hN.nonempty
    exact ⟨hN.theory_model.bundled, rfl⟩

中文:
定理 exists_model_card_eq
  结论: (h : 存在 M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
  证明: by
  cases h with
  | intro M MI =>
    obtain ⟨N, hN, rfl⟩ := exists_elementarilyEquivalent_card_eq L M κ h1 h2
    have : Nonempty N := hN.nonempty
    exact ⟨hN.theory_model.bundled, rfl⟩

Depends on / 依赖: Nonempty, bundled, exists_elementarilyEquivalent_card_eq, hN.nonempty, hN.theory_model.bundled, nonempty, theory_model
-/
theorem exists_model_card_eq (h : exists M : ModelType.{u, v, max u v} T, Infinite M) (κ : Cardinal.{w})
    (h1 : ℵ₀ <= κ) (h2 : Cardinal.lift.{w} L.card <= Cardinal.lift.{max u v} κ) :
    exists N : ModelType.{u, v, w} T, #N = κ := by
  cases h with
  | intro M MI =>
    obtain ⟨N, hN, rfl⟩ := exists_elementarilyEquivalent_card_eq L M κ h1 h2
    have : Nonempty N := hN.nonempty
    exact ⟨hN.theory_model.bundled, rfl⟩

variable (T)

/--
Definition of `ModelsBoundedFormula` / `ModelsBoundedFormula` 的定义

English:
definition ModelsBoundedFormula
  signature: (φ : L.BoundedFormula α n)
  body: forall (M : ModelType.{u, v, max u v w} T) (v : α -> M) (xs : Fin n -> M), φ.Realize v xs

@[inherit_doc FirstOrder.Language.Theory.ModelsBoundedFormula]
infixl:51 " ⊨ᵇ " => ModelsBoundedFormula -- input using \|= or \vDash, but not using \models

中文:
定义 ModelsBoundedFormula
  签名: (φ : L.BoundedFormula α n)
  定义体: forall (M : ModelType.{u, v, max u v w} T) (v : α -> M) (xs : Fin n -> M), φ.Realize v xs

@[inherit_doc FirstOrder.Language.Theory.ModelsBoundedFormula]
infixl:51 " ⊨ᵇ " => ModelsBoundedFormula -- input using \|= or \vDash, but not using \models

Depends on / 依赖: ModelType, Realize
-/
def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  forall (M : ModelType.{u, v, max u v w} T) (v : α -> M) (xs : Fin n -> M), φ.Realize v xs

@[inherit_doc FirstOrder.Language.Theory.ModelsBoundedFormula]
infixl:51 " ⊨ᵇ " => ModelsBoundedFormula -- input using \|= or \vDash, but not using \models

variable {T}

/--
theorem `models_formula_iff` / 定理 `models_formula_iff`

English:
theorem models_formula_iff
  given: {φ : L.Formula α}
  proof: forall_congr' fun _ => forall_congr' fun _ => Unique.forall_iff

中文:
定理 models_formula_iff
  条件: {φ : L.Formula α}
  证明: forall_congr' fun _ => forall_congr' fun _ => Unique.forall_iff

Depends on / 依赖: Unique, Unique.forall_iff, forall_congr, forall_iff
-/
theorem models_formula_iff {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ forall (M : ModelType.{u, v, max u v w} T) (v : α -> M), φ.Realize v :=
  forall_congr' fun _ => forall_congr' fun _ => Unique.forall_iff

/--
theorem `models_sentence_iff` / 定理 `models_sentence_iff`

English:
theorem models_sentence_iff
  given: {φ : L.Sentence}
  statement: T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ
  proof: models_formula_iff.trans (forall_congr' fun _ => Unique.forall_iff)

中文:
定理 models_sentence_iff
  条件: {φ : L.Sentence}
  结论: T ⊨ᵇ φ ↔ 对任意 M : ModelType.{u, v, max u v} T, M ⊨ φ
  证明: models_formula_iff.trans (forall_congr' fun _ => Unique.forall_iff)

Depends on / 依赖: Unique, Unique.forall_iff, forall_congr, forall_iff, models_formula_iff, models_formula_iff.trans
-/
theorem models_sentence_iff {φ : L.Sentence} : T ⊨ᵇ φ ↔ forall M : ModelType.{u, v, max u v} T, M ⊨ φ :=
  models_formula_iff.trans (forall_congr' fun _ => Unique.forall_iff)

/--
theorem `models_sentence_of_mem` / 定理 `models_sentence_of_mem`

English:
theorem models_sentence_of_mem
  given: {φ : L.Sentence} (h : φ in T)
  statement: T ⊨ᵇ φ
  proof: models_sentence_iff.2 fun _ => realize_sentence_of_mem T h

中文:
定理 models_sentence_of_mem
  条件: {φ : L.Sentence} (h : φ in T)
  结论: T ⊨ᵇ φ
  证明: models_sentence_iff.2 fun _ => realize_sentence_of_mem T h

Depends on / 依赖: models_sentence_iff, realize_sentence_of_mem
-/
theorem models_sentence_of_mem {φ : L.Sentence} (h : φ in T) : T ⊨ᵇ φ :=
  models_sentence_iff.2 fun _ => realize_sentence_of_mem T h

/--
theorem `models_iff_not_satisfiable` / 定理 `models_iff_not_satisfiable`

English:
theorem models_iff_not_satisfiable
  given: (φ : L.Sentence)
  statement: T ⊨ᵇ φ ↔ ¬IsSatisfiable (T union {φ.not})
  proof: by
  rw [models_sentence_iff]; rw [IsSatisfiable]
  refine
    ⟨fun h1 h2 =>
      (Sentence.realize_not _).1
        (realize_sentence_of_mem (T union {Formula.not φ})
          (Set.subset_union_right (Set.mem_singleton _)))
        (h1 (h2.some.subtheoryModel Set.subset_union_left)),
      fun h 

中文:
定理 models_iff_not_satisfiable
  条件: (φ : L.Sentence)
  结论: T ⊨ᵇ φ ↔ ¬IsSatisfiable (T union {φ.not})
  证明: by
  rw [models_sentence_iff]; rw [IsSatisfiable]
  refine
    ⟨fun h1 h2 =>
      (Sentence.realize_not _).1
        (realize_sentence_of_mem (T union {Formula.not φ})
          (Set.subset_union_right (Set.mem_singleton _)))
        (h1 (h2.some.subtheoryModel Set.subset_union_left)),
      fun h 

Depends on / 依赖: Carrier, Formula, Formula.not, IsSatisfiable, Sentence, Sentence.realize_not, Set.mem_singleton, Set.mem_singleton_iff, Set.subset_union_left, Set.subset_union_right, contrapose, h2.some.subtheoryModel, is_model, mem_singleton, mem_singleton_iff, models_sentence_iff, realize_not, realize_sentence_of_mem, subset_union_left, subset_union_right
-/
theorem models_iff_not_satisfiable (φ : L.Sentence) : T ⊨ᵇ φ ↔ ¬IsSatisfiable (T union {φ.not}) := by
  rw [models_sentence_iff]; rw [IsSatisfiable]
  refine
    ⟨fun h1 h2 =>
      (Sentence.realize_not _).1
        (realize_sentence_of_mem (T union {Formula.not φ})
          (Set.subset_union_right (Set.mem_singleton _)))
        (h1 (h2.some.subtheoryModel Set.subset_union_left)),
      fun h M => ?_⟩
  contrapose h
  rw [← Sentence.realize_not] at h
  refine
    ⟨{ Carrier := M
        is_model := ⟨fun ψ hψ => hψ.elim (realize_sentence_of_mem _) fun h' => ?_⟩ }⟩
  rw [Set.mem_singleton_iff.1 h']
  exact h

/--
theorem `ModelsBoundedFormula.realize_sentence` / 定理 `ModelsBoundedFormula.realize_sentence`

English:
theorem ModelsBoundedFormula.realize_sentence
  statement: {φ : L.Sentence} (h : T ⊨ᵇ φ) (M : Type*)
  proof: by
  rw [models_iff_not_satisfiable] at h
  contrapose h
  have : M ⊨ T union {Formula.not φ} := by
    simp only [Set.union_singleton, model_iff, Set.mem_insert_iff, forall_eq_or_imp,
      Sentence.realize_not]
    rw [← model_iff]
    exact ⟨h, inferInstance⟩
  exact Model.isSatisfiable M

中文:
定理 ModelsBoundedFormula.realize_sentence
  结论: {φ : L.Sentence} (h : T ⊨ᵇ φ) (M : 类型)
  证明: by
  rw [models_iff_not_satisfiable] at h
  contrapose h
  have : M ⊨ T union {Formula.not φ} := by
    simp only [Set.union_singleton, model_iff, Set.mem_insert_iff, forall_eq_or_imp,
      Sentence.realize_not]
    rw [← model_iff]
    exact ⟨h, inferInstance⟩
  exact Model.isSatisfiable M

Depends on / 依赖: Formula, Formula.not, Model.isSatisfiable, Sentence, Sentence.realize_not, Set.mem_insert_iff, Set.union_singleton, contrapose, forall_eq_or_imp, isSatisfiable, mem_insert_iff, model_iff, models_iff_not_satisfiable, realize_not, union_singleton
-/
theorem ModelsBoundedFormula.realize_sentence {φ : L.Sentence} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] : M ⊨ φ := by
  rw [models_iff_not_satisfiable] at h
  contrapose h
  have : M ⊨ T union {Formula.not φ} := by
    simp only [Set.union_singleton, model_iff, Set.mem_insert_iff, forall_eq_or_imp,
      Sentence.realize_not]
    rw [← model_iff]
    exact ⟨h, inferInstance⟩
  exact Model.isSatisfiable M

/--
theorem `models_formula_iff_onTheory_models_equivSentence` / 定理 `models_formula_iff_onTheory_models_equivSentence`

English:
theorem models_formula_iff_onTheory_models_equivSentence
  given: {φ : L.Formula α}
  proof: by
  refine ⟨fun h => models_sentence_iff.2 (fun M => ?_),
    fun h => models_formula_iff.2 (fun M v => ?_)⟩
  · let := (L.lhomWithConstants α).reduct M
    rw [Formula.realize_equivSentence]
    have : M ⊨ T := (LHom.onTheory_model _ _).1 M.is_model -- why isn't M.is_model inferInstance?
    let M

中文:
定理 models_formula_iff_onTheory_models_equivSentence
  条件: {φ : L.Formula α}
  证明: by
  refine ⟨fun h => models_sentence_iff.2 (fun M => ?_),
    fun h => models_formula_iff.2 (fun M v => ?_)⟩
  · let := (L.lhomWithConstants α).reduct M
    rw [Formula.realize_equivSentence]
    have : M ⊨ T := (LHom.onTheory_model _ _).1 M.is_model -- why isn't M.is_model inferInstance?
    let M

Depends on / 依赖: Formula, Formula.realize_equivSentence, L.con, L.lhomWithConstants, LHom.onTheory_model, M.is_model, ModelType, Structure, Theory, Theory.ModelType.of, constantsOn, constantsOn.structure, is_model, lhomWithConstants, models_formula_iff, models_sentence_iff, onTheory, onTheory_model, realize_equivSentence, reduct
-/
theorem models_formula_iff_onTheory_models_equivSentence {φ : L.Formula α} :
    T ⊨ᵇ φ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ Formula.equivSentence φ := by
  refine ⟨fun h => models_sentence_iff.2 (fun M => ?_),
    fun h => models_formula_iff.2 (fun M v => ?_)⟩
  · let := (L.lhomWithConstants α).reduct M
    rw [Formula.realize_equivSentence]
    have : M ⊨ T := (LHom.onTheory_model _ _).1 M.is_model -- why isn't M.is_model inferInstance?
    let M' := Theory.ModelType.of T M
    exact h M' (fun a => (L.con a : M)) _
  · let : (constantsOn α).Structure M := constantsOn.structure v
    have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
    exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)

/--
theorem `ModelsBoundedFormula.realize_formula` / 定理 `ModelsBoundedFormula.realize_formula`

English:
theorem ModelsBoundedFormula.realize_formula
  statement: {φ : L.Formula α} (h : T ⊨ᵇ φ) (M : Type*)
  proof: by
  rw [models_formula_iff_onTheory_models_equivSentence] at h
  let : (constantsOn α).Structure M := constantsOn.structure v
  have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
  exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)

中文:
定理 ModelsBoundedFormula.realize_formula
  结论: {φ : L.Formula α} (h : T ⊨ᵇ φ) (M : 类型)
  证明: by
  rw [models_formula_iff_onTheory_models_equivSentence] at h
  let : (constantsOn α).Structure M := constantsOn.structure v
  have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
  exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)

Depends on / 依赖: Formula, Formula.realize_equivSentence, L.lhomWithConstants, LHom.onTheory_model, Structure, constantsOn, constantsOn.structure, h.realize_sentence, lhomWithConstants, models_formula_iff_onTheory_models_equivSentence, onTheory, onTheory_model, realize_equivSentence, realize_sentence, structure
-/
theorem ModelsBoundedFormula.realize_formula {φ : L.Formula α} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] {v : α -> M} : φ.Realize v := by
  rw [models_formula_iff_onTheory_models_equivSentence] at h
  let : (constantsOn α).Structure M := constantsOn.structure v
  have : M ⊨ (L.lhomWithConstants α).onTheory T := (LHom.onTheory_model _ _).2 inferInstance
  exact (Formula.realize_equivSentence _ _).1 (h.realize_sentence M)

/--
theorem `models_toFormula_iff` / 定理 `models_toFormula_iff`

English:
theorem models_toFormula_iff
  given: {φ : L.BoundedFormula α n}
  statement: T ⊨ᵇ φ.toFormula ↔ T ⊨ᵇ φ
  proof: by
  refine ⟨fun h M v xs => ?_, ?_⟩
  · have h' : φ.toFormula.Realize (Sum.elim v xs) := h.realize_formula M
    simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
    exact h'
  · simp only [models_formula_iff, BoundedFormula.realize_toFormula]
    exact fun h

中文:
定理 models_toFormula_iff
  条件: {φ : L.BoundedFormula α n}
  结论: T ⊨ᵇ φ.toFormula ↔ T ⊨ᵇ φ
  证明: by
  refine ⟨fun h M v xs => ?_, ?_⟩
  · have h' : φ.toFormula.Realize (Sum.elim v xs) := h.realize_formula M
    simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
    exact h'
  · simp only [models_formula_iff, BoundedFormula.realize_toFormula]
    exact fun h

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_toFormula, Realize, Sum.elim, Sum.elim_comp_inl, Sum.elim_comp_inr, elim_comp_inl, elim_comp_inr, h.realize_formula, models_formula_iff, realize_formula, realize_toFormula, toFormula, toFormula.Realize
-/
theorem models_toFormula_iff {φ : L.BoundedFormula α n} : T ⊨ᵇ φ.toFormula ↔ T ⊨ᵇ φ := by
  refine ⟨fun h M v xs => ?_, ?_⟩
  · have h' : φ.toFormula.Realize (Sum.elim v xs) := h.realize_formula M
    simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
    exact h'
  · simp only [models_formula_iff, BoundedFormula.realize_toFormula]
    exact fun h M v => h M _ _

/--
theorem `ModelsBoundedFormula.realize_boundedFormula` / 定理 `ModelsBoundedFormula.realize_boundedFormula`

English:
theorem ModelsBoundedFormula.realize_boundedFormula
  proof: by
  have h' : φ.toFormula.Realize (Sum.elim v xs) := (models_toFormula_iff.2 h).realize_formula M
  simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
  exact h'

中文:
定理 ModelsBoundedFormula.realize_boundedFormula
  证明: by
  have h' : φ.toFormula.Realize (Sum.elim v xs) := (models_toFormula_iff.2 h).realize_formula M
  simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
  exact h'

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_toFormula, Realize, Sum.elim, Sum.elim_comp_inl, Sum.elim_comp_inr, elim_comp_inl, elim_comp_inr, models_toFormula_iff, realize_formula, realize_toFormula, toFormula, toFormula.Realize
-/
theorem ModelsBoundedFormula.realize_boundedFormula
    {φ : L.BoundedFormula α n} (h : T ⊨ᵇ φ) (M : Type*)
    [L.Structure M] [M ⊨ T] [Nonempty M] {v : α -> M} {xs : Fin n -> M} : φ.Realize v xs := by
  have h' : φ.toFormula.Realize (Sum.elim v xs) := (models_toFormula_iff.2 h).realize_formula M
  simp only [BoundedFormula.realize_toFormula, Sum.elim_comp_inl, Sum.elim_comp_inr] at h'
  exact h'

/--
theorem `models_of_models_theory` / 定理 `models_of_models_theory`

English:
theorem models_of_models_theory
  statement: {T' : L.Theory}
  proof: fun M => by
  have hM : M ⊨ T' := T'.model_iff.2 (fun ψ hψ => (h ψ hψ).realize_sentence M)
  let M' : ModelType T' := ⟨M⟩
  exact hφ M'

中文:
定理 models_of_models_theory
  结论: {T' : L.Theory}
  证明: fun M => by
  have hM : M ⊨ T' := T'.model_iff.2 (fun ψ hψ => (h ψ hψ).realize_sentence M)
  let M' : ModelType T' := ⟨M⟩
  exact hφ M'

Depends on / 依赖: ModelType, model_iff, realize_sentence
-/
theorem models_of_models_theory {T' : L.Theory}
    (h : forall φ : L.Sentence, φ in T' -> T ⊨ᵇ φ)
    {φ : L.Formula α} (hφ : T' ⊨ᵇ φ) : T ⊨ᵇ φ := fun M => by
  have hM : M ⊨ T' := T'.model_iff.2 (fun ψ hψ => (h ψ hψ).realize_sentence M)
  let M' : ModelType T' := ⟨M⟩
  exact hφ M'

/--
theorem `models_iff_finset_models` / 定理 `models_iff_finset_models`

English:
theorem models_iff_finset_models
  given: {φ : L.Sentence}
  proof: by
  simp only [models_iff_not_satisfiable]
  rw [isSatisfiable_iff_isFinitelySatisfiable]; rw [IsFinitelySatisfiable]
  contrapose!
  let := Classical.decEq (Sentence L)
  constructor
  · intro h T0 hT0
    simpa using h (T0 union {Formula.not φ})
      (by
        simp only [Finset.coe_union, Fins

中文:
定理 models_iff_finset_models
  条件: {φ : L.Sentence}
  证明: by
  simp only [models_iff_not_satisfiable]
  rw [isSatisfiable_iff_isFinitelySatisfiable]; rw [IsFinitelySatisfiable]
  contrapose!
  let := Classical.decEq (Sentence L)
  constructor
  · intro h T0 hT0
    simpa using h (T0 union {Formula.not φ})
      (by
        simp only [Finset.coe_union, Fins

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.coe_singleton, Finset.coe_union, Formula, Formula.not, IsFinitelySatisfiable, IsSatisfiable, IsSatisfiable.mono, Sentence, Set.Subset.refl, Set.union_subset_union, Subset, T0.erase, coe_singleton, coe_union, contrapose, isSatisfiable_iff_isFinitelySatisfiable, models_iff_not_satisfiable
-/
theorem models_iff_finset_models {φ : L.Sentence} :
    T ⊨ᵇ φ ↔ exists T0 : Finset L.Sentence, (T0 : L.Theory) subseteq T ∧ (T0 : L.Theory) ⊨ᵇ φ := by
  simp only [models_iff_not_satisfiable]
  rw [isSatisfiable_iff_isFinitelySatisfiable]; rw [IsFinitelySatisfiable]
  contrapose!
  let := Classical.decEq (Sentence L)
  constructor
  · intro h T0 hT0
    simpa using h (T0 union {Formula.not φ})
      (by
        simp only [Finset.coe_union, Finset.coe_singleton]
        exact Set.union_subset_union hT0 (Set.Subset.refl _))
  · intro h T0 hT0
    exact IsSatisfiable.mono (h (T0.erase (Formula.not φ))
      (by simpa using hT0)) (by simp)

/--
Definition of `IsComplete` / `IsComplete` 的定义

English:
definition IsComplete
  signature: (T : L.Theory)
  body: T.IsSatisfiable ∧ forall φ : L.Sentence, T ⊨ᵇ φ ∨ T ⊨ᵇ φ.not

中文:
定义 IsComplete
  签名: (T : L.Theory)
  定义体: T.IsSatisfiable ∧ forall φ : L.Sentence, T ⊨ᵇ φ ∨ T ⊨ᵇ φ.not

Depends on / 依赖: IsSatisfiable, L.Sentence, Sentence, T.IsSatisfiable
-/
def IsComplete (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ forall φ : L.Sentence, T ⊨ᵇ φ ∨ T ⊨ᵇ φ.not

namespace IsComplete

/--
theorem `models_not_iff` / 定理 `models_not_iff`

English:
theorem models_not_iff
  given: (h : T.IsComplete) (φ : L.Sentence)
  statement: T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ
  proof: by
  rcases h.2 φ with hφ | hφn
  · simp only [hφ, not_true, iff_false]
    rw [models_sentence_iff]; rw [not_forall]
    refine ⟨h.1.some, ?_⟩
    simp only [Sentence.realize_not, Classical.not_not]
    exact models_sentence_iff.1 hφ _
  · simp only [hφn, true_iff]
    intro hφ
    rw [models_sente

中文:
定理 models_not_iff
  条件: (h : T.IsComplete) (φ : L.Sentence)
  结论: T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ
  证明: by
  rcases h.2 φ with hφ | hφn
  · simp only [hφ, not_true, iff_false]
    rw [models_sentence_iff]; rw [not_forall]
    refine ⟨h.1.some, ?_⟩
    simp only [Sentence.realize_not, Classical.not_not]
    exact models_sentence_iff.1 hφ _
  · simp only [hφn, true_iff]
    intro hφ
    rw [models_sente

Depends on / 依赖: Classical, Classical.not_not, Sentence, Sentence.realize_not, iff_false, models_sentence_iff, not_forall, not_not, not_true, realize_not, true_iff
-/
theorem models_not_iff (h : T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · simp only [hφ, not_true, iff_false]
    rw [models_sentence_iff]; rw [not_forall]
    refine ⟨h.1.some, ?_⟩
    simp only [Sentence.realize_not, Classical.not_not]
    exact models_sentence_iff.1 hφ _
  · simp only [hφn, true_iff]
    intro hφ
    rw [models_sentence_iff] at *
    exact hφn h.1.some (hφ _)

/--
theorem `realize_sentence_iff` / 定理 `realize_sentence_iff`

English:
theorem realize_sentence_iff
  statement: (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M]
  proof: by
  rcases h.2 φ with hφ | hφn
  · exact iff_of_true (hφ.realize_sentence M) hφ
  · exact
      iff_of_false ((Sentence.realize_not M).1 (hφn.realize_sentence M))
        ((h.models_not_iff φ).1 hφn)

中文:
定理 realize_sentence_iff
  结论: (h : T.IsComplete) (φ : L.Sentence) (M : 类型) [L.Structure M]
  证明: by
  rcases h.2 φ with hφ | hφn
  · exact iff_of_true (hφ.realize_sentence M) hφ
  · exact
      iff_of_false ((Sentence.realize_not M).1 (hφn.realize_sentence M))
        ((h.models_not_iff φ).1 hφn)

Depends on / 依赖: Sentence, Sentence.realize_not, h.models_not_iff, iff_of_false, iff_of_true, models_not_iff, n.realize_sentence, realize_not, realize_sentence
-/
theorem realize_sentence_iff (h : T.IsComplete) (φ : L.Sentence) (M : Type*) [L.Structure M]
    [M ⊨ T] [Nonempty M] : M ⊨ φ ↔ T ⊨ᵇ φ := by
  rcases h.2 φ with hφ | hφn
  · exact iff_of_true (hφ.realize_sentence M) hφ
  · exact
      iff_of_false ((Sentence.realize_not M).1 (hφn.realize_sentence M))
        ((h.models_not_iff φ).1 hφn)

/--
theorem `eq_complete_theory` / 定理 `eq_complete_theory`

English:
theorem eq_complete_theory
  given: (h : T.IsComplete) (M : Type*) [L.Structure M] [M ⊨ T] [Nonempty M]
  proof: by
  ext φ
  simp only [Set.mem_ofPred_eq, L.mem_completeTheory]
  refine ⟨fun h_models => h_models.realize_sentence M, fun h_realize => ?_⟩
  cases h.2 φ with
  | inl hT => exact hT
  | inr hT =>
      have : M ⊨ φ.not := hT.realize_sentence M
      rw [Sentence.realize_not] at this
      contradic

中文:
定理 eq_complete_theory
  条件: (h : T.IsComplete) (M : 类型) [L.Structure M] [M ⊨ T] [Nonempty M]
  证明: by
  ext φ
  simp only [Set.mem_ofPred_eq, L.mem_completeTheory]
  refine ⟨fun h_models => h_models.realize_sentence M, fun h_realize => ?_⟩
  cases h.2 φ with
  | inl hT => exact hT
  | inr hT =>
      have : M ⊨ φ.not := hT.realize_sentence M
      rw [Sentence.realize_not] at this
      contradic

Depends on / 依赖: L.mem_completeTheory, Sentence, Sentence.realize_not, Set.mem_ofPred_eq, hT.realize_sentence, h_models, h_models.realize_sentence, h_realize, mem_completeTheory, mem_ofPred_eq, realize_not, realize_sentence
-/
theorem eq_complete_theory (h : T.IsComplete) (M : Type*) [L.Structure M] [M ⊨ T] [Nonempty M] :
    {φ | T ⊨ᵇ φ} = L.completeTheory M := by
  ext φ
  simp only [Set.mem_ofPred_eq, L.mem_completeTheory]
  refine ⟨fun h_models => h_models.realize_sentence M, fun h_realize => ?_⟩
  cases h.2 φ with
  | inl hT => exact hT
  | inr hT =>
      have : M ⊨ φ.not := hT.realize_sentence M
      rw [Sentence.realize_not] at this
      contradiction

/--
theorem `isComplete_iff_models_elementarily_equivalent` / 定理 `isComplete_iff_models_elementarily_equivalent`

English:
theorem isComplete_iff_models_elementarily_equivalent
  proof: by
  constructor
  · intro hcomp
    refine ⟨hcomp.1, ?_⟩
    intro M N
    rw [ElementarilyEquivalent]; rw [← hcomp.eq_complete_theory]; rw [← hcomp.eq_complete_theory]
  · rintro ⟨hsat, h⟩
    refine ⟨hsat, ?_⟩
    intro φ
    obtain ⟨M⟩ := hsat
    by_cases hφ : M ⊨ φ
    · left
      exact model

中文:
定理 isComplete_iff_models_elementarily_equivalent
  证明: by
  constructor
  · intro hcomp
    refine ⟨hcomp.1, ?_⟩
    intro M N
    rw [ElementarilyEquivalent]; rw [← hcomp.eq_complete_theory]; rw [← hcomp.eq_complete_theory]
  · rintro ⟨hsat, h⟩
    refine ⟨hsat, ?_⟩
    intro φ
    obtain ⟨M⟩ := hsat
    by_cases hφ : M ⊨ φ
    · left
      exact model

Depends on / 依赖: ElementarilyEquivalent, Sentence, Sentence.realize_not, elementarilyEquivalent_iff, eq_complete_theory, hcomp.eq_complete_theory, models_sentence_iff, realize_not
-/
theorem isComplete_iff_models_elementarily_equivalent :
    T.IsComplete ↔
    T.IsSatisfiable ∧ forall (M N : ModelType.{u, v, max u v} T), ElementarilyEquivalent L M N := by
  constructor
  · intro hcomp
    refine ⟨hcomp.1, ?_⟩
    intro M N
    rw [ElementarilyEquivalent]; rw [← hcomp.eq_complete_theory]; rw [← hcomp.eq_complete_theory]
  · rintro ⟨hsat, h⟩
    refine ⟨hsat, ?_⟩
    intro φ
    obtain ⟨M⟩ := hsat
    by_cases hφ : M ⊨ φ
    · left
      exact models_sentence_iff.2 fun N => (elementarilyEquivalent_iff.1 (h M N) φ).1 hφ
    · right
      exact models_sentence_iff.2 fun N => (Sentence.realize_not N).2
        (mt (elementarilyEquivalent_iff.1 (h M N) φ).2 hφ)

/--
theorem `models_elementarily_equivalent` / 定理 `models_elementarily_equivalent`

English:
theorem models_elementarily_equivalent
  proof: by
  rw [ElementarilyEquivalent]; rw [← h.eq_complete_theory]; rw [← h.eq_complete_theory]

中文:
定理 models_elementarily_equivalent
  证明: by
  rw [ElementarilyEquivalent]; rw [← h.eq_complete_theory]; rw [← h.eq_complete_theory]

Depends on / 依赖: ElementarilyEquivalent, eq_complete_theory, h.eq_complete_theory
-/
theorem models_elementarily_equivalent
    (h : T.IsComplete)
    (M N : Type*) [L.Structure M] [L.Structure N]
    [M ⊨ T] [N ⊨ T] [Nonempty M] [Nonempty N] :
    ElementarilyEquivalent L M N := by
  rw [ElementarilyEquivalent]; rw [← h.eq_complete_theory]; rw [← h.eq_complete_theory]

end IsComplete

/--
Definition of `IsMaximal` / `IsMaximal` 的定义

English:
definition IsMaximal
  signature: (T : L.Theory)
  body: T.IsSatisfiable ∧ forall φ : L.Sentence, φ in T ∨ φ.not in T

中文:
定义 IsMaximal
  签名: (T : L.Theory)
  定义体: T.IsSatisfiable ∧ forall φ : L.Sentence, φ in T ∨ φ.not in T

Depends on / 依赖: IsSatisfiable, L.Sentence, Sentence, T.IsSatisfiable
-/
def IsMaximal (T : L.Theory) : Prop :=
  T.IsSatisfiable ∧ forall φ : L.Sentence, φ in T ∨ φ.not in T

/--
theorem `IsMaximal.isComplete` / 定理 `IsMaximal.isComplete`

English:
theorem IsMaximal.isComplete
  given: (h : T.IsMaximal)
  statement: T.IsComplete
  proof: h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)

中文:
定理 IsMaximal.isComplete
  条件: (h : T.IsMaximal)
  结论: T.IsComplete
  证明: h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)

Depends on / 依赖: Or.imp, forall_imp, h.imp_right, imp_right, models_sentence_of_mem
-/
theorem IsMaximal.isComplete (h : T.IsMaximal) : T.IsComplete :=
  h.imp_right (forall_imp fun _ => Or.imp models_sentence_of_mem models_sentence_of_mem)

/--
theorem `IsMaximal.mem_or_not_mem` / 定理 `IsMaximal.mem_or_not_mem`

English:
theorem IsMaximal.mem_or_not_mem
  given: (h : T.IsMaximal) (φ : L.Sentence)
  statement: φ in T ∨ φ.not in T
  proof: h.2 φ

中文:
定理 IsMaximal.mem_or_not_mem
  条件: (h : T.IsMaximal) (φ : L.Sentence)
  结论: φ in T ∨ φ.not in T
  证明: h.2 φ
-/
theorem IsMaximal.mem_or_not_mem (h : T.IsMaximal) (φ : L.Sentence) : φ in T ∨ φ.not in T :=
  h.2 φ

/--
theorem `IsMaximal.mem_of_models` / 定理 `IsMaximal.mem_of_models`

English:
theorem IsMaximal.mem_of_models
  given: (h : T.IsMaximal) {φ : L.Sentence} (hφ : T ⊨ᵇ φ)
  statement: φ in T
  proof: by
  refine (h.mem_or_not_mem φ).resolve_right fun con => ?_
  rw [models_iff_not_satisfiable]; rw [Set.union_singleton]; rw [Set.insert_eq_of_mem con] at hφ
  exact hφ h.1

中文:
定理 IsMaximal.mem_of_models
  条件: (h : T.IsMaximal) {φ : L.Sentence} (hφ : T ⊨ᵇ φ)
  结论: φ in T
  证明: by
  refine (h.mem_or_not_mem φ).resolve_right fun con => ?_
  rw [models_iff_not_satisfiable]; rw [Set.union_singleton]; rw [Set.insert_eq_of_mem con] at hφ
  exact hφ h.1

Depends on / 依赖: Set.insert_eq_of_mem, Set.union_singleton, h.mem_or_not_mem, insert_eq_of_mem, mem_or_not_mem, models_iff_not_satisfiable, resolve_right, union_singleton
-/
theorem IsMaximal.mem_of_models (h : T.IsMaximal) {φ : L.Sentence} (hφ : T ⊨ᵇ φ) : φ in T := by
  refine (h.mem_or_not_mem φ).resolve_right fun con => ?_
  rw [models_iff_not_satisfiable]; rw [Set.union_singleton]; rw [Set.insert_eq_of_mem con] at hφ
  exact hφ h.1

/--
theorem `IsMaximal.mem_iff_models` / 定理 `IsMaximal.mem_iff_models`

English:
theorem IsMaximal.mem_iff_models
  given: (h : T.IsMaximal) (φ : L.Sentence)
  statement: φ in T ↔ T ⊨ᵇ φ
  proof: ⟨models_sentence_of_mem, h.mem_of_models⟩

中文:
定理 IsMaximal.mem_iff_models
  条件: (h : T.IsMaximal) (φ : L.Sentence)
  结论: φ in T ↔ T ⊨ᵇ φ
  证明: ⟨models_sentence_of_mem, h.mem_of_models⟩

Depends on / 依赖: h.mem_of_models, mem_of_models, models_sentence_of_mem
-/
theorem IsMaximal.mem_iff_models (h : T.IsMaximal) (φ : L.Sentence) : φ in T ↔ T ⊨ᵇ φ :=
  ⟨models_sentence_of_mem, h.mem_of_models⟩

end Theory

namespace completeTheory

variable (L) (M : Type w)
variable [L.Structure M]

/--
theorem `isSatisfiable` / 定理 `isSatisfiable`

English:
theorem isSatisfiable
  given: [Nonempty M]
  statement: (L.completeTheory M).IsSatisfiable
  proof: Theory.Model.isSatisfiable M

中文:
定理 isSatisfiable
  条件: [Nonempty M]
  结论: (L.completeTheory M).IsSatisfiable
  证明: Theory.Model.isSatisfiable M

Depends on / 依赖: Theory, Theory.Model.isSatisfiable, isSatisfiable
-/
theorem isSatisfiable [Nonempty M] : (L.completeTheory M).IsSatisfiable :=
  Theory.Model.isSatisfiable M

/--
theorem `mem_or_not_mem` / 定理 `mem_or_not_mem`

English:
theorem mem_or_not_mem
  given: (φ : L.Sentence)
  statement: φ in L.completeTheory M ∨ φ.not in L.completeTheory M
  proof: by
  simp_rw [completeTheory, Set.mem_ofPred_eq, Sentence.Realize, Formula.realize_not, or_not]

中文:
定理 mem_or_not_mem
  条件: (φ : L.Sentence)
  结论: φ in L.completeTheory M ∨ φ.not in L.completeTheory M
  证明: by
  simp_rw [completeTheory, Set.mem_ofPred_eq, Sentence.Realize, Formula.realize_not, or_not]

Depends on / 依赖: Formula, Formula.realize_not, Realize, Sentence, Sentence.Realize, Set.mem_ofPred_eq, completeTheory, mem_ofPred_eq, or_not, realize_not, simp_rw
-/
theorem mem_or_not_mem (φ : L.Sentence) : φ in L.completeTheory M ∨ φ.not in L.completeTheory M := by
  simp_rw [completeTheory, Set.mem_ofPred_eq, Sentence.Realize, Formula.realize_not, or_not]

/--
theorem `isMaximal` / 定理 `isMaximal`

English:
theorem isMaximal
  given: [Nonempty M]
  statement: (L.completeTheory M).IsMaximal
  proof: ⟨isSatisfiable L M, mem_or_not_mem L M⟩

中文:
定理 isMaximal
  条件: [Nonempty M]
  结论: (L.completeTheory M).IsMaximal
  证明: ⟨isSatisfiable L M, mem_or_not_mem L M⟩

Depends on / 依赖: isSatisfiable, mem_or_not_mem
-/
theorem isMaximal [Nonempty M] : (L.completeTheory M).IsMaximal :=
  ⟨isSatisfiable L M, mem_or_not_mem L M⟩

/--
theorem `isComplete` / 定理 `isComplete`

English:
theorem isComplete
  given: [Nonempty M]
  statement: (L.completeTheory M).IsComplete
  proof: (completeTheory.isMaximal L M).isComplete

中文:
定理 isComplete
  条件: [Nonempty M]
  结论: (L.completeTheory M).IsComplete
  证明: (completeTheory.isMaximal L M).isComplete

Depends on / 依赖: completeTheory, completeTheory.isMaximal, isComplete, isMaximal
-/
theorem isComplete [Nonempty M] : (L.completeTheory M).IsComplete :=
  (completeTheory.isMaximal L M).isComplete

end completeTheory

end Language

end FirstOrder

namespace Cardinal

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} (κ : Cardinal.{w}) (T : L.Theory)

/--
Definition of `Categorical` / `Categorical` 的定义

English:
definition Categorical
  signature: : Prop
  body: forall M N : T.ModelType, #M = κ -> #N = κ -> Nonempty (M ≃[L] N)

中文:
定义 Categorical
  签名: : 命题
  定义体: forall M N : T.ModelType, #M = κ -> #N = κ -> Nonempty (M ≃[L] N)

Depends on / 依赖: ModelType, Nonempty, T.ModelType
-/
def Categorical : Prop :=
  forall M N : T.ModelType, #M = κ -> #N = κ -> Nonempty (M ≃[L] N)

/--
theorem `Categorical.isComplete` / 定理 `Categorical.isComplete`

English:
theorem Categorical.isComplete
  statement: (h : κ.Categorical T) (h1 : ℵ₀ <= κ)
  proof: ⟨hS, fun φ => by
    obtain ⟨_, _⟩ := Theory.exists_model_card_eq ⟨hS.some, hT hS.some⟩ κ h1 h2
    rw [Theory.models_sentence_iff]; rw [Theory.models_sentence_iff]
    by_contra! ⟨⟨MF, hMF⟩, MT, hMT⟩
    rw [Sentence.realize_not]; rw [Classical.not_not] at hMT
    refine hMF ?_
    have := hT MT
  

中文:
定理 Categorical.isComplete
  结论: (h : κ.Categorical T) (h1 : ℵ₀ <= κ)
  证明: ⟨hS, fun φ => by
    obtain ⟨_, _⟩ := Theory.exists_model_card_eq ⟨hS.some, hT hS.some⟩ κ h1 h2
    rw [Theory.models_sentence_iff]; rw [Theory.models_sentence_iff]
    by_contra! ⟨⟨MF, hMF⟩, MT, hMT⟩
    rw [Sentence.realize_not]; rw [Classical.not_not] at hMT
    refine hMF ?_
    have := hT MT
  

Depends on / 依赖: Classical, Classical.not_not, MNF.toModel, MNT.toModel, Sentence, Sentence.realize_not, Theory, Theory.exists_model_card_eq, Theory.models_sentence_iff, exists_elementarilyEquivalent_card_eq, exists_model_card_eq, hS.some, models_sentence_iff, not_not, realize_not, toModel
-/
theorem Categorical.isComplete (h : κ.Categorical T) (h1 : ℵ₀ <= κ)
    (h2 : Cardinal.lift.{w} L.card <= Cardinal.lift.{max u v} κ) (hS : T.IsSatisfiable)
    (hT : forall M : Theory.ModelType.{u, v, max u v} T, Infinite M) : T.IsComplete :=
  ⟨hS, fun φ => by
    obtain ⟨_, _⟩ := Theory.exists_model_card_eq ⟨hS.some, hT hS.some⟩ κ h1 h2
    rw [Theory.models_sentence_iff]; rw [Theory.models_sentence_iff]
    by_contra! ⟨⟨MF, hMF⟩, MT, hMT⟩
    rw [Sentence.realize_not]; rw [Classical.not_not] at hMT
    refine hMF ?_
    have := hT MT
    have := hT MF
    obtain ⟨NT, MNT, hNT⟩ := exists_elementarilyEquivalent_card_eq L MT κ h1 h2
    obtain ⟨NF, MNF, hNF⟩ := exists_elementarilyEquivalent_card_eq L MF κ h1 h2
    obtain ⟨TF⟩ := h (MNT.toModel T) (MNF.toModel T) hNT hNF
    exact
      ((MNT.realize_sentence φ).trans
        ((StrongHomClass.realize_sentence TF φ).trans (MNF.realize_sentence φ).symm)).1 hMT⟩

/--
theorem `empty_theory_categorical` / 定理 `empty_theory_categorical`

English:
theorem empty_theory_categorical
  given: (T : Language.empty.Theory)
  statement: κ.Categorical T
  proof: fun M N hM hN =>
  by rw [empty.nonempty_equiv_iff, hM, hN]

中文:
定理 empty_theory_categorical
  条件: (T : Language.empty.Theory)
  结论: κ.Categorical T
  证明: fun M N hM hN =>
  by rw [empty.nonempty_equiv_iff, hM, hN]
-/
theorem empty_theory_categorical (T : Language.empty.Theory) : κ.Categorical T := fun M N hM hN =>
  by rw [empty.nonempty_equiv_iff, hM, hN]

/--
theorem `empty_infinite_Theory_isComplete` / 定理 `empty_infinite_Theory_isComplete`

English:
theorem empty_infinite_Theory_isComplete
  statement: Language.empty.infiniteTheory.IsComplete
  proof: (empty_theory_categorical.{0} ℵ₀ _).isComplete ℵ₀ _ le_rfl (by simp)
    ⟨by
      haveI : Language.empty.Structure Nat := emptyStructure
      exact ((model_infiniteTheory_iff Language.empty).2 (inferInstance : Infinite Nat)).bundled⟩
    fun M => (model_infiniteTheory_iff Language.empty).1 M.is_mo

中文:
定理 empty_infinite_Theory_isComplete
  结论: Language.empty.infiniteTheory.IsComplete
  证明: (empty_theory_categorical.{0} ℵ₀ _).isComplete ℵ₀ _ le_rfl (by simp)
    ⟨by
      haveI : Language.empty.Structure Nat := emptyStructure
      exact ((model_infiniteTheory_iff Language.empty).2 (inferInstance : Infinite Nat)).bundled⟩
    fun M => (model_infiniteTheory_iff Language.empty).1 M.is_mo

Depends on / 依赖: Infinite, Language, Language.empty, Language.empty.Structure, M.is_model, Structure, bundled, emptyStructure, empty_theory_categorical, isComplete, is_model, le_rfl, model_infiniteTheory_iff
-/
theorem empty_infinite_Theory_isComplete : Language.empty.infiniteTheory.IsComplete :=
  (empty_theory_categorical.{0} ℵ₀ _).isComplete ℵ₀ _ le_rfl (by simp)
    ⟨by
      haveI : Language.empty.Structure Nat := emptyStructure
      exact ((model_infiniteTheory_iff Language.empty).2 (inferInstance : Infinite Nat)).bundled⟩
    fun M => (model_infiniteTheory_iff Language.empty).1 M.is_model

end Cardinal
