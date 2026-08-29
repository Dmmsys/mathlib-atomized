/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Data.Rel

/-!
# Hall's Marriage Theorem

Given a list of finite subsets $X_1, X_2, \dots, X_n$ of some given set
$S$, P. Hall in [Hall1935] gave a necessary and sufficient condition for
there to be a list of distinct elements $x_1, x_2, \dots, x_n$ with
$x_i\in X_i$ for each $i$: it is when for each $k$, the union of every
$k$ of these subsets has at least $k$ elements.

Rather than a list of finite subsets, one may consider indexed families
`t : ι → Finset α` of finite subsets with `ι` a `Fintype`, and then the list
of distinct representatives is given by an injective function `f : ι → α`
such that `∀ i, f i ∈ t i`, called a *matching*.
This version is formalized as `Finset.all_card_le_biUnion_card_iff_exists_injective'`
in a separate module.

The theorem can be generalized to remove the constraint that `ι` be a `Fintype`.
As observed in [Halpern1966], one may use the constrained version of the theorem
in a compactness argument to remove this constraint.
The formulation of compactness we use is that inverse limits of nonempty finite sets
are nonempty (`nonempty_sections_of_finite_inverse_system`), which uses the
Tychonoff theorem.
The core of this module is constructing the inverse system: for every finite subset `ι'` of
`ι`, we can consider the matchings on the restriction of the indexed family `t` to `ι'`.

## Main statements

* `Finset.all_card_le_biUnion_card_iff_exists_injective` is in terms of `t : ι → Finset α`.
* `Fintype.all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `R.image {a}` is a finite set for all `a : α`.
* `Fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Tags

Hall's Marriage Theorem, indexed families
-/

@[expose] public section

open Finset Function CategoryTheory
open scoped SetRel

universe u v

/--
Definition of `hallMatchingsOn` / `hallMatchingsOn` 的定义

English:
definition hallMatchingsOn
  signature: {ι : Type u} {α : Type v} (t : ι -> Finset α) (ι' : Finset ι)
  body: { f : ι' -> α | Function.Injective f ∧ forall (x : {x // x in ι'}), f x in t x }

中文:
定义 hallMatchingsOn
  签名: {ι : 类型u} {α : 类型v} (t : ι -> 有限集 α) (ι' : 有限集 ι)
  定义体: { f : ι' -> α | Function.Injective f ∧ forall (x : {x // x in ι'}), f x in t x }

Depends on / 依赖: Function, Function.Injective, Injective
-/
def hallMatchingsOn {ι : Type u} {α : Type v} (t : ι -> Finset α) (ι' : Finset ι) :=
  { f : ι' -> α | Function.Injective f ∧ forall (x : {x // x in ι'}), f x in t x }

/--
Definition of `hallMatchingsOn.restrict` / `hallMatchingsOn.restrict` 的定义

English:
definition hallMatchingsOn.restrict
  signature: {ι : Type u} {α : Type v} (t : ι -> Finset α) {ι' ι'' : Finset ι}
  body: by
  refine ⟨fun i => f.val ⟨i, h i.property⟩, ?_⟩
  obtain ⟨hinj, hc⟩ := f.property
  refine ⟨?_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh

中文:
定义 hallMatchingsOn.restrict
  签名: {ι : 类型u} {α : 类型v} (t : ι -> 有限集 α) {ι' ι'' : 有限集 ι}
  定义体: by
  refine ⟨fun i => f.val ⟨i, h i.property⟩, ?_⟩
  obtain ⟨hinj, hc⟩ := f.property
  refine ⟨?_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, f.property, f.val, i.property, mk_eq_mk, property
-/
def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι -> Finset α) {ι' ι'' : Finset ι}
    (h : ι' subseteq ι'') (f : hallMatchingsOn t ι'') : hallMatchingsOn t ι' := by
  refine ⟨fun i => f.val ⟨i, h i.property⟩, ?_⟩
  obtain ⟨hinj, hc⟩ := f.property
  refine ⟨?_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh

/--
theorem `hallMatchingsOn.nonempty` / 定理 `hallMatchingsOn.nonempty`

English:
theorem hallMatchingsOn.nonempty
  statement: {ι : Type u} {α : Type v} [DecidableEq α] (t : ι -> Finset α)
  proof: by
  classical
    refine ⟨Classical.indefiniteDescription _ ?_⟩
    apply (all_card_le_biUnion_card_iff_existsInjective' fun i : ι' => t i).mp
    intro s'
    convert! h (s'.image (↑)) using 1
    · simp only [card_image_of_injective s' Subtype.coe_injective]
    · rw [image_biUnion]

中文:
定理 hallMatchingsOn.nonempty
  结论: {ι : 类型u} {α : 类型v} [DecidableEq α] (t : ι -> 有限集 α)
  证明: by
  classical
    refine ⟨Classical.indefiniteDescription _ ?_⟩
    apply (all_card_le_biUnion_card_iff_existsInjective' fun i : ι' => t i).mp
    intro s'
    convert! h (s'.image (↑)) using 1
    · simp only [card_image_of_injective s' Subtype.coe_injective]
    · rw [image_biUnion]

Depends on / 依赖: Classical, Classical.indefiniteDescription, Subtype, Subtype.coe_injective, all_card_le_biUnion_card_iff_existsInjective, card_image_of_injective, classical, coe_injective, convert, image_biUnion, indefiniteDescription
-/
theorem hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι -> Finset α)
    (h : forall s : Finset ι, #s <= #(s.biUnion t)) (ι' : Finset ι) :
    Nonempty (hallMatchingsOn t ι') := by
  classical
    refine ⟨Classical.indefiniteDescription _ ?_⟩
    apply (all_card_le_biUnion_card_iff_existsInjective' fun i : ι' => t i).mp
    intro s'
    convert! h (s'.image (↑)) using 1
    · simp only [card_image_of_injective s' Subtype.coe_injective]
    · rw [image_biUnion]

/--
Definition of `hallMatchingsFunctor` / `hallMatchingsFunctor` 的定义

English:
definition hallMatchingsFunctor
  signature: {ι : Type u} {α : Type v} (t : ι -> Finset α)
  body: hallMatchingsOn t ι'.unop
  map {_ _} g := ↾(hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop))

中文:
定义 hallMatchingsFunctor
  签名: {ι : 类型u} {α : 类型v} (t : ι -> 有限集 α)
  定义体: hallMatchingsOn t ι'.unop
  map {_ _} g := ↾(hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop))

Depends on / 依赖: hallMatchingsOn
-/
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι -> Finset α) :
    (Finset ι)ᵒᵖ ⥤ Type (max u v) where
  obj ι' := hallMatchingsOn t ι'.unop
  map {_ _} g := ↾(hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop))

/--
Instance `hallMatchingsOn.finite` / 实例 `hallMatchingsOn.finite`

English:
instance hallMatchingsOn.finite
  signature: {ι : Type u} {α : Type v} (t : ι -> Finset α) (ι' : Finset ι)
  body: by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' -> ι' -> ι'.biUnion t := by
      rintro f i
      refine ⟨f.val i, ?_⟩
      rw [mem_biUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    ext a
    rw [funext_iff] at h
    simpa [g] using h a

中文:
实例 hallMatchingsOn.finite
  签名: {ι : 类型u} {α : 类型v} (t : ι -> 有限集 α) (ι' : 有限集 ι)
  定义体: by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' -> ι' -> ι'.biUnion t := by
      rintro f i
      refine ⟨f.val i, ?_⟩
      rw [mem_biUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    ext a
    rw [funext_iff] at h
    simpa [g] using h a

Depends on / 依赖: Finite, Finite.of_injective, biUnion, classical, f.property, f.val, funext_iff, hallMatchingsOn, i.property, mem_biUnion, of_injective, property
-/
instance hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι -> Finset α) (ι' : Finset ι) :
    Finite (hallMatchingsOn t ι') := by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' -> ι' -> ι'.biUnion t := by
      rintro f i
      refine ⟨f.val i, ?_⟩
      rw [mem_biUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    ext a
    rw [funext_iff] at h
    simpa [g] using h a

/--
theorem `Finset.all_card_le_biUnion_card_iff_exists_injective` / 定理 `Finset.all_card_le_biUnion_card_iff_exists_injective`

English:
theorem Finset.all_card_le_biUnion_card_iff_exists_injective
  statement: {ι : Type u} {α : Type v}
  proof: by
  constructor
  · intro h
    -- Set up the functor
    have : forall ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
      have : forall ι' : (Finset ι)ᵒᵖ, Finite ((hallMatchingsFunctor t).obj ι') := by
        intro ι'
        rw [hallMatchingsFunctor]
        infer_instance
      -- Apply the compactness argument
      obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (hallMatchingsFunctor t)
      -- Interpret the resulting section of the inverse limit
      refine ⟨?_, ?_, ?_⟩
      · -- Build the matching function from the section
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [mem_singleton]⟩
      · -- Show that it is injective
        intro i i'
        have subi : ({i} : Finset ι) subseteq {i, i'} := by simp
        have subi' : ({i'} : Finset ι) subseteq {i, i'} := by simp
        simp only
        rw [← hu (CategoryTheory.homOfLE subi).op]; rw [← hu (CategoryTheory.homOfLE subi').op]
        let uii' := u (Opposite.op ({i, i'} : Finset ι))
        exact fun h => Subtype.mk_eq_mk.mp (uii'.property.1 h)
      · -- Show that it maps each index to the corresponding finite set
        intro i
        apply (u (Opposite.op ({i} : Finset ι))).property.2
  · -- The reverse direction is a straightforward cardinality argument
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_card
    grind

中文:
定理 有限集.all_card_le_biUnion_card_iff_存在_injective
  结论: {ι : 类型u} {α : 类型v}
  证明: by
  constructor
  · intro h
    -- Set up the functor
    have : forall ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
      have : forall ι' : (Finset ι)ᵒᵖ, Finite ((hallMatchingsFunctor t).obj ι') := by
        intro ι'
        rw [hallMatchingsFunctor]
        infer_instance
      -- Apply the compactness argument
      obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (hallMatchingsFunctor t)
      -- Interpret the resulting section of the inverse limit
      refine ⟨?_, ?_, ?_⟩
      · -- Build the matching function from the section
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [mem_singleton]⟩
      · -- Show that it is injective
        intro i i'
        have subi : ({i} : Finset ι) subseteq {i, i'} := by simp
        have subi' : ({i'} : Finset ι) subseteq {i, i'} := by simp
        simp only
        rw [← hu (CategoryTheory.homOfLE subi).op]; rw [← hu (CategoryTheory.homOfLE subi').op]
        let uii' := u (Opposite.op ({i, i'} : Finset ι))
        exact fun h => Subtype.mk_eq_mk.mp (uii'.property.1 h)
      · -- Show that it maps each index to the corresponding finite set
        intro i
        apply (u (Opposite.op ({i} : Finset ι))).property.2
  · -- The reverse direction is a straightforward cardinality argument
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_card
    grind
-/
theorem Finset.all_card_le_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v}
    [DecidableEq α] (t : ι -> Finset α) :
    (forall s : Finset ι, #s <= #(s.biUnion t)) ↔
      exists f : ι -> α, Function.Injective f ∧ forall x, f x in t x := by
  constructor
  · intro h
    -- Set up the functor
    have : forall ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
      have : forall ι' : (Finset ι)ᵒᵖ, Finite ((hallMatchingsFunctor t).obj ι') := by
        intro ι'
        rw [hallMatchingsFunctor]
        infer_instance
      -- Apply the compactness argument
      obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (hallMatchingsFunctor t)
      -- Interpret the resulting section of the inverse limit
      refine ⟨?_, ?_, ?_⟩
      · -- Build the matching function from the section
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [mem_singleton]⟩
      · -- Show that it is injective
        intro i i'
        have subi : ({i} : Finset ι) subseteq {i, i'} := by simp
        have subi' : ({i'} : Finset ι) subseteq {i, i'} := by simp
        simp only
        rw [← hu (CategoryTheory.homOfLE subi).op]; rw [← hu (CategoryTheory.homOfLE subi').op]
        let uii' := u (Opposite.op ({i, i'} : Finset ι))
        exact fun h => Subtype.mk_eq_mk.mp (uii'.property.1 h)
      · -- Show that it maps each index to the corresponding finite set
        intro i
        apply (u (Opposite.op ({i} : Finset ι))).property.2
  · -- The reverse direction is a straightforward cardinality argument
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_card
    grind

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α : Type u} {β : Type v} [DecidableEq β] (R : SetRel α β)
    [forall a : α, Fintype (R.image {a})] (A : Finset α) : Fintype (R.image A) := by
  have h : R.image A = (A.biUnion fun a => (R.image {a}).toFinset : Set β) := by
    ext
    simp [SetRel.image]
  rw [h]
  apply FinsetCoe.fintype

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Fintype.all_card_le_rel_image_card_iff_exists_injective` / 定理 `Fintype.all_card_le_rel_image_card_iff_exists_injective`

English:
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective
  statement: {α : Type u} {β : Type v}
  proof: by
  let r' a := (R.image {a}).toFinset
  have h : forall A : Finset α, Fintype.card (R.image A) = #(A.biUnion r') := by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [r', SetRel.image]
  have h' : forall (f : α -> β) (x), x ~[R] f x ↔ f x in r' x := by simp [r', SetRel.image]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective

中文:
定理 有限类型.all_card_le_rel_image_card_iff_存在_injective
  结论: {α : 类型u} {β : 类型v}
  证明: by
  let r' a := (R.image {a}).toFinset
  have h : forall A : Finset α, Fintype.card (R.image A) = #(A.biUnion r') := by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [r', SetRel.image]
  have h' : forall (f : α -> β) (x), x ~[R] f x ↔ f x in r' x := by simp [r', SetRel.image]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective

Depends on / 依赖: A.biUnion, Finset, Finset.all_card_le_biUnion_card_iff_exists_injective, Fintype, Fintype.card, R.image, Set.toFinset_card, SetRel, SetRel.image, all_card_le_biUnion_card_iff_exists_injective, biUnion, congr_arg, toFinset, toFinset_card
-/
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : Type v}
    [DecidableEq β] (R : SetRel α β) [forall a : α, Fintype (R.image {a})] :
    (forall A : Finset α, #A <= Fintype.card (R.image A)) ↔
      exists f : α -> β, Function.Injective f ∧ forall x, x ~[R] f x := by
  let r' a := (R.image {a}).toFinset
  have h : forall A : Finset α, Fintype.card (R.image A) = #(A.biUnion r') := by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [r', SetRel.image]
  have h' : forall (f : α -> β) (x), x ~[R] f x ↔ f x in r' x := by simp [r', SetRel.image]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective

/--
theorem `Fintype.all_card_le_filter_rel_iff_exists_injective` / 定理 `Fintype.all_card_le_filter_rel_iff_exists_injective`

English:
theorem Fintype.all_card_le_filter_rel_iff_exists_injective
  statement: {α : Type u} {β : Type v} [Fintype β]
  proof: by
  have := Classical.decEq β
  let r' a : Finset β := {b | r a b}
  have h : forall A : Finset α, ({b | exists a in A, r a b} : Finset _) = A.biUnion r' := by
    intro A
    ext b
    simp [r']
  have h' : forall (f : α -> β) (x), r x (f x) ↔ f x in r' x := by simp [r']
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective

中文:
定理 有限类型.all_card_le_filter_rel_iff_存在_injective
  结论: {α : 类型u} {β : 类型v} [有限类型 β]
  证明: by
  have := Classical.decEq β
  let r' a : Finset β := {b | r a b}
  have h : forall A : Finset α, ({b | exists a in A, r a b} : Finset _) = A.biUnion r' := by
    intro A
    ext b
    simp [r']
  have h' : forall (f : α -> β) (x), r x (f x) ↔ f x in r' x := by simp [r']
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective

Depends on / 依赖: A.biUnion, Classical, Classical.decEq, Finset, Finset.all_card_le_biUnion_card_iff_exists_injective, all_card_le_biUnion_card_iff_exists_injective, biUnion, simp_rw
-/
theorem Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type v} [Fintype β]
    (r : α -> β -> Prop) [DecidableRel r] :
    (forall A : Finset α, #A <= #{b | exists a in A, r a b}) ↔ exists f : α -> β, Injective f ∧ forall x, r x (f x) := by
  have := Classical.decEq β
  let r' a : Finset β := {b | r a b}
  have h : forall A : Finset α, ({b | exists a in A, r a b} : Finset _) = A.biUnion r' := by
    intro A
    ext b
    simp [r']
  have h' : forall (f : α -> β) (x), r x (f x) ↔ f x in r' x := by simp [r']
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
