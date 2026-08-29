/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Data.List.Triplewise

/-!
# Betweenness for lists of points.

This file defines notions of lists of points in an affine space being in order on a line.

## Main definitions

* `List.Wbtw R l`: The points in list `l` are weakly in order on a line.
* `List.Sbtw R l`: The points in list `l` are strictly in order on a line.

-/

@[expose] public section


variable (R : Type*) {V V' P P' : Type*}

open AffineEquiv AffineMap

namespace List

section OrderedRing

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

/--
Definition of `Wbtw` / `Wbtw` 的定义

English:
definition Wbtw
  signature: (l : List P)
  body: l.Triplewise (Wbtw R)

中文:
定义 Wbtw
  签名: (l : List P)
  定义体: l.Triplewise (Wbtw R)
-/
protected def Wbtw (l : List P) : Prop :=
  l.Triplewise (Wbtw R)

variable {R}

/--
lemma `wbtw_cons` / 引理 `wbtw_cons`

English:
lemma wbtw_cons
  given: {p : P} {l : List P}
  statement: (p :: l).Wbtw R ↔ l.Pairwise (Wbtw R p) ∧ l.Wbtw R
  proof: triplewise_cons

中文:
引理 wbtw_cons
  条件: {p : P} {l : List P}
  结论: (p :: l).Wbtw R ↔ l.Pairwise (Wbtw R p) ∧ l.Wbtw R
  证明: triplewise_cons

Depends on / 依赖: triplewise_cons
-/
lemma wbtw_cons {p : P} {l : List P} : (p :: l).Wbtw R ↔ l.Pairwise (Wbtw R p) ∧ l.Wbtw R :=
  triplewise_cons

variable (R)

/--
Definition of `Sbtw` / `Sbtw` 的定义

English:
definition Sbtw
  signature: (l : List P)
  body: l.Wbtw R ∧ l.Pairwise (· != ·)

中文:
定义 Sbtw
  签名: (l : List P)
  定义体: l.Wbtw R ∧ l.Pairwise (· != ·)
-/
protected def Sbtw (l : List P) : Prop :=
  l.Wbtw R ∧ l.Pairwise (· != ·)

variable (P)

/--
lemma `wbtw_nil` / 引理 `wbtw_nil`

English:
lemma wbtw_nil
  statement: ([] : List P).Wbtw R
  proof: by
  simp [List.Wbtw]

中文:
引理 wbtw_nil
  结论: ([] : List P).Wbtw R
  证明: by
  simp [List.Wbtw]
-/
@[simp] lemma wbtw_nil : ([] : List P).Wbtw R := by
  simp [List.Wbtw]

/--
lemma `sbtw_nil` / 引理 `sbtw_nil`

English:
lemma sbtw_nil
  statement: ([] : List P).Sbtw R
  proof: by
  simp [List.Sbtw]

中文:
引理 sbtw_nil
  结论: ([] : List P).Sbtw R
  证明: by
  simp [List.Sbtw]
-/
@[simp] lemma sbtw_nil : ([] : List P).Sbtw R := by
  simp [List.Sbtw]

variable {P}

/--
lemma `wbtw_singleton` / 引理 `wbtw_singleton`

English:
lemma wbtw_singleton
  given: (p₁ : P)
  statement: [p₁].Wbtw R
  proof: by
  simp [List.Wbtw]

中文:
引理 wbtw_singleton
  条件: (p₁ : P)
  结论: [p₁].Wbtw R
  证明: by
  simp [List.Wbtw]
-/
@[simp] lemma wbtw_singleton (p₁ : P) : [p₁].Wbtw R := by
  simp [List.Wbtw]

/--
lemma `sbtw_singleton` / 引理 `sbtw_singleton`

English:
lemma sbtw_singleton
  given: (p₁ : P)
  statement: [p₁].Sbtw R
  proof: by
  simp [List.Sbtw]

中文:
引理 sbtw_singleton
  条件: (p₁ : P)
  结论: [p₁].Sbtw R
  证明: by
  simp [List.Sbtw]
-/
@[simp] lemma sbtw_singleton (p₁ : P) : [p₁].Sbtw R := by
  simp [List.Sbtw]

/--
lemma `wbtw_pair` / 引理 `wbtw_pair`

English:
lemma wbtw_pair
  given: (p₁ p₂ : P)
  statement: [p₁, p₂].Wbtw R
  proof: by
  simp [List.Wbtw]

中文:
引理 wbtw_pair
  条件: (p₁ p₂ : P)
  结论: [p₁, p₂].Wbtw R
  证明: by
  simp [List.Wbtw]
-/
@[simp] lemma wbtw_pair (p₁ p₂ : P) : [p₁, p₂].Wbtw R := by
  simp [List.Wbtw]

/--
lemma `sbtw_pair` / 引理 `sbtw_pair`

English:
lemma sbtw_pair
  given: {p₁ p₂ : P}
  statement: [p₁, p₂].Sbtw R ↔ p₁ != p₂
  proof: by
  simp [List.Sbtw]

中文:
引理 sbtw_pair
  条件: {p₁ p₂ : P}
  结论: [p₁, p₂].Sbtw R ↔ p₁ != p₂
  证明: by
  simp [List.Sbtw]
-/
@[simp] lemma sbtw_pair {p₁ p₂ : P} : [p₁, p₂].Sbtw R ↔ p₁ != p₂ := by
  simp [List.Sbtw]

variable {R}

/--
lemma `wbtw_triple` / 引理 `wbtw_triple`

English:
lemma wbtw_triple
  given: {p₁ p₂ p₃ : P}
  statement: [p₁, p₂, p₃].Wbtw R ↔ Wbtw R p₁ p₂ p₃
  proof: by
  simp [List.Wbtw]

@[simp]

中文:
引理 wbtw_triple
  条件: {p₁ p₂ p₃ : P}
  结论: [p₁, p₂, p₃].Wbtw R ↔ Wbtw R p₁ p₂ p₃
  证明: by
  simp [List.Wbtw]

@[simp]
-/
@[simp] lemma wbtw_triple {p₁ p₂ p₃ : P} : [p₁, p₂, p₃].Wbtw R ↔ Wbtw R p₁ p₂ p₃ := by
  simp [List.Wbtw]

@[simp]
/--
lemma `sbtw_triple` / 引理 `sbtw_triple`

English:
lemma sbtw_triple
  given: [IsOrderedRing R] {p₁ p₂ p₃ : P}
  statement: [p₁, p₂, p₃].Sbtw R ↔ Sbtw R p₁ p₂ p₃
  proof: by
  simp only [List.Sbtw, wbtw_triple, ne_eq, pairwise_cons, mem_cons, not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, Pairwise.nil, and_self, and_true]
  exact ⟨fun ⟨hw, ⟨h₁₂, h₁₃⟩, h₂₃⟩ => ⟨hw, Ne.symm h₁₂, h₂₃⟩,
         fun h => ⟨h.1, ⟨h.2.1.symm, h.lef

中文:
引理 sbtw_triple
  条件: [IsOrderedRing R] {p₁ p₂ p₃ : P}
  结论: [p₁, p₂, p₃].Sbtw R ↔ Sbtw R p₁ p₂ p₃
  证明: by
  simp only [List.Sbtw, wbtw_triple, ne_eq, pairwise_cons, mem_cons, not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, Pairwise.nil, and_self, and_true]
  exact ⟨fun ⟨hw, ⟨h₁₂, h₁₃⟩, h₂₃⟩ => ⟨hw, Ne.symm h₁₂, h₂₃⟩,
         fun h => ⟨h.1, ⟨h.2.1.symm, h.lef

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, List.Sbtw, Ne.symm, Pairwise, Pairwise.nil, and_self, and_true, forall_eq, forall_eq_or_imp, forall_iff, h.left_ne_right, implies_true, left_ne_right, mem_cons, ne_eq, not_mem_nil, or_false, pairwise_cons, wbtw_triple
-/
lemma sbtw_triple [IsOrderedRing R] {p₁ p₂ p₃ : P} : [p₁, p₂, p₃].Sbtw R ↔ Sbtw R p₁ p₂ p₃ := by
  simp only [List.Sbtw, wbtw_triple, ne_eq, pairwise_cons, mem_cons, not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, Pairwise.nil, and_self, and_true]
  exact ⟨fun ⟨hw, ⟨h₁₂, h₁₃⟩, h₂₃⟩ => ⟨hw, Ne.symm h₁₂, h₂₃⟩,
         fun h => ⟨h.1, ⟨h.2.1.symm, h.left_ne_right⟩, h.2.2⟩⟩

/--
lemma `wbtw_four` / 引理 `wbtw_four`

English:
lemma wbtw_four
  given: {p₁ p₂ p₃ p₄ : P}
  statement: [p₁, p₂, p₃, p₄].Wbtw R ↔
  proof: by
  simp [List.Wbtw, triplewise_cons, and_assoc]

中文:
引理 wbtw_four
  条件: {p₁ p₂ p₃ p₄ : P}
  结论: [p₁, p₂, p₃, p₄].Wbtw R ↔
  证明: by
  simp [List.Wbtw, triplewise_cons, and_assoc]

Depends on / 依赖: List.Wbtw, and_assoc, triplewise_cons
-/
lemma wbtw_four {p₁ p₂ p₃ p₄ : P} : [p₁, p₂, p₃, p₄].Wbtw R ↔
    Wbtw R p₁ p₂ p₃ ∧ Wbtw R p₁ p₂ p₄ ∧ Wbtw R p₁ p₃ p₄ ∧ Wbtw R p₂ p₃ p₄ := by
  simp [List.Wbtw, triplewise_cons, and_assoc]

/--
lemma `sbtw_four` / 引理 `sbtw_four`

English:
lemma sbtw_four
  given: [IsOrderedRing R] {p₁ p₂ p₃ p₄ : P}
  statement: [p₁, p₂, p₃, p₄].Sbtw R ↔
  proof: by
  simp [List.Sbtw, List.Wbtw, triplewise_cons, Sbtw]
  aesop

中文:
引理 sbtw_four
  条件: [IsOrderedRing R] {p₁ p₂ p₃ p₄ : P}
  结论: [p₁, p₂, p₃, p₄].Sbtw R ↔
  证明: by
  simp [List.Sbtw, List.Wbtw, triplewise_cons, Sbtw]
  aesop

Depends on / 依赖: List.Sbtw, List.Wbtw, triplewise_cons
-/
lemma sbtw_four [IsOrderedRing R] {p₁ p₂ p₃ p₄ : P} : [p₁, p₂, p₃, p₄].Sbtw R ↔
    Sbtw R p₁ p₂ p₃ ∧ Sbtw R p₁ p₂ p₄ ∧ Sbtw R p₁ p₃ p₄ ∧ Sbtw R p₂ p₃ p₄ := by
  simp [List.Sbtw, List.Wbtw, triplewise_cons, Sbtw]
  aesop

/--
lemma `Sbtw.wbtw` / 引理 `Sbtw.wbtw`

English:
lemma Sbtw.wbtw
  given: {l : List P} (h : l.Sbtw R)
  statement: l.Wbtw R
  proof: h.1

中文:
引理 Sbtw.wbtw
  条件: {l : List P} (h : l.Sbtw R)
  结论: l.Wbtw R
  证明: h.1
-/
protected lemma Sbtw.wbtw {l : List P} (h : l.Sbtw R) : l.Wbtw R :=
  h.1

/--
lemma `Sbtw.pairwise_ne` / 引理 `Sbtw.pairwise_ne`

English:
lemma Sbtw.pairwise_ne
  given: {l : List P} (h : l.Sbtw R)
  statement: l.Pairwise (· != ·)
  proof: h.2

中文:
引理 Sbtw.pairwise_ne
  条件: {l : List P} (h : l.Sbtw R)
  结论: l.Pairwise (· != ·)
  证明: h.2
-/
lemma Sbtw.pairwise_ne {l : List P} (h : l.Sbtw R) : l.Pairwise (· != ·) :=
  h.2

/--
lemma `sbtw_iff_triplewise_and_ne_pair` / 引理 `sbtw_iff_triplewise_and_ne_pair`

English:
lemma sbtw_iff_triplewise_and_ne_pair
  given: [IsOrderedRing R] {l : List P}
  proof: by
  rw [List.Sbtw]
  induction l with
  | nil => simp
  | cons head tail ih =>
    rw [wbtw_cons]; rw [triplewise_cons]
    refine ⟨fun h => ?_,
            fun ⟨⟨hp, ht⟩, ha⟩ => ⟨⟨hp.imp _root_.Sbtw.wbtw, ht.imp _root_.Sbtw.wbtw⟩, ?_⟩⟩
    · rcases h with ⟨⟨hp, ht⟩, hpne⟩
      refine ⟨⟨?_, ?_⟩, ?

中文:
引理 sbtw_iff_triplewise_and_ne_pair
  条件: [IsOrderedRing R] {l : List P}
  证明: by
  rw [List.Sbtw]
  induction l with
  | nil => simp
  | cons head tail ih =>
    rw [wbtw_cons]; rw [triplewise_cons]
    refine ⟨fun h => ?_,
            fun ⟨⟨hp, ht⟩, ha⟩ => ⟨⟨hp.imp _root_.Sbtw.wbtw, ht.imp _root_.Sbtw.wbtw⟩, ?_⟩⟩
    · rcases h with ⟨⟨hp, ht⟩, hpne⟩
      refine ⟨⟨?_, ?_⟩, ?

Depends on / 依赖: List.Sbtw, _root_, _root_.Sbtw.wbtw, hp.imp, ht.imp, pairwise_cons, triplewise_cons, wbtw_cons
-/
lemma sbtw_iff_triplewise_and_ne_pair [IsOrderedRing R] {l : List P} :
    l.Sbtw R ↔ l.Triplewise (Sbtw R) ∧ forall a, l != [a, a] := by
  rw [List.Sbtw]
  induction l with
  | nil => simp
  | cons head tail ih =>
    rw [wbtw_cons]; rw [triplewise_cons]
    refine ⟨fun h => ?_,
            fun ⟨⟨hp, ht⟩, ha⟩ => ⟨⟨hp.imp _root_.Sbtw.wbtw, ht.imp _root_.Sbtw.wbtw⟩, ?_⟩⟩
    · rcases h with ⟨⟨hp, ht⟩, hpne⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · clear ih
        induction tail with
        | nil => simp
        | cons head2 tail ih' =>
          rw [pairwise_cons] at hp hpne hpne ⊢
          refine ⟨fun a ha => ⟨hp.1 a ha, ?_⟩, ?_⟩
          · refine ⟨(hpne.1 head2 ?_).symm, hpne.2.1 a ha⟩
            simp
          · rw [wbtw_cons] at ht
            grind [List.pairwise_iff_forall_sublist]
      · rw [pairwise_cons] at hpne
        exact (ih.1 ⟨ht, hpne.2⟩).1
      · grind
    · have ht' : tail.Wbtw R := ht.imp _root_.Sbtw.wbtw
      simp only [ht', true_and, ht] at ih
      rw [pairwise_cons]; rw [ih]
      refine ⟨fun a ha' => ?_, fun a => ?_⟩
      · rintro rfl
        cases tail with
        | nil => simp at ha'
        | cons head2 tail =>
          rw [pairwise_cons] at hp
          rcases mem_cons.1 ha' with rfl | hat
          · cases tail with
            | nil => simp at ha
            | cons head3 tail => simpa using hp.1 head3
          · simpa using hp.1 head hat
      · rintro rfl
        simp at hp

/--
lemma `sbtw_cons` / 引理 `sbtw_cons`

English:
lemma sbtw_cons
  given: [IsOrderedRing R] {p : P} {l : List P}
  proof: by
  rw [sbtw_iff_triplewise_and_ne_pair]; rw [← not_exists]; rw [triplewise_cons]
  simp only [cons.injEq, exists_eq_left', and_assoc, and_congr_right_iff, ne_eq, and_congr_left_iff]
  intro hp hne
  rw [sbtw_iff_triplewise_and_ne_pair]; rw [iff_self_and]; rw [← not_exists]
  rintro hl ⟨a, rfl⟩
  s

中文:
引理 sbtw_cons
  条件: [IsOrderedRing R] {p : P} {l : List P}
  证明: by
  rw [sbtw_iff_triplewise_and_ne_pair]; rw [← not_exists]; rw [triplewise_cons]
  simp only [cons.injEq, exists_eq_left', and_assoc, and_congr_right_iff, ne_eq, and_congr_left_iff]
  intro hp hne
  rw [sbtw_iff_triplewise_and_ne_pair]; rw [iff_self_and]; rw [← not_exists]
  rintro hl ⟨a, rfl⟩
  s

Depends on / 依赖: and_assoc, and_congr_left_iff, and_congr_right_iff, cons.injEq, exists_eq_left, iff_self_and, ne_eq, not_exists, sbtw_iff_triplewise_and_ne_pair, triplewise_cons
-/
lemma sbtw_cons [IsOrderedRing R] {p : P} {l : List P} :
    (p :: l).Sbtw R ↔ l.Pairwise (Sbtw R p) ∧ l.Sbtw R ∧ l != [p] := by
  rw [sbtw_iff_triplewise_and_ne_pair]; rw [← not_exists]; rw [triplewise_cons]
  simp only [cons.injEq, exists_eq_left', and_assoc, and_congr_right_iff, ne_eq, and_congr_left_iff]
  intro hp hne
  rw [sbtw_iff_triplewise_and_ne_pair]; rw [iff_self_and]; rw [← not_exists]
  rintro hl ⟨a, rfl⟩
  simp at hp

protected nonrec lemma Wbtw.map {l : List P} (h : l.Wbtw R) (f : P ->ᵃ[R] P') : (l.map f).Wbtw R :=
  Triplewise.map (fun h => Wbtw.map h f) h

/--
lemma `_root_.Function.Injective.list_wbtw_map_iff` / 引理 `_root_.Function.Injective.list_wbtw_map_iff`

English:
lemma _root_.Function.Injective.list_wbtw_map_iff
  statement: {l : List P} {f : P ->ᵃ[R] P'}
  proof: ⟨fun h => h.of_map hf.wbtw_map_iff.1, fun h => h.map f⟩

中文:
引理 _root_.Function.Injective.list_wbtw_map_iff
  结论: {l : List P} {f : P ->ᵃ[R] P'}
  证明: ⟨fun h => h.of_map hf.wbtw_map_iff.1, fun h => h.map f⟩

Depends on / 依赖: h.map, h.of_map, hf.wbtw_map_iff, of_map, wbtw_map_iff
-/
lemma _root_.Function.Injective.list_wbtw_map_iff {l : List P} {f : P ->ᵃ[R] P'}
    (hf : Function.Injective f) : (l.map f).Wbtw R ↔ l.Wbtw R :=
  ⟨fun h => h.of_map hf.wbtw_map_iff.1, fun h => h.map f⟩

/--
lemma `_root_.Function.Injective.list_sbtw_map_iff` / 引理 `_root_.Function.Injective.list_sbtw_map_iff`

English:
lemma _root_.Function.Injective.list_sbtw_map_iff
  statement: {l : List P} {f : P ->ᵃ[R] P'}
  proof: by
  rw [List.Sbtw]; rw [List.Sbtw]; rw [hf.list_wbtw_map_iff]
  refine ⟨fun ⟨hl, hp⟩ => ⟨hl, hp.of_map _ ?_⟩, fun ⟨hl, hp⟩ => ⟨hl, hp.map _ ?_⟩⟩ <;>
    simp [hf.ne_iff]

中文:
引理 _root_.Function.Injective.list_sbtw_map_iff
  结论: {l : List P} {f : P ->ᵃ[R] P'}
  证明: by
  rw [List.Sbtw]; rw [List.Sbtw]; rw [hf.list_wbtw_map_iff]
  refine ⟨fun ⟨hl, hp⟩ => ⟨hl, hp.of_map _ ?_⟩, fun ⟨hl, hp⟩ => ⟨hl, hp.map _ ?_⟩⟩ <;>
    simp [hf.ne_iff]

Depends on / 依赖: List.Sbtw, hf.list_wbtw_map_iff, hf.ne_iff, hp.map, hp.of_map, list_wbtw_map_iff, ne_iff, of_map
-/
lemma _root_.Function.Injective.list_sbtw_map_iff {l : List P} {f : P ->ᵃ[R] P'}
    (hf : Function.Injective f) : (l.map f).Sbtw R ↔ l.Sbtw R := by
  rw [List.Sbtw]; rw [List.Sbtw]; rw [hf.list_wbtw_map_iff]
  refine ⟨fun ⟨hl, hp⟩ => ⟨hl, hp.of_map _ ?_⟩, fun ⟨hl, hp⟩ => ⟨hl, hp.map _ ?_⟩⟩ <;>
    simp [hf.ne_iff]

/--
lemma `_root_.AffineEquiv.list_wbtw_map_iff` / 引理 `_root_.AffineEquiv.list_wbtw_map_iff`

English:
lemma _root_.AffineEquiv.list_wbtw_map_iff
  given: {l : List P} (f : P ≃ᵃ[R] P')
  proof: by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_wbtw_map_iff

中文:
引理 _root_.AffineEquiv.list_wbtw_map_iff
  条件: {l : List P} (f : P ≃ᵃ[R] P')
  证明: by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_wbtw_map_iff

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, hf.list_wbtw_map_iff, injective, list_wbtw_map_iff, toAffineMap
-/
lemma _root_.AffineEquiv.list_wbtw_map_iff {l : List P} (f : P ≃ᵃ[R] P') :
    (l.map f).Wbtw R ↔ l.Wbtw R := by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_wbtw_map_iff

/--
lemma `_root_.AffineEquiv.list_sbtw_map_iff` / 引理 `_root_.AffineEquiv.list_sbtw_map_iff`

English:
lemma _root_.AffineEquiv.list_sbtw_map_iff
  given: {l : List P} (f : P ≃ᵃ[R] P')
  proof: by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_sbtw_map_iff

中文:
引理 _root_.AffineEquiv.list_sbtw_map_iff
  条件: {l : List P} (f : P ≃ᵃ[R] P')
  证明: by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_sbtw_map_iff

Depends on / 依赖: Function, Function.Injective, Injective, f.injective, f.toAffineMap, hf.list_sbtw_map_iff, injective, list_sbtw_map_iff, toAffineMap
-/
lemma _root_.AffineEquiv.list_sbtw_map_iff {l : List P} (f : P ≃ᵃ[R] P') :
    (l.map f).Sbtw R ↔ l.Sbtw R := by
  have hf : Function.Injective f.toAffineMap := f.injective
  apply hf.list_sbtw_map_iff

end OrderedRing

section LinearOrderedField

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [AddTorsor V P] {x y z : P}
variable {R}

/--
lemma `SortedLE.wbtw` / 引理 `SortedLE.wbtw`

English:
lemma SortedLE.wbtw
  given: {l : List R} (h : l.SortedLE)
  statement: l.Wbtw R
  proof: by
  rw [List.Wbtw]; rw [List.triplewise_iff_getElem]
  intro i j k hij hjk hk
  exact Wbtw.of_le_of_le (h.getElem_le_getElem_of_le hij.le) (h.getElem_le_getElem_of_le hjk.le)

中文:
引理 SortedLE.wbtw
  条件: {l : List R} (h : l.SortedLE)
  结论: l.Wbtw R
  证明: by
  rw [List.Wbtw]; rw [List.triplewise_iff_getElem]
  intro i j k hij hjk hk
  exact Wbtw.of_le_of_le (h.getElem_le_getElem_of_le hij.le) (h.getElem_le_getElem_of_le hjk.le)

Depends on / 依赖: List.Wbtw, List.triplewise_iff_getElem, Wbtw.of_le_of_le, getElem_le_getElem_of_le, h.getElem_le_getElem_of_le, hij.le, hjk.le, of_le_of_le, triplewise_iff_getElem
-/
lemma SortedLE.wbtw {l : List R} (h : l.SortedLE) : l.Wbtw R := by
  rw [List.Wbtw]; rw [List.triplewise_iff_getElem]
  intro i j k hij hjk hk
  exact Wbtw.of_le_of_le (h.getElem_le_getElem_of_le hij.le) (h.getElem_le_getElem_of_le hjk.le)

/--
lemma `SortedLT.sbtw` / 引理 `SortedLT.sbtw`

English:
lemma SortedLT.sbtw
  given: {l : List R} (h : l.SortedLT)
  statement: l.Sbtw R
  proof: ⟨h.sortedLE.wbtw, h.nodup⟩

中文:
引理 SortedLT.sbtw
  条件: {l : List R} (h : l.SortedLT)
  结论: l.Sbtw R
  证明: ⟨h.sortedLE.wbtw, h.nodup⟩

Depends on / 依赖: h.nodup, h.sortedLE.wbtw, sortedLE
-/
lemma SortedLT.sbtw {l : List R} (h : l.SortedLT) : l.Sbtw R :=
  ⟨h.sortedLE.wbtw, h.nodup⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_map_eq_of_sorted_nonempty_iff_wbtw` / 引理 `exists_map_eq_of_sorted_nonempty_iff_wbtw`

English:
lemma exists_map_eq_of_sorted_nonempty_iff_wbtw
  given: {l : List P} (hl : l != [])
  proof: by
  refine ⟨fun ⟨l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · rw [← hl'l]
    exact Wbtw.map hl's.wbtw _
  · suffices exists l' : List R, (forall a in l', 0 <= a) ∧ l'.SortedLE ∧
        l'.map (lineMap (l.head hl) (l.getLast hl)) = l by
      rcases this with ⟨l', -, hl'⟩
      exact ⟨l', hl'⟩
    indu

中文:
引理 exists_map_eq_of_sorted_nonempty_iff_wbtw
  条件: {l : List P} (hl : l != [])
  证明: by
  refine ⟨fun ⟨l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · rw [← hl'l]
    exact Wbtw.map hl's.wbtw _
  · suffices exists l' : List R, (forall a in l', 0 <= a) ∧ l'.SortedLE ∧
        l'.map (lineMap (l.head hl) (l.getLast hl)) = l by
      rcases this with ⟨l', -, hl'⟩
      exact ⟨l', hl'⟩
    indu

Depends on / 依赖: SortedLE, Wbtw.map, getLast, l.getLast, l.head, lineMap, replace, s.wbtw, sortedLE_iff_pairwise, wbtw_cons
-/
lemma exists_map_eq_of_sorted_nonempty_iff_wbtw {l : List P} (hl : l != []) :
    (exists l' : List R, l'.SortedLE ∧ l'.map (lineMap (l.head hl) (l.getLast hl)) = l) ↔
      l.Wbtw R := by
  refine ⟨fun ⟨l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · rw [← hl'l]
    exact Wbtw.map hl's.wbtw _
  · suffices exists l' : List R, (forall a in l', 0 <= a) ∧ l'.SortedLE ∧
        l'.map (lineMap (l.head hl) (l.getLast hl)) = l by
      rcases this with ⟨l', -, hl'⟩
      exact ⟨l', hl'⟩
    induction l with
    | nil => simp at hl
    | cons head tail ih =>
      by_cases ht : tail = []
      · refine ⟨[0], ?_⟩
        simp [ht, sortedLE_iff_pairwise]
      · rw [wbtw_cons] at h
        replace ih := ih ht h.2
        rcases ih with ⟨l'', hl''0, hl''s, hl''⟩
        simp only [head_cons, getLast_cons ht]
        cases tail with
        | nil => simp at ht
        | cons head2 tail =>
          by_cases ht2 : tail = []
          · exact ⟨[0, 1], by simp [ht2, sortedLE_iff_pairwise]⟩
          · simp only [head_cons, getLast_cons ht2] at hl'' ⊢
            rw [pairwise_cons] at h
            have hw := h.1.1 _ (getLast_mem ht2)
            rcases hw with ⟨r, ⟨hr0, hr1⟩, rfl⟩
            refine ⟨0 :: l''.map fun x => r + (1 - r) * x, ?_, ?_, ?_⟩
            · simp only [mem_cons, mem_map, forall_eq_or_imp, le_refl, forall_exists_index,
                and_imp, forall_apply_eq_imp_iff₂, true_and]
              intro a ha
              have := hl''0 a ha
              nlinarith
            · simp only [sortedLE_iff_pairwise, pairwise_cons, mem_map,
                forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
              refine ⟨?_, ?_⟩
              · intro a ha
                have := hl''0 a ha
                nlinarith
              · refine hl''s.pairwise.map _ fun a b hab => ?_
                gcongr
            · simp only [map_cons, lineMap_apply_zero, map_map, ← hl'', cons.injEq,
                map_inj_left, Function.comp_apply, lineMap_lineMap_left, lineMap_eq_lineMap_iff,
                true_and]
              ring_nf
              simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_map_eq_of_sorted_iff_wbtw` / 引理 `exists_map_eq_of_sorted_iff_wbtw`

English:
lemma exists_map_eq_of_sorted_iff_wbtw
  given: {l : List P}
  proof: by
  refine ⟨fun ⟨p₁, p₂, l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · subst hl'l
    exact Wbtw.map hl's.wbtw _
  · by_cases hl : l = []
    · exact ⟨AddTorsor.nonempty.some, AddTorsor.nonempty.some, [], by
        simp [hl, sortedLE_iff_pairwise]⟩
    · exact ⟨l.head hl, l.getLast hl, (exists_map_eq_of

中文:
引理 exists_map_eq_of_sorted_iff_wbtw
  条件: {l : List P}
  证明: by
  refine ⟨fun ⟨p₁, p₂, l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · subst hl'l
    exact Wbtw.map hl's.wbtw _
  · by_cases hl : l = []
    · exact ⟨AddTorsor.nonempty.some, AddTorsor.nonempty.some, [], by
        simp [hl, sortedLE_iff_pairwise]⟩
    · exact ⟨l.head hl, l.getLast hl, (exists_map_eq_of

Depends on / 依赖: AddTorsor, AddTorsor.nonempty.some, Wbtw.map, exists_map_eq_of_sorted_nonempty_iff_wbtw, getLast, l.getLast, l.head, nonempty, s.wbtw, sortedLE_iff_pairwise
-/
lemma exists_map_eq_of_sorted_iff_wbtw {l : List P} :
    (exists p₁ p₂ : P, exists l' : List R, l'.SortedLE ∧ l'.map (lineMap p₁ p₂) = l) ↔ l.Wbtw R := by
  refine ⟨fun ⟨p₁, p₂, l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · subst hl'l
    exact Wbtw.map hl's.wbtw _
  · by_cases hl : l = []
    · exact ⟨AddTorsor.nonempty.some, AddTorsor.nonempty.some, [], by
        simp [hl, sortedLE_iff_pairwise]⟩
    · exact ⟨l.head hl, l.getLast hl, (exists_map_eq_of_sorted_nonempty_iff_wbtw hl).2 h⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_map_eq_of_sorted_nonempty_iff_sbtw` / 引理 `exists_map_eq_of_sorted_nonempty_iff_sbtw`

English:
lemma exists_map_eq_of_sorted_nonempty_iff_sbtw
  given: {l : List P} (hl : l != [])
  proof: by
  refine ⟨fun ⟨l', hl's, hl'l, hla⟩ =>
            ⟨(exists_map_eq_of_sorted_nonempty_iff_wbtw hl).1
            ⟨l', (hl's.pairwise.imp LT.lt.le).sortedLE, hl'l⟩, ?_⟩,
          fun h => ?_⟩
  · rw [← hl'l]
    rcases hla with hla | hla
    · grind [List.pairwise_iff_forall_sublist]
    · exact 

中文:
引理 exists_map_eq_of_sorted_nonempty_iff_sbtw
  条件: {l : List P} (hl : l != [])
  证明: by
  refine ⟨fun ⟨l', hl's, hl'l, hla⟩ =>
            ⟨(exists_map_eq_of_sorted_nonempty_iff_wbtw hl).1
            ⟨l', (hl's.pairwise.imp LT.lt.le).sortedLE, hl'l⟩, ?_⟩,
          fun h => ?_⟩
  · rw [← hl'l]
    rcases hla with hla | hla
    · grind [List.pairwise_iff_forall_sublist]
    · exact 

Depends on / 依赖: LT.lt.le, LT.lt.ne, List.Sbtw, List.pairwise_iff_forall_sublist, Pairwise, exists_map_eq_of_sorted_nonempty_iff_wbtw, lineMap_injective, pairwise, pairwise_iff_forall_sublist, s.pairwise.imp, sortedLE
-/
lemma exists_map_eq_of_sorted_nonempty_iff_sbtw {l : List P} (hl : l != []) :
    (exists l' : List R, l'.SortedLT ∧ l'.map (lineMap (l.head hl) (l.getLast hl)) = l ∧
      (l.length = 1 ∨ l.head hl != l.getLast hl)) ↔ l.Sbtw R := by
  refine ⟨fun ⟨l', hl's, hl'l, hla⟩ =>
            ⟨(exists_map_eq_of_sorted_nonempty_iff_wbtw hl).1
            ⟨l', (hl's.pairwise.imp LT.lt.le).sortedLE, hl'l⟩, ?_⟩,
          fun h => ?_⟩
  · rw [← hl'l]
    rcases hla with hla | hla
    · grind [List.pairwise_iff_forall_sublist]
    · exact (hl's.pairwise.imp LT.lt.ne).map _ fun _ _ => (lineMap_injective _ hla).ne
  · rw [List.Sbtw, ← exists_map_eq_of_sorted_nonempty_iff_wbtw hl] at h
    rcases h with ⟨⟨l', hl's, hl'l⟩, hp⟩
    refine ⟨l', ?_, hl'l, ?_⟩
    · rw [← hl'l] at hp
      have hp' : l'.Pairwise (· != ·) := hp.of_map _ (by simp)
      exact ((pairwise_and_iff.2 ⟨hl's.pairwise, hp'⟩).imp lt_iff_le_and_ne.2).sortedLT
    · cases l with
      | nil => simp at hl
      | cons head tail =>
        simp only [length_cons, add_eq_right, length_eq_zero_iff, head_cons]
        cases tail with
        | nil => simp
        | cons head2 tail =>
          simp only [reduceCtorEq, false_or]
          rw [pairwise_cons] at hp
          refine hp.1 ((head :: head2 :: tail).getLast hl) ?_
          simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_map_eq_of_sorted_iff_sbtw` / 引理 `exists_map_eq_of_sorted_iff_sbtw`

English:
lemma exists_map_eq_of_sorted_iff_sbtw
  given: [Nontrivial P] {l : List P}
  proof: by
  refine ⟨fun ⟨p₁, p₂, hp₁p₂, l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · subst hl'l
    rw [(lineMap_injective _ hp₁p₂).list_sbtw_map_iff]
    exact hl's.sbtw
  · by_cases hl : l = []
    · rcases exists_pair_ne P with ⟨p₁, p₂, hp₁p₂⟩
      exact ⟨p₁, p₂, hp₁p₂, by simp [hl, sortedLT_iff_pairwise]⟩


中文:
引理 exists_map_eq_of_sorted_iff_sbtw
  条件: [Nontrivial P] {l : List P}
  证明: by
  refine ⟨fun ⟨p₁, p₂, hp₁p₂, l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · subst hl'l
    rw [(lineMap_injective _ hp₁p₂).list_sbtw_map_iff]
    exact hl's.sbtw
  · by_cases hl : l = []
    · rcases exists_pair_ne P with ⟨p₁, p₂, hp₁p₂⟩
      exact ⟨p₁, p₂, hp₁p₂, by simp [hl, sortedLT_iff_pairwise]⟩


Depends on / 依赖: exists_ne, exists_pair_ne, getLast, l.getLast, l.head, l.length, length, length_eq_one_iff, lineMap_injective, list_sbtw_map_iff, s.sbtw, sortedLT_iff_pairwise
-/
lemma exists_map_eq_of_sorted_iff_sbtw [Nontrivial P] {l : List P} :
    (exists p₁ p₂ : P, p₁ != p₂ ∧ exists l' : List R, l'.SortedLT ∧ l'.map (lineMap p₁ p₂) = l) ↔
      l.Sbtw R := by
  refine ⟨fun ⟨p₁, p₂, hp₁p₂, l', hl's, hl'l⟩ => ?_, fun h => ?_⟩
  · subst hl'l
    rw [(lineMap_injective _ hp₁p₂).list_sbtw_map_iff]
    exact hl's.sbtw
  · by_cases hl : l = []
    · rcases exists_pair_ne P with ⟨p₁, p₂, hp₁p₂⟩
      exact ⟨p₁, p₂, hp₁p₂, by simp [hl, sortedLT_iff_pairwise]⟩
    · by_cases hlen : l.length = 1
      · rw [length_eq_one_iff] at hlen
        rcases hlen with ⟨p₁, rfl⟩
        rcases exists_ne p₁ with ⟨p₂, hp₂p₁⟩
        exact ⟨p₁, p₂, hp₂p₁.symm, [0], by simp [sortedLT_iff_pairwise]⟩
      · refine ⟨l.head hl, l.getLast hl, ?_⟩
        rw [← exists_map_eq_of_sorted_nonempty_iff_sbtw hl] at h
        simp only [hlen, false_or] at h
        rcases h with ⟨l', hl's, hl'l, hl⟩
        exact ⟨hl, l', hl's, hl'l⟩

end LinearOrderedField

end List
