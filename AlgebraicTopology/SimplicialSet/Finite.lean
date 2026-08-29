/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.Data.Finite.Sigma

/-!
# Finite simplicial sets

A simplicial set is finite (`SSet.Finite`) if it has finitely
many nondegenerate simplices.

-/

public section

universe u

open Simplicial CategoryTheory

namespace SSet

variable (X : SSet.{u})

/--
Definition of `Finite` / `Finite` 的定义

English:
class Finite
  parameters: : Prop where
  axioms and operations (1):
    - finite : _root_.Finite X.N

中文:
类 有限
  参数: : 命题 where
  公理与运算 (1 个):
    - finite : _root_.有限 X.N
-/
protected class Finite : Prop where
  finite : _root_.Finite X.N

attribute [instance] Finite.finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Finite]
  signature: (n : Nat)
  body: Finite.of_injective (fun x => N.mk _ x.property) (fun x y h => by
    rw [N.ext_iff]; rw [S.ext_iff'] at h
    aesop)

中文:
实例 [X.有限]
  签名: (n : 自然数)
  定义体: Finite.of_injective (fun x => N.mk _ x.property) (fun x y h => by
    rw [N.ext_iff]; rw [S.ext_iff'] at h
    aesop)

Depends on / 依赖: Finite, Finite.of_injective, N.ext_iff, N.mk, S.ext_iff, ext_iff, of_injective, property, x.property
-/
instance [X.Finite] (n : Nat) : Finite (X.nonDegenerate n) :=
  Finite.of_injective (fun x => N.mk _ x.property) (fun x y h => by
    rw [N.ext_iff]; rw [S.ext_iff'] at h
    aesop)

/--
lemma `finite_of_hasDimensionLT` / 引理 `finite_of_hasDimensionLT`

English:
lemma finite_of_hasDimensionLT
  statement: (d : Nat) [X.HasDimensionLT d]
  proof: by
    have (i : Fin d) : Finite (X.nonDegenerate i) := h i.1 i.2
    refine Finite.of_surjective (α := Σ (i : Fin d), X.nonDegenerate i)
      (f := fun ⟨i, x⟩ => N.mk _ x.property) (fun x => ?_)
    by_cases hj : x.dim < d
    · exact ⟨⟨⟨_, hj⟩, ⟨_, x.nonDegenerate⟩⟩, rfl⟩
    · have := x.nonDegen

中文:
引理 finite_of_hasDimensionLT
  结论: (d : 自然数) [X.有DimensionLT d]
  证明: by
    have (i : Fin d) : Finite (X.nonDegenerate i) := h i.1 i.2
    refine Finite.of_surjective (α := Σ (i : Fin d), X.nonDegenerate i)
      (f := fun ⟨i, x⟩ => N.mk _ x.property) (fun x => ?_)
    by_cases hj : x.dim < d
    · exact ⟨⟨⟨_, hj⟩, ⟨_, x.nonDegenerate⟩⟩, rfl⟩
    · have := x.nonDegen

Depends on / 依赖: Finite, Finite.of_surjective, N.mk, X.nonDegenerate, X.nonDegenerate_eq_empty_of_hasDimensionLT, nonDegenerate, nonDegenerate_eq_empty_of_hasDimensionLT, of_surjective, property, x.dim, x.nonDegenerate, x.property
-/
lemma finite_of_hasDimensionLT (d : Nat) [X.HasDimensionLT d]
    (h : forall (i : Nat) (_ : i < d), Finite (X.nonDegenerate i)) :
    X.Finite where
  finite := by
    have (i : Fin d) : Finite (X.nonDegenerate i) := h i.1 i.2
    refine Finite.of_surjective (α := Σ (i : Fin d), X.nonDegenerate i)
      (f := fun ⟨i, x⟩ => N.mk _ x.property) (fun x => ?_)
    by_cases hj : x.dim < d
    · exact ⟨⟨⟨_, hj⟩, ⟨_, x.nonDegenerate⟩⟩, rfl⟩
    · have := x.nonDegenerate
      simp [X.nonDegenerate_eq_empty_of_hasDimensionLT d x.dim (by simpa using hj)] at this

set_option backward.defeqAttrib.useBackward true in
/--
lemma `hasDimensionLT_of_finite` / 引理 `hasDimensionLT_of_finite`

English:
lemma hasDimensionLT_of_finite
  given: [X.Finite]
  proof: by
  have : Fintype X.N := Fintype.ofFinite _
  let φ (x : X.N) : Nat := x.dim
  obtain ⟨d, hd⟩ : exists (d : Nat), forall (s : Nat) (_ : s in Finset.image φ ⊤), s < d := by
    by_cases h : (Finset.image φ ⊤).Nonempty
    · obtain ⟨d, hd⟩ := Finset.max_of_nonempty h
      exact ⟨d + 1, fun _ _ => b

中文:
引理 hasDimensionLT_of_finite
  条件: [X.有限]
  证明: by
  have : Fintype X.N := Fintype.ofFinite _
  let φ (x : X.N) : Nat := x.dim
  obtain ⟨d, hd⟩ : exists (d : Nat), forall (s : Nat) (_ : s in Finset.image φ ⊤), s < d := by
    by_cases h : (Finset.image φ ⊤).Nonempty
    · obtain ⟨d, hd⟩ := Finset.max_of_nonempty h
      exact ⟨d + 1, fun _ _ => b

Depends on / 依赖: Finset, Finset.image, Finset.le_max, Finset.max_of_nonempty, Finset.not_nonempty_iff_eq_empty, Fintype, Fintype.ofFinite, Nonempty, Set.top, WithBot, WithBot.coe_le_coe, coe_le_coe, le_max, max_of_nonempty, mem_degenerate_iff_notMem_nonDegenerate, not_nonempty_iff_eq_empty, ofFinite, x.dim
-/
lemma hasDimensionLT_of_finite [X.Finite] :
    exists (d : Nat), X.HasDimensionLT d := by
  have : Fintype X.N := Fintype.ofFinite _
  let φ (x : X.N) : Nat := x.dim
  obtain ⟨d, hd⟩ : exists (d : Nat), forall (s : Nat) (_ : s in Finset.image φ ⊤), s < d := by
    by_cases h : (Finset.image φ ⊤).Nonempty
    · obtain ⟨d, hd⟩ := Finset.max_of_nonempty h
      exact ⟨d + 1, fun _ _ => by grind [WithBot.coe_le_coe, -> Finset.le_max]⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      simp only [h]
      exact ⟨0, by simp⟩
  refine ⟨d, ⟨fun n hn => ?_⟩⟩
  ext x
  simp only [mem_degenerate_iff_notMem_nonDegenerate, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  intro hx
  have := hd (φ (N.mk _ hx)) (by simp)
  dsimp [φ] at this
  lia

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Finite]
  signature: (n : SimplexCategoryᵒᵖ)
  body: by
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  let φ : (Σ (m : Fin (n + 1)) (f : ⦋n⦌ ⟶ ⦋m.1⦌),
    X.nonDegenerate m.1) -> X _⦋n⦌ := fun ⟨m, f, x⟩ => X.map f.op x.1
  have hφ : Function.Surjective φ := fun x => by
    obtain ⟨m, f, hf, y, rfl⟩ := X.exists_nonDegenerate x
 

中文:
实例 [X.有限]
  签名: (n : SimplexCategoryᵒᵖ)
  定义体: by
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  let φ : (Σ (m : Fin (n + 1)) (f : ⦋n⦌ ⟶ ⦋m.1⦌),
    X.nonDegenerate m.1) -> X _⦋n⦌ := fun ⟨m, f, x⟩ => X.map f.op x.1
  have hφ : Function.Surjective φ := fun x => by
    obtain ⟨m, f, hf, y, rfl⟩ := X.exists_nonDegenerate x
 

Depends on / 依赖: Finite, Finite.of_surjective, Function, Function.Surjective, SimplexCategory, SimplexCategory.le_of_epi, SimplexCategory.rec, Surjective, X.exists_nonDegenerate, X.map, X.nonDegenerate, exists_nonDegenerate, f.op, le_of_epi, nonDegenerate, of_surjective
-/
instance [X.Finite] (n : SimplexCategoryᵒᵖ) : Finite (X.obj n) := by
  obtain ⟨n⟩ := n
  induction n using SimplexCategory.rec with | _ n
  let φ : (Σ (m : Fin (n + 1)) (f : ⦋n⦌ ⟶ ⦋m.1⦌),
    X.nonDegenerate m.1) -> X _⦋n⦌ := fun ⟨m, f, x⟩ => X.map f.op x.1
  have hφ : Function.Surjective φ := fun x => by
    obtain ⟨m, f, hf, y, rfl⟩ := X.exists_nonDegenerate x
    have := SimplexCategory.le_of_epi f
    exact ⟨⟨⟨m, by lia⟩, f, y⟩, rfl⟩
  exact Finite.of_surjective _ hφ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Finite]
  signature: (A : X.Subcomplex)
  body: by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  refine finite_of_hasDimensionLT _ d (fun i hi => ?_)
  apply Finite.of_injective (f := fun a => a.1.1)
  rintro ⟨⟨x, _⟩, _⟩ ⟨⟨y, _⟩, _⟩ rfl
  rfl

中文:
实例 [X.有限]
  签名: (A : X.子复形)
  定义体: by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  refine finite_of_hasDimensionLT _ d (fun i hi => ?_)
  apply Finite.of_injective (f := fun a => a.1.1)
  rintro ⟨⟨x, _⟩, _⟩ ⟨⟨y, _⟩, _⟩ rfl
  rfl

Depends on / 依赖: Finite, Finite.of_injective, X.hasDimensionLT_of_finite, finite_of_hasDimensionLT, hasDimensionLT_of_finite, of_injective
-/
instance [X.Finite] (A : X.Subcomplex) : SSet.Finite A := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  refine finite_of_hasDimensionLT _ d (fun i hi => ?_)
  apply Finite.of_injective (f := fun a => a.1.1)
  rintro ⟨⟨x, _⟩, _⟩ ⟨⟨y, _⟩, _⟩ rfl
  rfl

variable {X}

/--
lemma `finite_of_mono` / 引理 `finite_of_mono`

English:
lemma finite_of_mono
  given: {Y : SSet.{u}} [Y.Finite] (f : X ⟶ Y) [hf : Mono f]
  statement: X.Finite
  proof: by
  obtain ⟨d, _⟩ := Y.hasDimensionLT_of_finite
  have := hasDimensionLT_of_mono f d
  exact finite_of_hasDimensionLT _ d
    (fun _ _ => Finite.of_injective _
      ((injective_of_mono (f.app _)).comp Subtype.val_injective))

中文:
引理 finite_of_mono
  条件: {Y : SSet.{u}} [Y.有限] (f : X ⟶ Y) [hf : 单态射 f]
  结论: X.有限
  证明: by
  obtain ⟨d, _⟩ := Y.hasDimensionLT_of_finite
  have := hasDimensionLT_of_mono f d
  exact finite_of_hasDimensionLT _ d
    (fun _ _ => Finite.of_injective _
      ((injective_of_mono (f.app _)).comp Subtype.val_injective))

Depends on / 依赖: Finite, Finite.of_injective, Subtype, Subtype.val_injective, Y.hasDimensionLT_of_finite, f.app, finite_of_hasDimensionLT, hasDimensionLT_of_finite, hasDimensionLT_of_mono, injective_of_mono, of_injective, val_injective
-/
lemma finite_of_mono {Y : SSet.{u}} [Y.Finite] (f : X ⟶ Y) [hf : Mono f] : X.Finite := by
  obtain ⟨d, _⟩ := Y.hasDimensionLT_of_finite
  have := hasDimensionLT_of_mono f d
  exact finite_of_hasDimensionLT _ d
    (fun _ _ => Finite.of_injective _
      ((injective_of_mono (f.app _)).comp Subtype.val_injective))

/--
lemma `finite_of_epi` / 引理 `finite_of_epi`

English:
lemma finite_of_epi
  given: {Y : SSet.{u}} [X.Finite] (f : X ⟶ Y) [hf : Epi f]
  statement: Y.Finite
  proof: by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  have := hasDimensionLT_of_epi f d
  refine finite_of_hasDimensionLT _ d (fun i hi => ?_)
  have : Finite (Y _⦋i⦌) := by
    rw [NatTrans.epi_iff_epi_app] at hf
    simp only [epi_iff_surjective] at hf
    exact Finite.of_surjective _ (hf _)
  infer_

中文:
引理 finite_of_epi
  条件: {Y : SSet.{u}} [X.有限] (f : X ⟶ Y) [hf : 满态射 f]
  结论: Y.有限
  证明: by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  have := hasDimensionLT_of_epi f d
  refine finite_of_hasDimensionLT _ d (fun i hi => ?_)
  have : Finite (Y _⦋i⦌) := by
    rw [NatTrans.epi_iff_epi_app] at hf
    simp only [epi_iff_surjective] at hf
    exact Finite.of_surjective _ (hf _)
  infer_

Depends on / 依赖: Finite, Finite.of_surjective, NatTrans, NatTrans.epi_iff_epi_app, X.hasDimensionLT_of_finite, epi_iff_epi_app, epi_iff_surjective, finite_of_hasDimensionLT, hasDimensionLT_of_epi, hasDimensionLT_of_finite, infer_instance, of_surjective
-/
lemma finite_of_epi {Y : SSet.{u}} [X.Finite] (f : X ⟶ Y) [hf : Epi f] : Y.Finite := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  have := hasDimensionLT_of_epi f d
  refine finite_of_hasDimensionLT _ d (fun i hi => ?_)
  have : Finite (Y _⦋i⦌) := by
    rw [NatTrans.epi_iff_epi_app] at hf
    simp only [epi_iff_surjective] at hf
    exact Finite.of_surjective _ (hf _)
  infer_instance

/--
lemma `finite_of_iso` / 引理 `finite_of_iso`

English:
lemma finite_of_iso
  given: {Y : SSet.{u}} (e : X ≅ Y) [X.Finite]
  statement: Y.Finite
  proof: finite_of_mono e.inv

中文:
引理 finite_of_iso
  条件: {Y : SSet.{u}} (e : X ≅ Y) [X.有限]
  结论: Y.有限
  证明: finite_of_mono e.inv

Depends on / 依赖: e.inv, finite_of_mono
-/
lemma finite_of_iso {Y : SSet.{u}} (e : X ≅ Y) [X.Finite] : Y.Finite :=
  finite_of_mono e.inv

/--
lemma `finite_iff_of_iso` / 引理 `finite_iff_of_iso`

English:
lemma finite_iff_of_iso
  given: {Y : SSet.{u}} (e : X ≅ Y)
  statement: X.Finite ↔ Y.Finite
  proof: ⟨fun _ => finite_of_iso e, fun _ => finite_of_iso e.symm⟩

中文:
引理 finite_iff_of_iso
  条件: {Y : SSet.{u}} (e : X ≅ Y)
  结论: X.有限 ↔ Y.有限
  证明: ⟨fun _ => finite_of_iso e, fun _ => finite_of_iso e.symm⟩

Depends on / 依赖: e.symm, finite_of_iso
-/
lemma finite_iff_of_iso {Y : SSet.{u}} (e : X ≅ Y) : X.Finite ↔ Y.Finite :=
  ⟨fun _ => finite_of_iso e, fun _ => finite_of_iso e.symm⟩

variable (X) in
/--
lemma `finite_subcomplex_top_iff` / 引理 `finite_subcomplex_top_iff`

English:
lemma finite_subcomplex_top_iff
  proof: finite_iff_of_iso (Subcomplex.topIso X)

中文:
引理 finite_subcomplex_top_iff
  证明: finite_iff_of_iso (Subcomplex.topIso X)

Depends on / 依赖: Subcomplex, Subcomplex.topIso, finite_iff_of_iso, topIso
-/
lemma finite_subcomplex_top_iff :
    SSet.Finite (⊤ : X.Subcomplex) ↔ X.Finite :=
  finite_iff_of_iso (Subcomplex.topIso X)

/--
Instance `finite_range` / 实例 `finite_range`

English:
instance finite_range
  signature: {Y : SSet.{u}} (f : Y ⟶ X) [Y.Finite]
  body: finite_of_epi (Subcomplex.toRange f)

中文:
实例 finite_range
  签名: {Y : SSet.{u}} (f : Y ⟶ X) [Y.有限]
  定义体: finite_of_epi (Subcomplex.toRange f)

Depends on / 依赖: Subcomplex, Subcomplex.toRange, finite_of_epi, toRange
-/
instance finite_range {Y : SSet.{u}} (f : Y ⟶ X) [Y.Finite] :
    SSet.Finite (Subcomplex.range f) :=
  finite_of_epi (Subcomplex.toRange f)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `finite_iSup_iff` / 引理 `finite_iSup_iff`

English:
lemma finite_iSup_iff
  statement: {X : SSet.{u}} {ι : Type*} [Finite ι]
  proof: by
  refine ⟨fun h i => finite_of_mono (Subcomplex.homOfLE (le_iSup A i)), fun h => ⟨?_⟩⟩
  refine Finite.of_surjective (f := fun (⟨i, s⟩ : Σ (i : ι), (A i).toSSet.N) =>
    N.mk ((Subcomplex.homOfLE (le_iSup A i)).app _ s.simplex)
      (by simpa only [nonDegenerate_iff_of_mono] using s.nonDegenera

中文:
引理 finite_iSup_iff
  结论: {X : SSet.{u}} {ι : 类型} [有限 ι]
  证明: by
  refine ⟨fun h i => finite_of_mono (Subcomplex.homOfLE (le_iSup A i)), fun h => ⟨?_⟩⟩
  refine Finite.of_surjective (f := fun (⟨i, s⟩ : Σ (i : ι), (A i).toSSet.N) =>
    N.mk ((Subcomplex.homOfLE (le_iSup A i)).app _ s.simplex)
      (by simpa only [nonDegenerate_iff_of_mono] using s.nonDegenera

Depends on / 依赖: Finite, Finite.of_surjective, N.mk, Set.mem_iUnion, Subcomplex, Subcomplex.homOfLE, Subcomplex.mem_nonDegenerate_iff, Subfunctor, Subfunctor.iSup_obj, finite_of_mono, homOfLE, iSup_obj, le_iSup, mem_iUnion, mem_nonDegenerate_iff, mk_surjective, nonDegenerate, nonDegenerate_iff_of_mono, of_surjective, s.mk_surjective
-/
lemma finite_iSup_iff {X : SSet.{u}} {ι : Type*} [Finite ι]
    (A : ι -> X.Subcomplex) :
    SSet.Finite (⨆ i, A i :) ↔ forall i, SSet.Finite (A i) := by
  refine ⟨fun h i => finite_of_mono (Subcomplex.homOfLE (le_iSup A i)), fun h => ⟨?_⟩⟩
  refine Finite.of_surjective (f := fun (⟨i, s⟩ : Σ (i : ι), (A i).toSSet.N) =>
    N.mk ((Subcomplex.homOfLE (le_iSup A i)).app _ s.simplex)
      (by simpa only [nonDegenerate_iff_of_mono] using s.nonDegenerate)) ?_
  intro s
  obtain ⟨d, ⟨⟨s, h₁⟩, h₂⟩, rfl⟩ := s.mk_surjective
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at h₁
  obtain ⟨i, hi⟩ := h₁
  rw [Subcomplex.mem_nonDegenerate_iff] at h₂
  exact ⟨⟨i, N.mk ⟨s, hi⟩ (by rwa [Subcomplex.mem_nonDegenerate_iff])⟩, rfl⟩

end SSet
