/-
Copyright (c) 2026 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Light.InternallyProjective

import Mathlib.Condensed.Light.EffectiveEpi
import Mathlib.Topology.Category.LightProfinite.Injective
/-!

# The free light condensed `R`-module `R[ℕ∪∞]` is internally projective
-/

open CategoryTheory Category Functor LightProfinite OnePoint LightCondensed
  MonoidalCategory CartesianMonoidalCategory CompHausLike

variable (R : Type) [CommRing R]
-- `R` is in `Type` because `ℕ∪∞` currently only exists in `LightProfinite.{0}`.
-- TODO: make a universe polymorphic `ℕ∪∞` and generalize this result.

namespace InternalProjectivityProof

section

variable {X Y : LightProfinite} (y : Y) (f : X ⟶ Y)

/--
Definition of `LightProfinite.fibre` / `LightProfinite.fibre` 的定义

English:
definition LightProfinite.fibre
  signature: : LightProfinite
  body: haveI : CompactSpace (f ⁻¹' {y}) :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton).isCompact
  of (f ⁻¹' {y})

中文:
定义 LightProfinite.fibre
  签名: : LightProfinite
  定义体: haveI : CompactSpace (f ⁻¹' {y}) :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton).isCompact
  of (f ⁻¹' {y})

Depends on / 依赖: CompactSpace, IsClosed, IsClosed.preimage, fun_prop, isClosed_singleton, isCompact, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, preimage
-/
def LightProfinite.fibre : LightProfinite :=
  haveI : CompactSpace (f ⁻¹' {y}) :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton).isCompact
  of (f ⁻¹' {y})

/--
Definition of `LightProfinite.fibreIncl` / `LightProfinite.fibreIncl` 的定义

English:
definition LightProfinite.fibreIncl
  signature: : fibre y f ⟶ X
  body: ⟨TopCat.ofHom { toFun := Subtype.val }⟩

中文:
定义 LightProfinite.fibreIncl
  签名: : fibre y f ⟶ X
  定义体: ⟨TopCat.ofHom { toFun := Subtype.val }⟩

Depends on / 依赖: Subtype, Subtype.val, TopCat, TopCat.ofHom
-/
def LightProfinite.fibreIncl : fibre y f ⟶ X := ⟨TopCat.ofHom { toFun := Subtype.val }⟩

end

section

variable {S T X : Type*}

/--
Definition of `fibres` / `fibres` 的定义

English:
definition fibres
  signature: (π : T -> S × Option X) (σ : Option X -> S -> T)
  body: {t : T | (π t).2 = none} union (⋃ (x : X), Set.range (σ x))

@[simp, grind =]

中文:
定义 fibres
  签名: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  定义体: {t : T | (π t).2 = none} union (⋃ (x : X), Set.range (σ x))

@[simp, grind =]

Depends on / 依赖: Set.range
-/
def fibres (π : T -> S × Option X) (σ : Option X -> S -> T) : Set T :=
  {t : T | (π t).2 = none} union (⋃ (x : X), Set.range (σ x))

@[simp, grind =]
/--
lemma `mem_fibres_iff` / 引理 `mem_fibres_iff`

English:
lemma mem_fibres_iff
  given: (π : T -> S × Option X) (σ : Option X -> S -> T) (t : T)
  proof: by
  simp [fibres]

中文:
引理 mem_fibres_iff
  条件: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T) (t : T)
  证明: by
  simp [fibres]

Depends on / 依赖: fibres
-/
lemma mem_fibres_iff (π : T -> S × Option X) (σ : Option X -> S -> T) (t : T) :
    t in fibres π σ ↔ (π t).2 = none ∨ exists (x : X) (s : S), σ x s = t := by
  simp [fibres]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fibres_compl_eq_iUnion` / 引理 `fibres_compl_eq_iUnion`

English:
lemma fibres_compl_eq_iUnion
  statement: (π : T -> S × Option X) (σ : Option X -> S -> T)
  proof: by
  ext x
  -- simp? says:
  simp only [Set.mem_compl_iff, mem_fibres_iff, not_or, not_exists, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, Function.comp_apply,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨n, hn, hn'⟩ => ?_⟩
  · obtain ⟨n, hn⟩ := Option.n

中文:
引理 fibres_compl_eq_iUnion
  结论: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  证明: by
  ext x
  -- simp? says:
  simp only [Set.mem_compl_iff, mem_fibres_iff, not_or, not_exists, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, Function.comp_apply,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨n, hn, hn'⟩ => ?_⟩
  · obtain ⟨n, hn⟩ := Option.n
-/
lemma fibres_compl_eq_iUnion (π : T -> S × Option X) (σ : Option X -> S -> T)
    (hσ' : forall (x : Option X) (s : S), (π (σ x s)).2 = x) :
    (fibres π σ)ᶜ =
      ⋃ i, (Set.range (σ (Option.some i)))ᶜ inter (Prod.snd ∘ π) ⁻¹' {(i : OnePoint X)} := by
  ext x
  -- simp? says:
  simp only [Set.mem_compl_iff, mem_fibres_iff, not_or, not_exists, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, Function.comp_apply,
    Set.mem_singleton_iff]
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨n, hn, hn'⟩ => ?_⟩
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h₁
    exact ⟨n, h₂ n, hn⟩
  · refine ⟨by simpa [hn'] using Option.isSome_iff_ne_none.mp rfl, fun i s h => hn s ?_⟩
    rw [← h]; rw [hσ'] at hn'
    rw [← h]; rw [Option.some_injective _ hn'.symm]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fibres_closed` / 引理 `fibres_closed`

English:
lemma fibres_closed
  statement: [TopologicalSpace S] [TopologicalSpace T]
  proof: IsClosed.mk by
  rw [fibres_compl_eq_iUnion π σ hσ']
  refine isOpen_iUnion fun i => IsOpen.inter ?_ ?_
  · simpa using IsCompact.isClosed (isCompact_range (hσ i))
  · exact .preimage (continuous_snd.comp hπ) ⟨fun h => by simp_all, by simp⟩

中文:
引理 fibres_closed
  结论: [拓扑空间 S] [拓扑空间 T]
  证明: IsClosed.mk by
  rw [fibres_compl_eq_iUnion π σ hσ']
  refine isOpen_iUnion fun i => IsOpen.inter ?_ ?_
  · simpa using IsCompact.isClosed (isCompact_range (hσ i))
  · exact .preimage (continuous_snd.comp hπ) ⟨fun h => by simp_all, by simp⟩

Depends on / 依赖: IsClosed, IsClosed.mk, IsCompact, IsCompact.isClosed, IsOpen, IsOpen.inter, continuous_snd, continuous_snd.comp, fibres_compl_eq_iUnion, isClosed, isCompact_range, isOpen_iUnion, preimage
-/
lemma fibres_closed [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace X] [DiscreteTopology X] [T2Space T] [CompactSpace S]
    (π : T -> S × OnePoint X) (hπ : Continuous π)
    (σ : Option X -> S -> T) (hσ : forall x, Continuous (σ x))
    (hσ' : forall (x : Option X) (s : S), (π (σ x s)).2 = x) :
IsClosed (fibres π σ) := IsClosed.mk by
  rw [fibres_compl_eq_iUnion π σ hσ']
  refine isOpen_iUnion fun i => IsOpen.inter ?_ ?_
  · simpa using IsCompact.isClosed (isCompact_range (hσ i))
  · exact .preimage (continuous_snd.comp hπ) ⟨fun h => by simp_all, by simp⟩

/--
Definition of `π_r` / `π_r` 的定义

English:
definition π_r
  signature: (π : T -> S × Option X) (σ : Option X -> S -> T)
  body: fun x => π x

@[grind =]

中文:
定义 π_r
  签名: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  定义体: fun x => π x

@[grind =]
-/
def π_r (π : T -> S × Option X) (σ : Option X -> S -> T) :
    fibres π σ -> S × Option X :=
  fun x => π x

@[grind =]
/--
lemma `π_r_apply` / 引理 `π_r_apply`

English:
lemma π_r_apply
  statement: (π : T -> S × Option X) (σ : Option X -> S -> T)
  proof: rfl

中文:
引理 π_r_apply
  结论: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  证明: rfl
-/
lemma π_r_apply (π : T -> S × Option X) (σ : Option X -> S -> T)
    (x : fibres π σ) : π_r π σ x = π x :=
  rfl

/--
Definition of `fibreIncl` / `fibreIncl` 的定义

English:
definition fibreIncl
  signature: (π : T -> S × Option X) (σ : Option X -> S -> T)
  body: Subtype.val

@[grind =]

中文:
定义 fibreIncl
  签名: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  定义体: Subtype.val

@[grind =]

Depends on / 依赖: Subtype, Subtype.val
-/
def fibreIncl (π : T -> S × Option X) (σ : Option X -> S -> T) :
    (Prod.snd ∘ π_r π σ) ⁻¹' {none} -> fibres π σ :=
  Subtype.val

@[grind =]
/--
lemma `fibreIncl_apply` / 引理 `fibreIncl_apply`

English:
lemma fibreIncl_apply
  statement: (π : T -> S × Option X) (σ : Option X -> S -> T)
  proof: rfl

中文:
引理 fibreIncl_apply
  结论: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  证明: rfl
-/
lemma fibreIncl_apply (π : T -> S × Option X) (σ : Option X -> S -> T)
    (x : (Prod.snd ∘ π_r π σ) ⁻¹' {none}) : fibreIncl π σ x = x :=
  rfl

/--
lemma `fibres_surjective` / 引理 `fibres_surjective`

English:
lemma fibres_surjective
  proof: by
  rintro ⟨s, (rfl | x)⟩
  · obtain ⟨y, hy⟩ := hπ (s, none)
    exact ⟨⟨y, by grind⟩, hy⟩
  · exact ⟨⟨σ x s, by simp⟩, Prod.ext (by grind) (by grind)⟩

中文:
引理 fibres_surjective
  证明: by
  rintro ⟨s, (rfl | x)⟩
  · obtain ⟨y, hy⟩ := hπ (s, none)
    exact ⟨⟨y, by grind⟩, hy⟩
  · exact ⟨⟨σ x s, by simp⟩, Prod.ext (by grind) (by grind)⟩

Depends on / 依赖: Prod.ext
-/
lemma fibres_surjective
    (π : T -> S × Option X) (hπ : π.Surjective) (σ : Option X -> S -> T)
    (hσ : forall (x : Option X) s, (π (σ x s)).1 = s)
    (hσ' : forall (x : Option X) (s : S), (π (σ x s)).2 = x) :
    (fun (x : fibres π σ) => π x).Surjective := by
  rintro ⟨s, (rfl | x)⟩
  · obtain ⟨y, hy⟩ := hπ (s, none)
    exact ⟨⟨y, by grind⟩, hy⟩
  · exact ⟨⟨σ x s, by simp⟩, Prod.ext (by grind) (by grind)⟩

/--
Definition of `coverToFun` / `coverToFun` 的定义

English:
definition coverToFun
  signature: {S T X Y : Type*} (i : Y -> T) (π : T -> S × Option X)
  body: Sum.elim (fun t => ⟨(t, t), rfl⟩) (fun xy => ⟨(i xy.val.1, i xy.val.2), xy.prop⟩)

@[grind =]

中文:
定义 coverToFun
  签名: {S T X Y : 类型} (i : Y -> T) (π : T -> S × 选项类型 X)
  定义体: Sum.elim (fun t => ⟨(t, t), rfl⟩) (fun xy => ⟨(i xy.val.1, i xy.val.2), xy.prop⟩)

@[grind =]

Depends on / 依赖: Sum.elim, xy.prop, xy.val
-/
def coverToFun {S T X Y : Type*} (i : Y -> T) (π : T -> S × Option X) :
    T oplus {xy : Y × Y // π (i xy.1) = π (i xy.2)} -> {xy : T × T // π xy.1 = π xy.2} :=
  Sum.elim (fun t => ⟨(t, t), rfl⟩) (fun xy => ⟨(i xy.val.1, i xy.val.2), xy.prop⟩)

@[grind =]
/--
lemma `coverToFun_apply` / 引理 `coverToFun_apply`

English:
lemma coverToFun_apply
  statement: {S T X Y : Type*} (i : Y -> T) (π : T -> S × Option X)
  proof: rfl

中文:
引理 coverToFun_apply
  结论: {S T X Y : 类型} (i : Y -> T) (π : T -> S × 选项类型 X)
  证明: rfl
-/
lemma coverToFun_apply {S T X Y : Type*} (i : Y -> T) (π : T -> S × Option X)
    (t : T oplus {xy : Y × Y // π (i xy.1) = π (i xy.2)}) :
    coverToFun i π t =
      Sum.elim (fun t => ⟨(t, t), rfl⟩) (fun xy => ⟨(i xy.val.1, i xy.val.2), xy.prop⟩) t :=
  rfl

/--
lemma `coverToFun_surjective` / 引理 `coverToFun_surjective`

English:
lemma coverToFun_surjective
  statement: (π : T -> S × Option X) (σ : Option X -> S -> T)
  proof: by
  intro ⟨⟨⟨t, ht⟩, ⟨t', ht'⟩⟩, _⟩
  by_cases h : (π t).2 = none
  · exact ⟨Sum.inr ⟨(⟨⟨t, ht⟩, by grind⟩, ⟨⟨t', ht'⟩, by grind⟩), by grind⟩, by grind⟩
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨Sum.inl ⟨σ n (π t).1, by grind⟩, by grind⟩

中文:
引理 coverToFun_surjective
  结论: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  证明: by
  intro ⟨⟨⟨t, ht⟩, ⟨t', ht'⟩⟩, _⟩
  by_cases h : (π t).2 = none
  · exact ⟨Sum.inr ⟨(⟨⟨t, ht⟩, by grind⟩, ⟨⟨t', ht'⟩, by grind⟩), by grind⟩, by grind⟩
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨Sum.inl ⟨σ n (π t).1, by grind⟩, by grind⟩

Depends on / 依赖: Option.ne_none_iff_exists, Sum.inl, Sum.inr, ne_none_iff_exists
-/
lemma coverToFun_surjective (π : T -> S × Option X) (σ : Option X -> S -> T)
    (hσ : forall (x : Option X) s, (π (σ x s)).1 = s)
    (hσ' : forall (x : Option X) (s : S), (π (σ x s)).2 = x) :
    Function.Surjective (coverToFun (fibreIncl π σ) (π_r π σ)) := by
  intro ⟨⟨⟨t, ht⟩, ⟨t', ht'⟩⟩, _⟩
  by_cases h : (π t).2 = none
  · exact ⟨Sum.inr ⟨(⟨⟨t, ht⟩, by grind⟩, ⟨⟨t', ht'⟩, by grind⟩), by grind⟩, by grind⟩
  · obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨Sum.inl ⟨σ n (π t).1, by grind⟩, by grind⟩

/--
Definition of `sectionOfFibreIncl` / `sectionOfFibreIncl` 的定义

English:
definition sectionOfFibreIncl
  signature: (π : T -> S × Option X) (σ : Option X -> S -> T)
  body: fun s => ⟨⟨σ none s, by grind⟩, by grind⟩

中文:
定义 sectionOfFibreIncl
  签名: (π : T -> S × 选项类型 X) (σ : 选项类型 X -> S -> T)
  定义体: fun s => ⟨⟨σ none s, by grind⟩, by grind⟩
-/
def sectionOfFibreIncl (π : T -> S × Option X) (σ : Option X -> S -> T)
    (hσ' : forall (x : Option X) (s : S), (π (σ x s)).2 = x) : S -> (Prod.snd ∘ π_r π σ) ⁻¹' {none} :=
  fun s => ⟨⟨σ none s, by grind⟩, by grind⟩

/--
Definition of `S'` / `S'` 的定义

English:
definition S'
  signature: (π : T -> S × OnePoint X)
  body: {x | forall n m, (π (x n).val).1 = (π (x m).val).1}

@[simp, grind =]

中文:
定义 S'
  签名: (π : T -> S × OnePoint X)
  定义体: {x | forall n m, (π (x n).val).1 = (π (x m).val).1}

@[simp, grind =]
-/
def S' (π : T -> S × OnePoint X) : Set (forall x : OnePoint X, (Prod.snd ∘ π) ⁻¹' {x}) :=
  {x | forall n m, (π (x n).val).1 = (π (x m).val).1}

@[simp, grind =]
/--
lemma `mem_S'_iff` / 引理 `mem_S'_iff`

English:
lemma mem_S'_iff
  given: (π : T -> S × OnePoint X) (y : forall x : OnePoint X, (Prod.snd ∘ π) ⁻¹' {x})
  proof: Iff.rfl

中文:
引理 mem_S'_iff
  条件: (π : T -> S × OnePoint X) (y : 对任意 x : OnePoint X, (积类型.snd ∘ π) ⁻¹' {x})
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_S'_iff (π : T -> S × OnePoint X) (y : forall x : OnePoint X, (Prod.snd ∘ π) ⁻¹' {x}) :
    y in S' π ↔ forall n m, (π (y n).val).1 = (π (y m).val).1 :=
  Iff.rfl

/--
Definition of `y` / `y` 的定义

English:
definition y
  signature: (π : T -> S × OnePoint X)
  body: fun x => (π (x.val ∞).val).1

@[grind =]

中文:
定义 y
  签名: (π : T -> S × OnePoint X)
  定义体: fun x => (π (x.val ∞).val).1

@[grind =]

Depends on / 依赖: x.val
-/
def y (π : T -> S × OnePoint X) : S' π -> S := fun x => (π (x.val ∞).val).1

@[grind =]
/--
lemma `y_apply` / 引理 `y_apply`

English:
lemma y_apply
  given: (π : T -> S × OnePoint X) (x : S' π)
  statement: y π x = (π (x.val ∞).val).1
  proof: rfl

中文:
引理 y_apply
  条件: (π : T -> S × OnePoint X) (x : S' π)
  结论: y π x = (π (x.val ∞).val).1
  证明: rfl
-/
lemma y_apply (π : T -> S × OnePoint X) (x : S' π) : y π x = (π (x.val ∞).val).1 := rfl

/--
lemma `y_continuous` / 引理 `y_continuous`

English:
lemma y_continuous
  statement: [TopologicalSpace S] [TopologicalSpace T]
  proof: continuous_fst.comp hπ.comp continuous_subtype_val.comp
    (continuous_apply _).comp (by fun_prop)

中文:
引理 y_continuous
  结论: [拓扑空间 S] [拓扑空间 T]
  证明: continuous_fst.comp hπ.comp continuous_subtype_val.comp
    (continuous_apply _).comp (by fun_prop)

Depends on / 依赖: Continuous, continuous_apply, continuous_fst, continuous_fst.comp, continuous_subtype_val, continuous_subtype_val.comp, fun_prop
-/
lemma y_continuous [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace X] (π : T -> S × OnePoint X) (hπ : Continuous π := by fun_prop) :
    Continuous (y π) :=
continuous_fst.comp hπ.comp continuous_subtype_val.comp
    (continuous_apply _).comp (by fun_prop)

/--
lemma `y_surjective` / 引理 `y_surjective`

English:
lemma y_surjective
  given: (π : T -> S × OnePoint X) (hπ : π.Surjective)
  proof: by
  intro s
  let p (s : S) (n : OnePoint X) : T := (hπ (s, n)).choose
  have hp (s : S) (n : OnePoint X) : π (p s n) = (s, n) := (hπ (s, n)).choose_spec
  exact ⟨⟨fun n => ⟨p s n, by grind⟩, by grind⟩, by grind⟩

中文:
引理 y_surjective
  条件: (π : T -> S × OnePoint X) (hπ : π.满射)
  证明: by
  intro s
  let p (s : S) (n : OnePoint X) : T := (hπ (s, n)).choose
  have hp (s : S) (n : OnePoint X) : π (p s n) = (s, n) := (hπ (s, n)).choose_spec
  exact ⟨⟨fun n => ⟨p s n, by grind⟩, by grind⟩, by grind⟩

Depends on / 依赖: OnePoint, choose_spec
-/
lemma y_surjective (π : T -> S × OnePoint X) (hπ : π.Surjective) :
    (y π).Surjective := by
  intro s
  let p (s : S) (n : OnePoint X) : T := (hπ (s, n)).choose
  have hp (s : S) (n : OnePoint X) : π (p s n) = (s, n) := (hπ (s, n)).choose_spec
  exact ⟨⟨fun n => ⟨p s n, by grind⟩, by grind⟩, by grind⟩

/--
lemma `S'_compactSpace` / 引理 `S'_compactSpace`

English:
lemma S'_compactSpace
  statement: [TopologicalSpace S] [T2Space S] [TopologicalSpace T]
  proof: by
  rw [← isCompact_iff_compactSpace]; rw [show S' π =
    ⋂ (n : OnePoint X) (m : OnePoint X)]; rw [{x | (π (x n).val).1 = (π (x m).val).1} by aesop]
have (x : OnePoint X) : CompactSpace (Prod.snd ∘ π) ⁻¹' {x} :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton

中文:
引理 S'_compactSpace
  结论: [拓扑空间 S] [T2空间 S] [拓扑空间 T]
  证明: by
  rw [← isCompact_iff_compactSpace]; rw [show S' π =
    ⋂ (n : OnePoint X) (m : OnePoint X)]; rw [{x | (π (x n).val).1 = (π (x m).val).1} by aesop]
have (x : OnePoint X) : CompactSpace (Prod.snd ∘ π) ⁻¹' {x} :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton
-/
lemma S'_compactSpace [TopologicalSpace S] [T2Space S] [TopologicalSpace T]
    [CompactSpace T] [TopologicalSpace X] [T1Space (OnePoint X)]
    (π : T -> S × OnePoint X) (hπ : Continuous π) : CompactSpace (S' π) := by
  rw [← isCompact_iff_compactSpace]; rw [show S' π =
    ⋂ (n : OnePoint X) (m : OnePoint X)]; rw [{x | (π (x n).val).1 = (π (x m).val).1} by aesop]
have (x : OnePoint X) : CompactSpace (Prod.snd ∘ π) ⁻¹' {x} :=
    isCompact_iff_compactSpace.mp (IsClosed.preimage (by fun_prop) isClosed_singleton).isCompact
  refine (isClosed_iInter fun n => isClosed_iInter fun m => isClosed_eq ?_ ?_).isCompact
  all_goals fun_prop

end

/--
Definition of `cover` / `cover` 的定义

English:
definition cover
  signature: {S T : LightProfinite} (π : T ⟶ S otimes Natunion{∞})
  body: ⟨TopCat.ofHom {
  toFun := coverToFun _ _
  continuous_toFun := by dsimp [coverToFun]; fun_prop }⟩

中文:
定义 cover
  签名: {S T : LightProfinite} (π : T ⟶ S otimes 自然数union{∞})
  定义体: ⟨TopCat.ofHom {
  toFun := coverToFun _ _
  continuous_toFun := by dsimp [coverToFun]; fun_prop }⟩

Depends on / 依赖: TopCat, TopCat.ofHom
-/
def cover {S T : LightProfinite} (π : T ⟶ S otimes Natunion{∞}) :
    (of _ (T oplus (pullback (LightProfinite.fibreIncl ∞ (π ≫ snd S Natunion{∞}) ≫ π)
      (LightProfinite.fibreIncl ∞ (π ≫ snd S Natunion{∞}) ≫ π)))) ⟶ pullback π π := ⟨TopCat.ofHom {
  toFun := coverToFun _ _
  continuous_toFun := by dsimp [coverToFun]; fun_prop }⟩

open Limits in
set_option backward.isDefEq.respectTransparency false in
/-- Given a map `π : T ⟶ S ⊗ ℕ∪{∞}` and map `g : (free R) T.toCondensed ⟶ X`, the corresponding
map of free condensed R modules, construct a cocone for the parallel pair of both projections of
the pullback, which will descend down to a map `S ⊗ ℕ∪{∞} ⟶ X` by the universal property of
effective epimorphisms. The cocone is constructed by modifying `g` at the at the fibre over `∞`
using the retraction `r_inf`. -/
@[simps! pt ι_app]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: {X : LightCondMod R} {S T : LightProfinite} (π : T ⟶ S otimes Natunion{∞})
  body: by
  refine Cocone.ofCofork (Cofork.ofπ (g -
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g +
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫
        LightProfini

中文:
定义 cocone
  签名: {X : LightCondMod R} {S T : LightProfinite} (π : T ⟶ S otimes 自然数union{∞})
  定义体: by
  refine Cocone.ofCofork (Cofork.ofπ (g -
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g +
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫
        LightProfini

Depends on / 依赖: Cocone, Cocone.ofCofork, Cofork, Cofork.of, LightProfinite, LightProfinite.fibreIncl, cancel_epi, coproductIsColimit, fibreIncl, hom_ext, isColimitOfPreserves, lightProfiniteToLightCondSet, ofCofork, r_inf
-/
noncomputable def cocone {X : LightCondMod R} {S T : LightProfinite} (π : T ⟶ S otimes Natunion{∞})
    [Epi ((lightProfiniteToLightCondSet ⋙ free R).map <| cover π)]
    (g : ((lightProfiniteToLightCondSet ⋙ free R).obj T) ⟶ X)
    (r_inf : T ⟶ (LightProfinite.fibre ∞ (π ≫ snd _ _)))
    (σ : S ⟶ (LightProfinite.fibre ∞ (π ≫ snd _ _)))
    (hr : LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ r_inf =
      𝟙 (LightProfinite.fibre ∞ (π ≫ snd _ _))) :
    Cocone ((parallelPair (lightProfiniteToLightCondSet.map (CompHausLike.pullback.fst π π))
      (lightProfiniteToLightCondSet.map (pullback.snd π π))) ⋙ free R) := by
  refine Cocone.ofCofork (Cofork.ofπ (g -
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g +
    (lightProfiniteToLightCondSet ⋙ free R).map
      (r_inf ≫ LightProfinite.fibreIncl ∞ (π ≫ snd _ _) ≫ π ≫ fst _ _ ≫ σ ≫
        LightProfinite.fibreIncl ∞ (π ≫ snd _ _)) ≫ g) ?_)
  rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ free R).map <| cover π)]
  apply (isColimitOfPreserves (lightProfiniteToLightCondSet ⋙ free R)
      (coproductIsColimit _ _)).hom_ext
  rintro ⟨⟨⟩⟩
  · simp [← map_comp_assoc, -Functor.map_comp]
    rfl
  · -- simp? [← map_comp_assoc, -Functor.map_comp] says:
    simp only [pair_obj_right, mapCocone_ι_app,
      Functor.comp_map, parallelPair_obj_zero, parallelPair_obj_one, parallelPair_map_left,
      Preadditive.comp_add, Preadditive.comp_sub, ← map_comp_assoc, parallelPair_map_right]
    have : cover π = (BinaryCofan.IsColimit.desc' (coproductIsColimit _ _)
        (CompHausLike.pullback.lift _ _ (𝟙 T) (𝟙 T) (by simp))
        (CompHausLike.pullback.lift _ _
          ((CompHausLike.pullback.fst _ _) ≫ LightProfinite.fibreIncl _ _)
          ((pullback.snd _ _) ≫ LightProfinite.fibreIncl _ _)
          (by simp [pullback.condition]))).val := rfl
    -- simp? [this, ← Functor.map_comp] says:
    simp only [this, pair_obj_left, pair_obj_right, BinaryCofan.IsColimit.desc'_coe,
      IsColimit.fac, BinaryCofan.mk_inr, ← Functor.map_comp,
      pullback.lift_fst, IsColimit.fac_assoc, assoc,
      pullback.lift_snd]
    -- simp? [-Functor.map_comp, ← assoc, hr] says:
    simp only [← assoc, hr, id_comp, sub_self, zero_add]
    simp [pullback.condition]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  given: {S T : LightProfinite} (π : T ⟶ S otimes Natunion{∞}) [Epi π]
  proof: by
  -- Construct the space `S'` space which has functions `σ'` we can plug into
  -- `fibres`.
  have := S'_compactSpace π (by fun_prop)
  let S'π (n : Natunion{∞}) : LightProfinite.of (S' π) ⟶ LightProfinite.fibre n (π ≫ snd _ _) :=
    ⟨TopCat.ofHom {
      toFun x := x.val n,
      continuous_to

中文:
引理 aux
  条件: {S T : LightProfinite} (π : T ⟶ S otimes 自然数union{∞}) [满态射 π]
  证明: by
  -- Construct the space `S'` space which has functions `σ'` we can plug into
  -- `fibres`.
  have := S'_compactSpace π (by fun_prop)
  let S'π (n : Natunion{∞}) : LightProfinite.of (S' π) ⟶ LightProfinite.fibre n (π ≫ snd _ _) :=
    ⟨TopCat.ofHom {
      toFun x := x.val n,
      continuous_to
-/
lemma aux {S T : LightProfinite} (π : T ⟶ S otimes Natunion{∞}) [Epi π] :
    exists (S' T' : LightProfinite) (y' : S' ⟶ S) (π' : T' ⟶ S' otimes Natunion{∞}) (g' : T' ⟶ T),
      Epi π' ∧ Epi y' ∧ π' ≫ (y' ▷ Natunion{∞}) = g' ≫ π ∧
        IsSplitEpi (LightProfinite.fibreIncl ∞ (π' ≫ snd S' Natunion{∞}) ≫ π' ≫ fst S' Natunion{∞}) ∧
          Epi (cover π') := by
  -- Construct the space `S'` space which has functions `σ'` we can plug into
  -- `fibres`.
  have := S'_compactSpace π (by fun_prop)
  let S'π (n : Natunion{∞}) : LightProfinite.of (S' π) ⟶ LightProfinite.fibre n (π ≫ snd _ _) :=
    ⟨TopCat.ofHom {
      toFun x := x.val n,
      continuous_toFun := by refine (continuous_apply _).comp ?_; fun_prop }⟩
  let y' : LightProfinite.of (S' π) ⟶ S := ConcreteCategory.ofHom ⟨y π, y_continuous π⟩
  let π' := pullback.snd π (y' ▷ Natunion{∞})
  let σ' : Natunion{∞} -> LightProfinite.of (S' π) -> pullback π (y' ▷ Natunion{∞}) := fun n =>
pullback.lift _ _ (S'π n ≫ LightProfinite.fibreIncl _ _) (lift (𝟙 _) (const _ n)) by
      apply CartesianMonoidalCategory.hom_ext<;> ext x; exacts [x.prop n ∞, (x.val n).prop]
  have hσ (x : Natunion{∞}) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).1 = s := rfl
  have hσ' (x : Natunion{∞}) (s : LightProfinite.of (S' π)) : (π' (σ' x s)).2 = x := rfl
  -- The space `T'` is given by the union of the images of the `σ'` together
  -- with the whole fibre over `∞`. Here `cover` is an epimorphism
  -- because the projection is an isomorphism away from the fibre at `∞`.
  have : CompactSpace (fibres π' σ') := isCompact_iff_compactSpace.mp
    (fibres_closed π' (by fun_prop) σ' (by fun_prop) hσ').isCompact
  refine ⟨LightProfinite.of (S' π), LightProfinite.of (fibres π' σ'), y',
    ⟨TopCat.ofHom ⟨Subtype.val, by fun_prop⟩⟩ ≫ π',
    ⟨TopCat.ofHom ⟨Subtype.val, by fun_prop⟩⟩ ≫ pullback.fst _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LightProfinite.epi_iff_surjective]
    refine fibres_surjective _ ?_ _ hσ hσ'
    rw [← LightProfinite.epi_iff_surjective]
    dsimp [π']
    infer_instance
  · rw [LightProfinite.epi_iff_surjective]
    apply y_surjective
    rwa [← LightProfinite.epi_iff_surjective]
  · simp [π', pullback.condition]
  · exact ⟨ConcreteCategory.ofHom ⟨(sectionOfFibreIncl π' σ' hσ'),
      (.subtype_mk (by fun_prop) _)⟩, rfl⟩
  · rw [LightProfinite.epi_iff_surjective]
    exact coverToFun_surjective _ _ hσ hσ'

end InternalProjectivityProof

open InternalProjectivityProof

set_option backward.isDefEq.respectTransparency false in
public theorem LightCondensed.internallyProjective_free_natUnionInfty :
    InternallyProjective ((free R).obj (Natunion{∞}).toCondensed) := by
  rw [free_lightProfinite_internallyProjective_iff_tensor_condition' R Natunion{∞}]
  intro X Y p hp S f
  obtain ⟨T, π, g, hπ, comm⟩ := LightCondMod.factorsThru_lightProfinite_epi_of_epi R p f
  obtain ⟨S', T', y', π', g', hπ', hy', comp, ⟨⟨split⟩⟩, epi⟩ := aux π
  refine ⟨S', y', (LightProfinite.epi_iff_surjective _).mp inferInstance, ?_⟩
  -- There is a commutative square
  -- T' -> S' ⊗ ℕ∪{∞}
  -- | |
  -- v v
  -- X -> Y
  -- and the goal is a diagonal map such that the lower right triangle
  -- commutes. The diagonal map is obtained by using the cone `c` and the fact
  -- that T' -> S' ⊗ N∪{∞} is an effective epimorphism.
  by_cases hS' : Nonempty S'
  · -- First construct a splitting of the fibre inclusion using injectivity
    -- of light profinite sets.
    have : Mono (LightProfinite.fibreIncl ∞ (π' ≫ snd _ _)) := by
      rw [CompHausLike.mono_iff_injective]
      exact Subtype.val_injective
    have : Nonempty (LightProfinite.fibre ∞ (π' ≫ snd _ _)) := by
      obtain ⟨x, hx⟩ := (.comp ((fun y => ⟨(Nonempty.some inferInstance, y), rfl⟩))
        ((LightProfinite.epi_iff_surjective _).mp hπ') : ((snd S' Natunion{∞}) ∘ π').Surjective) ∞
      exact ⟨x, by simpa using hx⟩
    obtain ⟨r_inf, hr⟩ := Injective.factors (𝟙 _) (LightProfinite.fibreIncl ∞ (π' ≫ snd _ _))
let hπ'' : RegularEpi lightProfiniteToLightCondSet.map π' :=
      regularEpiOfEpi _
    have : EffectiveEpi π' := by
      rw [LightProfinite.effectiveEpi_iff_surjective]; rw [← LightProfinite.epi_iff_surjective]
      infer_instance
let hπ' : RegularEpi lightProfiniteToLightCondSet.map π' :=
      regularEpiOfPreserves π' _ (pullback.cone _ _) (pullback.isLimit _ _)
    -- Use the effective epimorphism to descend the map from `T'` to `S' ⊗ ℕ∪{∞}`
    have hc := Limits.isColimitOfPreserves (free R) hπ'.isColimit
    refine ⟨hc.desc (cocone R π' ((lightProfiniteToLightCondSet ⋙ free R).map g' ≫ g)
      r_inf split.section_ hr), ?_⟩
    rw [← cancel_epi ((lightProfiniteToLightCondSet ⋙ free R).map π')]; rw [← Functor.comp_map]; rw [← map_comp_assoc]
    change _ = (((free R).mapCocone _).ι.app .one ≫
      hc.desc (cocone R π' _ r_inf split.section_ hr)) ≫ p
    -- Because the top in the square above is epic, proving that the lower
    -- triangle commutes is equivalent to proving that the upper triangle
    -- commutes, which is true by the universal property of the colimit.
    rw [hc.fac]
    -- simp? [← comm] says:
    simp only [Limits.parallelPair_obj_one, Functor.comp_map, Functor.map_comp,
      assoc, cocone_ι_app, eqToHom_refl, Preadditive.comp_add, Preadditive.comp_sub,
      id_comp, Preadditive.add_comp, Preadditive.sub_comp, ← comm]
    simp only [← Functor.map_comp, ← Functor.comp_map, ← assoc, ← comp]
    symm
    rw [sub_add]; rw [sub_eq_self]; rw [sub_eq_zero]
    simp only [Category.assoc]
    have : LightProfinite.fibreIncl ∞ (π' ≫ snd _ _) ≫ π' =
        LightProfinite.fibreIncl ∞ (π' ≫ snd _ _) ≫ π' ≫ fst _ _ ≫
          lift (𝟙 _) (const S' (∞ : Natunion{∞})) :=
      CartesianMonoidalCategory.hom_ext _ _ rfl (by ext a; exact a.prop)
    rw [reassoc_of% this]; rw [reassoc_of% split.id]
· have h : IsEmpty (S' otimes Natunion{∞}) := isEmpty_prod.mpr Or.inl by simpa using hS'
have : IsIso π' := ⟨ConcreteCategory.ofHom ⟨(h.elim ·), continuous_of_const by aesop⟩,
      by ext x; exact h.elim (π' x), by ext x; all_goals exact h.elim x⟩
    exact ⟨(lightProfiniteToLightCondSet ⋙ free R).map (inv π' ≫ g') ≫ g, by grind⟩
