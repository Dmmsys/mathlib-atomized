/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Topology.Category.Profinite.Product
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Preliminaries for Nöbeling's theorem

This file constructs basic objects and results concerning them that are needed in the proof of
Nöbeling's theorem, which is in `Mathlib/Topology/Category/Profinite/Nobeling/Induction.lean`.
See the section docstrings for more information.

## Proof idea

We follow the proof of theorem 5.4 in [scholze2019condensed], in which the idea is to embed `S` in
a product of `I` copies of `Bool` for some sufficiently large `I`, and then to choose a
well-ordering on `I` and use ordinal induction over that well-order. Here we can let `I` be
the set of clopen subsets of `S` since `S` is totally separated.

The above means it suffices to prove the following statement: For a closed subset `C` of `I → Bool`,
the `ℤ`-module `LocallyConstant C ℤ` is free.

For `i : I`, let `e C i : LocallyConstant C ℤ` denote the map `fun f ↦ (if f.val i then 1 else 0)`.

The basis will consist of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be written
as linear combinations of lexicographically smaller products. We call this set `GoodProducts C`.

What is proved by ordinal induction (in
`Mathlib/Topology/Category/Profinite/Nobeling/ZeroLimit.lean` and
`Mathlib/Topology/Category/Profinite/Nobeling/Successor.lean`) is that this set is linearly
independent. The fact that it spans is proved directly in
`Mathlib/Topology/Category/Profinite/Nobeling/Span.lean`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

open CategoryTheory ContinuousMap Limits Opposite Submodule

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I -> Bool))

section Projections
/-!
## Projection maps

The purpose of this section is twofold.

Firstly, in the proof that the set `GoodProducts C` spans the whole module `LocallyConstant C ℤ`,
we need to project `C` down to finite discrete subsets and write `C` as a cofiltered limit of those.

Secondly, in the inductive argument, we need to project `C` down to "smaller" sets satisfying the
inductive hypothesis.

In this section we define the relevant projection maps and prove some compatibility results.

### Main definitions

* Let `J : I → Prop`. Then `Proj J : (I → Bool) → (I → Bool)` is the projection mapping everything
  that satisfies `J i` to itself, and everything else to `false`.

* The image of `C` under `Proj J` is denoted `π C J` and the corresponding map `C → π C J` is called
  `ProjRestrict`. If `J` implies `K` we have a map `ProjRestricts : π C K → π C J`.

* `spanCone_isLimit` establishes that when `C` is compact, it can be written as a limit of its
  images under the maps `Proj (· ∈ s)` where `s : Finset I`.
-/

variable (J K L : I -> Prop) [forall i, Decidable (J i)] [forall i, Decidable (K i)] [forall i, Decidable (L i)]

/--
Definition of `Proj` / `Proj` 的定义

English:
definition Proj
  signature: : (I -> Bool) -> (I -> Bool)
  body: fun c i => if J i then c i else false

@[simp]

中文:
定义 Proj
  签名: : (I -> 布尔) -> (I -> 布尔)
  定义体: fun c i => if J i then c i else false

@[simp]
-/
def Proj : (I -> Bool) -> (I -> Bool) :=
  fun c i => if J i then c i else false

@[simp]
/--
theorem `continuous_proj` / 定理 `continuous_proj`

English:
theorem continuous_proj
  proof: by
  dsimp +unfoldPartialApp [Proj]
  apply continuous_pi
  intro i
  split <;> fun_prop

中文:
定理 continuous_proj
  证明: by
  dsimp +unfoldPartialApp [Proj]
  apply continuous_pi
  intro i
  split <;> fun_prop

Depends on / 依赖: continuous_pi, fun_prop, unfoldPartialApp
-/
theorem continuous_proj :
    Continuous (Proj J : (I -> Bool) -> (I -> Bool)) := by
  dsimp +unfoldPartialApp [Proj]
  apply continuous_pi
  intro i
  split <;> fun_prop

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : Set (I -> Bool)
  body: (Proj J) '' C

中文:
定义 π
  签名: : Set (I -> 布尔)
  定义体: (Proj J) '' C
-/
def π : Set (I -> Bool) := (Proj J) '' C

/-- The restriction of `Proj π J` to a subset, mapping to its image. -/
@[simps!]
/--
Definition of `ProjRestrict` / `ProjRestrict` 的定义

English:
definition ProjRestrict
  signature: : C -> π C J
  body: Set.MapsTo.restrict (Proj J) _ _ (Set.mapsTo_image _ _)

@[simp]

中文:
定义 ProjRestrict
  签名: : C -> π C J
  定义体: Set.MapsTo.restrict (Proj J) _ _ (Set.mapsTo_image _ _)

@[simp]

Depends on / 依赖: MapsTo, Set.MapsTo.restrict, Set.mapsTo_image, mapsTo_image, restrict
-/
def ProjRestrict : C -> π C J :=
  Set.MapsTo.restrict (Proj J) _ _ (Set.mapsTo_image _ _)

@[simp]
/--
theorem `continuous_projRestrict` / 定理 `continuous_projRestrict`

English:
theorem continuous_projRestrict
  statement: Continuous (ProjRestrict C J)
  proof: Continuous.restrict _ (continuous_proj _)

中文:
定理 continuous_projRestrict
  结论: Continuous (ProjRestrict C J)
  证明: Continuous.restrict _ (continuous_proj _)

Depends on / 依赖: Continuous, Continuous.restrict, continuous_proj, restrict
-/
theorem continuous_projRestrict : Continuous (ProjRestrict C J) :=
  Continuous.restrict _ (continuous_proj _)

/--
theorem `proj_eq_self` / 定理 `proj_eq_self`

English:
theorem proj_eq_self
  given: {x : I -> Bool} (h : forall i, x i != false -> J i)
  statement: Proj J x = x
  proof: by
  ext i
  simp only [Proj, ite_eq_left_iff]
  contrapose!
  simpa only [ne_comm] using h i

中文:
定理 proj_eq_self
  条件: {x : I -> 布尔} (h : 对任意 i, x i != false -> J i)
  结论: Proj J x = x
  证明: by
  ext i
  simp only [Proj, ite_eq_left_iff]
  contrapose!
  simpa only [ne_comm] using h i

Depends on / 依赖: contrapose, ite_eq_left_iff, ne_comm
-/
theorem proj_eq_self {x : I -> Bool} (h : forall i, x i != false -> J i) : Proj J x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff]
  contrapose!
  simpa only [ne_comm] using h i

/--
theorem `proj_prop_eq_self` / 定理 `proj_prop_eq_self`

English:
theorem proj_prop_eq_self
  given: (hh : forall i x, x in C -> x i != false -> J i)
  statement: π C J = C
  proof: by
  ext x
  refine ⟨fun ⟨y, hy, h⟩ => ?_, fun h => ⟨x, h, ?_⟩⟩
  · rwa [← h, proj_eq_self]; exact (hh · y hy)
  · rw [proj_eq_self]; exact (hh · x h)

中文:
定理 proj_prop_eq_self
  条件: (hh : 对任意 i x, x in C -> x i != false -> J i)
  结论: π C J = C
  证明: by
  ext x
  refine ⟨fun ⟨y, hy, h⟩ => ?_, fun h => ⟨x, h, ?_⟩⟩
  · rwa [← h, proj_eq_self]; exact (hh · y hy)
  · rw [proj_eq_self]; exact (hh · x h)

Depends on / 依赖: proj_eq_self
-/
theorem proj_prop_eq_self (hh : forall i x, x in C -> x i != false -> J i) : π C J = C := by
  ext x
  refine ⟨fun ⟨y, hy, h⟩ => ?_, fun h => ⟨x, h, ?_⟩⟩
  · rwa [← h, proj_eq_self]; exact (hh · y hy)
  · rw [proj_eq_self]; exact (hh · x h)

/--
theorem `proj_comp_of_subset` / 定理 `proj_comp_of_subset`

English:
theorem proj_comp_of_subset
  given: (h : forall i, J i -> K i)
  statement: (Proj J ∘ Proj K) =
  proof: by
  ext x i; dsimp [Proj]; simp_all

中文:
定理 proj_comp_of_subset
  条件: (h : 对任意 i, J i -> K i)
  结论: (Proj J ∘ Proj K) =
  证明: by
  ext x i; dsimp [Proj]; simp_all
-/
theorem proj_comp_of_subset (h : forall i, J i -> K i) : (Proj J ∘ Proj K) =
    (Proj J : (I -> Bool) -> (I -> Bool)) := by
  ext x i; dsimp [Proj]; simp_all

/--
theorem `proj_eq_of_subset` / 定理 `proj_eq_of_subset`

English:
theorem proj_eq_of_subset
  given: (h : forall i, J i -> K i)
  statement: π (π C K) J = π C J
  proof: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := h
    refine ⟨z, hz, (?_ : _ = (Proj J ∘ Proj K) z)⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy, rfl⟩ := h
    dsimp [π]
    rw [← Set.image_comp]
    refine ⟨y, hy, ?_⟩
    rw [proj_comp_of_subset J K h]

中文:
定理 proj_eq_of_subset
  条件: (h : 对任意 i, J i -> K i)
  结论: π (π C K) J = π C J
  证明: by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := h
    refine ⟨z, hz, (?_ : _ = (Proj J ∘ Proj K) z)⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy, rfl⟩ := h
    dsimp [π]
    rw [← Set.image_comp]
    refine ⟨y, hy, ?_⟩
    rw [proj_comp_of_subset J K h]

Depends on / 依赖: Set.image_comp, image_comp, proj_comp_of_subset
-/
theorem proj_eq_of_subset (h : forall i, J i -> K i) : π (π C K) J = π C J := by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := h
    refine ⟨z, hz, (?_ : _ = (Proj J ∘ Proj K) z)⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy, rfl⟩ := h
    dsimp [π]
    rw [← Set.image_comp]
    refine ⟨y, hy, ?_⟩
    rw [proj_comp_of_subset J K h]

variable {J K L}

/-- A variant of `ProjRestrict` with domain of the form `π C K` -/
@[simps!]
/--
Definition of `ProjRestricts` / `ProjRestricts` 的定义

English:
definition ProjRestricts
  signature: (h : forall i, J i -> K i)
  body: Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (π C K) J

@[simp]

中文:
定义 ProjRestricts
  签名: (h : 对任意 i, J i -> K i)
  定义体: Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (π C K) J

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.setCongr, ProjRestrict, proj_eq_of_subset, setCongr
-/
def ProjRestricts (h : forall i, J i -> K i) : π C K -> π C J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (π C K) J

@[simp]
/--
theorem `continuous_projRestricts` / 定理 `continuous_projRestricts`

English:
theorem continuous_projRestricts
  given: (h : forall i, J i -> K i)
  statement: Continuous (ProjRestricts C h)
  proof: Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

中文:
定理 continuous_projRestricts
  条件: (h : 对任意 i, J i -> K i)
  结论: Continuous (ProjRestricts C h)
  证明: Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

Depends on / 依赖: Continuous, Continuous.comp, Homeomorph, Homeomorph.continuous, continuous, continuous_projRestrict
-/
theorem continuous_projRestricts (h : forall i, J i -> K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

/--
theorem `surjective_projRestricts` / 定理 `surjective_projRestricts`

English:
theorem surjective_projRestricts
  given: (h : forall i, J i -> K i)
  statement: Function.Surjective (ProjRestricts C h)
  proof: (Homeomorph.surjective _).comp (Set.surjective_mapsTo_image_restrict _ _)

中文:
定理 surjective_projRestricts
  条件: (h : 对任意 i, J i -> K i)
  结论: Function.Surjective (ProjRestricts C h)
  证明: (Homeomorph.surjective _).comp (Set.surjective_mapsTo_image_restrict _ _)

Depends on / 依赖: Homeomorph, Homeomorph.surjective, Set.surjective_mapsTo_image_restrict, surjective, surjective_mapsTo_image_restrict
-/
theorem surjective_projRestricts (h : forall i, J i -> K i) : Function.Surjective (ProjRestricts C h) :=
  (Homeomorph.surjective _).comp (Set.surjective_mapsTo_image_restrict _ _)

set_option backward.isDefEq.respectTransparency.types false in
variable (J) in
/--
theorem `projRestricts_eq_id` / 定理 `projRestricts_eq_id`

English:
theorem projRestricts_eq_id
  statement: ProjRestricts C (fun i (h : J i) => h) = id
  proof: by
  ext ⟨x, y, hy, rfl⟩ i
  simp +contextual only [π, Proj, ProjRestricts_coe, id_eq, if_true]

中文:
定理 projRestricts_eq_id
  结论: ProjRestricts C (fun i (h : J i) => h) = id
  证明: by
  ext ⟨x, y, hy, rfl⟩ i
  simp +contextual only [π, Proj, ProjRestricts_coe, id_eq, if_true]

Depends on / 依赖: ProjRestricts_coe, contextual, id_eq, if_true
-/
theorem projRestricts_eq_id : ProjRestricts C (fun i (h : J i) => h) = id := by
  ext ⟨x, y, hy, rfl⟩ i
  simp +contextual only [π, Proj, ProjRestricts_coe, id_eq, if_true]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `projRestricts_eq_comp` / 定理 `projRestricts_eq_comp`

English:
theorem projRestricts_eq_comp
  given: (hJK : forall i, J i -> K i) (hKL : forall i, K i -> L i)
  proof: by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe]
  simp_all

中文:
定理 projRestricts_eq_comp
  条件: (hJK : 对任意 i, J i -> K i) (hKL : 对任意 i, K i -> L i)
  证明: by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe]
  simp_all

Depends on / 依赖: Function, Function.comp_apply, ProjRestricts_coe, comp_apply
-/
theorem projRestricts_eq_comp (hJK : forall i, J i -> K i) (hKL : forall i, K i -> L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i => hKL i ∘ hJK i) := by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe]
  simp_all

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `projRestricts_comp_projRestrict` / 定理 `projRestricts_comp_projRestrict`

English:
theorem projRestricts_comp_projRestrict
  given: (h : forall i, J i -> K i)
  proof: by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  simp_all

中文:
定理 projRestricts_comp_projRestrict
  条件: (h : 对任意 i, J i -> K i)
  证明: by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  simp_all

Depends on / 依赖: Function, Function.comp_apply, ProjRestrict_coe, ProjRestricts_coe, comp_apply
-/
theorem projRestricts_comp_projRestrict (h : forall i, J i -> K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  simp_all

variable (J)

/--
Definition of `iso_map` / `iso_map` 的定义

English:
definition iso_map
  signature: : C(π C J, (IndexFunctor.obj C J))
  body: ⟨fun x => ⟨fun i => x.val i.val, by
    rcases x with ⟨x, y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    ext ⟨i, hi⟩
    simp [precomp, Proj, hi]⟩, by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
    exact (continuous_apply i.val).comp continuous_subtype_val⟩

中文:
定义 iso_map
  签名: : C(π C J, (IndexFunctor.obj C J))
  定义体: ⟨fun x => ⟨fun i => x.val i.val, by
    rcases x with ⟨x, y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    ext ⟨i, hi⟩
    simp [precomp, Proj, hi]⟩, by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
    exact (continuous_apply i.val).comp continuous_subtype_val⟩

Depends on / 依赖: Continuous, Continuous.subtype_mk, continuous_apply, continuous_pi, continuous_subtype_val, i.val, precomp, subtype_mk, x.val
-/
def iso_map : C(π C J, (IndexFunctor.obj C J)) :=
  ⟨fun x => ⟨fun i => x.val i.val, by
    rcases x with ⟨x, y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    ext ⟨i, hi⟩
    simp [precomp, Proj, hi]⟩, by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
    exact (continuous_apply i.val).comp continuous_subtype_val⟩

/--
lemma `iso_map_bijective` / 引理 `iso_map_bijective`

English:
lemma iso_map_bijective
  statement: Function.Bijective (iso_map C J)
  proof: by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · ext i
    rw [Subtype.ext_iff] at h
    by_cases hi : J i
    · exact congr_fun h ⟨i, hi⟩
    · rcases a with ⟨_, c, hc, rfl⟩
      rcases b with ⟨_, d, hd, rfl⟩
      simp only [Proj, if_neg hi]
  · refine ⟨⟨fun i => if hi : J i then a.val ⟨i, hi⟩ else

中文:
引理 iso_map_bijective
  结论: Function.Bijective (iso_map C J)
  证明: by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · ext i
    rw [Subtype.ext_iff] at h
    by_cases hi : J i
    · exact congr_fun h ⟨i, hi⟩
    · rcases a with ⟨_, c, hc, rfl⟩
      rcases b with ⟨_, d, hd, rfl⟩
      simp only [Proj, if_neg hi]
  · refine ⟨⟨fun i => if hi : J i then a.val ⟨i, hi⟩ else

Depends on / 依赖: Subtype, Subtype.ext_iff, a.val, congr_fun, dif_pos, ext_iff, i.prop, if_neg
-/
lemma iso_map_bijective : Function.Bijective (iso_map C J) := by
  refine ⟨fun a b h => ?_, fun a => ?_⟩
  · ext i
    rw [Subtype.ext_iff] at h
    by_cases hi : J i
    · exact congr_fun h ⟨i, hi⟩
    · rcases a with ⟨_, c, hc, rfl⟩
      rcases b with ⟨_, d, hd, rfl⟩
      simp only [Proj, if_neg hi]
  · refine ⟨⟨fun i => if hi : J i then a.val ⟨i, hi⟩ else false, ?_⟩, ?_⟩
    · rcases a with ⟨_, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · ext i
      exact dif_pos i.prop

variable {C}

/--
For a given compact subset `C` of `I → Bool`, `spanFunctor` is the functor from the poset of finsets
of `I` to `Profinite`, sending a finite subset set `J` to the image of `C` under the projection
`Proj J`.
-/
noncomputable
/--
Definition of `spanFunctor` / `spanFunctor` 的定义

English:
definition spanFunctor
  signature: [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C)
  body: @Profinite.of (π C (· in (unop s))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := @CompHausLike.ofHom _ _ _ (_) (_) (_) (_) (_) (_) (_) (_)
    ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by simp only [projRestric

中文:
定义 spanFunctor
  签名: [对任意 (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C)
  定义体: @Profinite.of (π C (· in (unop s))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := @CompHausLike.ofHom _ _ _ (_) (_) (_) (_) (_) (_) (_) (_)
    ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by simp only [projRestric

Depends on / 依赖: Profinite, Profinite.of
-/
def spanFunctor [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C) :
    (Finset I)ᵒᵖ ⥤ Profinite.{u} where
  obj s := @Profinite.of (π C (· in (unop s))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := @CompHausLike.ofHom _ _ _ (_) (_) (_) (_) (_) (_) (_) (_)
    ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by simp only [projRestricts_eq_id C (· in (unop J))]; rfl
  map_comp _ _ := by rw [← CompHausLike.ofHom_comp]; congr; dsimp; rw [projRestricts_eq_comp]

/-- The limit cone on `spanFunctor` with point `C`. -/
noncomputable
/--
Definition of `spanCone` / `spanCone` 的定义

English:
definition spanCone
  signature: [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C)
  body: @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app s := ConcreteCategory.ofHom ⟨ProjRestrict C (· in unop s), continuous_projRestrict _ _⟩
    naturality := by
      intro X Y h
      simp only [Functor.const_obj_map,
        ← projRestricts_comp_projRestrict C (leOfHom h.u

中文:
定义 spanCone
  签名: [对任意 (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C)
  定义体: @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app s := ConcreteCategory.ofHom ⟨ProjRestrict C (· in unop s), continuous_projRestrict _ _⟩
    naturality := by
      intro X Y h
      simp only [Functor.const_obj_map,
        ← projRestricts_comp_projRestrict C (leOfHom h.u

Depends on / 依赖: Profinite, Profinite.of, isCompact_iff_compactSpace
-/
def spanCone [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C) :
    Cone (spanFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app s := ConcreteCategory.ofHom ⟨ProjRestrict C (· in unop s), continuous_projRestrict _ _⟩
    naturality := by
      intro X Y h
      simp only [Functor.const_obj_map,
        ← projRestricts_comp_projRestrict C (leOfHom h.unop)]
      rfl }

/-- The isomorphism `spanFunctor hC ≅ indexFunctor hC` when `hC : IsCompact C`. -/
@[simps!]
/--
Definition of `spanFunctorIsoIndexFunctor` / `spanFunctorIsoIndexFunctor` 的定义

English:
definition spanFunctorIsoIndexFunctor
  body: NatIso.ofComponents
    (fun s => CompHausLike.isoOfBijective (ConcreteCategory.ofHom (iso_map C (· in unop s)))
      (iso_map_bijective C (· in unop s))) (by
        rintro ⟨s⟩ ⟨t⟩ ⟨⟨⟨f⟩⟩⟩
        ext x
        have : iso_map C (· in t) ∘ ProjRestricts C f =
            IndexFunctor.map C f ∘ iso_

中文:
定义 spanFunctorIsoIndexFunctor
  定义体: NatIso.ofComponents
    (fun s => CompHausLike.isoOfBijective (ConcreteCategory.ofHom (iso_map C (· in unop s)))
      (iso_map_bijective C (· in unop s))) (by
        rintro ⟨s⟩ ⟨t⟩ ⟨⟨⟨f⟩⟩⟩
        ext x
        have : iso_map C (· in t) ∘ ProjRestricts C f =
            IndexFunctor.map C f ∘ iso_

Depends on / 依赖: CompHausLike, CompHausLike.isoOfBijective, ConcreteCategory, ConcreteCategory.ofHom, IndexFunctor, IndexFunctor.map, NatIso, NatIso.ofComponents, ProjRestricts, congr_fun, dif_pos, i.prop, isoOfBijective, iso_map, iso_map_bijective, ofComponents
-/
noncomputable def spanFunctorIsoIndexFunctor
    [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C) :
    spanFunctor hC ≅ indexFunctor hC :=
  NatIso.ofComponents
    (fun s => CompHausLike.isoOfBijective (ConcreteCategory.ofHom (iso_map C (· in unop s)))
      (iso_map_bijective C (· in unop s))) (by
        rintro ⟨s⟩ ⟨t⟩ ⟨⟨⟨f⟩⟩⟩
        ext x
        have : iso_map C (· in t) ∘ ProjRestricts C f =
            IndexFunctor.map C f ∘ iso_map C (· in s) := by
          ext _ i; exact dif_pos i.prop
        exact congr_fun this x)

/-- `spanCone` is a limit cone. -/
noncomputable
/--
Definition of `spanCone_isLimit` / `spanCone_isLimit` 的定义

English:
definition spanCone_isLimit
  signature: [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C)
  body: IsLimit.postcomposeHomEquiv (spanFunctorIsoIndexFunctor hC) _
    (IsLimit.ofIsoLimit (indexCone_isLimit hC) (Cone.ext (Iso.refl _) (fun ⟨s⟩ => by
      ext
      have : iso_map C (· in s) ∘ ProjRestrict C (· in s) = IndexFunctor.π_app C (· in s) := by
        ext _ i; exact dif_pos i.prop
      exa

中文:
定义 spanCone_isLimit
  签名: [对任意 (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C)
  定义体: IsLimit.postcomposeHomEquiv (spanFunctorIsoIndexFunctor hC) _
    (IsLimit.ofIsoLimit (indexCone_isLimit hC) (Cone.ext (Iso.refl _) (fun ⟨s⟩ => by
      ext
      have : iso_map C (· in s) ∘ ProjRestrict C (· in s) = IndexFunctor.π_app C (· in s) := by
        ext _ i; exact dif_pos i.prop
      exa

Depends on / 依赖: Cone.ext, IndexFunctor, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, ProjRestrict, congr_fun, dif_pos, i.prop, indexCone_isLimit, iso_map, ofIsoLimit, postcomposeHomEquiv, spanFunctorIsoIndexFunctor, this.symm
-/
def spanCone_isLimit [forall (s : Finset I) (i : I), Decidable (i in s)] (hC : IsCompact C) :
    CategoryTheory.Limits.IsLimit (spanCone hC) :=
  IsLimit.postcomposeHomEquiv (spanFunctorIsoIndexFunctor hC) _
    (IsLimit.ofIsoLimit (indexCone_isLimit hC) (Cone.ext (Iso.refl _) (fun ⟨s⟩ => by
      ext
      have : iso_map C (· in s) ∘ ProjRestrict C (· in s) = IndexFunctor.π_app C (· in s) := by
        ext _ i; exact dif_pos i.prop
      exact congr_fun this.symm _)))

end Projections

section Products
/-!
## Defining the basis

Our proposed basis consists of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be
written as linear combinations of lexicographically smaller products. See below for the definition
of `e`.

### Main definitions

* For `i : I`, we let `e C i : LocallyConstant C ℤ` denote the map
  `fun f ↦ (if f.val i then 1 else 0)`.

* `Products I` is the type of lists of decreasing elements of `I`, so a typical element is
  `[i₁, i₂,..., iᵣ]` with `i₁ > i₂ > ... > iᵣ`.

* `Products.eval C` is the `C`-evaluation of a list. It takes a term `[i₁, i₂,..., iᵣ] : Products I`
  and returns the actual product `e C i₁ ··· e C iᵣ : LocallyConstant C ℤ`.

* `GoodProducts C` is the set of `Products I` such that their `C`-evaluation cannot be written as
  a linear combination of evaluations of lexicographically smaller lists.

### Main results

* `Products.evalFacProp` and `Products.evalFacProps` establish the fact that `Products.eval`
  interacts nicely with the projection maps from the previous section.

* `GoodProducts.span_iff_products`: the good products span `LocallyConstant C ℤ` iff all the
  products span `LocallyConstant C ℤ`.
-/

/--
Definition of `e` / `e` 的定义

English:
definition e
  signature: (i : I)
  body: fun f => (if f.val i then 1 else 0)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    exact (continuous_of_discreteTopology (f := fun (a : Bool) => (if a then (1 : Int) else 0))).comp
      ((continuous_apply i).comp continuous_subtype_val)

中文:
定义 e
  签名: (i : I)
  定义体: fun f => (if f.val i then 1 else 0)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    exact (continuous_of_discreteTopology (f := fun (a : Bool) => (if a then (1 : Int) else 0))).comp
      ((continuous_apply i).comp continuous_subtype_val)

Depends on / 依赖: f.val
-/
def e (i : I) : LocallyConstant C Int where
  toFun := fun f => (if f.val i then 1 else 0)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    exact (continuous_of_discreteTopology (f := fun (a : Bool) => (if a then (1 : Int) else 0))).comp
      ((continuous_apply i).comp continuous_subtype_val)

variable [LinearOrder I]

/--
Definition of `Products` / `Products` 的定义

English:
definition Products
  signature: (I : Type*) [LinearOrder I]
  body: {l : List I // l.IsChain (· > ·)}

中文:
定义 Products
  签名: (I : 类型) [LinearOrder I]
  定义体: {l : List I // l.IsChain (· > ·)}

Depends on / 依赖: IsChain, l.IsChain
-/
def Products (I : Type*) [LinearOrder I] := {l : List I // l.IsChain (· > ·)}

namespace Products

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder (Products I)
  body: inferInstanceAs (LinearOrder {l : List I // l.IsChain (· > ·)})

中文:
实例 :
  签名: LinearOrder (Products I)
  定义体: inferInstanceAs (LinearOrder {l : List I // l.IsChain (· > ·)})

Depends on / 依赖: IsChain, LinearOrder, l.IsChain
-/
instance : LinearOrder (Products I) :=
  inferInstanceAs (LinearOrder {l : List I // l.IsChain (· > ·)})

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lt_iff_lex_lt` / 定理 `lt_iff_lex_lt`

English:
theorem lt_iff_lex_lt
  given: (l m : Products I)
  statement: l < m ↔ List.Lex (· < ·) l.val m.val
  proof: by
  simp

中文:
定理 lt_iff_lex_lt
  条件: (l m : Products I)
  结论: l < m ↔ List.Lex (· < ·) l.val m.val
  证明: by
  simp
-/
theorem lt_iff_lex_lt (l m : Products I) : l < m ↔ List.Lex (· < ·) l.val m.val := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedLT
  signature: I] : WellFoundedLT (Products I)
  body: by
  have : (· < · : Products I -> _ -> _) = (fun l m => List.Lex (· < ·) l.val m.val) := by
    ext; exact lt_iff_lex_lt _ _
  rw [WellFoundedLT]; rw [this]
  dsimp [Products]
  rw [(by rfl : (· > · : I -> _) = flip (· < ·))]
  infer_instance

中文:
实例 [WellFoundedLT
  签名: I] : WellFoundedLT (Products I)
  定义体: by
  have : (· < · : Products I -> _ -> _) = (fun l m => List.Lex (· < ·) l.val m.val) := by
    ext; exact lt_iff_lex_lt _ _
  rw [WellFoundedLT]; rw [this]
  dsimp [Products]
  rw [(by rfl : (· > · : I -> _) = flip (· < ·))]
  infer_instance

Depends on / 依赖: List.Lex, Products, WellFoundedLT, infer_instance, l.val, lt_iff_lex_lt, m.val
-/
instance [WellFoundedLT I] : WellFoundedLT (Products I) := by
  have : (· < · : Products I -> _ -> _) = (fun l m => List.Lex (· < ·) l.val m.val) := by
    ext; exact lt_iff_lex_lt _ _
  rw [WellFoundedLT]; rw [this]
  dsimp [Products]
  rw [(by rfl : (· > · : I -> _) = flip (· < ·))]
  infer_instance

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (l : Products I)
  body: (l.1.map (e C)).prod

中文:
定义 eval
  签名: (l : Products I)
  定义体: (l.1.map (e C)).prod
-/
def eval (l : Products I) := (l.1.map (e C)).prod

/--
Definition of `isGood` / `isGood` 的定义

English:
definition isGood
  signature: (l : Products I)
  body: l.eval C ∉ Submodule.span Int ((Products.eval C) '' {m | m < l})

中文:
定义 isGood
  签名: (l : Products I)
  定义体: l.eval C ∉ Submodule.span Int ((Products.eval C) '' {m | m < l})

Depends on / 依赖: Products, Products.eval, Submodule, Submodule.span, l.eval
-/
def isGood (l : Products I) : Prop :=
  l.eval C ∉ Submodule.span Int ((Products.eval C) '' {m | m < l})

/--
theorem `rel_head!_of_mem` / 定理 `rel_head!_of_mem`

English:
theorem rel_head!_of_mem
  given: [Inhabited I] {i : I} {l : Products I} (hi : i in l.val)
  proof: List.Pairwise.head!_le l.2.sortedGT.sortedGE.pairwise hi

中文:
定理 rel_head!_of_mem
  条件: [Inhabited I] {i : I} {l : Products I} (hi : i in l.val)
  证明: List.Pairwise.head!_le l.2.sortedGT.sortedGE.pairwise hi

Depends on / 依赖: List.Pairwise.head, Pairwise, pairwise, sortedGE, sortedGT, sortedGT.sortedGE.pairwise
-/
theorem rel_head!_of_mem [Inhabited I] {i : I} {l : Products I} (hi : i in l.val) :
    i <= l.val.head! :=
  List.Pairwise.head!_le l.2.sortedGT.sortedGE.pairwise hi

/--
theorem `head!_le_of_lt` / 定理 `head!_le_of_lt`

English:
theorem head!_le_of_lt
  given: [Inhabited I] {q l : Products I} (h : q < l) (hq : q.val != [])
  proof: List.head!_le_of_lt l.val q.val h hq

中文:
定理 head!_le_of_lt
  条件: [Inhabited I] {q l : Products I} (h : q < l) (hq : q.val != [])
  证明: List.head!_le_of_lt l.val q.val h hq

Depends on / 依赖: List.head, _le_of_lt, l.val, q.val
-/
theorem head!_le_of_lt [Inhabited I] {q l : Products I} (h : q < l) (hq : q.val != []) :
    q.val.head! <= l.val.head! :=
  List.head!_le_of_lt l.val q.val h hq

end Products

/--
Definition of `GoodProducts` / `GoodProducts` 的定义

English:
definition GoodProducts
  body: {l : Products I | l.isGood C}

中文:
定义 GoodProducts
  定义体: {l : Products I | l.isGood C}

Depends on / 依赖: Products, isGood, l.isGood
-/
def GoodProducts := {l : Products I | l.isGood C}

namespace GoodProducts

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (l : {l : Products I // l.isGood C})
  body: Products.eval C l.1

中文:
定义 eval
  签名: (l : {l : Products I // l.isGood C})
  定义体: Products.eval C l.1

Depends on / 依赖: Products, Products.eval
-/
def eval (l : {l : Products I // l.isGood C}) : LocallyConstant C Int :=
  Products.eval C l.1

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Function.Injective (eval C)
  proof: by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  dsimp [eval] at h
  by_contra! hne
  cases hne.lt_or_gt with
  | inl h' => apply hb; rw [← h]; exact Submodule.subset_span ⟨a, h', rfl⟩
  | inr h' => apply ha; rw [h]; exact Submodule.subset_span ⟨b, h', rfl⟩

中文:
定理 injective
  结论: Function.Injective (eval C)
  证明: by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  dsimp [eval] at h
  by_contra! hne
  cases hne.lt_or_gt with
  | inl h' => apply hb; rw [← h]; exact Submodule.subset_span ⟨a, h', rfl⟩
  | inr h' => apply ha; rw [h]; exact Submodule.subset_span ⟨b, h', rfl⟩

Depends on / 依赖: Submodule, Submodule.subset_span, hne.lt_or_gt, lt_or_gt, subset_span
-/
theorem injective : Function.Injective (eval C) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  dsimp [eval] at h
  by_contra! hne
  cases hne.lt_or_gt with
  | inl h' => apply hb; rw [← h]; exact Submodule.subset_span ⟨a, h', rfl⟩
  | inr h' => apply ha; rw [h]; exact Submodule.subset_span ⟨b, h', rfl⟩

/--
Definition of `range` / `range` 的定义

English:
definition range
  body: Set.range (GoodProducts.eval C)

中文:
定义 range
  定义体: Set.range (GoodProducts.eval C)

Depends on / 依赖: GoodProducts, GoodProducts.eval, Set.range
-/
def range := Set.range (GoodProducts.eval C)

/-- The type of good products is equivalent to its image. -/
noncomputable
/--
Definition of `equiv_range` / `equiv_range` 的定义

English:
definition equiv_range
  signature: : GoodProducts C ≃ range C
  body: Equiv.ofInjective (eval C) (injective C)

中文:
定义 equiv_range
  签名: : GoodProducts C ≃ range C
  定义体: Equiv.ofInjective (eval C) (injective C)

Depends on / 依赖: Equiv.ofInjective, injective, ofInjective
-/
def equiv_range : GoodProducts C ≃ range C :=
  Equiv.ofInjective (eval C) (injective C)

/--
theorem `equiv_toFun_eq_eval` / 定理 `equiv_toFun_eq_eval`

English:
theorem equiv_toFun_eq_eval
  statement: (equiv_range C).toFun = Set.rangeFactorization (eval C)
  proof: rfl

中文:
定理 equiv_toFun_eq_eval
  结论: (equiv_range C).toFun = Set.rangeFactorization (eval C)
  证明: rfl
-/
theorem equiv_toFun_eq_eval : (equiv_range C).toFun = Set.rangeFactorization (eval C) := rfl

/--
theorem `linearIndependent_iff_range` / 定理 `linearIndependent_iff_range`

English:
theorem linearIndependent_iff_range
  statement: LinearIndependent Int (GoodProducts.eval C) ↔
  proof: by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C)]; rw [← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_range C)

中文:
定理 linearIndependent_iff_range
  结论: LinearIndependent 整数 (GoodProducts.eval C) ↔
  证明: by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C)]; rw [← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_range C)

Depends on / 依赖: GoodProducts, GoodProducts.eval, Set.rangeFactorization_eq, equiv_range, equiv_toFun_eq_eval, linearIndependent_equiv, rangeFactorization_eq
-/
theorem linearIndependent_iff_range : LinearIndependent Int (GoodProducts.eval C) ↔
    LinearIndependent Int (fun (p : range C) => p.1) := by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C)]; rw [← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_range C)

end GoodProducts

namespace Products

set_option backward.defeqAttrib.useBackward true in
/--
theorem `eval_eq` / 定理 `eval_eq`

English:
theorem eval_eq
  given: (l : Products I) (x : C)
  proof: by
  change LocallyConstant.evalMonoidHom x (l.eval C) = _
  rw [eval]; rw [map_list_prod]
  split_ifs with h
  · simp only [List.map_map]
    apply List.prod_eq_one
    simp only [List.mem_map, Function.comp_apply]
    rintro _ ⟨i, hi, rfl⟩
    exact if_pos (h i hi)
  · simp only [List.map_map, Lis

中文:
定理 eval_eq
  条件: (l : Products I) (x : C)
  证明: by
  change LocallyConstant.evalMonoidHom x (l.eval C) = _
  rw [eval]; rw [map_list_prod]
  split_ifs with h
  · simp only [List.map_map]
    apply List.prod_eq_one
    simp only [List.mem_map, Function.comp_apply]
    rintro _ ⟨i, hi, rfl⟩
    exact if_pos (h i hi)
  · simp only [List.map_map, Lis

Depends on / 依赖: Function, Function.comp_apply, List.map_map, List.mem_map, List.prod_eq_one, List.prod_eq_zero_iff, LocallyConstant, LocallyConstant.evalMonoidHom, comp_apply, convert, evalMonoidHom, if_pos, ite_eq_right_iff, l.eval, map_list_prod, map_map, mem_map, one_ne_zero, prod_eq_one, prod_eq_zero_iff
-/
theorem eval_eq (l : Products I) (x : C) :
    l.eval C x = if forall i, i in l.val -> (x.val i = true) then 1 else 0 := by
  change LocallyConstant.evalMonoidHom x (l.eval C) = _
  rw [eval]; rw [map_list_prod]
  split_ifs with h
  · simp only [List.map_map]
    apply List.prod_eq_one
    simp only [List.mem_map, Function.comp_apply]
    rintro _ ⟨i, hi, rfl⟩
    exact if_pos (h i hi)
  · simp only [List.map_map, List.prod_eq_zero_iff, List.mem_map, Function.comp_apply]
    push Not at h
    convert! h with i
    dsimp [LocallyConstant.evalMonoidHom, e]
    simp only [ite_eq_right_iff, one_ne_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `evalFacProp` / 定理 `evalFacProp`

English:
theorem evalFacProp
  statement: {l : Products I} (J : I -> Prop)
  proof: by
  ext x
  dsimp only [ProjRestrict, Function.comp_apply]
  rw [Products.eval_eq]; rw [Products.eval_eq]
  simp +contextual [h, Proj]

中文:
定理 evalFacProp
  结论: {l : Products I} (J : I -> 命题)
  证明: by
  ext x
  dsimp only [ProjRestrict, Function.comp_apply]
  rw [Products.eval_eq]; rw [Products.eval_eq]
  simp +contextual [h, Proj]

Depends on / 依赖: Function, Function.comp_apply, Products, Products.eval_eq, ProjRestrict, comp_apply, contextual, eval_eq
-/
theorem evalFacProp {l : Products I} (J : I -> Prop)
    (h : forall a, a in l.val -> J a) [forall j, Decidable (J j)] :
    l.eval (π C J) ∘ ProjRestrict C J = l.eval C := by
  ext x
  dsimp only [ProjRestrict, Function.comp_apply]
  rw [Products.eval_eq]; rw [Products.eval_eq]
  simp +contextual [h, Proj]

/--
theorem `evalFacProps` / 定理 `evalFacProps`

English:
theorem evalFacProps
  statement: {l : Products I} (J K : I -> Prop)
  proof: by
  have : l.eval (π C J) ∘ Homeomorph.setCongr (proj_eq_of_subset C J K hJK) =
      l.eval (π (π C K) J) := by
    ext; simp [Homeomorph.setCongr, Products.eval_eq]
  rw [ProjRestricts]; rw [← Function.comp_assoc]; rw [this]; rw [← evalFacProp (π C K) J h]

中文:
定理 evalFacProps
  结论: {l : Products I} (J K : I -> 命题)
  证明: by
  have : l.eval (π C J) ∘ Homeomorph.setCongr (proj_eq_of_subset C J K hJK) =
      l.eval (π (π C K) J) := by
    ext; simp [Homeomorph.setCongr, Products.eval_eq]
  rw [ProjRestricts]; rw [← Function.comp_assoc]; rw [this]; rw [← evalFacProp (π C K) J h]

Depends on / 依赖: Function, Function.comp_assoc, Homeomorph, Homeomorph.setCongr, Products, Products.eval_eq, ProjRestricts, comp_assoc, evalFacProp, eval_eq, l.eval, proj_eq_of_subset, setCongr
-/
theorem evalFacProps {l : Products I} (J K : I -> Prop)
    (h : forall a, a in l.val -> J a) [forall j, Decidable (J j)] [forall j, Decidable (K j)]
    (hJK : forall i, J i -> K i) :
    l.eval (π C J) ∘ ProjRestricts C hJK = l.eval (π C K) := by
  have : l.eval (π C J) ∘ Homeomorph.setCongr (proj_eq_of_subset C J K hJK) =
      l.eval (π (π C K) J) := by
    ext; simp [Homeomorph.setCongr, Products.eval_eq]
  rw [ProjRestricts]; rw [← Function.comp_assoc]; rw [this]; rw [← evalFacProp (π C K) J h]

/--
theorem `prop_of_isGood` / 定理 `prop_of_isGood`

English:
theorem prop_of_isGood
  statement: {l : Products I} (J : I -> Prop) [forall j, Decidable (J j)]
  proof: by
  intro i hi
  by_contra h'
  apply h
  suffices eval (π C J) l = 0 by
    rw [this]
    exact Submodule.zero_mem _
  ext ⟨_, _, _, rfl⟩
  rw [eval_eq]; rw [if_neg fun h => ?_]; rw [LocallyConstant.zero_apply]
  simpa [Proj, h'] using h i hi

中文:
定理 prop_of_isGood
  结论: {l : Products I} (J : I -> 命题) [对任意 j, Decidable (J j)]
  证明: by
  intro i hi
  by_contra h'
  apply h
  suffices eval (π C J) l = 0 by
    rw [this]
    exact Submodule.zero_mem _
  ext ⟨_, _, _, rfl⟩
  rw [eval_eq]; rw [if_neg fun h => ?_]; rw [LocallyConstant.zero_apply]
  simpa [Proj, h'] using h i hi

Depends on / 依赖: LocallyConstant, LocallyConstant.zero_apply, Submodule, Submodule.zero_mem, eval_eq, if_neg, zero_apply, zero_mem
-/
theorem prop_of_isGood {l : Products I} (J : I -> Prop) [forall j, Decidable (J j)]
    (h : l.isGood (π C J)) : forall a, a in l.val -> J a := by
  intro i hi
  by_contra h'
  apply h
  suffices eval (π C J) l = 0 by
    rw [this]
    exact Submodule.zero_mem _
  ext ⟨_, _, _, rfl⟩
  rw [eval_eq]; rw [if_neg fun h => ?_]; rw [LocallyConstant.zero_apply]
  simpa [Proj, h'] using h i hi

end Products

/--
theorem `GoodProducts.span_iff_products` / 定理 `GoodProducts.span_iff_products`

English:
theorem GoodProducts.span_iff_products
  given: [WellFoundedLT I]
  proof: by
  refine ⟨fun h => le_trans h (span_mono (fun a ⟨b, hb⟩ => ⟨b.val, hb⟩)), fun h => le_trans h ?_⟩
  rw [span_le]
  rintro f ⟨l, rfl⟩
  let L : Products I -> Prop := fun m => m.eval C in span Int (Set.range (GoodProducts.eval C))
  suffices L l by assumption
  apply IsWellFounded.induction (· < · 

中文:
定理 GoodProducts.span_iff_products
  条件: [WellFoundedLT I]
  证明: by
  refine ⟨fun h => le_trans h (span_mono (fun a ⟨b, hb⟩ => ⟨b.val, hb⟩)), fun h => le_trans h ?_⟩
  rw [span_le]
  rintro f ⟨l, rfl⟩
  let L : Products I -> Prop := fun m => m.eval C in span Int (Set.range (GoodProducts.eval C))
  suffices L l by assumption
  apply IsWellFounded.induction (· < · 

Depends on / 依赖: GoodProducts, GoodProducts.eval, IsWellFounded, IsWellFounded.induction, Products, Products.eval, Products.isGood, Set.range, b.val, isGood, l.isGood, le_trans, m.eval, not_not, span_le, span_mono, subset_span, subseteq
-/
theorem GoodProducts.span_iff_products [WellFoundedLT I] :
    ⊤ <= Submodule.span Int (Set.range (eval C)) ↔
      ⊤ <= Submodule.span Int (Set.range (Products.eval C)) := by
  refine ⟨fun h => le_trans h (span_mono (fun a ⟨b, hb⟩ => ⟨b.val, hb⟩)), fun h => le_trans h ?_⟩
  rw [span_le]
  rintro f ⟨l, rfl⟩
  let L : Products I -> Prop := fun m => m.eval C in span Int (Set.range (GoodProducts.eval C))
  suffices L l by assumption
  apply IsWellFounded.induction (· < · : Products I -> Products I -> Prop)
  intro l h
  by_cases hl : l.isGood C
  · apply subset_span
    exact ⟨⟨l, hl⟩, rfl⟩
  · simp only [Products.isGood, not_not] at hl
    suffices Products.eval C '' {m | m < l} subseteq span Int (Set.range (GoodProducts.eval C)) by
      rw [← span_le] at this
      exact this hl
    rintro a ⟨m, hm, rfl⟩
    exact h m hm

end Products

variable [LinearOrder I] [WellFoundedLT I]

section Ordinal
/-!
## Relating elements of the well-order `I` with ordinals

We choose a well-ordering on `I`. This amounts to regarding `I` as an ordinal, and as such it
can be regarded as the set of all strictly smaller ordinals, allowing to apply ordinal induction.

### Main definitions

* `ord I i` is the term `i` of `I` regarded as an ordinal.

* `term I ho` is a sufficiently small ordinal regarded as a term of `I`.

* `contained C o` is a predicate saying that `C` is "small" enough in relation to the ordinal `o`
  to satisfy the inductive hypothesis.

* `P I` is the predicate on ordinals about linear independence of good products, which the rest of
  this file is spent on proving by induction.
-/

variable (I)

/--
Definition of `ord` / `ord` 的定义

English:
definition ord
  signature: (i : I)
  body: Ordinal.typein ((· < ·) : I -> I -> Prop) i

中文:
定义 ord
  签名: (i : I)
  定义体: Ordinal.typein ((· < ·) : I -> I -> Prop) i

Depends on / 依赖: Ordinal, Ordinal.typein, typein
-/
def ord (i : I) : Ordinal := Ordinal.typein ((· < ·) : I -> I -> Prop) i

/-- An ordinal regarded as a term of `I`. -/
noncomputable
/--
Definition of `term` / `term` 的定义

English:
definition term
  signature: {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop))
  body: Ordinal.enum ((· < ·) : I -> I -> Prop) ⟨o, ho⟩

中文:
定义 term
  签名: {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> 命题))
  定义体: Ordinal.enum ((· < ·) : I -> I -> Prop) ⟨o, ho⟩

Depends on / 依赖: Ordinal, Ordinal.enum
-/
def term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)) : I :=
  Ordinal.enum ((· < ·) : I -> I -> Prop) ⟨o, ho⟩

variable {I}

/--
theorem `term_ord_aux` / 定理 `term_ord_aux`

English:
theorem term_ord_aux
  given: {i : I} (ho : ord I i < Ordinal.type ((· < ·) : I -> I -> Prop))
  proof: by
  simp only [term, ord, Ordinal.enum_typein]

@[simp]

中文:
定理 term_ord_aux
  条件: {i : I} (ho : ord I i < Ordinal.type ((· < ·) : I -> I -> 命题))
  证明: by
  simp only [term, ord, Ordinal.enum_typein]

@[simp]

Depends on / 依赖: Ordinal, Ordinal.enum_typein, enum_typein
-/
theorem term_ord_aux {i : I} (ho : ord I i < Ordinal.type ((· < ·) : I -> I -> Prop)) :
    term I ho = i := by
  simp only [term, ord, Ordinal.enum_typein]

@[simp]
/--
theorem `ord_term_aux` / 定理 `ord_term_aux`

English:
theorem ord_term_aux
  given: {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop))
  proof: by
  simp only [ord, term, Ordinal.typein_enum]

中文:
定理 ord_term_aux
  条件: {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> 命题))
  证明: by
  simp only [ord, term, Ordinal.typein_enum]

Depends on / 依赖: Ordinal, Ordinal.typein_enum, typein_enum
-/
theorem ord_term_aux {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)) :
    ord I (term I ho) = o := by
  simp only [ord, term, Ordinal.typein_enum]

/--
theorem `ord_term` / 定理 `ord_term`

English:
theorem ord_term
  given: {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)) (i : I)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact term_ord_aux ho
  · subst h
    exact ord_term_aux ho

中文:
定理 ord_term
  条件: {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> 命题)) (i : I)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact term_ord_aux ho
  · subst h
    exact ord_term_aux ho

Depends on / 依赖: ord_term_aux, term_ord_aux
-/
theorem ord_term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I -> I -> Prop)) (i : I) :
    ord I i = o ↔ term I ho = i := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact term_ord_aux ho
  · subst h
    exact ord_term_aux ho

/--
Definition of `contained` / `contained` 的定义

English:
definition contained
  signature: (o : Ordinal)
  body: forall f, f in C -> forall (i : I), f i = true -> ord I i < o

中文:
定义 contained
  签名: (o : Ordinal)
  定义体: forall f, f in C -> forall (i : I), f i = true -> ord I i < o
-/
def contained (o : Ordinal) : Prop := forall f, f in C -> forall (i : I), f i = true -> ord I i < o

variable (I) in
/--
Definition of `P` / `P` 的定义

English:
definition P
  signature: (o : Ordinal)
  body: o <= Ordinal.type (· < · : I -> I -> Prop) ->
  (forall (C : Set (I -> Bool)), IsClosed C -> contained C o ->
    LinearIndependent Int (GoodProducts.eval C))

中文:
定义 P
  签名: (o : Ordinal)
  定义体: o <= Ordinal.type (· < · : I -> I -> Prop) ->
  (forall (C : Set (I -> Bool)), IsClosed C -> contained C o ->
    LinearIndependent Int (GoodProducts.eval C))

Depends on / 依赖: GoodProducts, GoodProducts.eval, IsClosed, LinearIndependent, Ordinal, Ordinal.type, contained
-/
def P (o : Ordinal) : Prop :=
  o <= Ordinal.type (· < · : I -> I -> Prop) ->
  (forall (C : Set (I -> Bool)), IsClosed C -> contained C o ->
    LinearIndependent Int (GoodProducts.eval C))

/--
theorem `Products.prop_of_isGood_of_contained` / 定理 `Products.prop_of_isGood_of_contained`

English:
theorem Products.prop_of_isGood_of_contained
  statement: {l : Products I} (o : Ordinal) (h : l.isGood C)
  proof: by
  by_contra h'
  apply h
  suffices eval C l = 0 by simp [this]
  ext x
  simp only [eval_eq, LocallyConstant.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero]
  contrapose! h'
  exact hsC x.val x.prop i (h'.1 i hi)

中文:
定理 Products.prop_of_isGood_of_contained
  结论: {l : Products I} (o : Ordinal) (h : l.isGood C)
  证明: by
  by_contra h'
  apply h
  suffices eval C l = 0 by simp [this]
  ext x
  simp only [eval_eq, LocallyConstant.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero]
  contrapose! h'
  exact hsC x.val x.prop i (h'.1 i hi)

Depends on / 依赖: LocallyConstant, LocallyConstant.coe_zero, Pi.zero_apply, coe_zero, contrapose, eval_eq, ite_eq_right_iff, one_ne_zero, x.prop, x.val, zero_apply
-/
theorem Products.prop_of_isGood_of_contained {l : Products I} (o : Ordinal) (h : l.isGood C)
    (hsC : contained C o) (i : I) (hi : i in l.val) : ord I i < o := by
  by_contra h'
  apply h
  suffices eval C l = 0 by simp [this]
  ext x
  simp only [eval_eq, LocallyConstant.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero]
  contrapose! h'
  exact hsC x.val x.prop i (h'.1 i hi)

end Ordinal

section Maps

/--
theorem `contained_eq_proj` / 定理 `contained_eq_proj`

English:
theorem contained_eq_proj
  given: (o : Ordinal) (h : contained C o)
  proof: by
  have := proj_prop_eq_self C (ord I · < o)
  simp only [ne_eq, Bool.not_eq_false, π] at this
  exact (this (fun i x hx => h x hx i)).symm

中文:
定理 contained_eq_proj
  条件: (o : Ordinal) (h : contained C o)
  证明: by
  have := proj_prop_eq_self C (ord I · < o)
  simp only [ne_eq, Bool.not_eq_false, π] at this
  exact (this (fun i x hx => h x hx i)).symm

Depends on / 依赖: Bool.not_eq_false, ne_eq, not_eq_false, proj_prop_eq_self
-/
theorem contained_eq_proj (o : Ordinal) (h : contained C o) :
    C = π C (ord I · < o) := by
  have := proj_prop_eq_self C (ord I · < o)
  simp only [ne_eq, Bool.not_eq_false, π] at this
  exact (this (fun i x hx => h x hx i)).symm

/--
theorem `isClosed_proj` / 定理 `isClosed_proj`

English:
theorem isClosed_proj
  given: (o : Ordinal) (hC : IsClosed C)
  statement: IsClosed (π C (ord I · < o))
  proof: (continuous_proj (ord I · < o)).isClosedMap C hC

中文:
定理 isClosed_proj
  条件: (o : Ordinal) (hC : IsClosed C)
  结论: IsClosed (π C (ord I · < o))
  证明: (continuous_proj (ord I · < o)).isClosedMap C hC

Depends on / 依赖: continuous_proj, isClosedMap
-/
theorem isClosed_proj (o : Ordinal) (hC : IsClosed C) : IsClosed (π C (ord I · < o)) :=
  (continuous_proj (ord I · < o)).isClosedMap C hC

/--
theorem `contained_proj` / 定理 `contained_proj`

English:
theorem contained_proj
  given: (o : Ordinal)
  statement: contained (π C (ord I · < o)) o
  proof: by
  intro x ⟨_, _, h⟩ j hj
  aesop (add simp Proj)

中文:
定理 contained_proj
  条件: (o : Ordinal)
  结论: contained (π C (ord I · < o)) o
  证明: by
  intro x ⟨_, _, h⟩ j hj
  aesop (add simp Proj)
-/
theorem contained_proj (o : Ordinal) : contained (π C (ord I · < o)) o := by
  intro x ⟨_, _, h⟩ j hj
  aesop (add simp Proj)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (ord I · < o)`. -/
@[simps!]
noncomputable
/--
Definition of `πs` / `πs` 的定义

English:
definition πs
  signature: (o : Ordinal)
  body: LocallyConstant.comapₗ Int ⟨(ProjRestrict C (ord I · < o)), (continuous_projRestrict _ _)⟩

中文:
定义 πs
  签名: (o : Ordinal)
  定义体: LocallyConstant.comapₗ Int ⟨(ProjRestrict C (ord I · < o)), (continuous_projRestrict _ _)⟩

Depends on / 依赖: LocallyConstant, LocallyConstant.comap, ProjRestrict, continuous_projRestrict
-/
def πs (o : Ordinal) : LocallyConstant (π C (ord I · < o)) Int ->ₗ[Int] LocallyConstant C Int :=
  LocallyConstant.comapₗ Int ⟨(ProjRestrict C (ord I · < o)), (continuous_projRestrict _ _)⟩

/--
theorem `coe_πs` / 定理 `coe_πs`

English:
theorem coe_πs
  given: (o : Ordinal) (f : LocallyConstant (π C (ord I · < o)) Int)
  proof: by
  rfl

中文:
定理 coe_πs
  条件: (o : Ordinal) (f : LocallyConstant (π C (ord I · < o)) 整数)
  证明: by
  rfl
-/
theorem coe_πs (o : Ordinal) (f : LocallyConstant (π C (ord I · < o)) Int) :
    πs C o f = f ∘ ProjRestrict C (ord I · < o) := by
  rfl

/--
theorem `injective_πs` / 定理 `injective_πs`

English:
theorem injective_πs
  given: (o : Ordinal)
  statement: Function.Injective (πs C o)
  proof: LocallyConstant.comap_injective ⟨_, (continuous_projRestrict _ _)⟩
    (Set.surjective_mapsTo_image_restrict _ _)

中文:
定理 injective_πs
  条件: (o : Ordinal)
  结论: Function.Injective (πs C o)
  证明: LocallyConstant.comap_injective ⟨_, (continuous_projRestrict _ _)⟩
    (Set.surjective_mapsTo_image_restrict _ _)

Depends on / 依赖: LocallyConstant, LocallyConstant.comap_injective, Set.surjective_mapsTo_image_restrict, comap_injective, continuous_projRestrict, surjective_mapsTo_image_restrict
-/
theorem injective_πs (o : Ordinal) : Function.Injective (πs C o) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestrict _ _)⟩
    (Set.surjective_mapsTo_image_restrict _ _)

/-- The `ℤ`-linear map induced by precomposition of the projection
`π C (ord I · < o₂) → π C (ord I · < o₁)` for `o₁ ≤ o₂`. -/
@[simps!]
noncomputable
/--
Definition of `πs'` / `πs'` 的定义

English:
definition πs'
  signature: {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  body: LocallyConstant.comapₗ Int ⟨(ProjRestricts C (fun _ hh => lt_of_lt_of_le hh h)),
    (continuous_projRestricts _ _)⟩

中文:
定义 πs'
  签名: {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  定义体: LocallyConstant.comapₗ Int ⟨(ProjRestricts C (fun _ hh => lt_of_lt_of_le hh h)),
    (continuous_projRestricts _ _)⟩

Depends on / 依赖: LocallyConstant, LocallyConstant.comap, ProjRestricts, continuous_projRestricts, lt_of_lt_of_le
-/
def πs' {o₁ o₂ : Ordinal} (h : o₁ <= o₂) :
    LocallyConstant (π C (ord I · < o₁)) Int ->ₗ[Int] LocallyConstant (π C (ord I · < o₂)) Int :=
  LocallyConstant.comapₗ Int ⟨(ProjRestricts C (fun _ hh => lt_of_lt_of_le hh h)),
    (continuous_projRestricts _ _)⟩

/--
theorem `coe_πs'` / 定理 `coe_πs'`

English:
theorem coe_πs'
  given: {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (f : LocallyConstant (π C (ord I · < o₁)) Int)
  proof: by
  rfl

中文:
定理 coe_πs'
  条件: {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (f : LocallyConstant (π C (ord I · < o₁)) 整数)
  证明: by
  rfl
-/
theorem coe_πs' {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (f : LocallyConstant (π C (ord I · < o₁)) Int) :
    (πs' C h f).toFun = f.toFun ∘ (ProjRestricts C (fun _ hh => lt_of_lt_of_le hh h)) := by
  rfl

/--
theorem `injective_πs'` / 定理 `injective_πs'`

English:
theorem injective_πs'
  given: {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  statement: Function.Injective (πs' C h)
  proof: LocallyConstant.comap_injective ⟨_, (continuous_projRestricts _ _)⟩
    (surjective_projRestricts _ fun _ hi => lt_of_lt_of_le hi h)

中文:
定理 injective_πs'
  条件: {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  结论: Function.Injective (πs' C h)
  证明: LocallyConstant.comap_injective ⟨_, (continuous_projRestricts _ _)⟩
    (surjective_projRestricts _ fun _ hi => lt_of_lt_of_le hi h)

Depends on / 依赖: LocallyConstant, LocallyConstant.comap_injective, comap_injective, continuous_projRestricts, lt_of_lt_of_le, surjective_projRestricts
-/
theorem injective_πs' {o₁ o₂ : Ordinal} (h : o₁ <= o₂) : Function.Injective (πs' C h) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestricts _ _)⟩
    (surjective_projRestricts _ fun _ hi => lt_of_lt_of_le hi h)

namespace Products

/--
theorem `lt_ord_of_lt` / 定理 `lt_ord_of_lt`

English:
theorem lt_ord_of_lt
  statement: {l m : Products I} {o : Ordinal} (h₁ : m < l)
  proof: List.SortedGT.lt_ord_of_lt l.2.sortedGT m.2.sortedGT h₁ h₂

中文:
定理 lt_ord_of_lt
  结论: {l m : Products I} {o : Ordinal} (h₁ : m < l)
  证明: List.SortedGT.lt_ord_of_lt l.2.sortedGT m.2.sortedGT h₁ h₂

Depends on / 依赖: List.SortedGT.lt_ord_of_lt, SortedGT, lt_ord_of_lt, sortedGT
-/
theorem lt_ord_of_lt {l m : Products I} {o : Ordinal} (h₁ : m < l)
    (h₂ : forall i in l.val, ord I i < o) : forall i in m.val, ord I i < o :=
  List.SortedGT.lt_ord_of_lt l.2.sortedGT m.2.sortedGT h₁ h₂

/--
theorem `eval_πs` / 定理 `eval_πs`

English:
theorem eval_πs
  given: {l : Products I} {o : Ordinal} (hlt : forall i in l.val, ord I i < o)
  proof: by
  simpa only [← LocallyConstant.coe_inj] using! evalFacProp C (ord I · < o) hlt

中文:
定理 eval_πs
  条件: {l : Products I} {o : Ordinal} (hlt : 对任意 i in l.val, ord I i < o)
  证明: by
  simpa only [← LocallyConstant.coe_inj] using! evalFacProp C (ord I · < o) hlt

Depends on / 依赖: LocallyConstant, LocallyConstant.coe_inj, coe_inj, evalFacProp
-/
theorem eval_πs {l : Products I} {o : Ordinal} (hlt : forall i in l.val, ord I i < o) :
    πs C o (l.eval (π C (ord I · < o))) = l.eval C := by
  simpa only [← LocallyConstant.coe_inj] using! evalFacProp C (ord I · < o) hlt

/--
theorem `eval_πs'` / 定理 `eval_πs'`

English:
theorem eval_πs'
  statement: {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  proof: by
  rw [← LocallyConstant.coe_inj]; rw [← LocallyConstant.toFun_eq_coe]
  exact evalFacProps C (fun (i : I) => ord I i < o₁) (fun (i : I) => ord I i < o₂) hlt
    (fun _ hh => lt_of_lt_of_le hh h)

中文:
定理 eval_πs'
  结论: {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  证明: by
  rw [← LocallyConstant.coe_inj]; rw [← LocallyConstant.toFun_eq_coe]
  exact evalFacProps C (fun (i : I) => ord I i < o₁) (fun (i : I) => ord I i < o₂) hlt
    (fun _ hh => lt_of_lt_of_le hh h)

Depends on / 依赖: LocallyConstant, LocallyConstant.coe_inj, LocallyConstant.toFun_eq_coe, coe_inj, evalFacProps, lt_of_lt_of_le, toFun_eq_coe
-/
theorem eval_πs' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
    (hlt : forall i in l.val, ord I i < o₁) :
    πs' C h (l.eval (π C (ord I · < o₁))) = l.eval (π C (ord I · < o₂)) := by
  rw [← LocallyConstant.coe_inj]; rw [← LocallyConstant.toFun_eq_coe]
  exact evalFacProps C (fun (i : I) => ord I i < o₁) (fun (i : I) => ord I i < o₂) hlt
    (fun _ hh => lt_of_lt_of_le hh h)

/--
theorem `eval_πs_image` / 定理 `eval_πs_image`

English:
theorem eval_πs_image
  statement: {l : Products I} {o : Ordinal}
  proof: by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs C (lt_ord_of_lt hm hl)]

中文:
定理 eval_πs_image
  结论: {l : Products I} {o : Ordinal}
  证明: by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs C (lt_ord_of_lt hm hl)]

Depends on / 依赖: Set.mem_image, Set.mem_ofPred_eq, and_congr_right, exists_congr, exists_exists_and_eq_and, lt_ord_of_lt, mem_image, mem_ofPred_eq
-/
theorem eval_πs_image {l : Products I} {o : Ordinal}
    (hl : forall i in l.val, ord I i < o) : eval C '' { m | m < l } =
    (πs C o) '' eval (π C (ord I · < o)) '' { m | m < l } := by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs C (lt_ord_of_lt hm hl)]

/--
theorem `eval_πs_image'` / 定理 `eval_πs_image'`

English:
theorem eval_πs_image'
  statement: {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  proof: by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs' C h (lt_ord_of_lt hm hl)]

中文:
定理 eval_πs_image'
  结论: {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  证明: by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs' C h (lt_ord_of_lt hm hl)]

Depends on / 依赖: Set.mem_image, Set.mem_ofPred_eq, and_congr_right, exists_congr, exists_exists_and_eq_and, lt_ord_of_lt, mem_image, mem_ofPred_eq
-/
theorem eval_πs_image' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
    (hl : forall i in l.val, ord I i < o₁) : eval (π C (ord I · < o₂)) '' { m | m < l } =
    (πs' C h) '' eval (π C (ord I · < o₁)) '' { m | m < l } := by
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs' C h (lt_ord_of_lt hm hl)]

/--
theorem `head_lt_ord_of_isGood` / 定理 `head_lt_ord_of_isGood`

English:
theorem head_lt_ord_of_isGood
  statement: [Inhabited I] {l : Products I} {o : Ordinal}
  proof: prop_of_isGood C (ord I · < o) h l.val.head! (List.head!_mem_self hn)

中文:
定理 head_lt_ord_of_isGood
  结论: [Inhabited I] {l : Products I} {o : Ordinal}
  证明: prop_of_isGood C (ord I · < o) h l.val.head! (List.head!_mem_self hn)

Depends on / 依赖: List.head, _mem_self, l.val.head, prop_of_isGood
-/
theorem head_lt_ord_of_isGood [Inhabited I] {l : Products I} {o : Ordinal}
    (h : l.isGood (π C (ord I · < o))) (hn : l.val != []) : ord I (l.val.head!) < o :=
  prop_of_isGood C (ord I · < o) h l.val.head! (List.head!_mem_self hn)

/--
theorem `isGood_mono` / 定理 `isGood_mono`

English:
theorem isGood_mono
  statement: {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  proof: by
  intro hl'
  apply hl
  rwa [eval_πs_image' C h (prop_of_isGood C _ hl), ← eval_πs' C h (prop_of_isGood C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

中文:
定理 isGood_mono
  结论: {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  证明: by
  intro hl'
  apply hl
  rwa [eval_πs_image' C h (prop_of_isGood C _ hl), ← eval_πs' C h (prop_of_isGood C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

Depends on / 依赖: Submodule, Submodule.apply_mem_span_image_iff_mem_span, apply_mem_span_image_iff_mem_span, prop_of_isGood
-/
theorem isGood_mono {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
    (hl : l.isGood (π C (ord I · < o₁))) : l.isGood (π C (ord I · < o₂)) := by
  intro hl'
  apply hl
  rwa [eval_πs_image' C h (prop_of_isGood C _ hl), ← eval_πs' C h (prop_of_isGood C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

end Products

end Maps

end Profinite.NobelingProof
