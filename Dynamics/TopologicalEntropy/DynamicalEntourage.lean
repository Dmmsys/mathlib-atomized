/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.UniformSpace.Basic

/-!
# Dynamical entourages

Bowen-Dinaburg's definition of topological entropy of a transformation `T` in a metric space
`(X, d)` relies on the so-called dynamical balls. These balls are sets
`B (x, ε, n) = { y | ∀ k < n, d(T^[k] x, T^[k] y) < ε }`.

We implement Bowen-Dinaburg's definitions in the more general context of uniform spaces. Dynamical
balls are replaced by what we call dynamical entourages. This file collects all general lemmas
about these objects.

## Main definitions

- `dynEntourage`: dynamical entourage associated with a given transformation `T`, entourage `U`
  and time `n`.

## Tags

entropy

## TODO

Add product of entourages.

In the context of (pseudo-e)metric spaces, relate the usual definition of dynamical balls with
these dynamical entourages.
-/

@[expose] public section

namespace Dynamics

open Prod Set UniformSpace
open scoped SetRel Topology Uniformity

variable {X : Type*} {T : X -> X} {U V : SetRel X X} {m n : Nat} {x y : X}

/--
Definition of `dynEntourage` / `dynEntourage` 的定义

English:
definition dynEntourage
  signature: (T : X -> X) (U : SetRel X X) (n : Nat)
  body: ⋂ k < n, (map T T)^[k] ⁻¹' U

中文:
定义 dynEntourage
  签名: (T : X -> X) (U : SetRel X X) (n : 自然数)
  定义体: ⋂ k < n, (map T T)^[k] ⁻¹' U
-/
def dynEntourage (T : X -> X) (U : SetRel X X) (n : Nat) : SetRel X X :=
  ⋂ k < n, (map T T)^[k] ⁻¹' U

/--
lemma `dynEntourage_eq_inter_Ico` / 引理 `dynEntourage_eq_inter_Ico`

English:
lemma dynEntourage_eq_inter_Ico
  given: (T : X -> X) (U : SetRel X X) (n : Nat)
  proof: by
  simp [dynEntourage]

中文:
引理 dynEntourage_eq_inter_Ico
  条件: (T : X -> X) (U : SetRel X X) (n : 自然数)
  证明: by
  simp [dynEntourage]

Depends on / 依赖: dynEntourage
-/
lemma dynEntourage_eq_inter_Ico (T : X -> X) (U : SetRel X X) (n : Nat) :
    dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U := by
  simp [dynEntourage]

/--
lemma `mem_dynEntourage` / 引理 `mem_dynEntourage`

English:
lemma mem_dynEntourage
  statement: (x, y) in dynEntourage T U n ↔ forall k < n, (T^[k] x, T^[k] y) in U
  proof: by
  simp [dynEntourage]

中文:
引理 mem_dynEntourage
  结论: (x, y) in dynEntourage T U n ↔ 对任意 k < n, (T^[k] x, T^[k] y) in U
  证明: by
  simp [dynEntourage]

Depends on / 依赖: dynEntourage
-/
lemma mem_dynEntourage : (x, y) in dynEntourage T U n ↔ forall k < n, (T^[k] x, T^[k] y) in U := by
  simp [dynEntourage]

/--
lemma `mem_ball_dynEntourage` / 引理 `mem_ball_dynEntourage`

English:
lemma mem_ball_dynEntourage
  proof: by
  simp only [ball, mem_preimage, mem_dynEntourage]

中文:
引理 mem_ball_dynEntourage
  证明: by
  simp only [ball, mem_preimage, mem_dynEntourage]

Depends on / 依赖: mem_dynEntourage, mem_preimage
-/
lemma mem_ball_dynEntourage :
    y in ball x (dynEntourage T U n) ↔ forall k < n, T^[k] y in ball (T^[k] x) U := by
  simp only [ball, mem_preimage, mem_dynEntourage]

/--
lemma `dynEntourage_mem_uniformity` / 引理 `dynEntourage_mem_uniformity`

English:
lemma dynEntourage_mem_uniformity
  statement: [UniformSpace X] (h : UniformContinuous T)
  proof: by
  rw [dynEntourage_eq_inter_Ico T U n]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iInter_coe_set, mem_Ico, Nat.zero_le, true_and] at ih ⊢
    rw [Set.biInter_lt_succ]
    apply Filter.inter_mem ih
    rw [map_iterate T T n]
    exact uniformContinuous_def.1 (UniformContin

中文:
引理 dynEntourage_mem_uniformity
  结论: [UniformSpace X] (h : UniformContinuous T)
  证明: by
  rw [dynEntourage_eq_inter_Ico T U n]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iInter_coe_set, mem_Ico, Nat.zero_le, true_and] at ih ⊢
    rw [Set.biInter_lt_succ]
    apply Filter.inter_mem ih
    rw [map_iterate T T n]
    exact uniformContinuous_def.1 (UniformContin

Depends on / 依赖: Filter, Filter.inter_mem, Nat.zero_le, Set.biInter_lt_succ, U_uni, UniformContinuous, UniformContinuous.iterate, biInter_lt_succ, dynEntourage_eq_inter_Ico, iInter_coe_set, inter_mem, iterate, map_iterate, mem_Ico, true_and, uniformContinuous_def, zero_le
-/
lemma dynEntourage_mem_uniformity [UniformSpace X] (h : UniformContinuous T)
    (U_uni : U in 𝓤 X) (n : Nat) :
    dynEntourage T U n in 𝓤 X := by
  rw [dynEntourage_eq_inter_Ico T U n]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iInter_coe_set, mem_Ico, Nat.zero_le, true_and] at ih ⊢
    rw [Set.biInter_lt_succ]
    apply Filter.inter_mem ih
    rw [map_iterate T T n]
    exact uniformContinuous_def.1 (UniformContinuous.iterate T n h) U U_uni

/--
lemma `ball_dynEntourage_mem_nhds` / 引理 `ball_dynEntourage_mem_nhds`

English:
lemma ball_dynEntourage_mem_nhds
  statement: [UniformSpace X] (h : Continuous T)
  proof: by
  rw [dynEntourage_eq_inter_Ico T U n]; rw [ball_iInter]; rw [Filter.iInter_mem]; rw [Subtype.forall]
  intro k _
  simp only [map_iterate, _root_.ball_preimage]
  exact (h.iterate k).continuousAt.preimage_mem_nhds (ball_mem_nhds (T^[k] x) U_uni)

中文:
引理 ball_dynEntourage_mem_nhds
  结论: [UniformSpace X] (h : Continuous T)
  证明: by
  rw [dynEntourage_eq_inter_Ico T U n]; rw [ball_iInter]; rw [Filter.iInter_mem]; rw [Subtype.forall]
  intro k _
  simp only [map_iterate, _root_.ball_preimage]
  exact (h.iterate k).continuousAt.preimage_mem_nhds (ball_mem_nhds (T^[k] x) U_uni)

Depends on / 依赖: Filter, Filter.iInter_mem, Subtype, Subtype.forall, U_uni, _root_, _root_.ball_preimage, ball_iInter, ball_mem_nhds, ball_preimage, continuousAt, continuousAt.preimage_mem_nhds, dynEntourage_eq_inter_Ico, h.iterate, iInter_mem, iterate, map_iterate, preimage_mem_nhds
-/
lemma ball_dynEntourage_mem_nhds [UniformSpace X] (h : Continuous T)
    (U_uni : U in 𝓤 X) (n : Nat) (x : X) :
    ball x (dynEntourage T U n) in 𝓝 x := by
  rw [dynEntourage_eq_inter_Ico T U n]; rw [ball_iInter]; rw [Filter.iInter_mem]; rw [Subtype.forall]
  intro k _
  simp only [map_iterate, _root_.ball_preimage]
  exact (h.iterate k).continuousAt.preimage_mem_nhds (ball_mem_nhds (T^[k] x) U_uni)

/--
Instance `isRefl_dynEntourage` / 实例 `isRefl_dynEntourage`

English:
instance isRefl_dynEntourage
  signature: [U.IsRefl]
  body: by
  simp only [dynEntourage, map_iterate]
  infer_instance

中文:
实例 isRefl_dynEntourage
  签名: [U.IsRefl]
  定义体: by
  simp only [dynEntourage, map_iterate]
  infer_instance

Depends on / 依赖: dynEntourage, infer_instance, map_iterate
-/
instance isRefl_dynEntourage [U.IsRefl] : (dynEntourage T U n).IsRefl := by
  simp only [dynEntourage, map_iterate]
  infer_instance

/--
Instance `isSymm_dynEntourage` / 实例 `isSymm_dynEntourage`

English:
instance isSymm_dynEntourage
  signature: [U.IsSymm]
  body: by
  simp only [dynEntourage, map_iterate]
  infer_instance

中文:
实例 isSymm_dynEntourage
  签名: [U.IsSymm]
  定义体: by
  simp only [dynEntourage, map_iterate]
  infer_instance

Depends on / 依赖: dynEntourage, infer_instance, map_iterate
-/
instance isSymm_dynEntourage [U.IsSymm] : (dynEntourage T U n).IsSymm := by
  simp only [dynEntourage, map_iterate]
  infer_instance

/--
lemma `dynEntourage_comp_subset` / 引理 `dynEntourage_comp_subset`

English:
lemma dynEntourage_comp_subset
  given: (T : X -> X) (U V : SetRel X X) (n : Nat)
  proof: by
  simp only [dynEntourage, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [SetRel.comp, mem_iInter, mem_preimage, map_apply, mem_ofPred_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)

中文:
引理 dynEntourage_comp_subset
  条件: (T : X -> X) (U V : SetRel X X) (n : 自然数)
  证明: by
  simp only [dynEntourage, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [SetRel.comp, mem_iInter, mem_preimage, map_apply, mem_ofPred_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)

Depends on / 依赖: SetRel, SetRel.comp, dynEntourage, map_apply, map_iterate, mem_ball_comp, mem_iInter, mem_ofPred_eq, mem_preimage, subset_iInter_iff, xy_comp
-/
lemma dynEntourage_comp_subset (T : X -> X) (U V : SetRel X X) (n : Nat) :
    (dynEntourage T U n) ○ (dynEntourage T V n) subseteq dynEntourage T (U ○ V) n := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [SetRel.comp, mem_iInter, mem_preimage, map_apply, mem_ofPred_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)

/--
lemma `_root_.isOpen.dynEntourage` / 引理 `_root_.isOpen.dynEntourage`

English:
lemma _root_.isOpen.dynEntourage
  statement: [TopologicalSpace X] {T : X -> X} (T_cont : Continuous T)
  proof: by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k => ?_
  exact U_open.preimage ((T_cont.prodMap T_cont).iterate k)

中文:
引理 _root_.isOpen.dynEntourage
  结论: [TopologicalSpace X] {T : X -> X} (T_cont : Continuous T)
  证明: by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k => ?_
  exact U_open.preimage ((T_cont.prodMap T_cont).iterate k)

Depends on / 依赖: T_cont, T_cont.prodMap, U_open, U_open.preimage, dynEntourage_eq_inter_Ico, isOpen_iInter_of_finite, iterate, preimage, prodMap
-/
lemma _root_.isOpen.dynEntourage [TopologicalSpace X] {T : X -> X} (T_cont : Continuous T)
    (U_open : IsOpen U) (n : Nat) :
    IsOpen (dynEntourage T U n) := by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k => ?_
  exact U_open.preimage ((T_cont.prodMap T_cont).iterate k)

/--
lemma `dynEntourage_monotone` / 引理 `dynEntourage_monotone`

English:
lemma dynEntourage_monotone
  given: (T : X -> X) (n : Nat)
  proof: fun _ _ h => iInter₂_mono fun _ _ => preimage_mono h

中文:
引理 dynEntourage_monotone
  条件: (T : X -> X) (n : 自然数)
  证明: fun _ _ h => iInter₂_mono fun _ _ => preimage_mono h

Depends on / 依赖: preimage_mono
-/
lemma dynEntourage_monotone (T : X -> X) (n : Nat) :
    Monotone (fun U : SetRel X X => dynEntourage T U n) :=
  fun _ _ h => iInter₂_mono fun _ _ => preimage_mono h

/--
lemma `dynEntourage_antitone` / 引理 `dynEntourage_antitone`

English:
lemma dynEntourage_antitone
  given: (T : X -> X) (U : SetRel X X)
  proof: fun m n m_n => iInter₂_mono' fun k k_m => by use k, lt_of_lt_of_le k_m m_n

@[gcongr]

中文:
引理 dynEntourage_antitone
  条件: (T : X -> X) (U : SetRel X X)
  证明: fun m n m_n => iInter₂_mono' fun k k_m => by use k, lt_of_lt_of_le k_m m_n

@[gcongr]

Depends on / 依赖: lt_of_lt_of_le
-/
lemma dynEntourage_antitone (T : X -> X) (U : SetRel X X) :
    Antitone (fun n : Nat => dynEntourage T U n) :=
  fun m n m_n => iInter₂_mono' fun k k_m => by use k, lt_of_lt_of_le k_m m_n

@[gcongr]
/--
lemma `dynEntourage_mono` / 引理 `dynEntourage_mono`

English:
lemma dynEntourage_mono
  given: (hUV : U subseteq V) (hmn : m <= n)
  statement: dynEntourage T U n subseteq dynEntourage T V m
  proof: (dynEntourage_monotone _ _ hUV).trans (dynEntourage_antitone _ _ hmn)

中文:
引理 dynEntourage_mono
  条件: (hUV : U subseteq V) (hmn : m <= n)
  结论: dynEntourage T U n subseteq dynEntourage T V m
  证明: (dynEntourage_monotone _ _ hUV).trans (dynEntourage_antitone _ _ hmn)

Depends on / 依赖: dynEntourage_antitone, dynEntourage_monotone
-/
lemma dynEntourage_mono (hUV : U subseteq V) (hmn : m <= n) : dynEntourage T U n subseteq dynEntourage T V m :=
  (dynEntourage_monotone _ _ hUV).trans (dynEntourage_antitone _ _ hmn)

/--
lemma `dynEntourage_zero` / 引理 `dynEntourage_zero`

English:
lemma dynEntourage_zero
  statement: dynEntourage T U 0 = univ
  proof: by simp [dynEntourage]

中文:
引理 dynEntourage_zero
  结论: dynEntourage T U 0 = univ
  证明: by simp [dynEntourage]
-/
@[simp] lemma dynEntourage_zero : dynEntourage T U 0 = univ := by simp [dynEntourage]
/--
lemma `dynEntourage_one` / 引理 `dynEntourage_one`

English:
lemma dynEntourage_one
  statement: dynEntourage T U 1 = U
  proof: by simp [dynEntourage]

@[simp]

中文:
引理 dynEntourage_one
  结论: dynEntourage T U 1 = U
  证明: by simp [dynEntourage]

@[simp]
-/
@[simp] lemma dynEntourage_one : dynEntourage T U 1 = U := by simp [dynEntourage]

@[simp]
/--
lemma `dynEntourage_univ` / 引理 `dynEntourage_univ`

English:
lemma dynEntourage_univ
  given: {T : X -> X} {n : Nat}
  proof: by simp [dynEntourage]

中文:
引理 dynEntourage_univ
  条件: {T : X -> X} {n : 自然数}
  证明: by simp [dynEntourage]

Depends on / 依赖: dynEntourage
-/
lemma dynEntourage_univ {T : X -> X} {n : Nat} :
    dynEntourage T univ n = univ := by simp [dynEntourage]

/--
lemma `mem_ball_dynEntourage_comp` / 引理 `mem_ball_dynEntourage_comp`

English:
lemma mem_ball_dynEntourage_comp
  statement: (T : X -> X) (n : Nat) {U : SetRel X X} [U.IsSymm]
  proof: by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry] at z_Bx
  exact dynEntourage_comp_subset T U U n (mem_ball_comp z_By z_Bx)

中文:
引理 mem_ball_dynEntourage_comp
  结论: (T : X -> X) (n : 自然数) {U : SetRel X X} [U.IsSymm]
  证明: by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry] at z_Bx
  exact dynEntourage_comp_subset T U U n (mem_ball_comp z_By z_Bx)

Depends on / 依赖: dynEntourage_comp_subset, mem_ball_comp, mem_ball_symmetry, z_Bx, z_By
-/
lemma mem_ball_dynEntourage_comp (T : X -> X) (n : Nat) {U : SetRel X X} [U.IsSymm]
    (x y : X) (h : (ball x (dynEntourage T U n) inter ball y (dynEntourage T U n)).Nonempty) :
    x in ball y (dynEntourage T (U ○ U) n) := by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry] at z_Bx
  exact dynEntourage_comp_subset T U U n (mem_ball_comp z_By z_Bx)

/--
lemma `_root_.Function.Semiconj.preimage_dynEntourage` / 引理 `_root_.Function.Semiconj.preimage_dynEntourage`

English:
lemma _root_.Function.Semiconj.preimage_dynEntourage
  statement: {Y : Type*} {S : X -> X} {T : Y -> Y} {φ : X -> Y}
  proof: by
  rw [dynEntourage]; rw [preimage_iInter₂]
  refine iInter₂_congr fun k _ => ?_
  rw [← preimage_comp]; rw [← preimage_comp]; rw [map_iterate S S k]; rw [map_iterate T T k]; rw [map_comp_map]; rw [map_comp_map]; rw [(Function.Semiconj.iterate_right h k).comp_eq]

中文:
引理 _root_.Function.Semiconj.preimage_dynEntourage
  结论: {Y : 类型} {S : X -> X} {T : Y -> Y} {φ : X -> Y}
  证明: by
  rw [dynEntourage]; rw [preimage_iInter₂]
  refine iInter₂_congr fun k _ => ?_
  rw [← preimage_comp]; rw [← preimage_comp]; rw [map_iterate S S k]; rw [map_iterate T T k]; rw [map_comp_map]; rw [map_comp_map]; rw [(Function.Semiconj.iterate_right h k).comp_eq]

Depends on / 依赖: Function, Function.Semiconj.iterate_right, Semiconj, comp_eq, dynEntourage, iterate_right, map_comp_map, map_iterate, preimage_comp
-/
lemma _root_.Function.Semiconj.preimage_dynEntourage {Y : Type*} {S : X -> X} {T : Y -> Y} {φ : X -> Y}
    (h : Function.Semiconj φ S T) (U : Set (Y × Y)) (n : Nat) :
    (map φ φ) ⁻¹' (dynEntourage T U n) = dynEntourage S ((map φ φ) ⁻¹' U) n := by
  rw [dynEntourage]; rw [preimage_iInter₂]
  refine iInter₂_congr fun k _ => ?_
  rw [← preimage_comp]; rw [← preimage_comp]; rw [map_iterate S S k]; rw [map_iterate T T k]; rw [map_comp_map]; rw [map_comp_map]; rw [(Function.Semiconj.iterate_right h k).comp_eq]

end Dynamics
