/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.Bases

/-!
# Ultrametric (nonarchimedean) uniform spaces

Ultrametric (nonarchimedean) uniform spaces are ones that generalize ultrametric spaces by
having a uniformity based on equivalence relations.

## Main definitions

In this file we define `IsUltraUniformity`, a Prop mixin typeclass.

## Main results

* `TopologicalSpace.isTopologicalBasis_clopens`: a uniform space with a nonarchimedean uniformity
  has a topological basis of clopen sets in the topology, meaning that it is topologically
  zero-dimensional.

## Implementation notes

As in the `Mathlib/Topology/UniformSpace/Defs.lean` file, we do not reuse `Mathlib/Data/Rel.lean`
but rather extend the relation properties as needed.

## TODOs

* Prove that `IsUltraUniformity` iff metrizable by `IsUltrametricDist` on a `PseudoMetricSpace`
  under a countable system/basis condition
* Generalize `IsUltrametricDist` to `IsUltrametricUniformity`
* Provide `IsUltraUniformity` for the uniformity in a `Valued` ring
* Generalize results about open/closed balls and spheres in `IsUltraUniformity` to
  combine applications for `MetricSpace.ball` and valued "balls"
* Use `IsUltraUniformity` to work with profinite/totally separated spaces

## References

* [D. Windisch, *Equivalent characterizations of non-Archimedean uniform spaces*][windisch2021]
* [A. C. M. van Rooij, *Non-Archimedean uniformities*][vanrooij1970]

-/

@[expose] public section

open Set Filter Topology
open scoped SetRel Uniformity

variable {X : Type*}

/--
lemma `IsTransitiveRel.prod_subset_trans` / 引理 `IsTransitiveRel.prod_subset_trans`

English:
lemma IsTransitiveRel.prod_subset_trans
  statement: {s : SetRel X X} {t u v : Set X} [s.IsTrans]
  proof: by
  rintro ⟨a, b⟩ hab
  simp only [mem_prod] at hab
  obtain ⟨x, hx⟩ := hu
  exact s.trans (@htu ⟨a, x⟩ ⟨hab.left, hx⟩) (@huv ⟨x, b⟩ ⟨hx, hab.right⟩)

中文:
引理 IsTransitiveRel.prod_subset_trans
  结论: {s : SetRel X X} {t u v : Set X} [s.IsTrans]
  证明: by
  rintro ⟨a, b⟩ hab
  simp only [mem_prod] at hab
  obtain ⟨x, hx⟩ := hu
  exact s.trans (@htu ⟨a, x⟩ ⟨hab.left, hx⟩) (@huv ⟨x, b⟩ ⟨hx, hab.right⟩)

Depends on / 依赖: hab.left, hab.right, mem_prod, s.trans
-/
lemma IsTransitiveRel.prod_subset_trans {s : SetRel X X} {t u v : Set X} [s.IsTrans]
    (htu : t ×ˢ u subseteq s) (huv : u ×ˢ v subseteq s) (hu : u.Nonempty) :
    t ×ˢ v subseteq s := by
  rintro ⟨a, b⟩ hab
  simp only [mem_prod] at hab
  obtain ⟨x, hx⟩ := hu
  exact s.trans (@htu ⟨a, x⟩ ⟨hab.left, hx⟩) (@huv ⟨x, b⟩ ⟨hx, hab.right⟩)

/--
lemma `IsTransitiveRel.mem_filter_prod_trans` / 引理 `IsTransitiveRel.mem_filter_prod_trans`

English:
lemma IsTransitiveRel.mem_filter_prod_trans
  statement: {s : SetRel X X} {f g h : Filter X} [g.NeBot]
  proof: Eventually.trans_prod (p := (fun x y => (x, y) in s)) (q := (fun x y => (x, y) in s))
    (r := (fun x y => (x, y) in s)) hfg hgh fun _ _ _ => s.trans

中文:
引理 IsTransitiveRel.mem_filter_prod_trans
  结论: {s : SetRel X X} {f g h : Filter X} [g.NeBot]
  证明: Eventually.trans_prod (p := (fun x y => (x, y) in s)) (q := (fun x y => (x, y) in s))
    (r := (fun x y => (x, y) in s)) hfg hgh fun _ _ _ => s.trans

Depends on / 依赖: Eventually, Eventually.trans_prod, s.trans, trans_prod
-/
lemma IsTransitiveRel.mem_filter_prod_trans {s : SetRel X X} {f g h : Filter X} [g.NeBot]
    [s.IsTrans] (hfg : s in f ×ˢ g) (hgh : s in g ×ˢ h) :
    s in f ×ˢ h :=
  Eventually.trans_prod (p := (fun x y => (x, y) in s)) (q := (fun x y => (x, y) in s))
    (r := (fun x y => (x, y) in s)) hfg hgh fun _ _ _ => s.trans

open UniformSpace

/--
lemma `ball_subset_of_mem` / 引理 `ball_subset_of_mem`

English:
lemma ball_subset_of_mem
  given: {V : SetRel X X} [V.IsTrans] {x y : X} (hy : y in ball x V)
  proof: ball_subset_of_comp_subset hy SetRel.comp_subset_self

中文:
引理 ball_subset_of_mem
  条件: {V : SetRel X X} [V.IsTrans] {x y : X} (hy : y in ball x V)
  证明: ball_subset_of_comp_subset hy SetRel.comp_subset_self

Depends on / 依赖: SetRel, SetRel.comp_subset_self, ball_subset_of_comp_subset, comp_subset_self
-/
lemma ball_subset_of_mem {V : SetRel X X} [V.IsTrans] {x y : X} (hy : y in ball x V) :
    ball y V subseteq ball x V :=
  ball_subset_of_comp_subset hy SetRel.comp_subset_self

/--
lemma `ball_eq_of_mem` / 引理 `ball_eq_of_mem`

English:
lemma ball_eq_of_mem
  given: {V : SetRel X X} [V.IsSymm] [V.IsTrans] {x y : X} (hy : y in ball x V)
  proof: by
  refine le_antisymm (ball_subset_of_mem ?_) (ball_subset_of_mem hy)
  rwa [← mem_ball_symmetry]

中文:
引理 ball_eq_of_mem
  条件: {V : SetRel X X} [V.IsSymm] [V.IsTrans] {x y : X} (hy : y in ball x V)
  证明: by
  refine le_antisymm (ball_subset_of_mem ?_) (ball_subset_of_mem hy)
  rwa [← mem_ball_symmetry]

Depends on / 依赖: ball_subset_of_mem, le_antisymm, mem_ball_symmetry
-/
lemma ball_eq_of_mem {V : SetRel X X} [V.IsSymm] [V.IsTrans] {x y : X} (hy : y in ball x V) :
    ball x V = ball y V := by
  refine le_antisymm (ball_subset_of_mem ?_) (ball_subset_of_mem hy)
  rwa [← mem_ball_symmetry]

variable [UniformSpace X]

variable (X) in
/--
Definition of `IsUltraUniformity` / `IsUltraUniformity` 的定义

English:
class IsUltraUniformity
  parameters: : Prop where
  axioms and operations (1):
    - hasBasis : (𝓤 X).HasBasis (fun s : SetRel X X => s in 𝓤 X ∧ SetRel.IsSymm s ∧ SetRel.IsTrans s) id

中文:
类 IsUltraUniformity
  参数: : 命题 where
  公理与运算 (1 个):
    - hasBasis : (𝓤 X).HasBasis (fun s : SetRel X X => s in 𝓤 X ∧ SetRel.IsSymm s ∧ SetRel.IsTrans s) id
-/
class IsUltraUniformity : Prop where
  hasBasis : (𝓤 X).HasBasis
    (fun s : SetRel X X => s in 𝓤 X ∧ SetRel.IsSymm s ∧ SetRel.IsTrans s) id

/--
lemma `IsUltraUniformity.mk_of_hasBasis` / 引理 `IsUltraUniformity.mk_of_hasBasis`

English:
lemma IsUltraUniformity.mk_of_hasBasis
  statement: {ι : Type*} {p : ι -> Prop} {s : ι -> SetRel X X}
  proof: h_basis.to_hasBasis'
    (fun i hi => ⟨s i, ⟨h_basis.mem_of_mem hi, h_symm i hi, h_trans i hi⟩, subset_rfl⟩)
    (fun _ hs => hs.1)

中文:
引理 IsUltraUniformity.mk_of_hasBasis
  结论: {ι : 类型} {p : ι -> 命题} {s : ι -> SetRel X X}
  证明: h_basis.to_hasBasis'
    (fun i hi => ⟨s i, ⟨h_basis.mem_of_mem hi, h_symm i hi, h_trans i hi⟩, subset_rfl⟩)
    (fun _ hs => hs.1)

Depends on / 依赖: h_basis, h_basis.to_hasBasis, to_hasBasis
-/
lemma IsUltraUniformity.mk_of_hasBasis {ι : Type*} {p : ι -> Prop} {s : ι -> SetRel X X}
    (h_basis : (𝓤 X).HasBasis p s) (h_symm : forall i, p i -> SetRel.IsSymm (s i))
    (h_trans : forall i, p i -> SetRel.IsTrans (s i)) :
    IsUltraUniformity X where
  hasBasis := h_basis.to_hasBasis'
    (fun i hi => ⟨s i, ⟨h_basis.mem_of_mem hi, h_symm i hi, h_trans i hi⟩, subset_rfl⟩)
    (fun _ hs => hs.1)

/--
lemma `IsUltraUniformity.mem_nhds_iff_symm_trans` / 引理 `IsUltraUniformity.mem_nhds_iff_symm_trans`

English:
lemma IsUltraUniformity.mem_nhds_iff_symm_trans
  given: [IsUltraUniformity X] {x : X} {s : Set X}
  proof: by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    rw [IsUltraUniformity.hasBasis.mem_iff'] at V_in
    obtain ⟨U, ⟨U_in, U_sym, U_trans⟩, U_sub⟩ := V_in
    refine ⟨U, U_in, U_sym, U_trans, (UniformSpace.ball_mono U_sub _).trans V_sub⟩
  · rintro ⟨V, V_in, _, _, V_sub

中文:
引理 IsUltraUniformity.mem_nhds_iff_symm_trans
  条件: [IsUltraUniformity X] {x : X} {s : Set X}
  证明: by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    rw [IsUltraUniformity.hasBasis.mem_iff'] at V_in
    obtain ⟨U, ⟨U_in, U_sym, U_trans⟩, U_sub⟩ := V_in
    refine ⟨U, U_in, U_sym, U_trans, (UniformSpace.ball_mono U_sub _).trans V_sub⟩
  · rintro ⟨V, V_in, _, _, V_sub

Depends on / 依赖: IsUltraUniformity, IsUltraUniformity.hasBasis.mem_iff, U_in, U_sub, U_sym, U_trans, UniformSpace, UniformSpace.ball_mono, UniformSpace.mem_nhds_iff, V_in, V_sub, ball_mono, hasBasis, mem_iff, mem_nhds_iff
-/
lemma IsUltraUniformity.mem_nhds_iff_symm_trans [IsUltraUniformity X] {x : X} {s : Set X} :
    s in 𝓝 x ↔ exists V in 𝓤 X, SetRel.IsSymm V ∧ SetRel.IsTrans V ∧ UniformSpace.ball x V subseteq s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  · rintro ⟨V, V_in, V_sub⟩
    rw [IsUltraUniformity.hasBasis.mem_iff'] at V_in
    obtain ⟨U, ⟨U_in, U_sym, U_trans⟩, U_sub⟩ := V_in
    refine ⟨U, U_in, U_sym, U_trans, (UniformSpace.ball_mono U_sub _).trans V_sub⟩
  · rintro ⟨V, V_in, _, _, V_sub⟩
    exact ⟨V, V_in, V_sub⟩

namespace UniformSpace

/--
lemma `isOpen_ball_of_mem_uniformity` / 引理 `isOpen_ball_of_mem_uniformity`

English:
lemma isOpen_ball_of_mem_uniformity
  given: (x : X) {V : SetRel X X} [V.IsTrans] (h' : V in 𝓤 X)
  proof: by
  rw [isOpen_iff_ball_subset]
  intro y hy
  exact ⟨V, h', ball_subset_of_mem hy⟩

中文:
引理 isOpen_ball_of_mem_uniformity
  条件: (x : X) {V : SetRel X X} [V.IsTrans] (h' : V in 𝓤 X)
  证明: by
  rw [isOpen_iff_ball_subset]
  intro y hy
  exact ⟨V, h', ball_subset_of_mem hy⟩

Depends on / 依赖: ball_subset_of_mem, isOpen_iff_ball_subset
-/
lemma isOpen_ball_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsTrans] (h' : V in 𝓤 X) :
    IsOpen (ball x V) := by
  rw [isOpen_iff_ball_subset]
  intro y hy
  exact ⟨V, h', ball_subset_of_mem hy⟩

/--
lemma `isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity` / 引理 `isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity`

English:
lemma isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity
  statement: (x : X) {V : SetRel X X} [V.IsSymm]
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_ball_subset]
exact fun y hy => ⟨V, h', fun z hyz hxz => hy V.trans hxz V.symm hyz⟩

中文:
引理 isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity
  结论: (x : X) {V : SetRel X X} [V.IsSymm]
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_ball_subset]
exact fun y hy => ⟨V, h', fun z hyz hxz => hy V.trans hxz V.symm hyz⟩

Depends on / 依赖: V.symm, V.trans, isOpen_compl_iff, isOpen_iff_ball_subset
-/
lemma isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSymm]
    [V.IsTrans] (h' : V in 𝓤 X) :
    IsClosed (ball x V) := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_ball_subset]
exact fun y hy => ⟨V, h', fun z hyz hxz => hy V.trans hxz V.symm hyz⟩

/--
lemma `isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity` / 引理 `isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity`

English:
lemma isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity
  statement: (x : X) {V : SetRel X X} [V.IsSymm]
  proof: ⟨isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity _ ‹_›, isOpen_ball_of_mem_uniformity _ ‹_›⟩

中文:
引理 isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity
  结论: (x : X) {V : SetRel X X} [V.IsSymm]
  证明: ⟨isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity _ ‹_›, isOpen_ball_of_mem_uniformity _ ‹_›⟩

Depends on / 依赖: isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity, isOpen_ball_of_mem_uniformity
-/
lemma isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity (x : X) {V : SetRel X X} [V.IsSymm]
    [V.IsTrans] (h' : V in 𝓤 X) :
    IsClopen (ball x V) :=
  ⟨isClosed_ball_of_isSymm_of_isTrans_of_mem_uniformity _ ‹_›, isOpen_ball_of_mem_uniformity _ ‹_›⟩

variable [IsUltraUniformity X]

/--
lemma `nhds_basis_clopens` / 引理 `nhds_basis_clopens`

English:
lemma nhds_basis_clopens
  given: (x : X)
  proof: by
  refine (nhds_basis_uniformity' (IsUltraUniformity.hasBasis)).to_hasBasis' ?_ ?_
  · intro V ⟨hV, h_symm, h_trans⟩
    exact ⟨ball x V, ⟨mem_ball_self _ hV,
      isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity _ hV⟩, le_rfl⟩
  · rintro u ⟨hx, hu⟩
    simp [hu.right.mem_nhds_iff, hx]

中文:
引理 nhds_basis_clopens
  条件: (x : X)
  证明: by
  refine (nhds_basis_uniformity' (IsUltraUniformity.hasBasis)).to_hasBasis' ?_ ?_
  · intro V ⟨hV, h_symm, h_trans⟩
    exact ⟨ball x V, ⟨mem_ball_self _ hV,
      isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity _ hV⟩, le_rfl⟩
  · rintro u ⟨hx, hu⟩
    simp [hu.right.mem_nhds_iff, hx]

Depends on / 依赖: IsUltraUniformity, IsUltraUniformity.hasBasis, h_symm, h_trans, hasBasis, hu.right.mem_nhds_iff, isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity, le_rfl, mem_ball_self, mem_nhds_iff, nhds_basis_uniformity, to_hasBasis
-/
lemma nhds_basis_clopens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x in s ∧ IsClopen s) id := by
  refine (nhds_basis_uniformity' (IsUltraUniformity.hasBasis)).to_hasBasis' ?_ ?_
  · intro V ⟨hV, h_symm, h_trans⟩
    exact ⟨ball x V, ⟨mem_ball_self _ hV,
      isClopen_ball_of_isSymm_of_isTrans_of_mem_uniformity _ hV⟩, le_rfl⟩
  · rintro u ⟨hx, hu⟩
    simp [hu.right.mem_nhds_iff, hx]

/--
lemma `_root_.TopologicalSpace.isTopologicalBasis_clopens` / 引理 `_root_.TopologicalSpace.isTopologicalBasis_clopens`

English:
lemma _root_.TopologicalSpace.isTopologicalBasis_clopens
  proof: .of_hasBasis_nhds fun x => by simpa [and_comm] using nhds_basis_clopens x

中文:
引理 _root_.TopologicalSpace.isTopologicalBasis_clopens
  证明: .of_hasBasis_nhds fun x => by simpa [and_comm] using nhds_basis_clopens x

Depends on / 依赖: and_comm, nhds_basis_clopens, of_hasBasis_nhds
-/
lemma _root_.TopologicalSpace.isTopologicalBasis_clopens :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
  .of_hasBasis_nhds fun x => by simpa [and_comm] using nhds_basis_clopens x

end UniformSpace
