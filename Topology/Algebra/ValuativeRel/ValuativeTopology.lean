/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.WithZeroTopology

/-!
# The topology on a ring induced by a valuation

In this file, we define the non-Archimedean topology induced by a valuation on a ring.

## Main definitions

* If we have both `[ValuativeRel R]` and `[TopologicalSpace R]`, then writing
  `[IsValuativeTopology R]` ensures that the topology on `R` agrees with the one induced by the
  valuation.
* `ValuativeRel.uniformSpace`: The uniform structure introduced by a `ValuativeRel`.

*NOTE* (2026-03-17): The `Valued` instance on a ring `R` would be
replaced by `[ValuativeRel R] [UniformSpace R] [IsValuativeTopology R] [IsUniformAddGroup R]`
(or `[ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]` when the uniformity is
not relevant). Additional input `(v : Valuation R Γ₀) [v.Compatible]` can be introduced whenever
a specific compatible valuation is chosen.

The canonical way to introduce the topological structure from a chosen valuation is:
1. First define the `ValuativeRel` structure using `ValuativeRel.ofValuation`;
2. Then define the `UniformSpace` structure using `ValuativeRel.uniformSpace`.
-/

public section

open scoped Topology Uniformity
open Set Filter Valuation ValuativeRel MonoidWithZeroHom ValueGroup₀ ValueGroupWithZero

noncomputable section

variable (R : Type*) [Ring R] [ValuativeRel R]

variable {R} in
/--
lemma `Valuation.exists_setOfPred_restrict_le_iff` / 引理 `Valuation.exists_setOfPred_restrict_le_iff`

English:
lemma Valuation.exists_setOfPred_restrict_le_iff
  statement: {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  proof: by
  refine ⟨fun ⟨r, hr⟩ => ⟨r.mapEquiv (orderMonoidIso v).symm, ?_⟩,
    fun ⟨r, hr⟩ => ⟨r.mapEquiv (orderMonoidIso v), ?_⟩⟩
  all_goals convert! hr; simp

@[deprecated (since := "2026-07-09")]
alias Valuation.exists_setOf_restrict_le_iff := Valuation.exists_setOfPred_restrict_le_iff

中文:
引理 赋值.存在_setOfPred_restrict_le_iff
  结论: {Γ₀ : 类型} [带零LinearOrderedComm群 Γ₀]
  证明: by
  refine ⟨fun ⟨r, hr⟩ => ⟨r.mapEquiv (orderMonoidIso v).symm, ?_⟩,
    fun ⟨r, hr⟩ => ⟨r.mapEquiv (orderMonoidIso v), ?_⟩⟩
  all_goals convert! hr; simp

@[deprecated (since := "2026-07-09")]
alias Valuation.exists_setOf_restrict_le_iff := Valuation.exists_setOfPred_restrict_le_iff

Depends on / 依赖: all_goals, convert, mapEquiv, orderMonoidIso, r.mapEquiv
-/
lemma Valuation.exists_setOfPred_restrict_le_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] (x : R) (s : Set R) :
    (exists γ : (ValueGroup₀ (.ofClass v))ˣ, {z | v.restrict (z - x) < γ.val} subseteq s) ↔
    exists γ : (ValueGroupWithZero R)ˣ, {a | valuation R (a - x) < γ} subseteq s := by
  refine ⟨fun ⟨r, hr⟩ => ⟨r.mapEquiv (orderMonoidIso v).symm, ?_⟩,
    fun ⟨r, hr⟩ => ⟨r.mapEquiv (orderMonoidIso v), ?_⟩⟩
  all_goals convert! hr; simp

@[deprecated (since := "2026-07-09")]
alias Valuation.exists_setOf_restrict_le_iff := Valuation.exists_setOfPred_restrict_le_iff

/--
Definition of `IsValuativeTopology` / `IsValuativeTopology` 的定义

English:
class IsValuativeTopology
  parameters: [TopologicalSpace R]
  axioms and operations (1):
    - mem_nhds_iff({s : Set R} {x : R}) : s in 𝓝 (x : R) ↔ exists γ : (ValueGroupWithZero R)ˣ, (x + ·) '' { z | valuation _ z < γ } subseteq s

中文:
类 是赋值拓扑
  参数: [拓扑空间 R]
  公理与运算 (1 个):
    - mem_nhds_iff({s : 集合 R} {x : R}) : s in 𝓝 (x : R) ↔ 存在 γ : (ValueGroupWithZero R)ˣ, (x + ·) '' { z | valuation _ z < γ } subseteq s
-/
class IsValuativeTopology [TopologicalSpace R] where
  mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 (x : R) ↔
    exists γ : (ValueGroupWithZero R)ˣ, (x + ·) '' { z | valuation _ z < γ } subseteq s

namespace ValuativeRel

/-- The topology induced by a valuative relation. Note that this is not made into a global instance
to avoid diamonds. If desired, one can equip a ring with a topological space from a valuative
relation by hand. But as long as they do so, the fact that the topology is valuative and
nonarchemidean can be automatically inferred. -/
local instance topologicalSpace : TopologicalSpace R := (valuation R).subgroups_basis.topology

/--
Instance `nonarchimedeanRing` / 实例 `nonarchimedeanRing`

English:
instance nonarchimedeanRing
  signature: : NonarchimedeanRing R
  body: (valuation R).subgroups_basis.nonarchimedean

中文:
实例 nonarchimedeanRing
  签名: : Nonarchimedean环 R
  定义体: (valuation R).subgroups_basis.nonarchimedean

Depends on / 依赖: nonarchimedean, subgroups_basis, subgroups_basis.nonarchimedean, valuation
-/
instance nonarchimedeanRing : NonarchimedeanRing R :=
  (valuation R).subgroups_basis.nonarchimedean

/--
Instance `isValuativeTopology` / 实例 `isValuativeTopology`

English:
instance isValuativeTopology
  signature: : IsValuativeTopology R where
  body: by
    rw [Filter.hasBasis_iff.mp ((valuation R).subgroups_basis.hasBasis_nhds x) s]
    simp [neg_add_eq_sub, ← (valuation R).exists_setOfPred_restrict_le_iff,
      ← restrict_lt_iff_lt_embedding]

中文:
实例 isValuativeTopology
  签名: : 是赋值拓扑 R where
  定义体: by
    rw [Filter.hasBasis_iff.mp ((valuation R).subgroups_basis.hasBasis_nhds x) s]
    simp [neg_add_eq_sub, ← (valuation R).exists_setOfPred_restrict_le_iff,
      ← restrict_lt_iff_lt_embedding]

Depends on / 依赖: Filter, Filter.hasBasis_iff.mp, exists_setOfPred_restrict_le_iff, hasBasis_iff, hasBasis_nhds, neg_add_eq_sub, restrict_lt_iff_lt_embedding, subgroups_basis, subgroups_basis.hasBasis_nhds, valuation
-/
instance isValuativeTopology : IsValuativeTopology R where
  mem_nhds_iff {s x} := by
    rw [Filter.hasBasis_iff.mp ((valuation R).subgroups_basis.hasBasis_nhds x) s]
    simp [neg_add_eq_sub, ← (valuation R).exists_setOfPred_restrict_le_iff,
      ← restrict_lt_iff_lt_embedding]

/-- The uniform structure induced by a valuative relation. Note that this is not made into a
global instance to avoid diamonds. If desired, one can equip a ring with a uniform space
from a valuative relation by hand. But as long as they do so, the fact that the topology is
valuative and nonarchimedean, and the addition is uniformly continuous,
can be automatically inferred. -/
local instance uniformSpace : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R

/-- This is not made into a global instance to avoid diamonds. -/
local instance isUniformAddGroup : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup

end ValuativeRel

variable {R}

variable {K : Type*} [DivisionRing K] [ValuativeRel K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀]

section TopologicalSpace

variable [TopologicalSpace R] (v : Valuation R Γ₀) [v.Compatible]
namespace IsValuativeTopology

/--
theorem `of_mem_nhds_iff_vle` / 定理 `of_mem_nhds_iff_vle`

English:
theorem of_mem_nhds_iff_vle
  statement: (H : forall {s : Set R} {x : R}, s in 𝓝 x ↔
  proof: by
  constructor
  refine fun {s x} => ⟨fun h_mem => ?_, fun ⟨γ, hγ⟩ =>
    H.mpr ⟨.mk0 ((orderMonoidIso v) γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩⟩
  obtain ⟨γ, hγ⟩ := H.mp h_mem
  exact ⟨.mk0 ((orderMonoidIso v).symm γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩

中文:
定理 of_mem_nhds_iff_vle
  结论: (H : 对任意 {s : 集合 R} {x : R}, s in 𝓝 x ↔
  证明: by
  constructor
  refine fun {s x} => ⟨fun h_mem => ?_, fun ⟨γ, hγ⟩ =>
    H.mpr ⟨.mk0 ((orderMonoidIso v) γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩⟩
  obtain ⟨γ, hγ⟩ := H.mp h_mem
  exact ⟨.mk0 ((orderMonoidIso v).symm γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩

Depends on / 依赖: H.mp, H.mpr, h_mem, neg_add_eq_sub, orderMonoidIso, subset_trans
-/
theorem of_mem_nhds_iff_vle (H : forall {s : Set R} {x : R}, s in 𝓝 x ↔
    exists (γ : (ValueGroup₀ (.ofClass v))ˣ), {z : R | v.restrict (z - x) < γ} subseteq s) :
    IsValuativeTopology R := by
  constructor
  refine fun {s x} => ⟨fun h_mem => ?_, fun ⟨γ, hγ⟩ =>
    H.mpr ⟨.mk0 ((orderMonoidIso v) γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩⟩
  obtain ⟨γ, hγ⟩ := H.mp h_mem
  exact ⟨.mk0 ((orderMonoidIso v).symm γ) (by simp), subset_trans (by simp [neg_add_eq_sub]) hγ⟩

open scoped Pointwise in
/--
theorem `of_mem_nhds_zero_iff_vle` / 定理 `of_mem_nhds_zero_iff_vle`

English:
theorem of_mem_nhds_zero_iff_vle
  statement: [IsTopologicalAddGroup R]
  proof: by
  apply of_mem_nhds_iff_vle v (fun {s x} => ?_)
  rw [← vadd_mem_nhds_vadd_iff (g := -x)]
  simp only [vadd_eq_add, neg_add_cancel, H, subset_vadd_set_iff, neg_neg]
  suffices forall (γ : (ValueGroup₀ (.ofClass v))ˣ), (x +ᵥ {z | v.restrict z < ↑γ}) =
    {a | v.restrict (-x + a) < ↑γ} by simp_all [neg_add_eq_sub]
  simp [Set.ext_iff, mem_vadd_set_iff_neg_vadd_mem]

中文:
定理 of_mem_nhds_zero_iff_vle
  结论: [是拓扑加群 R]
  证明: by
  apply of_mem_nhds_iff_vle v (fun {s x} => ?_)
  rw [← vadd_mem_nhds_vadd_iff (g := -x)]
  simp only [vadd_eq_add, neg_add_cancel, H, subset_vadd_set_iff, neg_neg]
  suffices forall (γ : (ValueGroup₀ (.ofClass v))ˣ), (x +ᵥ {z | v.restrict z < ↑γ}) =
    {a | v.restrict (-x + a) < ↑γ} by simp_all [neg_add_eq_sub]
  simp [Set.ext_iff, mem_vadd_set_iff_neg_vadd_mem]

Depends on / 依赖: Set.ext_iff, ext_iff, mem_vadd_set_iff_neg_vadd_mem, neg_add_cancel, neg_add_eq_sub, neg_neg, ofClass, of_mem_nhds_iff_vle, restrict, subset_vadd_set_iff, v.restrict, vadd_eq_add, vadd_mem_nhds_vadd_iff
-/
theorem of_mem_nhds_zero_iff_vle [IsTopologicalAddGroup R]
    (H : forall {s : Set R}, s in 𝓝 0 ↔ exists (γ : (ValueGroup₀ (.ofClass v))ˣ),
    {z : R | v.restrict z < γ} subseteq s) : IsValuativeTopology R := by
  apply of_mem_nhds_iff_vle v (fun {s x} => ?_)
  rw [← vadd_mem_nhds_vadd_iff (g := -x)]
  simp only [vadd_eq_add, neg_add_cancel, H, subset_vadd_set_iff, neg_neg]
  suffices forall (γ : (ValueGroup₀ (.ofClass v))ˣ), (x +ᵥ {z | v.restrict z < ↑γ}) =
    {a | v.restrict (-x + a) < ↑γ} by simp_all [neg_add_eq_sub]
  simp [Set.ext_iff, mem_vadd_set_iff_neg_vadd_mem]

variable [IsValuativeTopology R]

/--
lemma `mem_nhds_iff'` / 引理 `mem_nhds_iff'`

English:
lemma mem_nhds_iff'
  given: {s : Set R} {x : R}
  proof: by
  convert! mem_nhds_iff (s := s) using 4
  simp [neg_add_eq_sub]

中文:
引理 mem_nhds_iff'
  条件: {s : 集合 R} {x : R}
  证明: by
  convert! mem_nhds_iff (s := s) using 4
  simp [neg_add_eq_sub]

Depends on / 依赖: convert, mem_nhds_iff, neg_add_eq_sub
-/
lemma mem_nhds_iff' {s : Set R} {x : R} :
    s in 𝓝 x ↔ exists γ : (ValueGroupWithZero R)ˣ, { z | valuation R (z - x) < γ } subseteq s := by
  convert! mem_nhds_iff (s := s) using 4
  simp [neg_add_eq_sub]

/--
lemma `mem_nhds_zero_iff` / 引理 `mem_nhds_zero_iff`

English:
lemma mem_nhds_zero_iff
  given: (s : Set R)
  proof: by
  simp [mem_nhds_iff']

中文:
引理 mem_nhds_zero_iff
  条件: (s : 集合 R)
  证明: by
  simp [mem_nhds_iff']

Depends on / 依赖: mem_nhds_iff
-/
lemma mem_nhds_zero_iff (s : Set R) :
    s in 𝓝 0 ↔ exists γ : (ValueGroupWithZero R)ˣ, { x | valuation R x < γ } subseteq s := by
  simp [mem_nhds_iff']

/--
theorem `hasBasis_nhds` / 定理 `hasBasis_nhds`

English:
theorem hasBasis_nhds
  given: (x : R)
  proof: by
  simp [Filter.hasBasis_iff, mem_nhds_iff']

中文:
定理 hasBasis_nhds
  条件: (x : R)
  证明: by
  simp [Filter.hasBasis_iff, mem_nhds_iff']

Depends on / 依赖: Filter, Filter.hasBasis_iff, hasBasis_iff, mem_nhds_iff
-/
theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { z | valuation R (z - x) < γ } := by
  simp [Filter.hasBasis_iff, mem_nhds_iff']

/--
lemma `hasBasis_nhds'` / 引理 `hasBasis_nhds'`

English:
lemma hasBasis_nhds'
  given: (x : R)
  proof: (hasBasis_nhds x).to_hasBasis (fun γ _ => ⟨γ, by simp⟩)
    fun γ hγ => ⟨.mk0 γ hγ, by simp⟩

中文:
引理 hasBasis_nhds'
  条件: (x : R)
  证明: (hasBasis_nhds x).to_hasBasis (fun γ _ => ⟨γ, by simp⟩)
    fun γ hγ => ⟨.mk0 γ hγ, by simp⟩

Depends on / 依赖: hasBasis_nhds, to_hasBasis
-/
lemma hasBasis_nhds' (x : R) :
    (𝓝 x).HasBasis (· != 0) ({ y | valuation R (y - x) < · }) :=
  (hasBasis_nhds x).to_hasBasis (fun γ _ => ⟨γ, by simp⟩)
    fun γ hγ => ⟨.mk0 γ hγ, by simp⟩

variable (R) in
/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  proof: by
  convert! hasBasis_nhds (0 : R)
  rw [sub_zero]

中文:
定理 hasBasis_nhds_zero
  证明: by
  convert! hasBasis_nhds (0 : R)
  rw [sub_zero]

Depends on / 依赖: convert, hasBasis_nhds, sub_zero
-/
theorem hasBasis_nhds_zero :
    (𝓝 0).HasBasis (fun _ => True)
      fun γ : (ValueGroupWithZero R)ˣ => { x | valuation R x < γ } := by
  convert! hasBasis_nhds (0 : R)
  rw [sub_zero]

variable (R) in
/--
lemma `hasBasis_nhds_zero'` / 引理 `hasBasis_nhds_zero'`

English:
lemma hasBasis_nhds_zero'
  proof: (hasBasis_nhds_zero R).to_hasBasis (fun γ _ => ⟨γ, by simp⟩)
    fun γ hγ => ⟨.mk0 γ hγ, by simp⟩

中文:
引理 hasBasis_nhds_zero'
  证明: (hasBasis_nhds_zero R).to_hasBasis (fun γ _ => ⟨γ, by simp⟩)
    fun γ hγ => ⟨.mk0 γ hγ, by simp⟩

Depends on / 依赖: hasBasis_nhds_zero, to_hasBasis
-/
lemma hasBasis_nhds_zero' :
    (𝓝 0).HasBasis (· != 0) ({ x | valuation R x < · }) :=
  (hasBasis_nhds_zero R).to_hasBasis (fun γ _ => ⟨γ, by simp⟩)
    fun γ hγ => ⟨.mk0 γ hγ, by simp⟩

end IsValuativeTopology

open IsValuativeTopology

variable [IsValuativeTopology R]

namespace Valuation

/--
lemma `mem_nhds_iff` / 引理 `mem_nhds_iff`

English:
lemma mem_nhds_iff
  given: {s : Set R} {x : R}
  statement: s in 𝓝 x ↔
  proof: by
  convert! IsValuativeTopology.mem_nhds_iff (s := s) using 4
  simpa [neg_add_eq_sub] using v.exists_setOfPred_restrict_le_iff _ _

中文:
引理 mem_nhds_iff
  条件: {s : 集合 R} {x : R}
  结论: s in 𝓝 x ↔
  证明: by
  convert! IsValuativeTopology.mem_nhds_iff (s := s) using 4
  simpa [neg_add_eq_sub] using v.exists_setOfPred_restrict_le_iff _ _

Depends on / 依赖: IsValuativeTopology, IsValuativeTopology.mem_nhds_iff, convert, exists_setOfPred_restrict_le_iff, mem_nhds_iff, neg_add_eq_sub, v.exists_setOfPred_restrict_le_iff
-/
lemma mem_nhds_iff {s : Set R} {x : R} : s in 𝓝 x ↔
    exists γ : (ValueGroup₀ (.ofClass v))ˣ, { z | v.restrict (z - x) < γ.val } subseteq s := by
  convert! IsValuativeTopology.mem_nhds_iff (s := s) using 4
  simpa [neg_add_eq_sub] using v.exists_setOfPred_restrict_le_iff _ _

/--
lemma `mem_nhds_zero_iff` / 引理 `mem_nhds_zero_iff`

English:
lemma mem_nhds_zero_iff
  given: (s : Set R)
  statement: s in 𝓝 0 ↔
  proof: by
  simp [v.mem_nhds_iff]

alias is_topological_valuation := mem_nhds_zero_iff

中文:
引理 mem_nhds_zero_iff
  条件: (s : 集合 R)
  结论: s in 𝓝 0 ↔
  证明: by
  simp [v.mem_nhds_iff]

alias is_topological_valuation := mem_nhds_zero_iff

Depends on / 依赖: mem_nhds_iff, v.mem_nhds_iff
-/
lemma mem_nhds_zero_iff (s : Set R) : s in 𝓝 0 ↔
    exists γ : (ValueGroup₀ (.ofClass v))ˣ, { x | v.restrict x < γ.val } subseteq s := by
  simp [v.mem_nhds_iff]

alias is_topological_valuation := mem_nhds_zero_iff

/--
theorem `hasBasis_nhds` / 定理 `hasBasis_nhds`

English:
theorem hasBasis_nhds
  given: (x : R)
  proof: by
  simp [Filter.hasBasis_iff, v.mem_nhds_iff]

中文:
定理 hasBasis_nhds
  条件: (x : R)
  证明: by
  simp [Filter.hasBasis_iff, v.mem_nhds_iff]

Depends on / 依赖: Filter, Filter.hasBasis_iff, hasBasis_iff, mem_nhds_iff, v.mem_nhds_iff
-/
theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ => True)
      fun γ : (ValueGroup₀ (.ofClass v))ˣ => { z | v.restrict (z - x) < γ.val } := by
  simp [Filter.hasBasis_iff, v.mem_nhds_iff]

/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  proof: by
  simp [Filter.hasBasis_iff, v.is_topological_valuation]

中文:
定理 hasBasis_nhds_zero
  证明: by
  simp [Filter.hasBasis_iff, v.is_topological_valuation]

Depends on / 依赖: Filter, Filter.hasBasis_iff, hasBasis_iff, is_topological_valuation, v.is_topological_valuation
-/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (ValueGroup₀ (.ofClass v))ˣ => { x | v.restrict x < γ.val } := by
  simp [Filter.hasBasis_iff, v.is_topological_valuation]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `locally_const` / 定理 `locally_const`

English:
theorem locally_const
  given: {x : R} (h : (v x : Γ₀) != 0)
  statement: { y : R | v y = v x } in 𝓝 x
  proof: by
  rw [v.mem_nhds_iff]
  have h' : v.restrict x != 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

中文:
定理 locally_const
  条件: {x : R} (h : (v x : Γ₀) != 0)
  结论: { y : R | v y = v x } in 𝓝 x
  证明: by
  rw [v.mem_nhds_iff]
  have h' : v.restrict x != 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

Depends on / 依赖: Units.mk0, Units.val_mk0, Valuation, Valuation.map_eq_of_sub_lt, map_eq_of_sub_lt, mem_nhds_iff, restrict, restrict_lt_iff, v.mem_nhds_iff, v.restrict, v.restrict_lt_iff.mp, val_mk0, y_in
-/
theorem locally_const {x : R} (h : (v x : Γ₀) != 0) : { y : R | v y = v x } in 𝓝 x := by
  rw [v.mem_nhds_iff]
  have h' : v.restrict x != 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

end Valuation

namespace IsValuativeTopology

variable (R) in
instance (priority := low) : IsTopologicalAddGroup R := by
  have cts_add : ContinuousConstVAdd R R :=
    ⟨fun x => continuous_iff_continuousAt.2 fun z =>
      (((valuation R).hasBasis_nhds z).tendsto_iff ((valuation R).hasBasis_nhds (x + z))).2
        fun γ _ => ⟨γ, trivial, fun y hy => by simpa using hy⟩⟩
  have basis := (valuation R).hasBasis_nhds_zero
  refine .of_comm_of_nhds_zero ?_ ?_ fun x₀ => (map_eq_of_inverse (-x₀ + ·) ?_ ?_ ?_).symm
  · exact (basis.prod_self.tendsto_iff basis).2 fun γ _ =>
      ⟨γ, trivial, fun ⟨_, _⟩ hx => (valuation R).restrict.map_add_lt hx.left hx.right⟩
  · exact (basis.tendsto_iff basis).2 fun γ _ => ⟨γ, trivial, fun y hy => by simpa using hy⟩
  · ext; simp
  · simpa [ContinuousAt] using (cts_add.1 x₀).continuousAt (x := 0)
  · simpa [ContinuousAt] using (cts_add.1 (-x₀)).continuousAt (x := x₀)

end IsValuativeTopology

end TopologicalSpace

namespace Valuation

section UniformSpace

variable [_u : UniformSpace R] [IsUniformAddGroup R] [IsValuativeTopology R] (v : Valuation R Γ₀)
  [v.Compatible]

/--
theorem `hasBasis_uniformity` / 定理 `hasBasis_uniformity`

English:
theorem hasBasis_uniformity
  statement: (𝓤 R).HasBasis (fun _ => True)
  proof: by
  rw [uniformity_eq_comap_nhds_zero]
  exact v.hasBasis_nhds_zero.comap _

中文:
定理 hasBasis_uniformity
  结论: (𝓤 R).有基 (fun _ => 真)
  证明: by
  rw [uniformity_eq_comap_nhds_zero]
  exact v.hasBasis_nhds_zero.comap _

Depends on / 依赖: hasBasis_nhds_zero, uniformity_eq_comap_nhds_zero, v.hasBasis_nhds_zero.comap
-/
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : (ValueGroup₀ (.ofClass v))ˣ =>
      { p : R × R | v.restrict (p.2 - p.1) < γ.1 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact v.hasBasis_nhds_zero.comap _

/--
theorem `toUniformSpace_eq` / 定理 `toUniformSpace_eq`

English:
theorem toUniformSpace_eq
  statement: _u =
  proof: by
  refine UniformSpace.ext (v.hasBasis_uniformity.eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp [restrict_lt_iff_lt_embedding, sub_eq_add_neg]

中文:
定理 toUniformSpace_eq
  结论: _u =
  证明: by
  refine UniformSpace.ext (v.hasBasis_uniformity.eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp [restrict_lt_iff_lt_embedding, sub_eq_add_neg]

Depends on / 依赖: UniformSpace, UniformSpace.ext, convert, eq_of_same_basis, hasBasis_nhds_zero, hasBasis_uniformity, restrict_lt_iff_lt_embedding, sub_eq_add_neg, subgroups_basis, v.hasBasis_uniformity.eq_of_same_basis, v.subgroups_basis.hasBasis_nhds_zero.comap
-/
theorem toUniformSpace_eq : _u =
    @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _ := by
  refine UniformSpace.ext (v.hasBasis_uniformity.eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp [restrict_lt_iff_lt_embedding, sub_eq_add_neg]

/--
theorem `cauchy_iff` / 定理 `cauchy_iff`

English:
theorem cauchy_iff
  given: {F : Filter R}
  statement: Cauchy F ↔
  proof: by
  rw [v.toUniformSpace_eq]; rw [AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

中文:
定理 cauchy_iff
  条件: {F : 滤子 R}
  结论: Cauchy F ↔
  证明: by
  rw [v.toUniformSpace_eq]; rw [AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

Depends on / 依赖: AddGroupFilterBasis, AddGroupFilterBasis.cauchy_iff, Iff.rfl, and_congr, cauchy_iff, mem_addGroupFilterBasis, mem_addGroupFilterBasis_iff, restrict_lt_iff_lt_embedding, simp_rw, subgroups_basis, toUniformSpace_eq, v.subgroups_basis.mem_addGroupFilterBasis, v.subgroups_basis.mem_addGroupFilterBasis_iff, v.toUniformSpace_eq
-/
theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ forall γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ,
      exists M in F, forallᵉ (x in M) (y in M), v.restrict (y - x) < γ.1 := by
  rw [v.toUniformSpace_eq]; rw [AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

end UniformSpace

section TopologicalSpace

variable [_t : TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]
  [TopologicalSpace K] [IsValuativeTopology K]

/--
theorem `toTopologicalSpace_eq` / 定理 `toTopologicalSpace_eq`

English:
theorem toTopologicalSpace_eq
  proof: by
  let u := IsTopologicalAddGroup.rightUniformSpace R
  let := isUniformAddGroup_of_addCommGroup (G := R)
  exact congrArg (fun u => @UniformSpace.toTopologicalSpace R u) v.toUniformSpace_eq

中文:
定理 toTopologicalSpace_eq
  证明: by
  let u := IsTopologicalAddGroup.rightUniformSpace R
  let := isUniformAddGroup_of_addCommGroup (G := R)
  exact congrArg (fun u => @UniformSpace.toTopologicalSpace R u) v.toUniformSpace_eq

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, UniformSpace, UniformSpace.toTopologicalSpace, isUniformAddGroup_of_addCommGroup, rightUniformSpace, toTopologicalSpace, toUniformSpace_eq, v.toUniformSpace_eq
-/
theorem toTopologicalSpace_eq :
    _t = v.subgroups_basis.topology := by
  let u := IsTopologicalAddGroup.rightUniformSpace R
  let := isUniformAddGroup_of_addCommGroup (G := R)
  exact congrArg (fun u => @UniformSpace.toTopologicalSpace R u) v.toUniformSpace_eq

instance (priority := low) _root_.IsValuativeTopology.isTopologicalRing : IsTopologicalRing R := by
  convert! (ValuativeRel.nonarchimedeanRing R).toIsTopologicalRing
  exact toTopologicalSpace_eq _

section Discrete

/--
lemma `discreteTopology_of_forall_map_eq_one` / 引理 `discreteTopology_of_forall_map_eq_one`

English:
lemma discreteTopology_of_forall_map_eq_one
  given: (h : forall x : R, x != 0 -> v x = 1)
  proof: by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, v.mem_nhds_zero_iff, subset_singleton_iff, mem_ofPred_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding]; rw [Units.val_one]; rw [map_one] at hx
  exact ⟨x, hx', hx.ne⟩

中文:
引理 discreteTopology_of_对任意_map_eq_one
  条件: (h : 对任意 x : R, x != 0 -> v x = 1)
  证明: by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, v.mem_nhds_zero_iff, subset_singleton_iff, mem_ofPred_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding]; rw [Units.val_one]; rw [map_one] at hx
  exact ⟨x, hx', hx.ne⟩

Depends on / 依赖: Units.val_one, contrapose, discreteTopology_iff_isOpen_singleton_zero, forall_eq, hx.ne, isOpen_iff_mem_nhds, map_one, mem_nhds_zero_iff, mem_ofPred_eq, mem_singleton_iff, restrict_lt_iff_lt_embedding, subset_singleton_iff, v.mem_nhds_zero_iff, val_one
-/
lemma discreteTopology_of_forall_map_eq_one (h : forall x : R, x != 0 -> v x = 1) :
    DiscreteTopology R := by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, v.mem_nhds_zero_iff, subset_singleton_iff, mem_ofPred_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding]; rw [Units.val_one]; rw [map_one] at hx
  exact ⟨x, hx', hx.ne⟩

/--
lemma `discreteTopology_of_forall_lt` / 引理 `discreteTopology_of_forall_lt`

English:
lemma discreteTopology_of_forall_lt
  statement: [MulArchimedean Γ₀] (v : Valuation K Γ₀)
  proof: v.discreteTopology_of_forall_map_eq_one (by simpa using v.map_eq_one_of_forall_lt hr h)

中文:
引理 discreteTopology_of_对任意_lt
  结论: [MulArchimedean Γ₀] (v : 赋值 K Γ₀)
  证明: v.discreteTopology_of_forall_map_eq_one (by simpa using v.map_eq_one_of_forall_lt hr h)

Depends on / 依赖: discreteTopology_of_forall_map_eq_one, map_eq_one_of_forall_lt, v.discreteTopology_of_forall_map_eq_one, v.map_eq_one_of_forall_lt
-/
lemma discreteTopology_of_forall_lt [MulArchimedean Γ₀] (v : Valuation K Γ₀)
    [v.Compatible] {r : Γ₀} (hr : r != 0) (h : forall x : K, v x != 0 -> r < v x) :
    DiscreteTopology K :=
  v.discreteTopology_of_forall_map_eq_one (by simpa using v.map_eq_one_of_forall_lt hr h)

end Discrete

variable {v}

/--
theorem `isOpen_ball` / 定理 `isOpen_ball`

English:
theorem isOpen_ball
  given: (r : ValueGroup₀ (.ofClass v))
  statement: IsOpen {x | v.restrict x < r}
  proof: by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [v.mem_nhds_iff]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

中文:
定理 isOpen_ball
  条件: (r : ValueGroup₀ (.ofClass v))
  结论: 是开集 {x | v.restrict x < r}
  证明: by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [v.mem_nhds_iff]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

Depends on / 依赖: Units.mk0, eq_or_ne, isOpen_iff_mem_nhds, map_add, max_lt, mem_nhds_iff, ofPred_subset_ofPred, restrict, sub_add_cancel, trans_lt, v.mem_nhds_iff, v.restrict.map_add
-/
theorem isOpen_ball (r : ValueGroup₀ (.ofClass v)) : IsOpen {x | v.restrict x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [v.mem_nhds_iff]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

/--
theorem `isClosed_ball` / 定理 `isClosed_ball`

English:
theorem isClosed_ball
  given: (r : ValueGroup₀ (.ofClass v))
  proof: by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _)

中文:
定理 isClosed_ball
  条件: (r : ValueGroup₀ (.ofClass v))
  证明: by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _)

Depends on / 依赖: AddSubgroup, AddSubgroup.isClosed_of_isOpen, Units.mk0, Valuation, Valuation.ltAddSubgroup, eq_or_ne, isClosed_of_isOpen, isOpen_ball, ltAddSubgroup, restrict, v.restrict
-/
theorem isClosed_ball (r : ValueGroup₀ (.ofClass v)) :
    IsClosed {x | v.restrict x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _)

/--
theorem `isClopen_ball` / 定理 `isClopen_ball`

English:
theorem isClopen_ball
  given: (r : ValueGroup₀ (.ofClass v))
  proof: ⟨isClosed_ball _, isOpen_ball _⟩

中文:
定理 isClopen_ball
  条件: (r : ValueGroup₀ (.ofClass v))
  证明: ⟨isClosed_ball _, isOpen_ball _⟩

Depends on / 依赖: isClosed_ball, isOpen_ball
-/
theorem isClopen_ball (r : ValueGroup₀ (.ofClass v)) :
    IsClopen {x | v.restrict x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

/--
theorem `isOpen_closedBall` / 定理 `isOpen_closedBall`

English:
theorem isOpen_closedBall
  given: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  proof: by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [v.mem_nhds_iff, ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy =>
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

中文:
定理 isOpen_closedBall
  条件: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  证明: by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [v.mem_nhds_iff, ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy =>
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

Depends on / 依赖: Units.mk0, isOpen_iff_mem_nhds, le_of_lt, le_trans, map_add, max_le, mem_nhds_iff, ofPred_subset_ofPred, restrict, sub_add_cancel, v.mem_nhds_iff, v.restrict.map_add
-/
theorem isOpen_closedBall {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) :
  IsOpen {x | v.restrict x <= r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [v.mem_nhds_iff, ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy =>
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isClosed_closedBall` / 定理 `isClosed_closedBall`

English:
theorem isClosed_closedBall
  given: (r : ValueGroup₀ (.ofClass v))
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [v.mem_nhds_iff]
  have hx' : v.restrict x != 0 := hx.ne_zero
exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

中文:
定理 isClosed_closedBall
  条件: (r : ValueGroup₀ (.ofClass v))
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [v.mem_nhds_iff]
  have hx' : v.restrict x != 0 := hx.ne_zero
exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

Depends on / 依赖: Units.mk0, Valuation, Valuation.map_sub_eq_of_lt_left, hx.ne_zero, isOpen_compl_iff, isOpen_iff_mem_nhds, lt_of_le_of_lt, map_sub_eq_of_lt_left, map_sub_swap, mem_compl_iff, mem_nhds_iff, mem_ofPred_eq, ne_of_lt, ne_zero, not_le, restrict, v.mem_nhds_iff, v.restrict
-/
theorem isClosed_closedBall (r : ValueGroup₀ (.ofClass v)) :
    IsClosed {x | v.restrict x <= r} := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [v.mem_nhds_iff]
  have hx' : v.restrict x != 0 := hx.ne_zero
exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

/--
theorem `isClopen_closedBall` / 定理 `isClopen_closedBall`

English:
theorem isClopen_closedBall
  given: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  proof: ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

中文:
定理 isClopen_closedBall
  条件: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  证明: ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

Depends on / 依赖: isClosed_closedBall, isOpen_closedBall
-/
theorem isClopen_closedBall {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) :
    IsClopen {x | v.restrict x <= r} :=
  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isClopen_sphere` / 定理 `isClopen_sphere`

English:
theorem isClopen_sphere
  given: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  proof: by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x <= r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

中文:
定理 isClopen_sphere
  条件: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  证明: by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x <= r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

Depends on / 依赖: IsClopen, IsClopen.diff, isClopen_ball, isClopen_closedBall, le_antisymm_iff, restrict, v.restrict
-/
theorem isClopen_sphere {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) :
    IsClopen {x | v.restrict x = r} := by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x <= r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall hr) (isClopen_ball _)

/--
theorem `isOpen_sphere` / 定理 `isOpen_sphere`

English:
theorem isOpen_sphere
  given: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  proof: .isOpen isClopen_sphere hr

中文:
定理 isOpen_sphere
  条件: {r : ValueGroup₀ (.ofClass v)} (hr : r != 0)
  证明: .isOpen isClopen_sphere hr

Depends on / 依赖: isClopen_sphere, isOpen
-/
theorem isOpen_sphere {r : ValueGroup₀ (.ofClass v)} (hr : r != 0) :
    IsOpen {x | v.restrict x = r} :=
.isOpen isClopen_sphere hr

/--
theorem `isClosed_sphere` / 定理 `isClosed_sphere`

English:
theorem isClosed_sphere
  given: (r : ValueGroup₀ (.ofClass v))
  proof: by
  rcases eq_or_ne r 0 with rfl | hr
  · convert! v.isClosed_closedBall 0 using 3
    simp
.isClosed exact isClopen_sphere hr

中文:
定理 isClosed_sphere
  条件: (r : ValueGroup₀ (.ofClass v))
  证明: by
  rcases eq_or_ne r 0 with rfl | hr
  · convert! v.isClosed_closedBall 0 using 3
    simp
.isClosed exact isClopen_sphere hr

Depends on / 依赖: convert, eq_or_ne, isClopen_sphere, isClosed, isClosed_closedBall, v.isClosed_closedBall
-/
theorem isClosed_sphere (r : ValueGroup₀ (.ofClass v)) :
    IsClosed {x | v.restrict x = r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · convert! v.isClosed_closedBall 0 using 3
    simp
.isClosed exact isClopen_sphere hr

/--
theorem `isOpen_integer` / 定理 `isOpen_integer`

English:
theorem isOpen_integer
  statement: IsOpen (v.integer : Set R)
  proof: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  apply isOpen_closedBall one_ne_zero

中文:
定理 isOpen_integer
  结论: 是开集 (v.integer : 集合 R)
  证明: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  apply isOpen_closedBall one_ne_zero

Depends on / 依赖: Submonoid, Submonoid.coe_set_mk, Subring, Subring.coe_set_mk, Subsemigroup, Subsemigroup.coe_set_mk, Subsemiring, Subsemiring.coe_set_mk, coe_set_mk, integer, isOpen_closedBall, one_ne_zero, restrict_le_one_iff, v.restrict_le_one_iff
-/
theorem isOpen_integer : IsOpen (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  apply isOpen_closedBall one_ne_zero

/--
theorem `isClosed_integer` / 定理 `isClosed_integer`

English:
theorem isClosed_integer
  statement: IsClosed (v.integer : Set R)
  proof: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _

中文:
定理 isClosed_integer
  结论: 是闭集 (v.integer : 集合 R)
  证明: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _

Depends on / 依赖: Submonoid, Submonoid.coe_set_mk, Subring, Subring.coe_set_mk, Subsemigroup, Subsemigroup.coe_set_mk, Subsemiring, Subsemiring.coe_set_mk, coe_set_mk, integer, isClosed_closedBall, restrict_le_one_iff, v.restrict_le_one_iff
-/
theorem isClosed_integer : IsClosed (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _

/--
theorem `isClopen_integer` / 定理 `isClopen_integer`

English:
theorem isClopen_integer
  statement: IsClopen (v.integer : Set R)
  proof: ⟨isClosed_integer, isOpen_integer⟩

中文:
定理 isClopen_integer
  结论: IsClopen (v.integer : 集合 R)
  证明: ⟨isClosed_integer, isOpen_integer⟩

Depends on / 依赖: isClosed_integer, isOpen_integer
-/
theorem isClopen_integer : IsClopen (v.integer : Set R) :=
  ⟨isClosed_integer, isOpen_integer⟩

section Field

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]

/--
theorem `isOpen_valuationSubring` / 定理 `isOpen_valuationSubring`

English:
theorem isOpen_valuationSubring
  given: (v : Valuation K Γ₀) [v.Compatible]
  proof: isOpen_integer

中文:
定理 isOpen_valuationSubring
  条件: (v : 赋值 K Γ₀) [v.余mpatible]
  证明: isOpen_integer

Depends on / 依赖: isOpen_integer
-/
theorem isOpen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsOpen (v.valuationSubring : Set K) :=
  isOpen_integer

/--
theorem `isClosed_valuationSubring` / 定理 `isClosed_valuationSubring`

English:
theorem isClosed_valuationSubring
  given: (v : Valuation K Γ₀) [v.Compatible]
  proof: isClosed_integer

中文:
定理 isClosed_valuationSubring
  条件: (v : 赋值 K Γ₀) [v.余mpatible]
  证明: isClosed_integer

Depends on / 依赖: isClosed_integer
-/
theorem isClosed_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClosed (v.valuationSubring : Set K) :=
  isClosed_integer

/--
theorem `isClopen_valuationSubring` / 定理 `isClopen_valuationSubring`

English:
theorem isClopen_valuationSubring
  given: (v : Valuation K Γ₀) [v.Compatible]
  proof: isClopen_integer

中文:
定理 isClopen_valuationSubring
  条件: (v : 赋值 K Γ₀) [v.余mpatible]
  证明: isClopen_integer

Depends on / 依赖: isClopen_integer
-/
theorem isClopen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClopen (v.valuationSubring : Set K) :=
  isClopen_integer

end Field

end TopologicalSpace

end Valuation

namespace IsValuativeTopology

@[deprecated (since := "2026-03-17")] alias isOpen_ball := Valuation.isOpen_ball
@[deprecated (since := "2026-03-17")] alias isClosed_ball := Valuation.isClosed_ball
@[deprecated (since := "2026-03-17")] alias isClopen_ball := Valuation.isClopen_ball
@[deprecated (since := "2026-03-17")] alias isOpen_closedBall := Valuation.isOpen_closedBall
@[deprecated (since := "2026-03-17")] alias isClosed_closedBall := Valuation.isClosed_closedBall
@[deprecated (since := "2026-03-17")] alias isClopen_closedBall := Valuation.isClopen_closedBall
@[deprecated (since := "2026-03-17")] alias isClopen_sphere := Valuation.isClopen_sphere
@[deprecated (since := "2026-03-17")] alias isOpen_sphere := Valuation.isOpen_sphere

end IsValuativeTopology
