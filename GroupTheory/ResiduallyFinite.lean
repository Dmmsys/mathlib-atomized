/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

/-!
# Residually Finite Groups

In this file we define residually finite groups and prove some basic properties.

## Main definitions

- `Group.ResiduallyFinite G`: A group `G` is residually finite if the intersection of all
  finite index normal subgroups is trivial.

-/

@[expose] public section

/--
Definition of `AddGroup.ResiduallyFinite` / `AddGroup.ResiduallyFinite` 的定义

English:
class AddGroup.ResiduallyFinite
  parameters: (G : Type*) [AddGroup G]
  axioms and operations (1):
    - iInf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥

中文:
类 AddGroup.ResiduallyFinite
  参数: (G : 类型) [AddGroup G]
  公理与运算 (1 个):
    - iInf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥
-/
class AddGroup.ResiduallyFinite (G : Type*) [AddGroup G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥

namespace Group

/--
Definition of `ResiduallyFinite` / `ResiduallyFinite` 的定义

English:
class ResiduallyFinite
  parameters: (G : Type*) [Group G]
  axioms and operations (1):
    - iInf_eq_bot : ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥

中文:
类 ResiduallyFinite
  参数: (G : 类型) [Group G]
  公理与运算 (1 个):
    - iInf_eq_bot : ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥
-/
class ResiduallyFinite (G : Type*) [Group G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥

attribute [to_additive existing] ResiduallyFinite

variable {G G' : Type*} [Group G] [Group G']

@[to_additive]
/--
theorem `residuallyFinite_def` / 定理 `residuallyFinite_def`

English:
theorem residuallyFinite_def
  proof: ⟨fun h => h.iInf_eq_bot, fun h => ⟨h⟩⟩

@[to_additive]

中文:
定理 residuallyFinite_def
  证明: ⟨fun h => h.iInf_eq_bot, fun h => ⟨h⟩⟩

@[to_additive]

Depends on / 依赖: h.iInf_eq_bot, iInf_eq_bot
-/
theorem residuallyFinite_def :
    ResiduallyFinite G ↔ ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥ :=
  ⟨fun h => h.iInf_eq_bot, fun h => ⟨h⟩⟩

@[to_additive]
/--
theorem `residuallyFinite_iff_forall_finiteIndexNormalSubgroup` / 定理 `residuallyFinite_iff_forall_finiteIndexNormalSubgroup`

English:
theorem residuallyFinite_iff_forall_finiteIndexNormalSubgroup
  proof: by
  simp_rw [residuallyFinite_def, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]

@[to_additive]

中文:
定理 residuallyFinite_iff_forall_finiteIndexNormalSubgroup
  证明: by
  simp_rw [residuallyFinite_def, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]

@[to_additive]

Depends on / 依赖: FiniteIndexNormalSubgroup, FiniteIndexNormalSubgroup.mem_toSubgroup_iff, Subgroup, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf, eq_bot_iff_forall, mem_iInf, mem_toSubgroup_iff, residuallyFinite_def, simp_rw
-/
theorem residuallyFinite_iff_forall_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ forall g : G, (forall H : FiniteIndexNormalSubgroup G, g in H) -> g = 1 := by
  simp_rw [residuallyFinite_def, Subgroup.eq_bot_iff_forall, Subgroup.mem_iInf,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]

@[to_additive]
/--
theorem `eq_one_iff_forall_finiteIndexNormalSubroup` / 定理 `eq_one_iff_forall_finiteIndexNormalSubroup`

English:
theorem eq_one_iff_forall_finiteIndexNormalSubroup
  statement: [ResiduallyFinite G]
  proof: residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]

中文:
定理 eq_one_iff_forall_finiteIndexNormalSubroup
  结论: [ResiduallyFinite G]
  证明: residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]

Depends on / 依赖: residuallyFinite_iff_forall_finiteIndexNormalSubgroup, residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mp
-/
theorem eq_one_iff_forall_finiteIndexNormalSubroup [ResiduallyFinite G]
    (g : G) (hg : forall H : FiniteIndexNormalSubgroup G, g in H) : g = 1 :=
  residuallyFinite_iff_forall_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]
/--
theorem `residuallyFinite_iff_exists_finiteIndexNormalSubgroup` / 定理 `residuallyFinite_iff_exists_finiteIndexNormalSubgroup`

English:
theorem residuallyFinite_iff_exists_finiteIndexNormalSubgroup
  proof: by
  simp_rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup, ← not_forall, not_imp_not]

@[to_additive]

中文:
定理 residuallyFinite_iff_exists_finiteIndexNormalSubgroup
  证明: by
  simp_rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup, ← not_forall, not_imp_not]

@[to_additive]

Depends on / 依赖: not_forall, not_imp_not, residuallyFinite_iff_forall_finiteIndexNormalSubgroup, simp_rw
-/
theorem residuallyFinite_iff_exists_finiteIndexNormalSubgroup :
    ResiduallyFinite G ↔ forall g : G, g != 1 -> exists H : FiniteIndexNormalSubgroup G, g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup, ← not_forall, not_imp_not]

@[to_additive]
/--
theorem `exists_finiteIndexNormalSubgroup_notMem` / 定理 `exists_finiteIndexNormalSubgroup_notMem`

English:
theorem exists_finiteIndexNormalSubgroup_notMem
  given: [ResiduallyFinite G] (g : G) (hg : g != 1)
  proof: residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]

中文:
定理 exists_finiteIndexNormalSubgroup_notMem
  条件: [ResiduallyFinite G] (g : G) (hg : g != 1)
  证明: residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]

Depends on / 依赖: residuallyFinite_iff_exists_finiteIndexNormalSubgroup, residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mp
-/
theorem exists_finiteIndexNormalSubgroup_notMem [ResiduallyFinite G] (g : G) (hg : g != 1) :
    exists H : FiniteIndexNormalSubgroup G, g ∉ H :=
  residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mp ‹_› g hg

@[to_additive]
/--
theorem `residuallyFinite_iff_forall_finiteIndex` / 定理 `residuallyFinite_iff_forall_finiteIndex`

English:
theorem residuallyFinite_iff_forall_finiteIndex
  proof: by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  exact forall_congr' fun g => ⟨fun h hg => h fun H => hg H,
    fun h hg => h fun H hH => H.normalCore_le (hg (.ofSubgroup H.normalCore))⟩

@[to_additive]

中文:
定理 residuallyFinite_iff_forall_finiteIndex
  证明: by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  exact forall_congr' fun g => ⟨fun h hg => h fun H => hg H,
    fun h hg => h fun H hH => H.normalCore_le (hg (.ofSubgroup H.normalCore))⟩

@[to_additive]

Depends on / 依赖: H.normalCore, H.normalCore_le, forall_congr, normalCore, normalCore_le, ofSubgroup, residuallyFinite_iff_forall_finiteIndexNormalSubgroup
-/
theorem residuallyFinite_iff_forall_finiteIndex :
    ResiduallyFinite G ↔ forall g : G, (forall (H : Subgroup G) [H.FiniteIndex], g in H) -> g = 1 := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  exact forall_congr' fun g => ⟨fun h hg => h fun H => hg H,
    fun h hg => h fun H hH => H.normalCore_le (hg (.ofSubgroup H.normalCore))⟩

@[to_additive]
/--
theorem `residuallyFinite_iff_exists_finiteIndex` / 定理 `residuallyFinite_iff_exists_finiteIndex`

English:
theorem residuallyFinite_iff_exists_finiteIndex
  proof: by
  simp_rw [residuallyFinite_iff_forall_finiteIndex, ← Classical.not_imp, ← not_forall,
    not_imp_not]

中文:
定理 residuallyFinite_iff_exists_finiteIndex
  证明: by
  simp_rw [residuallyFinite_iff_forall_finiteIndex, ← Classical.not_imp, ← not_forall,
    not_imp_not]

Depends on / 依赖: Classical, Classical.not_imp, not_forall, not_imp, not_imp_not, residuallyFinite_iff_forall_finiteIndex, simp_rw
-/
theorem residuallyFinite_iff_exists_finiteIndex :
    ResiduallyFinite G ↔ forall g : G, g != 1 -> exists (H : Subgroup G), H.FiniteIndex ∧ g ∉ H := by
  simp_rw [residuallyFinite_iff_forall_finiteIndex, ← Classical.not_imp, ← not_forall,
    not_imp_not]

/-- If `G` is residually finite, for every pair of distinct elements `g`, `h` there exists a finite
index normal subgroup `H` such that `g` and `h` differ in the quotient `G ⧸ H`. -/
@[to_additive]
/--
theorem `exists_finiteIndexNormalSubgroup_of_residuallyFinite` / 定理 `exists_finiteIndexNormalSubgroup_of_residuallyFinite`

English:
theorem exists_finiteIndexNormalSubgroup_of_residuallyFinite
  statement: [ResiduallyFinite G] (g h : G)
  proof: by
  obtain ⟨H, hH⟩ :=
exists_finiteIndexNormalSubgroup_notMem (g⁻¹ * h) fun h => hgh eq_of_inv_mul_eq_one h
  exact ⟨H, by simpa [QuotientGroup.eq]⟩

中文:
定理 exists_finiteIndexNormalSubgroup_of_residuallyFinite
  结论: [ResiduallyFinite G] (g h : G)
  证明: by
  obtain ⟨H, hH⟩ :=
exists_finiteIndexNormalSubgroup_notMem (g⁻¹ * h) fun h => hgh eq_of_inv_mul_eq_one h
  exact ⟨H, by simpa [QuotientGroup.eq]⟩

Depends on / 依赖: QuotientGroup, QuotientGroup.eq, eq_of_inv_mul_eq_one, exists_finiteIndexNormalSubgroup_notMem
-/
theorem exists_finiteIndexNormalSubgroup_of_residuallyFinite [ResiduallyFinite G] (g h : G)
    (hgh : g != h) : exists H : FiniteIndexNormalSubgroup G, (g : G ⧸ H.toSubgroup) != ↑h := by
  obtain ⟨H, hH⟩ :=
exists_finiteIndexNormalSubgroup_notMem (g⁻¹ * h) fun h => hgh eq_of_inv_mul_eq_one h
  exact ⟨H, by simpa [QuotientGroup.eq]⟩

/-- `G` is residually finite if for every element `g` not equal to `1` there exists a group
homomorphism `f` to a finite group `H` such that `f g ≠ 1`. -/
@[to_additive]
/--
theorem `residuallyFinite_of_forall_exists_finite_monoidHom.` / 定理 `residuallyFinite_of_forall_exists_finite_monoidHom.`

English:
theorem residuallyFinite_of_forall_exists_finite_monoidHom.{u}
  proof: by
  rw [residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  obtain ⟨_, _, _, f, hf⟩ := h g hg
  exact ⟨f.ker, Subgroup.finiteIndex_ker f, by simpa using hf⟩

@[to_additive]

中文:
定理 residuallyFinite_of_forall_exists_finite_monoidHom.{u}
  证明: by
  rw [residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  obtain ⟨_, _, _, f, hf⟩ := h g hg
  exact ⟨f.ker, Subgroup.finiteIndex_ker f, by simpa using hf⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.finiteIndex_ker, f.ker, finiteIndex_ker, residuallyFinite_iff_exists_finiteIndex
-/
theorem residuallyFinite_of_forall_exists_finite_monoidHom.{u}
    (h : forall g : G, g != 1 -> exists (H : Type u) (_ : Group H) (_ : Finite H) (f : G ->* H), f g != 1) :
    ResiduallyFinite G := by
  rw [residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  obtain ⟨_, _, _, f, hf⟩ := h g hg
  exact ⟨f.ker, Subgroup.finiteIndex_ker f, by simpa using hf⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] : ResiduallyFinite G
  body: residuallyFinite_iff_forall_finiteIndex.mpr fun _ hg => hg ⊥

@[to_additive]

中文:
实例 [Finite
  签名: G] : ResiduallyFinite G
  定义体: residuallyFinite_iff_forall_finiteIndex.mpr fun _ hg => hg ⊥

@[to_additive]

Depends on / 依赖: residuallyFinite_iff_forall_finiteIndex, residuallyFinite_iff_forall_finiteIndex.mpr
-/
instance [Finite G] : ResiduallyFinite G :=
  residuallyFinite_iff_forall_finiteIndex.mpr fun _ hg => hg ⊥

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ResiduallyFinite
  signature: G] {H
  body: by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K => hg (K.comap H.subtype)

@[to_additive]

中文:
实例 [ResiduallyFinite
  签名: G] {H
  定义体: by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K => hg (K.comap H.subtype)

@[to_additive]

Depends on / 依赖: H.subtype, K.comap, eq_one_iff_forall_finiteIndexNormalSubroup, residuallyFinite_iff_forall_finiteIndexNormalSubgroup, subtype
-/
instance [ResiduallyFinite G] {H : Subgroup G} : ResiduallyFinite H := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K => hg (K.comap H.subtype)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ResiduallyFinite
  signature: G] [ResiduallyFinite G'] : ResiduallyFinite (G × G')
  body: by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K => hg (K.comap (MonoidHom.fst G G'))
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.2 fun K => hg (K.comap (MonoidHom.snd G G'))

中文:
实例 [ResiduallyFinite
  签名: G] [ResiduallyFinite G'] : ResiduallyFinite (G × G')
  定义体: by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K => hg (K.comap (MonoidHom.fst G G'))
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.2 fun K => hg (K.comap (MonoidHom.snd G G'))

Depends on / 依赖: K.comap, MonoidHom, MonoidHom.fst, MonoidHom.snd, eq_one_iff_forall_finiteIndexNormalSubroup, residuallyFinite_iff_forall_finiteIndexNormalSubgroup
-/
instance [ResiduallyFinite G] [ResiduallyFinite G'] : ResiduallyFinite (G × G') := by
  rw [residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  ext
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.1 fun K => hg (K.comap (MonoidHom.fst G G'))
  · exact eq_one_iff_forall_finiteIndexNormalSubroup g.2 fun K => hg (K.comap (MonoidHom.snd G G'))

end Group
