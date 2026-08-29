/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Order.GroupWithZero.Range

/-!
# The topology on a valued ring

In this file, we define the non-Archimedean topology induced by a valuation on a ring.
The main definition is a `Valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.

*NOTE* (2025-07-02):
The `Valued` class defined in this file will eventually get replaced with `ValuativeRel`
from `Mathlib.RingTheory.Valuation.ValuativeRel.Basic`. New developments on valued rings/fields
should take this into consideration.

-/

@[expose] public section

open scoped Topology uniformity
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Set Valuation

noncomputable section

universe v u

variable {R K : Type u} [Ring R] [DivisionRing K] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

/--
lemma `map_eq_one_of_forall_lt` / 引理 `map_eq_one_of_forall_lt`

English:
lemma map_eq_one_of_forall_lt
  statement: [MulArchimedean Γ₀] {v : Valuation K Γ₀} {r : Γ₀} (hr : r != 0)
  proof: by
  lift r to Γ₀ˣ using IsUnit.mk0 _ hr
  rcases lt_trichotomy (Units.mk0 _ hx) 1 with H | H | H
  · obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ k) (by simp [hx])
    simp [← Units.val_lt_val, ← map_pow, h.not_gt] at hk
  · simpa [Units.ext_iff] using H
  · rw [← inv_lt_one'] at H
    obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ (-k : Int)) (by simp [hx])
    simp only [zpow_neg, zpow_natCast, map_inv₀, map_pow] at h
    simp [← Units.val_lt_val, h.not_gt, inv_pow] at hk

中文:
引理 map_eq_one_of_对任意_lt
  结论: [MulArchimedean Γ₀] {v : 赋值 K Γ₀} {r : Γ₀} (hr : r != 0)
  证明: by
  lift r to Γ₀ˣ using IsUnit.mk0 _ hr
  rcases lt_trichotomy (Units.mk0 _ hx) 1 with H | H | H
  · obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ k) (by simp [hx])
    simp [← Units.val_lt_val, ← map_pow, h.not_gt] at hk
  · simpa [Units.ext_iff] using H
  · rw [← inv_lt_one'] at H
    obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ (-k : Int)) (by simp [hx])
    simp only [zpow_neg, zpow_natCast, map_inv₀, map_pow] at h
    simp [← Units.val_lt_val, h.not_gt, inv_pow] at hk

Depends on / 依赖: IsUnit, IsUnit.mk0, Units.ext_iff, Units.mk0, Units.val_lt_val, exists_pow_lt, ext_iff, h.not_gt, inv_lt_one, inv_pow, lt_trichotomy, map_pow, not_gt, specialize, val_lt_val, zpow_natCast, zpow_neg
-/
lemma map_eq_one_of_forall_lt [MulArchimedean Γ₀] {v : Valuation K Γ₀} {r : Γ₀} (hr : r != 0)
    (h : forall x : K, v x != 0 -> r < v x) (x : K) (hx : v x != 0) : v x = 1 := by
  lift r to Γ₀ˣ using IsUnit.mk0 _ hr
  rcases lt_trichotomy (Units.mk0 _ hx) 1 with H | H | H
  · obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ k) (by simp [hx])
    simp [← Units.val_lt_val, ← map_pow, h.not_gt] at hk
  · simpa [Units.ext_iff] using H
  · rw [← inv_lt_one'] at H
    obtain ⟨k, hk⟩ := exists_pow_lt H r
    specialize h (x ^ (-k : Int)) (by simp [hx])
    simp only [zpow_neg, zpow_natCast, map_inv₀, map_pow] at h
    simp [← Units.val_lt_val, h.not_gt, inv_pow] at hk

/--
theorem `subgroups_basis` / 定理 `subgroups_basis`

English:
theorem subgroups_basis
  proof: { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      have hmin : embedding (min γ₀.1 γ₁.1) = min (embedding γ₀.1) (embedding γ₁.1) :=
        embedding_strictMono.monotone.map_inf γ₀.1 γ₁.1
      simp [ltAddSubgroup, hmin]
      tauto
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, AddSubgroup.coe_set_mk,
        AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, mem_ofPred_eq] at r_in s_in
      simp only [coe_ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, mem_ofPred_eq]
      rw [← restrict_lt_iff_lt_embedding] at *
      calc
        v.restrict (r * s) = v.restrict r * v.restrict s := Valuation.map_mul _ _ _
        _ < γ₀.1 * γ₀.1 := by gcongr <;> exact zero_le
        _ <= γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : (ValueGroup₀ (.ofClass v))ˣ)
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul]; rw [Hx]; rw [zero_mul]
        exact Units.zero_lt _
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by
          simp [restrict₀_apply, embedding_apply, hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul]; rw [Hx]; rw [mul_comm]
        rw [Units.val_mul]; rw [mul_comm]; rw [map_mul]; rw [hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx,
          mul_zero, Units.zero_lt]
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by simp [restrict₀_apply, embedding_apply,
          hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx]
        rw [Units.val_mul]; rw [mul_comm]; rw [map_mul]; rw [hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

中文:
定理 subgroups_basis
  证明: { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      have hmin : embedding (min γ₀.1 γ₁.1) = min (embedding γ₀.1) (embedding γ₁.1) :=
        embedding_strictMono.monotone.map_inf γ₀.1 γ₁.1
      simp [ltAddSubgroup, hmin]
      tauto
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, AddSubgroup.coe_set_mk,
        AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, mem_ofPred_eq] at r_in s_in
      simp only [coe_ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, mem_ofPred_eq]
      rw [← restrict_lt_iff_lt_embedding] at *
      calc
        v.restrict (r * s) = v.restrict r * v.restrict s := Valuation.map_mul _ _ _
        _ < γ₀.1 * γ₀.1 := by gcongr <;> exact zero_le
        _ <= γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : (ValueGroup₀ (.ofClass v))ˣ)
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul]; rw [Hx]; rw [zero_mul]
        exact Units.zero_lt _
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by
          simp [restrict₀_apply, embedding_apply, hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul]; rw [Hx]; rw [mul_comm]
        rw [Units.val_mul]; rw [mul_comm]; rw [map_mul]; rw [hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx,
          mul_zero, Units.zero_lt]
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by simp [restrict₀_apply, embedding_apply,
          hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx]
        rw [Units.val_mul]; rw [mul_comm]; rw [map_mul]; rw [hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

Depends on / 依赖: ofClass
-/
theorem subgroups_basis :
    RingSubgroupsBasis fun γ : (ValueGroup₀ (.ofClass v))ˣ =>
v.ltAddSubgroup Units.map (ValueGroup₀.embedding (f := (.ofClass v))) γ :=
  { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      have hmin : embedding (min γ₀.1 γ₁.1) = min (embedding γ₀.1) (embedding γ₁.1) :=
        embedding_strictMono.monotone.map_inf γ₀.1 γ₁.1
      simp [ltAddSubgroup, hmin]
      tauto
    mul := by
      rintro γ
      obtain ⟨γ₀, h⟩ := exists_square_le γ
      use γ₀
      rintro - ⟨r, r_in, s, s_in, rfl⟩
      simp only [ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, AddSubgroup.coe_set_mk,
        AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, mem_ofPred_eq] at r_in s_in
      simp only [coe_ltAddSubgroup, Units.coe_map, MonoidHom.coe_coe, mem_ofPred_eq]
      rw [← restrict_lt_iff_lt_embedding] at *
      calc
        v.restrict (r * s) = v.restrict r * v.restrict s := Valuation.map_mul _ _ _
        _ < γ₀.1 * γ₀.1 := by gcongr <;> exact zero_le
        _ <= γ := mod_cast h
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : (ValueGroup₀ (.ofClass v))ˣ)
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul]; rw [Hx]; rw [zero_mul]
        exact Units.zero_lt _
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by
          simp [restrict₀_apply, embedding_apply, hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq]
        rw [Valuation.map_mul]; rw [Hx]; rw [mul_comm]
        rw [Units.val_mul]; rw [mul_comm]; rw [map_mul]; rw [hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y _
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx,
          mul_zero, Units.zero_lt]
      · set u : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 ((restrict₀ (.ofClass v)) x)
          (by simp [restrict₀_apply]; aesop) with hu_def
        have hu : ValueGroup₀.embedding u⁻¹.1 = γx⁻¹ := by simp [restrict₀_apply, embedding_apply,
          hu_def, Hx]
        use u⁻¹ * γ
        rintro y (vy_lt : v y < ValueGroup₀.embedding (u⁻¹ * γ).1)
        simp only [coe_ltAddSubgroup, preimage_ofPred_eq, mem_ofPred_eq, Valuation.map_mul, Hx]
        rw [Units.val_mul]; rw [mul_comm]; rw [map_mul]; rw [hu] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }

end Valuation

/--
Definition of `Valued` / `Valued` 的定义

English:
class Valued
  parameters: (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  extends: UniformSpace R, IsUniformAddGroup R
  axioms and operations (2):
    - v : Valuation R Γ₀
    - is_topological_valuation : forall s, s in 𝓝 (0 : R) ↔ exists γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ, { x : R | v.restrict x < γ.1 } subseteq s

中文:
类 赋值
  参数: (R : 类型u) [环 R] (Γ₀ : outParam (类型v))
  继承: 一致空间 R, 是UniformAdd群 R
  公理与运算 (2 个):
    - v : 赋值 R Γ₀
    - is_topological_valuation : 对任意 s, s in 𝓝 (0 : R) ↔ 存在 γ : (带零幺半群态射.ValueGroup₀ (.ofClass v))ˣ, { x : R | v.restrict x < γ.1 } subseteq s
-/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, IsUniformAddGroup R where
  v : Valuation R Γ₀
  is_topological_valuation : forall s, s in 𝓝 (0 : R) ↔
    exists γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ, { x : R | v.restrict x < γ.1 } subseteq s

namespace Valued

/-- Alternative `Valued` constructor for use when there is no preferred `UniformSpace` structure. -/
@[instance_reducible]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (v : Valuation R Γ₀)
  body: { v
    toUniformSpace := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      let := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      simp_rw [restrict_lt_iff_lt_embedding]
      exact exists_congr fun γ => by rw [true_and]; rfl }

中文:
定义 mk'
  签名: (v : 赋值 R Γ₀)
  定义体: { v
    toUniformSpace := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      let := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      simp_rw [restrict_lt_iff_lt_embedding]
      exact exists_congr fun γ => by rw [true_and]; rfl }

Depends on / 依赖: Filter, Filter.hasBasis_iff.mp, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, exists_congr, hasBasis_iff, hasBasis_nhds_zero, isUniformAddGroup_of_addCommGroup, is_topological_valuation, restrict_lt_iff_lt_embedding, rightUniformSpace, simp_rw, subgroups_basis, toIsUniformAddGroup, toUniformSpace, topology, true_and, v.subgroups_basis.hasBasis_nhds_zero, v.subgroups_basis.topology
-/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { v
    toUniformSpace := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
    toIsUniformAddGroup := @isUniformAddGroup_of_addCommGroup _ _ v.subgroups_basis.topology _
    is_topological_valuation := by
      let := @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [Filter.hasBasis_iff.mp v.subgroups_basis.hasBasis_nhds_zero s]
      simp_rw [restrict_lt_iff_lt_embedding]
      exact exists_congr fun γ => by rw [true_and]; rfl }

variable (R Γ₀)
variable [_i : Valued R Γ₀]

/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  proof: by
  simp [Filter.hasBasis_iff, is_topological_valuation]

中文:
定理 hasBasis_nhds_zero
  证明: by
  simp [Filter.hasBasis_iff, is_topological_valuation]

Depends on / 依赖: Filter, Filter.hasBasis_iff, hasBasis_iff, is_topological_valuation
-/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v.restrict x < γ.1 } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]

open Uniformity in
/--
theorem `hasBasis_uniformity` / 定理 `hasBasis_uniformity`

English:
theorem hasBasis_uniformity
  statement: (𝓤 R).HasBasis (fun _ => True)
  proof: by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

中文:
定理 hasBasis_uniformity
  结论: (𝓤 R).有基 (fun _ => 真)
  证明: by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

Depends on / 依赖: hasBasis_nhds_zero, uniformity_eq_comap_nhds_zero
-/
theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ => True)
    fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ =>
      { p : R × R | v.restrict (p.2 - p.1) < γ.1 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact (hasBasis_nhds_zero R Γ₀).comap _

/--
theorem `toUniformSpace_eq` / 定理 `toUniformSpace_eq`

English:
theorem toUniformSpace_eq
  statement: toUniformSpace =
  proof: by
  refine UniformSpace.ext ((hasBasis_uniformity R Γ₀).eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp_rw [restrict_lt_iff_lt_embedding, sub_eq_add_neg]
  simp

中文:
定理 toUniformSpace_eq
  结论: toUniformSpace =
  证明: by
  refine UniformSpace.ext ((hasBasis_uniformity R Γ₀).eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp_rw [restrict_lt_iff_lt_embedding, sub_eq_add_neg]
  simp

Depends on / 依赖: UniformSpace, UniformSpace.ext, convert, eq_of_same_basis, hasBasis_nhds_zero, hasBasis_uniformity, restrict_lt_iff_lt_embedding, simp_rw, sub_eq_add_neg, subgroups_basis, v.subgroups_basis.hasBasis_nhds_zero.comap
-/
theorem toUniformSpace_eq : toUniformSpace =
    @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _ := by
  refine UniformSpace.ext ((hasBasis_uniformity R Γ₀).eq_of_same_basis ?_)
  convert! v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp_rw [restrict_lt_iff_lt_embedding, sub_eq_add_neg]
  simp

variable {R Γ₀}

/--
theorem `mem_nhds` / 定理 `mem_nhds`

English:
theorem mem_nhds
  given: {s : Set R} {x : R}
  statement: s in 𝓝 x ↔
  proof: by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_ofPred_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

中文:
定理 mem_nhds
  条件: {s : 集合 R} {x : R}
  结论: s in 𝓝 x ↔
  证明: by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_ofPred_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

Depends on / 依赖: hasBasis_nhds_zero, mem_iff, nhds_translation_add_neg, preimage_ofPred_eq, sub_eq_add_neg, true_and
-/
theorem mem_nhds {s : Set R} {x : R} : s in 𝓝 x ↔
    exists γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ,
    { y | (v.restrict (y - x) ) < γ.1 } subseteq s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_ofPred_eq, true_and,
    ((hasBasis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]

/--
theorem `mem_nhds_zero` / 定理 `mem_nhds_zero`

English:
theorem mem_nhds_zero
  given: {s : Set R}
  statement: s in 𝓝 (0 : R) ↔
  proof: by
  simp only [mem_nhds, sub_zero]

中文:
定理 mem_nhds_zero
  条件: {s : 集合 R}
  结论: s in 𝓝 (0 : R) ↔
  证明: by
  simp only [mem_nhds, sub_zero]

Depends on / 依赖: mem_nhds, sub_zero
-/
theorem mem_nhds_zero {s : Set R} : s in 𝓝 (0 : R) ↔
    exists γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { x | v.restrict x < γ.1 } subseteq s := by
  simp only [mem_nhds, sub_zero]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `locally_const` / 定理 `locally_const`

English:
theorem locally_const
  given: {x : R} (h : (v x : Γ₀) != 0)
  statement: { y : R | v y = v x } in 𝓝 x
  proof: by
  rw [mem_nhds]
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
  rw [mem_nhds]
  have h' : v.restrict x != 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

Depends on / 依赖: Units.mk0, Units.val_mk0, Valuation, Valuation.map_eq_of_sub_lt, map_eq_of_sub_lt, mem_nhds, restrict, restrict_lt_iff, v.restrict, v.restrict_lt_iff.mp, val_mk0, y_in
-/
theorem locally_const {x : R} (h : (v x : Γ₀) != 0) : { y : R | v y = v x } in 𝓝 x := by
  rw [mem_nhds]
  have h' : v.restrict x != 0 := by simp [h]
  use Units.mk0 _ h'
  rw [Units.val_mk0]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ (v.restrict_lt_iff.mp y_in)

instance (priority := 100) : IsTopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

section Discrete

/--
lemma `discreteTopology_of_forall_map_eq_one` / 引理 `discreteTopology_of_forall_map_eq_one`

English:
lemma discreteTopology_of_forall_map_eq_one
  given: (h : forall x : R, x != 0 -> v x = 1)
  proof: by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, mem_nhds_zero, subset_singleton_iff, mem_ofPred_eq]
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
    forall_eq, mem_nhds_zero, subset_singleton_iff, mem_ofPred_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding]; rw [Units.val_one]; rw [map_one] at hx
  exact ⟨x, hx', hx.ne⟩

Depends on / 依赖: Units.val_one, contrapose, discreteTopology_iff_isOpen_singleton_zero, forall_eq, hx.ne, isOpen_iff_mem_nhds, map_one, mem_nhds_zero, mem_ofPred_eq, mem_singleton_iff, restrict_lt_iff_lt_embedding, subset_singleton_iff, val_one
-/
lemma discreteTopology_of_forall_map_eq_one (h : forall x : R, x != 0 -> v x = 1) :
    DiscreteTopology R := by
  simp only [discreteTopology_iff_isOpen_singleton_zero, isOpen_iff_mem_nhds, mem_singleton_iff,
    forall_eq, mem_nhds_zero, subset_singleton_iff, mem_ofPred_eq]
  use 1
  contrapose! h
  obtain ⟨x, hx, hx'⟩ := h
  rw [restrict_lt_iff_lt_embedding]; rw [Units.val_one]; rw [map_one] at hx
  exact ⟨x, hx', hx.ne⟩

/--
lemma `discreteTopology_of_forall_lt` / 引理 `discreteTopology_of_forall_lt`

English:
lemma discreteTopology_of_forall_lt
  statement: [MulArchimedean Γ₀] [Valued K Γ₀] {r : Γ₀} (hr : r != 0)
  proof: discreteTopology_of_forall_map_eq_one (by simpa using Valued.v.map_eq_one_of_forall_lt hr h)

中文:
引理 discreteTopology_of_对任意_lt
  结论: [MulArchimedean Γ₀] [赋值 K Γ₀] {r : Γ₀} (hr : r != 0)
  证明: discreteTopology_of_forall_map_eq_one (by simpa using Valued.v.map_eq_one_of_forall_lt hr h)

Depends on / 依赖: Valued, Valued.v.map_eq_one_of_forall_lt, discreteTopology_of_forall_map_eq_one, map_eq_one_of_forall_lt
-/
lemma discreteTopology_of_forall_lt [MulArchimedean Γ₀] [Valued K Γ₀] {r : Γ₀} (hr : r != 0)
    (h : forall x : K, v x != 0 -> r < v x) :
    DiscreteTopology K :=
  discreteTopology_of_forall_map_eq_one (by simpa using Valued.v.map_eq_one_of_forall_lt hr h)

end Discrete

/--
theorem `cauchy_iff` / 定理 `cauchy_iff`

English:
theorem cauchy_iff
  given: {F : Filter R}
  statement: Cauchy F ↔
  proof: by
  rw [toUniformSpace_eq]; rw [AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

中文:
定理 cauchy_iff
  条件: {F : 滤子 R}
  结论: Cauchy F ↔
  证明: by
  rw [toUniformSpace_eq]; rw [AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

Depends on / 依赖: AddGroupFilterBasis, AddGroupFilterBasis.cauchy_iff, Iff.rfl, Valued, Valued.v.subgroups_basis.mem_addGroupFilterBasis, Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff, and_congr, cauchy_iff, mem_addGroupFilterBasis, mem_addGroupFilterBasis_iff, restrict_lt_iff_lt_embedding, simp_rw, subgroups_basis, toUniformSpace_eq
-/
theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ forall γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ,
      exists M in F, forallᵉ (x in M) (y in M), _i.v.restrict (y - x) < γ.1 := by
  rw [toUniformSpace_eq]; rw [AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [Valued.v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (Valued.v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

variable (R)

/--
theorem `isOpen_ball` / 定理 `isOpen_ball`

English:
theorem isOpen_ball
  given: (r : ValueGroup₀ (.ofClass _i.v))
  proof: by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

中文:
定理 isOpen_ball
  条件: (r : ValueGroup₀ (.ofClass _i.v))
  证明: by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

Depends on / 依赖: Units.mk0, eq_or_ne, isOpen_iff_mem_nhds, map_add, max_lt, mem_nhds, ofPred_subset_ofPred, restrict, sub_add_cancel, trans_lt, v.restrict.map_add
-/
theorem isOpen_ball (r : ValueGroup₀ (.ofClass _i.v)) :
    IsOpen {x | v.restrict x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr,
    fun y hy => (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

/--
theorem `isClosed_ball` / 定理 `isClosed_ball`

English:
theorem isClosed_ball
  given: (r : ValueGroup₀ (.ofClass _i.v))
  proof: by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _ _)

中文:
定理 isClosed_ball
  条件: (r : ValueGroup₀ (.ofClass _i.v))
  证明: by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _ _)

Depends on / 依赖: AddSubgroup, AddSubgroup.isClosed_of_isOpen, Units.mk0, Valuation, Valuation.ltAddSubgroup, eq_or_ne, isClosed_of_isOpen, isOpen_ball, ltAddSubgroup, restrict, v.restrict
-/
theorem isClosed_ball (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClosed {x | v.restrict x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _ _)

/--
theorem `isClopen_ball` / 定理 `isClopen_ball`

English:
theorem isClopen_ball
  given: (r : ValueGroup₀ (.ofClass _i.v))
  proof: ⟨isClosed_ball _ _, isOpen_ball _ _⟩

中文:
定理 isClopen_ball
  条件: (r : ValueGroup₀ (.ofClass _i.v))
  证明: ⟨isClosed_ball _ _, isOpen_ball _ _⟩

Depends on / 依赖: isClosed_ball, isOpen_ball
-/
theorem isClopen_ball (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClopen {x | v.restrict x < r} :=
  ⟨isClosed_ball _ _, isOpen_ball _ _⟩

/--
theorem `isOpen_closedBall` / 定理 `isOpen_closedBall`

English:
theorem isOpen_closedBall
  given: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  proof: by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy =>
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

中文:
定理 isOpen_closedBall
  条件: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  证明: by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy =>
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

Depends on / 依赖: Units.mk0, isOpen_iff_mem_nhds, le_of_lt, le_trans, map_add, max_le, mem_nhds, ofPred_subset_ofPred, restrict, sub_add_cancel, v.restrict.map_add
-/
theorem isOpen_closedBall {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) :
  IsOpen {x | v.restrict x <= r} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds]
  simp only [ofPred_subset_ofPred]
  exact ⟨Units.mk0 _ hr, fun y hy =>
    (sub_add_cancel y x).symm ▸ le_trans (v.restrict.map_add _ _) (max_le (le_of_lt hy) hx)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isClosed_closedBall` / 定理 `isClosed_closedBall`

English:
theorem isClosed_closedBall
  given: (r : ValueGroup₀ (.ofClass _i.v))
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v.restrict x != 0 := hx.ne_zero
exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

中文:
定理 isClosed_closedBall
  条件: (r : ValueGroup₀ (.ofClass _i.v))
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v.restrict x != 0 := hx.ne_zero
exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

Depends on / 依赖: Units.mk0, Valuation, Valuation.map_sub_eq_of_lt_left, hx.ne_zero, isOpen_compl_iff, isOpen_iff_mem_nhds, lt_of_le_of_lt, map_sub_eq_of_lt_left, map_sub_swap, mem_compl_iff, mem_nhds, mem_ofPred_eq, ne_of_lt, ne_zero, not_le, restrict, v.restrict
-/
theorem isClosed_closedBall (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClosed {x | v.restrict x <= r} := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hx
  rw [mem_nhds]
  have hx' : v.restrict x != 0 := hx.ne_zero
exact ⟨Units.mk0 _ hx', fun y hy hy' => ne_of_lt hy map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

/--
theorem `isClopen_closedBall` / 定理 `isClopen_closedBall`

English:
theorem isClopen_closedBall
  given: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  proof: ⟨isClosed_closedBall _ _, isOpen_closedBall _ hr⟩

中文:
定理 isClopen_closedBall
  条件: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  证明: ⟨isClosed_closedBall _ _, isOpen_closedBall _ hr⟩

Depends on / 依赖: isClosed_closedBall, isOpen_closedBall
-/
theorem isClopen_closedBall {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) :
    IsClopen {x | v.restrict x <= r} :=
  ⟨isClosed_closedBall _ _, isOpen_closedBall _ hr⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isClopen_sphere` / 定理 `isClopen_sphere`

English:
theorem isClopen_sphere
  given: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  proof: by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x <= r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall _ hr) (isClopen_ball _ _)

中文:
定理 isClopen_sphere
  条件: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  证明: by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x <= r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall _ hr) (isClopen_ball _ _)

Depends on / 依赖: IsClopen, IsClopen.diff, isClopen_ball, isClopen_closedBall, le_antisymm_iff, restrict, v.restrict
-/
theorem isClopen_sphere {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) :
    IsClopen {x | v.restrict x = r} := by
  have h : {x : R | v.restrict x = r} = {x | v.restrict x <= r} \ {x | v.restrict x < r} := by
    ext x
    simp [← le_antisymm_iff]
  rw [h]
  exact IsClopen.diff (isClopen_closedBall _ hr) (isClopen_ball _ _)

/--
theorem `isOpen_sphere` / 定理 `isOpen_sphere`

English:
theorem isOpen_sphere
  given: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  proof: .isOpen isClopen_sphere _ hr

中文:
定理 isOpen_sphere
  条件: {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0)
  证明: .isOpen isClopen_sphere _ hr

Depends on / 依赖: isClopen_sphere, isOpen
-/
theorem isOpen_sphere {r : ValueGroup₀ (.ofClass _i.v)} (hr : r != 0) :
    IsOpen {x | v.restrict x = r} :=
.isOpen isClopen_sphere _ hr

/--
theorem `isClosed_sphere` / 定理 `isClosed_sphere`

English:
theorem isClosed_sphere
  given: (r : ValueGroup₀ (.ofClass _i.v))
  proof: by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa using isClosed_closedBall R 0
.isClosed exact isClopen_sphere _ hr

中文:
定理 isClosed_sphere
  条件: (r : ValueGroup₀ (.ofClass _i.v))
  证明: by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa using isClosed_closedBall R 0
.isClosed exact isClopen_sphere _ hr

Depends on / 依赖: eq_or_ne, isClopen_sphere, isClosed, isClosed_closedBall
-/
theorem isClosed_sphere (r : ValueGroup₀ (.ofClass _i.v)) :
    IsClosed {x | v.restrict x = r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simpa using isClosed_closedBall R 0
.isClosed exact isClopen_sphere _ hr

/--
theorem `isOpen_integer` / 定理 `isOpen_integer`

English:
theorem isOpen_integer
  statement: IsOpen (_i.v.integer : Set R)
  proof: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isOpen_closedBall _ one_ne_zero

中文:
定理 isOpen_integer
  结论: 是开集 (_i.v.integer : 集合 R)
  证明: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isOpen_closedBall _ one_ne_zero

Depends on / 依赖: Submonoid, Submonoid.coe_set_mk, Subring, Subring.coe_set_mk, Subsemigroup, Subsemigroup.coe_set_mk, Subsemiring, Subsemiring.coe_set_mk, coe_set_mk, integer, isOpen_closedBall, one_ne_zero, restrict_le_one_iff, v.restrict_le_one_iff
-/
theorem isOpen_integer : IsOpen (_i.v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isOpen_closedBall _ one_ne_zero

/--
theorem `isClosed_integer` / 定理 `isClosed_integer`

English:
theorem isClosed_integer
  statement: IsClosed (_i.v.integer : Set R)
  proof: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _ _

中文:
定理 isClosed_integer
  结论: 是闭集 (_i.v.integer : 集合 R)
  证明: by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _ _

Depends on / 依赖: Submonoid, Submonoid.coe_set_mk, Subring, Subring.coe_set_mk, Subsemigroup, Subsemigroup.coe_set_mk, Subsemiring, Subsemiring.coe_set_mk, coe_set_mk, integer, isClosed_closedBall, restrict_le_one_iff, v.restrict_le_one_iff
-/
theorem isClosed_integer : IsClosed (_i.v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _ _

/--
theorem `isClopen_integer` / 定理 `isClopen_integer`

English:
theorem isClopen_integer
  statement: IsClopen (_i.v.integer : Set R)
  proof: ⟨isClosed_integer _, isOpen_integer _⟩

中文:
定理 isClopen_integer
  结论: IsClopen (_i.v.integer : 集合 R)
  证明: ⟨isClosed_integer _, isOpen_integer _⟩

Depends on / 依赖: isClosed_integer, isOpen_integer
-/
theorem isClopen_integer : IsClopen (_i.v.integer : Set R) :=
  ⟨isClosed_integer _, isOpen_integer _⟩

/--
theorem `isOpen_valuationSubring` / 定理 `isOpen_valuationSubring`

English:
theorem isOpen_valuationSubring
  given: (K : Type u) [Field K] [hv : Valued K Γ₀]
  proof: isOpen_integer K

中文:
定理 isOpen_valuationSubring
  条件: (K : 类型u) [域 K] [hv : 赋值 K Γ₀]
  证明: isOpen_integer K

Depends on / 依赖: isOpen_integer
-/
theorem isOpen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsOpen (hv.v.valuationSubring : Set K) :=
  isOpen_integer K

/--
theorem `isClosed_valuationSubring` / 定理 `isClosed_valuationSubring`

English:
theorem isClosed_valuationSubring
  given: (K : Type u) [Field K] [hv : Valued K Γ₀]
  proof: isClosed_integer K

中文:
定理 isClosed_valuationSubring
  条件: (K : 类型u) [域 K] [hv : 赋值 K Γ₀]
  证明: isClosed_integer K

Depends on / 依赖: isClosed_integer
-/
theorem isClosed_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClosed (hv.v.valuationSubring : Set K) :=
  isClosed_integer K

/--
theorem `isClopen_valuationSubring` / 定理 `isClopen_valuationSubring`

English:
theorem isClopen_valuationSubring
  given: (K : Type u) [Field K] [hv : Valued K Γ₀]
  proof: isClopen_integer K

中文:
定理 isClopen_valuationSubring
  条件: (K : 类型u) [域 K] [hv : 赋值 K Γ₀]
  证明: isClopen_integer K

Depends on / 依赖: isClopen_integer
-/
theorem isClopen_valuationSubring (K : Type u) [Field K] [hv : Valued K Γ₀] :
    IsClopen (hv.v.valuationSubring : Set K) :=
  isClopen_integer K

end Valued
