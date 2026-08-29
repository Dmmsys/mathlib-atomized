/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Submonoid.Center

/-!
# Centers of subgroups

-/

@[expose] public section

assert_not_exists MonoidWithZero Multiset

variable {G : Type*} [Group G]

namespace Subgroup

variable (G)

/-- The center of a group `G` is the set of elements that commute with everything in `G` -/
@[to_additive
      /-- The center of an additive group `G` is the set of elements that commute with
      everything in `G` -/]
/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : Subgroup G where
  body: Submonoid.center G
  inv_mem' := Set.inv_mem_center

@[to_additive]

中文:
定义 center
  签名: : 子群 G where
  定义体: Submonoid.center G
  inv_mem' := Set.inv_mem_center

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.center, center
-/
def center : Subgroup G where
  __ := Submonoid.center G
  inv_mem' := Set.inv_mem_center

@[to_additive]
/--
theorem `coe_center` / 定理 `coe_center`

English:
theorem coe_center
  statement: ↑(center G) = Set.center G
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_center
  结论: ↑(center G) = 集合.center G
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_center : ↑(center G) = Set.center G :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `center_toSubmonoid` / 定理 `center_toSubmonoid`

English:
theorem center_toSubmonoid
  statement: (center G).toSubmonoid = Submonoid.center G
  proof: rfl

中文:
定理 center_toSubmonoid
  结论: (center G).toSubmonoid = 子幺半群.center G
  证明: rfl
-/
theorem center_toSubmonoid : (center G).toSubmonoid = Submonoid.center G :=
  rfl

/--
Instance `center.isMulCommutative` / 实例 `center.isMulCommutative`

English:
instance center.isMulCommutative
  signature: : IsMulCommutative (center G)
  body: ⟨⟨fun a b => Subtype.ext (b.2.comm a).symm⟩⟩

中文:
实例 center.isMulCommutative
  签名: : 是MulCommutative (center G)
  定义体: ⟨⟨fun a b => Subtype.ext (b.2.comm a).symm⟩⟩

Depends on / 依赖: Subtype, Subtype.ext
-/
instance center.isMulCommutative : IsMulCommutative (center G) :=
  ⟨⟨fun a b => Subtype.ext (b.2.comm a).symm⟩⟩

variable {G} in
/-- The center of isomorphic groups are isomorphic. -/
@[to_additive (attr := simps!) /-- The center of isomorphic additive groups are isomorphic. -/]
/--
Definition of `centerCongr` / `centerCongr` 的定义

English:
definition centerCongr
  signature: {H} [Group H] (e : G ≃* H)
  body: Submonoid.centerCongr e

中文:
定义 centerCongr
  签名: {H} [群 H] (e : G ≃* H)
  定义体: Submonoid.centerCongr e

Depends on / 依赖: Submonoid, Submonoid.centerCongr, centerCongr
-/
def centerCongr {H} [Group H] (e : G ≃* H) : center G ≃* center H := Submonoid.centerCongr e

/-- The center of a group is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps!)
/-- The center of an additive group is isomorphic to the center of its opposite. -/]
/--
Definition of `centerToMulOpposite` / `centerToMulOpposite` 的定义

English:
definition centerToMulOpposite
  signature: : center G ≃* center Gᵐᵒᵖ
  body: Submonoid.centerToMulOpposite

中文:
定义 centerToMulOpposite
  签名: : center G ≃* center Gᵐᵒᵖ
  定义体: Submonoid.centerToMulOpposite

Depends on / 依赖: Submonoid, Submonoid.centerToMulOpposite, centerToMulOpposite
-/
def centerToMulOpposite : center G ≃* center Gᵐᵒᵖ := Submonoid.centerToMulOpposite

variable {G}

@[to_additive]
/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {z : G}
  statement: z in center G ↔ forall g, g * z = z * g
  proof: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

中文:
定理 mem_center_iff
  条件: {z : G}
  结论: z in center G ↔ 对任意 g, g * z = z * g
  证明: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

Depends on / 依赖: Iff.rfl, Semigroup, Semigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {z : G} : z in center G ↔ forall g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: (z : G) [Decidable (forall g, g * z = z * g)]
  body: decidable_of_iff' _ mem_center_iff

@[to_additive]

中文:
实例 decidableMemCenter
  签名: (z : G) [可判定 (对任意 g, g * z = z * g)]
  定义体: decidable_of_iff' _ mem_center_iff

@[to_additive]

Depends on / 依赖: decidable_of_iff, mem_center_iff
-/
instance decidableMemCenter (z : G) [Decidable (forall g, g * z = z * g)] : Decidable (z in center G) :=
  decidable_of_iff' _ mem_center_iff

@[to_additive]
/--
Instance `centerCharacteristic` / 实例 `centerCharacteristic`

English:
instance centerCharacteristic
  signature: : (center G).Characteristic
  body: by
  refine characteristic_iff_comap_le.mpr fun ϕ g hg => ?_
  rw [mem_center_iff]
  intro h
  rw [← ϕ.injective.eq_iff]; rw [map_mul]; rw [map_mul]
  exact (hg.comm (ϕ h)).symm

@[to_additive]

中文:
实例 centerCharacteristic
  签名: : (center G).特征
  定义体: by
  refine characteristic_iff_comap_le.mpr fun ϕ g hg => ?_
  rw [mem_center_iff]
  intro h
  rw [← ϕ.injective.eq_iff]; rw [map_mul]; rw [map_mul]
  exact (hg.comm (ϕ h)).symm

@[to_additive]

Depends on / 依赖: characteristic_iff_comap_le, characteristic_iff_comap_le.mpr, eq_iff, hg.comm, injective, injective.eq_iff, map_mul, mem_center_iff
-/
instance centerCharacteristic : (center G).Characteristic := by
  refine characteristic_iff_comap_le.mpr fun ϕ g hg => ?_
  rw [mem_center_iff]
  intro h
  rw [← ϕ.injective.eq_iff]; rw [map_mul]; rw [map_mul]
  exact (hg.comm (ϕ h)).symm

@[to_additive]
/--
theorem `_root_.CommGroup.center_eq_top` / 定理 `_root_.CommGroup.center_eq_top`

English:
theorem _root_.CommGroup.center_eq_top
  given: {G : Type*} [CommGroup G]
  statement: center G = ⊤
  proof: by
  rw [eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  exact mul_comm y x

@[to_additive]

中文:
定理 _root_.交换群.center_eq_top
  条件: {G : 类型} [交换群 G]
  结论: center G = ⊤
  证明: by
  rw [eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  exact mul_comm y x

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.mem_center_iff, eq_top_iff, mem_center_iff, mul_comm
-/
theorem _root_.CommGroup.center_eq_top {G : Type*} [CommGroup G] : center G = ⊤ := by
  rw [eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  exact mul_comm y x

@[to_additive]
/--
theorem `center_eq_top_iff` / 定理 `center_eq_top_iff`

English:
theorem center_eq_top_iff
  statement: center G = ⊤ ↔ IsMulCommutative G
  proof: by
  simp [eq_top_iff', isMulCommutative_iff, mem_center_iff, eq_comm]

@[to_additive]

中文:
定理 center_eq_top_iff
  结论: center G = ⊤ ↔ 是MulCommutative G
  证明: by
  simp [eq_top_iff', isMulCommutative_iff, mem_center_iff, eq_comm]

@[to_additive]

Depends on / 依赖: eq_comm, eq_top_iff, isMulCommutative_iff, mem_center_iff
-/
theorem center_eq_top_iff : center G = ⊤ ↔ IsMulCommutative G := by
  simp [eq_top_iff', isMulCommutative_iff, mem_center_iff, eq_comm]

@[to_additive]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  given: [hG : IsMulCommutative G]
  statement: center G = ⊤
  proof: center_eq_top_iff.mpr hG

中文:
定理 center_eq_top
  条件: [hG : 是MulCommutative G]
  结论: center G = ⊤
  证明: center_eq_top_iff.mpr hG

Depends on / 依赖: center_eq_top_iff, center_eq_top_iff.mpr
-/
theorem center_eq_top [hG : IsMulCommutative G] : center G = ⊤ :=
    center_eq_top_iff.mpr hG

/-- A group is commutative if the center is the whole group. -/
@[to_additive /-- An additive group is commutative if the center is the whole group. -/,
  instance_reducible]
/--
Definition of `_root_.Group.commGroupOfCenterEqTop` / `_root_.Group.commGroupOfCenterEqTop` 的定义

English:
definition _root_.Group.commGroupOfCenterEqTop
  signature: (h : center G = ⊤)
  body: { ‹Group G› with
    mul_comm := by
      rw [eq_top_iff'] at h
      intro x y
      apply Subgroup.mem_center_iff.mp _ x
      exact h y
  }

@[to_additive]

中文:
定义 _root_.群.commGroupOfCenterEqTop
  签名: (h : center G = ⊤)
  定义体: { ‹Group G› with
    mul_comm := by
      rw [eq_top_iff'] at h
      intro x y
      apply Subgroup.mem_center_iff.mp _ x
      exact h y
  }

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.mem_center_iff.mp, eq_top_iff, mem_center_iff, mul_comm
-/
def _root_.Group.commGroupOfCenterEqTop (h : center G = ⊤) : CommGroup G :=
  { ‹Group G› with
    mul_comm := by
      rw [eq_top_iff'] at h
      intro x y
      apply Subgroup.mem_center_iff.mp _ x
      exact h y
  }

@[to_additive]
/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  given: {H : Type*} [Group H]
  statement: center (G × H) = prod (center G) (center H)
  proof: SetLike.coe_injective Set.center_prod

@[to_additive]

中文:
定理 center_prod
  条件: {H : 类型} [群 H]
  结论: center (G × H) = 乘积 (center G) (center H)
  证明: SetLike.coe_injective Set.center_prod

@[to_additive]

Depends on / 依赖: RelEmbedding, RelEmbedding.preimage, antisymm, preimage
-/
protected theorem center_prod {H : Type*} [Group H] : center (G × H) = prod (center G) (center H) :=
  SetLike.coe_injective Set.center_prod

@[to_additive]
/--
theorem `center_pi` / 定理 `center_pi`

English:
theorem center_pi
  given: {η : Type*} {G : η -> Type*} [Π i, Group (G i)]
  proof: SetLike.coe_injective Set.center_pi

中文:
定理 center_pi
  条件: {η : 类型} {G : η -> 类型} [Π i, 群 (G i)]
  证明: SetLike.coe_injective Set.center_pi

Depends on / 依赖: RelEmbedding, RelEmbedding.preimage, preimage
-/
protected theorem center_pi {η : Type*} {G : η -> Type*} [Π i, Group (G i)] :
    center (Π i, G i) = pi .univ fun i => center (G i) :=
  SetLike.coe_injective Set.center_pi

variable {H : Subgroup G}

section Normalizer

@[to_additive]
/--
Instance `instNormalCenter` / 实例 `instNormalCenter`

English:
instance instNormalCenter
  signature: : (center G).Normal
  body: ⟨fun a ha b => by simpa [mem_center_iff.mp ha b]⟩

@[to_additive]

中文:
实例 instNormalCenter
  签名: : (center G).正规
  定义体: ⟨fun a ha b => by simpa [mem_center_iff.mp ha b]⟩

@[to_additive]

Depends on / 依赖: mem_center_iff, mem_center_iff.mp
-/
instance instNormalCenter : (center G).Normal :=
  ⟨fun a ha b => by simpa [mem_center_iff.mp ha b]⟩

@[to_additive]
/--
theorem `center_le_normalizer` / 定理 `center_le_normalizer`

English:
theorem center_le_normalizer
  given: (s : Set G)
  statement: center G <= normalizer s
  proof: by
  intro x hx y
  simp [← mem_center_iff.mp hx y]

中文:
定理 center_le_normalizer
  条件: (s : 集合 G)
  结论: center G <= normalizer s
  证明: by
  intro x hx y
  simp [← mem_center_iff.mp hx y]

Depends on / 依赖: mem_center_iff, mem_center_iff.mp
-/
theorem center_le_normalizer (s : Set G) : center G <= normalizer s := by
  intro x hx y
  simp [← mem_center_iff.mp hx y]

end Normalizer

end Subgroup

namespace IsConj

variable {M : Type*} [Monoid M]

/--
theorem `eq_of_left_mem_center` / 定理 `eq_of_left_mem_center`

English:
theorem eq_of_left_mem_center
  given: {g h : M} (H : IsConj g h) (Hg : g in Set.center M)
  statement: g = h
  proof: by
  rcases H with ⟨u, hu⟩; rwa [← u.mul_left_inj, Hg.comm u]

中文:
定理 eq_of_left_mem_center
  条件: {g h : M} (H : IsConj g h) (Hg : g in 集合.center M)
  结论: g = h
  证明: by
  rcases H with ⟨u, hu⟩; rwa [← u.mul_left_inj, Hg.comm u]

Depends on / 依赖: Hg.comm, mul_left_inj, u.mul_left_inj
-/
theorem eq_of_left_mem_center {g h : M} (H : IsConj g h) (Hg : g in Set.center M) : g = h := by
  rcases H with ⟨u, hu⟩; rwa [← u.mul_left_inj, Hg.comm u]

/--
theorem `eq_of_right_mem_center` / 定理 `eq_of_right_mem_center`

English:
theorem eq_of_right_mem_center
  given: {g h : M} (H : IsConj g h) (Hh : h in Set.center M)
  statement: g = h
  proof: (H.symm.eq_of_left_mem_center Hh).symm

中文:
定理 eq_of_right_mem_center
  条件: {g h : M} (H : IsConj g h) (Hh : h in 集合.center M)
  结论: g = h
  证明: (H.symm.eq_of_left_mem_center Hh).symm

Depends on / 依赖: H.symm.eq_of_left_mem_center, eq_of_left_mem_center
-/
theorem eq_of_right_mem_center {g h : M} (H : IsConj g h) (Hh : h in Set.center M) : g = h :=
  (H.symm.eq_of_left_mem_center Hh).symm

end IsConj

namespace ConjClasses

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mk_bijOn` / 定理 `mk_bijOn`

English:
theorem mk_bijOn
  given: (G : Type*) [Group G]
  proof: by
  refine ⟨fun g hg => ?_, fun x hx y _ H => ?_, ?_⟩
  · simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff]
    intro x hx y hy
    simp only [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj] at hx hy
    rw [hx.eq_of_right_mem_center hg]; rw [hy.eq_of_right_mem_center hg]
  · rw [mk_eq_mk_iff_isConj] at H
    exact H.eq_of_left_mem_center hx
  · rintro ⟨g⟩ hg
    refine ⟨g, ?_, rfl⟩
    simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff] at hg
    rw [SetLike.mem_coe]; rw [Subgroup.mem_center_iff]
    intro h
    rw [← mul_inv_eq_iff_eq_mul]
    refine hg ?_ mem_carrier_mk
    rw [mem_carrier_iff_mk_eq]
    apply mk_eq_mk_iff_isConj.mpr
    rw [isConj_comm]; rw [isConj_iff]
    exact ⟨h, rfl⟩

中文:
定理 mk_bijOn
  条件: (G : 类型) [群 G]
  证明: by
  refine ⟨fun g hg => ?_, fun x hx y _ H => ?_, ?_⟩
  · simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff]
    intro x hx y hy
    simp only [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj] at hx hy
    rw [hx.eq_of_right_mem_center hg]; rw [hy.eq_of_right_mem_center hg]
  · rw [mk_eq_mk_iff_isConj] at H
    exact H.eq_of_left_mem_center hx
  · rintro ⟨g⟩ hg
    refine ⟨g, ?_, rfl⟩
    simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff] at hg
    rw [SetLike.mem_coe]; rw [Subgroup.mem_center_iff]
    intro h
    rw [← mul_inv_eq_iff_eq_mul]
    refine hg ?_ mem_carrier_mk
    rw [mem_carrier_iff_mk_eq]
    apply mk_eq_mk_iff_isConj.mpr
    rw [isConj_comm]; rw [isConj_iff]
    exact ⟨h, rfl⟩

Depends on / 依赖: H.eq_of_left_mem_center, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff, SetLike, SetLike.mem_coe, compl_def, eq_of_left_mem_center, eq_of_right_mem_center, hx.eq_of_right_mem_center, hy.eq_of_right_mem_center, mem_carrier_iff_mk_eq, mem_coe, mem_noncenter, mem_ofPred, mk_eq_mk_iff_isConj, not_nontrivial_iff
-/
theorem mk_bijOn (G : Type*) [Group G] :
    Set.BijOn ConjClasses.mk (↑(Subgroup.center G)) (noncenter G)ᶜ := by
  refine ⟨fun g hg => ?_, fun x hx y _ H => ?_, ?_⟩
  · simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff]
    intro x hx y hy
    simp only [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj] at hx hy
    rw [hx.eq_of_right_mem_center hg]; rw [hy.eq_of_right_mem_center hg]
  · rw [mk_eq_mk_iff_isConj] at H
    exact H.eq_of_left_mem_center hx
  · rintro ⟨g⟩ hg
    refine ⟨g, ?_, rfl⟩
    simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff] at hg
    rw [SetLike.mem_coe]; rw [Subgroup.mem_center_iff]
    intro h
    rw [← mul_inv_eq_iff_eq_mul]
    refine hg ?_ mem_carrier_mk
    rw [mem_carrier_iff_mk_eq]
    apply mk_eq_mk_iff_isConj.mpr
    rw [isConj_comm]; rw [isConj_iff]
    exact ⟨h, rfl⟩

end ConjClasses
