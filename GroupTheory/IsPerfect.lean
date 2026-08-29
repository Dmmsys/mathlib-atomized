/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inna Capdeboscq, Damiano Testa
-/
module

public import Mathlib.GroupTheory.Nilpotent

/-!
# Perfect groups

A group `G` is perfect if it equals its commutator subgroup, that is `⁅G, G⁆ = G`.

Among the basic results, we show that
* a nontrivial perfect group is not solvable (`IsPerfect.not_isSolvable`);
* an abelian perfect group is trivial (`IsPerfect.subsingleton_of_isMulCommutative`).

## Main Definition

* `Group.IsPerfect`: a group `G` is *perfect* if it equals its own commutator,
  that is `⁅⊤, ⊤⁆ = ⊤`, where `⊤` is the full subgroup `G`.

## Main Theorems

* `IsPerfect.map`: The image of a perfect group under a monoid homomorphism is perfect.
* `IsPerfect.instQuotientSubgroup`: The quotient of a perfect group by a normal subgroup is perfect.
* `IsPerfect.ofSurjective`: The image of a perfect group under a surjective monoid
  homomorphism is perfect.
-/

@[expose] public section

namespace Group
open Subgroup

variable {G G' : Type*} [Group G] [Group G'] {H K : Subgroup G} (f : G ->* G')

variable (G) in
/--
Definition of `IsPerfect` / `IsPerfect` 的定义

English:
class IsPerfect
  parameters: where
  axioms and operations (1):
    - commutator_eq_top : commutator G = (⊤ : Subgroup G)

中文:
类 是完美
  参数: where
  公理与运算 (1 个):
    - commutator_eq_top : commutator G = (⊤ : 子群 G)
-/
class IsPerfect where
  /-- The commutator of the group `G` with itself is the whole group `G`. -/
  commutator_eq_top : commutator G = (⊤ : Subgroup G)

attribute [simp] IsPerfect.commutator_eq_top

/--
lemma `isPerfect_def` / 引理 `isPerfect_def`

English:
lemma isPerfect_def
  statement: IsPerfect G ↔ commutator G = ⊤
  proof: ⟨fun h => h.commutator_eq_top, fun h => ⟨h⟩⟩

中文:
引理 isPerfect_def
  结论: 是完美 G ↔ commutator G = ⊤
  证明: ⟨fun h => h.commutator_eq_top, fun h => ⟨h⟩⟩

Depends on / 依赖: commutator_eq_top, h.commutator_eq_top
-/
lemma isPerfect_def : IsPerfect G ↔ commutator G = ⊤ :=
  ⟨fun h => h.commutator_eq_top, fun h => ⟨h⟩⟩

/--
lemma `_root_.Subgroup.isPerfect_iff` / 引理 `_root_.Subgroup.isPerfect_iff`

English:
lemma _root_.Subgroup.isPerfect_iff
  statement: IsPerfect H ↔ ⁅H, H⁆ = H
  proof: by
  rw [Group.isPerfect_def]; rw [← map_subtype_inj]; rw [map_subtype_commutator]; rw [← MonoidHom.range_eq_map]; rw [range_subtype]

中文:
引理 _root_.子群.isPerfect_iff
  结论: 是完美 H ↔ ⁅H, H⁆ = H
  证明: by
  rw [Group.isPerfect_def]; rw [← map_subtype_inj]; rw [map_subtype_commutator]; rw [← MonoidHom.range_eq_map]; rw [range_subtype]

Depends on / 依赖: Group.isPerfect_def, MonoidHom, MonoidHom.range_eq_map, isPerfect_def, map_subtype_commutator, map_subtype_inj, range_eq_map, range_subtype
-/
lemma _root_.Subgroup.isPerfect_iff : IsPerfect H ↔ ⁅H, H⁆ = H := by
  rw [Group.isPerfect_def]; rw [← map_subtype_inj]; rw [map_subtype_commutator]; rw [← MonoidHom.range_eq_map]; rw [range_subtype]

/--
lemma `_root_.Subgroup.commutator_eq_self` / 引理 `_root_.Subgroup.commutator_eq_self`

English:
lemma _root_.Subgroup.commutator_eq_self
  given: [hH : IsPerfect H]
  statement: ⁅H, H⁆ = H
  proof: isPerfect_iff.mp hH

中文:
引理 _root_.子群.commutator_eq_self
  条件: [hH : 是完美 H]
  结论: ⁅H, H⁆ = H
  证明: isPerfect_iff.mp hH

Depends on / 依赖: isPerfect_iff, isPerfect_iff.mp
-/
lemma _root_.Subgroup.commutator_eq_self [hH : IsPerfect H] : ⁅H, H⁆ = H :=
  isPerfect_iff.mp hH

namespace IsPerfect

/--
lemma `mem_commutator` / 引理 `mem_commutator`

English:
lemma mem_commutator
  given: [hP : IsPerfect G] {g : G}
  statement: g in commutator G
  proof: by
  simp

中文:
引理 mem_commutator
  条件: [hP : 是完美 G] {g : G}
  结论: g in commutator G
  证明: by
  simp
-/
lemma mem_commutator [hP : IsPerfect G] {g : G} : g in commutator G := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: G] : IsPerfect G where
  body: Subsingleton.elim _ _

中文:
实例 [子单例
  签名: G] : 是完美 G where
  定义体: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [Subsingleton G] : IsPerfect G where
  commutator_eq_top := Subsingleton.elim _ _

/--
theorem `top_iff` / 定理 `top_iff`

English:
theorem top_iff
  statement: IsPerfect (⊤ : Subgroup G) ↔ IsPerfect G
  proof: by
  rw [isPerfect_def]; rw [isPerfect_def]; rw [← map_subtype_inj]; rw [map_subtype_commutator]; rw [← MonoidHom.range_eq_map]; rw [subtype_range]; rw [commutator_def]

中文:
定理 top_iff
  结论: 是完美 (⊤ : 子群 G) ↔ 是完美 G
  证明: by
  rw [isPerfect_def]; rw [isPerfect_def]; rw [← map_subtype_inj]; rw [map_subtype_commutator]; rw [← MonoidHom.range_eq_map]; rw [subtype_range]; rw [commutator_def]

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_map, commutator_def, isPerfect_def, map_subtype_commutator, map_subtype_inj, range_eq_map, subtype_range
-/
theorem top_iff : IsPerfect (⊤ : Subgroup G) ↔ IsPerfect G := by
  rw [isPerfect_def]; rw [isPerfect_def]; rw [← map_subtype_inj]; rw [map_subtype_commutator]; rw [← MonoidHom.range_eq_map]; rw [subtype_range]; rw [commutator_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPerfect
  signature: G] : IsPerfect (⊤
  body: top_iff.mpr inferInstance

中文:
实例 [是完美
  签名: G] : 是完美 (⊤
  定义体: top_iff.mpr inferInstance

Depends on / 依赖: top_iff, top_iff.mpr
-/
instance [IsPerfect G] : IsPerfect (⊤ : Subgroup G) :=
  top_iff.mpr inferInstance

variable (G) in
/--
lemma `not_isSolvable` / 引理 `not_isSolvable`

English:
lemma not_isSolvable
  given: [Nontrivial G] [IsPerfect G]
  statement: ¬ IsSolvable G
  proof: by
  intro h
  exact (h.commutator_lt_top_of_nontrivial G).ne commutator_eq_top

中文:
引理 not_isSolvable
  条件: [非平凡 G] [是完美 G]
  结论: ¬ 是可解 G
  证明: by
  intro h
  exact (h.commutator_lt_top_of_nontrivial G).ne commutator_eq_top

Depends on / 依赖: commutator_eq_top, commutator_lt_top_of_nontrivial, h.commutator_lt_top_of_nontrivial
-/
lemma not_isSolvable [Nontrivial G] [IsPerfect G] : ¬ IsSolvable G := by
  intro h
  exact (h.commutator_lt_top_of_nontrivial G).ne commutator_eq_top

variable (G) in
/--
lemma `not_isNilpotent` / 引理 `not_isNilpotent`

English:
lemma not_isNilpotent
  given: [Nontrivial G] [IsPerfect G]
  statement: ¬ IsNilpotent G
  proof: fun _ => (not_isSolvable G) IsNilpotent.to_isSolvable

中文:
引理 not_isNilpotent
  条件: [非平凡 G] [是完美 G]
  结论: ¬ 是幂零 G
  证明: fun _ => (not_isSolvable G) IsNilpotent.to_isSolvable

Depends on / 依赖: IsNilpotent, IsNilpotent.to_isSolvable, not_isSolvable, to_isSolvable
-/
lemma not_isNilpotent [Nontrivial G] [IsPerfect G] : ¬ IsNilpotent G :=
  fun _ => (not_isSolvable G) IsNilpotent.to_isSolvable

open scoped IsMulCommutative in
variable (G) in
/--
lemma `not_isMulCommutative` / 引理 `not_isMulCommutative`

English:
lemma not_isMulCommutative
  given: [Nontrivial G] [IsPerfect G]
  statement: ¬ IsMulCommutative G
  proof: fun _ => (not_isSolvable G) inferInstance

中文:
引理 not_isMulCommutative
  条件: [非平凡 G] [是完美 G]
  结论: ¬ 是MulCommutative G
  证明: fun _ => (not_isSolvable G) inferInstance

Depends on / 依赖: not_isSolvable
-/
lemma not_isMulCommutative [Nontrivial G] [IsPerfect G] : ¬ IsMulCommutative G :=
  fun _ => (not_isSolvable G) inferInstance

/--
Instance `subsingleton_of_isMulCommutative` / 实例 `subsingleton_of_isMulCommutative`

English:
instance subsingleton_of_isMulCommutative
  body: by
  by_contra! h_not_subsingleton
  exact not_isMulCommutative G h_comm

中文:
实例 subsingleton_of_isMulCommutative
  定义体: by
  by_contra! h_not_subsingleton
  exact not_isMulCommutative G h_comm

Depends on / 依赖: h_comm, h_not_subsingleton, not_isMulCommutative
-/
instance subsingleton_of_isMulCommutative
    [hG : IsPerfect G] [h_comm : IsMulCommutative G] : Subsingleton G := by
  by_contra! h_not_subsingleton
  exact not_isMulCommutative G h_comm

/--
lemma `map` / 引理 `map`

English:
lemma map
  given: [IsPerfect H]
  statement: IsPerfect (H.map f)
  proof: by
  rw [isPerfect_iff]; rw [← map_commutator]; rw [commutator_eq_self]

中文:
引理 map
  条件: [是完美 H]
  结论: 是完美 (H.map f)
  证明: by
  rw [isPerfect_iff]; rw [← map_commutator]; rw [commutator_eq_self]
-/
protected lemma map [IsPerfect H] : IsPerfect (H.map f) := by
  rw [isPerfect_iff]; rw [← map_commutator]; rw [commutator_eq_self]

/--
lemma `range` / 引理 `range`

English:
lemma range
  given: [IsPerfect G]
  statement: IsPerfect f.range
  proof: by
  rw [MonoidHom.range_eq_map]
  exact IsPerfect.map _

中文:
引理 range
  条件: [是完美 G]
  结论: 是完美 f.range
  证明: by
  rw [MonoidHom.range_eq_map]
  exact IsPerfect.map _
-/
protected lemma range [IsPerfect G] : IsPerfect f.range := by
  rw [MonoidHom.range_eq_map]
  exact IsPerfect.map _

variable {f} in
/--
lemma `ofSurjective` / 引理 `ofSurjective`

English:
lemma ofSurjective
  given: [IsPerfect G] (hf : Function.Surjective f)
  statement: IsPerfect G'
  proof: by
  rw [← top_iff]; rw [← MonoidHom.range_eq_top_of_surjective f hf]
  exact IsPerfect.range f

中文:
引理 ofSurjective
  条件: [是完美 G] (hf : 函数.满射 f)
  结论: 是完美 G'
  证明: by
  rw [← top_iff]; rw [← MonoidHom.range_eq_top_of_surjective f hf]
  exact IsPerfect.range f

Depends on / 依赖: IsPerfect, IsPerfect.range, MonoidHom, MonoidHom.range_eq_top_of_surjective, range_eq_top_of_surjective, top_iff
-/
lemma ofSurjective [IsPerfect G] (hf : Function.Surjective f) : IsPerfect G' := by
  rw [← top_iff]; rw [← MonoidHom.range_eq_top_of_surjective f hf]
  exact IsPerfect.range f

/--
Instance `instQuotientSubgroup` / 实例 `instQuotientSubgroup`

English:
instance instQuotientSubgroup
  signature: [H.Normal] [IsPerfect G]
  body: ofSurjective (QuotientGroup.mk'_surjective H)

中文:
实例 instQuotientSubgroup
  签名: [H.正规] [是完美 G]
  定义体: ofSurjective (QuotientGroup.mk'_surjective H)

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, _surjective, ofSurjective
-/
instance instQuotientSubgroup [H.Normal] [IsPerfect G] : IsPerfect (G ⧸ H) :=
  ofSurjective (QuotientGroup.mk'_surjective H)

variable (G) in
@[simp]
/--
theorem `derivedSeries_eq_top` / 定理 `derivedSeries_eq_top`

English:
theorem derivedSeries_eq_top
  given: [IsPerfect G] (n : Nat)
  statement: derivedSeries G n = ⊤
  proof: by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [derivedSeries_succ]; rw [derivedSeries_eq_top]; rw [commutator_eq_self]

@[simp]

中文:
定理 derivedSeries_eq_top
  条件: [是完美 G] (n : 自然数)
  结论: derivedSeries G n = ⊤
  证明: by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [derivedSeries_succ]; rw [derivedSeries_eq_top]; rw [commutator_eq_self]

@[simp]

Depends on / 依赖: commutator_eq_self, derivedSeries_eq_top, derivedSeries_succ
-/
theorem derivedSeries_eq_top [IsPerfect G] (n : Nat) : derivedSeries G n = ⊤ := by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [derivedSeries_succ]; rw [derivedSeries_eq_top]; rw [commutator_eq_self]

@[simp]
/--
theorem `lowerCentralSeries_eq_top` / 定理 `lowerCentralSeries_eq_top`

English:
theorem lowerCentralSeries_eq_top
  given: (H : Subgroup G) [IsPerfect H] (n : Nat)
  proof: by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [Subgroup.lowerCentralSeries_succ]; rw [lowerCentralSeries_eq_top]; rw [commutator_eq_self]

中文:
定理 lowerCentralSeries_eq_top
  条件: (H : 子群 G) [是完美 H] (n : 自然数)
  证明: by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [Subgroup.lowerCentralSeries_succ]; rw [lowerCentralSeries_eq_top]; rw [commutator_eq_self]

Depends on / 依赖: Subgroup, Subgroup.lowerCentralSeries_succ, commutator_eq_self, lowerCentralSeries_eq_top, lowerCentralSeries_succ
-/
theorem lowerCentralSeries_eq_top (H : Subgroup G) [IsPerfect H] (n : Nat) :
    H.lowerCentralSeries n = H := by
  match n with
  | 0 => simp
  | n + 1 =>
    rw [Subgroup.lowerCentralSeries_succ]; rw [lowerCentralSeries_eq_top]; rw [commutator_eq_self]

variable (G) in
@[simp]
/--
theorem `upperCentralSeries_eq_center` / 定理 `upperCentralSeries_eq_center`

English:
theorem upperCentralSeries_eq_center
  given: [IsPerfect G] {n : Nat} (hn : n != 0)
  proof: by
  rw [← Subgroup.upperCentralSeries_one]; rw [eq_comm]
apply Subgroup.upperCentralSeries.eq_ge_of_eq_succ by lia
apply le_antisymm Subgroup.upperCentralSeries_mono G one_le_two
  rw [Subgroup.upperCentralSeries_one]; rw [← commutator_top_right_eq_bot_iff_le_center]; rw [← commutator_eq_top]; rw [commutator_comm]; rw [commutator_def]
  suffices ⁅⁅Subgroup.upperCentralSeries G 2, ⊤⁆, ⊤⁆ = ⊥ from
    commutator_commutator_eq_bot_of_rotate (by simpa [commutator_comm]) this
  rw [commutator_top_right_eq_bot_iff_le_center]; rw [← Subgroup.upperCentralSeries_one]
  apply commutator_upperCentralSeries_top_le

中文:
定理 upperCentralSeries_eq_center
  条件: [是完美 G] {n : 自然数} (hn : n != 0)
  证明: by
  rw [← Subgroup.upperCentralSeries_one]; rw [eq_comm]
apply Subgroup.upperCentralSeries.eq_ge_of_eq_succ by lia
apply le_antisymm Subgroup.upperCentralSeries_mono G one_le_two
  rw [Subgroup.upperCentralSeries_one]; rw [← commutator_top_right_eq_bot_iff_le_center]; rw [← commutator_eq_top]; rw [commutator_comm]; rw [commutator_def]
  suffices ⁅⁅Subgroup.upperCentralSeries G 2, ⊤⁆, ⊤⁆ = ⊥ from
    commutator_commutator_eq_bot_of_rotate (by simpa [commutator_comm]) this
  rw [commutator_top_right_eq_bot_iff_le_center]; rw [← Subgroup.upperCentralSeries_one]
  apply commutator_upperCentralSeries_top_le

Depends on / 依赖: Subgroup, Subgroup.upperCentralSeries, Subgroup.upperCentralSeries.eq_ge_of_eq_succ, Subgroup.upperCentralSeries_mono, Subgroup.upperCentralSeries_one, commutator_comm, commutator_commutator_eq_bot_of_rotate, commutator_def, commutator_eq_top, commutator_top_right_eq_bot_i, commutator_top_right_eq_bot_iff_le_center, eq_comm, eq_ge_of_eq_succ, le_antisymm, one_le_two, upperCentralSeries, upperCentralSeries_mono, upperCentralSeries_one
-/
theorem upperCentralSeries_eq_center [IsPerfect G] {n : Nat} (hn : n != 0) :
    Subgroup.upperCentralSeries G n = center G := by
  rw [← Subgroup.upperCentralSeries_one]; rw [eq_comm]
apply Subgroup.upperCentralSeries.eq_ge_of_eq_succ by lia
apply le_antisymm Subgroup.upperCentralSeries_mono G one_le_two
  rw [Subgroup.upperCentralSeries_one]; rw [← commutator_top_right_eq_bot_iff_le_center]; rw [← commutator_eq_top]; rw [commutator_comm]; rw [commutator_def]
  suffices ⁅⁅Subgroup.upperCentralSeries G 2, ⊤⁆, ⊤⁆ = ⊥ from
    commutator_commutator_eq_bot_of_rotate (by simpa [commutator_comm]) this
  rw [commutator_top_right_eq_bot_iff_le_center]; rw [← Subgroup.upperCentralSeries_one]
  apply commutator_upperCentralSeries_top_le

variable (G) in
/--
theorem `center_quotient_center_eq_bot` / 定理 `center_quotient_center_eq_bot`

English:
theorem center_quotient_center_eq_bot
  given: [IsPerfect G]
  statement: center (G ⧸ center G) = ⊥
  proof: by
  rw [← Subgroup.upperCentralSeries_one (G ⧸ center G)]; rw [← comap_eq_ker_of_surjective QuotientGroup.mk'_surjective _]; rw [QuotientGroup.ker_mk']; rw [Subgroup.comap_upperCentralSeries_quotient_center]; rw [upperCentralSeries_eq_center G by lia]

中文:
定理 center_quotient_center_eq_bot
  条件: [是完美 G]
  结论: center (G ⧸ center G) = ⊥
  证明: by
  rw [← Subgroup.upperCentralSeries_one (G ⧸ center G)]; rw [← comap_eq_ker_of_surjective QuotientGroup.mk'_surjective _]; rw [QuotientGroup.ker_mk']; rw [Subgroup.comap_upperCentralSeries_quotient_center]; rw [upperCentralSeries_eq_center G by lia]

Depends on / 依赖: QuotientGroup, QuotientGroup.ker_mk, QuotientGroup.mk, Subgroup, Subgroup.comap_upperCentralSeries_quotient_center, Subgroup.upperCentralSeries_one, _surjective, center, comap_eq_ker_of_surjective, comap_upperCentralSeries_quotient_center, ker_mk, upperCentralSeries_eq_center, upperCentralSeries_one
-/
theorem center_quotient_center_eq_bot [IsPerfect G] : center (G ⧸ center G) = ⊥ := by
  rw [← Subgroup.upperCentralSeries_one (G ⧸ center G)]; rw [← comap_eq_ker_of_surjective QuotientGroup.mk'_surjective _]; rw [QuotientGroup.ker_mk']; rw [Subgroup.comap_upperCentralSeries_quotient_center]; rw [upperCentralSeries_eq_center G by lia]

end Group.IsPerfect
