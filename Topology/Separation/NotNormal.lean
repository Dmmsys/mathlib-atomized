/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Tian Chen
-/
module

public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.Topology.Separation.Regular

/-!
# Not normal topological spaces

In this file we prove (see `IsClosed.not_normal_of_continuum_le_mk`) that a separable space with a
discrete subspace of cardinality continuum is not a normal topological space.

## References

* [Willard's *General Topology*][zbMATH02107988]
-/

public section

open Set Function Cardinal TopologicalSpace

universe u
variable {X : Type u} [TopologicalSpace X]

namespace IsClosed

/--
theorem `two_pow_mk_le_two_pow_mk_dense` / 定理 `two_pow_mk_le_two_pow_mk_dense`

English:
theorem two_pow_mk_le_two_pow_mk_dense
  statement: [NormalSpace X] {s d : Set X} (hs : IsClosed s)
  proof: by
  have h_closed (t) (ht : t in 𝒫 s) : IsClosed t := by
    rw [← inter_eq_self_of_subset_right ht]; rw [← Subtype.image_preimage_val]
    exact hs.isClosedMap_subtype_val _ (isClosed_discrete _)
  choose U V hU hV hUs hVs hUV using fun t : 𝒫 s =>
    normal_separation (h_closed t t.2) (h_closed _ sdiff_subset) disjoint_sdiff_right
  have hUd {t₁ t₂} (h : U t₁ inter d = U t₂ inter d) : t₁.1 subseteq t₂.1 := by
    by_contra ht
    rw [← sdiff_nonempty] at ht
have hUVd := hd.inter_open_nonempty _ ((hU t₁).inter (hV t₂)) ht.mono
      subset_inter (sdiff_subset.trans (hUs t₁)) ((sdiff_subset_sdiff_left t₁.2).trans (hVs t₂))
    rw [inter_right_comm]; rw [h] at hUVd
exact hUVd.not_disjoint disjoint_of_subset_left inter_subset_left (hUV t₂)
have h_inj : Injective (U · inter d) := fun _ _ h => SetCoe.ext (hUd h).antisymm (hUd h.symm)
  rw [← mk_powerset]; rw [← mk_powerset]; rw [← mk_range_eq _ h_inj]
  apply mk_le_mk_of_subset
  rw [range_subset_iff]
  intro
  exact inter_subset_right

中文:
定理 two_pow_mk_le_two_pow_mk_dense
  结论: [正规空间 X] {s d : 集合 X} (hs : 是闭集 s)
  证明: by
  have h_closed (t) (ht : t in 𝒫 s) : IsClosed t := by
    rw [← inter_eq_self_of_subset_right ht]; rw [← Subtype.image_preimage_val]
    exact hs.isClosedMap_subtype_val _ (isClosed_discrete _)
  choose U V hU hV hUs hVs hUV using fun t : 𝒫 s =>
    normal_separation (h_closed t t.2) (h_closed _ sdiff_subset) disjoint_sdiff_right
  have hUd {t₁ t₂} (h : U t₁ inter d = U t₂ inter d) : t₁.1 subseteq t₂.1 := by
    by_contra ht
    rw [← sdiff_nonempty] at ht
have hUVd := hd.inter_open_nonempty _ ((hU t₁).inter (hV t₂)) ht.mono
      subset_inter (sdiff_subset.trans (hUs t₁)) ((sdiff_subset_sdiff_left t₁.2).trans (hVs t₂))
    rw [inter_right_comm]; rw [h] at hUVd
exact hUVd.not_disjoint disjoint_of_subset_left inter_subset_left (hUV t₂)
have h_inj : Injective (U · inter d) := fun _ _ h => SetCoe.ext (hUd h).antisymm (hUd h.symm)
  rw [← mk_powerset]; rw [← mk_powerset]; rw [← mk_range_eq _ h_inj]
  apply mk_le_mk_of_subset
  rw [range_subset_iff]
  intro
  exact inter_subset_right

Depends on / 依赖: IsClosed, Subtype, Subtype.image_preimage_val, disjoint_sdiff_right, h_closed, hd.inter_open_nonempty, hs.isClosedMap_subtype_val, image_preimage_val, inter_eq_self_of_subset_right, inter_open_nonempty, isClosedMap_subtype_val, isClosed_discrete, normal_separation, sdiff_nonempty, sdiff_subset, subseteq
-/
theorem two_pow_mk_le_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hd : Dense d) : (2 : Cardinal) ^ #s <= 2 ^ #d := by
  have h_closed (t) (ht : t in 𝒫 s) : IsClosed t := by
    rw [← inter_eq_self_of_subset_right ht]; rw [← Subtype.image_preimage_val]
    exact hs.isClosedMap_subtype_val _ (isClosed_discrete _)
  choose U V hU hV hUs hVs hUV using fun t : 𝒫 s =>
    normal_separation (h_closed t t.2) (h_closed _ sdiff_subset) disjoint_sdiff_right
  have hUd {t₁ t₂} (h : U t₁ inter d = U t₂ inter d) : t₁.1 subseteq t₂.1 := by
    by_contra ht
    rw [← sdiff_nonempty] at ht
have hUVd := hd.inter_open_nonempty _ ((hU t₁).inter (hV t₂)) ht.mono
      subset_inter (sdiff_subset.trans (hUs t₁)) ((sdiff_subset_sdiff_left t₁.2).trans (hVs t₂))
    rw [inter_right_comm]; rw [h] at hUVd
exact hUVd.not_disjoint disjoint_of_subset_left inter_subset_left (hUV t₂)
have h_inj : Injective (U · inter d) := fun _ _ h => SetCoe.ext (hUd h).antisymm (hUd h.symm)
  rw [← mk_powerset]; rw [← mk_powerset]; rw [← mk_range_eq _ h_inj]
  apply mk_le_mk_of_subset
  rw [range_subset_iff]
  intro
  exact inter_subset_right

/--
theorem `mk_lt_two_pow_mk_dense` / 定理 `mk_lt_two_pow_mk_dense`

English:
theorem mk_lt_two_pow_mk_dense
  statement: [NormalSpace X] {s d : Set X} (hs : IsClosed s)
  proof: (#s).cantor.trans_le hs.two_pow_mk_le_two_pow_mk_dense hd

中文:
定理 mk_lt_two_pow_mk_dense
  结论: [正规空间 X] {s d : 集合 X} (hs : 是闭集 s)
  证明: (#s).cantor.trans_le hs.two_pow_mk_le_two_pow_mk_dense hd

Depends on / 依赖: cantor, cantor.trans_le, hs.two_pow_mk_le_two_pow_mk_dense, trans_le, two_pow_mk_le_two_pow_mk_dense
-/
theorem mk_lt_two_pow_mk_dense [NormalSpace X] {s d : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hd : Dense d) : #s < 2 ^ #d :=
(#s).cantor.trans_le hs.two_pow_mk_le_two_pow_mk_dense hd

variable [SeparableSpace X]

/--
theorem `two_pow_mk_lt_continuum` / 定理 `two_pow_mk_lt_continuum`

English:
theorem two_pow_mk_lt_continuum
  statement: [NormalSpace X] {s : Set X} (hs : IsClosed s)
  proof: have ⟨d, hd_countable, hd_dense⟩ := exists_countable_dense X
  calc
    2 ^ #s <= 2 ^ #d := hs.two_pow_mk_le_two_pow_mk_dense hd_dense
    _ <= 2 ^ ℵ₀ := power_le_power_left two_ne_zero hd_countable.le_aleph0
    _ = 𝔠 := two_power_aleph0

中文:
定理 two_pow_mk_lt_continuum
  结论: [正规空间 X] {s : 集合 X} (hs : 是闭集 s)
  证明: have ⟨d, hd_countable, hd_dense⟩ := exists_countable_dense X
  calc
    2 ^ #s <= 2 ^ #d := hs.two_pow_mk_le_two_pow_mk_dense hd_dense
    _ <= 2 ^ ℵ₀ := power_le_power_left two_ne_zero hd_countable.le_aleph0
    _ = 𝔠 := two_power_aleph0

Depends on / 依赖: exists_countable_dense, hd_countable, hd_countable.le_aleph0, hd_dense, hs.two_pow_mk_le_two_pow_mk_dense, le_aleph0, power_le_power_left, two_ne_zero, two_pow_mk_le_two_pow_mk_dense, two_power_aleph0
-/
theorem two_pow_mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s)
    [DiscreteTopology s] : 2 ^ #s <= 𝔠 :=
  have ⟨d, hd_countable, hd_dense⟩ := exists_countable_dense X
  calc
    2 ^ #s <= 2 ^ #d := hs.two_pow_mk_le_two_pow_mk_dense hd_dense
    _ <= 2 ^ ℵ₀ := power_le_power_left two_ne_zero hd_countable.le_aleph0
    _ = 𝔠 := two_power_aleph0

/--
theorem `mk_lt_continuum` / 定理 `mk_lt_continuum`

English:
theorem mk_lt_continuum
  statement: [NormalSpace X] {s : Set X} (hs : IsClosed s)
  proof: (#s).cantor.trans_le hs.two_pow_mk_lt_continuum

中文:
定理 mk_lt_continuum
  结论: [正规空间 X] {s : 集合 X} (hs : 是闭集 s)
  证明: (#s).cantor.trans_le hs.two_pow_mk_lt_continuum

Depends on / 依赖: cantor, cantor.trans_le, hs.two_pow_mk_lt_continuum, trans_le, two_pow_mk_lt_continuum
-/
theorem mk_lt_continuum [NormalSpace X] {s : Set X} (hs : IsClosed s)
  [DiscreteTopology s] : #s < 𝔠 := (#s).cantor.trans_le hs.two_pow_mk_lt_continuum

/--
theorem `not_normal_of_continuum_le_mk` / 定理 `not_normal_of_continuum_le_mk`

English:
theorem not_normal_of_continuum_le_mk
  statement: {s : Set X} (hs : IsClosed s) [DiscreteTopology s]
  proof: fun _ => hs.mk_lt_continuum.not_ge hmk

中文:
定理 not_normal_of_continuum_le_mk
  结论: {s : 集合 X} (hs : 是闭集 s) [离散拓扑 s]
  证明: fun _ => hs.mk_lt_continuum.not_ge hmk

Depends on / 依赖: hs.mk_lt_continuum.not_ge, mk_lt_continuum, not_ge
-/
theorem not_normal_of_continuum_le_mk {s : Set X} (hs : IsClosed s) [DiscreteTopology s]
    (hmk : 𝔠 <= #s) : ¬NormalSpace X := fun _ => hs.mk_lt_continuum.not_ge hmk

end IsClosed
