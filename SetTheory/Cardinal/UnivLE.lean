/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.SetTheory.Ordinal.Univ

/-!
# UnivLE and cardinals
-/

public section

noncomputable section

universe u v

open Cardinal

/--
theorem `univLE_iff_cardinal_le` / 定理 `univLE_iff_cardinal_le`

English:
theorem univLE_iff_cardinal_le
  statement: UnivLE.{u, v} ↔ univ.{u, v + 1} <= univ.{v, u + 1}
  proof: by
  simp_rw [univLE_iff, small_iff_lift_mk_lt_univ]
  contrapose!
  -- strange: simp_rw [univ_umax.{v,u}] doesn't work
  refine ⟨fun ⟨α, le⟩ => ?_, fun h => ?_⟩
  · rw [univ_umax.{v, u}, ← lift_le.{u + 1}, lift_univ, lift_lift] at le
    exact le.trans_lt (lift_lt_univ'.{u, v + 1} #α)
  · obtain ⟨⟨

中文:
定理 univLE_iff_cardinal_le
  结论: UnivLE.{u, v} ↔ univ.{u, v + 1} <= univ.{v, u + 1}
  证明: by
  simp_rw [univLE_iff, small_iff_lift_mk_lt_univ]
  contrapose!
  -- strange: simp_rw [univ_umax.{v,u}] doesn't work
  refine ⟨fun ⟨α, le⟩ => ?_, fun h => ?_⟩
  · rw [univ_umax.{v, u}, ← lift_le.{u + 1}, lift_univ, lift_lift] at le
    exact le.trans_lt (lift_lt_univ'.{u, v + 1} #α)
  · obtain ⟨⟨

Depends on / 依赖: contrapose, simp_rw, small_iff_lift_mk_lt_univ, univLE_iff
-/
theorem univLE_iff_cardinal_le : UnivLE.{u, v} ↔ univ.{u, v + 1} <= univ.{v, u + 1} := by
  simp_rw [univLE_iff, small_iff_lift_mk_lt_univ]
  contrapose!
  -- strange: simp_rw [univ_umax.{v,u}] doesn't work
  refine ⟨fun ⟨α, le⟩ => ?_, fun h => ?_⟩
  · rw [univ_umax.{v, u}, ← lift_le.{u + 1}, lift_univ, lift_lift] at le
    exact le.trans_lt (lift_lt_univ'.{u, v + 1} #α)
  · obtain ⟨⟨α⟩, h⟩ := lt_univ'.mp h; use α
    rw [univ_umax.{v]; rw [u}]; rw [← lift_le.{u + 1}]; rw [lift_univ]; rw [lift_lift]
    exact h.le

/--
theorem `univLE_iff_exists_embedding` / 定理 `univLE_iff_exists_embedding`

English:
theorem univLE_iff_exists_embedding
  statement: UnivLE.{u, v} ↔ Nonempty (Ordinal.{u} ↪ Ordinal.{v})
  proof: by
  rw [univLE_iff_cardinal_le]
  exact lift_mk_le'

中文:
定理 univLE_iff_存在_embedding
  结论: UnivLE.{u, v} ↔ 非空 (序数.{u} ↪ 序数.{v})
  证明: by
  rw [univLE_iff_cardinal_le]
  exact lift_mk_le'

Depends on / 依赖: lift_mk_le, univLE_iff_cardinal_le
-/
theorem univLE_iff_exists_embedding : UnivLE.{u, v} ↔ Nonempty (Ordinal.{u} ↪ Ordinal.{v}) := by
  rw [univLE_iff_cardinal_le]
  exact lift_mk_le'

/--
theorem `Ordinal.univLE_of_injective` / 定理 `Ordinal.univLE_of_injective`

English:
theorem Ordinal.univLE_of_injective
  given: {f : Ordinal.{u} -> Ordinal.{v}} (h : f.Injective)
  proof: univLE_iff_exists_embedding.2 ⟨f, h⟩

中文:
定理 序数.univLE_of_injective
  条件: {f : 序数.{u} -> 序数.{v}} (h : f.单射)
  证明: univLE_iff_exists_embedding.2 ⟨f, h⟩

Depends on / 依赖: univLE_iff_exists_embedding
-/
theorem Ordinal.univLE_of_injective {f : Ordinal.{u} -> Ordinal.{v}} (h : f.Injective) :
    UnivLE.{u, v} :=
  univLE_iff_exists_embedding.2 ⟨f, h⟩

/--
theorem `univLE_total` / 定理 `univLE_total`

English:
theorem univLE_total
  statement: UnivLE.{u, v} ∨ UnivLE.{v, u}
  proof: by
  simp_rw [univLE_iff_cardinal_le]; apply le_total

中文:
定理 univLE_total
  结论: UnivLE.{u, v} ∨ UnivLE.{v, u}
  证明: by
  simp_rw [univLE_iff_cardinal_le]; apply le_total

Depends on / 依赖: le_total, simp_rw, univLE_iff_cardinal_le
-/
theorem univLE_total : UnivLE.{u, v} ∨ UnivLE.{v, u} := by
  simp_rw [univLE_iff_cardinal_le]; apply le_total
