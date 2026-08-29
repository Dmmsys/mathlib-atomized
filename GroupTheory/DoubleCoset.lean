/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be written as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `setoid`: The double coset relation defined by two subgroups `H K` of `G`.
* `DoubleCoset.quotient`: The quotient of `G` by the double coset relation, i.e, `H \ G / K`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G : Type*} [Group G] {α : Type*} [Mul α]

open MulOpposite
open scoped Pointwise

namespace DoubleCoset

/--
Definition of `doubleCoset` / `doubleCoset` 的定义

English:
definition doubleCoset
  signature: (a : α) (s t : Set α)
  body: s * {a} * t

中文:
定义 doubleCoset
  签名: (a : α) (s t : 集合 α)
  定义体: s * {a} * t
-/
def doubleCoset (a : α) (s t : Set α) : Set α :=
  s * {a} * t

/--
lemma `doubleCoset_eq_image2` / 引理 `doubleCoset_eq_image2`

English:
lemma doubleCoset_eq_image2
  given: (a : α) (s t : Set α)
  proof: by
  simp_rw [doubleCoset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]

中文:
引理 doubleCoset_eq_image2
  条件: (a : α) (s t : 集合 α)
  证明: by
  simp_rw [doubleCoset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]

Depends on / 依赖: Set.image2_image_left, Set.image2_mul, Set.mul_singleton, doubleCoset, image2_image_left, image2_mul, mul_singleton, simp_rw
-/
lemma doubleCoset_eq_image2 (a : α) (s t : Set α) :
    doubleCoset a s t = Set.image2 (· * a * ·) s t := by
  simp_rw [doubleCoset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]

/--
lemma `mem_doubleCoset` / 引理 `mem_doubleCoset`

English:
lemma mem_doubleCoset
  given: {s t : Set α} {a b : α}
  proof: by
  simp only [doubleCoset_eq_image2, Set.mem_image2, eq_comm]

中文:
引理 mem_doubleCoset
  条件: {s t : 集合 α} {a b : α}
  证明: by
  simp only [doubleCoset_eq_image2, Set.mem_image2, eq_comm]

Depends on / 依赖: Set.mem_image2, doubleCoset_eq_image2, eq_comm, mem_image2
-/
lemma mem_doubleCoset {s t : Set α} {a b : α} :
    b in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y := by
  simp only [doubleCoset_eq_image2, Set.mem_image2, eq_comm]

/--
lemma `mem_doubleCoset_self` / 引理 `mem_doubleCoset_self`

English:
lemma mem_doubleCoset_self
  given: (H K : Subgroup G) (a : G)
  statement: a in doubleCoset a H K
  proof: mem_doubleCoset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

中文:
引理 mem_doubleCoset_self
  条件: (H K : 子群 G) (a : G)
  结论: a in doubleCoset a H K
  证明: mem_doubleCoset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

Depends on / 依赖: H.one_mem, K.one_mem, mem_doubleCoset, mem_doubleCoset.mpr, mul_one, one_mem, one_mul, symm.trans
-/
lemma mem_doubleCoset_self (H K : Subgroup G) (a : G) : a in doubleCoset a H K :=
  mem_doubleCoset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩

/--
lemma `doubleCoset_eq_of_mem` / 引理 `doubleCoset_eq_of_mem`

English:
lemma doubleCoset_eq_of_mem
  given: {H K : Subgroup G} {a b : G} (hb : b in doubleCoset a H K)
  proof: by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doubleCoset.1 hb
  rw [doubleCoset]; rw [doubleCoset]; rw [← Set.singleton_mul_singleton]; rw [← Set.singleton_mul_singleton]; rw [mul_assoc]; rw [mul_assoc]; rw [Subgroup.singleton_mul_subgroup hk]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Subgroup.subgroup_mul

中文:
引理 doubleCoset_eq_of_mem
  条件: {H K : 子群 G} {a b : G} (hb : b in doubleCoset a H K)
  证明: by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doubleCoset.1 hb
  rw [doubleCoset]; rw [doubleCoset]; rw [← Set.singleton_mul_singleton]; rw [← Set.singleton_mul_singleton]; rw [mul_assoc]; rw [mul_assoc]; rw [Subgroup.singleton_mul_subgroup hk]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Subgroup.subgroup_mul

Depends on / 依赖: Set.singleton_mul_singleton, Subgroup, Subgroup.singleton_mul_subgroup, Subgroup.subgroup_mul_singleton, doubleCoset, mem_doubleCoset, mul_assoc, singleton_mul_singleton, singleton_mul_subgroup, subgroup_mul_singleton
-/
lemma doubleCoset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b in doubleCoset a H K) :
    doubleCoset b H K = doubleCoset a H K := by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doubleCoset.1 hb
  rw [doubleCoset]; rw [doubleCoset]; rw [← Set.singleton_mul_singleton]; rw [← Set.singleton_mul_singleton]; rw [mul_assoc]; rw [mul_assoc]; rw [Subgroup.singleton_mul_subgroup hk]; rw [← mul_assoc]; rw [← mul_assoc]; rw [Subgroup.subgroup_mul_singleton hh]

/--
lemma `mem_doubleCoset_of_not_disjoint` / 引理 `mem_doubleCoset_of_not_disjoint`

English:
lemma mem_doubleCoset_of_not_disjoint
  statement: {H K : Subgroup G} {a b : G}
  proof: by
  rw [Set.not_disjoint_iff] at h
  simp only [mem_doubleCoset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), ?_⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_asso

中文:
引理 mem_doubleCoset_of_not_disjoint
  结论: {H K : 子群 G} {a b : G}
  证明: by
  rw [Set.not_disjoint_iff] at h
  simp only [mem_doubleCoset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), ?_⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_asso

Depends on / 依赖: H.inv_mem, H.mul_mem, K.inv_mem, K.mul_mem, Set.not_disjoint_iff, eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq, inv_mem, mem_doubleCoset, mul_assoc, mul_mem, not_disjoint_iff
-/
lemma mem_doubleCoset_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) : b in doubleCoset a H K := by
  rw [Set.not_disjoint_iff] at h
  simp only [mem_doubleCoset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), ?_⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, eq_mul_inv_iff_mul_eq]

/--
lemma `eq_of_not_disjoint` / 引理 `eq_of_not_disjoint`

English:
lemma eq_of_not_disjoint
  statement: {H K : Subgroup G} {a b : G}
  proof: by
  rw [disjoint_comm] at h
  have ha : a in doubleCoset b H K := mem_doubleCoset_of_not_disjoint h
  apply doubleCoset_eq_of_mem ha

中文:
引理 eq_of_not_disjoint
  结论: {H K : 子群 G} {a b : G}
  证明: by
  rw [disjoint_comm] at h
  have ha : a in doubleCoset b H K := mem_doubleCoset_of_not_disjoint h
  apply doubleCoset_eq_of_mem ha

Depends on / 依赖: disjoint_comm, doubleCoset, doubleCoset_eq_of_mem, mem_doubleCoset_of_not_disjoint
-/
lemma eq_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) :
    doubleCoset a H K = doubleCoset b H K := by
  rw [disjoint_comm] at h
  have ha : a in doubleCoset b H K := mem_doubleCoset_of_not_disjoint h
  apply doubleCoset_eq_of_mem ha

/-- The setoid defined by the `doubleCoset` relation -/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: (H K : Set G)
  body: Setoid.ker fun x => doubleCoset x H K

中文:
定义 setoid
  签名: (H K : 集合 G)
  定义体: Setoid.ker fun x => doubleCoset x H K

Depends on / 依赖: Setoid, Setoid.ker, doubleCoset
-/
def setoid (H K : Set G) : Setoid G :=
  Setoid.ker fun x => doubleCoset x H K

/--
Definition of `Quotient` / `Quotient` 的定义

English:
definition Quotient
  signature: (H K : Set G)
  body: _root_.Quotient (setoid H K)

中文:
定义 商
  签名: (H K : 集合 G)
  定义体: _root_.Quotient (setoid H K)

Depends on / 依赖: Quotient, _root_, _root_.Quotient, setoid
-/
def Quotient (H K : Set G) : Type _ :=
  _root_.Quotient (setoid H K)

/--
lemma `rel_iff` / 引理 `rel_iff`

English:
lemma rel_iff
  given: {H K : Subgroup G} {x y : G}
  proof: Iff.trans
    ⟨fun (hxy : doubleCoset x H K = doubleCoset y H K) => hxy ▸ mem_doubleCoset_self H K y,
      fun hxy => (doubleCoset_eq_of_mem hxy).symm⟩ mem_doubleCoset

中文:
引理 rel_iff
  条件: {H K : 子群 G} {x y : G}
  证明: Iff.trans
    ⟨fun (hxy : doubleCoset x H K = doubleCoset y H K) => hxy ▸ mem_doubleCoset_self H K y,
      fun hxy => (doubleCoset_eq_of_mem hxy).symm⟩ mem_doubleCoset

Depends on / 依赖: Iff.trans, doubleCoset, doubleCoset_eq_of_mem, mem_doubleCoset, mem_doubleCoset_self
-/
lemma rel_iff {H K : Subgroup G} {x y : G} :
    setoid ↑H ↑K x y ↔ exists a in H, exists b in K, y = a * x * b :=
  Iff.trans
    ⟨fun (hxy : doubleCoset x H K = doubleCoset y H K) => hxy ▸ mem_doubleCoset_self H K y,
      fun hxy => (doubleCoset_eq_of_mem hxy).symm⟩ mem_doubleCoset

/--
lemma `bot_rel_eq_leftRel` / 引理 `bot_rel_eq_leftRel`

English:
lemma bot_rel_eq_leftRel
  given: (H : Subgroup G)
  proof: by
  ext a b
  rw [rel_iff]; rw [QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    rwa [one_mul, inv_mul_cancel_left]
  · rintro (h : a⁻¹ * b in H)
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩

中文:
引理 bot_rel_eq_leftRel
  条件: (H : 子群 G)
  证明: by
  ext a b
  rw [rel_iff]; rw [QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    rwa [one_mul, inv_mul_cancel_left]
  · rintro (h : a⁻¹ * b in H)
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩

Depends on / 依赖: QuotientGroup, QuotientGroup.leftRel_apply, inv_mul_cancel_left, leftRel_apply, mul_inv_cancel_left, one_mul, rel_iff
-/
lemma bot_rel_eq_leftRel (H : Subgroup G) :
    ⇑(setoid ↑(⊥ : Subgroup G) ↑H) = ⇑(QuotientGroup.leftRel H) := by
  ext a b
  rw [rel_iff]; rw [QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    rwa [one_mul, inv_mul_cancel_left]
  · rintro (h : a⁻¹ * b in H)
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩

/--
lemma `rel_bot_eq_right_group_rel` / 引理 `rel_bot_eq_right_group_rel`

English:
lemma rel_bot_eq_right_group_rel
  given: (H : Subgroup G)
  proof: by
  ext a b
  rw [rel_iff]; rw [QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    rwa [mul_one, mul_inv_cancel_right]
  · rintro (h : b * a⁻¹ in H)
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩

中文:
引理 rel_bot_eq_right_group_rel
  条件: (H : 子群 G)
  证明: by
  ext a b
  rw [rel_iff]; rw [QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    rwa [mul_one, mul_inv_cancel_right]
  · rintro (h : b * a⁻¹ in H)
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩

Depends on / 依赖: QuotientGroup, QuotientGroup.rightRel_apply, inv_mul_cancel_right, mul_inv_cancel_right, mul_one, rel_iff, rightRel_apply
-/
lemma rel_bot_eq_right_group_rel (H : Subgroup G) :
    ⇑(setoid ↑H ↑(⊥ : Subgroup G)) = ⇑(QuotientGroup.rightRel H) := by
  ext a b
  rw [rel_iff]; rw [QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    rwa [mul_one, mul_inv_cancel_right]
  · rintro (h : b * a⁻¹ in H)
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `quotToDoubleCoset` / `quotToDoubleCoset` 的定义

English:
definition quotToDoubleCoset
  signature: (H K : Subgroup G) (q : Quotient (H : Set G) K)
  body: doubleCoset q.out H K

中文:
定义 quotToDoubleCoset
  签名: (H K : 子群 G) (q : 商 (H : 集合 G) K)
  定义体: doubleCoset q.out H K

Depends on / 依赖: doubleCoset, q.out
-/
noncomputable def quotToDoubleCoset (H K : Subgroup G) (q : Quotient (H : Set G) K) : Set G :=
  doubleCoset q.out H K

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (H K : Subgroup G) (a : G)
  body: Quotient.mk'' a

中文:
缩写 mk
  签名: (H K : 子群 G) (a : G)
  定义体: Quotient.mk'' a

Depends on / 依赖: Quotient, Quotient.mk
-/
abbrev mk (H K : Subgroup G) (a : G) : Quotient (H : Set G) K :=
  Quotient.mk'' a

instance (H K : Subgroup G) : Inhabited (Quotient (H : Set G) K) :=
  ⟨mk H K (1 : G)⟩

/--
lemma `eq''` / 引理 `eq''`

English:
lemma eq''
  given: {a b : G} (H K : Subgroup G)
  statement: mk H K a = mk H K b ↔ setoid H K a b
  proof: Quotient.eq

中文:
引理 eq''
  条件: {a b : G} (H K : 子群 G)
  结论: mk H K a = mk H K b ↔ setoid H K a b
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
lemma eq'' {a b : G} (H K : Subgroup G) : mk H K a = mk H K b ↔ setoid H K a b :=
  Quotient.eq

/--
lemma `eq` / 引理 `eq`

English:
lemma eq
  given: (H K : Subgroup G) (a b : G)
  proof: by
  rw [eq'']
  exact rel_iff

中文:
引理 eq
  条件: (H K : 子群 G) (a b : G)
  证明: by
  rw [eq'']
  exact rel_iff

Depends on / 依赖: rel_iff
-/
lemma eq (H K : Subgroup G) (a b : G) :
    mk H K a = mk H K b ↔ exists h in H, exists k in K, b = h * a * k := by
  rw [eq'']
  exact rel_iff

/--
lemma `out_eq'` / 引理 `out_eq'`

English:
lemma out_eq'
  given: (H K : Subgroup G) (q : Quotient ↑H ↑K)
  statement: mk H K q.out = q
  proof: Quotient.out_eq' q

中文:
引理 out_eq'
  条件: (H K : 子群 G) (q : 商 ↑H ↑K)
  结论: mk H K q.out = q
  证明: Quotient.out_eq' q

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
lemma out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : mk H K q.out = q :=
  Quotient.out_eq' q

/--
lemma `mk_out_eq_mul` / 引理 `mk_out_eq_mul`

English:
lemma mk_out_eq_mul
  given: (H K : Subgroup G) (g : G)
  proof: by
  have := eq H K (mk H K g : Quotient ↑H ↑K).out g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq ?_)⟩
  rw [← mul_assoc]; rw [← T]

中文:
引理 mk_out_eq_mul
  条件: (H K : 子群 G) (g : G)
  证明: by
  have := eq H K (mk H K g : Quotient ↑H ↑K).out g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq ?_)⟩
  rw [← mul_assoc]; rw [← T]

Depends on / 依赖: H.inv_mem, K.inv_mem, Quotient, eq_inv_mul_of_mul_eq, eq_mul_inv_of_mul_eq, inv_mem, mul_assoc, out_eq
-/
lemma mk_out_eq_mul (H K : Subgroup G) (g : G) :
    exists h k : G, h in H ∧ k in K ∧ (mk H K g : Quotient ↑H ↑K).out = h * g * k := by
  have := eq H K (mk H K g : Quotient ↑H ↑K).out g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq ?_)⟩
  rw [← mul_assoc]; rw [← T]

/--
lemma `mk_eq_of_doubleCoset_eq` / 引理 `mk_eq_of_doubleCoset_eq`

English:
lemma mk_eq_of_doubleCoset_eq
  statement: {H K : Subgroup G} {a b : G}
  proof: by
  rw [eq]
  exact mem_doubleCoset.mp (h.symm ▸ mem_doubleCoset_self H K b)

中文:
引理 mk_eq_of_doubleCoset_eq
  结论: {H K : 子群 G} {a b : G}
  证明: by
  rw [eq]
  exact mem_doubleCoset.mp (h.symm ▸ mem_doubleCoset_self H K b)

Depends on / 依赖: h.symm, mem_doubleCoset, mem_doubleCoset.mp, mem_doubleCoset_self
-/
lemma mk_eq_of_doubleCoset_eq {H K : Subgroup G} {a b : G}
    (h : doubleCoset a H K = doubleCoset b H K) : mk H K a = mk H K b := by
  rw [eq]
  exact mem_doubleCoset.mp (h.symm ▸ mem_doubleCoset_self H K b)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_quotToDoubleCoset_iff` / 引理 `mem_quotToDoubleCoset_iff`

English:
lemma mem_quotToDoubleCoset_iff
  given: {H K : Subgroup G} (i : Quotient (H : Set G) K) (a : G)
  proof: by
  refine ⟨fun hg => by simp [mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hg)], fun hg => ?_⟩
  rw [← out_eq' _ _ i] at hg
  exact mem_doubleCoset.mpr ((eq _ _ _ a).mp hg.symm)

中文:
引理 mem_quotToDoubleCoset_iff
  条件: {H K : 子群 G} (i : 商 (H : 集合 G) K) (a : G)
  证明: by
  refine ⟨fun hg => by simp [mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hg)], fun hg => ?_⟩
  rw [← out_eq' _ _ i] at hg
  exact mem_doubleCoset.mpr ((eq _ _ _ a).mp hg.symm)

Depends on / 依赖: doubleCoset_eq_of_mem, hg.symm, mem_doubleCoset, mem_doubleCoset.mpr, mk_eq_of_doubleCoset_eq, out_eq
-/
lemma mem_quotToDoubleCoset_iff {H K : Subgroup G} (i : Quotient (H : Set G) K) (a : G) :
    a in quotToDoubleCoset H K i ↔ mk H K a = i := by
  refine ⟨fun hg => by simp [mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hg)], fun hg => ?_⟩
  rw [← out_eq' _ _ i] at hg
  exact mem_doubleCoset.mpr ((eq _ _ _ a).mp hg.symm)

/--
lemma `disjoint_out` / 引理 `disjoint_out`

English:
lemma disjoint_out
  given: {H K : Subgroup G} {a b : Quotient H K}
  proof: by
  contrapose
  intro h
  simpa [out_eq'] using mk_eq_of_doubleCoset_eq (eq_of_not_disjoint h)

中文:
引理 disjoint_out
  条件: {H K : 子群 G} {a b : 商 H K}
  证明: by
  contrapose
  intro h
  simpa [out_eq'] using mk_eq_of_doubleCoset_eq (eq_of_not_disjoint h)

Depends on / 依赖: contrapose, eq_of_not_disjoint, mk_eq_of_doubleCoset_eq, out_eq
-/
lemma disjoint_out {H K : Subgroup G} {a b : Quotient H K} :
    a != b -> Disjoint (doubleCoset a.out H K) (doubleCoset b.out (H : Set G) K) := by
  contrapose
  intro h
  simpa [out_eq'] using mk_eq_of_doubleCoset_eq (eq_of_not_disjoint h)

/--
lemma `iUnion_quotToDoubleCoset` / 引理 `iUnion_quotToDoubleCoset`

English:
lemma iUnion_quotToDoubleCoset
  given: (H K : Subgroup G)
  statement: ⋃ q, quotToDoubleCoset H K q = Set.univ
  proof: by
  ext x
  simp only [Set.mem_iUnion, quotToDoubleCoset, mem_doubleCoset, SetLike.mem_coe, Set.mem_univ,
    iff_true]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out_eq_mul H K x
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, ?_⟩
  simp only [h5, ← mul_assoc, one_mul, inv_mul_cancel, mul_in

中文:
引理 iUnion_quotToDoubleCoset
  条件: (H K : 子群 G)
  结论: ⋃ q, quotToDoubleCoset H K q = 集合.univ
  证明: by
  ext x
  simp only [Set.mem_iUnion, quotToDoubleCoset, mem_doubleCoset, SetLike.mem_coe, Set.mem_univ,
    iff_true]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out_eq_mul H K x
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, ?_⟩
  simp only [h5, ← mul_assoc, one_mul, inv_mul_cancel, mul_in

Depends on / 依赖: H.inv_mem, K.inv_mem, Set.mem_iUnion, Set.mem_univ, SetLike, SetLike.mem_coe, iff_true, inv_mem, inv_mul_cancel, mem_coe, mem_doubleCoset, mem_iUnion, mem_univ, mk_out_eq_mul, mul_assoc, mul_inv_cancel_right, one_mul, quotToDoubleCoset
-/
lemma iUnion_quotToDoubleCoset (H K : Subgroup G) : ⋃ q, quotToDoubleCoset H K q = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, quotToDoubleCoset, mem_doubleCoset, SetLike.mem_coe, Set.mem_univ,
    iff_true]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out_eq_mul H K x
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, ?_⟩
  simp only [h5, ← mul_assoc, one_mul, inv_mul_cancel, mul_inv_cancel_right]

@[deprecated (since := "2026-04-03")]
alias union_quotToDoubleCoset := iUnion_quotToDoubleCoset

/--
lemma `doubleCoset_union_rightCoset` / 引理 `doubleCoset_union_rightCoset`

English:
lemma doubleCoset_union_rightCoset
  given: (H K : Subgroup G) (a : G)
  proof: by
  ext x
  simp only [mem_rightCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    ref

中文:
引理 doubleCoset_union_rightCoset
  条件: (H K : 子群 G) (a : G)
  证明: by
  ext x
  simp only [mem_rightCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    ref

Depends on / 依赖: InvMemClass, InvMemClass.coe_inv, Set.mem_iUnion, SetLike, SetLike.mem_coe, coe_inv, inv_mul_cancel_right, mem_coe, mem_doubleCoset, mem_iUnion, mem_rightCoset_iff, mul_assoc, mul_inv_cancel_right, mul_inv_rev
-/
lemma doubleCoset_union_rightCoset (H K : Subgroup G) (a : G) :
    ⋃ k : K, op (a * k) • ↑H = doubleCoset a H K := by
  ext x
  simp only [mem_rightCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hx, mul_inv_cancel_right]

/--
lemma `doubleCoset_union_leftCoset` / 引理 `doubleCoset_union_leftCoset`

English:
lemma doubleCoset_union_leftCoset
  given: (H K : Subgroup G) (a : G)
  proof: by
  ext x
  simp only [mem_leftCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, ?_⟩
    simp only [← mul_assoc, one_mul, mul_inv_cancel, mul_inv_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    re

中文:
引理 doubleCoset_union_leftCoset
  条件: (H K : 子群 G) (a : G)
  证明: by
  ext x
  simp only [mem_leftCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, ?_⟩
    simp only [← mul_assoc, one_mul, mul_inv_cancel, mul_inv_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    re

Depends on / 依赖: InvMemClass, InvMemClass.coe_inv, Set.mem_iUnion, coe_inv, inv_mul_cancel, inv_mul_cancel_right, mem_doubleCoset, mem_iUnion, mem_leftCoset_iff, mul_assoc, mul_inv_cancel, mul_inv_cancel_right, mul_inv_rev, one_mul
-/
lemma doubleCoset_union_leftCoset (H K : Subgroup G) (a : G) :
    ⋃ h : H, (h * a : G) • ↑K = doubleCoset a H K := by
  ext x
  simp only [mem_leftCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, ?_⟩
    simp only [← mul_assoc, one_mul, mul_inv_cancel, mul_inv_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hy, one_mul, inv_mul_cancel, inv_mul_cancel_right]

open Quotient QuotientGroup

/--
lemma `left_bot_eq_left_quot` / 引理 `left_bot_eq_left_quot`

English:
lemma left_bot_eq_left_quot
  given: (H : Subgroup G)
  proof: by
  unfold Quotient
  congr
  ext
  simp_rw [← bot_rel_eq_leftRel H]

中文:
引理 left_bot_eq_left_quot
  条件: (H : 子群 G)
  证明: by
  unfold Quotient
  congr
  ext
  simp_rw [← bot_rel_eq_leftRel H]

Depends on / 依赖: Quotient, bot_rel_eq_leftRel, simp_rw
-/
lemma left_bot_eq_left_quot (H : Subgroup G) :
    Quotient (⊥ : Subgroup G) (H : Set G) = (G ⧸ H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← bot_rel_eq_leftRel H]

/--
lemma `right_bot_eq_right_quot` / 引理 `right_bot_eq_right_quot`

English:
lemma right_bot_eq_right_quot
  given: (H : Subgroup G)
  proof: by
  unfold Quotient
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]

中文:
引理 right_bot_eq_right_quot
  条件: (H : 子群 G)
  证明: by
  unfold Quotient
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]

Depends on / 依赖: Quotient, rel_bot_eq_right_group_rel, simp_rw
-/
lemma right_bot_eq_right_quot (H : Subgroup G) :
    Quotient (H : Set G) (⊥ : Subgroup G) = _root_.Quotient (rightRel H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]

/--
lemma `finite_quotient_iff_exists_finset_iUnion_eq_univ` / 引理 `finite_quotient_iff_exists_finset_iUnion_eq_univ`

English:
lemma finite_quotient_iff_exists_finset_iUnion_eq_univ
  given: (H K : Subgroup G)
  proof: by
  constructor
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    exact ⟨Finset.univ, by simpa using! iUnion_quotToDoubleCoset _ _⟩
  · rintro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      simp_rw [← Set.finite_univ_iff, ← this, I.finite_toSet]
    rw

中文:
引理 finite_quotient_iff_存在_finset_iUnion_eq_univ
  条件: (H K : 子群 G)
  证明: by
  constructor
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    exact ⟨Finset.univ, by simpa using! iUnion_quotToDoubleCoset _ _⟩
  · rintro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      simp_rw [← Set.finite_univ_iff, ← this, I.finite_toSet]
    rw

Depends on / 依赖: Finset, Finset.univ, I.finite_toSet, Quotient, Set.eq_univ_iff_forall, Set.finite_univ_iff, Set.univ, eq_univ_iff_forall, finite_toSet, finite_univ_iff, iUnion_quotToDoubleCoset, mem_quotToDoubleCoset_iff, nonempty_fintype, quotToDoubleCoset, simp_rw
-/
lemma finite_quotient_iff_exists_finset_iUnion_eq_univ (H K : Subgroup G) :
    Finite (Quotient (H : Set G) K) ↔
    exists I : Finset (Quotient (H : Set G) K), ⋃ i in I, quotToDoubleCoset H K i = .univ := by
  constructor
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    exact ⟨Finset.univ, by simpa using! iUnion_quotToDoubleCoset _ _⟩
  · rintro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      simp_rw [← Set.finite_univ_iff, ← this, I.finite_toSet]
    rw [Set.eq_univ_iff_forall] at hI ⊢
    rintro ⟨g⟩
    obtain ⟨_, ⟨i, _, rfl⟩, T, ⟨hi, rfl⟩, hT : g in quotToDoubleCoset H K i⟩ := hI g
    simpa [← (mem_quotToDoubleCoset_iff _ _).mp hT] using! hi

/--
lemma `iUnion_image_mk_leftRel` / 引理 `iUnion_image_mk_leftRel`

English:
lemma iUnion_image_mk_leftRel
  given: {H K : Subgroup G}
  proof: by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : exists i : Quotient H K, y in doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exac

中文:
引理 iUnion_image_mk_leftRel
  条件: {H K : 子群 G}
  证明: by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : exists i : Quotient H K, y in doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exac

Depends on / 依赖: Quotient, Set.iUnion_eq_univ_iff, Set.ne_univ_iff_exists_notMem, contrapose, doubleCoset, exists_rep, iUnion_eq_univ_iff, iUnion_quotToDoubleCoset, ne_univ_iff_exists_notMem
-/
lemma iUnion_image_mk_leftRel {H K : Subgroup G} :
    ⋃ q : Quotient H K, Quot.mk (leftRel K) '' doubleCoset (out q : G) H K = Set.univ := by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : exists i : Quotient H K, y in doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exact ⟨i, y, hi, hy⟩

/--
lemma `iUnion_image_mk_rightRel` / 引理 `iUnion_image_mk_rightRel`

English:
lemma iUnion_image_mk_rightRel
  given: {H K : Subgroup G}
  proof: by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : exists i : Quotient H K, y in doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exac

中文:
引理 iUnion_image_mk_rightRel
  条件: {H K : 子群 G}
  证明: by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : exists i : Quotient H K, y in doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exac

Depends on / 依赖: Quotient, Set.iUnion_eq_univ_iff, Set.ne_univ_iff_exists_notMem, contrapose, doubleCoset, exists_rep, iUnion_eq_univ_iff, iUnion_quotToDoubleCoset, ne_univ_iff_exists_notMem
-/
lemma iUnion_image_mk_rightRel {H K : Subgroup G} :
    ⋃ q : Quotient H K, Quot.mk (rightRel H) '' doubleCoset (out q : G) H K = Set.univ := by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : exists i : Quotient H K, y in doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exact ⟨i, y, hi, hy⟩

/--
lemma `iUnion_finset_leftRel_eq_univ_of_leftRel` / 引理 `iUnion_finset_leftRel_eq_univ_of_leftRel`

English:
lemma iUnion_finset_leftRel_eq_univ_of_leftRel
  statement: {H K : Subgroup G} {t : Finset (Quotient H K)}
  proof: by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (leftRel K) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq

中文:
引理 iUnion_finset_leftRel_eq_univ_of_leftRel
  结论: {H K : 子群 G} {t : 有限集 (商 H K)}
  证明: by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (leftRel K) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq

Depends on / 依赖: MulOpposite, MulOpposite.unop, Quot.mk, Quotient, Quotient.eq.mp, Set.mem_iUnion, Set.mem_image, Set.ne_univ_iff_exists_notMem, Set.univ_subset_iff, contrapose, doubleCoset_eq_of_mem, exists_prop, leftRel, mem_doubleCoset, mem_iUnion, mem_image, ne_eq, ne_univ_iff_exists_notMem, not_and, not_exists
-/
lemma iUnion_finset_leftRel_eq_univ_of_leftRel {H K : Subgroup G} {t : Finset (Quotient H K)}
    (ht : Set.univ subseteq ⋃ i in t, Quot.mk (leftRel K) '' doubleCoset (out i) H K) :
    ⋃ q in t, doubleCoset (out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (leftRel K) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, ?_⟩
  rw [← doubleCoset_eq_of_mem hq]; rw [mem_doubleCoset]
  obtain ⟨a', ha'⟩ := Quotient.eq.mp hx
  exact ⟨1, one_mem H, MulOpposite.unop a'⁻¹, Subgroup.mem_op.mp (by simp), by simpa
    using (eq_mul_inv_of_mul_eq ha')⟩

/--
lemma `iUnion_finset_rightRel_eq_univ_of_rightRel` / 引理 `iUnion_finset_rightRel_eq_univ_of_rightRel`

English:
lemma iUnion_finset_rightRel_eq_univ_of_rightRel
  statement: {H K : Subgroup G} {t : Finset (Quotient H K)}
  proof: by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (rightRel H) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q h

中文:
引理 iUnion_finset_rightRel_eq_univ_of_rightRel
  结论: {H K : 子群 G} {t : 有限集 (商 H K)}
  证明: by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (rightRel H) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q h

Depends on / 依赖: Quot.mk, Set.mem_iUnion, Set.mem_image, Set.ne_univ_iff_exists_notMem, Set.univ_subset_iff, contrapose, doubleCoset_eq_of_mem, exists_prop, mem_doubleCoset, mem_iUnion, mem_image, ne_eq, ne_univ_iff_exists_notMem, not_and, not_exists, rightRel, univ_subset_iff
-/
lemma iUnion_finset_rightRel_eq_univ_of_rightRel {H K : Subgroup G} {t : Finset (Quotient H K)}
    (ht : Set.univ subseteq ⋃ i in t, Quot.mk (rightRel H) '' doubleCoset (out i) H K) :
    ⋃ q in t, doubleCoset (out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (rightRel H) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, ?_⟩
  rw [← doubleCoset_eq_of_mem hq]; rw [mem_doubleCoset]
  obtain ⟨a, ha⟩ : exists a : H, x = a * q := by
    obtain ⟨a, ha⟩ : exists a : H, a * x = q := Quotient.eq.mp hx
    exact ⟨⟨a⁻¹, by simp⟩, eq_inv_mul_of_mul_eq ha⟩
  exact ⟨a.1, a.2, ⟨1, Subgroup.one_mem K, by simpa using ha⟩⟩

end DoubleCoset
