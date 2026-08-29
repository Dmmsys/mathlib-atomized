/-
Copyright (c) 2026 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inna Capdeboscq, Damiano Testa
-/

module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Subnormal subgroups

In this file, we define subnormal subgroups.

We also show some basic results about the interaction of subnormality and simplicity of groups.
These should cover most of the results needed in this case.

## Main Definition

`IsSubnormal H`: A subgroup `H` of a group `G` satisfies `IsSubnormal` if
* either `H = ⊤`;
* or there is a subgroup `K` of `G` containing `H` and such that `H` is normal in `K` and
  `K` satisfies `IsSubnormal`.

## Main Statements

* `eq_bot_or_top_of_isSimpleGroup`: the only subnormal subgroups of simple groups are
  `⊥`, the trivial subgroup, and `⊤`, the whole group.
* `isSubnormal_iff`: Shows that `IsSubnormal H` holds if and only if there is
  an increasing chain of subgroups, each normal in the following, starting from `H` and
  reaching `⊤` in a finite number of steps.
* `IsSubnormal.trans`: The relation of being `IsSubnormal` is transitive.

## Implementation Notes

We deviate from the common informal definition of subnormality and use an inductive predicate.
This turns out to be more convenient to work with.
We show the equivalence of the current definition with the existence of chains in
`isSubnormal_iff`.
-/

variable {G : Type*} [Group G] {H K : Subgroup G}

public section

namespace Subgroup

/--
Inductive type `IsSubnormal` / 归纳类型 `IsSubnormal`

English:
inductive IsSubnormal
  parameters: : Subgroup G -> Prop where
  constructors (2):
    - top: IsSubnormal (⊤ : Subgroup G)
    - step: forall H K, (h_le : H <= K) -> (hSubn : IsSubnormal K) -> (hN : (H.subgroupOf K).Normal) -> IsSubnormal H

中文:
归纳类型 IsSubnormal
  参数: : Subgroup G -> 命题 where
  构造子 (2 个):
    - top: IsSubnormal (⊤ : Subgroup G)
    - step: 对任意 H K, (h_le : H <= K) -> (hSubn : IsSubnormal K) -> (hN : (H.subgroupOf K).Normal) -> IsSubnormal H
-/
inductive IsSubnormal : Subgroup G -> Prop where
  /-- The whole subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : Subgroup G)
  /-- A subgroup `H` is subnormal if there is a subnormal subgroup `K` containing `H` that is
  subnormal itself and such that `H` is normal in `K`. -/
  | step : forall H K, (h_le : H <= K) -> (hSubn : IsSubnormal K) -> (hN : (H.subgroupOf K).Normal) ->
    IsSubnormal H

/--
Inductive type `_root_.AddSubgroup.IsSubnormal` / 归纳类型 `_root_.AddSubgroup.IsSubnormal`

English:
inductive _root_.AddSubgroup.IsSubnormal
  parameters: {G : Type*} [AddGroup G]
  constructors (2):
    - top: IsSubnormal (⊤ : AddSubgroup G)
    - step: forall H K, (h_le : H <= K) -> (hSubn : IsSubnormal K) -> (hN : (H.addSubgroupOf K).Normal) -> IsSubnormal H

中文:
归纳类型 _root_.AddSubgroup.IsSubnormal
  参数: {G : 类型} [AddGroup G]
  构造子 (2 个):
    - top: IsSubnormal (⊤ : AddSubgroup G)
    - step: 对任意 H K, (h_le : H <= K) -> (hSubn : IsSubnormal K) -> (hN : (H.addSubgroupOf K).Normal) -> IsSubnormal H
-/
inductive _root_.AddSubgroup.IsSubnormal {G : Type*} [AddGroup G] : AddSubgroup G -> Prop where
  /-- The whole additive subgroup `G` is subnormal in itself. -/
  | top : IsSubnormal (⊤ : AddSubgroup G)
  /-- An additive subgroup `H` is subnormal if there is a subnormal additive subgroup `K`
  containing `H` that is subnormal itself and such that `H` is normal in `K`. -/
  | step : forall H K, (h_le : H <= K) -> (hSubn : IsSubnormal K) -> (hN : (H.addSubgroupOf K).Normal) ->
    IsSubnormal H

attribute [simp] Subgroup.IsSubnormal.top

/-- A normal subgroup is subnormal. -/
@[to_additive /-- A normal additive subgroup is subnormal. -/]
/--
lemma `Normal.isSubnormal` / 引理 `Normal.isSubnormal`

English:
lemma Normal.isSubnormal
  given: (hn : H.Normal)
  statement: IsSubnormal H
  proof: IsSubnormal.step _ ⊤ le_top IsSubnormal.top normal_subgroupOf

中文:
引理 Normal.isSubnormal
  条件: (hn : H.Normal)
  结论: IsSubnormal H
  证明: IsSubnormal.step _ ⊤ le_top IsSubnormal.top normal_subgroupOf

Depends on / 依赖: IsSubnormal, IsSubnormal.step, IsSubnormal.top, le_top, normal_subgroupOf
-/
lemma Normal.isSubnormal (hn : H.Normal) : IsSubnormal H :=
  IsSubnormal.step _ ⊤ le_top IsSubnormal.top normal_subgroupOf

namespace IsSubnormal

/-- The trivial subgroup is subnormal. -/
@[to_additive (attr := simp) /-- The trivial additive subgroup is subnormal. -/]
/--
lemma `bot` / 引理 `bot`

English:
lemma bot
  statement: IsSubnormal (⊥ : Subgroup G)
  proof: normal_bot.isSubnormal

中文:
引理 bot
  结论: IsSubnormal (⊥ : Subgroup G)
  证明: normal_bot.isSubnormal

Depends on / 依赖: isSubnormal, normal_bot, normal_bot.isSubnormal
-/
lemma bot : IsSubnormal (⊥ : Subgroup G) := normal_bot.isSubnormal

/-- A subnormal subgroup of a simple group is normal. -/
@[to_additive /-- A subnormal additive subgroup of a simple additive group is normal. -/]
/--
lemma `normal_of_isSimpleGroup` / 引理 `normal_of_isSimpleGroup`

English:
lemma normal_of_isSimpleGroup
  given: (hG : IsSimpleGroup G) (hN : H.IsSubnormal)
  proof: by
  induction hN with
  | top => simp
  | step H K h_le hSubn hN Knorm =>
    obtain rfl | rfl := Knorm.eq_bot_or_eq_top
    · grind
    · grind [!normal_subgroupOf_iff_le_normalizer_inf, inf_of_le_left, normalizer_eq_top_iff]

中文:
引理 normal_of_isSimpleGroup
  条件: (hG : IsSimpleGroup G) (hN : H.IsSubnormal)
  证明: by
  induction hN with
  | top => simp
  | step H K h_le hSubn hN Knorm =>
    obtain rfl | rfl := Knorm.eq_bot_or_eq_top
    · grind
    · grind [!normal_subgroupOf_iff_le_normalizer_inf, inf_of_le_left, normalizer_eq_top_iff]

Depends on / 依赖: Knorm.eq_bot_or_eq_top, eq_bot_or_eq_top, h_le, inf_of_le_left, normal_subgroupOf_iff_le_normalizer_inf, normalizer_eq_top_iff
-/
lemma normal_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : H.IsSubnormal) :
    H.Normal := by
  induction hN with
  | top => simp
  | step H K h_le hSubn hN Knorm =>
    obtain rfl | rfl := Knorm.eq_bot_or_eq_top
    · grind
    · grind [!normal_subgroupOf_iff_le_normalizer_inf, inf_of_le_left, normalizer_eq_top_iff]

/-- A subnormal subgroup of a simple group is either trivial or the whole group. -/
@[to_additive /-- A subnormal additive subgroup of a simple additive group is either trivial or the
whole group. -/]
/--
lemma `eq_bot_or_top_of_isSimpleGroup` / 引理 `eq_bot_or_top_of_isSimpleGroup`

English:
lemma eq_bot_or_top_of_isSimpleGroup
  given: (hG : IsSimpleGroup G) (hN : IsSubnormal H)
  proof: (hN.normal_of_isSimpleGroup hG).eq_bot_or_eq_top

@[to_additive]

中文:
引理 eq_bot_or_top_of_isSimpleGroup
  条件: (hG : IsSimpleGroup G) (hN : IsSubnormal H)
  证明: (hN.normal_of_isSimpleGroup hG).eq_bot_or_eq_top

@[to_additive]

Depends on / 依赖: eq_bot_or_eq_top, hN.normal_of_isSimpleGroup, normal_of_isSimpleGroup
-/
lemma eq_bot_or_top_of_isSimpleGroup (hG : IsSimpleGroup G) (hN : IsSubnormal H) :
    H = ⊥ ∨ H = ⊤ :=
  (hN.normal_of_isSimpleGroup hG).eq_bot_or_eq_top

@[to_additive]
/--
lemma `iff_eq_top_or_exists` / 引理 `iff_eq_top_or_exists`

English:
lemma iff_eq_top_or_exists
  proof: by
    induction h with
    | top => simp
    | step H K HK hS hN ih =>
      obtain rfl | ⟨K', HK', hS', hN'⟩ := ih
      · obtain rfl | hH := eq_or_ne H ⊤
        · simp
        · exact Or.inr ⟨⊤, by simp [hH.lt_top , *]⟩
      right
      obtain rfl | hH := eq_or_ne H K
      · use K'
      · exa

中文:
引理 iff_eq_top_or_exists
  证明: by
    induction h with
    | top => simp
    | step H K HK hS hN ih =>
      obtain rfl | ⟨K', HK', hS', hN'⟩ := ih
      · obtain rfl | hH := eq_or_ne H ⊤
        · simp
        · exact Or.inr ⟨⊤, by simp [hH.lt_top , *]⟩
      right
      obtain rfl | hH := eq_or_ne H K
      · use K'
      · exa

Depends on / 依赖: HK.le, HK.lt_of_ne, Or.inr, eq_or_ne, hH.lt_top, lt_of_ne, lt_top
-/
lemma iff_eq_top_or_exists :
    IsSubnormal H ↔ H = ⊤ ∨ exists K, H < K ∧ IsSubnormal K ∧ (H.subgroupOf K).Normal where
  mp h := by
    induction h with
    | top => simp
    | step H K HK hS hN ih =>
      obtain rfl | ⟨K', HK', hS', hN'⟩ := ih
      · obtain rfl | hH := eq_or_ne H ⊤
        · simp
        · exact Or.inr ⟨⊤, by simp [hH.lt_top , *]⟩
      right
      obtain rfl | hH := eq_or_ne H K
      · use K'
      · exact ⟨K, by simpa [*] using HK.lt_of_ne hH⟩
  mpr h := by
    obtain rfl | ⟨K, HK, Ksn, h⟩ := h
    · exact top
    · exact step _ _ HK.le Ksn h

/-- A proper subnormal subgroup is contained in a proper normal subgroup. -/
@[to_additive /-- A proper subnormal additive subgroup is contained in a proper normal additive
subgroup. -/]
/--
lemma `exists_normal_and_le_and_lt_top_of_ne` / 引理 `exists_normal_and_le_and_lt_top_of_ne`

English:
lemma exists_normal_and_le_and_lt_top_of_ne
  given: (hN : H.IsSubnormal) (ne_top : H != ⊤)
  proof: by
  induction hN with
  | top => contradiction
  | step H K h_le hSubn hN ih =>
    obtain rfl | K_ne := eq_or_ne K ⊤
    · rw [normal_subgroupOf_iff_le_normalizer h_le, top_le_iff, normalizer_eq_top_iff] at hN
      exact ⟨H, hN, le_rfl, ne_top.lt_top⟩
    · grind

中文:
引理 exists_normal_and_le_and_lt_top_of_ne
  条件: (hN : H.IsSubnormal) (ne_top : H != ⊤)
  证明: by
  induction hN with
  | top => contradiction
  | step H K h_le hSubn hN ih =>
    obtain rfl | K_ne := eq_or_ne K ⊤
    · rw [normal_subgroupOf_iff_le_normalizer h_le, top_le_iff, normalizer_eq_top_iff] at hN
      exact ⟨H, hN, le_rfl, ne_top.lt_top⟩
    · grind

Depends on / 依赖: K_ne, eq_or_ne, h_le, le_rfl, lt_top, ne_top, ne_top.lt_top, normal_subgroupOf_iff_le_normalizer, normalizer_eq_top_iff, top_le_iff
-/
lemma exists_normal_and_le_and_lt_top_of_ne (hN : H.IsSubnormal) (ne_top : H != ⊤) :
    exists K, K.Normal ∧ H <= K ∧ K < ⊤ := by
  induction hN with
  | top => contradiction
  | step H K h_le hSubn hN ih =>
    obtain rfl | K_ne := eq_or_ne K ⊤
    · rw [normal_subgroupOf_iff_le_normalizer h_le, top_le_iff, normalizer_eq_top_iff] at hN
      exact ⟨H, hN, le_rfl, ne_top.lt_top⟩
    · grind

/--
A subnormal subgroup is either the whole group or it is contained in a proper normal subgroup.
-/
@[to_additive /-- A subnormal additive subgroup is either the whole group or it is contained in a
proper normal additive subgroup. -/]
/--
lemma `lt_normal` / 引理 `lt_normal`

English:
lemma lt_normal
  given: (hN : H.IsSubnormal)
  statement: H = ⊤ ∨ exists K, K.Normal ∧ H <= K ∧ K < ⊤
  proof: by
  obtain rfl | H_ne := eq_or_ne H ⊤
  · simp
  · grind only [iff_eq_top_or_exists, exists_normal_and_le_and_lt_top_of_ne]

中文:
引理 lt_normal
  条件: (hN : H.IsSubnormal)
  结论: H = ⊤ ∨ 存在 K, K.Normal ∧ H <= K ∧ K < ⊤
  证明: by
  obtain rfl | H_ne := eq_or_ne H ⊤
  · simp
  · grind only [iff_eq_top_or_exists, exists_normal_and_le_and_lt_top_of_ne]

Depends on / 依赖: H_ne, eq_or_ne, exists_normal_and_le_and_lt_top_of_ne, iff_eq_top_or_exists
-/
lemma lt_normal (hN : H.IsSubnormal) : H = ⊤ ∨ exists K, K.Normal ∧ H <= K ∧ K < ⊤ := by
  obtain rfl | H_ne := eq_or_ne H ⊤
  · simp
  · grind only [iff_eq_top_or_exists, exists_normal_and_le_and_lt_top_of_ne]

/--
A characterisation of satisfying `IsSubnormal` in terms of chains of subgroups, each normal in
the following one.

The sequence stabilises once it reaches `⊤`, which is guaranteed at the asserted `n`.
-/
@[to_additive /-- A characterisation of satisfying `IsSubnormal` in terms of chains of additive
subgroups, each normal in the following one.

The sequence stabilises once it reaches `⊤`, which is guaranteed at the asserted `n`. -/]
/--
lemma `isSubnormal_iff` / 引理 `isSubnormal_iff`

English:
lemma isSubnormal_iff
  statement: H.IsSubnormal ↔
  proof: by
    induction h with
    | top =>
      use 0, fun _ => ⊤, ?_, (by simp)
      exact monotone_nat_of_le_succ fun _ => le_top
    | step H K h_le hSubn hN ih =>
      obtain ⟨n, f, hf, f0, fn⟩ := ih
      use n + 1, fun | 0 => H | n + 1 => f n, ?_, ?_
      · grind
      · refine monotone_nat_of_l

中文:
引理 isSubnormal_iff
  结论: H.IsSubnormal ↔
  证明: by
    induction h with
    | top =>
      use 0, fun _ => ⊤, ?_, (by simp)
      exact monotone_nat_of_le_succ fun _ => le_top
    | step H K h_le hSubn hN ih =>
      obtain ⟨n, f, hf, f0, fn⟩ := ih
      use n + 1, fun | 0 => H | n + 1 => f n, ?_, ?_
      · grind
      · refine monotone_nat_of_l

Depends on / 依赖: H_le, Nat.le_add_right, h_le, le_add_right, le_top, monotone_iff_forall_lt, monotone_nat_of_le_succ, revert
-/
lemma isSubnormal_iff : H.IsSubnormal ↔
    exists n, exists f : Nat -> Subgroup G,
    (Monotone f) ∧ (forall i, ((f i).subgroupOf (f (i + 1))).Normal) ∧
      f 0 = H ∧ f n = ⊤ where
  mp h := by
    induction h with
    | top =>
      use 0, fun _ => ⊤, ?_, (by simp)
      exact monotone_nat_of_le_succ fun _ => le_top
    | step H K h_le hSubn hN ih =>
      obtain ⟨n, f, hf, f0, fn⟩ := ih
      use n + 1, fun | 0 => H | n + 1 => f n, ?_, ?_
      · grind
      · refine monotone_nat_of_le_succ ?_
        grind only [monotone_iff_forall_lt]
      · grind
  mpr := by
    rintro ⟨n, hyps⟩
    revert H
    induction n with
    | zero => simp_all
    | succ n ih =>
      rintro J ⟨F, hF, H_le, rfl, ih1⟩
      refine step _ _ (hF <| Nat.le_add_right 0 1) ?_ (H_le _)
      refine ih ⟨fun n => F (n + 1), ?_⟩
      grind only [Monotone, monotone_iff_forall_lt]

alias ⟨exists_chain, _⟩ := isSubnormal_iff

/--
Subnormality is transitive.

This version involves an explicit `subtype`; the version `IsSubnormal.trans` does not.
-/
@[to_additive /-- Subnormality is transitive.

This version involves an explicit `subtype`; the version `IsSubnormal.trans` does not. -/]
protected
/--
lemma `trans'` / 引理 `trans'`

English:
lemma trans'
  given: {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K)
  proof: by
  induction Hsn with
  | top =>
    rwa [← MonoidHom.range_eq_map, range_subtype]
  | step A B h_le hSubn hN ih =>
    refine step (A.map K.subtype) (B.map K.subtype) (map_mono h_le) ih ?_
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (map_mon

中文:
引理 trans'
  条件: {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K)
  证明: by
  induction Hsn with
  | top =>
    rwa [← MonoidHom.range_eq_map, range_subtype]
  | step A B h_le hSubn hN ih =>
    refine step (A.map K.subtype) (B.map K.subtype) (map_mono h_le) ih ?_
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (map_mon

Depends on / 依赖: A.map, B.map, K.subtype, MonoidHom, MonoidHom.range_eq_map, h_le, le_normalizer_map, le_trans, map_mono, normal_subgroupOf_iff_le_normalizer, range_eq_map, range_subtype, subtype
-/
lemma trans' {H : Subgroup K} (Hsn : IsSubnormal H) (Ksn : IsSubnormal K) :
    IsSubnormal (H.map K.subtype) := by
  induction Hsn with
  | top =>
    rwa [← MonoidHom.range_eq_map, range_subtype]
  | step A B h_le hSubn hN ih =>
    refine step (A.map K.subtype) (B.map K.subtype) (map_mono h_le) ih ?_
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (map_mono h_le)]
    exact le_trans (map_mono hN) (le_normalizer_map _)

/--
If `H` is a subnormal subgroup of `K` and `K` is a subnormal subgroup of `G`,
then `H` is a subnormal subgroup of `G`.
-/
@[to_additive /-- If `H` is a subnormal additive subgroup of `K` and `K` is a subnormal
additive subgroup of `G`, then `H` is a subnormal additive subgroup of `G`. -/]
protected
/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (HK : H <= K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K)
  proof: by
  have key := Hsn.trans' Ksn
  rwa [map_subgroupOf_eq_of_le HK] at key

中文:
引理 trans
  条件: (HK : H <= K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K)
  证明: by
  have key := Hsn.trans' Ksn
  rwa [map_subgroupOf_eq_of_le HK] at key

Depends on / 依赖: Hsn.trans, map_subgroupOf_eq_of_le
-/
lemma trans (HK : H <= K) (Hsn : IsSubnormal (H.subgroupOf K)) (Ksn : IsSubnormal K) :
    IsSubnormal H := by
  have key := Hsn.trans' Ksn
  rwa [map_subgroupOf_eq_of_le HK] at key

/-- The image of a subnormal subgroup under a surjective homomorphism is subnormal. -/
@[to_additive
/-- The image of a subnormal additive subgroup under a surjective homomorphism is subnormal. -/]
protected
/--
lemma `map` / 引理 `map`

English:
lemma map
  given: {G'} [Group G'] {f : G ->* G'} (hf : Function.Surjective f) (hS : H.IsSubnormal)
  proof: by
  induction hS with
  | top =>
    rw [map_top_of_surjective f hf]
    apply top
  | step H K h_le hSubn hN ih =>
    apply step _ (map f K) (map_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    exact normal_subgroupOf_of_le_normalizer ((map_mono hN).trans (H.le_normalize

中文:
引理 map
  条件: {G'} [Group G'] {f : G ->* G'} (hf : Function.Surjective f) (hS : H.IsSubnormal)
  证明: by
  induction hS with
  | top =>
    rw [map_top_of_surjective f hf]
    apply top
  | step H K h_le hSubn hN ih =>
    apply step _ (map f K) (map_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    exact normal_subgroupOf_of_le_normalizer ((map_mono hN).trans (H.le_normalize

Depends on / 依赖: H.le_normalizer_map, h_le, le_normalizer_map, map_mono, map_top_of_surjective, normal_subgroupOf_iff_le_normalizer, normal_subgroupOf_of_le_normalizer
-/
lemma map {G'} [Group G'] {f : G ->* G'} (hf : Function.Surjective f) (hS : H.IsSubnormal) :
    IsSubnormal (map f H) := by
  induction hS with
  | top =>
    rw [map_top_of_surjective f hf]
    apply top
  | step H K h_le hSubn hN ih =>
    apply step _ (map f K) (map_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    exact normal_subgroupOf_of_le_normalizer ((map_mono hN).trans (H.le_normalizer_map f))

/-- The quotient of a subnormal subgroup by a normal subgroup is subnormal. -/
@[to_additive
/-- The quotient of a subnormal additive subgroup by a normal additive subgroup is subnormal. -/]
/--
lemma `quotient` / 引理 `quotient`

English:
lemma quotient
  given: [K.Normal] (hS : H.IsSubnormal)
  proof: hS.map (QuotientGroup.mk'_surjective K)

中文:
引理 quotient
  条件: [K.Normal] (hS : H.IsSubnormal)
  证明: hS.map (QuotientGroup.mk'_surjective K)
-/
protected lemma quotient [K.Normal] (hS : H.IsSubnormal) :
    IsSubnormal (map (QuotientGroup.mk' K) H) :=
  hS.map (QuotientGroup.mk'_surjective K)

/-- The inverse image of a subnormal subgroup under a group homomorphism is a subnormal subgroup. -/
@[to_additive /-- The inverse image of a subnormal additive subgroup under an additive group
homomorphism is a subnormal additive subgroup. -/]
protected
/--
lemma `comap` / 引理 `comap`

English:
lemma comap
  given: {G'} [Group G'] {H' : Subgroup G'} (f : G ->* G') (h : H'.IsSubnormal)
  proof: by
  induction h with
  | top => simp
  | step H K h_le hSubn hN ih =>
    apply step _ (comap f K) (comap_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (comap_mono h_le)]
    exact (comap_mono hN).trans (le_normalizer_comap f)

@[t

中文:
引理 comap
  条件: {G'} [Group G'] {H' : Subgroup G'} (f : G ->* G') (h : H'.IsSubnormal)
  证明: by
  induction h with
  | top => simp
  | step H K h_le hSubn hN ih =>
    apply step _ (comap f K) (comap_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (comap_mono h_le)]
    exact (comap_mono hN).trans (le_normalizer_comap f)

@[t

Depends on / 依赖: comap_mono, h_le, le_normalizer_comap, normal_subgroupOf_iff_le_normalizer
-/
lemma comap {G'} [Group G'] {H' : Subgroup G'} (f : G ->* G') (h : H'.IsSubnormal) :
    (comap f H').IsSubnormal := by
  induction h with
  | top => simp
  | step H K h_le hSubn hN ih =>
    apply step _ (comap f K) (comap_mono h_le) ih
    rw [normal_subgroupOf_iff_le_normalizer h_le] at hN
    rw [normal_subgroupOf_iff_le_normalizer (comap_mono h_le)]
    exact (comap_mono hN).trans (le_normalizer_comap f)

@[to_additive (attr := simp)]
/--
lemma `subgroupOf` / 引理 `subgroupOf`

English:
lemma subgroupOf
  given: (hH : H.IsSubnormal)
  statement: (H.subgroupOf K).IsSubnormal
  proof: hH.comap _

中文:
引理 subgroupOf
  条件: (hH : H.IsSubnormal)
  结论: (H.subgroupOf K).IsSubnormal
  证明: hH.comap _
-/
protected lemma subgroupOf (hH : H.IsSubnormal) : (H.subgroupOf K).IsSubnormal := hH.comap _

/-- The intersection of two subnormal subgroups is subnormal. -/
@[to_additive /-- The intersection of two subnormal additive subgroups is additive subnormal. -/]
/--
lemma `inf` / 引理 `inf`

English:
lemma inf
  given: (hH : H.IsSubnormal) (hK : K.IsSubnormal)
  statement: (H ⊓ K).IsSubnormal
  proof: by
  simpa using hH.subgroupOf.trans' hK

中文:
引理 inf
  条件: (hH : H.IsSubnormal) (hK : K.IsSubnormal)
  结论: (H ⊓ K).IsSubnormal
  证明: by
  simpa using hH.subgroupOf.trans' hK
-/
protected lemma inf (hH : H.IsSubnormal) (hK : K.IsSubnormal) : (H ⊓ K).IsSubnormal := by
  simpa using hH.subgroupOf.trans' hK

open scoped Pointwise

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  statement: {Γ : Type*} [Group Γ] [MulDistribMulAction Γ G] (hS : H.IsSubnormal)
  proof: hS.map (MulAction.surjective g)

中文:
引理 smul
  结论: {Γ : 类型} [Group Γ] [MulDistribMulAction Γ G] (hS : H.IsSubnormal)
  证明: hS.map (MulAction.surjective g)
-/
protected lemma smul {Γ : Type*} [Group Γ] [MulDistribMulAction Γ G] (hS : H.IsSubnormal)
    (g : Γ) : (g • H).IsSubnormal :=
  hS.map (MulAction.surjective g)

/-- If the subgroup `H` of a group `G` is trivial, then it is subnormal. -/
@[to_additive /-- If the additive subgroup `H` of a group `G` is trivial, then it is subnormal. -/]
/--
lemma `of_subsingleton` / 引理 `of_subsingleton`

English:
lemma of_subsingleton
  given: [Subsingleton H]
  statement: H.IsSubnormal
  proof: by
  simp [eq_bot_of_subsingleton H]

中文:
引理 of_subsingleton
  条件: [Subsingleton H]
  结论: H.IsSubnormal
  证明: by
  simp [eq_bot_of_subsingleton H]

Depends on / 依赖: eq_bot_of_subsingleton
-/
lemma of_subsingleton [Subsingleton H] : H.IsSubnormal := by
  simp [eq_bot_of_subsingleton H]

end Subgroup.IsSubnormal
