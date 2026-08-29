/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.
Several theorems proved in this file are known as Lagrange's theorem.

## Main definitions

- `H.index` : the index of `H : Subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relIndex K` : the relative index of `H : Subgroup G` in `K : Subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

## Main results

- `card_mul_index` : `Nat.card H * H.index = Nat.card G`
- `index_mul_card` : `H.index * Nat.card H = Nat.card G`
- `index_dvd_card` : `H.index ∣ Nat.card G`
- `relIndex_mul_index` : If `H ≤ K`, then `H.relindex K * K.index = H.index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relIndex_mul_relIndex` : `relIndex` is multiplicative in towers
- `MulAction.index_stabilizer`: the index of the stabilizer is the cardinality of the orbit
-/

@[expose] public section

assert_not_exists Field

open scoped Pointwise

namespace Subgroup

open Cardinal Function

variable {G G' : Type*} [Group G] [Group G'] (H K L : Subgroup G)

/-- The index of a subgroup as a natural number. Returns `0` if the index is infinite. -/
@[to_additive (attr := wikidata Q1464168) /-- The index of an additive subgroup as a natural number.
Returns 0 if the index is infinite. -/]
/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: : Nat
  body: Nat.card (G ⧸ H)

中文:
定义 index
  签名: : 自然数
  定义体: Nat.card (G ⧸ H)

Depends on / 依赖: Nat.card
-/
noncomputable def index : Nat :=
  Nat.card (G ⧸ H)

/-- If `H` and `K` are subgroups of a group `G`, then `relIndex H K : ℕ` is the index
of `H ∩ K` in `K`. The function returns `0` if the index is infinite. -/
@[to_additive /-- If `H` and `K` are subgroups of an additive group `G`, then `relIndex H K : ℕ`
is the index of `H ∩ K` in `K`. The function returns `0` if the index is infinite. -/]
/--
Definition of `relIndex` / `relIndex` 的定义

English:
definition relIndex
  signature: : Nat
  body: (H.subgroupOf K).index

@[to_additive]

中文:
定义 relIndex
  签名: : 自然数
  定义体: (H.subgroupOf K).index

@[to_additive]

Depends on / 依赖: H.subgroupOf, subgroupOf
-/
noncomputable def relIndex : Nat :=
  (H.subgroupOf K).index

@[to_additive]
/--
theorem `index_comap_of_surjective` / 定理 `index_comap_of_surjective`

English:
theorem index_comap_of_surjective
  given: {f : G' ->* G} (hf : Function.Surjective f)
  proof: by
  have key : forall x y : G',
      QuotientGroup.leftRel (H.comap f) x y ↔ QuotientGroup.leftRel H (f x) (f y) := by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· in H) (by rw [f.map_mul, f.map_inv]))
  refine Nat.card_congr (Equiv.ofBijective (Quotient

中文:
定理 index_comap_of_surjective
  条件: {f : G' ->* G} (hf : 函数.满射 f)
  证明: by
  have key : forall x y : G',
      QuotientGroup.leftRel (H.comap f) x y ↔ QuotientGroup.leftRel H (f x) (f y) := by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· in H) (by rw [f.map_mul, f.map_inv]))
  refine Nat.card_congr (Equiv.ofBijective (Quotient

Depends on / 依赖: Equiv.ofBijective, H.comap, Nat.card_congr, Quotient, Quotient.eq, Quotient.ind, Quotient.map, QuotientGroup, QuotientGroup.leftRel, QuotientGroup.leftRel_apply, card_congr, congr_arg, f.map_inv, f.map_mul, iff_of_eq, leftRel, leftRel_apply, map_inv, map_mul, ofBijective
-/
theorem index_comap_of_surjective {f : G' ->* G} (hf : Function.Surjective f) :
    (H.comap f).index = H.index := by
  have key : forall x y : G',
      QuotientGroup.leftRel (H.comap f) x y ↔ QuotientGroup.leftRel H (f x) (f y) := by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· in H) (by rw [f.map_mul, f.map_inv]))
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' f fun x y => (key x y).mp) ⟨?_, ?_⟩)
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y => ?_
    exact (key x y).mpr
  · refine Quotient.ind' fun x => ?_
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y, (Quotient.map'_mk'' f _ y).trans (congr_arg Quotient.mk'' hy)⟩

@[to_additive]
/--
theorem `index_comap` / 定理 `index_comap`

English:
theorem index_comap
  given: (f : G' ->* G)
  proof: Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)

@[to_additive]

中文:
定理 index_comap
  条件: (f : G' ->* G)
  证明: Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)

@[to_additive]

Depends on / 依赖: Eq.trans, H.subgroupOf, congr_arg, f.range, f.rangeRestrict_surjective, index_comap_of_surjective, rangeRestrict_surjective, subgroupOf
-/
theorem index_comap (f : G' ->* G) :
    (H.comap f).index = H.relIndex f.range :=
  Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)

@[to_additive]
/--
theorem `relIndex_comap` / 定理 `relIndex_comap`

English:
theorem relIndex_comap
  given: (f : G' ->* G) (K : Subgroup G')
  proof: by
  rw [relIndex]; rw [subgroupOf]; rw [comap_comap]; rw [index_comap]; rw [← f.map_range]; rw [K.range_subtype]

@[to_additive]

中文:
定理 relIndex_comap
  条件: (f : G' ->* G) (K : 子群 G')
  证明: by
  rw [relIndex]; rw [subgroupOf]; rw [comap_comap]; rw [index_comap]; rw [← f.map_range]; rw [K.range_subtype]

@[to_additive]

Depends on / 依赖: K.range_subtype, comap_comap, f.map_range, index_comap, map_range, range_subtype, relIndex, subgroupOf
-/
theorem relIndex_comap (f : G' ->* G) (K : Subgroup G') :
    relIndex (comap f H) K = relIndex H (map f K) := by
  rw [relIndex]; rw [subgroupOf]; rw [comap_comap]; rw [index_comap]; rw [← f.map_range]; rw [K.range_subtype]

@[to_additive]
/--
theorem `relIndex_map_map_of_injective` / 定理 `relIndex_map_map_of_injective`

English:
theorem relIndex_map_map_of_injective
  given: {f : G ->* G'} (H K : Subgroup G) (hf : Function.Injective f)
  proof: by
  rw [← Subgroup.relIndex_comap]; rw [Subgroup.comap_map_eq_self_of_injective hf]

@[to_additive]

中文:
定理 relIndex_map_map_of_injective
  条件: {f : G ->* G'} (H K : 子群 G) (hf : 函数.单射 f)
  证明: by
  rw [← Subgroup.relIndex_comap]; rw [Subgroup.comap_map_eq_self_of_injective hf]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.comap_map_eq_self_of_injective, Subgroup.relIndex_comap, comap_map_eq_self_of_injective, relIndex_comap
-/
theorem relIndex_map_map_of_injective {f : G ->* G'} (H K : Subgroup G) (hf : Function.Injective f) :
    relIndex (map f H) (map f K) = relIndex H K := by
  rw [← Subgroup.relIndex_comap]; rw [Subgroup.comap_map_eq_self_of_injective hf]

@[to_additive]
/--
theorem `relIndex_map_map` / 定理 `relIndex_map_map`

English:
theorem relIndex_map_map
  given: (f : G ->* G') (H K : Subgroup G)
  proof: by
  rw [← comap_map_eq]; rw [← comap_map_eq]; rw [relIndex_comap]; rw [(gc_map_comap f).l_u_l_eq_l]

中文:
定理 relIndex_map_map
  条件: (f : G ->* G') (H K : 子群 G)
  证明: by
  rw [← comap_map_eq]; rw [← comap_map_eq]; rw [relIndex_comap]; rw [(gc_map_comap f).l_u_l_eq_l]

Depends on / 依赖: comap_map_eq, gc_map_comap, l_u_l_eq_l, relIndex_comap
-/
theorem relIndex_map_map (f : G ->* G') (H K : Subgroup G) :
    (map f H).relIndex (map f K) = (H ⊔ f.ker).relIndex (K ⊔ f.ker) := by
  rw [← comap_map_eq]; rw [← comap_map_eq]; rw [relIndex_comap]; rw [(gc_map_comap f).l_u_l_eq_l]

variable {H K L}

@[to_additive relIndex_mul_index]
/--
theorem `relIndex_mul_index` / 定理 `relIndex_mul_index`

English:
theorem relIndex_mul_index
  given: (h : H <= K)
  statement: H.relIndex K * K.index = H.index
  proof: by
  rw [mul_comm]
  simp_rw [relIndex, index, ← Nat.card_prod, Nat.card_congr <| quotientEquivProdOfLE h]

@[to_additive]

中文:
定理 relIndex_mul_index
  条件: (h : H <= K)
  结论: H.relIndex K * K.index = H.index
  证明: by
  rw [mul_comm]
  simp_rw [relIndex, index, ← Nat.card_prod, Nat.card_congr <| quotientEquivProdOfLE h]

@[to_additive]

Depends on / 依赖: Nat.card_congr, Nat.card_prod, card_congr, card_prod, mul_comm, quotientEquivProdOfLE, relIndex, simp_rw
-/
theorem relIndex_mul_index (h : H <= K) : H.relIndex K * K.index = H.index := by
  rw [mul_comm]
  simp_rw [relIndex, index, ← Nat.card_prod, Nat.card_congr <| quotientEquivProdOfLE h]

@[to_additive]
/--
theorem `index_dvd_of_le` / 定理 `index_dvd_of_le`

English:
theorem index_dvd_of_le
  given: (h : H <= K)
  statement: K.index ∣ H.index
  proof: dvd_of_mul_left_eq (H.relIndex K) (relIndex_mul_index h)

@[to_additive]

中文:
定理 index_dvd_of_le
  条件: (h : H <= K)
  结论: K.index ∣ H.index
  证明: dvd_of_mul_left_eq (H.relIndex K) (relIndex_mul_index h)

@[to_additive]

Depends on / 依赖: H.relIndex, dvd_of_mul_left_eq, relIndex, relIndex_mul_index
-/
theorem index_dvd_of_le (h : H <= K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relIndex K) (relIndex_mul_index h)

@[to_additive]
/--
theorem `relIndex_dvd_index_of_le` / 定理 `relIndex_dvd_index_of_le`

English:
theorem relIndex_dvd_index_of_le
  given: (h : H <= K)
  statement: H.relIndex K ∣ H.index
  proof: dvd_of_mul_right_eq K.index (relIndex_mul_index h)

@[to_additive]

中文:
定理 relIndex_dvd_index_of_le
  条件: (h : H <= K)
  结论: H.relIndex K ∣ H.index
  证明: dvd_of_mul_right_eq K.index (relIndex_mul_index h)

@[to_additive]

Depends on / 依赖: K.index, dvd_of_mul_right_eq, relIndex_mul_index
-/
theorem relIndex_dvd_index_of_le (h : H <= K) : H.relIndex K ∣ H.index :=
  dvd_of_mul_right_eq K.index (relIndex_mul_index h)

@[to_additive]
/--
theorem `relIndex_subgroupOf` / 定理 `relIndex_subgroupOf`

English:
theorem relIndex_subgroupOf
  given: (hKL : K <= L)
  proof: ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

中文:
定理 relIndex_subgroupOf
  条件: (hKL : K <= L)
  证明: ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

Depends on / 依赖: H.subgroupOf, congr_arg, inclusion, inclusion_range, index_comap, subgroupOf
-/
theorem relIndex_subgroupOf (hKL : K <= L) :
    (H.subgroupOf L).relIndex (K.subgroupOf L) = H.relIndex K :=
  ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

variable (H K L)

@[to_additive relIndex_mul_relIndex]
/--
theorem `relIndex_mul_relIndex` / 定理 `relIndex_mul_relIndex`

English:
theorem relIndex_mul_relIndex
  given: (hHK : H <= K) (hKL : K <= L)
  proof: by
  rw [← relIndex_subgroupOf hKL]
  exact relIndex_mul_index fun x hx => hHK hx

@[to_additive]

中文:
定理 relIndex_mul_relIndex
  条件: (hHK : H <= K) (hKL : K <= L)
  证明: by
  rw [← relIndex_subgroupOf hKL]
  exact relIndex_mul_index fun x hx => hHK hx

@[to_additive]

Depends on / 依赖: relIndex_mul_index, relIndex_subgroupOf
-/
theorem relIndex_mul_relIndex (hHK : H <= K) (hKL : K <= L) :
    H.relIndex K * K.relIndex L = H.relIndex L := by
  rw [← relIndex_subgroupOf hKL]
  exact relIndex_mul_index fun x hx => hHK hx

@[to_additive]
/--
theorem `inf_relIndex_right` / 定理 `inf_relIndex_right`

English:
theorem inf_relIndex_right
  statement: (H ⊓ K).relIndex K = H.relIndex K
  proof: by
  rw [relIndex]; rw [relIndex]; rw [inf_subgroupOf_right]

@[to_additive]

中文:
定理 inf_relIndex_right
  结论: (H ⊓ K).relIndex K = H.relIndex K
  证明: by
  rw [relIndex]; rw [relIndex]; rw [inf_subgroupOf_right]

@[to_additive]

Depends on / 依赖: inf_subgroupOf_right, relIndex
-/
theorem inf_relIndex_right : (H ⊓ K).relIndex K = H.relIndex K := by
  rw [relIndex]; rw [relIndex]; rw [inf_subgroupOf_right]

@[to_additive]
/--
theorem `inf_relIndex_left` / 定理 `inf_relIndex_left`

English:
theorem inf_relIndex_left
  statement: (H ⊓ K).relIndex H = K.relIndex H
  proof: by
  rw [inf_comm]; rw [inf_relIndex_right]

@[to_additive relIndex_inf_mul_relIndex]

中文:
定理 inf_relIndex_left
  结论: (H ⊓ K).relIndex H = K.relIndex H
  证明: by
  rw [inf_comm]; rw [inf_relIndex_right]

@[to_additive relIndex_inf_mul_relIndex]

Depends on / 依赖: inf_comm, inf_relIndex_right
-/
theorem inf_relIndex_left : (H ⊓ K).relIndex H = K.relIndex H := by
  rw [inf_comm]; rw [inf_relIndex_right]

@[to_additive relIndex_inf_mul_relIndex]
/--
theorem `relIndex_inf_mul_relIndex` / 定理 `relIndex_inf_mul_relIndex`

English:
theorem relIndex_inf_mul_relIndex
  statement: H.relIndex (K ⊓ L) * K.relIndex L = (H ⊓ K).relIndex L
  proof: by
  rw [← inf_relIndex_right H (K ⊓ L)]; rw [← inf_relIndex_right K L]; rw [← inf_relIndex_right (H ⊓ K) L]; rw [inf_assoc]; rw [relIndex_mul_relIndex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]

@[to_additive (attr := simp)]

中文:
定理 relIndex_inf_mul_relIndex
  结论: H.relIndex (K ⊓ L) * K.relIndex L = (H ⊓ K).relIndex L
  证明: by
  rw [← inf_relIndex_right H (K ⊓ L)]; rw [← inf_relIndex_right K L]; rw [← inf_relIndex_right (H ⊓ K) L]; rw [inf_assoc]; rw [relIndex_mul_relIndex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]

@[to_additive (attr := simp)]

Depends on / 依赖: inf_assoc, inf_le_right, inf_relIndex_right, relIndex_mul_relIndex
-/
theorem relIndex_inf_mul_relIndex : H.relIndex (K ⊓ L) * K.relIndex L = (H ⊓ K).relIndex L := by
  rw [← inf_relIndex_right H (K ⊓ L)]; rw [← inf_relIndex_right K L]; rw [← inf_relIndex_right (H ⊓ K) L]; rw [inf_assoc]; rw [relIndex_mul_relIndex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]

@[to_additive (attr := simp)]
/--
theorem `relIndex_sup_right` / 定理 `relIndex_sup_right`

English:
theorem relIndex_sup_right
  given: [K.Normal]
  statement: K.relIndex (H ⊔ K) = K.relIndex H
  proof: Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm

@[to_additive (attr := simp)]

中文:
定理 relIndex_sup_right
  条件: [K.正规]
  结论: K.relIndex (H ⊔ K) = K.relIndex H
  证明: Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.card_congr, QuotientGroup, QuotientGroup.quotientInfEquivProdNormalQuotient, card_congr, quotientInfEquivProdNormalQuotient, toEquiv, toEquiv.symm
-/
theorem relIndex_sup_right [K.Normal] : K.relIndex (H ⊔ K) = K.relIndex H :=
  Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm

@[to_additive (attr := simp)]
/--
theorem `relIndex_sup_left` / 定理 `relIndex_sup_left`

English:
theorem relIndex_sup_left
  given: [K.Normal]
  statement: K.relIndex (K ⊔ H) = K.relIndex H
  proof: by
  rw [sup_comm]; rw [relIndex_sup_right]

@[to_additive]

中文:
定理 relIndex_sup_left
  条件: [K.正规]
  结论: K.relIndex (K ⊔ H) = K.relIndex H
  证明: by
  rw [sup_comm]; rw [relIndex_sup_right]

@[to_additive]

Depends on / 依赖: relIndex_sup_right, sup_comm
-/
theorem relIndex_sup_left [K.Normal] : K.relIndex (K ⊔ H) = K.relIndex H := by
  rw [sup_comm]; rw [relIndex_sup_right]

@[to_additive]
/--
theorem `relIndex_dvd_index_of_normal` / 定理 `relIndex_dvd_index_of_normal`

English:
theorem relIndex_dvd_index_of_normal
  given: [H.Normal]
  statement: H.relIndex K ∣ H.index
  proof: relIndex_sup_right K H ▸ relIndex_dvd_index_of_le le_sup_right

中文:
定理 relIndex_dvd_index_of_normal
  条件: [H.正规]
  结论: H.relIndex K ∣ H.index
  证明: relIndex_sup_right K H ▸ relIndex_dvd_index_of_le le_sup_right

Depends on / 依赖: le_sup_right, relIndex_dvd_index_of_le, relIndex_sup_right
-/
theorem relIndex_dvd_index_of_normal [H.Normal] : H.relIndex K ∣ H.index :=
  relIndex_sup_right K H ▸ relIndex_dvd_index_of_le le_sup_right

variable {H K}

@[to_additive]
/--
theorem `relIndex_dvd_of_le_left` / 定理 `relIndex_dvd_of_le_left`

English:
theorem relIndex_dvd_of_le_left
  given: (hHK : H <= K)
  statement: K.relIndex L ∣ H.relIndex L
  proof: inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relIndex_inf_mul_relIndex _ _ _)

中文:
定理 relIndex_dvd_of_le_left
  条件: (hHK : H <= K)
  结论: K.relIndex L ∣ H.relIndex L
  证明: inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relIndex_inf_mul_relIndex _ _ _)

Depends on / 依赖: dvd_of_mul_left_eq, inf_of_le_left, relIndex_inf_mul_relIndex
-/
theorem relIndex_dvd_of_le_left (hHK : H <= K) : K.relIndex L ∣ H.relIndex L :=
  inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relIndex_inf_mul_relIndex _ _ _)

/-- A subgroup has index two if and only if there exists `a` such that for all `b`, exactly one
of `b * a` and `b` belong to `H`. -/
@[to_additive /-- An additive subgroup has index two if and only if there exists `a` such that
for all `b`, exactly one of `b + a` and `b` belong to `H`. -/]
/--
theorem `index_eq_two_iff` / 定理 `index_eq_two_iff`

English:
theorem index_eq_two_iff
  statement: H.index = 2 ↔ exists a, forall b, Xor (b * a in H) (b in H)
  proof: by
  simp only [index, Nat.card_eq_two_iff' ((1 : G) : G ⧸ H), ExistsUnique, inv_mem_iff,
    QuotientGroup.exists_mk, QuotientGroup.forall_mk, Ne, QuotientGroup.eq, mul_one,
    xor_iff_iff_not]
  refine exists_congr fun a =>
    ⟨fun ha b => ⟨fun hba hb => ?_, fun hb => ?_⟩, fun ha => ⟨?_, fun b h

中文:
定理 index_eq_two_iff
  结论: H.index = 2 ↔ 存在 a, 对任意 b, Xor (b * a in H) (b in H)
  证明: by
  simp only [index, Nat.card_eq_two_iff' ((1 : G) : G ⧸ H), ExistsUnique, inv_mem_iff,
    QuotientGroup.exists_mk, QuotientGroup.forall_mk, Ne, QuotientGroup.eq, mul_one,
    xor_iff_iff_not]
  refine exists_congr fun a =>
    ⟨fun ha b => ⟨fun hba hb => ?_, fun hb => ?_⟩, fun ha => ⟨?_, fun b h

Depends on / 依赖: ExistsUnique, Nat.card_eq_two_iff, QuotientGroup, QuotientGroup.eq, QuotientGroup.exists_mk, QuotientGroup.forall_mk, card_eq_two_iff, exists_congr, exists_mk, forall_mk, inv_inv, inv_mem_iff, inv_mul_cancel, mul_mem_cancel_left, mul_one, one_mem, xor_iff_iff_not
-/
theorem index_eq_two_iff : H.index = 2 ↔ exists a, forall b, Xor (b * a in H) (b in H) := by
  simp only [index, Nat.card_eq_two_iff' ((1 : G) : G ⧸ H), ExistsUnique, inv_mem_iff,
    QuotientGroup.exists_mk, QuotientGroup.forall_mk, Ne, QuotientGroup.eq, mul_one,
    xor_iff_iff_not]
  refine exists_congr fun a =>
    ⟨fun ha b => ⟨fun hba hb => ?_, fun hb => ?_⟩, fun ha => ⟨?_, fun b hb => ?_⟩⟩
  · exact ha.1 ((mul_mem_cancel_left hb).1 hba)
  · exact inv_inv b ▸ ha.2 _ (mt (inv_mem_iff (x := b)).1 hb)
  · rw [← inv_mem_iff (x := a), ← ha, inv_mul_cancel]
    exact one_mem _
  · rwa [ha, inv_mem_iff (x := b)]

/-- A subgroup has index two if and only if there exists `a` such that for all `b`, exactly one
of `a * b` and `b` belong to `H`. -/
@[to_additive /-- An additive subgroup has index two if and only if there exists `a` such that
for all `b`, exactly one of `a + b` and `b` belong to `H`. -/]
/--
theorem `index_eq_two_iff'` / 定理 `index_eq_two_iff'`

English:
theorem index_eq_two_iff'
  statement: H.index = 2 ↔ exists a, forall b, Xor (a * b in H) (b in H)
  proof: by
  rw [index_eq_two_iff]; rw [(Equiv.inv G).exists_congr]
  refine fun a => (Equiv.inv G).forall_congr fun b => ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

中文:
定理 index_eq_two_iff'
  结论: H.index = 2 ↔ 存在 a, 对任意 b, Xor (a * b in H) (b in H)
  证明: by
  rw [index_eq_two_iff]; rw [(Equiv.inv G).exists_congr]
  refine fun a => (Equiv.inv G).forall_congr fun b => ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

Depends on / 依赖: Equiv.inv, Equiv.inv_apply, exists_congr, forall_congr, index_eq_two_iff, inv_apply, inv_mem_iff, mul_inv_rev
-/
theorem index_eq_two_iff' : H.index = 2 ↔ exists a, forall b, Xor (a * b in H) (b in H) := by
  rw [index_eq_two_iff]; rw [(Equiv.inv G).exists_congr]
  refine fun a => (Equiv.inv G).forall_congr fun b => ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

/-- A subgroup `H` has index two if and only if there exists `a ∉ H` such that for all `b`, one
of `b * a` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup `H` has index two if and only if there exists `a ∉ H` such
that for all `b`, one of `b + a` and `b` belongs to `H`. -/]
/--
lemma `index_eq_two_iff_exists_notMem_and` / 引理 `index_eq_two_iff_exists_notMem_and`

English:
lemma index_eq_two_iff_exists_notMem_and
  proof: by
  simp only [index_eq_two_iff, xor_iff_or_and_not_and]
  exact exists_congr fun a => ⟨fun h => ⟨fun ha => ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b => (h b).1⟩,
    fun h b => ⟨h.2 b, fun h' => h.1 (by simpa using mul_mem (inv_mem h'.2) h'.1)⟩⟩

中文:
引理 index_eq_two_iff_存在_notMem_and
  证明: by
  simp only [index_eq_two_iff, xor_iff_or_and_not_and]
  exact exists_congr fun a => ⟨fun h => ⟨fun ha => ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b => (h b).1⟩,
    fun h b => ⟨h.2 b, fun h' => h.1 (by simpa using mul_mem (inv_mem h'.2) h'.1)⟩⟩

Depends on / 依赖: exists_congr, index_eq_two_iff, inv_mem, mul_mem, xor_iff_or_and_not_and
-/
lemma index_eq_two_iff_exists_notMem_and :
    H.index = 2 ↔ exists a, a ∉ H ∧ forall b, (b * a in H) ∨ (b in H) := by
  simp only [index_eq_two_iff, xor_iff_or_and_not_and]
  exact exists_congr fun a => ⟨fun h => ⟨fun ha => ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b => (h b).1⟩,
    fun h b => ⟨h.2 b, fun h' => h.1 (by simpa using mul_mem (inv_mem h'.2) h'.1)⟩⟩

/-- A subgroup `H` has index two if and only if there exists `a ∉ H` such that for all `b`, one
of `a * b` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup has index two if and only if there exists `a ∉ H` such that
for all `b`, one of `a + b` and `b` belongs to `H`. -/]
/--
lemma `index_eq_two_iff_exists_notMem_and'` / 引理 `index_eq_two_iff_exists_notMem_and'`

English:
lemma index_eq_two_iff_exists_notMem_and'
  proof: by
  simp only [index_eq_two_iff', xor_iff_or_and_not_and]
  exact exists_congr fun a => ⟨fun h => ⟨fun ha => ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b => (h b).1⟩,
    fun h b => ⟨h.2 b, fun h' => h.1 (by simpa using mul_mem h'.1 (inv_mem h'.2))⟩⟩

中文:
引理 index_eq_two_iff_存在_notMem_and'
  证明: by
  simp only [index_eq_two_iff', xor_iff_or_and_not_and]
  exact exists_congr fun a => ⟨fun h => ⟨fun ha => ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b => (h b).1⟩,
    fun h b => ⟨h.2 b, fun h' => h.1 (by simpa using mul_mem h'.1 (inv_mem h'.2))⟩⟩

Depends on / 依赖: exists_congr, index_eq_two_iff, inv_mem, mul_mem, xor_iff_or_and_not_and
-/
lemma index_eq_two_iff_exists_notMem_and' :
    H.index = 2 ↔ exists a, a ∉ H ∧ forall b, (a * b in H) ∨ (b in H) := by
  simp only [index_eq_two_iff', xor_iff_or_and_not_and]
  exact exists_congr fun a => ⟨fun h => ⟨fun ha => ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b => (h b).1⟩,
    fun h b => ⟨h.2 b, fun h' => h.1 (by simpa using mul_mem h'.1 (inv_mem h'.2))⟩⟩

/-- Relative version of `Subgroup.index_eq_two_iff`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff`. -/]
/--
theorem `relIndex_eq_two_iff` / 定理 `relIndex_eq_two_iff`

English:
theorem relIndex_eq_two_iff
  statement: H.relIndex K = 2 ↔ exists a in K, forall b in K, Xor (b * a in H) (b in H)
  proof: by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff, mem_subgroupOf]

中文:
定理 relIndex_eq_two_iff
  结论: H.relIndex K = 2 ↔ 存在 a in K, 对任意 b in K, Xor (b * a in H) (b in H)
  证明: by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff, mem_subgroupOf]

Depends on / 依赖: Subgroup, Subgroup.index_eq_two_iff, Subgroup.relIndex, index_eq_two_iff, mem_subgroupOf, relIndex
-/
theorem relIndex_eq_two_iff : H.relIndex K = 2 ↔ exists a in K, forall b in K, Xor (b * a in H) (b in H) := by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff, mem_subgroupOf]

/-- Relative version of `Subgroup.index_eq_two_iff'`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff'`. -/]
/--
theorem `relIindex_eq_two_iff'` / 定理 `relIindex_eq_two_iff'`

English:
theorem relIindex_eq_two_iff'
  statement: H.relIndex K = 2 ↔ exists a in K, forall b in K, Xor (a * b in H) (b in H)
  proof: by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff', mem_subgroupOf]

中文:
定理 relIindex_eq_two_iff'
  结论: H.relIndex K = 2 ↔ 存在 a in K, 对任意 b in K, Xor (a * b in H) (b in H)
  证明: by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff', mem_subgroupOf]

Depends on / 依赖: Subgroup, Subgroup.index_eq_two_iff, Subgroup.relIndex, index_eq_two_iff, mem_subgroupOf, relIndex
-/
theorem relIindex_eq_two_iff' : H.relIndex K = 2 ↔ exists a in K, forall b in K, Xor (a * b in H) (b in H) := by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff', mem_subgroupOf]

/-- Relative version of `Subgroup.index_eq_two_iff_exists_notMem_and`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff_exists_notMem_and`. -/]
/--
lemma `relIndex_eq_two_iff_exists_notMem_and` / 引理 `relIndex_eq_two_iff_exists_notMem_and`

English:
lemma relIndex_eq_two_iff_exists_notMem_and
  proof: by
  rw [Subgroup.relIndex]; rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g => ?_
  simp only [and_left_comm]

中文:
引理 relIndex_eq_two_iff_存在_notMem_and
  证明: by
  rw [Subgroup.relIndex]; rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g => ?_
  simp only [and_left_comm]

Depends on / 依赖: Subgroup, Subgroup.index_eq_two_iff_exists_notMem_and, Subgroup.relIndex, Subtype, Subtype.exists, Subtype.forall, and_left_comm, coe_mul, exists_and_left, exists_congr, exists_prop, index_eq_two_iff_exists_notMem_and, mem_subgroupOf, relIndex
-/
lemma relIndex_eq_two_iff_exists_notMem_and :
    H.relIndex K = 2 ↔ exists a in K, a ∉ H ∧ forall b in K, (b * a in H) ∨ (b in H) := by
  rw [Subgroup.relIndex]; rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g => ?_
  simp only [and_left_comm]

/-- Relative version of `Subgroup.index_eq_two_iff_exists_notMem_and'`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff_exists_notMem_and'`. -/]
/--
lemma `relIndex_eq_two_iff_exists_notMem_and'` / 引理 `relIndex_eq_two_iff_exists_notMem_and'`

English:
lemma relIndex_eq_two_iff_exists_notMem_and'
  proof: by
  rw [Subgroup.relIndex]; rw [Subgroup.index_eq_two_iff_exists_notMem_and']
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g => ?_
  simp only [and_left_comm]

@[to_additive]

中文:
引理 relIndex_eq_two_iff_存在_notMem_and'
  证明: by
  rw [Subgroup.relIndex]; rw [Subgroup.index_eq_two_iff_exists_notMem_and']
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g => ?_
  simp only [and_left_comm]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.index_eq_two_iff_exists_notMem_and, Subgroup.relIndex, Subtype, Subtype.exists, Subtype.forall, and_left_comm, coe_mul, exists_and_left, exists_congr, exists_prop, index_eq_two_iff_exists_notMem_and, mem_subgroupOf, relIndex
-/
lemma relIndex_eq_two_iff_exists_notMem_and' :
    H.relIndex K = 2 ↔ exists a in K, a ∉ H ∧ forall b in K, (a * b in H) ∨ (b in H) := by
  rw [Subgroup.relIndex]; rw [Subgroup.index_eq_two_iff_exists_notMem_and']
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g => ?_
  simp only [and_left_comm]

@[to_additive]
/--
theorem `mul_mem_iff_of_index_two` / 定理 `mul_mem_iff_of_index_two`

English:
theorem mul_mem_iff_of_index_two
  given: (h : H.index = 2) {a b : G}
  statement: a * b in H ↔ (a in H ↔ b in H)
  proof: by
  by_cases ha : a in H; · simp only [ha, true_iff, mul_mem_cancel_left ha]
  by_cases hb : b in H; · simp only [hb, iff_true, mul_mem_cancel_right hb]
  simp only [ha, hb, iff_true]
  rcases index_eq_two_iff.1 h with ⟨c, hc⟩
  refine (hc _).or.resolve_left ?_
  rwa [mul_assoc, mul_mem_cancel_righ

中文:
定理 mul_mem_iff_of_index_two
  条件: (h : H.index = 2) {a b : G}
  结论: a * b in H ↔ (a in H ↔ b in H)
  证明: by
  by_cases ha : a in H; · simp only [ha, true_iff, mul_mem_cancel_left ha]
  by_cases hb : b in H; · simp only [hb, iff_true, mul_mem_cancel_right hb]
  simp only [ha, hb, iff_true]
  rcases index_eq_two_iff.1 h with ⟨c, hc⟩
  refine (hc _).or.resolve_left ?_
  rwa [mul_assoc, mul_mem_cancel_righ

Depends on / 依赖: iff_true, index_eq_two_iff, mul_assoc, mul_mem_cancel_left, mul_mem_cancel_right, or.resolve_left, or.resolve_right, resolve_left, resolve_right, true_iff
-/
theorem mul_mem_iff_of_index_two (h : H.index = 2) {a b : G} : a * b in H ↔ (a in H ↔ b in H) := by
  by_cases ha : a in H; · simp only [ha, true_iff, mul_mem_cancel_left ha]
  by_cases hb : b in H; · simp only [hb, iff_true, mul_mem_cancel_right hb]
  simp only [ha, hb, iff_true]
  rcases index_eq_two_iff.1 h with ⟨c, hc⟩
  refine (hc _).or.resolve_left ?_
  rwa [mul_assoc, mul_mem_cancel_right ((hc _).or.resolve_right hb)]

@[to_additive]
/--
theorem `mul_self_mem_of_index_two` / 定理 `mul_self_mem_of_index_two`

English:
theorem mul_self_mem_of_index_two
  given: (h : H.index = 2) (a : G)
  statement: a * a in H
  proof: by
  rw [mul_mem_iff_of_index_two h]

@[to_additive two_smul_mem_of_index_two]

中文:
定理 mul_self_mem_of_index_two
  条件: (h : H.index = 2) (a : G)
  结论: a * a in H
  证明: by
  rw [mul_mem_iff_of_index_two h]

@[to_additive two_smul_mem_of_index_two]

Depends on / 依赖: mul_mem_iff_of_index_two
-/
theorem mul_self_mem_of_index_two (h : H.index = 2) (a : G) : a * a in H := by
  rw [mul_mem_iff_of_index_two h]

@[to_additive two_smul_mem_of_index_two]
/--
theorem `sq_mem_of_index_two` / 定理 `sq_mem_of_index_two`

English:
theorem sq_mem_of_index_two
  given: (h : H.index = 2) (a : G)
  statement: a ^ 2 in H
  proof: (pow_two a).symm ▸ mul_self_mem_of_index_two h a

中文:
定理 sq_mem_of_index_two
  条件: (h : H.index = 2) (a : G)
  结论: a ^ 2 in H
  证明: (pow_two a).symm ▸ mul_self_mem_of_index_two h a

Depends on / 依赖: mul_self_mem_of_index_two, pow_two
-/
theorem sq_mem_of_index_two (h : H.index = 2) (a : G) : a ^ 2 in H :=
  (pow_two a).symm ▸ mul_self_mem_of_index_two h a

variable (H K) {f : G ->* G'}

@[to_additive (attr := simp)]
/--
theorem `index_top` / 定理 `index_top`

English:
theorem index_top
  statement: (⊤ : Subgroup G).index = 1
  proof: Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[to_additive (attr := simp)]

中文:
定理 index_top
  结论: (⊤ : 子群 G).index = 1
  证明: Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.card_eq_one_iff_unique.mpr, QuotientGroup, QuotientGroup.subsingleton_quotient_top, card_eq_one_iff_unique, subsingleton_quotient_top
-/
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[to_additive (attr := simp)]
/--
theorem `index_bot` / 定理 `index_bot`

English:
theorem index_bot
  statement: (⊥ : Subgroup G).index = Nat.card G
  proof: Nat.card_congr QuotientGroup.quotientBot.toEquiv

@[to_additive (attr := simp)]

中文:
定理 index_bot
  结论: (⊥ : 子群 G).index = 自然数.card G
  证明: Nat.card_congr QuotientGroup.quotientBot.toEquiv

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.card_congr, QuotientGroup, QuotientGroup.quotientBot.toEquiv, card_congr, quotientBot, toEquiv
-/
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Nat.card_congr QuotientGroup.quotientBot.toEquiv

@[to_additive (attr := simp)]
/--
theorem `relIndex_top_left` / 定理 `relIndex_top_left`

English:
theorem relIndex_top_left
  statement: (⊤ : Subgroup G).relIndex H = 1
  proof: index_top

@[to_additive (attr := simp)]

中文:
定理 relIndex_top_left
  结论: (⊤ : 子群 G).relIndex H = 1
  证明: index_top

@[to_additive (attr := simp)]

Depends on / 依赖: index_top
-/
theorem relIndex_top_left : (⊤ : Subgroup G).relIndex H = 1 :=
  index_top

@[to_additive (attr := simp)]
/--
theorem `relIndex_top_right` / 定理 `relIndex_top_right`

English:
theorem relIndex_top_right
  statement: H.relIndex ⊤ = H.index
  proof: by
  rw [← relIndex_mul_index (show H <= ⊤ from le_top)]; rw [index_top]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 relIndex_top_right
  结论: H.relIndex ⊤ = H.index
  证明: by
  rw [← relIndex_mul_index (show H <= ⊤ from le_top)]; rw [index_top]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: index_top, le_top, mul_one, relIndex_mul_index
-/
theorem relIndex_top_right : H.relIndex ⊤ = H.index := by
  rw [← relIndex_mul_index (show H <= ⊤ from le_top)]; rw [index_top]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `relIndex_bot_left` / 定理 `relIndex_bot_left`

English:
theorem relIndex_bot_left
  statement: (⊥ : Subgroup G).relIndex H = Nat.card H
  proof: by
  rw [relIndex]; rw [bot_subgroupOf]; rw [index_bot]

@[to_additive (attr := simp)]

中文:
定理 relIndex_bot_left
  结论: (⊥ : 子群 G).relIndex H = 自然数.card H
  证明: by
  rw [relIndex]; rw [bot_subgroupOf]; rw [index_bot]

@[to_additive (attr := simp)]

Depends on / 依赖: bot_subgroupOf, coreflection_apply_coroot, index_bot, map_sub, mul_comm, reflection_apply, relIndex
-/
theorem relIndex_bot_left : (⊥ : Subgroup G).relIndex H = Nat.card H := by
  rw [relIndex]; rw [bot_subgroupOf]; rw [index_bot]

@[to_additive (attr := simp)]
/--
theorem `relIndex_bot_right` / 定理 `relIndex_bot_right`

English:
theorem relIndex_bot_right
  statement: H.relIndex ⊥ = 1
  proof: by rw [relIndex, subgroupOf_bot_eq_top, index_top]

@[to_additive (attr := simp)]

中文:
定理 relIndex_bot_right
  结论: H.relIndex ⊥ = 1
  证明: by rw [relIndex, subgroupOf_bot_eq_top, index_top]

@[to_additive (attr := simp)]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, P.coroot, _reflectionPerm, congr_fun, coroot, index_top, relIndex, subgroupOf_bot_eq_top
-/
theorem relIndex_bot_right : H.relIndex ⊥ = 1 := by rw [relIndex, subgroupOf_bot_eq_top, index_top]

@[to_additive (attr := simp)]
/--
theorem `relIndex_self` / 定理 `relIndex_self`

English:
theorem relIndex_self
  statement: H.relIndex H = 1
  proof: by rw [relIndex, subgroupOf_self, index_top]

@[to_additive]

中文:
定理 relIndex_self
  结论: H.relIndex H = 1
  证明: by rw [relIndex, subgroupOf_self, index_top]

@[to_additive]

Depends on / 依赖: index_top, relIndex, subgroupOf_self
-/
theorem relIndex_self : H.relIndex H = 1 := by rw [relIndex, subgroupOf_self, index_top]

@[to_additive]
/--
theorem `index_ker` / 定理 `index_ker`

English:
theorem index_ker
  given: (f : G ->* G')
  statement: f.ker.index = Nat.card f.range
  proof: by
  rw [← MonoidHom.comap_bot]; rw [index_comap]; rw [relIndex_bot_left]

@[to_additive]

中文:
定理 index_ker
  条件: (f : G ->* G')
  结论: f.ker.index = 自然数.card f.range
  证明: by
  rw [← MonoidHom.comap_bot]; rw [index_comap]; rw [relIndex_bot_left]

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.comap_bot, comap_bot, index_comap, relIndex_bot_left
-/
theorem index_ker (f : G ->* G') : f.ker.index = Nat.card f.range := by
  rw [← MonoidHom.comap_bot]; rw [index_comap]; rw [relIndex_bot_left]

@[to_additive]
/--
theorem `relIndex_ker` / 定理 `relIndex_ker`

English:
theorem relIndex_ker
  given: (f : G ->* G')
  statement: f.ker.relIndex K = Nat.card (K.map f)
  proof: by
  rw [← MonoidHom.comap_bot]; rw [relIndex_comap]; rw [relIndex_bot_left]

@[to_additive (attr := simp) card_mul_index]

中文:
定理 relIndex_ker
  条件: (f : G ->* G')
  结论: f.ker.relIndex K = 自然数.card (K.map f)
  证明: by
  rw [← MonoidHom.comap_bot]; rw [relIndex_comap]; rw [relIndex_bot_left]

@[to_additive (attr := simp) card_mul_index]

Depends on / 依赖: MonoidHom, MonoidHom.comap_bot, comap_bot, relIndex_bot_left, relIndex_comap
-/
theorem relIndex_ker (f : G ->* G') : f.ker.relIndex K = Nat.card (K.map f) := by
  rw [← MonoidHom.comap_bot]; rw [relIndex_comap]; rw [relIndex_bot_left]

@[to_additive (attr := simp) card_mul_index]
/--
theorem `card_mul_index` / 定理 `card_mul_index`

English:
theorem card_mul_index
  statement: Nat.card H * H.index = Nat.card G
  proof: by
  rw [← relIndex_bot_left]; rw [← index_bot]
  exact relIndex_mul_index bot_le

@[to_additive]

中文:
定理 card_mul_index
  结论: 自然数.card H * H.index = 自然数.card G
  证明: by
  rw [← relIndex_bot_left]; rw [← index_bot]
  exact relIndex_mul_index bot_le

@[to_additive]

Depends on / 依赖: bot_le, index_bot, relIndex_bot_left, relIndex_mul_index
-/
theorem card_mul_index : Nat.card H * H.index = Nat.card G := by
  rw [← relIndex_bot_left]; rw [← index_bot]
  exact relIndex_mul_index bot_le

@[to_additive]
/--
theorem `card_dvd_of_surjective` / 定理 `card_dvd_of_surjective`

English:
theorem card_dvd_of_surjective
  given: (f : G ->* G') (hf : Function.Surjective f)
  proof: by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index

@[to_additive]

中文:
定理 card_dvd_of_surjective
  条件: (f : G ->* G') (hf : 函数.满射 f)
  证明: by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index

@[to_additive]

Depends on / 依赖: Dvd.intro_left, Nat.card, Nat.card_congr, QuotientGroup, QuotientGroup.quotientKerEquivOfSurjective, card_congr, card_mul_index, f.ker, f.ker.card_mul_index, intro_left, quotientKerEquivOfSurjective, toEquiv
-/
theorem card_dvd_of_surjective (f : G ->* G') (hf : Function.Surjective f) :
    Nat.card G' ∣ Nat.card G := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index

@[to_additive]
/--
theorem `card_range_dvd` / 定理 `card_range_dvd`

English:
theorem card_range_dvd
  given: (f : G ->* G')
  statement: Nat.card f.range ∣ Nat.card G
  proof: card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]

中文:
定理 card_range_dvd
  条件: (f : G ->* G')
  结论: 自然数.card f.range ∣ 自然数.card G
  证明: card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]

Depends on / 依赖: card_dvd_of_surjective, f.rangeRestrict, f.rangeRestrict_surjective, rangeRestrict, rangeRestrict_surjective
-/
theorem card_range_dvd (f : G ->* G') : Nat.card f.range ∣ Nat.card G :=
  card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]
/--
theorem `card_map_dvd` / 定理 `card_map_dvd`

English:
theorem card_map_dvd
  given: (f : G ->* G')
  statement: Nat.card (H.map f) ∣ Nat.card H
  proof: card_dvd_of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

@[to_additive]

中文:
定理 card_map_dvd
  条件: (f : G ->* G')
  结论: 自然数.card (H.map f) ∣ 自然数.card H
  证明: card_dvd_of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

@[to_additive]

Depends on / 依赖: card_dvd_of_surjective, f.subgroupMap, f.subgroupMap_surjective, subgroupMap, subgroupMap_surjective
-/
theorem card_map_dvd (f : G ->* G') : Nat.card (H.map f) ∣ Nat.card H :=
  card_dvd_of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

@[to_additive]
/--
theorem `index_map` / 定理 `index_map`

English:
theorem index_map
  given: (f : G ->* G')
  proof: by
  rw [← comap_map_eq]; rw [index_comap]; rw [relIndex_mul_index (H.map_le_range f)]

@[to_additive]

中文:
定理 index_map
  条件: (f : G ->* G')
  证明: by
  rw [← comap_map_eq]; rw [index_comap]; rw [relIndex_mul_index (H.map_le_range f)]

@[to_additive]

Depends on / 依赖: H.map_le_range, comap_map_eq, index_comap, map_le_range, relIndex_mul_index
-/
theorem index_map (f : G ->* G') :
    (H.map f).index = (H ⊔ f.ker).index * f.range.index := by
  rw [← comap_map_eq]; rw [index_comap]; rw [relIndex_mul_index (H.map_le_range f)]

@[to_additive]
/--
theorem `index_map_dvd` / 定理 `index_map_dvd`

English:
theorem index_map_dvd
  given: {f : G ->* G'} (hf : Function.Surjective f)
  proof: by
  rw [index_map]; rw [f.range_eq_top_of_surjective hf]; rw [index_top]; rw [mul_one]
  exact index_dvd_of_le le_sup_left

@[to_additive]

中文:
定理 index_map_dvd
  条件: {f : G ->* G'} (hf : 函数.满射 f)
  证明: by
  rw [index_map]; rw [f.range_eq_top_of_surjective hf]; rw [index_top]; rw [mul_one]
  exact index_dvd_of_le le_sup_left

@[to_additive]

Depends on / 依赖: f.range_eq_top_of_surjective, index_dvd_of_le, index_map, index_top, le_sup_left, mul_one, range_eq_top_of_surjective
-/
theorem index_map_dvd {f : G ->* G'} (hf : Function.Surjective f) :
    (H.map f).index ∣ H.index := by
  rw [index_map]; rw [f.range_eq_top_of_surjective hf]; rw [index_top]; rw [mul_one]
  exact index_dvd_of_le le_sup_left

@[to_additive]
/--
theorem `dvd_index_map` / 定理 `dvd_index_map`

English:
theorem dvd_index_map
  given: {f : G ->* G'} (hf : f.ker <= H)
  proof: by
  rw [index_map]; rw [sup_of_le_left hf]
  apply dvd_mul_right

@[to_additive]

中文:
定理 dvd_index_map
  条件: {f : G ->* G'} (hf : f.ker <= H)
  证明: by
  rw [index_map]; rw [sup_of_le_left hf]
  apply dvd_mul_right

@[to_additive]

Depends on / 依赖: dvd_mul_right, index_map, sup_of_le_left
-/
theorem dvd_index_map {f : G ->* G'} (hf : f.ker <= H) :
    H.index ∣ (H.map f).index := by
  rw [index_map]; rw [sup_of_le_left hf]
  apply dvd_mul_right

@[to_additive]
/--
theorem `index_map_eq` / 定理 `index_map_eq`

English:
theorem index_map_eq
  given: (hf1 : Surjective f) (hf2 : f.ker <= H)
  statement: (H.map f).index = H.index
  proof: Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive]

中文:
定理 index_map_eq
  条件: (hf1 : 满射 f) (hf2 : f.ker <= H)
  结论: (H.map f).index = H.index
  证明: Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive]

Depends on / 依赖: H.dvd_index_map, H.index_map_dvd, Nat.dvd_antisymm, dvd_antisymm, dvd_index_map, index_map_dvd
-/
theorem index_map_eq (hf1 : Surjective f) (hf2 : f.ker <= H) : (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive]
/--
lemma `index_map_of_bijective` / 引理 `index_map_of_bijective`

English:
lemma index_map_of_bijective
  given: (hf : Bijective f) (H : Subgroup G)
  statement: (H.map f).index = H.index
  proof: index_map_eq _ hf.2 (by rw [f.ker_eq_bot hf.1]; exact bot_le)

@[to_additive (attr := simp)]

中文:
引理 index_map_of_bijective
  条件: (hf : 双射 f) (H : 子群 G)
  结论: (H.map f).index = H.index
  证明: index_map_eq _ hf.2 (by rw [f.ker_eq_bot hf.1]; exact bot_le)

@[to_additive (attr := simp)]

Depends on / 依赖: bot_le, f.ker_eq_bot, index_map_eq, ker_eq_bot
-/
lemma index_map_of_bijective (hf : Bijective f) (H : Subgroup G) : (H.map f).index = H.index :=
  index_map_eq _ hf.2 (by rw [f.ker_eq_bot hf.1]; exact bot_le)

@[to_additive (attr := simp)]
/--
theorem `index_map_equiv` / 定理 `index_map_equiv`

English:
theorem index_map_equiv
  given: (e : G ≃* G')
  statement: (map (e : G ->* G') H).index = H.index
  proof: index_map_of_bijective e.bijective H

@[to_additive]

中文:
定理 index_map_equiv
  条件: (e : G ≃* G')
  结论: (map (e : G ->* G') H).index = H.index
  证明: index_map_of_bijective e.bijective H

@[to_additive]

Depends on / 依赖: bijective, e.bijective, index_map_of_bijective
-/
theorem index_map_equiv (e : G ≃* G') : (map (e : G ->* G') H).index = H.index :=
  index_map_of_bijective e.bijective H

@[to_additive]
/--
theorem `index_map_of_injective` / 定理 `index_map_of_injective`

English:
theorem index_map_of_injective
  given: {f : G ->* G'} (hf : Function.Injective f)
  proof: by
  rw [H.index_map]; rw [f.ker_eq_bot hf]; rw [sup_bot_eq]

@[to_additive]

中文:
定理 index_map_of_injective
  条件: {f : G ->* G'} (hf : 函数.单射 f)
  证明: by
  rw [H.index_map]; rw [f.ker_eq_bot hf]; rw [sup_bot_eq]

@[to_additive]

Depends on / 依赖: H.index_map, f.ker_eq_bot, index_map, ker_eq_bot, sup_bot_eq
-/
theorem index_map_of_injective {f : G ->* G'} (hf : Function.Injective f) :
    (H.map f).index = H.index * f.range.index := by
  rw [H.index_map]; rw [f.ker_eq_bot hf]; rw [sup_bot_eq]

@[to_additive]
/--
theorem `index_map_subtype` / 定理 `index_map_subtype`

English:
theorem index_map_subtype
  given: {H : Subgroup G} (K : Subgroup H)
  proof: by
  rw [K.index_map_of_injective H.subtype_injective]; rw [H.range_subtype]

@[to_additive]

中文:
定理 index_map_subtype
  条件: {H : 子群 G} (K : 子群 H)
  证明: by
  rw [K.index_map_of_injective H.subtype_injective]; rw [H.range_subtype]

@[to_additive]

Depends on / 依赖: H.range_subtype, H.subtype_injective, K.index_map_of_injective, index_map_of_injective, range_subtype, subtype_injective
-/
theorem index_map_subtype {H : Subgroup G} (K : Subgroup H) :
    (K.map H.subtype).index = K.index * H.index := by
  rw [K.index_map_of_injective H.subtype_injective]; rw [H.range_subtype]

@[to_additive]
/--
theorem `index_eq_card` / 定理 `index_eq_card`

English:
theorem index_eq_card
  statement: H.index = Nat.card (G ⧸ H)
  proof: rfl

@[to_additive index_mul_card]

中文:
定理 index_eq_card
  结论: H.index = 自然数.card (G ⧸ H)
  证明: rfl

@[to_additive index_mul_card]
-/
theorem index_eq_card : H.index = Nat.card (G ⧸ H) :=
  rfl

@[to_additive index_mul_card]
/--
theorem `index_mul_card` / 定理 `index_mul_card`

English:
theorem index_mul_card
  statement: H.index * Nat.card H = Nat.card G
  proof: by
  rw [mul_comm]; rw [card_mul_index]

@[to_additive]

中文:
定理 index_mul_card
  结论: H.index * 自然数.card H = 自然数.card G
  证明: by
  rw [mul_comm]; rw [card_mul_index]

@[to_additive]

Depends on / 依赖: card_mul_index, mul_comm
-/
theorem index_mul_card : H.index * Nat.card H = Nat.card G := by
  rw [mul_comm]; rw [card_mul_index]

@[to_additive]
/--
theorem `index_dvd_card` / 定理 `index_dvd_card`

English:
theorem index_dvd_card
  statement: H.index ∣ Nat.card G
  proof: ⟨Nat.card H, H.index_mul_card.symm⟩

@[to_additive]

中文:
定理 index_dvd_card
  结论: H.index ∣ 自然数.card G
  证明: ⟨Nat.card H, H.index_mul_card.symm⟩

@[to_additive]

Depends on / 依赖: H.index_mul_card.symm, Nat.card, index_mul_card
-/
theorem index_dvd_card : H.index ∣ Nat.card G :=
  ⟨Nat.card H, H.index_mul_card.symm⟩

@[to_additive]
/--
theorem `relIndex_dvd_card` / 定理 `relIndex_dvd_card`

English:
theorem relIndex_dvd_card
  statement: H.relIndex K ∣ Nat.card K
  proof: (H.subgroupOf K).index_dvd_card

中文:
定理 relIndex_dvd_card
  结论: H.relIndex K ∣ 自然数.card K
  证明: (H.subgroupOf K).index_dvd_card

Depends on / 依赖: H.subgroupOf, index_dvd_card, subgroupOf
-/
theorem relIndex_dvd_card : H.relIndex K ∣ Nat.card K :=
  (H.subgroupOf K).index_dvd_card

variable {H K L}

@[to_additive]
/--
theorem `relIndex_eq_zero_of_le_left` / 定理 `relIndex_eq_zero_of_le_left`

English:
theorem relIndex_eq_zero_of_le_left
  given: (hHK : H <= K) (hKL : K.relIndex L = 0)
  statement: H.relIndex L = 0
  proof: eq_zero_of_zero_dvd (hKL ▸ relIndex_dvd_of_le_left L hHK)

@[to_additive]

中文:
定理 relIndex_eq_zero_of_le_left
  条件: (hHK : H <= K) (hKL : K.relIndex L = 0)
  结论: H.relIndex L = 0
  证明: eq_zero_of_zero_dvd (hKL ▸ relIndex_dvd_of_le_left L hHK)

@[to_additive]

Depends on / 依赖: eq_zero_of_zero_dvd, relIndex_dvd_of_le_left
-/
theorem relIndex_eq_zero_of_le_left (hHK : H <= K) (hKL : K.relIndex L = 0) : H.relIndex L = 0 :=
  eq_zero_of_zero_dvd (hKL ▸ relIndex_dvd_of_le_left L hHK)

@[to_additive]
/--
theorem `relIndex_eq_zero_of_le_right` / 定理 `relIndex_eq_zero_of_le_right`

English:
theorem relIndex_eq_zero_of_le_right
  given: (hKL : K <= L) (hHK : H.relIndex K = 0)
  statement: H.relIndex L = 0
  proof: Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLE H hKL) hHK

中文:
定理 relIndex_eq_zero_of_le_right
  条件: (hKL : K <= L) (hHK : H.relIndex K = 0)
  结论: H.relIndex L = 0
  证明: Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLE H hKL) hHK

Depends on / 依赖: Finite, Finite.card_eq_zero_of_embedding, card_eq_zero_of_embedding, quotientSubgroupOfEmbeddingOfLE
-/
theorem relIndex_eq_zero_of_le_right (hKL : K <= L) (hHK : H.relIndex K = 0) : H.relIndex L = 0 :=
  Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLE H hKL) hHK

/-- If `J` has finite index in `K`, then the same holds for their comaps under any group hom. -/
@[to_additive /-- If `J` has finite index in `K`, then the same holds for their comaps under any
additive group hom. -/]
/--
lemma `relIndex_comap_ne_zero` / 引理 `relIndex_comap_ne_zero`

English:
lemma relIndex_comap_ne_zero
  given: (f : G ->* G') {J K : Subgroup G'} (hJK : J.relIndex K != 0)
  proof: by
  rw [relIndex_comap]
exact fun h => hJK relIndex_eq_zero_of_le_right (map_comap_le _ _) h

@[to_additive]

中文:
引理 relIndex_comap_ne_zero
  条件: (f : G ->* G') {J K : 子群 G'} (hJK : J.relIndex K != 0)
  证明: by
  rw [relIndex_comap]
exact fun h => hJK relIndex_eq_zero_of_le_right (map_comap_le _ _) h

@[to_additive]

Depends on / 依赖: map_comap_le, relIndex_comap, relIndex_eq_zero_of_le_right
-/
lemma relIndex_comap_ne_zero (f : G ->* G') {J K : Subgroup G'} (hJK : J.relIndex K != 0) :
    (J.comap f).relIndex (K.comap f) != 0 := by
  rw [relIndex_comap]
exact fun h => hJK relIndex_eq_zero_of_le_right (map_comap_le _ _) h

@[to_additive]
/--
theorem `index_eq_zero_of_relIndex_eq_zero` / 定理 `index_eq_zero_of_relIndex_eq_zero`

English:
theorem index_eq_zero_of_relIndex_eq_zero
  given: (h : H.relIndex K = 0)
  statement: H.index = 0
  proof: H.relIndex_top_right.symm.trans (relIndex_eq_zero_of_le_right le_top h)

@[to_additive]

中文:
定理 index_eq_zero_of_relIndex_eq_zero
  条件: (h : H.relIndex K = 0)
  结论: H.index = 0
  证明: H.relIndex_top_right.symm.trans (relIndex_eq_zero_of_le_right le_top h)

@[to_additive]

Depends on / 依赖: H.relIndex_top_right.symm.trans, le_top, relIndex_eq_zero_of_le_right, relIndex_top_right
-/
theorem index_eq_zero_of_relIndex_eq_zero (h : H.relIndex K = 0) : H.index = 0 :=
  H.relIndex_top_right.symm.trans (relIndex_eq_zero_of_le_right le_top h)

@[to_additive]
/--
theorem `relIndex_le_of_le_left` / 定理 `relIndex_le_of_le_left`

English:
theorem relIndex_le_of_le_left
  given: (hHK : H <= K) (hHL : H.relIndex L != 0)
  proof: Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relIndex_dvd_of_le_left L hHK)

@[to_additive]

中文:
定理 relIndex_le_of_le_left
  条件: (hHK : H <= K) (hHL : H.relIndex L != 0)
  证明: Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relIndex_dvd_of_le_left L hHK)

@[to_additive]

Depends on / 依赖: Nat.le_of_dvd, Nat.pos_of_ne_zero, le_of_dvd, pos_of_ne_zero, relIndex_dvd_of_le_left
-/
theorem relIndex_le_of_le_left (hHK : H <= K) (hHL : H.relIndex L != 0) :
    K.relIndex L <= H.relIndex L :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relIndex_dvd_of_le_left L hHK)

@[to_additive]
/--
theorem `relIndex_le_of_le_right` / 定理 `relIndex_le_of_le_right`

English:
theorem relIndex_le_of_le_right
  given: (hKL : K <= L) (hHL : H.relIndex L != 0)
  proof: Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLE H hKL) fun h => (hHL h).elim

@[to_additive]

中文:
定理 relIndex_le_of_le_right
  条件: (hKL : K <= L) (hHL : H.relIndex L != 0)
  证明: Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLE H hKL) fun h => (hHL h).elim

@[to_additive]

Depends on / 依赖: Finite, Finite.card_le_of_embedding, card_le_of_embedding, quotientSubgroupOfEmbeddingOfLE
-/
theorem relIndex_le_of_le_right (hKL : K <= L) (hHL : H.relIndex L != 0) :
    H.relIndex K <= H.relIndex L :=
  Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLE H hKL) fun h => (hHL h).elim

@[to_additive]
/--
theorem `relIndex_ne_zero_trans` / 定理 `relIndex_ne_zero_trans`

English:
theorem relIndex_ne_zero_trans
  given: (hHK : H.relIndex K != 0) (hKL : K.relIndex L != 0)
  proof: fun h =>
  mul_ne_zero (mt (relIndex_eq_zero_of_le_right (show K ⊓ L <= K from inf_le_left)) hHK) hKL
    ((relIndex_inf_mul_relIndex H K L).trans (relIndex_eq_zero_of_le_left inf_le_left h))

@[to_additive]

中文:
定理 relIndex_ne_zero_trans
  条件: (hHK : H.relIndex K != 0) (hKL : K.relIndex L != 0)
  证明: fun h =>
  mul_ne_zero (mt (relIndex_eq_zero_of_le_right (show K ⊓ L <= K from inf_le_left)) hHK) hKL
    ((relIndex_inf_mul_relIndex H K L).trans (relIndex_eq_zero_of_le_left inf_le_left h))

@[to_additive]
-/
theorem relIndex_ne_zero_trans (hHK : H.relIndex K != 0) (hKL : K.relIndex L != 0) :
    H.relIndex L != 0 := fun h =>
  mul_ne_zero (mt (relIndex_eq_zero_of_le_right (show K ⊓ L <= K from inf_le_left)) hHK) hKL
    ((relIndex_inf_mul_relIndex H K L).trans (relIndex_eq_zero_of_le_left inf_le_left h))

@[to_additive]
/--
theorem `relIndex_inf_ne_zero` / 定理 `relIndex_inf_ne_zero`

English:
theorem relIndex_inf_ne_zero
  given: (hH : H.relIndex L != 0) (hK : K.relIndex L != 0)
  proof: by
  replace hH : H.relIndex (K ⊓ L) != 0 := mt (relIndex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relIndex_right] at hH hK ⊢
  rw [inf_assoc]
  exact relIndex_ne_zero_trans hH hK

@[to_additive]

中文:
定理 relIndex_inf_ne_zero
  条件: (hH : H.relIndex L != 0) (hK : K.relIndex L != 0)
  证明: by
  replace hH : H.relIndex (K ⊓ L) != 0 := mt (relIndex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relIndex_right] at hH hK ⊢
  rw [inf_assoc]
  exact relIndex_ne_zero_trans hH hK

@[to_additive]

Depends on / 依赖: H.relIndex, inf_assoc, inf_le_right, inf_relIndex_right, relIndex, relIndex_eq_zero_of_le_right, relIndex_ne_zero_trans, replace
-/
theorem relIndex_inf_ne_zero (hH : H.relIndex L != 0) (hK : K.relIndex L != 0) :
    (H ⊓ K).relIndex L != 0 := by
  replace hH : H.relIndex (K ⊓ L) != 0 := mt (relIndex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relIndex_right] at hH hK ⊢
  rw [inf_assoc]
  exact relIndex_ne_zero_trans hH hK

@[to_additive]
/--
theorem `index_inf_ne_zero` / 定理 `index_inf_ne_zero`

English:
theorem index_inf_ne_zero
  given: (hH : H.index != 0) (hK : K.index != 0)
  statement: (H ⊓ K).index != 0
  proof: by
  rw [← relIndex_top_right] at hH hK ⊢
  exact relIndex_inf_ne_zero hH hK

中文:
定理 index_inf_ne_zero
  条件: (hH : H.index != 0) (hK : K.index != 0)
  结论: (H ⊓ K).index != 0
  证明: by
  rw [← relIndex_top_right] at hH hK ⊢
  exact relIndex_inf_ne_zero hH hK

Depends on / 依赖: relIndex_inf_ne_zero, relIndex_top_right
-/
theorem index_inf_ne_zero (hH : H.index != 0) (hK : K.index != 0) : (H ⊓ K).index != 0 := by
  rw [← relIndex_top_right] at hH hK ⊢
  exact relIndex_inf_ne_zero hH hK

/-- If `J` has finite index in `K`, then `J ⊓ L` has finite index in `K ⊓ L` for any `L`. -/
@[to_additive /-- If `J` has finite index in `K`, then `J ⊓ L` has finite index in `K ⊓ L` for any
`L`. -/]
/--
lemma `relIndex_inter_ne_zero` / 引理 `relIndex_inter_ne_zero`

English:
lemma relIndex_inter_ne_zero
  given: {J K : Subgroup G} (hJK : J.relIndex K != 0) (L : Subgroup G)
  proof: by
  rw [← range_subtype L]; rw [inf_comm]; rw [← map_comap_eq]; rw [inf_comm]; rw [← map_comap_eq]; rw [← relIndex_comap]; rw [comap_map_eq_self_of_injective (subtype_injective L)]
  exact relIndex_comap_ne_zero _ hJK

@[to_additive]

中文:
引理 relIndex_inter_ne_zero
  条件: {J K : 子群 G} (hJK : J.relIndex K != 0) (L : 子群 G)
  证明: by
  rw [← range_subtype L]; rw [inf_comm]; rw [← map_comap_eq]; rw [inf_comm]; rw [← map_comap_eq]; rw [← relIndex_comap]; rw [comap_map_eq_self_of_injective (subtype_injective L)]
  exact relIndex_comap_ne_zero _ hJK

@[to_additive]

Depends on / 依赖: comap_map_eq_self_of_injective, inf_comm, map_comap_eq, range_subtype, relIndex_comap, relIndex_comap_ne_zero, subtype_injective
-/
lemma relIndex_inter_ne_zero {J K : Subgroup G} (hJK : J.relIndex K != 0) (L : Subgroup G) :
    (J ⊓ L).relIndex (K ⊓ L) != 0 := by
  rw [← range_subtype L]; rw [inf_comm]; rw [← map_comap_eq]; rw [inf_comm]; rw [← map_comap_eq]; rw [← relIndex_comap]; rw [comap_map_eq_self_of_injective (subtype_injective L)]
  exact relIndex_comap_ne_zero _ hJK

@[to_additive]
/--
theorem `relIndex_inf_le` / 定理 `relIndex_inf_le`

English:
theorem relIndex_inf_le
  statement: (H ⊓ K).relIndex L <= H.relIndex L * K.relIndex L
  proof: by
  by_cases h : H.relIndex L = 0
  · simp [relIndex_eq_zero_of_le_left inf_le_left h]
  rw [← inf_relIndex_right]; rw [inf_assoc]; rw [← relIndex_mul_relIndex _ _ L inf_le_right inf_le_right]; rw [inf_relIndex_right]; rw [inf_relIndex_right]
  grw [relIndex_le_of_le_right inf_le_right h]

@[to_add

中文:
定理 relIndex_inf_le
  结论: (H ⊓ K).relIndex L <= H.relIndex L * K.relIndex L
  证明: by
  by_cases h : H.relIndex L = 0
  · simp [relIndex_eq_zero_of_le_left inf_le_left h]
  rw [← inf_relIndex_right]; rw [inf_assoc]; rw [← relIndex_mul_relIndex _ _ L inf_le_right inf_le_right]; rw [inf_relIndex_right]; rw [inf_relIndex_right]
  grw [relIndex_le_of_le_right inf_le_right h]

@[to_add

Depends on / 依赖: H.relIndex, inf_assoc, inf_le_left, inf_le_right, inf_relIndex_right, relIndex, relIndex_eq_zero_of_le_left, relIndex_le_of_le_right, relIndex_mul_relIndex
-/
theorem relIndex_inf_le : (H ⊓ K).relIndex L <= H.relIndex L * K.relIndex L := by
  by_cases h : H.relIndex L = 0
  · simp [relIndex_eq_zero_of_le_left inf_le_left h]
  rw [← inf_relIndex_right]; rw [inf_assoc]; rw [← relIndex_mul_relIndex _ _ L inf_le_right inf_le_right]; rw [inf_relIndex_right]; rw [inf_relIndex_right]
  grw [relIndex_le_of_le_right inf_le_right h]

@[to_additive]
/--
theorem `index_inf_le` / 定理 `index_inf_le`

English:
theorem index_inf_le
  statement: (H ⊓ K).index <= H.index * K.index
  proof: by
  simp_rw [← relIndex_top_right, relIndex_inf_le]

@[to_additive]

中文:
定理 index_inf_le
  结论: (H ⊓ K).index <= H.index * K.index
  证明: by
  simp_rw [← relIndex_top_right, relIndex_inf_le]

@[to_additive]

Depends on / 依赖: relIndex_inf_le, relIndex_top_right, simp_rw
-/
theorem index_inf_le : (H ⊓ K).index <= H.index * K.index := by
  simp_rw [← relIndex_top_right, relIndex_inf_le]

@[to_additive]
/--
theorem `relIndex_iInf_ne_zero` / 定理 `relIndex_iInf_ne_zero`

English:
theorem relIndex_iInf_ne_zero
  statement: {ι : Type*} [_hι : Finite ι] {f : ι -> Subgroup G}
  proof: haveI := Fintype.ofFinite ι
  (Finset.prod_ne_zero_iff.mpr fun i _hi => hf i) ∘
    Nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotientiInfSubgroupOfEmbedding f L)

@[to_additive]

中文:
定理 relIndex_iInf_ne_zero
  结论: {ι : 类型} [_hι : 有限 ι] {f : ι -> 子群 G}
  证明: haveI := Fintype.ofFinite ι
  (Finset.prod_ne_zero_iff.mpr fun i _hi => hf i) ∘
    Nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotientiInfSubgroupOfEmbedding f L)

@[to_additive]

Depends on / 依赖: Finite, Finite.card_eq_zero_of_embedding, Finset, Finset.prod_ne_zero_iff.mpr, Fintype, Fintype.ofFinite, Nat.card_pi.symm.trans, card_eq_zero_of_embedding, card_pi, ofFinite, prod_ne_zero_iff, quotientiInfSubgroupOfEmbedding
-/
theorem relIndex_iInf_ne_zero {ι : Type*} [_hι : Finite ι] {f : ι -> Subgroup G}
    (hf : forall i, (f i).relIndex L != 0) : (⨅ i, f i).relIndex L != 0 :=
  haveI := Fintype.ofFinite ι
  (Finset.prod_ne_zero_iff.mpr fun i _hi => hf i) ∘
    Nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotientiInfSubgroupOfEmbedding f L)

@[to_additive]
/--
theorem `relIndex_iInf_le` / 定理 `relIndex_iInf_le`

English:
theorem relIndex_iInf_le
  given: {ι : Type*} [Fintype ι] (f : ι -> Subgroup G)
  proof: le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientiInfSubgroupOfEmbedding f L) fun h =>
      let ⟨i, _hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relIndex_eq_zero_of_le_left (iInf_le f i) h)
    Nat.card_pi

@[to_additive]

中文:
定理 relIndex_iInf_le
  条件: {ι : 类型} [有限类型 ι] (f : ι -> 子群 G)
  证明: le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientiInfSubgroupOfEmbedding f L) fun h =>
      let ⟨i, _hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relIndex_eq_zero_of_le_left (iInf_le f i) h)
    Nat.card_pi

@[to_additive]

Depends on / 依赖: Finite, Finite.card_le_of_embedding, Finset, Finset.prod_eq_zero_iff.mp, Nat.card_pi, Nat.card_pi.symm.trans, card_le_of_embedding, card_pi, iInf_le, le_of_le_of_eq, prod_eq_zero_iff, quotientiInfSubgroupOfEmbedding, relIndex_eq_zero_of_le_left
-/
theorem relIndex_iInf_le {ι : Type*} [Fintype ι] (f : ι -> Subgroup G) :
    (⨅ i, f i).relIndex L <= ∏ i, (f i).relIndex L :=
  le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientiInfSubgroupOfEmbedding f L) fun h =>
      let ⟨i, _hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relIndex_eq_zero_of_le_left (iInf_le f i) h)
    Nat.card_pi

@[to_additive]
/--
theorem `index_iInf_ne_zero` / 定理 `index_iInf_ne_zero`

English:
theorem index_iInf_ne_zero
  statement: {ι : Type*} [Finite ι] {f : ι -> Subgroup G}
  proof: by
  simp_rw [← relIndex_top_right] at hf ⊢
  exact relIndex_iInf_ne_zero hf

@[to_additive]

中文:
定理 index_iInf_ne_zero
  结论: {ι : 类型} [有限 ι] {f : ι -> 子群 G}
  证明: by
  simp_rw [← relIndex_top_right] at hf ⊢
  exact relIndex_iInf_ne_zero hf

@[to_additive]

Depends on / 依赖: relIndex_iInf_ne_zero, relIndex_top_right, simp_rw
-/
theorem index_iInf_ne_zero {ι : Type*} [Finite ι] {f : ι -> Subgroup G}
    (hf : forall i, (f i).index != 0) : (⨅ i, f i).index != 0 := by
  simp_rw [← relIndex_top_right] at hf ⊢
  exact relIndex_iInf_ne_zero hf

@[to_additive]
/--
theorem `index_iInf_le` / 定理 `index_iInf_le`

English:
theorem index_iInf_le
  given: {ι : Type*} [Fintype ι] (f : ι -> Subgroup G)
  proof: by simp_rw [← relIndex_top_right, relIndex_iInf_le]

@[to_additive (attr := simp) index_eq_one]

中文:
定理 index_iInf_le
  条件: {ι : 类型} [有限类型 ι] (f : ι -> 子群 G)
  证明: by simp_rw [← relIndex_top_right, relIndex_iInf_le]

@[to_additive (attr := simp) index_eq_one]

Depends on / 依赖: relIndex_iInf_le, relIndex_top_right, simp_rw
-/
theorem index_iInf_le {ι : Type*} [Fintype ι] (f : ι -> Subgroup G) :
    (⨅ i, f i).index <= ∏ i, (f i).index := by simp_rw [← relIndex_top_right, relIndex_iInf_le]

@[to_additive (attr := simp) index_eq_one]
/--
theorem `index_eq_one` / 定理 `index_eq_one`

English:
theorem index_eq_one
  statement: H.index = 1 ↔ H = ⊤
  proof: ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩

@[to_additive (attr := simp) relIndex_eq_one]

中文:
定理 index_eq_one
  结论: H.index = 1 ↔ H = ⊤
  证明: ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩

@[to_additive (attr := simp) relIndex_eq_one]

Depends on / 依赖: Nat.card_eq_one_iff_unique.mp, QuotientGroup, QuotientGroup.subgroup_eq_top_of_subsingleton, card_eq_one_iff_unique, congr_arg, index_top, subgroup_eq_top_of_subsingleton
-/
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩

@[to_additive (attr := simp) relIndex_eq_one]
/--
theorem `relIndex_eq_one` / 定理 `relIndex_eq_one`

English:
theorem relIndex_eq_one
  statement: H.relIndex K = 1 ↔ K <= H
  proof: index_eq_one.trans subgroupOf_eq_top

@[to_additive (attr := simp) card_eq_one]

中文:
定理 relIndex_eq_one
  结论: H.relIndex K = 1 ↔ K <= H
  证明: index_eq_one.trans subgroupOf_eq_top

@[to_additive (attr := simp) card_eq_one]

Depends on / 依赖: index_eq_one, index_eq_one.trans, subgroupOf_eq_top
-/
theorem relIndex_eq_one : H.relIndex K = 1 ↔ K <= H :=
  index_eq_one.trans subgroupOf_eq_top

@[to_additive (attr := simp) card_eq_one]
/--
theorem `card_eq_one` / 定理 `card_eq_one`

English:
theorem card_eq_one
  statement: Nat.card H = 1 ↔ H = ⊥
  proof: H.relIndex_bot_left ▸ relIndex_eq_one.trans le_bot_iff

中文:
定理 card_eq_one
  结论: 自然数.card H = 1 ↔ H = ⊥
  证明: H.relIndex_bot_left ▸ relIndex_eq_one.trans le_bot_iff

Depends on / 依赖: H.relIndex_bot_left, le_bot_iff, relIndex_bot_left, relIndex_eq_one, relIndex_eq_one.trans
-/
theorem card_eq_one : Nat.card H = 1 ↔ H = ⊥ :=
  H.relIndex_bot_left ▸ relIndex_eq_one.trans le_bot_iff

/-- A subgroup has index dividing 2 if and only if there exists `a` such that for all `b`, at least
one of `b * a` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup has index dividing 2 if and only if there exists `a` such
that for all `b`, at least one of `b + a` and `b` belongs to `H`. -/]
/--
theorem `index_dvd_two_iff` / 定理 `index_dvd_two_iff`

English:
theorem index_dvd_two_iff
  statement: H.index ∣ 2 ↔ exists a, forall b, (b * a in H) ∨ (b in H) where
  proof: by
    obtain (hH | hH) : H.index = 1 ∨ H.index = 2 := by
      -- This is just showing that 2 is prime, but we do it "longhand" to avoid making any
      -- dependence on number theory files.
      have := Nat.le_succ_iff.mp (Nat.le_of_dvd two_pos hH)
      rw [Nat.le_one_iff_eq_zero_or_eq_one]; rw

中文:
定理 index_dvd_two_iff
  结论: H.index ∣ 2 ↔ 存在 a, 对任意 b, (b * a in H) ∨ (b in H) where
  证明: by
    obtain (hH | hH) : H.index = 1 ∨ H.index = 2 := by
      -- This is just showing that 2 is prime, but we do it "longhand" to avoid making any
      -- dependence on number theory files.
      have := Nat.le_succ_iff.mp (Nat.le_of_dvd two_pos hH)
      rw [Nat.le_one_iff_eq_zero_or_eq_one]; rw

Depends on / 依赖: H.index
-/
theorem index_dvd_two_iff : H.index ∣ 2 ↔ exists a, forall b, (b * a in H) ∨ (b in H) where
  mp hH := by
    obtain (hH | hH) : H.index = 1 ∨ H.index = 2 := by
      -- This is just showing that 2 is prime, but we do it "longhand" to avoid making any
      -- dependence on number theory files.
      have := Nat.le_succ_iff.mp (Nat.le_of_dvd two_pos hH)
      rw [Nat.le_one_iff_eq_zero_or_eq_one]; rw [or_assoc] at this
      exact this.resolve_left fun h => (two_ne_zero <| Nat.zero_dvd.mp (h ▸ hH)).elim
    · simp [index_eq_one.mp hH]
    · exact match index_eq_two_iff.mp hH with | ⟨a, ha⟩ => ⟨a, fun b => (ha b).or⟩
  mpr := by
    rintro ⟨a, ha⟩
    by_cases ha' : a in H
    · suffices forall b, b in H by simp [(eq_top_iff' _).mpr this]
      exact fun b => (ha b).elim (fun h => by simpa using mul_mem h (inv_mem ha')) id
    · refine dvd_of_eq (index_eq_two_iff.mpr
        ⟨a, fun b => (xor_iff_or_and_not_and _ _).mpr ⟨ha b, fun h => ha' ?_⟩⟩)
      simpa using mul_mem (inv_mem h.2) h.1

/-- A subgroup has index dividing 2 if and only if there exists `a` such that for all `b`, at least
one of `a * b` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup has index dividing 2 if and only if there exists `a` such
that for all `b`, at least one of `a + b` and `b` belongs to `H`. -/]
/--
theorem `index_dvd_two_iff'` / 定理 `index_dvd_two_iff'`

English:
theorem index_dvd_two_iff'
  statement: H.index ∣ 2 ↔ exists a, forall b, (a * b in H) ∨ (b in H)
  proof: by
  rw [index_dvd_two_iff]; rw [(Equiv.inv G).exists_congr]
  refine fun a => (Equiv.inv G).forall_congr fun b => ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

中文:
定理 index_dvd_two_iff'
  结论: H.index ∣ 2 ↔ 存在 a, 对任意 b, (a * b in H) ∨ (b in H)
  证明: by
  rw [index_dvd_two_iff]; rw [(Equiv.inv G).exists_congr]
  refine fun a => (Equiv.inv G).forall_congr fun b => ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

Depends on / 依赖: Equiv.inv, Equiv.inv_apply, exists_congr, forall_congr, index_dvd_two_iff, inv_apply, inv_mem_iff, mul_inv_rev
-/
theorem index_dvd_two_iff' : H.index ∣ 2 ↔ exists a, forall b, (a * b in H) ∨ (b in H) := by
  rw [index_dvd_two_iff]; rw [(Equiv.inv G).exists_congr]
  refine fun a => (Equiv.inv G).forall_congr fun b => ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

/-- Relative version of `Subgroup.index_dvd_two_iff`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_dvd_two_iff`. -/]
/--
theorem `relIndex_dvd_two_iff` / 定理 `relIndex_dvd_two_iff`

English:
theorem relIndex_dvd_two_iff
  statement: H.relIndex K ∣ 2 ↔ exists a in K, forall b in K, (b * a in H) ∨ (b in H)
  proof: by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff, mem_subgroupOf]

中文:
定理 relIndex_dvd_two_iff
  结论: H.relIndex K ∣ 2 ↔ 存在 a in K, 对任意 b in K, (b * a in H) ∨ (b in H)
  证明: by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff, mem_subgroupOf]

Depends on / 依赖: Subgroup, Subgroup.index_dvd_two_iff, Subgroup.relIndex, index_dvd_two_iff, mem_subgroupOf, relIndex
-/
theorem relIndex_dvd_two_iff : H.relIndex K ∣ 2 ↔ exists a in K, forall b in K, (b * a in H) ∨ (b in H) := by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff, mem_subgroupOf]

/-- Relative version of `Subgroup.index_dvd_two_iff'`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_dvd_two_iff'`. -/]
/--
theorem `relIindex_dvd_two_iff'` / 定理 `relIindex_dvd_two_iff'`

English:
theorem relIindex_dvd_two_iff'
  statement: H.relIndex K ∣ 2 ↔ exists a in K, forall b in K, (a * b in H) ∨ (b in H)
  proof: by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff', mem_subgroupOf]

@[to_additive]

中文:
定理 relIindex_dvd_two_iff'
  结论: H.relIndex K ∣ 2 ↔ 存在 a in K, 对任意 b in K, (a * b in H) ∨ (b in H)
  证明: by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff', mem_subgroupOf]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.index_dvd_two_iff, Subgroup.relIndex, index_dvd_two_iff, mem_subgroupOf, relIndex
-/
theorem relIindex_dvd_two_iff' : H.relIndex K ∣ 2 ↔ exists a in K, forall b in K, (a * b in H) ∨ (b in H) := by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff', mem_subgroupOf]

@[to_additive]
/--
lemma `disjoint_of_coprime_natCard` / 引理 `disjoint_of_coprime_natCard`

English:
lemma disjoint_of_coprime_natCard
  given: (h : Nat.card H |>.Coprime <| Nat.card K)
  statement: Disjoint H K
  proof: disjoint_iff.mpr card_eq_one.mp Nat.eq_one_of_dvd_coprimes h
    (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

@[to_additive (attr := deprecated disjoint_of_coprime_natCard (since := "2026-05-28"))]

中文:
引理 disjoint_of_coprime_natCard
  条件: (h : 自然数.card H |>.Coprime <| 自然数.card K)
  结论: Disjoint H K
  证明: disjoint_iff.mpr card_eq_one.mp Nat.eq_one_of_dvd_coprimes h
    (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

@[to_additive (attr := deprecated disjoint_of_coprime_natCard (since := "2026-05-28"))]

Depends on / 依赖: Nat.eq_one_of_dvd_coprimes, card_dvd_of_le, card_eq_one, card_eq_one.mp, disjoint_iff, disjoint_iff.mpr, eq_one_of_dvd_coprimes, inf_le_left, inf_le_right
-/
lemma disjoint_of_coprime_natCard (h : Nat.card H |>.Coprime <| Nat.card K) : Disjoint H K :=
disjoint_iff.mpr card_eq_one.mp Nat.eq_one_of_dvd_coprimes h
    (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

@[to_additive (attr := deprecated disjoint_of_coprime_natCard (since := "2026-05-28"))]
/--
lemma `inf_eq_bot_of_coprime` / 引理 `inf_eq_bot_of_coprime`

English:
lemma inf_eq_bot_of_coprime
  given: (h : Nat.Coprime (Nat.card H) (Nat.card K))
  statement: H ⊓ K = ⊥
  proof: disjoint_iff.mp disjoint_of_coprime_natCard h

@[to_additive]

中文:
引理 inf_eq_bot_of_coprime
  条件: (h : 自然数.Coprime (自然数.card H) (自然数.card K))
  结论: H ⊓ K = ⊥
  证明: disjoint_iff.mp disjoint_of_coprime_natCard h

@[to_additive]

Depends on / 依赖: disjoint_iff, disjoint_iff.mp, disjoint_of_coprime_natCard
-/
lemma inf_eq_bot_of_coprime (h : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ :=
disjoint_iff.mp disjoint_of_coprime_natCard h

@[to_additive]
/--
theorem `index_ne_zero_of_finite` / 定理 `index_ne_zero_of_finite`

English:
theorem index_ne_zero_of_finite
  given: [hH : Finite (G ⧸ H)]
  statement: H.index != 0
  proof: by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Nat.card_pos.ne'

中文:
定理 index_ne_zero_of_finite
  条件: [hH : 有限 (G ⧸ H)]
  结论: H.index != 0
  证明: by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Nat.card_pos.ne'

Depends on / 依赖: Nat.card_pos.ne, card_pos, index_eq_card, nonempty_fintype
-/
theorem index_ne_zero_of_finite [hH : Finite (G ⧸ H)] : H.index != 0 := by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Nat.card_pos.ne'

/-- Finite index implies finite quotient. -/
@[to_additive (attr := instance_reducible) /-- Finite index implies finite quotient. -/]
/--
Definition of `fintypeOfIndexNeZero` / `fintypeOfIndexNeZero` 的定义

English:
definition fintypeOfIndexNeZero
  signature: (hH : H.index != 0)
  body: @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero hH)

@[to_additive]

中文:
定义 fintypeOfIndexNeZero
  签名: (hH : H.index != 0)
  定义体: @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero hH)

@[to_additive]

Depends on / 依赖: Fintype, Fintype.ofFinite, Nat.finite_of_card_ne_zero, finite_of_card_ne_zero, ofFinite
-/
noncomputable def fintypeOfIndexNeZero (hH : H.index != 0) : Fintype (G ⧸ H) :=
  @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero hH)

@[to_additive]
/--
lemma `index_eq_zero_iff_infinite` / 引理 `index_eq_zero_iff_infinite`

English:
lemma index_eq_zero_iff_infinite
  statement: H.index = 0 ↔ Infinite (G ⧸ H)
  proof: by
  simp [index_eq_card, Nat.card_eq_zero]

@[to_additive]

中文:
引理 index_eq_zero_iff_infinite
  结论: H.index = 0 ↔ 无限 (G ⧸ H)
  证明: by
  simp [index_eq_card, Nat.card_eq_zero]

@[to_additive]

Depends on / 依赖: Nat.card_eq_zero, card_eq_zero, index_eq_card
-/
lemma index_eq_zero_iff_infinite : H.index = 0 ↔ Infinite (G ⧸ H) := by
  simp [index_eq_card, Nat.card_eq_zero]

@[to_additive]
/--
lemma `index_ne_zero_iff_finite` / 引理 `index_ne_zero_iff_finite`

English:
lemma index_ne_zero_iff_finite
  statement: H.index != 0 ↔ Finite (G ⧸ H)
  proof: by
  simp [index_eq_zero_iff_infinite]

@[to_additive one_lt_index_of_ne_top]

中文:
引理 index_ne_zero_iff_finite
  结论: H.index != 0 ↔ 有限 (G ⧸ H)
  证明: by
  simp [index_eq_zero_iff_infinite]

@[to_additive one_lt_index_of_ne_top]

Depends on / 依赖: index_eq_zero_iff_infinite
-/
lemma index_ne_zero_iff_finite : H.index != 0 ↔ Finite (G ⧸ H) := by
  simp [index_eq_zero_iff_infinite]

@[to_additive one_lt_index_of_ne_top]
/--
theorem `one_lt_index_of_ne_top` / 定理 `one_lt_index_of_ne_top`

English:
theorem one_lt_index_of_ne_top
  given: [Finite (G ⧸ H)] (hH : H != ⊤)
  statement: 1 < H.index
  proof: Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_finite, mt index_eq_one.mp hH⟩

@[to_additive]

中文:
定理 one_lt_index_of_ne_top
  条件: [有限 (G ⧸ H)] (hH : H != ⊤)
  结论: 1 < H.index
  证明: Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_finite, mt index_eq_one.mp hH⟩

@[to_additive]

Depends on / 依赖: Nat.one_lt_iff_ne_zero_and_ne_one.mpr, index_eq_one, index_eq_one.mp, index_ne_zero_of_finite, one_lt_iff_ne_zero_and_ne_one
-/
theorem one_lt_index_of_ne_top [Finite (G ⧸ H)] (hH : H != ⊤) : 1 < H.index :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_finite, mt index_eq_one.mp hH⟩

@[to_additive]
/--
lemma `finite_quotient_of_finite_quotient_of_index_ne_zero` / 引理 `finite_quotient_of_finite_quotient_of_index_ne_zero`

English:
lemma finite_quotient_of_finite_quotient_of_index_ne_zero
  statement: {X : Type*} [MulAction G X]
  proof: by
  have := fintypeOfIndexNeZero hi
  exact MulAction.finite_quotient_of_finite_quotient_of_finite_quotient

@[to_additive]

中文:
引理 finite_quotient_of_finite_quotient_of_index_ne_zero
  结论: {X : 类型} [乘法作用 G X]
  证明: by
  have := fintypeOfIndexNeZero hi
  exact MulAction.finite_quotient_of_finite_quotient_of_finite_quotient

@[to_additive]

Depends on / 依赖: MulAction, MulAction.finite_quotient_of_finite_quotient_of_finite_quotient, finite_quotient_of_finite_quotient_of_finite_quotient, fintypeOfIndexNeZero
-/
lemma finite_quotient_of_finite_quotient_of_index_ne_zero {X : Type*} [MulAction G X]
    [Finite <| MulAction.orbitRel.Quotient G X] (hi : H.index != 0) :
Finite MulAction.orbitRel.Quotient H X := by
  have := fintypeOfIndexNeZero hi
  exact MulAction.finite_quotient_of_finite_quotient_of_finite_quotient

@[to_additive]
/--
lemma `finite_quotient_of_pretransitive_of_index_ne_zero` / 引理 `finite_quotient_of_pretransitive_of_index_ne_zero`

English:
lemma finite_quotient_of_pretransitive_of_index_ne_zero
  statement: {X : Type*} [MulAction G X]
  proof: by
  have := (MulAction.pretransitive_iff_subsingleton_quotient G X).1 inferInstance
  exact finite_quotient_of_finite_quotient_of_index_ne_zero hi

中文:
引理 finite_quotient_of_pretransitive_of_index_ne_zero
  结论: {X : 类型} [乘法作用 G X]
  证明: by
  have := (MulAction.pretransitive_iff_subsingleton_quotient G X).1 inferInstance
  exact finite_quotient_of_finite_quotient_of_index_ne_zero hi

Depends on / 依赖: MulAction, MulAction.pretransitive_iff_subsingleton_quotient, finite_quotient_of_finite_quotient_of_index_ne_zero, pretransitive_iff_subsingleton_quotient
-/
lemma finite_quotient_of_pretransitive_of_index_ne_zero {X : Type*} [MulAction G X]
    [MulAction.IsPretransitive G X] (hi : H.index != 0) :
Finite MulAction.orbitRel.Quotient H X := by
  have := (MulAction.pretransitive_iff_subsingleton_quotient G X).1 inferInstance
  exact finite_quotient_of_finite_quotient_of_index_ne_zero hi

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
lemma `exists_pow_mem_of_index_ne_zero` / 引理 `exists_pow_mem_of_index_ne_zero`

English:
lemma exists_pow_mem_of_index_ne_zero
  given: (h : H.index != 0) (a : G)
  proof: by
  suffices exists n₁ n₂, n₁ < n₂ ∧ n₂ <= H.index ∧ ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hlt, hle, he⟩
    refine ⟨n₂ - n₁, by lia, by lia, ?_⟩
    rw [eq_comm]; rw [QuotientGroup.eq]; rw [← zpow_natCast]; rw [← zpow_natCast]; rw [← zpow_neg]; rw [← zpow

中文:
引理 存在_pow_mem_of_index_ne_zero
  条件: (h : H.index != 0) (a : G)
  证明: by
  suffices exists n₁ n₂, n₁ < n₂ ∧ n₂ <= H.index ∧ ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hlt, hle, he⟩
    refine ⟨n₂ - n₁, by lia, by lia, ?_⟩
    rw [eq_comm]; rw [QuotientGroup.eq]; rw [← zpow_natCast]; rw [← zpow_natCast]; rw [← zpow_neg]; rw [← zpow

Depends on / 依赖: H.index, QuotientGroup, QuotientGroup.eq, add_comm, convert, eq_comm, zpow_add, zpow_natCast, zpow_neg
-/
lemma exists_pow_mem_of_index_ne_zero (h : H.index != 0) (a : G) :
    exists n, 0 < n ∧ n <= H.index ∧ a ^ n in H := by
  suffices exists n₁ n₂, n₁ < n₂ ∧ n₂ <= H.index ∧ ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hlt, hle, he⟩
    refine ⟨n₂ - n₁, by lia, by lia, ?_⟩
    rw [eq_comm]; rw [QuotientGroup.eq]; rw [← zpow_natCast]; rw [← zpow_natCast]; rw [← zpow_neg]; rw [← zpow_add]; rw [add_comm] at he
    rw [← zpow_natCast]
    convert! he
    lia
  suffices exists n₁ n₂, n₁ != n₂ ∧ n₁ <= H.index ∧ n₂ <= H.index ∧
      ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hne, hle₁, hle₂, he⟩
    rcases hne.lt_or_gt with hlt | hlt
    · exact ⟨n₁, n₂, hlt, hle₂, he⟩
    · exact ⟨n₂, n₁, hlt, hle₁, he.symm⟩
  by_contra hc
  simp_rw [not_exists] at hc
  let f : (Set.Icc 0 H.index) -> G ⧸ H := fun n => (a ^ (n : Nat) : G)
  have hf : Function.Injective f := by
    rintro ⟨n₁, h₁, hle₁⟩ ⟨n₂, h₂, hle₂⟩ he
    have hc' := hc n₁ n₂
    dsimp only [f] at he
    simpa [hle₁, hle₂, he] using hc'
  have := (fintypeOfIndexNeZero h).finite
  have hcard := Nat.card_le_card_of_injective f hf
  simp [← index_eq_card] at hcard

@[to_additive]
/--
lemma `exists_pow_mem_of_relIndex_ne_zero` / 引理 `exists_pow_mem_of_relIndex_ne_zero`

English:
lemma exists_pow_mem_of_relIndex_ne_zero
  given: (h : H.relIndex K != 0) {a : G} (ha : a in K)
  proof: by
  rcases exists_pow_mem_of_index_ne_zero h ⟨a, ha⟩ with ⟨n, hlt, hle, he⟩
  refine ⟨n, hlt, hle, ?_⟩
  simpa [pow_mem ha, mem_subgroupOf] using he

@[to_additive]

中文:
引理 存在_pow_mem_of_relIndex_ne_zero
  条件: (h : H.relIndex K != 0) {a : G} (ha : a in K)
  证明: by
  rcases exists_pow_mem_of_index_ne_zero h ⟨a, ha⟩ with ⟨n, hlt, hle, he⟩
  refine ⟨n, hlt, hle, ?_⟩
  simpa [pow_mem ha, mem_subgroupOf] using he

@[to_additive]

Depends on / 依赖: exists_pow_mem_of_index_ne_zero, mem_subgroupOf, pow_mem
-/
lemma exists_pow_mem_of_relIndex_ne_zero (h : H.relIndex K != 0) {a : G} (ha : a in K) :
    exists n, 0 < n ∧ n <= H.relIndex K ∧ a ^ n in H ⊓ K := by
  rcases exists_pow_mem_of_index_ne_zero h ⟨a, ha⟩ with ⟨n, hlt, hle, he⟩
  refine ⟨n, hlt, hle, ?_⟩
  simpa [pow_mem ha, mem_subgroupOf] using he

@[to_additive]
/--
lemma `pow_mem_of_index_ne_zero_of_dvd` / 引理 `pow_mem_of_index_ne_zero_of_dvd`

English:
lemma pow_mem_of_index_ne_zero_of_dvd
  statement: (h : H.index != 0) (a : G) {n : Nat}
  proof: by
  rcases exists_pow_mem_of_index_ne_zero h a with ⟨m, hlt, hle, he⟩
  rcases hn m hlt hle with ⟨k, rfl⟩
  rw [pow_mul]
  exact pow_mem he _

@[to_additive]

中文:
引理 pow_mem_of_index_ne_zero_of_dvd
  结论: (h : H.index != 0) (a : G) {n : 自然数}
  证明: by
  rcases exists_pow_mem_of_index_ne_zero h a with ⟨m, hlt, hle, he⟩
  rcases hn m hlt hle with ⟨k, rfl⟩
  rw [pow_mul]
  exact pow_mem he _

@[to_additive]

Depends on / 依赖: exists_pow_mem_of_index_ne_zero, pow_mem, pow_mul
-/
lemma pow_mem_of_index_ne_zero_of_dvd (h : H.index != 0) (a : G) {n : Nat}
    (hn : forall m, 0 < m -> m <= H.index -> m ∣ n) : a ^ n in H := by
  rcases exists_pow_mem_of_index_ne_zero h a with ⟨m, hlt, hle, he⟩
  rcases hn m hlt hle with ⟨k, rfl⟩
  rw [pow_mul]
  exact pow_mem he _

@[to_additive]
/--
lemma `pow_mem_of_relIndex_ne_zero_of_dvd` / 引理 `pow_mem_of_relIndex_ne_zero_of_dvd`

English:
lemma pow_mem_of_relIndex_ne_zero_of_dvd
  statement: (h : H.relIndex K != 0) {a : G} (ha : a in K) {n : Nat}
  proof: by
  convert! pow_mem_of_index_ne_zero_of_dvd h ⟨a, ha⟩ hn
  simp [pow_mem ha, mem_subgroupOf]

@[to_additive (attr := simp) index_prod]

中文:
引理 pow_mem_of_relIndex_ne_zero_of_dvd
  结论: (h : H.relIndex K != 0) {a : G} (ha : a in K) {n : 自然数}
  证明: by
  convert! pow_mem_of_index_ne_zero_of_dvd h ⟨a, ha⟩ hn
  simp [pow_mem ha, mem_subgroupOf]

@[to_additive (attr := simp) index_prod]

Depends on / 依赖: convert, mem_subgroupOf, pow_mem, pow_mem_of_index_ne_zero_of_dvd
-/
lemma pow_mem_of_relIndex_ne_zero_of_dvd (h : H.relIndex K != 0) {a : G} (ha : a in K) {n : Nat}
    (hn : forall m, 0 < m -> m <= H.relIndex K -> m ∣ n) : a ^ n in H ⊓ K := by
  convert! pow_mem_of_index_ne_zero_of_dvd h ⟨a, ha⟩ hn
  simp [pow_mem ha, mem_subgroupOf]

@[to_additive (attr := simp) index_prod]
/--
lemma `index_prod` / 引理 `index_prod`

English:
lemma index_prod
  given: (H : Subgroup G) (K : Subgroup G')
  statement: (H.prod K).index = H.index * K.index
  proof: by
  simp_rw [index, ← Nat.card_prod]
  exact Nat.card_congr (QuotientGroup.prodEquiv H K)

@[to_additive (attr := simp)]

中文:
引理 index_prod
  条件: (H : 子群 G) (K : 子群 G')
  结论: (H.乘积 K).index = H.index * K.index
  证明: by
  simp_rw [index, ← Nat.card_prod]
  exact Nat.card_congr (QuotientGroup.prodEquiv H K)

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.card_congr, Nat.card_prod, QuotientGroup, QuotientGroup.prodEquiv, card_congr, card_prod, prodEquiv, simp_rw
-/
lemma index_prod (H : Subgroup G) (K : Subgroup G') : (H.prod K).index = H.index * K.index := by
  simp_rw [index, ← Nat.card_prod]
  exact Nat.card_congr (QuotientGroup.prodEquiv H K)

@[to_additive (attr := simp)]
/--
lemma `index_pi` / 引理 `index_pi`

English:
lemma index_pi
  given: {ι : Type*} [Fintype ι] (H : ι -> Subgroup G)
  proof: by
  simp_rw [index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y => ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

@[simp]

中文:
引理 index_pi
  条件: {ι : 类型} [有限类型 ι] (H : ι -> 子群 G)
  证明: by
  simp_rw [index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y => ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

@[simp]

Depends on / 依赖: Nat.card_congr, Nat.card_pi, Quotient, Quotient.congrRight, QuotientGroup, QuotientGroup.leftRel_pi, Setoid, Setoid.piQuotientEquiv, card_congr, card_pi, congrRight, leftRel_pi, piQuotientEquiv, simp_rw
-/
lemma index_pi {ι : Type*} [Fintype ι] (H : ι -> Subgroup G) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y => ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

@[simp]
/--
lemma `index_toAddSubgroup` / 引理 `index_toAddSubgroup`

English:
lemma index_toAddSubgroup
  statement: (Subgroup.toAddSubgroup H).index = H.index
  proof: rfl

@[simp]

中文:
引理 index_toAddSubgroup
  结论: (子群.toAddSubgroup H).index = H.index
  证明: rfl

@[simp]
-/
lemma index_toAddSubgroup : (Subgroup.toAddSubgroup H).index = H.index :=
  rfl

@[simp]
/--
lemma `_root_.AddSubgroup.index_toSubgroup` / 引理 `_root_.AddSubgroup.index_toSubgroup`

English:
lemma _root_.AddSubgroup.index_toSubgroup
  given: {G : Type*} [AddGroup G] (H : AddSubgroup G)
  proof: rfl

@[simp]

中文:
引理 _root_.加法子群.index_toSubgroup
  条件: {G : 类型} [加法群 G] (H : 加法子群 G)
  证明: rfl

@[simp]
-/
lemma _root_.AddSubgroup.index_toSubgroup {G : Type*} [AddGroup G] (H : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).index = H.index :=
  rfl

@[simp]
/--
lemma `relIndex_toAddSubgroup` / 引理 `relIndex_toAddSubgroup`

English:
lemma relIndex_toAddSubgroup
  proof: rfl

@[simp]

中文:
引理 relIndex_toAddSubgroup
  证明: rfl

@[simp]
-/
lemma relIndex_toAddSubgroup :
    (Subgroup.toAddSubgroup H).relIndex (Subgroup.toAddSubgroup K) = H.relIndex K :=
  rfl

@[simp]
/--
lemma `_root_.AddSubgroup.relIndex_toSubgroup` / 引理 `_root_.AddSubgroup.relIndex_toSubgroup`

English:
lemma _root_.AddSubgroup.relIndex_toSubgroup
  given: {G : Type*} [AddGroup G] (H K : AddSubgroup G)
  proof: rfl

中文:
引理 _root_.加法子群.relIndex_toSubgroup
  条件: {G : 类型} [加法群 G] (H K : 加法子群 G)
  证明: rfl
-/
lemma _root_.AddSubgroup.relIndex_toSubgroup {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).relIndex (AddSubgroup.toSubgroup K) = H.relIndex K :=
  rfl

section FiniteIndex

/--
Definition of `_root_.AddSubgroup.FiniteIndex` / `_root_.AddSubgroup.FiniteIndex` 的定义

English:
class _root_.AddSubgroup.FiniteIndex
  parameters: {G : Type*} [AddGroup G] (H : AddSubgroup G)
  axioms and operations (1):
    - index_ne_zero : H.index != 0

中文:
类 _root_.加法子群.FiniteIndex
  参数: {G : 类型} [加法群 G] (H : 加法子群 G)
  公理与运算 (1 个):
    - index_ne_zero : H.index != 0
-/
class _root_.AddSubgroup.FiniteIndex {G : Type*} [AddGroup G] (H : AddSubgroup G) : Prop where
  /-- The additive subgroup has finite index;
  recall that `AddSubgroup.index` returns 0 when the index is infinite. -/
  index_ne_zero : H.index != 0

variable (H) in
/--
Definition of `FiniteIndex` / `FiniteIndex` 的定义

English:
class FiniteIndex
  parameters: : Prop where
  axioms and operations (1):
    - index_ne_zero : H.index != 0

中文:
类 FiniteIndex
  参数: : 命题 where
  公理与运算 (1 个):
    - index_ne_zero : H.index != 0
-/
@[to_additive] class FiniteIndex : Prop where
  /-- The subgroup has finite index;
  recall that `Subgroup.index` returns 0 when the index is infinite. -/
  index_ne_zero : H.index != 0

/--
Definition of `_root_.AddSubgroup.IsFiniteRelIndex` / `_root_.AddSubgroup.IsFiniteRelIndex` 的定义

English:
class _root_.AddSubgroup.IsFiniteRelIndex
  parameters: {G : Type*} [AddGroup G] (H K : AddSubgroup G)
  axioms and operations (1):
    - relIndex_ne_zero : H.relIndex K != 0

中文:
类 _root_.加法子群.是FiniteRelIndex
  参数: {G : 类型} [加法群 G] (H K : 加法子群 G)
  公理与运算 (1 个):
    - relIndex_ne_zero : H.relIndex K != 0
-/
class _root_.AddSubgroup.IsFiniteRelIndex {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    Prop where
  protected relIndex_ne_zero : H.relIndex K != 0

variable (H K) in
/--
Definition of `IsFiniteRelIndex` / `IsFiniteRelIndex` 的定义

English:
class IsFiniteRelIndex
  parameters: : Prop where
  axioms and operations (1):
    - relIndex_ne_zero : H.relIndex K != 0

中文:
类 是FiniteRelIndex
  参数: : 命题 where
  公理与运算 (1 个):
    - relIndex_ne_zero : H.relIndex K != 0
-/
@[to_additive] class IsFiniteRelIndex : Prop where
  protected relIndex_ne_zero : H.relIndex K != 0

/--
lemma `relIndex_ne_zero` / 引理 `relIndex_ne_zero`

English:
lemma relIndex_ne_zero
  given: [H.IsFiniteRelIndex K]
  statement: H.relIndex K != 0
  proof: IsFiniteRelIndex.relIndex_ne_zero

@[to_additive]

中文:
引理 relIndex_ne_zero
  条件: [H.是FiniteRelIndex K]
  结论: H.relIndex K != 0
  证明: IsFiniteRelIndex.relIndex_ne_zero

@[to_additive]
-/
@[to_additive] lemma relIndex_ne_zero [H.IsFiniteRelIndex K] : H.relIndex K != 0 :=
  IsFiniteRelIndex.relIndex_ne_zero

@[to_additive]
/--
Instance `IsFiniteRelIndex.to_finiteIndex_subgroupOf` / 实例 `IsFiniteRelIndex.to_finiteIndex_subgroupOf`

English:
instance IsFiniteRelIndex.to_finiteIndex_subgroupOf
  signature: [H.IsFiniteRelIndex K]
  body: relIndex_ne_zero

@[to_additive]

中文:
实例 是FiniteRelIndex.to_finiteIndex_subgroupOf
  签名: [H.是FiniteRelIndex K]
  定义体: relIndex_ne_zero

@[to_additive]

Depends on / 依赖: relIndex_ne_zero
-/
instance IsFiniteRelIndex.to_finiteIndex_subgroupOf [H.IsFiniteRelIndex K] :
    (H.subgroupOf K).FiniteIndex where
  index_ne_zero := relIndex_ne_zero

@[to_additive]
/--
lemma `isFiniteRelIndex_iff_relIndex_ne_zero` / 引理 `isFiniteRelIndex_iff_relIndex_ne_zero`

English:
lemma isFiniteRelIndex_iff_relIndex_ne_zero
  statement: H.IsFiniteRelIndex K ↔ H.relIndex K != 0
  proof: ⟨fun _ => relIndex_ne_zero, IsFiniteRelIndex.mk⟩

@[to_additive]

中文:
引理 isFiniteRelIndex_iff_relIndex_ne_zero
  结论: H.是FiniteRelIndex K ↔ H.relIndex K != 0
  证明: ⟨fun _ => relIndex_ne_zero, IsFiniteRelIndex.mk⟩

@[to_additive]

Depends on / 依赖: IsFiniteRelIndex, IsFiniteRelIndex.mk, relIndex_ne_zero
-/
lemma isFiniteRelIndex_iff_relIndex_ne_zero : H.IsFiniteRelIndex K ↔ H.relIndex K != 0 :=
  ⟨fun _ => relIndex_ne_zero, IsFiniteRelIndex.mk⟩

@[to_additive]
/--
theorem `finiteIndex_iff` / 定理 `finiteIndex_iff`

English:
theorem finiteIndex_iff
  statement: H.FiniteIndex ↔ H.index != 0
  proof: ⟨fun h => h.index_ne_zero, fun h => ⟨h⟩⟩

@[to_additive]

中文:
定理 finiteIndex_iff
  结论: H.FiniteIndex ↔ H.index != 0
  证明: ⟨fun h => h.index_ne_zero, fun h => ⟨h⟩⟩

@[to_additive]

Depends on / 依赖: h.index_ne_zero, index_ne_zero
-/
theorem finiteIndex_iff : H.FiniteIndex ↔ H.index != 0 :=
  ⟨fun h => h.index_ne_zero, fun h => ⟨h⟩⟩

@[to_additive]
/--
lemma `isFiniteRelIndex_iff_finiteIndex` / 引理 `isFiniteRelIndex_iff_finiteIndex`

English:
lemma isFiniteRelIndex_iff_finiteIndex
  proof: by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero]; rw [finiteIndex_iff]; rw [relIndex]

@[to_additive]

中文:
引理 isFiniteRelIndex_iff_finiteIndex
  证明: by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero]; rw [finiteIndex_iff]; rw [relIndex]

@[to_additive]

Depends on / 依赖: finiteIndex_iff, isFiniteRelIndex_iff_relIndex_ne_zero, relIndex
-/
lemma isFiniteRelIndex_iff_finiteIndex :
    H.IsFiniteRelIndex K ↔ (H.subgroupOf K).FiniteIndex := by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero]; rw [finiteIndex_iff]; rw [relIndex]

@[to_additive]
/--
theorem `not_finiteIndex_iff` / 定理 `not_finiteIndex_iff`

English:
theorem not_finiteIndex_iff
  statement: ¬ H.FiniteIndex ↔ H.index = 0
  proof: by
  simp [finiteIndex_iff]

@[simp]

中文:
定理 not_finiteIndex_iff
  结论: ¬ H.FiniteIndex ↔ H.index = 0
  证明: by
  simp [finiteIndex_iff]

@[simp]

Depends on / 依赖: finiteIndex_iff
-/
theorem not_finiteIndex_iff : ¬ H.FiniteIndex ↔ H.index = 0 := by
  simp [finiteIndex_iff]

@[simp]
/--
theorem `finiteIndex_toAddSubgroup_iff` / 定理 `finiteIndex_toAddSubgroup_iff`

English:
theorem finiteIndex_toAddSubgroup_iff
  statement: H.toAddSubgroup.FiniteIndex ↔ H.FiniteIndex
  proof: by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[simp]

中文:
定理 finiteIndex_toAddSubgroup_iff
  结论: H.toAddSubgroup.FiniteIndex ↔ H.FiniteIndex
  证明: by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[simp]

Depends on / 依赖: AddSubgroup, AddSubgroup.finiteIndex_iff, finiteIndex_iff
-/
theorem finiteIndex_toAddSubgroup_iff : H.toAddSubgroup.FiniteIndex ↔ H.FiniteIndex := by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[simp]
/--
theorem `_root_.AddSubgroup.finiteIndex_toSubgroup_iff` / 定理 `_root_.AddSubgroup.finiteIndex_toSubgroup_iff`

English:
theorem _root_.AddSubgroup.finiteIndex_toSubgroup_iff
  given: {G : Type*} [AddGroup G] (H : AddSubgroup G)
  proof: by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[to_additive (attr := simp)]

中文:
定理 _root_.加法子群.finiteIndex_toSubgroup_iff
  条件: {G : 类型} [加法群 G] (H : 加法子群 G)
  证明: by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: AddSubgroup, AddSubgroup.finiteIndex_iff, finiteIndex_iff
-/
theorem _root_.AddSubgroup.finiteIndex_toSubgroup_iff {G : Type*} [AddGroup G] (H : AddSubgroup G) :
    H.toSubgroup.FiniteIndex ↔ H.FiniteIndex := by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[to_additive (attr := simp)]
/--
lemma `isFiniteRelIndex_top_iff` / 引理 `isFiniteRelIndex_top_iff`

English:
lemma isFiniteRelIndex_top_iff
  statement: H.IsFiniteRelIndex ⊤ ↔ H.FiniteIndex
  proof: by
  rw [finiteIndex_iff]; rw [isFiniteRelIndex_iff_relIndex_ne_zero]; rw [relIndex_top_right]

中文:
引理 isFiniteRelIndex_top_iff
  结论: H.是FiniteRelIndex ⊤ ↔ H.FiniteIndex
  证明: by
  rw [finiteIndex_iff]; rw [isFiniteRelIndex_iff_relIndex_ne_zero]; rw [relIndex_top_right]

Depends on / 依赖: finiteIndex_iff, isFiniteRelIndex_iff_relIndex_ne_zero, relIndex_top_right
-/
lemma isFiniteRelIndex_top_iff : H.IsFiniteRelIndex ⊤ ↔ H.FiniteIndex := by
  rw [finiteIndex_iff]; rw [isFiniteRelIndex_iff_relIndex_ne_zero]; rw [relIndex_top_right]

/-- A finite index subgroup has finite quotient. -/
@[to_additive (attr := instance_reducible) /-- A finite index subgroup has finite quotient -/]
/--
Definition of `fintypeQuotientOfFiniteIndex` / `fintypeQuotientOfFiniteIndex` 的定义

English:
definition fintypeQuotientOfFiniteIndex
  signature: [FiniteIndex H]
  body: fintypeOfIndexNeZero FiniteIndex.index_ne_zero

@[to_additive]

中文:
定义 fintypeQuotientOfFiniteIndex
  签名: [FiniteIndex H]
  定义体: fintypeOfIndexNeZero FiniteIndex.index_ne_zero

@[to_additive]

Depends on / 依赖: FiniteIndex, FiniteIndex.index_ne_zero, fintypeOfIndexNeZero, index_ne_zero
-/
noncomputable def fintypeQuotientOfFiniteIndex [FiniteIndex H] : Fintype (G ⧸ H) :=
  fintypeOfIndexNeZero FiniteIndex.index_ne_zero

@[to_additive]
/--
Instance `finite_quotient_of_finiteIndex` / 实例 `finite_quotient_of_finiteIndex`

English:
instance finite_quotient_of_finiteIndex
  signature: [FiniteIndex H]
  body: fintypeQuotientOfFiniteIndex.finite

@[to_additive]

中文:
实例 finite_quotient_of_finiteIndex
  签名: [FiniteIndex H]
  定义体: fintypeQuotientOfFiniteIndex.finite

@[to_additive]

Depends on / 依赖: finite, fintypeQuotientOfFiniteIndex, fintypeQuotientOfFiniteIndex.finite
-/
instance finite_quotient_of_finiteIndex [FiniteIndex H] : Finite (G ⧸ H) :=
  fintypeQuotientOfFiniteIndex.finite

@[to_additive]
/--
theorem `finiteIndex_of_finite_quotient` / 定理 `finiteIndex_of_finite_quotient`

English:
theorem finiteIndex_of_finite_quotient
  given: [Finite (G ⧸ H)]
  statement: FiniteIndex H
  proof: ⟨index_ne_zero_of_finite⟩

@[to_additive]

中文:
定理 finiteIndex_of_finite_quotient
  条件: [有限 (G ⧸ H)]
  结论: FiniteIndex H
  证明: ⟨index_ne_zero_of_finite⟩

@[to_additive]

Depends on / 依赖: index_ne_zero_of_finite
-/
theorem finiteIndex_of_finite_quotient [Finite (G ⧸ H)] : FiniteIndex H :=
  ⟨index_ne_zero_of_finite⟩

@[to_additive]
/--
theorem `finiteIndex_iff_finite_quotient` / 定理 `finiteIndex_iff_finite_quotient`

English:
theorem finiteIndex_iff_finite_quotient
  statement: FiniteIndex H ↔ Finite (G ⧸ H)
  proof: ⟨fun _ => inferInstance, fun _ => finiteIndex_of_finite_quotient⟩

@[to_additive]

中文:
定理 finiteIndex_iff_finite_quotient
  结论: FiniteIndex H ↔ 有限 (G ⧸ H)
  证明: ⟨fun _ => inferInstance, fun _ => finiteIndex_of_finite_quotient⟩

@[to_additive]

Depends on / 依赖: finiteIndex_of_finite_quotient
-/
theorem finiteIndex_iff_finite_quotient : FiniteIndex H ↔ Finite (G ⧸ H) :=
  ⟨fun _ => inferInstance, fun _ => finiteIndex_of_finite_quotient⟩

@[to_additive]
instance (priority := 100) finiteIndex_of_finite [Finite G] : FiniteIndex H :=
  finiteIndex_of_finite_quotient

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteIndex
  signature: H] [FiniteIndex K] : FiniteIndex (H.prod K)
  body: by
  simp_all [finiteIndex_iff]

中文:
实例 [FiniteIndex
  签名: H] [FiniteIndex K] : FiniteIndex (H.乘积 K)
  定义体: by
  simp_all [finiteIndex_iff]

Depends on / 依赖: finiteIndex_iff
-/
instance [FiniteIndex H] [FiniteIndex K] : FiniteIndex (H.prod K) := by
  simp_all [finiteIndex_iff]

variable (H) in
@[to_additive]
/--
theorem `finite_iff_finite_and_finiteIndex` / 定理 `finite_iff_finite_and_finiteIndex`

English:
theorem finite_iff_finite_and_finiteIndex
  statement: Finite G ↔ Finite H ∧ H.FiniteIndex where
  proof: ⟨inferInstance, inferInstance⟩
mpr := fun ⟨_, _⟩ => Nat.finite_of_card_ne_zero
    H.card_mul_index ▸ mul_ne_zero Nat.card_pos.ne' FiniteIndex.index_ne_zero

@[to_additive]

中文:
定理 finite_iff_finite_and_finiteIndex
  结论: 有限 G ↔ 有限 H ∧ H.FiniteIndex where
  证明: ⟨inferInstance, inferInstance⟩
mpr := fun ⟨_, _⟩ => Nat.finite_of_card_ne_zero
    H.card_mul_index ▸ mul_ne_zero Nat.card_pos.ne' FiniteIndex.index_ne_zero

@[to_additive]
-/
theorem finite_iff_finite_and_finiteIndex : Finite G ↔ Finite H ∧ H.FiniteIndex where
  mp _ := ⟨inferInstance, inferInstance⟩
mpr := fun ⟨_, _⟩ => Nat.finite_of_card_ne_zero
    H.card_mul_index ▸ mul_ne_zero Nat.card_pos.ne' FiniteIndex.index_ne_zero

@[to_additive]
/--
theorem `_root_.MonoidHom.finite_iff_finite_ker_range` / 定理 `_root_.MonoidHom.finite_iff_finite_ker_range`

English:
theorem _root_.MonoidHom.finite_iff_finite_ker_range
  given: (f : G ->* G')
  proof: by
  rw [finite_iff_finite_and_finiteIndex f.ker]; rw [← (QuotientGroup.quotientKerEquivRange f).finite_iff]; rw [finiteIndex_iff_finite_quotient]

@[to_additive]

中文:
定理 _root_.幺半群态射.finite_iff_finite_ker_range
  条件: (f : G ->* G')
  证明: by
  rw [finite_iff_finite_and_finiteIndex f.ker]; rw [← (QuotientGroup.quotientKerEquivRange f).finite_iff]; rw [finiteIndex_iff_finite_quotient]

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.quotientKerEquivRange, f.ker, finiteIndex_iff_finite_quotient, finite_iff, finite_iff_finite_and_finiteIndex, quotientKerEquivRange
-/
theorem _root_.MonoidHom.finite_iff_finite_ker_range (f : G ->* G') :
    Finite G ↔ Finite f.ker ∧ Finite f.range := by
  rw [finite_iff_finite_and_finiteIndex f.ker]; rw [← (QuotientGroup.quotientKerEquivRange f).finite_iff]; rw [finiteIndex_iff_finite_quotient]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FiniteIndex (⊤ : Subgroup G)
  body: ⟨ne_of_eq_of_ne index_top one_ne_zero⟩

@[to_additive]

中文:
实例 :
  签名: FiniteIndex (⊤ : 子群 G)
  定义体: ⟨ne_of_eq_of_ne index_top one_ne_zero⟩

@[to_additive]

Depends on / 依赖: index_top, ne_of_eq_of_ne, one_ne_zero
-/
instance : FiniteIndex (⊤ : Subgroup G) :=
  ⟨ne_of_eq_of_ne index_top one_ne_zero⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FiniteIndex
  signature: H] [FiniteIndex K] : FiniteIndex (H ⊓ K)
  body: ⟨index_inf_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

@[to_additive]

中文:
实例 [FiniteIndex
  签名: H] [FiniteIndex K] : FiniteIndex (H ⊓ K)
  定义体: ⟨index_inf_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

@[to_additive]

Depends on / 依赖: FiniteIndex, FiniteIndex.index_ne_zero, index_inf_ne_zero, index_ne_zero
-/
instance [FiniteIndex H] [FiniteIndex K] : FiniteIndex (H ⊓ K) :=
  ⟨index_inf_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

@[to_additive]
/--
theorem `finiteIndex_iInf` / 定理 `finiteIndex_iInf`

English:
theorem finiteIndex_iInf
  statement: {ι : Type*} [Finite ι] {f : ι -> Subgroup G}
  proof: ⟨index_iInf_ne_zero fun i => (hf i).index_ne_zero⟩

@[to_additive]

中文:
定理 finiteIndex_iInf
  结论: {ι : 类型} [有限 ι] {f : ι -> 子群 G}
  证明: ⟨index_iInf_ne_zero fun i => (hf i).index_ne_zero⟩

@[to_additive]

Depends on / 依赖: index_iInf_ne_zero, index_ne_zero
-/
theorem finiteIndex_iInf {ι : Type*} [Finite ι] {f : ι -> Subgroup G}
    (hf : forall i, (f i).FiniteIndex) : (⨅ i, f i).FiniteIndex :=
  ⟨index_iInf_ne_zero fun i => (hf i).index_ne_zero⟩

@[to_additive]
/--
theorem `finiteIndex_iInf'` / 定理 `finiteIndex_iInf'`

English:
theorem finiteIndex_iInf'
  statement: {ι : Type*} {s : Finset ι}
  proof: by
  rw [iInf_subtype']
  exact finiteIndex_iInf fun ⟨i, hi⟩ => hs i hi

@[to_additive]

中文:
定理 finiteIndex_iInf'
  结论: {ι : 类型} {s : 有限集 ι}
  证明: by
  rw [iInf_subtype']
  exact finiteIndex_iInf fun ⟨i, hi⟩ => hs i hi

@[to_additive]

Depends on / 依赖: finiteIndex_iInf, iInf_subtype
-/
theorem finiteIndex_iInf' {ι : Type*} {s : Finset ι}
    (f : ι -> Subgroup G) (hs : forall i in s, (f i).FiniteIndex) :
    (⨅ i in s, f i).FiniteIndex := by
  rw [iInf_subtype']
  exact finiteIndex_iInf fun ⟨i, hi⟩ => hs i hi

@[to_additive]
/--
Instance `instFiniteIndex_subgroupOf` / 实例 `instFiniteIndex_subgroupOf`

English:
instance instFiniteIndex_subgroupOf
  signature: (H K : Subgroup G) [H.FiniteIndex]
  body: ⟨fun h => H.index_ne_zero_of_finite H.index_eq_zero_of_relIndex_eq_zero h⟩

@[to_additive]

中文:
实例 instFiniteIndex_subgroupOf
  签名: (H K : 子群 G) [H.FiniteIndex]
  定义体: ⟨fun h => H.index_ne_zero_of_finite H.index_eq_zero_of_relIndex_eq_zero h⟩

@[to_additive]

Depends on / 依赖: H.index_eq_zero_of_relIndex_eq_zero, H.index_ne_zero_of_finite, index_eq_zero_of_relIndex_eq_zero, index_ne_zero_of_finite
-/
instance instFiniteIndex_subgroupOf (H K : Subgroup G) [H.FiniteIndex] :
    (H.subgroupOf K).FiniteIndex :=
⟨fun h => H.index_ne_zero_of_finite H.index_eq_zero_of_relIndex_eq_zero h⟩

@[to_additive]
/--
theorem `finiteIndex_of_le` / 定理 `finiteIndex_of_le`

English:
theorem finiteIndex_of_le
  given: [FiniteIndex H] (h : H <= K)
  statement: FiniteIndex K
  proof: ⟨ne_zero_of_dvd_ne_zero FiniteIndex.index_ne_zero (index_dvd_of_le h)⟩

@[to_additive]

中文:
定理 finiteIndex_of_le
  条件: [FiniteIndex H] (h : H <= K)
  结论: FiniteIndex K
  证明: ⟨ne_zero_of_dvd_ne_zero FiniteIndex.index_ne_zero (index_dvd_of_le h)⟩

@[to_additive]

Depends on / 依赖: FiniteIndex, FiniteIndex.index_ne_zero, index_dvd_of_le, index_ne_zero, ne_zero_of_dvd_ne_zero
-/
theorem finiteIndex_of_le [FiniteIndex H] (h : H <= K) : FiniteIndex K :=
  ⟨ne_zero_of_dvd_ne_zero FiniteIndex.index_ne_zero (index_dvd_of_le h)⟩

@[to_additive]
/--
lemma `isFiniteRelIndex_of_le_left` / 引理 `isFiniteRelIndex_of_le_left`

English:
lemma isFiniteRelIndex_of_le_left
  given: (L : Subgroup G) [H.IsFiniteRelIndex L] (h : H <= K)
  proof: by
  rw [isFiniteRelIndex_iff_finiteIndex] at *
exact finiteIndex_of_le subgroupOf_mono L h

@[deprecated (since := "2026-05-09")] alias isFiniteRelIndex_of_le := isFiniteRelIndex_of_le_left
@[deprecated (since := "2026-05-09")] alias
  _root_.AddSubgroup.isFiniteRelIndex_of_le := AddSubgroup.isFini

中文:
引理 isFiniteRelIndex_of_le_left
  条件: (L : 子群 G) [H.是FiniteRelIndex L] (h : H <= K)
  证明: by
  rw [isFiniteRelIndex_iff_finiteIndex] at *
exact finiteIndex_of_le subgroupOf_mono L h

@[deprecated (since := "2026-05-09")] alias isFiniteRelIndex_of_le := isFiniteRelIndex_of_le_left
@[deprecated (since := "2026-05-09")] alias
  _root_.AddSubgroup.isFiniteRelIndex_of_le := AddSubgroup.isFini

Depends on / 依赖: finiteIndex_of_le, isFiniteRelIndex_iff_finiteIndex, subgroupOf_mono
-/
lemma isFiniteRelIndex_of_le_left (L : Subgroup G) [H.IsFiniteRelIndex L] (h : H <= K) :
    K.IsFiniteRelIndex L := by
  rw [isFiniteRelIndex_iff_finiteIndex] at *
exact finiteIndex_of_le subgroupOf_mono L h

@[deprecated (since := "2026-05-09")] alias isFiniteRelIndex_of_le := isFiniteRelIndex_of_le_left
@[deprecated (since := "2026-05-09")] alias
  _root_.AddSubgroup.isFiniteRelIndex_of_le := AddSubgroup.isFiniteRelIndex_of_le_left

variable (H) in
@[to_additive]
/--
lemma `isFiniteRelIndex_of_le_right` / 引理 `isFiniteRelIndex_of_le_right`

English:
lemma isFiniteRelIndex_of_le_right
  given: (h : K <= L) [H.IsFiniteRelIndex L]
  proof: by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero]
  exact mt (relIndex_eq_zero_of_le_right h) relIndex_ne_zero

@[to_additive]

中文:
引理 isFiniteRelIndex_of_le_right
  条件: (h : K <= L) [H.是FiniteRelIndex L]
  证明: by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero]
  exact mt (relIndex_eq_zero_of_le_right h) relIndex_ne_zero

@[to_additive]

Depends on / 依赖: isFiniteRelIndex_iff_relIndex_ne_zero, relIndex_eq_zero_of_le_right, relIndex_ne_zero
-/
lemma isFiniteRelIndex_of_le_right (h : K <= L) [H.IsFiniteRelIndex L] :
    H.IsFiniteRelIndex K := by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero]
  exact mt (relIndex_eq_zero_of_le_right h) relIndex_ne_zero

@[to_additive]
/--
lemma `isFiniteRelIndex_of_finiteIndex` / 引理 `isFiniteRelIndex_of_finiteIndex`

English:
lemma isFiniteRelIndex_of_finiteIndex
  given: [h : H.FiniteIndex]
  statement: H.IsFiniteRelIndex K
  proof: by
  rw [← isFiniteRelIndex_top_iff] at h
  exact isFiniteRelIndex_of_le_right _ le_top

@[to_additive (attr := gcongr)]

中文:
引理 isFiniteRelIndex_of_finiteIndex
  条件: [h : H.FiniteIndex]
  结论: H.是FiniteRelIndex K
  证明: by
  rw [← isFiniteRelIndex_top_iff] at h
  exact isFiniteRelIndex_of_le_right _ le_top

@[to_additive (attr := gcongr)]

Depends on / 依赖: isFiniteRelIndex_of_le_right, isFiniteRelIndex_top_iff, le_top
-/
lemma isFiniteRelIndex_of_finiteIndex [h : H.FiniteIndex] : H.IsFiniteRelIndex K := by
  rw [← isFiniteRelIndex_top_iff] at h
  exact isFiniteRelIndex_of_le_right _ le_top

@[to_additive (attr := gcongr)]
/--
lemma `index_antitone` / 引理 `index_antitone`

English:
lemma index_antitone
  given: (h : H <= K) [H.FiniteIndex]
  statement: K.index <= H.index
  proof: Nat.le_of_dvd (Nat.zero_lt_of_ne_zero FiniteIndex.index_ne_zero) (index_dvd_of_le h)

@[to_additive (attr := gcongr)]

中文:
引理 index_antitone
  条件: (h : H <= K) [H.FiniteIndex]
  结论: K.index <= H.index
  证明: Nat.le_of_dvd (Nat.zero_lt_of_ne_zero FiniteIndex.index_ne_zero) (index_dvd_of_le h)

@[to_additive (attr := gcongr)]

Depends on / 依赖: FiniteIndex, FiniteIndex.index_ne_zero, Nat.le_of_dvd, Nat.zero_lt_of_ne_zero, index_dvd_of_le, index_ne_zero, le_of_dvd, zero_lt_of_ne_zero
-/
lemma index_antitone (h : H <= K) [H.FiniteIndex] : K.index <= H.index :=
  Nat.le_of_dvd (Nat.zero_lt_of_ne_zero FiniteIndex.index_ne_zero) (index_dvd_of_le h)

@[to_additive (attr := gcongr)]
/--
lemma `index_strictAnti` / 引理 `index_strictAnti`

English:
lemma index_strictAnti
  given: (h : H < K) [H.FiniteIndex]
  statement: K.index < H.index
  proof: by
  have h0 : K.index != 0 := (finiteIndex_of_le h.le).index_ne_zero
  apply lt_of_le_of_ne (index_antitone h.le)
  rw [← relIndex_mul_index h.le]; rw [Ne]; rw [eq_comm]; rw [mul_eq_right₀ h0]; rw [relIndex_eq_one]
  exact h.not_ge

中文:
引理 index_strictAnti
  条件: (h : H < K) [H.FiniteIndex]
  结论: K.index < H.index
  证明: by
  have h0 : K.index != 0 := (finiteIndex_of_le h.le).index_ne_zero
  apply lt_of_le_of_ne (index_antitone h.le)
  rw [← relIndex_mul_index h.le]; rw [Ne]; rw [eq_comm]; rw [mul_eq_right₀ h0]; rw [relIndex_eq_one]
  exact h.not_ge

Depends on / 依赖: K.index, eq_comm, finiteIndex_of_le, h.le, h.not_ge, index_antitone, index_ne_zero, lt_of_le_of_ne, not_ge, relIndex_eq_one, relIndex_mul_index
-/
lemma index_strictAnti (h : H < K) [H.FiniteIndex] : K.index < H.index := by
  have h0 : K.index != 0 := (finiteIndex_of_le h.le).index_ne_zero
  apply lt_of_le_of_ne (index_antitone h.le)
  rw [← relIndex_mul_index h.le]; rw [Ne]; rw [eq_comm]; rw [mul_eq_right₀ h0]; rw [relIndex_eq_one]
  exact h.not_ge

variable (H K)

@[to_additive]
/--
Instance `finiteIndex_ker` / 实例 `finiteIndex_ker`

English:
instance finiteIndex_ker
  signature: {G' : Type*} [Group G'] (f : G ->* G') [Finite f.range]
  body: @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)

中文:
实例 finiteIndex_ker
  签名: {G' : 类型} [群 G'] (f : G ->* G') [有限 f.range]
  定义体: @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)

Depends on / 依赖: Finite, Finite.of_equiv, QuotientGroup, QuotientGroup.quotientKerEquivRange, f.ker, f.range, finiteIndex_of_finite_quotient, of_equiv, quotientKerEquivRange
-/
instance finiteIndex_ker {G' : Type*} [Group G'] (f : G ->* G') [Finite f.range] :
    f.ker.FiniteIndex :=
  @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)

/--
Instance `finiteIndex_normalCore` / 实例 `finiteIndex_normalCore`

English:
instance finiteIndex_normalCore
  signature: [H.FiniteIndex]
  body: by
  rw [normalCore_eq_ker]
  infer_instance

中文:
实例 finiteIndex_normalCore
  签名: [H.FiniteIndex]
  定义体: by
  rw [normalCore_eq_ker]
  infer_instance

Depends on / 依赖: infer_instance, normalCore_eq_ker
-/
instance finiteIndex_normalCore [H.FiniteIndex] : H.normalCore.FiniteIndex := by
  rw [normalCore_eq_ker]
  infer_instance

/--
Instance `_root_.AddSubgroup.finiteIndex_normalCore` / 实例 `_root_.AddSubgroup.finiteIndex_normalCore`

English:
instance _root_.AddSubgroup.finiteIndex_normalCore
  signature: {G : Type*} [AddGroup G] (H : AddSubgroup G)
  body: by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff] at h ⊢
  exact H.toSubgroup.finiteIndex_normalCore

中文:
实例 _root_.加法子群.finiteIndex_normalCore
  签名: {G : 类型} [加法群 G] (H : 加法子群 G)
  定义体: by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff] at h ⊢
  exact H.toSubgroup.finiteIndex_normalCore

Depends on / 依赖: AddSubgroup, AddSubgroup.finiteIndex_toSubgroup_iff, H.toSubgroup.finiteIndex_normalCore, finiteIndex_normalCore, finiteIndex_toSubgroup_iff, toSubgroup
-/
instance _root_.AddSubgroup.finiteIndex_normalCore {G : Type*} [AddGroup G] (H : AddSubgroup G)
    [h : H.FiniteIndex] : H.normalCore.FiniteIndex := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff] at h ⊢
  exact H.toSubgroup.finiteIndex_normalCore

attribute [to_additive existing] finiteIndex_normalCore

@[to_additive]
/--
theorem `index_range` / 定理 `index_range`

English:
theorem index_range
  given: {f : G ->* G} [hf : f.ker.FiniteIndex]
  proof: by
  rw [← mul_left_inj' hf.index_ne_zero]; rw [card_mul_index]; rw [index_ker]; rw [index_mul_card]

中文:
定理 index_range
  条件: {f : G ->* G} [hf : f.ker.FiniteIndex]
  证明: by
  rw [← mul_left_inj' hf.index_ne_zero]; rw [card_mul_index]; rw [index_ker]; rw [index_mul_card]

Depends on / 依赖: card_mul_index, hf.index_ne_zero, index_ker, index_mul_card, index_ne_zero, mul_left_inj
-/
theorem index_range {f : G ->* G} [hf : f.ker.FiniteIndex] :
    f.range.index = Nat.card f.ker := by
  rw [← mul_left_inj' hf.index_ne_zero]; rw [card_mul_index]; rw [index_ker]; rw [index_mul_card]

end FiniteIndex

end Subgroup

section Pointwise

open scoped Pointwise

variable {G H : Type*} [Group H] (h : H)

-- NB: `to_additive` does not work to generate the second lemma from the first here, because it
-- would need to additivize `G`, but not `H`.

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Subgroup.relIndex_pointwise_smul` / 引理 `Subgroup.relIndex_pointwise_smul`

English:
lemma Subgroup.relIndex_pointwise_smul
  given: [Group G] [MulDistribMulAction H G] (J K : Subgroup G)
  proof: by
  rw [pointwise_smul_def K]; rw [← relIndex_comap]; rw [pointwise_smul_def]; rw [comap_map_eq_self_of_injective (by intro a b; simp)]

中文:
引理 子群.relIndex_pointwise_smul
  条件: [群 G] [MulDistribMul作用 H G] (J K : 子群 G)
  证明: by
  rw [pointwise_smul_def K]; rw [← relIndex_comap]; rw [pointwise_smul_def]; rw [comap_map_eq_self_of_injective (by intro a b; simp)]

Depends on / 依赖: comap_map_eq_self_of_injective, pointwise_smul_def, relIndex_comap
-/
lemma Subgroup.relIndex_pointwise_smul [Group G] [MulDistribMulAction H G] (J K : Subgroup G) :
    (h • J).relIndex (h • K) = J.relIndex K := by
  rw [pointwise_smul_def K]; rw [← relIndex_comap]; rw [pointwise_smul_def]; rw [comap_map_eq_self_of_injective (by intro a b; simp)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `AddSubgroup.relIndex_pointwise_smul` / 引理 `AddSubgroup.relIndex_pointwise_smul`

English:
lemma AddSubgroup.relIndex_pointwise_smul
  statement: [AddGroup G] [DistribMulAction H G]
  proof: by
  rw [pointwise_smul_def K]; rw [← relIndex_comap]; rw [pointwise_smul_def]; rw [comap_map_eq_self_of_injective (by intro a b; simp)]

中文:
引理 加法子群.relIndex_pointwise_smul
  结论: [加法群 G] [分配乘法作用 H G]
  证明: by
  rw [pointwise_smul_def K]; rw [← relIndex_comap]; rw [pointwise_smul_def]; rw [comap_map_eq_self_of_injective (by intro a b; simp)]

Depends on / 依赖: comap_map_eq_self_of_injective, pointwise_smul_def, relIndex_comap
-/
lemma AddSubgroup.relIndex_pointwise_smul [AddGroup G] [DistribMulAction H G]
    (J K : AddSubgroup G) : (h • J).relIndex (h • K) = J.relIndex K := by
  rw [pointwise_smul_def K]; rw [← relIndex_comap]; rw [pointwise_smul_def]; rw [comap_map_eq_self_of_injective (by intro a b; simp)]

end Pointwise

namespace MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] (x : X)

/--
theorem `index_stabilizer` / 定理 `index_stabilizer`

English:
theorem index_stabilizer
  proof: (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)).symm.trans
    (Nat.card_coe_set_eq (orbit G x))

中文:
定理 index_stabilizer
  证明: (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)).symm.trans
    (Nat.card_coe_set_eq (orbit G x))
-/
@[to_additive] theorem index_stabilizer :
    (stabilizer G x).index = (orbit G x).ncard :=
  (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)).symm.trans
    (Nat.card_coe_set_eq (orbit G x))

/--
theorem `index_stabilizer_of_transitive` / 定理 `index_stabilizer_of_transitive`

English:
theorem index_stabilizer_of_transitive
  given: [IsPretransitive G X]
  proof: by
  rw [index_stabilizer]; rw [orbit_eq_univ]; rw [Set.ncard_univ]

中文:
定理 index_stabilizer_of_transitive
  条件: [是Pretransitive G X]
  证明: by
  rw [index_stabilizer]; rw [orbit_eq_univ]; rw [Set.ncard_univ]
-/
@[to_additive] theorem index_stabilizer_of_transitive [IsPretransitive G X] :
    (stabilizer G x).index = Nat.card X := by
  rw [index_stabilizer]; rw [orbit_eq_univ]; rw [Set.ncard_univ]

end MulAction

namespace MonoidHom

@[to_additive AddMonoidHom.surjective_of_card_ker_le_div]
/--
lemma `surjective_of_card_ker_le_div` / 引理 `surjective_of_card_ker_le_div`

English:
lemma surjective_of_card_ker_le_div
  statement: {G M : Type*} [Group G] [Group M] [Finite G] [Finite M]
  proof: by
refine range_eq_top.1 SetLike.ext' Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
  rw [Subgroup.coe_top]; rw [Set.ncard_univ]; rw [← Nat.card_coe_set_eq]; rw [SetLike.coe_sort_coe]; rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Nat.le_of_mul_le_mul_left (f.ke

中文:
引理 surjective_of_card_ker_le_div
  结论: {G M : 类型} [群 G] [群 M] [有限 G] [有限 M]
  证明: by
refine range_eq_top.1 SetLike.ext' Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
  rw [Subgroup.coe_top]; rw [Set.ncard_univ]; rw [← Nat.card_coe_set_eq]; rw [SetLike.coe_sort_coe]; rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Nat.le_of_mul_le_mul_left (f.ke

Depends on / 依赖: Nat.card_coe_set_eq, Nat.card_congr, Nat.card_pos, Nat.le_of_mul_le_mul_left, Nat.mul_le_of_le_div, QuotientGroup, QuotientGroup.quotientKerEquivRange, Set.eq_of_subset_of_ncard_le, Set.ncard_univ, Set.subset_univ, SetLike, SetLike.coe_sort_coe, SetLike.ext, Subgroup, Subgroup.coe_top, card_coe_set_eq, card_congr, card_mul_index, card_pos, coe_sort_coe
-/
lemma surjective_of_card_ker_le_div {G M : Type*} [Group G] [Group M] [Finite G] [Finite M]
    (f : G ->* M) (h : Nat.card f.ker <= Nat.card G / Nat.card M) : Function.Surjective f := by
refine range_eq_top.1 SetLike.ext' Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
  rw [Subgroup.coe_top]; rw [Set.ncard_univ]; rw [← Nat.card_coe_set_eq]; rw [SetLike.coe_sort_coe]; rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Nat.le_of_mul_le_mul_left (f.ker.card_mul_index ▸ Nat.mul_le_of_le_div _ _ _ h) Nat.card_pos

open Finset

variable {G M F : Type*} [Group G] [Fintype G] [Monoid M] [DecidableEq M]
  [FunLike F G M] [MonoidHomClass F G M]

@[to_additive]
/--
lemma `card_fiber_eq_of_mem_range` / 引理 `card_fiber_eq_of_mem_range`

English:
lemma card_fiber_eq_of_mem_range
  given: (f : F) {x y : M} (hx : x in Set.range f) (hy : y in Set.range f)
  proof: by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  rcases mul_left_surjective x y with ⟨y, rfl⟩
  conv_lhs =>
    rw [← map_univ_equiv (Equiv.mulRight y⁻¹)]; rw [filter_map]; rw [card_map]
  congr 2 with g
  simp only [Function.comp, Equiv.toEmbedding_apply, Equiv.coe_mulRight, map_mul]
  let 

中文:
引理 card_fiber_eq_of_mem_range
  条件: (f : F) {x y : M} (hx : x in 集合.range f) (hy : y in 集合.range f)
  证明: by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  rcases mul_left_surjective x y with ⟨y, rfl⟩
  conv_lhs =>
    rw [← map_univ_equiv (Equiv.mulRight y⁻¹)]; rw [filter_map]; rw [card_map]
  congr 2 with g
  simp only [Function.comp, Equiv.toEmbedding_apply, Equiv.coe_mulRight, map_mul]
  let 

Depends on / 依赖: Equiv.coe_mulRight, Equiv.mulRight, Equiv.toEmbedding_apply, Function, Function.comp, MonoidHomClass, MonoidHomClass.toMonoidHom, Units.mul_inv_eq_iff_eq_mul, card_map, coe_mulRight, coe_toHomUnits, conv_lhs, filter_map, map_inv, map_mul, map_univ_equiv, mulRight, mul_inv_eq_iff_eq_mul, mul_left_surjective, toEmbedding_apply
-/
lemma card_fiber_eq_of_mem_range (f : F) {x y : M} (hx : x in Set.range f) (hy : y in Set.range f) :
    #{g | f g = x} = #{g | f g = y} := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  rcases mul_left_surjective x y with ⟨y, rfl⟩
  conv_lhs =>
    rw [← map_univ_equiv (Equiv.mulRight y⁻¹)]; rw [filter_map]; rw [card_map]
  congr 2 with g
  simp only [Function.comp, Equiv.toEmbedding_apply, Equiv.coe_mulRight, map_mul]
  let f' := MonoidHomClass.toMonoidHom f
  change f' g * f' y⁻¹ = f' x ↔ f' g = f' x * f' y
  rw [← f'.coe_toHomUnits y⁻¹]; rw [map_inv]; rw [Units.mul_inv_eq_iff_eq_mul]; rw [f'.coe_toHomUnits]

end MonoidHom

namespace AddSubgroup
variable {G A : Type*} [Group G] [AddGroup A] [DistribMulAction G A]

@[simp]
/--
lemma `index_smul` / 引理 `index_smul`

English:
lemma index_smul
  given: (a : G) (S : AddSubgroup A)
  statement: (a • S).index = S.index
  proof: index_map_of_bijective (MulAction.bijective _) _

中文:
引理 index_smul
  条件: (a : G) (S : 加法子群 A)
  结论: (a • S).index = S.index
  证明: index_map_of_bijective (MulAction.bijective _) _

Depends on / 依赖: MulAction, MulAction.bijective, bijective, index_map_of_bijective
-/
lemma index_smul (a : G) (S : AddSubgroup A) : (a • S).index = S.index :=
  index_map_of_bijective (MulAction.bijective _) _

end AddSubgroup
