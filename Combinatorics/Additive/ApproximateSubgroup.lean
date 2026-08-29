/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Additive.CovBySMul
public import Mathlib.Combinatorics.Additive.RuzsaCovering
public import Mathlib.Combinatorics.Additive.SmallTripling

/-!
# Approximate subgroups

This file defines approximate subgroups of a group, namely symmetric sets `A` such that `A * A` can
be covered by a small number of translates of `A`.

## Main results

Approximate subgroups are a central concept in additive combinatorics, as a natural weakening and
flexible substitute of genuine subgroups. As such, they share numerous properties with subgroups:
* `IsApproximateSubgroup.image`: Group homomorphisms send approximate subgroups to approximate
  subgroups
* `IsApproximateSubgroup.pow_inter_pow`: The intersection of (non-trivial powers of) two approximate
  subgroups is an approximate subgroup. Warning: The intersection of two approximate subgroups isn't
  an approximate subgroup in general.

Approximate subgroups are close qualitatively and quantitatively to other concepts in additive
combinatorics:
* `IsApproximateSubgroup.card_pow_le`: An approximate subgroup has small powers.
* `IsApproximateSubgroup.of_small_tripling`: A set of small tripling can be made an approximate
  subgroup by squaring.

It can be readily confirmed that approximate subgroups are a weakening of subgroups:
* `isApproximateSubgroup_one`: A 1-approximate subgroup is the same thing as a subgroup.
-/

public section

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : Real} {m n : Nat}

/--
Definition of `IsApproximateAddSubgroup` / `IsApproximateAddSubgroup` 的定义

English:
structure IsApproximateAddSubgroup
  parameters: {G : Type*} [AddGroup G] (K : Real) (A : Set G)
  axioms and operations (3):
    - zero_mem : 0 in A
    - neg_eq_self : -A = A
    - two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A

中文:
结构 是ApproximateAdd子群
  参数: {G : 类型} [加法群 G] (K : 实数) (A : 集合 G)
  公理与运算 (3 个):
    - zero_mem : 0 in A
    - neg_eq_self : -A = A
    - two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A
-/
structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (K : Real) (A : Set G) : Prop where
  zero_mem : 0 in A
  neg_eq_self : -A = A
  two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A * A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
@[to_additive]
/--
Definition of `IsApproximateSubgroup` / `IsApproximateSubgroup` 的定义

English:
structure IsApproximateSubgroup
  parameters: (K : Real) (A : Set G)
  axioms and operations (3):
    - one_mem : 1 in A
    - inv_eq_self : A⁻¹ = A
    - sq_covBySMul : CovBySMul G K (A ^ 2) A

中文:
结构 是Approximate子群
  参数: (K : 实数) (A : 集合 G)
  公理与运算 (3 个):
    - one_mem : 1 in A
    - inv_eq_self : A⁻¹ = A
    - sq_covBySMul : CovBySMul G K (A ^ 2) A
-/
structure IsApproximateSubgroup (K : Real) (A : Set G) : Prop where
  one_mem : 1 in A
  inv_eq_self : A⁻¹ = A
  sq_covBySMul : CovBySMul G K (A ^ 2) A

namespace IsApproximateSubgroup

/--
lemma `nonempty` / 引理 `nonempty`

English:
lemma nonempty
  given: (hA : IsApproximateSubgroup K A)
  statement: A.Nonempty
  proof: ⟨1, hA.one_mem⟩

@[to_additive one_le]

中文:
引理 nonempty
  条件: (hA : 是Approximate子群 K A)
  结论: A.非空
  证明: ⟨1, hA.one_mem⟩

@[to_additive one_le]

Depends on / 依赖: Denumerable, Primcodable, ofDenumerable
-/
@[to_additive] lemma nonempty (hA : IsApproximateSubgroup K A) : A.Nonempty := ⟨1, hA.one_mem⟩

@[to_additive one_le]
/--
lemma `one_le` / 引理 `one_le`

English:
lemma one_le
  given: (hA : IsApproximateSubgroup K A)
  statement: 1 <= K
  proof: by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  grw [← hF]
  have : F.Nonempty := by by_contra! rfl; simp [hA.nonempty.ne_empty] at hSF
  simpa

@[to_additive]

中文:
引理 one_le
  条件: (hA : 是Approximate子群 K A)
  结论: 1 <= K
  证明: by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  grw [← hF]
  have : F.Nonempty := by by_contra! rfl; simp [hA.nonempty.ne_empty] at hSF
  simpa

@[to_additive]

Depends on / 依赖: F.Nonempty, Nonempty, hA.nonempty.ne_empty, hA.sq_covBySMul, ne_empty, nonempty, sq_covBySMul
-/
lemma one_le (hA : IsApproximateSubgroup K A) : 1 <= K := by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  grw [← hF]
  have : F.Nonempty := by by_contra! rfl; simp [hA.nonempty.ne_empty] at hSF
  simpa

@[to_additive]
/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: (hKL : K <= L) (hA : IsApproximateSubgroup K A)
  statement: IsApproximateSubgroup L A where
  proof: hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]

中文:
引理 mono
  条件: (hKL : K <= L) (hA : 是Approximate子群 K A)
  结论: 是Approximate子群 L A where
  证明: hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]

Depends on / 依赖: hA.one_mem, one_mem
-/
lemma mono (hKL : K <= L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
  one_mem := hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]
/--
lemma `card_pow_le` / 引理 `card_pow_le`

English:
lemma card_pow_le
  given: [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G))
  proof: hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : Real) <= #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by lia)
      _ <= #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ <= #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_p

中文:
引理 card_pow_le
  条件: [DecidableEq G] {A : 有限集 G} (hA : 是Approximate子群 K (A : 集合 G))
  证明: hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : Real) <= #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by lia)
      _ <= #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ <= #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_p

Depends on / 依赖: hA.sq_covBySMul, sq_covBySMul
-/
lemma card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    forall {n}, #(A ^ n) <= K ^ (n - 1) * #A
  | 0 => by simpa using hA.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : Real) <= #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by lia)
      _ <= #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ <= #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_pow_le
      _ <= K ^ (n + 1) * #A := by gcongr

@[to_additive]
/--
lemma `card_mul_self_le` / 引理 `card_mul_self_le`

English:
lemma card_mul_self_le
  given: [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G))
  proof: by simpa [sq] using hA.card_pow_le (n := 2)

@[to_additive]

中文:
引理 card_mul_self_le
  条件: [DecidableEq G] {A : 有限集 G} (hA : 是Approximate子群 K (A : 集合 G))
  证明: by simpa [sq] using hA.card_pow_le (n := 2)

@[to_additive]

Depends on / 依赖: card_pow_le, hA.card_pow_le
-/
lemma card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    #(A * A) <= K * #A := by simpa [sq] using hA.card_pow_le (n := 2)

@[to_additive]
/--
lemma `image` / 引理 `image`

English:
lemma image
  statement: {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
  proof: ⟨1, hA.one_mem, map_one _⟩
  inv_eq_self := by simp [← Set.image_inv, hA.inv_eq_self]
  sq_covBySMul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.sq_covBySMul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : Real) <= #F := mod_cast F.card_image_le
        _ <= K := hF
    · sim

中文:
引理 像
  结论: {F H : 类型} [群 H] [函数状 F G H] [幺半群态射类 F G H] (f : F)
  证明: ⟨1, hA.one_mem, map_one _⟩
  inv_eq_self := by simp [← Set.image_inv, hA.inv_eq_self]
  sq_covBySMul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.sq_covBySMul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : Real) <= #F := mod_cast F.card_image_le
        _ <= K := hF
    · sim

Depends on / 依赖: hA.one_mem, map_one, one_mem
-/
lemma image {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup K (f '' A) where
  one_mem := ⟨1, hA.one_mem, map_one _⟩
  inv_eq_self := by simp [← Set.image_inv, hA.inv_eq_self]
  sq_covBySMul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.sq_covBySMul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : Real) <= #F := mod_cast F.card_image_le
        _ <= K := hF
    · simp only [← Set.image_pow, Finset.coe_image, ← Set.image_mul, smul_eq_mul] at hAF ⊢
      gcongr

@[to_additive]
/--
lemma `subgroup` / 引理 `subgroup`

English:
lemma subgroup
  given: {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S}
  proof: OneMemClass.one_mem H
  inv_eq_self := inv_coe_set
  sq_covBySMul := ⟨{1}, by simp⟩

中文:
引理 subgroup
  条件: {S : 类型} [集合状 S G] [子群类 S G] {H : S}
  证明: OneMemClass.one_mem H
  inv_eq_self := inv_coe_set
  sq_covBySMul := ⟨{1}, by simp⟩

Depends on / 依赖: OneMemClass, OneMemClass.one_mem, one_mem
-/
lemma subgroup {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S} :
    IsApproximateSubgroup 1 (H : Set G) where
  one_mem := OneMemClass.one_mem H
  inv_eq_self := inv_coe_set
  sq_covBySMul := ⟨{1}, by simp⟩

open Finset in
@[to_additive]
/--
lemma `of_small_tripling` / 引理 `of_small_tripling`

English:
lemma of_small_tripling
  statement: [DecidableEq G] {A : Finset G} (hA₁ : 1 in A) (hAsymm : A⁻¹ = A)
  proof: by rw [sq, ← one_mul 1]; exact Set.mul_mem_mul hA₁ hA₁
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  sq_covBySMul := by
    replace hA := calc (#(A ^ 4 * A) : Real)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ <= K ^ 3 * #A := small_pow_of_small_tripling (by lia) hA hAsymm
    have h

中文:
引理 of_small_tripling
  结论: [DecidableEq G] {A : 有限集 G} (hA₁ : 1 in A) (hAsymm : A⁻¹ = A)
  证明: by rw [sq, ← one_mul 1]; exact Set.mul_mem_mul hA₁ hA₁
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  sq_covBySMul := by
    replace hA := calc (#(A ^ 4 * A) : Real)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ <= K ^ 3 * #A := small_pow_of_small_tripling (by lia) hA hAsymm
    have h

Depends on / 依赖: A.Nonempty, Nonempty, Set.mul_mem_mul, coe_inv, div_eq_mul_inv, hAsymm, inv_eq_self, inv_pow, mul_assoc, mul_mem_mul, one_mul, pow_succ, replace, ruzsa_covering_mul, small_pow_of_small_tripling, sq_covBySMul
-/
lemma of_small_tripling [DecidableEq G] {A : Finset G} (hA₁ : 1 in A) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) <= K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) where
  one_mem := by rw [sq, ← one_mul 1]; exact Set.mul_mem_mul hA₁ hA₁
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  sq_covBySMul := by
    replace hA := calc (#(A ^ 4 * A) : Real)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ <= K ^ 3 * #A := small_pow_of_small_tripling (by lia) hA hAsymm
    have hA₀ : A.Nonempty := ⟨1, hA₁⟩
    obtain ⟨F, -, hF, hAF⟩ := ruzsa_covering_mul hA₀ hA
    exact ⟨F, hF, by norm_cast; simpa [div_eq_mul_inv, pow_succ, mul_assoc, hAsymm] using hAF⟩

open Set in
@[to_additive]
/--
lemma `pow_inter_pow_covBySMul_sq_inter_sq` / 引理 `pow_inter_pow_covBySMul_sq_inter_sq`

English:
lemma pow_inter_pow_covBySMul_sq_inter_sq
  proof: by
  classical
  obtain ⟨F₁, hF₁, hAF₁⟩ := hA.sq_covBySMul
  obtain ⟨F₂, hF₂, hBF₂⟩ := hB.sq_covBySMul
  have := hA.one_le
  choose f hf using exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul A B
  refine ⟨.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1)), ?_, ?_⟩
  · calc
      (#(.image₂ f (F₁ ^ (m 

中文:
引理 pow_inter_pow_covBySMul_sq_inter_sq
  证明: by
  classical
  obtain ⟨F₁, hF₁, hAF₁⟩ := hA.sq_covBySMul
  obtain ⟨F₂, hF₂, hBF₂⟩ := hB.sq_covBySMul
  have := hA.one_le
  choose f hf using exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul A B
  refine ⟨.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1)), ?_, ?_⟩
  · calc
      (#(.image₂ f (F₁ ^ (m 

Depends on / 依赖: Finset, Finset.card_image, Finset.card_pow_le, card_pow_le, classical, exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul, hA.one_le, hA.sq_covBySMul, hB.sq_covBySMul, mod_cast, one_le, sq_covBySMul
-/
lemma pow_inter_pow_covBySMul_sq_inter_sq
    (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 <= m) (hn : 2 <= n) :
    CovBySMul G (K ^ (m - 1) * L ^ (n - 1)) (A ^ m inter B ^ n) (A ^ 2 inter B ^ 2) := by
  classical
  obtain ⟨F₁, hF₁, hAF₁⟩ := hA.sq_covBySMul
  obtain ⟨F₂, hF₂, hBF₂⟩ := hB.sq_covBySMul
  have := hA.one_le
  choose f hf using exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul A B
  refine ⟨.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1)), ?_, ?_⟩
  · calc
      (#(.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) : Real)
      _ <= #(F₁ ^ (m - 1)) * #(F₂ ^ (n - 1)) := mod_cast Finset.card_image₂_le ..
      _ <= #F₁ ^ (m - 1) * #F₂ ^ (n - 1) := by gcongr <;> exact mod_cast Finset.card_pow_le
      _ <= K ^ (m - 1) * L ^ (n - 1) := by gcongr
  · calc
      A ^ m inter B ^ n subseteq (F₁ ^ (m - 1) * A) inter (F₂ ^ (n - 1) * B) := by
        gcongr <;> apply pow_subset_pow_mul_of_sq_subset_mul <;> norm_cast <;> lia
      _ = ⋃ (a in F₁ ^ (m - 1)) (b in F₂ ^ (n - 1)), a • A inter b • B := by
        simp_rw [← smul_eq_mul, ← iUnion_smul_set, iUnion₂_inter_iUnion₂]; norm_cast
      _ subseteq ⋃ (a in F₁ ^ (m - 1)) (b in F₂ ^ (n - 1)), f a b • (A⁻¹ * A inter (B⁻¹ * B)) := by
        gcongr; exact hf ..
      _ = (Finset.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) * (A ^ 2 inter B ^ 2) := by
        simp_rw [hA.inv_eq_self, hB.inv_eq_self, ← sq]
        rw [Finset.coe_image₂]; rw [← smul_eq_mul]; rw [← iUnion_smul_set]; rw [biUnion_image2]
        simp_rw [Finset.mem_coe]

open Set in
@[to_additive]
/--
lemma `pow_inter_pow` / 引理 `pow_inter_pow`

English:
lemma pow_inter_pow
  statement: (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 <= m)
  proof: ⟨Set.one_mem_pow hA.one_mem, Set.one_mem_pow hB.one_mem⟩
  inv_eq_self := by simp_rw [inter_inv, ← inv_pow, hA.inv_eq_self, hB.inv_eq_self]
  sq_covBySMul := by
    refine (hA.pow_inter_pow_covBySMul_sq_inter_sq hB (by lia) (by lia)).subset ?_
      (by gcongr; exacts [hA.one_mem, hB.one_mem])
    c

中文:
引理 pow_inter_pow
  结论: (hA : 是Approximate子群 K A) (hB : 是Approximate子群 L B) (hm : 2 <= m)
  证明: ⟨Set.one_mem_pow hA.one_mem, Set.one_mem_pow hB.one_mem⟩
  inv_eq_self := by simp_rw [inter_inv, ← inv_pow, hA.inv_eq_self, hB.inv_eq_self]
  sq_covBySMul := by
    refine (hA.pow_inter_pow_covBySMul_sq_inter_sq hB (by lia) (by lia)).subset ?_
      (by gcongr; exacts [hA.one_mem, hB.one_mem])
    c

Depends on / 依赖: Set.one_mem_pow, hA.one_mem, hB.one_mem, one_mem, one_mem_pow
-/
lemma pow_inter_pow (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 <= m)
    (hn : 2 <= n) :
    IsApproximateSubgroup (K ^ (2 * m - 1) * L ^ (2 * n - 1)) (A ^ m inter B ^ n) where
  one_mem := ⟨Set.one_mem_pow hA.one_mem, Set.one_mem_pow hB.one_mem⟩
  inv_eq_self := by simp_rw [inter_inv, ← inv_pow, hA.inv_eq_self, hB.inv_eq_self]
  sq_covBySMul := by
    refine (hA.pow_inter_pow_covBySMul_sq_inter_sq hB (by lia) (by lia)).subset ?_
      (by gcongr; exacts [hA.one_mem, hB.one_mem])
    calc
      (A ^ m inter B ^ n) ^ 2 subseteq (A ^ m) ^ 2 inter (B ^ n) ^ 2 := Set.inter_pow_subset
      _ = A ^ (2 * m) inter B ^ (2 * n) := by simp [pow_mul']

end IsApproximateSubgroup

open Set in
/-- A `1`-approximate subgroup is the same thing as a subgroup. -/
@[to_additive (attr := simp)
/-- A `1`-approximate subgroup is the same thing as a subgroup. -/]
/--
lemma `isApproximateSubgroup_one` / 引理 `isApproximateSubgroup_one`

English:
lemma isApproximateSubgroup_one
  given: {A : Set G}
  proof: by
    suffices A * A subseteq A from
      let H : Subgroup G :=
        { carrier := A
          one_mem' := hA.one_mem
          inv_mem' hx := by rwa [← hA.inv_eq_self, inv_mem_inv]
          mul_mem' hx hy := this (mul_mem_mul hx hy) }
      ⟨H, rfl⟩
    obtain ⟨x, hx⟩ : exists x : G, A * A sub

中文:
引理 isApproximateSubgroup_one
  条件: {A : 集合 G}
  证明: by
    suffices A * A subseteq A from
      let H : Subgroup G :=
        { carrier := A
          one_mem' := hA.one_mem
          inv_mem' hx := by rwa [← hA.inv_eq_self, inv_mem_inv]
          mul_mem' hx hy := this (mul_mem_mul hx hy) }
      ⟨H, rfl⟩
    obtain ⟨x, hx⟩ : exists x : G, A * A sub

Depends on / 依赖: Finset, Finset.card_le_one_iff_subset_singleton, Finset.coe_singleton, Finset.subset_singleton_iff, Nat.cast_le_one, Subgroup, card_le_one_iff_subset_singleton, carrier, cast_le_one, coe_singleton, hA.inv_eq_self, hA.nonempty.ne_empty, hA.one_mem, hA.sq_covBySMul, inv_eq_self, inv_mem, inv_mem_inv, mul_mem, mul_mem_mul, ne_empty
-/
lemma isApproximateSubgroup_one {A : Set G} :
    IsApproximateSubgroup 1 (A : Set G) ↔ exists H : Subgroup G, H = A where
  mp hA := by
    suffices A * A subseteq A from
      let H : Subgroup G :=
        { carrier := A
          one_mem' := hA.one_mem
          inv_mem' hx := by rwa [← hA.inv_eq_self, inv_mem_inv]
          mul_mem' hx hy := this (mul_mem_mul hx hy) }
      ⟨H, rfl⟩
    obtain ⟨x, hx⟩ : exists x : G, A * A subseteq x • A := by
      obtain ⟨K, hK, hKA⟩ := hA.sq_covBySMul
      simp only [Nat.cast_le_one, Finset.card_le_one_iff_subset_singleton,
        Finset.subset_singleton_iff] at hK
      obtain ⟨x, rfl | rfl⟩ := hK
      · simp [hA.nonempty.ne_empty] at hKA
      · rw [Finset.coe_singleton, singleton_smul, sq] at hKA
        use x
    have hx' : x⁻¹ • (A * A) subseteq A := by rwa [← subset_smul_set_iff]
    have hx_inv : x⁻¹ in A := by
      simpa using hx' (smul_mem_smul_set (mul_mem_mul hA.one_mem hA.one_mem))
    have hx_sq : x * x in A := by
      rw [← hA.inv_eq_self]
      simpa using hx' (smul_mem_smul_set (mul_mem_mul hx_inv hA.one_mem))
    calc A * A subseteq x • A := by assumption
      _ = x⁻¹ • (x * x) • A := by simp [smul_smul]
      _ subseteq x⁻¹ • (A • A) := smul_set_mono (smul_set_subset_smul hx_sq)
      _ subseteq A := hx'
  mpr := by rintro ⟨H, rfl⟩; exact .subgroup
