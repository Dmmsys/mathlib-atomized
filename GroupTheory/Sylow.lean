/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `Sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `Sylow.exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `IsPGroup.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `Sylow.card_eq_multiplicity`: The cardinality of a Sylow subgroup is `p ^ n`
  where `n` is the multiplicity of `p` in the group order.
* `Sylow.isPretransitive_of_finite`: a generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modEq_one`: a generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/

@[expose] public section


open MulAction Subgroup

section InfiniteSylow

variable (p : Nat) (G : Type*) [Group G]

/--
Definition of `Sylow` / `Sylow` 的定义

English:
structure Sylow
  parameters: extends Subgroup G
  extends: Subgroup G
  axioms and operations (2):
    - isPGroup' : IsPGroup p toSubgroup
    - is_maximal' : forall {Q : Subgroup G}, IsPGroup p Q -> toSubgroup <= Q -> Q = toSubgroup

中文:
结构 Sylow
  参数: extends Subgroup G
  继承: Subgroup G
  公理与运算 (2 个):
    - isPGroup' : IsPGroup p toSubgroup
    - is_maximal' : 对任意 {Q : Subgroup G}, IsPGroup p Q -> toSubgroup <= Q -> Q = toSubgroup
-/
structure Sylow extends Subgroup G where
  isPGroup' : IsPGroup p toSubgroup
  is_maximal' : forall {Q : Subgroup G}, IsPGroup p Q -> toSubgroup <= Q -> Q = toSubgroup

variable {p} {G}

namespace Sylow

attribute [coe] toSubgroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (Sylow p G) (Subgroup G)
  body: ⟨toSubgroup⟩

@[ext]

中文:
实例 :
  签名: CoeOut (Sylow p G) (Subgroup G)
  定义体: ⟨toSubgroup⟩

@[ext]

Depends on / 依赖: toSubgroup
-/
instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨toSubgroup⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {P Q : Sylow p G} (h : (P : Subgroup G) = Q)
  statement: P = Q
  proof: by cases P; cases Q; congr

中文:
定理 ext
  条件: {P Q : Sylow p G} (h : (P : Subgroup G) = Q)
  结论: P = Q
  证明: by cases P; cases Q; congr
-/
theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by cases P; cases Q; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Sylow p G) G
  body: (↑)
  coe_injective _ _ h := ext (SetLike.coe_injective h)

中文:
实例 :
  签名: SetLike (Sylow p G) G
  定义体: (↑)
  coe_injective _ _ h := ext (SetLike.coe_injective h)
-/
instance : SetLike (Sylow p G) G where
  coe := (↑)
  coe_injective _ _ h := ext (SetLike.coe_injective h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Sylow p G)
  body: .ofSetLike (Sylow p G) G

中文:
实例 :
  签名: PartialOrder (Sylow p G)
  定义体: .ofSetLike (Sylow p G) G

Depends on / 依赖: ofSetLike
-/
instance : PartialOrder (Sylow p G) := .ofSetLike (Sylow p G) G

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubgroupClass (Sylow p G) G
  body: Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

@[simp]

中文:
实例 :
  签名: SubgroupClass (Sylow p G) G
  定义体: Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

@[simp]

Depends on / 依赖: Subgroup, Subgroup.mul_mem, mul_mem
-/
instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

@[simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (P : Sylow p G)
  statement: (P : Subgroup G) = (P : Set G)
  proof: rfl

中文:
定理 coe_coe
  条件: (P : Sylow p G)
  结论: (P : Subgroup G) = (P : Set G)
  证明: rfl
-/
protected theorem coe_coe (P : Sylow p G) : (P : Subgroup G) = (P : Set G) :=
  rfl

/--
Definition of `_root_.IsPGroup.toSylow` / `_root_.IsPGroup.toSylow` 的定义

English:
definition _root_.IsPGroup.toSylow
  signature: [Fact p.Prime] {P : Subgroup G}
  body: { P with
    isPGroup' := hP1
    is_maximal' := by
      intro Q hQ hPQ
      have : P.FiniteIndex := ⟨fun h => hP2 (h ▸ (dvd_zero p))⟩
      obtain ⟨k, hk⟩ := (hQ.to_quotient (P.normalCore.subgroupOf Q)).exists_card_eq
      have h := hk ▸ Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out hP2
   

中文:
定义 _root_.IsPGroup.toSylow
  签名: [Fact p.Prime] {P : Subgroup G}
  定义体: { P with
    isPGroup' := hP1
    is_maximal' := by
      intro Q hQ hPQ
      have : P.FiniteIndex := ⟨fun h => hP2 (h ▸ (dvd_zero p))⟩
      obtain ⟨k, hk⟩ := (hQ.to_quotient (P.normalCore.subgroupOf Q)).exists_card_eq
      have h := hk ▸ Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out hP2
   

Depends on / 依赖: Fact.out, FiniteIndex, Nat.Prime.coprime_pow_of_not_dvd, Nat.eq_one_of_dvd_coprimes, P.FiniteIndex, P.normalCore.subgroupOf, P.normalCore_le, Subgroup, Subgroup.relIndex_dvd_index_of_le, Subgroup.relIndex_dvd_of_le_left, Subgroup.relIndex_eq_one.mp, coprime_pow_of_not_dvd, dvd_zero, eq_one_of_dvd_coprimes, exists_card_eq, hQ.to_quotient, isPGroup, is_maximal, le_antisymm, normalCore
-/
def _root_.IsPGroup.toSylow [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : Sylow p G :=
  { P with
    isPGroup' := hP1
    is_maximal' := by
      intro Q hQ hPQ
      have : P.FiniteIndex := ⟨fun h => hP2 (h ▸ (dvd_zero p))⟩
      obtain ⟨k, hk⟩ := (hQ.to_quotient (P.normalCore.subgroupOf Q)).exists_card_eq
      have h := hk ▸ Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out hP2
      exact le_antisymm (Subgroup.relIndex_eq_one.mp
        (Nat.eq_one_of_dvd_coprimes h (Subgroup.relIndex_dvd_index_of_le hPQ)
        (Subgroup.relIndex_dvd_of_le_left Q P.normalCore_le))) hPQ }

/--
theorem `_root_.IsPGroup.toSylow_coe` / 定理 `_root_.IsPGroup.toSylow_coe`

English:
theorem _root_.IsPGroup.toSylow_coe
  statement: [Fact p.Prime] {P : Subgroup G}
  proof: rfl

中文:
定理 _root_.IsPGroup.toSylow_coe
  结论: [Fact p.Prime] {P : Subgroup G}
  证明: rfl
-/
@[simp] theorem _root_.IsPGroup.toSylow_coe [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : (hP1.toSylow hP2) = P :=
  rfl

/--
theorem `_root_.IsPGroup.mem_toSylow` / 定理 `_root_.IsPGroup.mem_toSylow`

English:
theorem _root_.IsPGroup.mem_toSylow
  statement: [Fact p.Prime] {P : Subgroup G}
  proof: .rfl

中文:
定理 _root_.IsPGroup.mem_toSylow
  结论: [Fact p.Prime] {P : Subgroup G}
  证明: .rfl
-/
@[simp] theorem _root_.IsPGroup.mem_toSylow [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) {g : G} : g in hP1.toSylow hP2 ↔ g in P :=
  .rfl

/--
theorem `_root_.IsPGroup.le_sylow_of_normal` / 定理 `_root_.IsPGroup.le_sylow_of_normal`

English:
theorem _root_.IsPGroup.le_sylow_of_normal
  statement: {N : Subgroup G} [N.Normal] (h : IsPGroup p N)
  proof: sup_eq_right.mp H.is_maximal' (h.to_sup_of_normal_left H.isPGroup') le_sup_right

中文:
定理 _root_.IsPGroup.le_sylow_of_normal
  结论: {N : Subgroup G} [N.Normal] (h : IsPGroup p N)
  证明: sup_eq_right.mp H.is_maximal' (h.to_sup_of_normal_left H.isPGroup') le_sup_right

Depends on / 依赖: H.isPGroup, H.is_maximal, h.to_sup_of_normal_left, isPGroup, is_maximal, le_sup_right, sup_eq_right, sup_eq_right.mp, to_sup_of_normal_left
-/
theorem _root_.IsPGroup.le_sylow_of_normal {N : Subgroup G} [N.Normal] (h : IsPGroup p N)
    (H : Sylow p G) : N <= H :=
sup_eq_right.mp H.is_maximal' (h.to_sup_of_normal_left H.isPGroup') le_sup_right

/--
Definition of `ofCard` / `ofCard` 的定义

English:
definition ofCard
  signature: [Finite G] {p : Nat} [Fact p.Prime] (H : Subgroup G)
  body: (IsPGroup.of_card card_eq).toSylow (by
    rw [← mul_dvd_mul_iff_left (Nat.card_pos (α := H)).ne']; rw [card_mul_index]; rw [card_eq]; rw [← pow_succ]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out)

@[simp, norm_cast]

中文:
定义 ofCard
  签名: [Finite G] {p : 自然数} [Fact p.Prime] (H : Subgroup G)
  定义体: (IsPGroup.of_card card_eq).toSylow (by
    rw [← mul_dvd_mul_iff_left (Nat.card_pos (α := H)).ne']; rw [card_mul_index]; rw [card_eq]; rw [← pow_succ]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out)

@[simp, norm_cast]

Depends on / 依赖: Fact.out, IsPGroup, IsPGroup.of_card, Nat.card_pos, Nat.card_pos.ne, Nat.pow_succ_factorization_not_dvd, card_eq, card_mul_index, card_pos, mul_dvd_mul_iff_left, of_card, pow_succ, pow_succ_factorization_not_dvd, toSylow
-/
def ofCard [Finite G] {p : Nat} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : Sylow p G :=
  (IsPGroup.of_card card_eq).toSylow (by
    rw [← mul_dvd_mul_iff_left (Nat.card_pos (α := H)).ne']; rw [card_mul_index]; rw [card_eq]; rw [← pow_succ]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out)

@[simp, norm_cast]
/--
theorem `coe_ofCard` / 定理 `coe_ofCard`

English:
theorem coe_ofCard
  statement: [Finite G] {p : Nat} [Fact p.Prime] (H : Subgroup G)
  proof: rfl

中文:
定理 coe_ofCard
  结论: [Finite G] {p : 自然数} [Fact p.Prime] (H : Subgroup G)
  证明: rfl
-/
theorem coe_ofCard [Finite G] {p : Nat} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : ofCard H card_eq = H :=
  rfl

/--
theorem `eq_top_of_zero` / 定理 `eq_top_of_zero`

English:
theorem eq_top_of_zero
  given: (H : Sylow 0 G)
  statement: (H : Subgroup G) = ⊤
  proof: (H.is_maximal' (.zero _) le_top).symm

中文:
定理 eq_top_of_zero
  条件: (H : Sylow 0 G)
  结论: (H : Subgroup G) = ⊤
  证明: (H.is_maximal' (.zero _) le_top).symm

Depends on / 依赖: H.is_maximal, is_maximal, le_top, piCongrLeft
-/
theorem eq_top_of_zero (H : Sylow 0 G) : (H : Subgroup G) = ⊤ :=
  (H.is_maximal' (.zero _) le_top).symm

/--
theorem `eq_bot_of_one` / 定理 `eq_bot_of_one`

English:
theorem eq_bot_of_one
  given: (H : Sylow 1 G)
  statement: (H : Subgroup G) = ⊥
  proof: have := isPGroup_one_iff_subsingleton.mp H.isPGroup'
  eq_bot_of_subsingleton _

中文:
定理 eq_bot_of_one
  条件: (H : Sylow 1 G)
  结论: (H : Subgroup G) = ⊥
  证明: have := isPGroup_one_iff_subsingleton.mp H.isPGroup'
  eq_bot_of_subsingleton _

Depends on / 依赖: H.isPGroup, _symm_apply, apply_symm_apply, congr_arg_heq, e.apply_symm_apply, eqRec_heq_iff, eq_bot_of_subsingleton, heq_iff_eq, isPGroup, isPGroup_one_iff_subsingleton, isPGroup_one_iff_subsingleton.mp, piCongrLeft
-/
theorem eq_bot_of_one (H : Sylow 1 G) : (H : Subgroup G) = ⊥ :=
  have := isPGroup_one_iff_subsingleton.mp H.isPGroup'
  eq_bot_of_subsingleton _

/--
Definition of `equivProdPrimeFactors` / `equivProdPrimeFactors` 的定义

English:
definition equivProdPrimeFactors
  signature: (h : p != 0)
  body: { H with
.mp H.isPGroup', isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h
is_maximal' hQ := H.is_maximal' .mpr hQ } isPGroup_iff_isPGroup_prod_primeFactors h
  invFun H := { H with
.mpr H.isPGroup', isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h
is_maximal' hQ := H.is_maximal' .mp hQ 

中文:
定义 equivProdPrimeFactors
  签名: (h : p != 0)
  定义体: { H with
.mp H.isPGroup', isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h
is_maximal' hQ := H.is_maximal' .mpr hQ } isPGroup_iff_isPGroup_prod_primeFactors h
  invFun H := { H with
.mpr H.isPGroup', isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h
is_maximal' hQ := H.is_maximal' .mp hQ 
-/
def equivProdPrimeFactors (h : p != 0) : Sylow p G ≃ Sylow (p.primeFactors.prod id) G where
  toFun H := { H with
.mp H.isPGroup', isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h
is_maximal' hQ := H.is_maximal' .mpr hQ } isPGroup_iff_isPGroup_prod_primeFactors h
  invFun H := { H with
.mpr H.isPGroup', isPGroup' := isPGroup_iff_isPGroup_prod_primeFactors h
is_maximal' hQ := H.is_maximal' .mp hQ } isPGroup_iff_isPGroup_prod_primeFactors h
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
/--
theorem `coe_equivProdPrimeFactors_apply` / 定理 `coe_equivProdPrimeFactors_apply`

English:
theorem coe_equivProdPrimeFactors_apply
  given: (h : p != 0) (H : Sylow p G)
  proof: rfl

@[simp]

中文:
定理 coe_equivProdPrimeFactors_apply
  条件: (h : p != 0) (H : Sylow p G)
  证明: rfl

@[simp]
-/
theorem coe_equivProdPrimeFactors_apply (h : p != 0) (H : Sylow p G) :
    (equivProdPrimeFactors h H : Subgroup G) = H :=
  rfl

@[simp]
/--
theorem `coe_symm_equivProdPrimeFactors_apply` / 定理 `coe_symm_equivProdPrimeFactors_apply`

English:
theorem coe_symm_equivProdPrimeFactors_apply
  given: (h : p != 0) (H : Sylow (p.primeFactors.prod id) G)
  proof: rfl

中文:
定理 coe_symm_equivProdPrimeFactors_apply
  条件: (h : p != 0) (H : Sylow (p.primeFactors.prod id) G)
  证明: rfl
-/
theorem coe_symm_equivProdPrimeFactors_apply (h : p != 0) (H : Sylow (p.primeFactors.prod id) G) :
    (equivProdPrimeFactors h |>.symm H : Subgroup G) = H :=
  rfl

variable (P : Sylow p G)

variable {K : Type*} [Group K] (ϕ : K ->* G) {N : Subgroup G}

/--
Definition of `comapOfKerIsPGroup` / `comapOfKerIsPGroup` 的定义

English:
definition comapOfKerIsPGroup
  signature: (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range)
  body: { P.1.comap ϕ with
    isPGroup' := P.2.comap_of_ker_isPGroup ϕ hϕ
    is_maximal' := fun {Q} hQ hle => by
      show Q = P.1.comap ϕ
      rw [← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }

@[simp

中文:
定义 comapOfKerIsPGroup
  签名: (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range)
  定义体: { P.1.comap ϕ with
    isPGroup' := P.2.comap_of_ker_isPGroup ϕ hϕ
    is_maximal' := fun {Q} hQ hle => by
      show Q = P.1.comap ϕ
      rw [← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }

@[simp

Depends on / 依赖: comap_map_eq_self, comap_of_ker_isPGroup, ge_of_eq, hQ.map, isPGroup, is_maximal, ker_le_comap, le_trans, map_comap_eq_self, map_mono
-/
def comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range) : Sylow p K :=
  { P.1.comap ϕ with
    isPGroup' := P.2.comap_of_ker_isPGroup ϕ hϕ
    is_maximal' := fun {Q} hQ hle => by
      show Q = P.1.comap ϕ
      rw [← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }

@[simp]
/--
theorem `coe_comapOfKerIsPGroup` / 定理 `coe_comapOfKerIsPGroup`

English:
theorem coe_comapOfKerIsPGroup
  given: (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range)
  proof: rfl

中文:
定理 coe_comapOfKerIsPGroup
  条件: (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range)
  证明: rfl
-/
theorem coe_comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P <= ϕ.range) :
    P.comapOfKerIsPGroup ϕ hϕ h = P.comap ϕ :=
  rfl

/--
Definition of `comapOfInjective` / `comapOfInjective` 的定义

English:
definition comapOfInjective
  signature: (hϕ : Function.Injective ϕ) (h : P <= ϕ.range)
  body: P.comapOfKerIsPGroup ϕ (IsPGroup.ker_isPGroup_of_injective hϕ) h

@[simp]

中文:
定义 comapOfInjective
  签名: (hϕ : Function.Injective ϕ) (h : P <= ϕ.range)
  定义体: P.comapOfKerIsPGroup ϕ (IsPGroup.ker_isPGroup_of_injective hϕ) h

@[simp]

Depends on / 依赖: IsPGroup, IsPGroup.ker_isPGroup_of_injective, P.comapOfKerIsPGroup, comapOfKerIsPGroup, ker_isPGroup_of_injective
-/
def comapOfInjective (hϕ : Function.Injective ϕ) (h : P <= ϕ.range) : Sylow p K :=
  P.comapOfKerIsPGroup ϕ (IsPGroup.ker_isPGroup_of_injective hϕ) h

@[simp]
/--
theorem `coe_comapOfInjective` / 定理 `coe_comapOfInjective`

English:
theorem coe_comapOfInjective
  given: (hϕ : Function.Injective ϕ) (h : P <= ϕ.range)
  proof: rfl

中文:
定理 coe_comapOfInjective
  条件: (hϕ : Function.Injective ϕ) (h : P <= ϕ.range)
  证明: rfl
-/
theorem coe_comapOfInjective (hϕ : Function.Injective ϕ) (h : P <= ϕ.range) :
    P.comapOfInjective ϕ hϕ h = P.comap ϕ :=
  rfl

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (h : P <= N)
  body: P.comapOfInjective N.subtype Subtype.coe_injective (by rwa [range_subtype])

@[simp]

中文:
定义 subtype
  签名: (h : P <= N)
  定义体: P.comapOfInjective N.subtype Subtype.coe_injective (by rwa [range_subtype])

@[simp]
-/
protected def subtype (h : P <= N) : Sylow p N :=
  P.comapOfInjective N.subtype Subtype.coe_injective (by rwa [range_subtype])

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  given: (h : P <= N)
  statement: P.subtype h = subgroupOf P N
  proof: rfl

中文:
定理 coe_subtype
  条件: (h : P <= N)
  结论: P.subtype h = subgroupOf P N
  证明: rfl
-/
theorem coe_subtype (h : P <= N) : P.subtype h = subgroupOf P N :=
  rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  statement: {P Q : Sylow p G} {hP : P <= N} {hQ : Q <= N}
  proof: by
  rw [SetLike.ext_iff] at h ⊢
  exact fun g => ⟨fun hg => (h ⟨g, hP hg⟩).mp hg, fun hg => (h ⟨g, hQ hg⟩).mpr hg⟩

中文:
定理 subtype_injective
  结论: {P Q : Sylow p G} {hP : P <= N} {hQ : Q <= N}
  证明: by
  rw [SetLike.ext_iff] at h ⊢
  exact fun g => ⟨fun hg => (h ⟨g, hP hg⟩).mp hg, fun hg => (h ⟨g, hQ hg⟩).mpr hg⟩

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
theorem subtype_injective {P Q : Sylow p G} {hP : P <= N} {hQ : Q <= N}
    (h : P.subtype hP = Q.subtype hQ) : P = Q := by
  rw [SetLike.ext_iff] at h ⊢
  exact fun g => ⟨fun hg => (h ⟨g, hP hg⟩).mp hg, fun hg => (h ⟨g, hQ hg⟩).mpr hg⟩

end Sylow

/--
theorem `IsPGroup.exists_le_sylow` / 定理 `IsPGroup.exists_le_sylow`

English:
theorem IsPGroup.exists_le_sylow
  given: {P : Subgroup G} (hP : IsPGroup p P)
  statement: exists Q : Sylow p G, P <= Q
  proof: Exists.elim
    (zorn_le_nonempty₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{ carrier := ⋃ R : c, R
            one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩
            inv_mem' := fun {_} ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩
            mul_mem' := fun {_}

中文:
定理 IsPGroup.exists_le_sylow
  条件: {P : Subgroup G} (hP : IsPGroup p P)
  结论: 存在 Q : Sylow p G, P <= Q
  证明: Exists.elim
    (zorn_le_nonempty₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{ carrier := ⋃ R : c, R
            one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩
            inv_mem' := fun {_} ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩
            mul_mem' := fun {_}

Depends on / 依赖: Exists, Exists.elim, Exists.imp, IsPGroup, Q.one_mem, Subgroup, carrier, hc2.total, inv_mem, mul_mem, one_mem
-/
theorem IsPGroup.exists_le_sylow {P : Subgroup G} (hP : IsPGroup p P) : exists Q : Sylow p G, P <= Q :=
  Exists.elim
    (zorn_le_nonempty₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{ carrier := ⋃ R : c, R
            one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩
            inv_mem' := fun {_} ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩
            mul_mem' := fun {_} _ ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩ =>
              (hc2.total R.2 S.2).elim (fun T => ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) fun T =>
                ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩ },
          fun ⟨g, _, ⟨S, rfl⟩, hg⟩ => by
          refine Exists.imp (fun k hk => ?_) (hc1 S.2 ⟨g, hg⟩)
          rwa [Subtype.ext_iff, coe_pow] at hk ⊢, fun M hM _ hg => ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩)
      P hP)
    fun {Q} h => ⟨⟨Q, h.2.prop, h.2.eq_of_ge⟩, h.1⟩

namespace Sylow

/--
Instance `nonempty` / 实例 `nonempty`

English:
instance nonempty
  signature: : Nonempty (Sylow p G)
  body: IsPGroup.of_bot.exists_le_sylow.nonempty

中文:
实例 nonempty
  签名: : Nonempty (Sylow p G)
  定义体: IsPGroup.of_bot.exists_le_sylow.nonempty

Depends on / 依赖: IsPGroup, IsPGroup.of_bot.exists_le_sylow.nonempty, exists_le_sylow, nonempty, of_bot
-/
instance nonempty : Nonempty (Sylow p G) :=
  IsPGroup.of_bot.exists_le_sylow.nonempty

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (Sylow p G)
  body: Classical.inhabited_of_nonempty nonempty

中文:
实例 inhabited
  签名: : Inhabited (Sylow p G)
  定义体: Classical.inhabited_of_nonempty nonempty

Depends on / 依赖: Classical, Classical.inhabited_of_nonempty, inhabited_of_nonempty, nonempty
-/
noncomputable instance inhabited : Inhabited (Sylow p G) :=
  Classical.inhabited_of_nonempty nonempty

/--
theorem `exists_comap_eq_of_ker_isPGroup` / 定理 `exists_comap_eq_of_ker_isPGroup`

English:
theorem exists_comap_eq_of_ker_isPGroup
  statement: {H : Type*} [Group H] (P : Sylow p H) {f : H ->* G}
  proof: Exists.imp (fun Q hQ => P.3 (Q.2.comap_of_ker_isPGroup f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow

中文:
定理 exists_comap_eq_of_ker_isPGroup
  结论: {H : 类型} [Group H] (P : Sylow p H) {f : H ->* G}
  证明: Exists.imp (fun Q hQ => P.3 (Q.2.comap_of_ker_isPGroup f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow

Depends on / 依赖: Exists, Exists.imp, comap_of_ker_isPGroup, exists_le_sylow, map_le_iff_le_comap, map_le_iff_le_comap.mp
-/
theorem exists_comap_eq_of_ker_isPGroup {H : Type*} [Group H] (P : Sylow p H) {f : H ->* G}
    (hf : IsPGroup p f.ker) : exists Q : Sylow p G, Q.comap f = P :=
  Exists.imp (fun Q hQ => P.3 (Q.2.comap_of_ker_isPGroup f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow

/--
theorem `exists_comap_eq_of_injective` / 定理 `exists_comap_eq_of_injective`

English:
theorem exists_comap_eq_of_injective
  statement: {H : Type*} [Group H] (P : Sylow p H) {f : H ->* G}
  proof: P.exists_comap_eq_of_ker_isPGroup (IsPGroup.ker_isPGroup_of_injective hf)

中文:
定理 exists_comap_eq_of_injective
  结论: {H : 类型} [Group H] (P : Sylow p H) {f : H ->* G}
  证明: P.exists_comap_eq_of_ker_isPGroup (IsPGroup.ker_isPGroup_of_injective hf)

Depends on / 依赖: IsPGroup, IsPGroup.ker_isPGroup_of_injective, P.exists_comap_eq_of_ker_isPGroup, exists_comap_eq_of_ker_isPGroup, ker_isPGroup_of_injective
-/
theorem exists_comap_eq_of_injective {H : Type*} [Group H] (P : Sylow p H) {f : H ->* G}
    (hf : Function.Injective f) : exists Q : Sylow p G, Q.comap f = P :=
  P.exists_comap_eq_of_ker_isPGroup (IsPGroup.ker_isPGroup_of_injective hf)

/--
theorem `exists_comap_subtype_eq` / 定理 `exists_comap_subtype_eq`

English:
theorem exists_comap_subtype_eq
  given: {H : Subgroup G} (P : Sylow p H)
  proof: P.exists_comap_eq_of_injective Subtype.coe_injective

中文:
定理 exists_comap_subtype_eq
  条件: {H : Subgroup G} (P : Sylow p H)
  证明: P.exists_comap_eq_of_injective Subtype.coe_injective

Depends on / 依赖: P.exists_comap_eq_of_injective, Subtype, Subtype.coe_injective, coe_injective, exists_comap_eq_of_injective
-/
theorem exists_comap_subtype_eq {H : Subgroup G} (P : Sylow p H) :
    exists Q : Sylow p G, Q.comap H.subtype = P :=
  P.exists_comap_eq_of_injective Subtype.coe_injective

/--
theorem `iSup_of_normal` / 定理 `iSup_of_normal`

English:
theorem iSup_of_normal
  statement: {ι : Type*} (H : ι -> Subgroup G) [forall i, (H i).Normal]
  proof: have H' := Classical.arbitrary Sylow p G
H'.isPGroup'.to_le iSup_le (h · |>.le_sylow_of_normal H')

中文:
定理 iSup_of_normal
  结论: {ι : 类型} (H : ι -> Subgroup G) [对任意 i, (H i).Normal]
  证明: have H' := Classical.arbitrary Sylow p G
H'.isPGroup'.to_le iSup_le (h · |>.le_sylow_of_normal H')

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, iSup_le, isPGroup, le_sylow_of_normal, piCongr, piCongr_apply_apply, to_le
-/
theorem iSup_of_normal {ι : Type*} (H : ι -> Subgroup G) [forall i, (H i).Normal]
    (h : forall i, IsPGroup p (H i)) : IsPGroup p (⨆ i, H i : Subgroup G) :=
have H' := Classical.arbitrary Sylow p G
H'.isPGroup'.to_le iSup_le (h · |>.le_sylow_of_normal H')

/--
theorem `biSup_of_normal` / 定理 `biSup_of_normal`

English:
theorem biSup_of_normal
  statement: {ι : Type*} (s : Set ι) (H : ι -> Subgroup G) (h : forall i in s, IsPGroup p (H i))
  proof: by
  rw [← iSup_subtype'']
  have : forall i : s, (H i).Normal := fun i => hn i i.property
  exact iSup_of_normal _ fun i => h i i.property

中文:
定理 biSup_of_normal
  结论: {ι : 类型} (s : Set ι) (H : ι -> Subgroup G) (h : 对任意 i in s, IsPGroup p (H i))
  证明: by
  rw [← iSup_subtype'']
  have : forall i : s, (H i).Normal := fun i => hn i i.property
  exact iSup_of_normal _ fun i => h i i.property

Depends on / 依赖: Normal, i.property, iSup_of_normal, iSup_subtype, property
-/
theorem biSup_of_normal {ι : Type*} (s : Set ι) (H : ι -> Subgroup G) (h : forall i in s, IsPGroup p (H i))
    (hn : forall i in s, (H i).Normal) : IsPGroup p (⨆ i in s, H i : Subgroup G) := by
  rw [← iSup_subtype'']
  have : forall i : s, (H i).Normal := fun i => hn i i.property
  exact iSup_of_normal _ fun i => h i i.property

/--
theorem `sSup_of_normal` / 定理 `sSup_of_normal`

English:
theorem sSup_of_normal
  statement: (Hs : Set (Subgroup G)) (h : forall H in Hs, IsPGroup p H)
  proof: by
  rw [sSup_eq_iSup]
  exact biSup_of_normal Hs id h hn

中文:
定理 sSup_of_normal
  结论: (Hs : Set (Subgroup G)) (h : 对任意 H in Hs, IsPGroup p H)
  证明: by
  rw [sSup_eq_iSup]
  exact biSup_of_normal Hs id h hn

Depends on / 依赖: biSup_of_normal, sSup_eq_iSup
-/
theorem sSup_of_normal (Hs : Set (Subgroup G)) (h : forall H in Hs, IsPGroup p H)
    (hn : forall H in Hs, H.Normal) : IsPGroup p (sSup Hs : Subgroup G) := by
  rw [sSup_eq_iSup]
  exact biSup_of_normal Hs id h hn

/--
theorem `finite_of_ker_is_pGroup` / 定理 `finite_of_ker_is_pGroup`

English:
theorem finite_of_ker_is_pGroup
  statement: {H : Type*} [Group H] {f : H ->* G}
  proof: let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_isPGroup hf
  let g : Sylow p H -> Sylow p G := fun P => Classical.choose (h_exists P)
  have hg : forall P : Sylow p H, (g P).1.comap f = P := fun P => Classical.choose_spec (h_exists P)
  Finite.of_injective g fun P Q h => ext (by rw [←

中文:
定理 finite_of_ker_is_pGroup
  结论: {H : 类型} [Group H] {f : H ->* G}
  证明: let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_isPGroup hf
  let g : Sylow p H -> Sylow p G := fun P => Classical.choose (h_exists P)
  have hg : forall P : Sylow p H, (g P).1.comap f = P := fun P => Classical.choose_spec (h_exists P)
  Finite.of_injective g fun P Q h => ext (by rw [←

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Finite, Finite.of_injective, P.exists_comap_eq_of_ker_isPGroup, choose_spec, exists_comap_eq_of_ker_isPGroup, h_exists, of_injective
-/
theorem finite_of_ker_is_pGroup {H : Type*} [Group H] {f : H ->* G}
    (hf : IsPGroup p f.ker) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_isPGroup hf
  let g : Sylow p H -> Sylow p G := fun P => Classical.choose (h_exists P)
  have hg : forall P : Sylow p H, (g P).1.comap f = P := fun P => Classical.choose_spec (h_exists P)
  Finite.of_injective g fun P Q h => ext (by rw [← hg, h]; exact (h_exists Q).choose_spec)

/--
theorem `finite_of_injective` / 定理 `finite_of_injective`

English:
theorem finite_of_injective
  statement: {H : Type*} [Group H] {f : H ->* G}
  proof: finite_of_ker_is_pGroup (IsPGroup.ker_isPGroup_of_injective hf)

中文:
定理 finite_of_injective
  结论: {H : 类型} [Group H] {f : H ->* G}
  证明: finite_of_ker_is_pGroup (IsPGroup.ker_isPGroup_of_injective hf)

Depends on / 依赖: IsPGroup, IsPGroup.ker_isPGroup_of_injective, finite_of_ker_is_pGroup, ker_isPGroup_of_injective
-/
theorem finite_of_injective {H : Type*} [Group H] {f : H ->* G}
    (hf : Function.Injective f) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_ker_is_pGroup (IsPGroup.ker_isPGroup_of_injective hf)

/-- If `H` is a subgroup of `G`, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
instance (H : Subgroup G) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_injective H.subtype_injective

/--
theorem `finite_of_finiteIndex` / 定理 `finite_of_finiteIndex`

English:
theorem finite_of_finiteIndex
  given: (P : Sylow p G) [P.FiniteIndex]
  statement: Finite (Sylow p G)
  proof: by
  apply finite_of_ker_is_pGroup (f := QuotientGroup.mk' P.normalCore)
  rw [QuotientGroup.ker_mk']
  exact P.isPGroup'.to_le P.normalCore_le

中文:
定理 finite_of_finiteIndex
  条件: (P : Sylow p G) [P.FiniteIndex]
  结论: Finite (Sylow p G)
  证明: by
  apply finite_of_ker_is_pGroup (f := QuotientGroup.mk' P.normalCore)
  rw [QuotientGroup.ker_mk']
  exact P.isPGroup'.to_le P.normalCore_le

Depends on / 依赖: P.isPGroup, P.normalCore, P.normalCore_le, QuotientGroup, QuotientGroup.ker_mk, QuotientGroup.mk, finite_of_ker_is_pGroup, isPGroup, ker_mk, normalCore, normalCore_le, to_le
-/
theorem finite_of_finiteIndex (P : Sylow p G) [P.FiniteIndex] : Finite (Sylow p G) := by
  apply finite_of_ker_is_pGroup (f := QuotientGroup.mk' P.normalCore)
  rw [QuotientGroup.ker_mk']
  exact P.isPGroup'.to_le P.normalCore_le

open scoped Pointwise

/--
Instance `pointwiseMulAction` / 实例 `pointwiseMulAction`

English:
instance pointwiseMulAction
  signature: {α : Type*} [Group α] [MulDistribMulAction α G]
  body: ⟨g • P.toSubgroup, P.2.map _, fun {Q} hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· in g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul P := ext (one_smul α P.toSu

中文:
实例 pointwiseMulAction
  签名: {α : 类型} [Group α] [MulDistribMulAction α G]
  定义体: ⟨g • P.toSubgroup, P.2.map _, fun {Q} hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· in g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul P := ext (one_smul α P.toSu

Depends on / 依赖: P.toSubgroup, congr_arg, hQ.map, inv_smul_eq_iff, inv_smul_eq_iff.mp, inv_smul_smul, mul_smul, one_smul, smul_mem_pointwise_smul, toSubgroup
-/
instance pointwiseMulAction {α : Type*} [Group α] [MulDistribMulAction α G] :
    MulAction α (Sylow p G) where
  smul g P :=
    ⟨g • P.toSubgroup, P.2.map _, fun {Q} hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· in g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul P := ext (one_smul α P.toSubgroup)
  mul_smul g h P := ext (mul_smul g h P.toSubgroup)

/--
theorem `pointwise_smul_def` / 定理 `pointwise_smul_def`

English:
theorem pointwise_smul_def
  statement: {α : Type*} [Group α] [MulDistribMulAction α G] {g : α}
  proof: rfl

中文:
定理 pointwise_smul_def
  结论: {α : 类型} [Group α] [MulDistribMulAction α G] {g : α}
  证明: rfl
-/
theorem pointwise_smul_def {α : Type*} [Group α] [MulDistribMulAction α G] {g : α}
    {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G) :=
  rfl

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: : MulAction G (Sylow p G)
  body: compHom _ MulAut.conj

中文:
实例 mulAction
  签名: : MulAction G (Sylow p G)
  定义体: compHom _ MulAut.conj

Depends on / 依赖: MulAut, MulAut.conj, compHom
-/
instance mulAction : MulAction G (Sylow p G) :=
  compHom _ MulAut.conj

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: {g : G} {P : Sylow p G}
  statement: g • P = MulAut.conj g • P
  proof: rfl

中文:
定理 smul_def
  条件: {g : G} {P : Sylow p G}
  结论: g • P = MulAut.conj g • P
  证明: rfl
-/
theorem smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P :=
  rfl

/--
theorem `coe_subgroup_smul` / 定理 `coe_subgroup_smul`

English:
theorem coe_subgroup_smul
  given: {g : G} {P : Sylow p G}
  proof: rfl

中文:
定理 coe_subgroup_smul
  条件: {g : G} {P : Sylow p G}
  证明: rfl
-/
theorem coe_subgroup_smul {g : G} {P : Sylow p G} :
    ↑(g • P) = MulAut.conj g • (P : Subgroup G) :=
  rfl

/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: {g : G} {P : Sylow p G}
  statement: ↑(g • P) = MulAut.conj g • (P : Set G)
  proof: rfl

中文:
定理 coe_smul
  条件: {g : G} {P : Sylow p G}
  结论: ↑(g • P) = MulAut.conj g • (P : Set G)
  证明: rfl
-/
theorem coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G) :=
  rfl

/--
theorem `smul_le` / 定理 `smul_le`

English:
theorem smul_le
  given: {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H)
  statement: ↑(h • P) <= H
  proof: Subgroup.conj_smul_le_of_le hP h

中文:
定理 smul_le
  条件: {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H)
  结论: ↑(h • P) <= H
  证明: Subgroup.conj_smul_le_of_le hP h

Depends on / 依赖: Subgroup, Subgroup.conj_smul_le_of_le, conj_smul_le_of_le
-/
theorem smul_le {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H) : ↑(h • P) <= H :=
  Subgroup.conj_smul_le_of_le hP h

/--
theorem `smul_subtype` / 定理 `smul_subtype`

English:
theorem smul_subtype
  given: {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H)
  proof: ext (Subgroup.conj_smul_subgroupOf hP h)

中文:
定理 smul_subtype
  条件: {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H)
  证明: ext (Subgroup.conj_smul_subgroupOf hP h)

Depends on / 依赖: Subgroup, Subgroup.conj_smul_subgroupOf, conj_smul_subgroupOf
-/
theorem smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : P <= H) (h : H) :
    h • P.subtype hP = (h • P).subtype (smul_le hP h) :=
  ext (Subgroup.conj_smul_subgroupOf hP h)

/--
theorem `smul_eq_iff_mem_normalizer` / 定理 `smul_eq_iff_mem_normalizer`

English:
theorem smul_eq_iff_mem_normalizer
  given: {g : G} {P : Sylow p G}
  proof: by
  rw [eq_comm]; rw [SetLike.ext_iff]; rw [← inv_mem_iff (G := G) (H := normalizer P)]; rw [mem_set_normalizer_iff]; rw [inv_inv]
  exact
    forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh, Mul

中文:
定理 smul_eq_iff_mem_normalizer
  条件: {g : G} {P : Sylow p G}
  证明: by
  rw [eq_comm]; rw [SetLike.ext_iff]; rw [← inv_mem_iff (G := G) (H := normalizer P)]; rw [mem_set_normalizer_iff]; rw [inv_inv]
  exact
    forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh, Mul

Depends on / 依赖: Iff.rfl, MulAut, MulAut.apply_inv_self, MulAut.conj, SetLike, SetLike.ext_iff, apply_inv_self, eq_comm, ext_iff, forall_congr, iff_congr, inv_inv, inv_mem_iff, mem_set_normalizer_iff, mul_assoc, normalizer
-/
theorem smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} :
    g • P = P ↔ g in normalizer P := by
  rw [eq_comm]; rw [SetLike.ext_iff]; rw [← inv_mem_iff (G := G) (H := normalizer P)]; rw [mem_set_normalizer_iff]; rw [inv_inv]
  exact
    forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh, MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩

/--
theorem `smul_eq_of_normal` / 定理 `smul_eq_of_normal`

English:
theorem smul_eq_of_normal
  given: {g : G} {P : Sylow p G} [h : P.Normal]
  statement: g • P = P
  proof: by
  simp only [smul_eq_iff_mem_normalizer, ← P.coe_coe, P.normalizer_eq_top, mem_top]

中文:
定理 smul_eq_of_normal
  条件: {g : G} {P : Sylow p G} [h : P.Normal]
  结论: g • P = P
  证明: by
  simp only [smul_eq_iff_mem_normalizer, ← P.coe_coe, P.normalizer_eq_top, mem_top]

Depends on / 依赖: P.coe_coe, P.normalizer_eq_top, coe_coe, mem_top, normalizer_eq_top, smul_eq_iff_mem_normalizer
-/
theorem smul_eq_of_normal {g : G} {P : Sylow p G} [h : P.Normal] : g • P = P := by
  simp only [smul_eq_iff_mem_normalizer, ← P.coe_coe, P.normalizer_eq_top, mem_top]

end Sylow

/--
theorem `Subgroup.sylow_mem_fixedPoints_iff` / 定理 `Subgroup.sylow_mem_fixedPoints_iff`

English:
theorem Subgroup.sylow_mem_fixedPoints_iff
  given: (H : Subgroup G) {P : Sylow p G}
  proof: by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer]; exact Subtype.forall

中文:
定理 Subgroup.sylow_mem_fixedPoints_iff
  条件: (H : Subgroup G) {P : Sylow p G}
  证明: by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer]; exact Subtype.forall

Depends on / 依赖: SetLike, SetLike.le_def, Subtype, Subtype.forall, Sylow.smul_eq_iff_mem_normalizer, le_def, simp_rw, smul_eq_iff_mem_normalizer
-/
theorem Subgroup.sylow_mem_fixedPoints_iff (H : Subgroup G) {P : Sylow p G} :
    P in fixedPoints H (Sylow p G) ↔ H <= normalizer P := by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer]; exact Subtype.forall

/--
theorem `IsPGroup.inf_normalizer_sylow` / 定理 `IsPGroup.inf_normalizer_sylow`

English:
theorem IsPGroup.inf_normalizer_sylow
  given: {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G)
  proof: le_antisymm
    (le_inf inf_le_left
      (sup_eq_right.mp
        (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)

中文:
定理 IsPGroup.inf_normalizer_sylow
  条件: {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G)
  证明: le_antisymm
    (le_inf inf_le_left
      (sup_eq_right.mp
        (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)

Depends on / 依赖: hP.to_inf_left.to_sup_of_normal_right, inf_le_inf_left, inf_le_left, inf_le_right, le_antisymm, le_inf, le_normalizer, le_sup_right, sup_eq_right, sup_eq_right.mp, to_inf_left, to_sup_of_normal_right
-/
theorem IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G) :
    P ⊓ normalizer Q = P ⊓ Q :=
  le_antisymm
    (le_inf inf_le_left
      (sup_eq_right.mp
        (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)

/--
theorem `IsPGroup.sylow_mem_fixedPoints_iff` / 定理 `IsPGroup.sylow_mem_fixedPoints_iff`

English:
theorem IsPGroup.sylow_mem_fixedPoints_iff
  given: {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G}
  proof: by
  rw [P.sylow_mem_fixedPoints_iff]; rw [← inf_eq_left]; rw [hP.inf_normalizer_sylow]; rw [inf_eq_left]

中文:
定理 IsPGroup.sylow_mem_fixedPoints_iff
  条件: {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G}
  证明: by
  rw [P.sylow_mem_fixedPoints_iff]; rw [← inf_eq_left]; rw [hP.inf_normalizer_sylow]; rw [inf_eq_left]

Depends on / 依赖: P.sylow_mem_fixedPoints_iff, hP.inf_normalizer_sylow, inf_eq_left, inf_normalizer_sylow, sylow_mem_fixedPoints_iff
-/
theorem IsPGroup.sylow_mem_fixedPoints_iff {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} :
    Q in fixedPoints P (Sylow p G) ↔ P <= Q := by
  rw [P.sylow_mem_fixedPoints_iff]; rw [← inf_eq_left]; rw [hP.inf_normalizer_sylow]; rw [inf_eq_left]

/--
Instance `Sylow.isPretransitive_of_finite` / 实例 `Sylow.isPretransitive_of_finite`

English:
instance Sylow.isPretransitive_of_finite
  signature: [hp : Fact p.Prime] [Finite (Sylow p G)]
  body: ⟨fun P Q => by
    have H := fun {R : Sylow p G} {S : orbit G P} =>
      calc
        S in fixedPoints R (orbit G P) ↔ S.1 in fixedPoints R (Sylow p G) :=
          forall_congr' fun a => Subtype.ext_iff
        _ ↔ R.1 <= S := R.2.sylow_mem_fixedPoints_iff
        _ ↔ S.1.1 = R := ⟨fun h => R.3 S.

中文:
实例 Sylow.isPretransitive_of_finite
  签名: [hp : Fact p.Prime] [Finite (Sylow p G)]
  定义体: ⟨fun P Q => by
    have H := fun {R : Sylow p G} {S : orbit G P} =>
      calc
        S in fixedPoints R (orbit G P) ↔ S.1 in fixedPoints R (Sylow p G) :=
          forall_congr' fun a => Subtype.ext_iff
        _ ↔ R.1 <= S := R.2.sylow_mem_fixedPoints_iff
        _ ↔ S.1.1 = R := ⟨fun h => R.3 S.

Depends on / 依赖: Exists, Exists.elim, H.mp, Nat.modEq_, Nonempty, Set.Nonempty, Subtype, Subtype.ext_iff, Sylow.ext, ext_iff, fixedPoints, forall_congr, ge_of_eq, hp.out.not_dvd_one, modEq_, nonempty_fixed_point_of_prime_not_dvd_card, not_dvd_one, sylow_mem_fixedPoints_iff
-/
instance Sylow.isPretransitive_of_finite [hp : Fact p.Prime] [Finite (Sylow p G)] :
    IsPretransitive G (Sylow p G) :=
  ⟨fun P Q => by
    have H := fun {R : Sylow p G} {S : orbit G P} =>
      calc
        S in fixedPoints R (orbit G P) ↔ S.1 in fixedPoints R (Sylow p G) :=
          forall_congr' fun a => Subtype.ext_iff
        _ ↔ R.1 <= S := R.2.sylow_mem_fixedPoints_iff
        _ ↔ S.1.1 = R := ⟨fun h => R.3 S.1.2 h, ge_of_eq⟩
    suffices Set.Nonempty (fixedPoints Q (orbit G P)) by
      exact Exists.elim this fun R hR => by
        rw [← Sylow.ext (H.mp hR)]
        exact R.2
    apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card
    refine fun h => hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.mp ?_)
    calc
      1 = Nat.card (fixedPoints P (orbit G P)) := ?_
      _ ≡ Nat.card (orbit G P) [MOD p] := (P.2.card_modEq_card_fixedPoints (orbit G P)).symm
      _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
    rw [← Nat.card_unique (α := ({⟨P]; rw [mem_orbit_self P⟩} : Set (orbit G P)))]; rw [eq_comm]
    congr
    rw [Set.eq_singleton_iff_unique_mem]
    exact ⟨H.mpr rfl, fun R h => Subtype.ext (Sylow.ext (H.mp h))⟩⟩

variable (p) (G)

/--
theorem `card_sylow_modEq_one` / 定理 `card_sylow_modEq_one`

English:
theorem card_sylow_modEq_one
  given: [Fact p.Prime] [Finite (Sylow p G)]
  proof: by
  refine Sylow.nonempty.elim fun P : Sylow p G => ?_
  have : fixedPoints P.1 (Sylow p G) = {P} :=
    Set.ext fun Q : Sylow p G =>
      calc
        Q in fixedPoints P (Sylow p G) ↔ P.1 <= Q := P.2.sylow_mem_fixedPoints_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q in {P} := Sy

中文:
定理 card_sylow_modEq_one
  条件: [Fact p.Prime] [Finite (Sylow p G)]
  证明: by
  refine Sylow.nonempty.elim fun P : Sylow p G => ?_
  have : fixedPoints P.1 (Sylow p G) = {P} :=
    Set.ext fun Q : Sylow p G =>
      calc
        Q in fixedPoints P (Sylow p G) ↔ P.1 <= Q := P.2.sylow_mem_fixedPoints_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q in {P} := Sy

Depends on / 依赖: Nat.card, Set.ext, Set.mem_singleton_iff.symm, Sylow.ext_iff.symm.trans, Sylow.nonempty.elim, card_modEq_card_fixedPoints, ext_iff, fixedPoints, ge_of_eq, mem_singleton_iff, nonempty, sylow_mem_fixedPoints_iff
-/
theorem card_sylow_modEq_one [Fact p.Prime] [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  refine Sylow.nonempty.elim fun P : Sylow p G => ?_
  have : fixedPoints P.1 (Sylow p G) = {P} :=
    Set.ext fun Q : Sylow p G =>
      calc
        Q in fixedPoints P (Sylow p G) ↔ P.1 <= Q := P.2.sylow_mem_fixedPoints_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q in {P} := Sylow.ext_iff.symm.trans Set.mem_singleton_iff.symm
  have : Nat.card (fixedPoints P.1 (Sylow p G)) = 1 := by simp [this]
  exact (P.2.card_modEq_card_fixedPoints (Sylow p G)).trans (by rw [this])

/--
theorem `not_dvd_card_sylow` / 定理 `not_dvd_card_sylow`

English:
theorem not_dvd_card_sylow
  given: [hp : Fact p.Prime] [Finite (Sylow p G)]
  statement: ¬p ∣ Nat.card (Sylow p G)
  proof: fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modEq_iff_dvd' zero_le_one).mp
        ((Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p G))))

中文:
定理 not_dvd_card_sylow
  条件: [hp : Fact p.Prime] [Finite (Sylow p G)]
  结论: ¬p ∣ 自然数.card (Sylow p G)
  证明: fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modEq_iff_dvd' zero_le_one).mp
        ((Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p G))))

Depends on / 依赖: Nat.dvd_one.mp, Nat.modEq_iff_dvd, Nat.modEq_zero_iff_dvd.mpr, card_sylow_modEq_one, dvd_one, modEq_iff_dvd, modEq_zero_iff_dvd, ne_one, symm.trans, zero_le_one
-/
theorem not_dvd_card_sylow [hp : Fact p.Prime] [Finite (Sylow p G)] : ¬p ∣ Nat.card (Sylow p G) :=
  fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modEq_iff_dvd' zero_le_one).mp
        ((Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p G))))

variable {p} {G}

namespace Sylow

/-- Sylow subgroups are isomorphic -/
nonrec def equivSMul (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  equivSMul (MulAut.conj g) P.toSubgroup

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G)
  body: by
  rw [← Classical.choose_spec (exists_smul_eq G P Q)]
  exact P.equivSMul (Classical.choose (exists_smul_eq G P Q))

@[simp]

中文:
定义 equiv
  签名: [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G)
  定义体: by
  rw [← Classical.choose_spec (exists_smul_eq G P Q)]
  exact P.equivSMul (Classical.choose (exists_smul_eq G P Q))

@[simp]

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, P.equivSMul, _update, choose_spec, e.piCongrLeft, equivSMul, exists_smul_eq, piCongrLeft, symm_apply_eq
-/
noncomputable def equiv [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) : P ≃* Q := by
  rw [← Classical.choose_spec (exists_smul_eq G P Q)]
  exact P.equivSMul (Classical.choose (exists_smul_eq G P Q))

@[simp]
/--
theorem `orbit_eq_top` / 定理 `orbit_eq_top`

English:
theorem orbit_eq_top
  given: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  statement: orbit G P = ⊤
  proof: top_le_iff.mp fun Q _ => exists_smul_eq G P Q

中文:
定理 orbit_eq_top
  条件: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  结论: orbit G P = ⊤
  证明: top_le_iff.mp fun Q _ => exists_smul_eq G P Q

Depends on / 依赖: exists_smul_eq, top_le_iff, top_le_iff.mp
-/
theorem orbit_eq_top [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : orbit G P = ⊤ :=
  top_le_iff.mp fun Q _ => exists_smul_eq G P Q

/--
theorem `stabilizer_eq_normalizer` / 定理 `stabilizer_eq_normalizer`

English:
theorem stabilizer_eq_normalizer
  given: (P : Sylow p G)
  proof: by
  ext; simp [smul_eq_iff_mem_normalizer]

中文:
定理 stabilizer_eq_normalizer
  条件: (P : Sylow p G)
  证明: by
  ext; simp [smul_eq_iff_mem_normalizer]

Depends on / 依赖: smul_eq_iff_mem_normalizer
-/
theorem stabilizer_eq_normalizer (P : Sylow p G) :
    stabilizer G P = normalizer P := by
  ext; simp [smul_eq_iff_mem_normalizer]

/--
theorem `conj_eq_normalizer_conj_of_mem_centralizer` / 定理 `conj_eq_normalizer_conj_of_mem_centralizer`

English:
theorem conj_eq_normalizer_conj_of_mem_centralizer
  statement: [Fact p.Prime] [Finite (Sylow p G)]
  proof: by
  have h1 : P <= centralizer (zpowers x : Set G) := by rwa [le_centralizer_iff, zpowers_le]
  have h2 : ↑(g • P) <= centralizer (zpowers x : Set G) := by
    rw [le_centralizer_iff]; rw [zpowers_le]
    rintro - ⟨z, hz, rfl⟩
    specialize hy z hz
    rwa [← mul_assoc, ← eq_mul_inv_iff_mul_eq, mu

中文:
定理 conj_eq_normalizer_conj_of_mem_centralizer
  结论: [Fact p.Prime] [Finite (Sylow p G)]
  证明: by
  have h1 : P <= centralizer (zpowers x : Set G) := by rwa [le_centralizer_iff, zpowers_le]
  have h2 : ↑(g • P) <= centralizer (zpowers x : Set G) := by
    rw [le_centralizer_iff]; rw [zpowers_le]
    rintro - ⟨z, hz, rfl⟩
    specialize hy z hz
    rwa [← mul_assoc, ← eq_mul_inv_iff_mul_eq, mu

Depends on / 依赖: P.subtype, centralizer, eq_inv_mul_iff_mul_eq, eq_mul_inv_iff_mul_eq, exists_smul_eq, le_centralizer_iff, mul_assoc, simp_rw, smul_subt, specialize, subtype, zpowers, zpowers_le
-/
theorem conj_eq_normalizer_conj_of_mem_centralizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) (x g : G) (hx : x in centralizer P)
    (hy : g⁻¹ * x * g in centralizer P) :
    exists n in normalizer P, g⁻¹ * x * g = n⁻¹ * x * n := by
  have h1 : P <= centralizer (zpowers x : Set G) := by rwa [le_centralizer_iff, zpowers_le]
  have h2 : ↑(g • P) <= centralizer (zpowers x : Set G) := by
    rw [le_centralizer_iff]; rw [zpowers_le]
    rintro - ⟨z, hz, rfl⟩
    specialize hy z hz
    rwa [← mul_assoc, ← eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc,
      eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc] at hy
  obtain ⟨h, hh⟩ :=
    exists_smul_eq (centralizer (zpowers x : Set G)) ((g • P).subtype h2) (P.subtype h1)
  simp_rw [smul_subtype, Subgroup.smul_def, smul_smul] at hh
  refine ⟨h * g, smul_eq_iff_mem_normalizer.mp (subtype_injective hh), ?_⟩
  rw [← mul_assoc]; rw [Commute.right_comm (h.prop x (mem_zpowers x))]; rw [mul_inv_rev]; rw [inv_mul_cancel_right]

/--
theorem `conj_eq_normalizer_conj_of_mem` / 定理 `conj_eq_normalizer_conj_of_mem`

English:
theorem conj_eq_normalizer_conj_of_mem
  statement: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  proof: P.conj_eq_normalizer_conj_of_mem_centralizer x g
    (P.le_centralizer hx) (P.le_centralizer hy)

中文:
定理 conj_eq_normalizer_conj_of_mem
  结论: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  证明: P.conj_eq_normalizer_conj_of_mem_centralizer x g
    (P.le_centralizer hx) (P.le_centralizer hy)

Depends on / 依赖: P.conj_eq_normalizer_conj_of_mem_centralizer, P.le_centralizer, conj_eq_normalizer_conj_of_mem_centralizer, le_centralizer
-/
theorem conj_eq_normalizer_conj_of_mem [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    [_hP : IsMulCommutative P] (x g : G) (hx : x in P) (hy : g⁻¹ * x * g in P) :
    exists n in normalizer P, g⁻¹ * x * g = n⁻¹ * x * n :=
  P.conj_eq_normalizer_conj_of_mem_centralizer x g
    (P.le_centralizer hx) (P.le_centralizer hy)

/--
Definition of `equivQuotientNormalizer` / `equivQuotientNormalizer` 的定义

English:
definition equivQuotientNormalizer
  signature: [Fact p.Prime] [Finite (Sylow p G)]
  body: calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equiv.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := Equiv.setCongr P.orbit_eq_top.symm
    _ ≃ G ⧸ stabilizer G P := orbitEquivQuotientStabilizer G P
    _ ≃ G ⧸ normalizer P := by rw [P.stabilizer_eq_normalizer]

中文:
定义 equivQuotientNormalizer
  签名: [Fact p.Prime] [Finite (Sylow p G)]
  定义体: calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equiv.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := Equiv.setCongr P.orbit_eq_top.symm
    _ ≃ G ⧸ stabilizer G P := orbitEquivQuotientStabilizer G P
    _ ≃ G ⧸ normalizer P := by rw [P.stabilizer_eq_normalizer]

Depends on / 依赖: Equiv.Set.univ, Equiv.setCongr, P.orbit_eq_top.symm, P.stabilizer_eq_normalizer, normalizer, orbitEquivQuotientStabilizer, orbit_eq_top, setCongr, stabilizer, stabilizer_eq_normalizer
-/
noncomputable def equivQuotientNormalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Sylow p G ≃ G ⧸ normalizer P :=
  calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equiv.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := Equiv.setCongr P.orbit_eq_top.symm
    _ ≃ G ⧸ stabilizer G P := orbitEquivQuotientStabilizer G P
    _ ≃ G ⧸ normalizer P := by rw [P.stabilizer_eq_normalizer]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fact
  signature: p.Prime] [Finite (Sylow p G)] (P
  body: Finite.of_equiv (Sylow p G) P.equivQuotientNormalizer

中文:
实例 [Fact
  签名: p.Prime] [Finite (Sylow p G)] (P
  定义体: Finite.of_equiv (Sylow p G) P.equivQuotientNormalizer

Depends on / 依赖: Finite, Finite.of_equiv, P.equivQuotientNormalizer, equivQuotientNormalizer, of_equiv
-/
instance [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Finite (G ⧸ normalizer P) :=
  Finite.of_equiv (Sylow p G) P.equivQuotientNormalizer

/--
theorem `card_eq_card_quotient_normalizer` / 定理 `card_eq_card_quotient_normalizer`

English:
theorem card_eq_card_quotient_normalizer
  statement: [Fact p.Prime] [Finite (Sylow p G)]
  proof: Nat.card_congr P.equivQuotientNormalizer

中文:
定理 card_eq_card_quotient_normalizer
  结论: [Fact p.Prime] [Finite (Sylow p G)]
  证明: Nat.card_congr P.equivQuotientNormalizer

Depends on / 依赖: Nat.card_congr, P.equivQuotientNormalizer, card_congr, equivQuotientNormalizer
-/
theorem card_eq_card_quotient_normalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Nat.card (Sylow p G) = Nat.card (G ⧸ normalizer P) :=
  Nat.card_congr P.equivQuotientNormalizer

/--
theorem `card_eq_index_normalizer` / 定理 `card_eq_index_normalizer`

English:
theorem card_eq_index_normalizer
  given: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  proof: P.card_eq_card_quotient_normalizer

中文:
定理 card_eq_index_normalizer
  条件: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  证明: P.card_eq_card_quotient_normalizer

Depends on / 依赖: P.card_eq_card_quotient_normalizer, card_eq_card_quotient_normalizer
-/
theorem card_eq_index_normalizer [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) = (normalizer (P : Set G)).index :=
  P.card_eq_card_quotient_normalizer

/--
theorem `card_dvd_index` / 定理 `card_dvd_index`

English:
theorem card_dvd_index
  given: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  proof: ((congr_arg _ P.card_eq_index_normalizer).mp dvd_rfl).trans
    (index_dvd_of_le le_normalizer)

中文:
定理 card_dvd_index
  条件: [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  证明: ((congr_arg _ P.card_eq_index_normalizer).mp dvd_rfl).trans
    (index_dvd_of_le le_normalizer)

Depends on / 依赖: P.card_eq_index_normalizer, card_eq_index_normalizer, congr_arg, dvd_rfl, index_dvd_of_le, le_normalizer
-/
theorem card_dvd_index [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.index :=
  ((congr_arg _ P.card_eq_index_normalizer).mp dvd_rfl).trans
    (index_dvd_of_le le_normalizer)

/--
theorem `not_dvd_index_aux` / 定理 `not_dvd_index_aux`

English:
theorem not_dvd_index_aux
  statement: [hp : Fact p.Prime] (P : Sylow p G) [P.Normal]
  proof: by
  intro h
  rw [P.index_eq_card] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ (P : Subgroup G)) p h
  have h := IsPGroup.of_card (((Nat.card_zpowers x).trans hx).trans (pow_one p).symm)
  let Q := (zpowers x).comap (QuotientGroup.mk' (P : Subgroup G))
  have hQ : IsPGroup p Q

中文:
定理 not_dvd_index_aux
  结论: [hp : Fact p.Prime] (P : Sylow p G) [P.Normal]
  证明: by
  intro h
  rw [P.index_eq_card] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ (P : Subgroup G)) p h
  have h := IsPGroup.of_card (((Nat.card_zpowers x).trans hx).trans (pow_one p).symm)
  let Q := (zpowers x).comap (QuotientGroup.mk' (P : Subgroup G))
  have hQ : IsPGroup p Q
-/
private theorem not_dvd_index_aux [hp : Fact p.Prime] (P : Sylow p G) [P.Normal]
    [P.FiniteIndex] : ¬ p ∣ P.index := by
  intro h
  rw [P.index_eq_card] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ (P : Subgroup G)) p h
  have h := IsPGroup.of_card (((Nat.card_zpowers x).trans hx).trans (pow_one p).symm)
  let Q := (zpowers x).comap (QuotientGroup.mk' (P : Subgroup G))
  have hQ : IsPGroup p Q := by
    apply h.comap_of_ker_isPGroup
    rw [QuotientGroup.ker_mk']
    exact P.2
  replace hp := mt orderOf_eq_one_iff.mpr (ne_of_eq_of_ne hx hp.1.ne_one)
  rw [← zpowers_eq_bot]; rw [← Ne]; rw [← bot_lt_iff_ne_bot]; rw [←
    comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective _)]; rw [MonoidHom.comap_bot]; rw [QuotientGroup.ker_mk'] at hp
  exact hp.ne' (P.3 hQ hp.le)

/--
theorem `not_dvd_index'` / 定理 `not_dvd_index'`

English:
theorem not_dvd_index'
  statement: [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  proof: by
  rw [← relIndex_mul_index le_normalizer]; rw [P.coe_coe]; rw [← card_eq_index_normalizer]
  have : (P.subtype le_normalizer).Normal :=
    Subgroup.normal_in_normalizer
  have : (P.subtype le_normalizer).FiniteIndex := ⟨hP⟩
  replace hP := not_dvd_index_aux (P.subtype le_normalizer)
  exact hp.1

中文:
定理 not_dvd_index'
  结论: [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  证明: by
  rw [← relIndex_mul_index le_normalizer]; rw [P.coe_coe]; rw [← card_eq_index_normalizer]
  have : (P.subtype le_normalizer).Normal :=
    Subgroup.normal_in_normalizer
  have : (P.subtype le_normalizer).FiniteIndex := ⟨hP⟩
  replace hP := not_dvd_index_aux (P.subtype le_normalizer)
  exact hp.1

Depends on / 依赖: EquivLike, EquivLike.toEquiv, FiniteIndex, Normal, P.coe_coe, P.subtype, Subgroup, Subgroup.normal_in_normalizer, card_eq_index_normalizer, coe_coe, le_normalizer, normal_in_normalizer, not_dvd_card_sylow, not_dvd_index_aux, not_dvd_mul, relIndex_mul_index, replace, subtype, toEquiv
-/
theorem not_dvd_index' [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hP : P.relIndex (normalizer P) != 0) : ¬ p ∣ P.index := by
  rw [← relIndex_mul_index le_normalizer]; rw [P.coe_coe]; rw [← card_eq_index_normalizer]
  have : (P.subtype le_normalizer).Normal :=
    Subgroup.normal_in_normalizer
  have : (P.subtype le_normalizer).FiniteIndex := ⟨hP⟩
  replace hP := not_dvd_index_aux (P.subtype le_normalizer)
  exact hp.1.not_dvd_mul hP (not_dvd_card_sylow p G)

/--
theorem `not_dvd_index` / 定理 `not_dvd_index`

English:
theorem not_dvd_index
  given: [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex]
  proof: by
  have := P.finite_of_finiteIndex
  exact P.not_dvd_index' Nat.card_pos.ne'

中文:
定理 not_dvd_index
  条件: [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex]
  证明: by
  have := P.finite_of_finiteIndex
  exact P.not_dvd_index' Nat.card_pos.ne'

Depends on / 依赖: Nat.card_pos.ne, P.finite_of_finiteIndex, P.not_dvd_index, card_pos, finite_of_finiteIndex, not_dvd_index
-/
theorem not_dvd_index [Fact p.Prime] (P : Sylow p G) [P.FiniteIndex] :
    ¬ p ∣ P.index := by
  have := P.finite_of_finiteIndex
  exact P.not_dvd_index' Nat.card_pos.ne'

section mapSurjective

variable [Finite G] {G' : Type*} [Group G'] {f : G ->* G'} (hf : Function.Surjective f)

/--
Definition of `mapSurjective` / `mapSurjective` 的定义

English:
definition mapSurjective
  signature: [Fact p.Prime] (P : Sylow p G)
  body: { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := fun hQ hPQ => ((P.2.map f).toSylow
      (fun h => P.not_dvd_index (h.trans (P.index_map_dvd hf)))).3 hQ hPQ }

中文:
定义 mapSurjective
  签名: [Fact p.Prime] (P : Sylow p G)
  定义体: { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := fun hQ hPQ => ((P.2.map f).toSylow
      (fun h => P.not_dvd_index (h.trans (P.index_map_dvd hf)))).3 hQ hPQ }

Depends on / 依赖: P.index_map_dvd, P.not_dvd_index, h.trans, index_map_dvd, isPGroup, is_maximal, not_dvd_index, toSylow
-/
def mapSurjective [Fact p.Prime] (P : Sylow p G) : Sylow p G' :=
  { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := fun hQ hPQ => ((P.2.map f).toSylow
      (fun h => P.not_dvd_index (h.trans (P.index_map_dvd hf)))).3 hQ hPQ }

/--
theorem `coe_mapSurjective` / 定理 `coe_mapSurjective`

English:
theorem coe_mapSurjective
  given: [Fact p.Prime] (P : Sylow p G)
  statement: P.mapSurjective hf = P.map f
  proof: rfl

中文:
定理 coe_mapSurjective
  条件: [Fact p.Prime] (P : Sylow p G)
  结论: P.mapSurjective hf = P.map f
  证明: rfl
-/
@[simp] theorem coe_mapSurjective [Fact p.Prime] (P : Sylow p G) : P.mapSurjective hf = P.map f :=
  rfl

/--
theorem `mapSurjective_surjective` / 定理 `mapSurjective_surjective`

English:
theorem mapSurjective_surjective
  given: (p : Nat) [Fact p.Prime]
  proof: by
  have : Finite G' := Finite.of_surjective f hf
  intro P
  let Q₀ : Sylow p (P.comap f) := Sylow.nonempty.some
  let Q : Subgroup G := Q₀.map (P.comap f).subtype
  have hPQ : Q.map f <= P := Subgroup.map_le_iff_le_comap.mpr (Subgroup.map_subtype_le Q₀.1)
  have hpQ : IsPGroup p Q := Q₀.2.map (P.

中文:
定理 mapSurjective_surjective
  条件: (p : 自然数) [Fact p.Prime]
  证明: by
  have : Finite G' := Finite.of_surjective f hf
  intro P
  let Q₀ : Sylow p (P.comap f) := Sylow.nonempty.some
  let Q : Subgroup G := Q₀.map (P.comap f).subtype
  have hPQ : Q.map f <= P := Subgroup.map_le_iff_le_comap.mpr (Subgroup.map_subtype_le Q₀.1)
  have hpQ : IsPGroup p Q := Q₀.2.map (P.

Depends on / 依赖: Fact.out, Finite, Finite.of_surjective, IsPGroup, Nat.Prime.not_dvd_mul, P.comap, P.index_comap_of_surjective, P.not_dvd_index, Q.index, Q.map, Subgroup, Subgroup.index_map_subtype, Subgroup.map_le_iff_le_comap.mpr, Subgroup.map_subtype_le, Sylow.nonempty.some, hpQ.toSylow, index_comap_of_surjective, index_map_subtype, map_le_iff_le_comap, map_subtype_le
-/
theorem mapSurjective_surjective (p : Nat) [Fact p.Prime] :
    Function.Surjective (Sylow.mapSurjective hf : Sylow p G -> Sylow p G') := by
  have : Finite G' := Finite.of_surjective f hf
  intro P
  let Q₀ : Sylow p (P.comap f) := Sylow.nonempty.some
  let Q : Subgroup G := Q₀.map (P.comap f).subtype
  have hPQ : Q.map f <= P := Subgroup.map_le_iff_le_comap.mpr (Subgroup.map_subtype_le Q₀.1)
  have hpQ : IsPGroup p Q := Q₀.2.map (P.comap f).subtype
  have hQ : ¬ p ∣ Q.index := by
    rw [Subgroup.index_map_subtype Q₀.1]; rw [P.index_comap_of_surjective hf]
    exact Nat.Prime.not_dvd_mul Fact.out Q₀.not_dvd_index P.not_dvd_index
  use hpQ.toSylow hQ
  rw [Sylow.ext_iff]; rw [Sylow.coe_mapSurjective]; rw [eq_comm]
  exact ((hpQ.map f).toSylow (fun h => hQ (h.trans (Q.index_map_dvd hf)))).3 P.2 hPQ

end mapSurjective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `normalizer_sup_eq_top` / 定理 `normalizer_sup_eq_top`

English:
theorem normalizer_sup_eq_top
  statement: {p : Nat} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  proof: by
  refine top_le_iff.mp fun g _ => ?_
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_left (↑n) g]; rw [sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [smul_def]; rw [← mul_smul]; rw [← MulAut.conjNormal_val]; rw [← MulAut.conjNormal.map_mul

中文:
定理 normalizer_sup_eq_top
  结论: {p : 自然数} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  证明: by
  refine top_le_iff.mp fun g _ => ?_
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_left (↑n) g]; rw [sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [smul_def]; rw [← mul_smul]; rw [← MulAut.conjNormal_val]; rw [← MulAut.conjNormal.map_mul

Depends on / 依赖: Function, Function.Injective, Injective, MulAut, MulAut.conj, MulAut.conjNormal, MulAut.conjNormal.map_mul, MulAut.conjNormal_val, N.inv_mem, Subgroup, Subgroup.pointwise_smul_def, Sylow.ext_iff, conjNormal, conjNormal_val, exists_smul_eq, ext_iff, injective, inv_mem, inv_mul_cancel_left, map_mul
-/
theorem normalizer_sup_eq_top {p : Nat} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p N) :
    normalizer (P.map N.subtype) ⊔ N = ⊤ := by
  refine top_le_iff.mp fun g _ => ?_
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_left (↑n) g]; rw [sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [smul_def]; rw [← mul_smul]; rw [← MulAut.conjNormal_val]; rw [← MulAut.conjNormal.map_mul]; rw [Sylow.ext_iff]; rw [pointwise_smul_def]; rw [Subgroup.pointwise_smul_def] at hn
  have : Function.Injective (MulAut.conj (n * g)).toMonoidHom := (MulAut.conj (n * g)).injective
  refine fun x => (mem_map_iff_mem this).symm.trans ?_
  rw [map_map]; rw [← congr_arg (map N.subtype) hn]; rw [map_map]
  rfl

/--
theorem `normalizer_sup_eq_top'` / 定理 `normalizer_sup_eq_top'`

English:
theorem normalizer_sup_eq_top'
  statement: {p : Nat} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  proof: by
  rw [← normalizer_sup_eq_top (P.subtype hP)]; rw [P.coe_subtype]; rw [subgroupOf_map_subtype]; rw [inf_of_le_left hP]; rw [P.coe_coe]

中文:
定理 normalizer_sup_eq_top'
  结论: {p : 自然数} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  证明: by
  rw [← normalizer_sup_eq_top (P.subtype hP)]; rw [P.coe_subtype]; rw [subgroupOf_map_subtype]; rw [inf_of_le_left hP]; rw [P.coe_coe]

Depends on / 依赖: P.coe_coe, P.coe_subtype, P.subtype, coe_coe, coe_subtype, e.symm, inf_of_le_left, normalizer_sup_eq_top, subgroupOf_map_subtype, subtype
-/
theorem normalizer_sup_eq_top' {p : Nat} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p G) (hP : P <= N) : normalizer P ⊔ N = ⊤ := by
  rw [← normalizer_sup_eq_top (P.subtype hP)]; rw [P.coe_subtype]; rw [subgroupOf_map_subtype]; rw [inf_of_le_left hP]; rw [P.coe_coe]

end Sylow

end InfiniteSylow

open Equiv Equiv.Perm Finset Function List QuotientGroup

universe u

variable {G : Type u} [Group G]

/--
theorem `QuotientGroup.card_preimage_mk` / 定理 `QuotientGroup.card_preimage_mk`

English:
theorem QuotientGroup.card_preimage_mk
  given: (s : Subgroup G) (t : Set (G ⧸ s))
  proof: by
  rw [← Nat.card_prod]; rw [Nat.card_congr (preimageMkEquivSubgroupProdSet _ _)]

中文:
定理 QuotientGroup.card_preimage_mk
  条件: (s : Subgroup G) (t : Set (G ⧸ s))
  证明: by
  rw [← Nat.card_prod]; rw [Nat.card_congr (preimageMkEquivSubgroupProdSet _ _)]

Depends on / 依赖: Nat.card_congr, Nat.card_prod, card_congr, card_prod, preimageMkEquivSubgroupProdSet
-/
theorem QuotientGroup.card_preimage_mk (s : Subgroup G) (t : Set (G ⧸ s)) :
    Nat.card (QuotientGroup.mk ⁻¹' t) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod]; rw [Nat.card_congr (preimageMkEquivSubgroupProdSet _ _)]

namespace Sylow
/--
theorem `mem_fixedPoints_mul_left_cosets_iff_mem_normalizer` / 定理 `mem_fixedPoints_mul_left_cosets_iff_mem_normalizer`

English:
theorem mem_fixedPoints_mul_left_cosets_iff_mem_normalizer
  statement: {H : Subgroup G} [Finite (H : Set G)]
  proof: ⟨fun hx =>
    have ha : forall {y : G ⧸ H}, y in orbit H (x : G ⧸ H) -> y = x := mem_fixedPoints'.1 hx _
    (inv_mem_iff (G := G)).1
      (mem_normalizer_fintype fun n (hn : n in H) =>
        have : (n⁻¹ * x)⁻¹ * x in H := QuotientGroup.eq.1 (ha ⟨⟨n⁻¹, inv_mem hn⟩, rfl⟩)
        show _ in H by
 

中文:
定理 mem_fixedPoints_mul_left_cosets_iff_mem_normalizer
  结论: {H : Subgroup G} [Finite (H : Set G)]
  证明: ⟨fun hx =>
    have ha : forall {y : G ⧸ H}, y in orbit H (x : G ⧸ H) -> y = x := mem_fixedPoints'.1 hx _
    (inv_mem_iff (G := G)).1
      (mem_normalizer_fintype fun n (hn : n in H) =>
        have : (n⁻¹ * x)⁻¹ * x in H := QuotientGroup.eq.1 (ha ⟨⟨n⁻¹, inv_mem hn⟩, rfl⟩)
        show _ in H by
 

Depends on / 依赖: Quotient, Quotient.inductionOn, QuotientGroup, QuotientGroup.eq, convert, inductionOn, inv_inv, inv_mem, inv_mem_iff, mem_fixedPoints, mem_normalizer_fintype, mul_inv_rev
-/
theorem mem_fixedPoints_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Finite (H : Set G)]
    {x : G} : (x : G ⧸ H) in MulAction.fixedPoints H (G ⧸ H) ↔ x in normalizer H :=
  ⟨fun hx =>
    have ha : forall {y : G ⧸ H}, y in orbit H (x : G ⧸ H) -> y = x := mem_fixedPoints'.1 hx _
    (inv_mem_iff (G := G)).1
      (mem_normalizer_fintype fun n (hn : n in H) =>
        have : (n⁻¹ * x)⁻¹ * x in H := QuotientGroup.eq.1 (ha ⟨⟨n⁻¹, inv_mem hn⟩, rfl⟩)
        show _ in H by
          rw [mul_inv_rev]; rw [inv_inv] at this
          convert! this
          rw [inv_inv]),
    fun hx : forall n : G, n in H ↔ x * n * x⁻¹ in H =>
    mem_fixedPoints'.2 fun y =>
      Quotient.inductionOn' y fun y hy =>
        QuotientGroup.eq.2
          (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy
          have hb₂ : (b * x)⁻¹ * y in H := QuotientGroup.eq.1 hb₂
(inv_mem_iff (G := G)).1
(hx _).2
(mul_mem_cancel_left (inv_mem hb₁)).1 by
                rw [hx] at hb₂; simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

/--
Definition of `fixedPointsMulLeftCosetsEquivQuotient` / `fixedPointsMulLeftCosetsEquivQuotient` 的定义

English:
definition fixedPointsMulLeftCosetsEquivQuotient
  signature: (H : Subgroup G) [Finite (H : Set G)]
  body: @subtypeQuotientEquivQuotientSubtype G (· in normalizer H) (_) (_)
    (· in MulAction.fixedPoints H (G ⧸ H))
    (fun _ => (@mem_fixedPoints_mul_left_cosets_iff_mem_normalizer _ _ _ ‹_› _).symm)
    (by
      intros
      unfold_projs
      rw [leftRel_apply (α := normalizer (H : Set G))]; rw [left

中文:
定义 fixedPointsMulLeftCosetsEquivQuotient
  签名: (H : Subgroup G) [Finite (H : Set G)]
  定义体: @subtypeQuotientEquivQuotientSubtype G (· in normalizer H) (_) (_)
    (· in MulAction.fixedPoints H (G ⧸ H))
    (fun _ => (@mem_fixedPoints_mul_left_cosets_iff_mem_normalizer _ _ _ ‹_› _).symm)
    (by
      intros
      unfold_projs
      rw [leftRel_apply (α := normalizer (H : Set G))]; rw [left

Depends on / 依赖: MulAction, MulAction.fixedPoints, fixedPoints, intros, leftRel_apply, mem_fixedPoints_mul_left_cosets_iff_mem_normalizer, normalizer, subtypeQuotientEquivQuotientSubtype, unfold_projs
-/
def fixedPointsMulLeftCosetsEquivQuotient (H : Subgroup G) [Finite (H : Set G)] :
    MulAction.fixedPoints H (G ⧸ H) ≃
      normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype :=
  @subtypeQuotientEquivQuotientSubtype G (· in normalizer H) (_) (_)
    (· in MulAction.fixedPoints H (G ⧸ H))
    (fun _ => (@mem_fixedPoints_mul_left_cosets_iff_mem_normalizer _ _ _ ‹_› _).symm)
    (by
      intros
      unfold_projs
      rw [leftRel_apply (α := normalizer (H : Set G))]; rw [leftRel_apply]
      rfl)

/--
theorem `card_quotient_normalizer_modEq_card_quotient` / 定理 `card_quotient_normalizer_modEq_card_quotient`

English:
theorem card_quotient_normalizer_modEq_card_quotient
  statement: [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime]
  proof: by
  rw [← Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H)]
  exact ((IsPGroup.of_card hH).card_modEq_card_fixedPoints _).symm

中文:
定理 card_quotient_normalizer_modEq_card_quotient
  结论: [Finite G] {p : 自然数} {n : 自然数} [hp : Fact p.Prime]
  证明: by
  rw [← Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H)]
  exact ((IsPGroup.of_card hH).card_modEq_card_fixedPoints _).symm

Depends on / 依赖: IsPGroup, IsPGroup.of_card, Nat.card_congr, card_congr, card_modEq_card_fixedPoints, fixedPointsMulLeftCosetsEquivQuotient, of_card
-/
theorem card_quotient_normalizer_modEq_card_quotient [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime]
    {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    Nat.card (normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype) ≡
      Nat.card (G ⧸ H) [MOD p] := by
  rw [← Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H)]
  exact ((IsPGroup.of_card hH).card_modEq_card_fixedPoints _).symm

/--
theorem `card_normalizer_modEq_card` / 定理 `card_normalizer_modEq_card`

English:
theorem card_normalizer_modEq_card
  statement: [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime] {H : Subgroup G}
  proof: by
  have : H.subgroupOf (normalizer H) ≃ H := (subgroupOfEquivOfLe le_normalizer).toEquiv
  rw [card_eq_card_quotient_mul_card_subgroup H]; rw [card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (normalizer H))]; rw [Nat.card_congr this]; rw [hH]; rw [pow_succ']
  exact (card_quotient_normalizer

中文:
定理 card_normalizer_modEq_card
  结论: [Finite G] {p : 自然数} {n : 自然数} [hp : Fact p.Prime] {H : Subgroup G}
  证明: by
  have : H.subgroupOf (normalizer H) ≃ H := (subgroupOfEquivOfLe le_normalizer).toEquiv
  rw [card_eq_card_quotient_mul_card_subgroup H]; rw [card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (normalizer H))]; rw [Nat.card_congr this]; rw [hH]; rw [pow_succ']
  exact (card_quotient_normalizer

Depends on / 依赖: H.subgroupOf, Nat.card_congr, card_congr, card_eq_card_quotient_mul_card_subgroup, card_quotient_normalizer_modEq_card_quotient, le_normalizer, mul_right, normalizer, pow_succ, subgroupOf, subgroupOfEquivOfLe, toEquiv
-/
theorem card_normalizer_modEq_card [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Nat.card H = p ^ n) :
    Nat.card (normalizer (H : Set G)) ≡ Nat.card G [MOD p ^ (n + 1)] := by
  have : H.subgroupOf (normalizer H) ≃ H := (subgroupOfEquivOfLe le_normalizer).toEquiv
  rw [card_eq_card_quotient_mul_card_subgroup H]; rw [card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (normalizer H))]; rw [Nat.card_congr this]; rw [hH]; rw [pow_succ']
  exact (card_quotient_normalizer_modEq_card_quotient hH).mul_right' _

/--
theorem `prime_dvd_card_quotient_normalizer` / 定理 `prime_dvd_card_quotient_normalizer`

English:
theorem prime_dvd_card_quotient_normalizer
  statement: [Finite G] {p : Nat} {n : Nat} [Fact p.Prime]
  proof: let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H != 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H]; rw [hH]; rw [hs]; rw [pow_succ']; rw [mul_assoc]; rw [mul_comm p])
  have hm

中文:
定理 prime_dvd_card_quotient_normalizer
  结论: [Finite G] {p : 自然数} {n : 自然数} [Fact p.Prime]
  证明: let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H != 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H]; rw [hH]; rw [hs]; rw [pow_succ']; rw [mul_assoc]; rw [mul_comm p])
  have hm

Depends on / 依赖: H.comap, Nat.card, Nat.card_pos.ne, Nat.dvd_of_mod_eq_zero, Nat.mod_eq_zero_of_dvd, card_eq_card_quotient_mul_card_subgroup, card_pos, card_quotient_normalizer_modEq_card_quotient, dvd_mul_left, dvd_of_mod_eq_zero, exists_eq_mul_left_of_dvd, mod_eq_zero_of_dvd, mul_assoc, mul_comm, mul_left_inj, normalizer, pow_succ, subtype
-/
theorem prime_dvd_card_quotient_normalizer [Finite G] {p : Nat} {n : Nat} [Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ∣ Nat.card (normalizer (H : Set G) ⧸ H.comap (normalizer (H : Set G)).subtype) :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H != 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H]; rw [hH]; rw [hs]; rw [pow_succ']; rw [mul_assoc]; rw [mul_comm p])
  have hm :
    s * p % p =
      Nat.card (normalizer H ⧸ H.comap (normalizer (H : Set G)).subtype) % p :=
    hcard ▸ (card_quotient_normalizer_modEq_card_quotient hH).symm
  Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/--
theorem `prime_pow_dvd_card_normalizer` / 定理 `prime_pow_dvd_card_normalizer`

English:
theorem prime_pow_dvd_card_normalizer
  statement: [Finite G] {p : Nat} {n : Nat} [_hp : Fact p.Prime]
  proof: Nat.modEq_zero_iff_dvd.1 ((card_normalizer_modEq_card hH).trans hdvd.modEq_zero_nat)

中文:
定理 prime_pow_dvd_card_normalizer
  结论: [Finite G] {p : 自然数} {n : 自然数} [_hp : Fact p.Prime]
  证明: Nat.modEq_zero_iff_dvd.1 ((card_normalizer_modEq_card hH).trans hdvd.modEq_zero_nat)

Depends on / 依赖: Nat.modEq_zero_iff_dvd, card_normalizer_modEq_card, hdvd.modEq_zero_nat, modEq_zero_iff_dvd, modEq_zero_nat
-/
theorem prime_pow_dvd_card_normalizer [Finite G] {p : Nat} {n : Nat} [_hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ^ (n + 1) ∣ Nat.card (normalizer (H : Set G)) :=
  Nat.modEq_zero_iff_dvd.1 ((card_normalizer_modEq_card hH).trans hdvd.modEq_zero_nat)

/--
theorem `exists_subgroup_card_pow_succ` / 定理 `exists_subgroup_card_pow_succ`

English:
theorem exists_subgroup_card_pow_succ
  statement: [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime]
  proof: let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H != 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H]; rw [hH]; rw [hs]; rw [pow_succ']; rw [mul_assoc]; rw [mul_comm p])
  have hm

中文:
定理 exists_subgroup_card_pow_succ
  结论: [Finite G] {p : 自然数} {n : 自然数} [hp : Fact p.Prime]
  证明: let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H != 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H]; rw [hH]; rw [hs]; rw [pow_succ']; rw [mul_assoc]; rw [mul_comm p])
  have hm

Depends on / 依赖: H.subgroupOf, IsPGroup, IsPGroup.of_card, Nat.card, Nat.card_congr, Nat.card_pos.ne, card_congr, card_eq_card_quotient_mul_card_subgroup, card_modEq_card_fixedPoints, card_pos, exists_eq_mul_left_of_dvd, fixedPointsMulLeftCosetsEquivQuotient, mul_assoc, mul_comm, mul_left_inj, normalizer, of_card, pow_succ, subgroupOf
-/
theorem exists_subgroup_card_pow_succ [Finite G] {p : Nat} {n : Nat} [hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    exists K : Subgroup G, Nat.card K = p ^ (n + 1) ∧ H <= K :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H != 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H]; rw [hH]; rw [hs]; rw [pow_succ']; rw [mul_assoc]; rw [mul_comm p])
  have hm : s * p % p = Nat.card (normalizer H ⧸ H.subgroupOf (normalizer H)) % p :=
    Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H) ▸
      hcard ▸ (IsPGroup.of_card hH).card_modEq_card_fixedPoints _
  have hm' : p ∣ Nat.card (normalizer H ⧸ H.subgroupOf (normalizer H)) :=
    Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)
  let ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' _ (QuotientGroup.Quotient.group _) _ _ hp hm'
  have hequiv : H ≃ H.subgroupOf (normalizer H) := (subgroupOfEquivOfLe le_normalizer).symm.toEquiv
  ⟨((zpowers x).comap (mk' (H.subgroupOf (normalizer H)))).map (normalizer H).subtype, by
    show Nat.card (Subgroup.map (normalizer (H : Set G)).subtype
      (comap (mk' (H.subgroupOf (normalizer H))) (Subgroup.zpowers x))) = p ^ (n + 1)
    suffices Nat.card (Subtype.val ''
      ((zpowers x).comap (mk' (H.subgroupOf (normalizer H))) : Set (normalizer H))) = p ^ (n + 1)
      by convert! this using 2
    rw [Nat.card_image_of_injective Subtype.val_injective
        ((zpowers x).comap (mk' (H.subgroupOf (normalizer H))) : Set (normalizer (H : Set G)))]; rw [pow_succ]; rw [← hH]; rw [Nat.card_congr hequiv]; rw [← hx]; rw [← Nat.card_zpowers]; rw [← Nat.card_prod]
    exact Nat.card_congr
      (preimageMkEquivSubgroupProdSet (H.subgroupOf (normalizer H)) (zpowers x)), by
    intro y hy
    simp only [Subgroup.coe_subtype, mk'_apply, Subgroup.mem_map, Subgroup.mem_comap]
    refine ⟨⟨y, le_normalizer hy⟩, ⟨0, ?_⟩, rfl⟩
    dsimp only
    rw [zpow_zero]; rw [eq_comm]; rw [QuotientGroup.eq_one_iff]
    simpa using! hy⟩

/--
theorem `exists_subgroup_card_pow_prime_le` / 定理 `exists_subgroup_card_pow_prime_le`

English:
theorem exists_subgroup_card_pow_prime_le
  given: [Finite G] (p : Nat)

中文:
定理 exists_subgroup_card_pow_prime_le
  条件: [Finite G] (p : 自然数)

Depends on / 依赖: lt_of_le_of_lt, n.zero_le, zero_le
-/
theorem exists_subgroup_card_pow_prime_le [Finite G] (p : Nat) :
    forall {n m : Nat} [_hp : Fact p.Prime] (_hdvd : p ^ m ∣ Nat.card G) (H : Subgroup G)
      (_hH : Nat.card H = p ^ n) (_hnm : n <= m), exists K : Subgroup G, Nat.card K = p ^ m ∧ H <= K
  | n, m => fun {hdvd H hH hnm} =>
    (lt_or_eq_of_le hnm).elim
      (fun hnm : n < m =>
        have h0m : 0 < m := lt_of_le_of_lt n.zero_le hnm
        have hnm1 : n <= m - 1 := le_tsub_of_add_le_right hnm
        let ⟨K, hK⟩ :=
          @exists_subgroup_card_pow_prime_le _ _ n (m - 1) _
            (Nat.pow_dvd_of_le_of_pow_dvd tsub_le_self hdvd) H hH hnm1
        have hdvd' : p ^ (m - 1 + 1) ∣ Nat.card G := by rwa [tsub_add_cancel_of_le h0m.nat_succ_le]
        let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ _ hdvd' K hK.1
        ⟨K', by rw [hK'.1, tsub_add_cancel_of_le h0m.nat_succ_le], le_trans hK.2 hK'.2⟩)
      fun hnm : n = m => ⟨H, by simp [hH, hnm]⟩

/--
theorem `exists_subgroup_card_pow_prime` / 定理 `exists_subgroup_card_pow_prime`

English:
theorem exists_subgroup_card_pow_prime
  statement: [Finite G] (p : Nat) {n : Nat} [Fact p.Prime]
  proof: let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥
    (by rw [card_bot, pow_zero]) n.zero_le
  ⟨K, hK.1⟩

中文:
定理 exists_subgroup_card_pow_prime
  结论: [Finite G] (p : 自然数) {n : 自然数} [Fact p.Prime]
  证明: let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥
    (by rw [card_bot, pow_zero]) n.zero_le
  ⟨K, hK.1⟩

Depends on / 依赖: card_bot, exists_subgroup_card_pow_prime_le, n.zero_le, pow_zero, zero_le
-/
theorem exists_subgroup_card_pow_prime [Finite G] (p : Nat) {n : Nat} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : exists K : Subgroup G, Nat.card K = p ^ n :=
  let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥
    (by rw [card_bot, pow_zero]) n.zero_le
  ⟨K, hK.1⟩

/--
lemma `exists_subgroup_card_pow_prime_of_le_card` / 引理 `exists_subgroup_card_pow_prime_of_le_card`

English:
lemma exists_subgroup_card_pow_prime_of_le_card
  statement: {n p : Nat} (hp : p.Prime) (h : IsPGroup p G)
  proof: by
  have : Fact p.Prime := ⟨hp⟩
have : Finite G := Nat.finite_of_card_ne_zero by linarith [Nat.one_le_pow n p hp.pos]
  obtain ⟨m, hm⟩ := h.exists_card_eq
  refine exists_subgroup_card_pow_prime _ ?_
  rw [hm] at hn ⊢
exact pow_dvd_pow _ (Nat.pow_le_pow_iff_right hp.one_lt).1 hn

中文:
引理 exists_subgroup_card_pow_prime_of_le_card
  结论: {n p : 自然数} (hp : p.Prime) (h : IsPGroup p G)
  证明: by
  have : Fact p.Prime := ⟨hp⟩
have : Finite G := Nat.finite_of_card_ne_zero by linarith [Nat.one_le_pow n p hp.pos]
  obtain ⟨m, hm⟩ := h.exists_card_eq
  refine exists_subgroup_card_pow_prime _ ?_
  rw [hm] at hn ⊢
exact pow_dvd_pow _ (Nat.pow_le_pow_iff_right hp.one_lt).1 hn

Depends on / 依赖: Finite, Nat.finite_of_card_ne_zero, Nat.one_le_pow, Nat.pow_le_pow_iff_right, exists_card_eq, exists_subgroup_card_pow_prime, finite_of_card_ne_zero, h.exists_card_eq, hp.one_lt, hp.pos, one_le_pow, one_lt, p.Prime, pow_dvd_pow, pow_le_pow_iff_right
-/
lemma exists_subgroup_card_pow_prime_of_le_card {n p : Nat} (hp : p.Prime) (h : IsPGroup p G)
    (hn : p ^ n <= Nat.card G) : exists H : Subgroup G, Nat.card H = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
have : Finite G := Nat.finite_of_card_ne_zero by linarith [Nat.one_le_pow n p hp.pos]
  obtain ⟨m, hm⟩ := h.exists_card_eq
  refine exists_subgroup_card_pow_prime _ ?_
  rw [hm] at hn ⊢
exact pow_dvd_pow _ (Nat.pow_le_pow_iff_right hp.one_lt).1 hn

/--
lemma `exists_subgroup_le_card_pow_prime_of_le_card` / 引理 `exists_subgroup_le_card_pow_prime_of_le_card`

English:
lemma exists_subgroup_le_card_pow_prime_of_le_card
  statement: {n p : Nat} (hp : p.Prime) (h : IsPGroup p G)
  proof: by
  obtain ⟨H', H'card⟩ := exists_subgroup_card_pow_prime_of_le_card hp (h.to_subgroup H) hn
  refine ⟨H'.map H.subtype, map_subtype_le _, ?_⟩
  rw [← H'card]
  let e : H' ≃* H'.map H.subtype := H'.equivMapOfInjective (Subgroup.subtype H) H.subtype_injective
  exact Nat.card_congr e.symm.toEquiv

中文:
引理 exists_subgroup_le_card_pow_prime_of_le_card
  结论: {n p : 自然数} (hp : p.Prime) (h : IsPGroup p G)
  证明: by
  obtain ⟨H', H'card⟩ := exists_subgroup_card_pow_prime_of_le_card hp (h.to_subgroup H) hn
  refine ⟨H'.map H.subtype, map_subtype_le _, ?_⟩
  rw [← H'card]
  let e : H' ≃* H'.map H.subtype := H'.equivMapOfInjective (Subgroup.subtype H) H.subtype_injective
  exact Nat.card_congr e.symm.toEquiv

Depends on / 依赖: H.subtype, H.subtype_injective, Nat.card_congr, Subgroup, Subgroup.subtype, card_congr, e.symm.toEquiv, equivMapOfInjective, exists_subgroup_card_pow_prime_of_le_card, h.to_subgroup, map_subtype_le, subtype, subtype_injective, toEquiv, to_subgroup
-/
lemma exists_subgroup_le_card_pow_prime_of_le_card {n p : Nat} (hp : p.Prime) (h : IsPGroup p G)
    {H : Subgroup G} (hn : p ^ n <= Nat.card H) : exists H' <= H, Nat.card H' = p ^ n := by
  obtain ⟨H', H'card⟩ := exists_subgroup_card_pow_prime_of_le_card hp (h.to_subgroup H) hn
  refine ⟨H'.map H.subtype, map_subtype_le _, ?_⟩
  rw [← H'card]
  let e : H' ≃* H'.map H.subtype := H'.equivMapOfInjective (Subgroup.subtype H) H.subtype_injective
  exact Nat.card_congr e.symm.toEquiv

/--
lemma `exists_subgroup_le_card_le` / 引理 `exists_subgroup_le_card_le`

English:
lemma exists_subgroup_le_card_le
  statement: {k p : Nat} (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G}
  proof: by
  obtain ⟨m, hmk, hkm⟩ : exists s, p ^ s <= k ∧ k < p ^ (s + 1) :=
    exists_nat_pow_near (Nat.one_le_iff_ne_zero.2 hk₀) hp.one_lt
  obtain ⟨H', H'H, H'card⟩ := exists_subgroup_le_card_pow_prime_of_le_card hp h (hmk.trans hk)
  refine ⟨H', H'H, ?_⟩
  simpa only [pow_succ', H'card] using And.intr

中文:
引理 exists_subgroup_le_card_le
  结论: {k p : 自然数} (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G}
  证明: by
  obtain ⟨m, hmk, hkm⟩ : exists s, p ^ s <= k ∧ k < p ^ (s + 1) :=
    exists_nat_pow_near (Nat.one_le_iff_ne_zero.2 hk₀) hp.one_lt
  obtain ⟨H', H'H, H'card⟩ := exists_subgroup_le_card_pow_prime_of_le_card hp h (hmk.trans hk)
  refine ⟨H', H'H, ?_⟩
  simpa only [pow_succ', H'card] using And.intr

Depends on / 依赖: And.intro, Nat.one_le_iff_ne_zero, exists_nat_pow_near, exists_subgroup_le_card_pow_prime_of_le_card, hmk.trans, hp.one_lt, one_le_iff_ne_zero, one_lt, pow_succ
-/
lemma exists_subgroup_le_card_le {k p : Nat} (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G}
    (hk : k <= Nat.card H) (hk₀ : k != 0) : exists H' <= H, Nat.card H' <= k ∧ k < p * Nat.card H' := by
  obtain ⟨m, hmk, hkm⟩ : exists s, p ^ s <= k ∧ k < p ^ (s + 1) :=
    exists_nat_pow_near (Nat.one_le_iff_ne_zero.2 hk₀) hp.one_lt
  obtain ⟨H', H'H, H'card⟩ := exists_subgroup_le_card_pow_prime_of_le_card hp h (hmk.trans hk)
  refine ⟨H', H'H, ?_⟩
  simpa only [pow_succ', H'card] using And.intro hmk hkm

/--
theorem `pow_dvd_card_of_pow_dvd_card` / 定理 `pow_dvd_card_of_pow_dvd_card`

English:
theorem pow_dvd_card_of_pow_dvd_card
  statement: [Finite G] {p n : Nat} [hp : Fact p.Prime] (P : Sylow p G)
  proof: by
  rw [← index_mul_card P.1] at hdvd
  exact (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm.dvd_of_dvd_mul_left hdvd

中文:
定理 pow_dvd_card_of_pow_dvd_card
  结论: [Finite G] {p n : 自然数} [hp : Fact p.Prime] (P : Sylow p G)
  证明: by
  rw [← index_mul_card P.1] at hdvd
  exact (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm.dvd_of_dvd_mul_left hdvd

Depends on / 依赖: P.not_dvd_index, coprime_pow_of_not_dvd, dvd_of_dvd_mul_left, index_mul_card, not_dvd_index, symm.dvd_of_dvd_mul_left
-/
theorem pow_dvd_card_of_pow_dvd_card [Finite G] {p n : Nat} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ^ n ∣ Nat.card G) : p ^ n ∣ Nat.card P := by
  rw [← index_mul_card P.1] at hdvd
  exact (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm.dvd_of_dvd_mul_left hdvd

/--
theorem `dvd_card_of_dvd_card` / 定理 `dvd_card_of_dvd_card`

English:
theorem dvd_card_of_dvd_card
  statement: [Finite G] {p : Nat} [Fact p.Prime] (P : Sylow p G)
  proof: by
  rw [← pow_one p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_one] at key

中文:
定理 dvd_card_of_dvd_card
  结论: [Finite G] {p : 自然数} [Fact p.Prime] (P : Sylow p G)
  证明: by
  rw [← pow_one p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_one] at key

Depends on / 依赖: P.pow_dvd_card_of_pow_dvd_card, pow_dvd_card_of_pow_dvd_card, pow_one
-/
theorem dvd_card_of_dvd_card [Finite G] {p : Nat} [Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : p ∣ Nat.card P := by
  rw [← pow_one p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_one] at key

/--
theorem `card_coprime_index` / 定理 `card_coprime_index`

English:
theorem card_coprime_index
  given: [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G)
  proof: let ⟨_n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm

中文:
定理 card_coprime_index
  条件: [Finite G] {p : 自然数} [hp : Fact p.Prime] (P : Sylow p G)
  证明: let ⟨_n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm

Depends on / 依赖: IsPGroup, IsPGroup.iff_card.mp, P.not_dvd_index, coprime_pow_of_not_dvd, hn.symm, iff_card, not_dvd_index
-/
theorem card_coprime_index [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G) :
    (Nat.card P).Coprime P.index :=
  let ⟨_n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm

/--
theorem `ne_bot_of_dvd_card` / 定理 `ne_bot_of_dvd_card`

English:
theorem ne_bot_of_dvd_card
  statement: [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G)
  proof: by
  refine fun h => hp.out.not_dvd_one ?_
  have key : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key

中文:
定理 ne_bot_of_dvd_card
  结论: [Finite G] {p : 自然数} [hp : Fact p.Prime] (P : Sylow p G)
  证明: by
  refine fun h => hp.out.not_dvd_one ?_
  have key : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key

Depends on / 依赖: Nat.card, P.dvd_card_of_dvd_card, card_bot, dvd_card_of_dvd_card, hp.out.not_dvd_one, not_dvd_one
-/
theorem ne_bot_of_dvd_card [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : (P : Subgroup G) != ⊥ := by
  refine fun h => hp.out.not_dvd_one ?_
  have key : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key

/--
theorem `card_eq_multiplicity` / 定理 `card_eq_multiplicity`

English:
theorem card_eq_multiplicity
  given: [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G)
  proof: by
  obtain ⟨n, heq : Nat.card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
  refine Nat.dvd_antisymm ?_ (P.pow_dvd_card_of_pow_dvd_card (Nat.ordProj_dvd _ p))
  rw [heq]; rw [← hp.out.pow_dvd_iff_dvd_ordProj (show Nat.card G != 0 from Nat.card_pos.ne')]; rw [← heq]
  exact P.1.card_subgroup_dvd_card

中文:
定理 card_eq_multiplicity
  条件: [Finite G] {p : 自然数} [hp : Fact p.Prime] (P : Sylow p G)
  证明: by
  obtain ⟨n, heq : Nat.card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
  refine Nat.dvd_antisymm ?_ (P.pow_dvd_card_of_pow_dvd_card (Nat.ordProj_dvd _ p))
  rw [heq]; rw [← hp.out.pow_dvd_iff_dvd_ordProj (show Nat.card G != 0 from Nat.card_pos.ne')]; rw [← heq]
  exact P.1.card_subgroup_dvd_card

Depends on / 依赖: IsPGroup, IsPGroup.iff_card.mp, Nat.card, Nat.card_pos.ne, Nat.dvd_antisymm, Nat.ordProj_dvd, P.isPGroup, P.pow_dvd_card_of_pow_dvd_card, card_pos, card_subgroup_dvd_card, dvd_antisymm, hp.out.pow_dvd_iff_dvd_ordProj, iff_card, isPGroup, ordProj_dvd, pow_dvd_card_of_pow_dvd_card, pow_dvd_iff_dvd_ordProj
-/
theorem card_eq_multiplicity [Finite G] {p : Nat} [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card P = p ^ Nat.factorization (Nat.card G) p := by
  obtain ⟨n, heq : Nat.card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
  refine Nat.dvd_antisymm ?_ (P.pow_dvd_card_of_pow_dvd_card (Nat.ordProj_dvd _ p))
  rw [heq]; rw [← hp.out.pow_dvd_iff_dvd_ordProj (show Nat.card G != 0 from Nat.card_pos.ne')]; rw [← heq]
  exact P.1.card_subgroup_dvd_card

variable (G) in
/--
theorem `_root_.Group.card_dvd_prod_orderOf` / 定理 `_root_.Group.card_dvd_prod_orderOf`

English:
theorem _root_.Group.card_dvd_prod_orderOf
  given: [Fintype G]
  statement: Nat.card G ∣ ∏ g : G, orderOf g
  proof: by
  classical
.mpr fun p k hp h => ?_ refine Nat.dvd_iff_prime_pow_dvd_dvd ..
  have := Fact.mk hp
  have ⟨H, hH⟩ := exists_subgroup_card_pow_prime p h
  have (g : G) (hg : g in (H \ {1} : Set G).toFinset) : p ∣ orderOf g := by
    have ⟨hg, hg1⟩ : g in H ∧ g != 1 := by simpa using hg
.dvd_orderOf 

中文:
定理 _root_.Group.card_dvd_prod_orderOf
  条件: [Fintype G]
  结论: 自然数.card G ∣ ∏ g : G, orderOf g
  证明: by
  classical
.mpr fun p k hp h => ?_ refine Nat.dvd_iff_prime_pow_dvd_dvd ..
  have := Fact.mk hp
  have ⟨H, hH⟩ := exists_subgroup_card_pow_prime p h
  have (g : G) (hg : g in (H \ {1} : Set G).toFinset) : p ∣ orderOf g := by
    have ⟨hg, hg1⟩ : g in H ∧ g != 1 := by simpa using hg
.dvd_orderOf 

Depends on / 依赖: Fact.mk, IsPGroup, IsPGroup.of_card, Nat.dvd_iff_prime_pow_dvd_dvd, classical, dvd_iff_prime_pow_dvd_dvd, dvd_orderOf, exists_subgroup_card_pow_prime, k.le_sub_one_of_lt, k.lt_pow_self, le_sub_one_of_lt, lt_pow_self, of_card, orderOf, prod_const, prod_dvd_prod_of_dvd, prod_dvd_prod_of_subset, subset_univ, toFinset, toFinset.subset_univ
-/
theorem _root_.Group.card_dvd_prod_orderOf [Fintype G] : Nat.card G ∣ ∏ g : G, orderOf g := by
  classical
.mpr fun p k hp h => ?_ refine Nat.dvd_iff_prime_pow_dvd_dvd ..
  have := Fact.mk hp
  have ⟨H, hH⟩ := exists_subgroup_card_pow_prime p h
  have (g : G) (hg : g in (H \ {1} : Set G).toFinset) : p ∣ orderOf g := by
    have ⟨hg, hg1⟩ : g in H ∧ g != 1 := by simpa using hg
.dvd_orderOf (g := ⟨g, hg⟩) by simpa simpa using IsPGroup.of_card hH
  grw [← prod_dvd_prod_of_subset _ _ _ (H \ {1} : Set G).toFinset.subset_univ,
← prod_dvd_prod_of_dvd _ _ this, prod_const, k.le_sub_one_of_lt k.lt_pow_self hp.one_lt]
  simp [Finset.card_sdiff, ← Nat.card_eq_fintype_card, hH]

/-- If `G` has a normal Sylow `p`-subgroup, then it is the only Sylow `p`-subgroup. -/
@[instance_reducible]
/--
Definition of `unique_of_normal` / `unique_of_normal` 的定义

English:
definition unique_of_normal
  signature: {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  body: by
  refine { uniq := fun Q => ?_ }
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := exists_smul_eq G P default
  rw [smul_eq_of_normal] at h1 h2
  rw [← h1]; rw [← h2]

中文:
定义 unique_of_normal
  签名: {p : 自然数} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  定义体: by
  refine { uniq := fun Q => ?_ }
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := exists_smul_eq G P default
  rw [smul_eq_of_normal] at h1 h2
  rw [← h1]; rw [← h2]

Depends on / 依赖: exists_smul_eq, smul_eq_of_normal
-/
noncomputable def unique_of_normal {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : Unique (Sylow p G) := by
  refine { uniq := fun Q => ?_ }
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := exists_smul_eq G P default
  rw [smul_eq_of_normal] at h1 h2
  rw [← h1]; rw [← h2]

/--
Instance `characteristic_of_subsingleton` / 实例 `characteristic_of_subsingleton`

English:
instance characteristic_of_subsingleton
  signature: {p : Nat} [Subsingleton (Sylow p G)] (P : Sylow p G)
  body: by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  have h := Subgroup.pointwise_smul_def (a := ϕ) (P : Subgroup G)
  rwa [← pointwise_smul_def, Subsingleton.elim (ϕ • P) P, eq_comm] at h

中文:
实例 characteristic_of_subsingleton
  签名: {p : 自然数} [Subsingleton (Sylow p G)] (P : Sylow p G)
  定义体: by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  have h := Subgroup.pointwise_smul_def (a := ϕ) (P : Subgroup G)
  rwa [← pointwise_smul_def, Subsingleton.elim (ϕ • P) P, eq_comm] at h

Depends on / 依赖: Subgroup, Subgroup.characteristic_iff_map_eq.mpr, Subgroup.pointwise_smul_def, Subsingleton, Subsingleton.elim, characteristic_iff_map_eq, eq_comm, pointwise_smul_def
-/
instance characteristic_of_subsingleton {p : Nat} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  have h := Subgroup.pointwise_smul_def (a := ϕ) (P : Subgroup G)
  rwa [← pointwise_smul_def, Subsingleton.elim (ϕ • P) P, eq_comm] at h

/--
theorem `normal_of_subsingleton` / 定理 `normal_of_subsingleton`

English:
theorem normal_of_subsingleton
  given: {p : Nat} [Subsingleton (Sylow p G)] (P : Sylow p G)
  proof: Subgroup.normal_of_characteristic _

中文:
定理 normal_of_subsingleton
  条件: {p : 自然数} [Subsingleton (Sylow p G)] (P : Sylow p G)
  证明: Subgroup.normal_of_characteristic _

Depends on / 依赖: Subgroup, Subgroup.normal_of_characteristic, normal_of_characteristic
-/
theorem normal_of_subsingleton {p : Nat} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Normal :=
  Subgroup.normal_of_characteristic _

/--
theorem `characteristic_of_normal` / 定理 `characteristic_of_normal`

English:
theorem characteristic_of_normal
  statement: {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  proof: by
  have _ := unique_of_normal P h
  exact characteristic_of_subsingleton _

中文:
定理 characteristic_of_normal
  结论: {p : 自然数} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  证明: by
  have _ := unique_of_normal P h
  exact characteristic_of_subsingleton _

Depends on / 依赖: characteristic_of_subsingleton, unique_of_normal
-/
theorem characteristic_of_normal {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : P.Characteristic := by
  have _ := unique_of_normal P h
  exact characteristic_of_subsingleton _

/--
theorem `normal_of_normalizer_normal` / 定理 `normal_of_normalizer_normal`

English:
theorem normal_of_normalizer_normal
  statement: {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  proof: by
  rw [← normalizer_eq_top_iff]; rw [← normalizer_sup_eq_top' P le_normalizer]; rw [P.coe_coe]; rw [sup_idem]

@[simp]

中文:
定理 normal_of_normalizer_normal
  结论: {p : 自然数} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  证明: by
  rw [← normalizer_eq_top_iff]; rw [← normalizer_sup_eq_top' P le_normalizer]; rw [P.coe_coe]; rw [sup_idem]

@[simp]

Depends on / 依赖: P.coe_coe, coe_coe, le_normalizer, normalizer_eq_top_iff, normalizer_sup_eq_top, sup_idem
-/
theorem normal_of_normalizer_normal {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hn : (normalizer (P : Set G)).Normal) : P.Normal := by
  rw [← normalizer_eq_top_iff]; rw [← normalizer_sup_eq_top' P le_normalizer]; rw [P.coe_coe]; rw [sup_idem]

@[simp]
/--
theorem `normalizer_normalizer` / 定理 `normalizer_normalizer`

English:
theorem normalizer_normalizer
  given: {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  proof: by
  have := normal_of_normalizer_normal (P.subtype (le_normalizer.trans le_normalizer))
  rw [← (P.subtype _).coe_coe]; rw [coe_subtype]; rw [normal_subgroupOf_iff_le_normalizer (le_normalizer.trans le_normalizer)]; rw [← subgroupOf_normalizer_eq (le_normalizer.trans le_normalizer)] at this
  exact

中文:
定理 normalizer_normalizer
  条件: {p : 自然数} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
  证明: by
  have := normal_of_normalizer_normal (P.subtype (le_normalizer.trans le_normalizer))
  rw [← (P.subtype _).coe_coe]; rw [coe_subtype]; rw [normal_subgroupOf_iff_le_normalizer (le_normalizer.trans le_normalizer)]; rw [← subgroupOf_normalizer_eq (le_normalizer.trans le_normalizer)] at this
  exact

Depends on / 依赖: P.subtype, coe_coe, coe_subtype, le_antisymm, le_normalizer, le_normalizer.trans, normal_in_normalizer, normal_of_normalizer_normal, normal_subgroupOf_iff_le_normalizer, subgroupOf_normalizer_eq, subtype
-/
theorem normalizer_normalizer {p : Nat} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    normalizer (normalizer (P : Set G)) = normalizer (P : Set G) := by
  have := normal_of_normalizer_normal (P.subtype (le_normalizer.trans le_normalizer))
  rw [← (P.subtype _).coe_coe]; rw [coe_subtype]; rw [normal_subgroupOf_iff_le_normalizer (le_normalizer.trans le_normalizer)]; rw [← subgroupOf_normalizer_eq (le_normalizer.trans le_normalizer)] at this
  exact le_antisymm (this normal_in_normalizer) le_normalizer

/--
theorem `normal_of_all_max_subgroups_normal` / 定理 `normal_of_all_max_subgroups_normal`

English:
theorem normal_of_all_max_subgroups_normal
  statement: [Finite G]
  proof: normalizer_eq_top_iff.mp
    (by
      rcases eq_top_or_exists_le_coatom (normalizer (P : Set G))
        with (heq | ⟨K, hK, hNK⟩)
      · exact heq
      · have := hnc _ hK
        have hPK : P <= K := le_trans le_normalizer hNK
        refine (hK.1 ?_).elim
        rw [← sup_of_le_right hNK]; rw 

中文:
定理 normal_of_all_max_subgroups_normal
  结论: [Finite G]
  证明: normalizer_eq_top_iff.mp
    (by
      rcases eq_top_or_exists_le_coatom (normalizer (P : Set G))
        with (heq | ⟨K, hK, hNK⟩)
      · exact heq
      · have := hnc _ hK
        have hPK : P <= K := le_trans le_normalizer hNK
        refine (hK.1 ?_).elim
        rw [← sup_of_le_right hNK]; rw 

Depends on / 依赖: P.normalizer_sup_eq_top, eq_top_or_exists_le_coatom, le_normalizer, le_trans, normalizer, normalizer_eq_top_iff, normalizer_eq_top_iff.mp, normalizer_sup_eq_top, sup_of_le_right
-/
theorem normal_of_all_max_subgroups_normal [Finite G]
    (hnc : forall H : Subgroup G, IsCoatom H -> H.Normal) {p : Nat} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : P.Normal :=
  normalizer_eq_top_iff.mp
    (by
      rcases eq_top_or_exists_le_coatom (normalizer (P : Set G))
        with (heq | ⟨K, hK, hNK⟩)
      · exact heq
      · have := hnc _ hK
        have hPK : P <= K := le_trans le_normalizer hNK
        refine (hK.1 ?_).elim
        rw [← sup_of_le_right hNK]; rw [P.normalizer_sup_eq_top' hPK])

/--
theorem `normal_of_normalizerCondition` / 定理 `normal_of_normalizerCondition`

English:
theorem normal_of_normalizerCondition
  statement: (hnc : NormalizerCondition G) {p : Nat} [Fact p.Prime]
  proof: normalizer_eq_top_iff.mp
normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ normalizer_normalizer _

中文:
定理 normal_of_normalizerCondition
  结论: (hnc : NormalizerCondition G) {p : 自然数} [Fact p.Prime]
  证明: normalizer_eq_top_iff.mp
normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ normalizer_normalizer _

Depends on / 依赖: normalizerCondition_iff_only_full_group_self_normalizing, normalizerCondition_iff_only_full_group_self_normalizing.mp, normalizer_eq_top_iff, normalizer_eq_top_iff.mp, normalizer_normalizer
-/
theorem normal_of_normalizerCondition (hnc : NormalizerCondition G) {p : Nat} [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) : P.Normal :=
normalizer_eq_top_iff.mp
normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ normalizer_normalizer _

/--
Definition of `directProductOfNormal` / `directProductOfNormal` 的定义

English:
definition directProductOfNormal
  signature: [Finite G]
  body: by
  have := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors
  -- “The” Sylow subgroup for p
  let P : forall p, Sylow p G := default
  have : forall p, Fintype (P p) := fun p => Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps => forall x y : G, x in P p₁ -> y in P p₂ -> Commu

中文:
定义 directProductOfNormal
  签名: [Finite G]
  定义体: by
  have := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors
  -- “The” Sylow subgroup for p
  let P : forall p, Sylow p G := default
  have : forall p, Fintype (P p) := fun p => Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps => forall x y : G, x in P p₁ -> y in P p₂ -> Commu

Depends on / 依赖: Fintype, Fintype.ofFinite, Nat.card, ofFinite, primeFactors
-/
noncomputable def directProductOfNormal [Finite G]
    (hn : forall {p : Nat} [Fact p.Prime] (P : Sylow p G), P.Normal) :
    (forall p : (Nat.card G).primeFactors, forall P : Sylow p G, P) ≃* G := by
  have := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors
  -- “The” Sylow subgroup for p
  let P : forall p, Sylow p G := default
  have : forall p, Fintype (P p) := fun p => Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps => forall x y : G, x in P p₁ -> y in P p₂ -> Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ != p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hn (P p₁)) (hn (P p₂))
    apply IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  refine MulEquiv.trans (N := forall p : ps, P p) ?_ ?_
  -- There is only one Sylow subgroup for each p, so the inner product is trivial
  · -- here we need to help the elaborator with an explicit instantiation
    apply @MulEquiv.piCongrRight ps (fun p => forall P : Sylow p G, P) (fun p => P p) _ _
    rintro ⟨p, hp⟩
    haveI hp' := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    letI := unique_of_normal _ (hn (P p))
    apply MulEquiv.piUnique
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    have hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ != p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    apply IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  · simp only [← Nat.card_eq_fintype_card]
    calc
      Nat.card (forall p : ps, P p) = ∏ p : ps, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : ps, p.1 ^ (Nat.card G).factorization p.1 := by
        congr 1 with ⟨p, hp⟩
        exact @card_eq_multiplicity _ _ _ p ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p in ps, p ^ (Nat.card G).factorization p :=
        (Finset.prod_finset_coe (fun p => p ^ (Nat.card G).factorization p) _)
      _ = (Nat.card G).factorization.prod (· ^ ·) := rfl
      _ = Nat.card G := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'

end Sylow
