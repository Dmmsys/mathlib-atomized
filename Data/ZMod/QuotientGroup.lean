/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# `ZMod n` and quotient groups / rings

This file relates `ZMod n` to the quotient group `ℤ / AddSubgroup.zmultiples (n : ℤ)`.

## Main definitions

- `ZMod.quotientZMultiplesNatEquivZMod` and `ZMod.quotientZMultiplesEquivZMod`:
  `ZMod n` is the group quotient of `ℤ` by `n ℤ := AddSubgroup.zmultiples (n)`,
  (where `n : ℕ` and `n : ℤ` respectively)
- `ZMod.lift n f` is the map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

open QuotientAddGroup Set ZMod
open scoped IsMulCommutative

variable (n : Nat) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

/--
Definition of `quotientZMultiplesNatEquivZMod` / `quotientZMultiplesNatEquivZMod` 的定义

English:
definition quotientZMultiplesNatEquivZMod
  signature: : Int ⧸ AddSubgroup.zmultiples (n : Int) ≃+ ZMod n
  body: (quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast

中文:
定义 quotientZMultiplesNatEquivZMod
  签名: : 整数 ⧸ AddSubgroup.zmultiples (n : 整数) ≃+ ZMod n
  定义体: (quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast

Depends on / 依赖: Int.castAddHom, ZMod.ker_intCastAddHom, castAddHom, intCast_zmod_cast, ker_intCastAddHom, quotientAddEquivOfEq, quotientKerEquivOfRightInverse, symm.trans
-/
def quotientZMultiplesNatEquivZMod : Int ⧸ AddSubgroup.zmultiples (n : Int) ≃+ ZMod n :=
(quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast

/--
Definition of `quotientZMultiplesEquivZMod` / `quotientZMultiplesEquivZMod` 的定义

English:
definition quotientZMultiplesEquivZMod
  signature: (a : Int)
  body: (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)

@[simp]

中文:
定义 quotientZMultiplesEquivZMod
  签名: (a : 整数)
  定义体: (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)

@[simp]

Depends on / 依赖: a.natAbs, natAbs, quotientAddEquivOfEq, quotientZMultiplesNatEquivZMod, symm.trans, zmultiples_natAbs
-/
def quotientZMultiplesEquivZMod (a : Int) : Int ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)

@[simp]
/--
lemma `index_zmultiples` / 引理 `index_zmultiples`

English:
lemma index_zmultiples
  given: (a : Int)
  statement: (AddSubgroup.zmultiples a).index = a.natAbs
  proof: by
  rw [AddSubgroup.index]; rw [Nat.card_congr (quotientZMultiplesEquivZMod a).toEquiv]; rw [Nat.card_zmod]

中文:
引理 index_zmultiples
  条件: (a : 整数)
  结论: (AddSubgroup.zmultiples a).index = a.natAbs
  证明: by
  rw [AddSubgroup.index]; rw [Nat.card_congr (quotientZMultiplesEquivZMod a).toEquiv]; rw [Nat.card_zmod]

Depends on / 依赖: AddSubgroup, AddSubgroup.index, Nat.card_congr, Nat.card_zmod, card_congr, card_zmod, quotientZMultiplesEquivZMod, toEquiv
-/
lemma index_zmultiples (a : Int) : (AddSubgroup.zmultiples a).index = a.natAbs := by
  rw [AddSubgroup.index]; rw [Nat.card_congr (quotientZMultiplesEquivZMod a).toEquiv]; rw [Nat.card_zmod]

end Int


namespace AddAction

open AddSubgroup AddMonoidHom AddEquiv Function

variable {α β : Type*} [AddGroup α] (a : α) [AddAction α β] (b : β)

/--
Definition of `zmultiplesQuotientStabilizerEquiv` / `zmultiplesQuotientStabilizerEquiv` 的定义

English:
definition zmultiplesQuotientStabilizerEquiv
  signature: :
  body: (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le]; rw [mem_comap]; rw [mem_stabilizer_iff]; rw [zmultiplesHom_apply]; rw [natCast_zsmul]
              simp_rw [← vadd_iterate]
            

中文:
定义 zmultiplesQuotientStabilizerEquiv
  签名: :
  定义体: (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le]; rw [mem_comap]; rw [mem_stabilizer_iff]; rw [zmultiplesHom_apply]; rw [natCast_zsmul]
              simp_rw [← vadd_iterate]
            

Depends on / 依赖: Int.mem_zmultiples_iff, eq_bot_iff, eq_zero_iff, induction_on, isPeriodicPt_minimalPeriod, ker_eq_bot_iff, mem_bot, mem_comap, mem_stabilizer_iff, mem_zmultiples, mem_zmultiples_iff, natCast_zsmul, ofBijective, simp_rw, stabilizer, vadd_iterate, zmultiples, zmultiplesHom, zmultiplesHom_apply, zmultiples_le
-/
noncomputable def zmultiplesQuotientStabilizerEquiv :
    zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le]; rw [mem_comap]; rw [mem_stabilizer_iff]; rw [zmultiplesHom_apply]; rw [natCast_zsmul]
              simp_rw [← vadd_iterate]
              exact isPeriodicPt_minimalPeriod (a +ᵥ ·) b))
          ⟨by
            rw [← ker_eq_bot_iff]; rw [eq_bot_iff]
            refine fun q => induction_on q fun n hn => ?_
            rw [mem_bot]; rw [eq_zero_iff]; rw [Int.mem_zmultiples_iff]; rw [←
              zsmul_vadd_eq_iff_minimalPeriod_dvd]
            exact (eq_zero_iff _).mp hn, fun q =>
            induction_on q fun ⟨_, n, rfl⟩ => ⟨n, rfl⟩⟩).symm.trans
    (Int.quotientZMultiplesNatEquivZMod (minimalPeriod (a +ᵥ ·) b))

/--
theorem `zmultiplesQuotientStabilizerEquiv_symm_apply` / 定理 `zmultiplesQuotientStabilizerEquiv_symm_apply`

English:
theorem zmultiplesQuotientStabilizerEquiv_symm_apply
  given: (n : ZMod (minimalPeriod (a +ᵥ ·) b))
  proof: rfl

中文:
定理 zmultiplesQuotientStabilizerEquiv_symm_apply
  条件: (n : ZMod (minimalPeriod (a +ᵥ ·) b))
  证明: rfl
-/
theorem zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a +ᵥ ·) b)) :
    (zmultiplesQuotientStabilizerEquiv a b).symm n =
      (cast n : Int) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
  rfl

end AddAction

namespace MulAction

open AddAction Subgroup AddSubgroup Function

variable {α β : Type*} [Group α] (a : α) [MulAction α β] (b : β)

/--
Definition of `zpowersQuotientStabilizerEquiv` / `zpowersQuotientStabilizerEquiv` 的定义

English:
definition zpowersQuotientStabilizerEquiv
  signature: :
  body: letI f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  AddEquiv.toMultiplicative f

中文:
定义 zpowersQuotientStabilizerEquiv
  签名: :
  定义体: letI f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  AddEquiv.toMultiplicative f

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicative, Additive, Additive.ofMul, toMultiplicative, zmultiplesQuotientStabilizerEquiv
-/
noncomputable def zpowersQuotientStabilizerEquiv :
    zpowers a ⧸ stabilizer (zpowers a) b ≃* Multiplicative (ZMod (minimalPeriod (a • ·) b)) :=
  letI f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  AddEquiv.toMultiplicative f

/--
theorem `zpowersQuotientStabilizerEquiv_symm_apply` / 定理 `zpowersQuotientStabilizerEquiv_symm_apply`

English:
theorem zpowersQuotientStabilizerEquiv_symm_apply
  given: (n : ZMod (minimalPeriod (a • ·) b))
  proof: rfl

中文:
定理 zpowersQuotientStabilizerEquiv_symm_apply
  条件: (n : ZMod (minimalPeriod (a • ·) b))
  证明: rfl
-/
theorem zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a • ·) b)) :
    (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast n : Int) :=
  rfl

/--
Definition of `orbitZPowersEquiv` / `orbitZPowersEquiv` 的定义

English:
definition orbitZPowersEquiv
  signature: : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b)
  body: (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv

中文:
定义 orbitZPowersEquiv
  签名: : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b)
  定义体: (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv

Depends on / 依赖: orbitEquivQuotientStabilizer, toEquiv, zpowersQuotientStabilizerEquiv
-/
noncomputable def orbitZPowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b) :=
  (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv

/--
Definition of `_root_.AddAction.orbitZMultiplesEquiv` / `_root_.AddAction.orbitZMultiplesEquiv` 的定义

English:
definition _root_.AddAction.orbitZMultiplesEquiv
  signature: {α β : Type*} [AddGroup α] (a : α)
  body: (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv

中文:
定义 _root_.AddAction.orbitZMultiplesEquiv
  签名: {α β : 类型} [AddGroup α] (a : α)
  定义体: (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv

Depends on / 依赖: AddAction, AddAction.orbitEquivQuotientStabilizer, Quotient, mapsTo_smul_orbit, orbitEquivQuotientStabilizer, orbitRel, orbitRel.Quotient.mapsTo_smul_orbit, restrict, toEquiv, zmultiples, zmultiplesQuotientStabilizerEquiv
-/
noncomputable def _root_.AddAction.orbitZMultiplesEquiv {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) :
    AddAction.orbit (zmultiples a) b ≃ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv

attribute [to_additive existing] orbitZPowersEquiv

@[to_additive]
/--
theorem `orbitZPowersEquiv_symm_apply` / 定理 `orbitZPowersEquiv_symm_apply`

English:
theorem orbitZPowersEquiv_symm_apply
  given: (k : ZMod (minimalPeriod (a • ·) b))
  proof: rfl

中文:
定理 orbitZPowersEquiv_symm_apply
  条件: (k : ZMod (minimalPeriod (a • ·) b))
  证明: rfl
-/
theorem orbitZPowersEquiv_symm_apply (k : ZMod (minimalPeriod (a • ·) b)) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast k : Int) • ⟨b, mem_orbit_self b⟩ :=
  rfl

/--
theorem `orbitZPowersEquiv_symm_apply'` / 定理 `orbitZPowersEquiv_symm_apply'`

English:
theorem orbitZPowersEquiv_symm_apply'
  given: (k : Int)
  proof: by
  rw [orbitZPowersEquiv_symm_apply]; rw [ZMod.coe_intCast]
  exact Subtype.ext (zpow_smul_mod_minimalPeriod _ _ k)

中文:
定理 orbitZPowersEquiv_symm_apply'
  条件: (k : 整数)
  证明: by
  rw [orbitZPowersEquiv_symm_apply]; rw [ZMod.coe_intCast]
  exact Subtype.ext (zpow_smul_mod_minimalPeriod _ _ k)

Depends on / 依赖: Subtype, Subtype.ext, ZMod.coe_intCast, coe_intCast, orbitZPowersEquiv_symm_apply, zpow_smul_mod_minimalPeriod
-/
theorem orbitZPowersEquiv_symm_apply' (k : Int) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ := by
  rw [orbitZPowersEquiv_symm_apply]; rw [ZMod.coe_intCast]
  exact Subtype.ext (zpow_smul_mod_minimalPeriod _ _ k)

/--
theorem `_root_.AddAction.orbitZMultiplesEquiv_symm_apply'` / 定理 `_root_.AddAction.orbitZMultiplesEquiv_symm_apply'`

English:
theorem _root_.AddAction.orbitZMultiplesEquiv_symm_apply'
  statement: {α β : Type*} [AddGroup α] (a : α)
  proof: by
  rw [AddAction.orbitZMultiplesEquiv_symm_apply]; rw [ZMod.coe_intCast]
  -- Making `a` explicit turns this from ~190000 heartbeats to ~700.
  exact Subtype.ext (zsmul_vadd_mod_minimalPeriod a _ k)

中文:
定理 _root_.AddAction.orbitZMultiplesEquiv_symm_apply'
  结论: {α β : 类型} [AddGroup α] (a : α)
  证明: by
  rw [AddAction.orbitZMultiplesEquiv_symm_apply]; rw [ZMod.coe_intCast]
  -- Making `a` explicit turns this from ~190000 heartbeats to ~700.
  exact Subtype.ext (zsmul_vadd_mod_minimalPeriod a _ k)

Depends on / 依赖: AddAction, AddAction.orbitZMultiplesEquiv_symm_apply, ZMod.coe_intCast, coe_intCast, orbitZMultiplesEquiv_symm_apply
-/
theorem _root_.AddAction.orbitZMultiplesEquiv_symm_apply' {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) (k : Int) :
    (AddAction.orbitZMultiplesEquiv a b).symm k =
      k • (⟨a, mem_zmultiples a⟩ : zmultiples a) +ᵥ ⟨b, AddAction.mem_orbit_self b⟩ := by
  rw [AddAction.orbitZMultiplesEquiv_symm_apply]; rw [ZMod.coe_intCast]
  -- Making `a` explicit turns this from ~190000 heartbeats to ~700.
  exact Subtype.ext (zsmul_vadd_mod_minimalPeriod a _ k)

attribute [to_additive existing]
  orbitZPowersEquiv_symm_apply'

@[to_additive]
/--
theorem `minimalPeriod_eq_card` / 定理 `minimalPeriod_eq_card`

English:
theorem minimalPeriod_eq_card
  given: [Fintype (orbit (zpowers a) b)]
  proof: by
  rw [← Fintype.ofEquiv_card (orbitZPowersEquiv a b)]; rw [ZMod.card]

@[to_additive]

中文:
定理 minimalPeriod_eq_card
  条件: [Fintype (orbit (zpowers a) b)]
  证明: by
  rw [← Fintype.ofEquiv_card (orbitZPowersEquiv a b)]; rw [ZMod.card]

@[to_additive]

Depends on / 依赖: Fintype, Fintype.ofEquiv_card, ZMod.card, ofEquiv_card, orbitZPowersEquiv
-/
theorem minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] :
    minimalPeriod (a • ·) b = Fintype.card (orbit (zpowers a) b) := by
  rw [← Fintype.ofEquiv_card (orbitZPowersEquiv a b)]; rw [ZMod.card]

@[to_additive]
/--
Instance `minimalPeriod_pos` / 实例 `minimalPeriod_pos`

English:
instance minimalPeriod_pos
  signature: [Finite <| orbit (zpowers a) b]
  body: ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    have : Nonempty (orbit (zpowers a) b) := (nonempty_orbit b).to_subtype
    rw [minimalPeriod_eq_card]
    exact Fintype.card_ne_zero⟩

中文:
实例 minimalPeriod_pos
  签名: [Finite <| orbit (zpowers a) b]
  定义体: ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    have : Nonempty (orbit (zpowers a) b) := (nonempty_orbit b).to_subtype
    rw [minimalPeriod_eq_card]
    exact Fintype.card_ne_zero⟩

Depends on / 依赖: Fintype, Fintype.card_ne_zero, Nonempty, card_ne_zero, minimalPeriod_eq_card, nonempty_fintype, nonempty_orbit, to_subtype, zpowers
-/
instance minimalPeriod_pos [Finite <| orbit (zpowers a) b] :
NeZero minimalPeriod (a • ·) b :=
  ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    have : Nonempty (orbit (zpowers a) b) := (nonempty_orbit b).to_subtype
    rw [minimalPeriod_eq_card]
    exact Fintype.card_ne_zero⟩

end MulAction

section Group

open Subgroup

variable {α : Type*} [Group α] (a : α)

/-- See also `Fintype.card_zpowers`. -/
@[to_additive (attr := simp) /-- See also `Fintype.card_zmultiples`. -/]
/--
theorem `Nat.card_zpowers` / 定理 `Nat.card_zpowers`

English:
theorem Nat.card_zpowers
  statement: Nat.card (zpowers a) = orderOf a
  proof: by
  have := Nat.card_congr (MulAction.orbitZPowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this

中文:
定理 Nat.card_zpowers
  结论: 自然数.card (zpowers a) = orderOf a
  证明: by
  have := Nat.card_congr (MulAction.orbitZPowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this

Depends on / 依赖: MulAction, MulAction.orbitZPowersEquiv, Nat.card_congr, Nat.card_zmod, card_congr, card_zmod, orbitZPowersEquiv, orbit_subgroup_one_eq_self
-/
theorem Nat.card_zpowers : Nat.card (zpowers a) = orderOf a := by
  have := Nat.card_congr (MulAction.orbitZPowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this

variable {a}

@[to_additive (attr := simp)]
/--
lemma `finite_zpowers` / 引理 `finite_zpowers`

English:
lemma finite_zpowers
  statement: (zpowers a : Set α).Finite ↔ IsOfFinOrder a
  proof: by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, OneMemClass.coe_nonempty, true_and]

@[to_additive (attr := simp)]

中文:
引理 finite_zpowers
  结论: (zpowers a : Set α).Finite ↔ IsOfFinOrder a
  证明: by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, OneMemClass.coe_nonempty, true_and]

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.card_pos_iff, Nat.card_zpowers, OneMemClass, OneMemClass.coe_nonempty, Set.finite_coe_iff, SetLike, SetLike.coe_sort_coe, card_pos_iff, card_zpowers, coe_nonempty, coe_sort_coe, finite_coe_iff, nonempty_coe_sort, orderOf_pos_iff, true_and
-/
lemma finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrder a := by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, OneMemClass.coe_nonempty, true_and]

@[to_additive (attr := simp)]
/--
lemma `infinite_zpowers` / 引理 `infinite_zpowers`

English:
lemma infinite_zpowers
  statement: (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a
  proof: finite_zpowers.not

@[to_additive]
protected alias ⟨_, IsOfFinOrder.finite_zpowers⟩ := finite_zpowers

中文:
引理 infinite_zpowers
  结论: (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a
  证明: finite_zpowers.not

@[to_additive]
protected alias ⟨_, IsOfFinOrder.finite_zpowers⟩ := finite_zpowers

Depends on / 依赖: finite_zpowers, finite_zpowers.not
-/
lemma infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a := finite_zpowers.not

@[to_additive]
protected alias ⟨_, IsOfFinOrder.finite_zpowers⟩ := finite_zpowers

end Group

namespace Subgroup
variable {G : Type*} [Group G] (H : Subgroup G) (g : G)

open Equiv Function MulAction

/--
Definition of `quotientEquivSigmaZMod` / `quotientEquivSigmaZMod` 的定义

English:
definition quotientEquivSigmaZMod
  signature: :
  body: (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

中文:
定义 quotientEquivSigmaZMod
  签名: :
  定义体: (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

Depends on / 依赖: orbitZPowersEquiv, q.out, selfEquivSigmaOrbits, sigmaCongrRight, zpowers
-/
noncomputable def quotientEquivSigmaZMod :
    G ⧸ H ≃ Σ q : orbitRel.Quotient (zpowers g) (G ⧸ H), ZMod (minimalPeriod (g • ·) q.out) :=
  (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

/--
lemma `quotientEquivSigmaZMod_symm_apply` / 引理 `quotientEquivSigmaZMod_symm_apply`

English:
lemma quotientEquivSigmaZMod_symm_apply
  statement: (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
  proof: rfl

中文:
引理 quotientEquivSigmaZMod_symm_apply
  结论: (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
  证明: rfl
-/
lemma quotientEquivSigmaZMod_symm_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    (quotientEquivSigmaZMod H g).symm ⟨q, k⟩ = g ^ (cast k : Int) • q.out := rfl

/--
lemma `quotientEquivSigmaZMod_apply` / 引理 `quotientEquivSigmaZMod_apply`

English:
lemma quotientEquivSigmaZMod_apply
  given: (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : Int)
  proof: by
  rw [← eq_symm_apply]; rw [quotientEquivSigmaZMod_symm_apply]; rw [ZMod.coe_intCast]; rw [zpow_smul_mod_minimalPeriod]

中文:
引理 quotientEquivSigmaZMod_apply
  条件: (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : 整数)
  证明: by
  rw [← eq_symm_apply]; rw [quotientEquivSigmaZMod_symm_apply]; rw [ZMod.coe_intCast]; rw [zpow_smul_mod_minimalPeriod]

Depends on / 依赖: ZMod.coe_intCast, coe_intCast, eq_symm_apply, quotientEquivSigmaZMod_symm_apply, zpow_smul_mod_minimalPeriod
-/
lemma quotientEquivSigmaZMod_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : Int) :
    quotientEquivSigmaZMod H g (g ^ k • q.out) = ⟨q, k⟩ := by
  rw [← eq_symm_apply]; rw [quotientEquivSigmaZMod_symm_apply]; rw [ZMod.coe_intCast]; rw [zpow_smul_mod_minimalPeriod]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `index_eq_sum_minimalPeriod` / 引理 `index_eq_sum_minimalPeriod`

English:
lemma index_eq_sum_minimalPeriod
  statement: (g : G) [Finite (G ⧸ H)]
  proof: by
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have (q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H))) :
      Fintype (MulAction.orbit (zpowers g) q.out) := Fintype.ofFinite _
  simp only [MulAction.minimalPeriod_eq_card, index_eq_card, Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma

中文:
引理 index_eq_sum_minimalPeriod
  结论: (g : G) [Finite (G ⧸ H)]
  证明: by
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have (q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H))) :
      Fintype (MulAction.orbit (zpowers g) q.out) := Fintype.ofFinite _
  simp only [MulAction.minimalPeriod_eq_card, index_eq_card, Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma

Depends on / 依赖: Fintype, Fintype.card_congr, Fintype.card_sigma, Fintype.ofFinite, MulAction, MulAction.minimalPeriod_eq_card, MulAction.orbit, MulAction.orbitRel, MulAction.selfEquivSigmaOrbits, Nat.card_eq_fintype_card, Quotient, card_congr, card_eq_fintype_card, card_sigma, index_eq_card, minimalPeriod_eq_card, ofFinite, orbitRel, q.out, selfEquivSigmaOrbits
-/
lemma index_eq_sum_minimalPeriod (g : G) [Finite (G ⧸ H)]
    [Fintype (Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H)))] :
    H.index = ∑ q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H)),
      Function.minimalPeriod (g • ·) q.out := by
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have (q : Quotient (MulAction.orbitRel (zpowers g) (G ⧸ H))) :
      Fintype (MulAction.orbit (zpowers g) q.out) := Fintype.ofFinite _
  simp only [MulAction.minimalPeriod_eq_card, index_eq_card, Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (MulAction.selfEquivSigmaOrbits (zpowers g) (G ⧸ H))

end Subgroup
