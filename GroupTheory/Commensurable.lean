/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Commensurability for subgroups

Two subgroups `H` and `K` of a group `G` are commensurable if `H ∩ K` has finite index in both `H`
and `K`.

This file defines commensurability for subgroups of a group `G`. It goes on to prove that
commensurability defines an equivalence relation on subgroups of `G` and finally defines the
commensurator of a subgroup `H` of `G`, which is the elements `g` of `G` such that `gHg⁻¹` is
commensurable with `H`.

## Main definitions

* `Commensurable H K`: the statement that the subgroups `H` and `K` of `G` are commensurable.
* `commensurator H`: the commensurator of a subgroup `H` of `G`.

## Implementation details

We define the commensurator of a subgroup `H` of `G` by first defining it as a subgroup of
`(conjAct G)`, which we call `commensurator'` and then taking the pre-image under
the map `G → (conjAct G)` to obtain our commensurator as a subgroup of `G`.

We define `Commensurable` both for additive and multiplicative groups (in the `AddSubgroup` and
`Subgroup` namespaces respectively); but `Commensurator` is not additivized, since it is not an
interesting concept for abelian groups, and it would be unusual to write a non-abelian group
additively.
-/

@[expose] public section

open scoped Pointwise

variable {G : Type*} [Group G]

/--
Definition of `Subgroup.quotConjEquiv` / `Subgroup.quotConjEquiv` 的定义

English:
definition Subgroup.quotConjEquiv
  signature: (H K : Subgroup G) (g : ConjAct G)
  body: Quotient.congr (K.equivSMul g).toEquiv fun a b => by
    dsimp
    rw [← Quotient.eq'']; rw [← Quotient.eq'']; rw [QuotientGroup.eq]; rw [QuotientGroup.eq]; rw [mem_subgroupOf]; rw [mem_subgroupOf]; rw [← map_inv]; rw [← map_mul]; rw [equivSMul_apply_coe]
    exact smul_mem_pointwise_smul_iff.symm

中文:
定义 Subgroup.quotConjEquiv
  签名: (H K : Subgroup G) (g : ConjAct G)
  定义体: Quotient.congr (K.equivSMul g).toEquiv fun a b => by
    dsimp
    rw [← Quotient.eq'']; rw [← Quotient.eq'']; rw [QuotientGroup.eq]; rw [QuotientGroup.eq]; rw [mem_subgroupOf]; rw [mem_subgroupOf]; rw [← map_inv]; rw [← map_mul]; rw [equivSMul_apply_coe]
    exact smul_mem_pointwise_smul_iff.symm

Depends on / 依赖: K.equivSMul, Quotient, Quotient.congr, Quotient.eq, QuotientGroup, QuotientGroup.eq, equivSMul, equivSMul_apply_coe, map_inv, map_mul, mem_subgroupOf, smul_mem_pointwise_smul_iff, smul_mem_pointwise_smul_iff.symm, toEquiv
-/
def Subgroup.quotConjEquiv (H K : Subgroup G) (g : ConjAct G) :
    K ⧸ H.subgroupOf K ≃ (g • K : Subgroup G) ⧸ (g • H).subgroupOf (g • K) :=
  Quotient.congr (K.equivSMul g).toEquiv fun a b => by
    dsimp
    rw [← Quotient.eq'']; rw [← Quotient.eq'']; rw [QuotientGroup.eq]; rw [QuotientGroup.eq]; rw [mem_subgroupOf]; rw [mem_subgroupOf]; rw [← map_inv]; rw [← map_mul]; rw [equivSMul_apply_coe]
    exact smul_mem_pointwise_smul_iff.symm

/-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both `H` and `K`. -/
@[to_additive /-- Two subgroups `H K` of `G` are commensurable if `H ⊓ K` has finite index in both
`H` and `K`. -/]
/--
Definition of `Subgroup.Commensurable` / `Subgroup.Commensurable` 的定义

English:
definition Subgroup.Commensurable
  signature: (H K : Subgroup G)
  body: H.relIndex K != 0 ∧ K.relIndex H != 0

中文:
定义 Subgroup.Commensurable
  签名: (H K : Subgroup G)
  定义体: H.relIndex K != 0 ∧ K.relIndex H != 0

Depends on / 依赖: H.relIndex, K.relIndex, relIndex
-/
def Subgroup.Commensurable (H K : Subgroup G) : Prop :=
  H.relIndex K != 0 ∧ K.relIndex H != 0

namespace Subgroup.Commensurable

@[to_additive (attr := refl)]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (H : Subgroup G)
  statement: Commensurable H H
  proof: by simp [Commensurable]

@[to_additive]

中文:
定理 refl
  条件: (H : Subgroup G)
  结论: Commensurable H H
  证明: by simp [Commensurable]

@[to_additive]
-/
protected theorem refl (H : Subgroup G) : Commensurable H H := by simp [Commensurable]

@[to_additive]
/--
theorem `comm` / 定理 `comm`

English:
theorem comm
  given: {H K : Subgroup G}
  statement: Commensurable H K ↔ Commensurable K H
  proof: and_comm

@[to_additive (attr := symm)]

中文:
定理 comm
  条件: {H K : Subgroup G}
  结论: Commensurable H K ↔ Commensurable K H
  证明: and_comm

@[to_additive (attr := symm)]

Depends on / 依赖: and_comm
-/
theorem comm {H K : Subgroup G} : Commensurable H K ↔ Commensurable K H := and_comm

@[to_additive (attr := symm)]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {H K : Subgroup G}
  statement: Commensurable H K -> Commensurable K H
  proof: And.symm

@[to_additive (attr := trans)]

中文:
定理 symm
  条件: {H K : Subgroup G}
  结论: Commensurable H K -> Commensurable K H
  证明: And.symm

@[to_additive (attr := trans)]

Depends on / 依赖: And.symm
-/
theorem symm {H K : Subgroup G} : Commensurable H K -> Commensurable K H := And.symm

@[to_additive (attr := trans)]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable K L)
  proof: ⟨Subgroup.relIndex_ne_zero_trans hhk.1 hkl.1, Subgroup.relIndex_ne_zero_trans hkl.2 hhk.2⟩

@[to_additive]

中文:
定理 trans
  条件: {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable K L)
  证明: ⟨Subgroup.relIndex_ne_zero_trans hhk.1 hkl.1, Subgroup.relIndex_ne_zero_trans hkl.2 hhk.2⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.relIndex_ne_zero_trans, relIndex_ne_zero_trans
-/
theorem trans {H K L : Subgroup G} (hhk : Commensurable H K) (hkl : Commensurable K L) :
    Commensurable H L :=
  ⟨Subgroup.relIndex_ne_zero_trans hhk.1 hkl.1, Subgroup.relIndex_ne_zero_trans hkl.2 hhk.2⟩

@[to_additive]
/--
theorem `equivalence` / 定理 `equivalence`

English:
theorem equivalence
  statement: Equivalence (@Commensurable G _)
  proof: ⟨Commensurable.refl, fun h => Commensurable.symm h, fun h₁ h₂ => Commensurable.trans h₁ h₂⟩

中文:
定理 equivalence
  结论: Equivalence (@Commensurable G _)
  证明: ⟨Commensurable.refl, fun h => Commensurable.symm h, fun h₁ h₂ => Commensurable.trans h₁ h₂⟩

Depends on / 依赖: Commensurable, Commensurable.refl, Commensurable.symm, Commensurable.trans
-/
theorem equivalence : Equivalence (@Commensurable G _) :=
  ⟨Commensurable.refl, fun h => Commensurable.symm h, fun h₁ h₂ => Commensurable.trans h₁ h₂⟩

/--
theorem `commensurable_conj` / 定理 `commensurable_conj`

English:
theorem commensurable_conj
  given: {H K : Subgroup G} (g : ConjAct G)
  proof: and_congr (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv H K g))))
    (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv K H g))))

中文:
定理 commensurable_conj
  条件: {H K : Subgroup G} (g : ConjAct G)
  证明: and_congr (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv H K g))))
    (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv K H g))))

Depends on / 依赖: Eq.congr_left, Nat.card_congr, and_congr, card_congr, congr_left, not_iff_not, not_iff_not.mpr, quotConjEquiv
-/
theorem commensurable_conj {H K : Subgroup G} (g : ConjAct G) :
    Commensurable H K ↔ Commensurable (g • H) (g • K) :=
  and_congr (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv H K g))))
    (not_iff_not.mpr (Eq.congr_left (Nat.card_congr (quotConjEquiv K H g))))

/--
theorem `conj` / 定理 `conj`

English:
theorem conj
  given: {H K : Subgroup G} (h : Commensurable H K) (g : ConjAct G)
  proof: (commensurable_conj g).mp h

中文:
定理 conj
  条件: {H K : Subgroup G} (h : Commensurable H K) (g : ConjAct G)
  证明: (commensurable_conj g).mp h

Depends on / 依赖: commensurable_conj
-/
theorem conj {H K : Subgroup G} (h : Commensurable H K) (g : ConjAct G) :
    Commensurable (g • H) (g • K) :=
  (commensurable_conj g).mp h

/--
theorem `commensurable_inv` / 定理 `commensurable_inv`

English:
theorem commensurable_inv
  given: (H : Subgroup G) (g : ConjAct G)
  proof: by rw [commensurable_conj, inv_smul_smul]

中文:
定理 commensurable_inv
  条件: (H : Subgroup G) (g : ConjAct G)
  证明: by rw [commensurable_conj, inv_smul_smul]

Depends on / 依赖: commensurable_conj, inv_smul_smul
-/
theorem commensurable_inv (H : Subgroup G) (g : ConjAct G) :
    Commensurable (g • H) H ↔ Commensurable H (g⁻¹ • H) := by rw [commensurable_conj, inv_smul_smul]

/--
Definition of `commensurator'` / `commensurator'` 的定义

English:
definition commensurator'
  signature: (H : Subgroup G)
  body: { g : ConjAct G | Commensurable (g • H) H }
  one_mem' := by rw [Set.mem_ofPred_eq, one_smul]
  mul_mem' ha hb := by
    rw [Set.mem_ofPred_eq]; rw [mul_smul]
    exact trans ((commensurable_conj _).mp hb) ha
  inv_mem' _ := by rwa [Set.mem_ofPred_eq, comm, ← commensurable_inv]

中文:
定义 commensurator'
  签名: (H : Subgroup G)
  定义体: { g : ConjAct G | Commensurable (g • H) H }
  one_mem' := by rw [Set.mem_ofPred_eq, one_smul]
  mul_mem' ha hb := by
    rw [Set.mem_ofPred_eq]; rw [mul_smul]
    exact trans ((commensurable_conj _).mp hb) ha
  inv_mem' _ := by rwa [Set.mem_ofPred_eq, comm, ← commensurable_inv]

Depends on / 依赖: Commensurable, ConjAct
-/
def commensurator' (H : Subgroup G) : Subgroup (ConjAct G) where
  carrier := { g : ConjAct G | Commensurable (g • H) H }
  one_mem' := by rw [Set.mem_ofPred_eq, one_smul]
  mul_mem' ha hb := by
    rw [Set.mem_ofPred_eq]; rw [mul_smul]
    exact trans ((commensurable_conj _).mp hb) ha
  inv_mem' _ := by rwa [Set.mem_ofPred_eq, comm, ← commensurable_inv]

/--
Definition of `commensurator` / `commensurator` 的定义

English:
definition commensurator
  signature: (H : Subgroup G)
  body: (commensurator' H).comap ConjAct.toConjAct.toMonoidHom

@[simp]

中文:
定义 commensurator
  签名: (H : Subgroup G)
  定义体: (commensurator' H).comap ConjAct.toConjAct.toMonoidHom

@[simp]

Depends on / 依赖: ConjAct, ConjAct.toConjAct.toMonoidHom, commensurator, toConjAct, toMonoidHom
-/
def commensurator (H : Subgroup G) : Subgroup G :=
  (commensurator' H).comap ConjAct.toConjAct.toMonoidHom

@[simp]
/--
theorem `commensurator'_mem_iff` / 定理 `commensurator'_mem_iff`

English:
theorem commensurator'_mem_iff
  given: (H : Subgroup G) (g : ConjAct G)
  proof: Iff.rfl

@[simp]

中文:
定理 commensurator'_mem_iff
  条件: (H : Subgroup G) (g : ConjAct G)
  证明: Iff.rfl

@[simp]
-/
theorem commensurator'_mem_iff (H : Subgroup G) (g : ConjAct G) :
    g in commensurator' H ↔ Commensurable (g • H) H := Iff.rfl

@[simp]
/--
theorem `commensurator_mem_iff` / 定理 `commensurator_mem_iff`

English:
theorem commensurator_mem_iff
  given: (H : Subgroup G) (g : G)
  proof: Iff.rfl

中文:
定理 commensurator_mem_iff
  条件: (H : Subgroup G) (g : G)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem commensurator_mem_iff (H : Subgroup G) (g : G) :
    g in commensurator H ↔ Commensurable (ConjAct.toConjAct g • H) H := Iff.rfl

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {H K : Subgroup G} (hk : Commensurable H K)
  statement: commensurator H = commensurator K
  proof: Subgroup.ext fun x =>
    let hx := (commensurable_conj x).1 hk
    ⟨fun h => hx.symm.trans (h.trans hk), fun h => hx.trans (h.trans hk.symm)⟩

中文:
定理 eq
  条件: {H K : Subgroup G} (hk : Commensurable H K)
  结论: commensurator H = commensurator K
  证明: Subgroup.ext fun x =>
    let hx := (commensurable_conj x).1 hk
    ⟨fun h => hx.symm.trans (h.trans hk), fun h => hx.trans (h.trans hk.symm)⟩

Depends on / 依赖: Subgroup, Subgroup.ext, commensurable_conj, h.trans, hk.symm, hx.symm.trans, hx.trans
-/
theorem eq {H K : Subgroup G} (hk : Commensurable H K) : commensurator H = commensurator K :=
  Subgroup.ext fun x =>
    let hx := (commensurable_conj x).1 hk
    ⟨fun h => hx.symm.trans (h.trans hk), fun h => hx.trans (h.trans hk.symm)⟩

end Subgroup.Commensurable
