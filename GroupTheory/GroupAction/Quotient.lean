/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Properties of group actions involving quotient groups

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'`
* Burnside's lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`,

as well as their analogues for additive groups.
-/

@[expose] public section

assert_not_exists Cardinal

universe u v w

variable {G : Type u} {X : Type v}

open Function

open scoped commutatorElement

namespace MulAction

variable [Group G]

section QuotientAction

open Subgroup MulOpposite QuotientGroup

variable (X) [Monoid X] [MulAction X G] (H : Subgroup G)

/--
Definition of `QuotientAction` / `QuotientAction` 的定义

English:
class QuotientAction
  parameters: : Prop where
  axioms and operations (1):
    - inv_mul_mem : forall (b : X) {a a' : G}, a⁻¹ * a' in H -> (b • a)⁻¹ * b • a' in H

中文:
类 QuotientAction
  参数: : 命题 where
  公理与运算 (1 个):
    - inv_mul_mem : 对任意 (b : X) {a a' : G}, a⁻¹ * a' in H -> (b • a)⁻¹ * b • a' in H
-/
class QuotientAction : Prop where
  /-- The action fulfils a normality condition on products that lie in `H`.
    This ensures that the action descends to an action on the quotient `G ⧸ H`. -/
  inv_mul_mem : forall (b : X) {a a' : G}, a⁻¹ * a' in H -> (b • a)⁻¹ * b • a' in H

/--
Definition of `_root_.AddAction.QuotientAction` / `_root_.AddAction.QuotientAction` 的定义

English:
class _root_.AddAction.QuotientAction
  parameters: {G : Type u} (X : Type v) [AddGroup G] [AddMonoid X]
  axioms and operations (1):
    - inv_mul_mem : forall (x : X) {g g' : G}, -g + g' in H -> -(x +ᵥ g) + (x +ᵥ g') in H

中文:
类 _root_.AddAction.QuotientAction
  参数: {G : 类型u} (X : 类型v) [AddGroup G] [AddMonoid X]
  公理与运算 (1 个):
    - inv_mul_mem : 对任意 (x : X) {g g' : G}, -g + g' in H -> -(x +ᵥ g) + (x +ᵥ g') in H
-/
class _root_.AddAction.QuotientAction {G : Type u} (X : Type v) [AddGroup G] [AddMonoid X]
  [AddAction X G] (H : AddSubgroup G) : Prop where
  /-- The action fulfils a normality condition on summands that lie in `H`.
    This ensures that the action descends to an action on the quotient `G ⧸ H`. -/
  inv_mul_mem : forall (x : X) {g g' : G}, -g + g' in H -> -(x +ᵥ g) + (x +ᵥ g') in H

attribute [to_additive] MulAction.QuotientAction

@[to_additive]
/--
Instance `left_quotientAction` / 实例 `left_quotientAction`

English:
instance left_quotientAction
  signature: : QuotientAction G H
  body: ⟨fun _ _ _ _ => by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩

@[to_additive]

中文:
实例 left_quotientAction
  签名: : QuotientAction G H
  定义体: ⟨fun _ _ _ _ => by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩

@[to_additive]

Depends on / 依赖: inv_mul_cancel_left, mul_assoc, mul_inv_rev, smul_eq_mul
-/
instance left_quotientAction : QuotientAction G H :=
  ⟨fun _ _ _ _ => by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩

@[to_additive]
/--
Instance `right_quotientAction` / 实例 `right_quotientAction`

English:
instance right_quotientAction
  signature: : QuotientAction (normalizer H : Subgroup G).op H
  body: ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive]

中文:
实例 right_quotientAction
  签名: : QuotientAction (normalizer H : Subgroup G).op H
  定义体: ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive]

Depends on / 依赖: b.prop, mem_normalizer_iff, mul_assoc, mul_inv_cancel_left, mul_inv_rev, smul_def, smul_eq_mul_unop
-/
instance right_quotientAction : QuotientAction (normalizer H : Subgroup G).op H :=
  ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive]
/--
Instance `right_quotientAction'` / 实例 `right_quotientAction'`

English:
instance right_quotientAction'
  signature: [hH : H.Normal]
  body: ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc,
      mul_inv_cancel_right]⟩

@[to_additive]

中文:
实例 right_quotientAction'
  签名: [hH : H.Normal]
  定义体: ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc,
      mul_inv_cancel_right]⟩

@[to_additive]

Depends on / 依赖: hH.mem_comm_iff, mem_comm_iff, mul_assoc, mul_inv_cancel_right, mul_inv_rev, smul_eq_mul_unop
-/
instance right_quotientAction' [hH : H.Normal] : QuotientAction Gᵐᵒᵖ H :=
  ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc,
      mul_inv_cancel_right]⟩

@[to_additive]
/--
Instance `quotient` / 实例 `quotient`

English:
instance quotient
  signature: [QuotientAction X H]
  body: Quotient.map' (b • ·) fun _ _ h =>
leftRel_apply.mpr QuotientAction.inv_mul_mem b leftRel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (one_smul X a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (mul_smul b b' a)

中文:
实例 quotient
  签名: [QuotientAction X H]
  定义体: Quotient.map' (b • ·) fun _ _ h =>
leftRel_apply.mpr QuotientAction.inv_mul_mem b leftRel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (one_smul X a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (mul_smul b b' a)

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.map, Quotient.mk, QuotientAction, QuotientAction.inv_mul_mem, congr_arg, inductionOn, inv_mul_mem, leftRel_apply, leftRel_apply.mp, leftRel_apply.mpr, mul_smul, one_smul
-/
instance quotient [QuotientAction X H] : MulAction X (G ⧸ H) where
  smul b :=
    Quotient.map' (b • ·) fun _ _ h =>
leftRel_apply.mpr QuotientAction.inv_mul_mem b leftRel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (one_smul X a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (mul_smul b b' a)

variable {X}

@[to_additive (attr := simp)]
/--
theorem `Quotient.smul_mk` / 定理 `Quotient.smul_mk`

English:
theorem Quotient.smul_mk
  given: [QuotientAction X H] (b : X) (g : G)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 Quotient.smul_mk
  条件: [QuotientAction X H] (b : X) (g : G)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem Quotient.smul_mk [QuotientAction X H] (b : X) (g : G) :
    (b • QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (b • g) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `Quotient.smul_coe` / 定理 `Quotient.smul_coe`

English:
theorem Quotient.smul_coe
  given: [QuotientAction X H] (b : X) (g : G)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 Quotient.smul_coe
  条件: [QuotientAction X H] (b : X) (g : G)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem Quotient.smul_coe [QuotientAction X H] (b : X) (g : G) :
    b • (g : G ⧸ H) = (↑(b • g) : G ⧸ H) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `Quotient.mk_smul_out` / 定理 `Quotient.mk_smul_out`

English:
theorem Quotient.mk_smul_out
  given: [QuotientAction X H] (b : X) (q : G ⧸ H)
  proof: by rw [← Quotient.smul_mk, QuotientGroup.out_eq']

@[to_additive]

中文:
定理 Quotient.mk_smul_out
  条件: [QuotientAction X H] (b : X) (q : G ⧸ H)
  证明: by rw [← Quotient.smul_mk, QuotientGroup.out_eq']

@[to_additive]

Depends on / 依赖: Quotient, Quotient.smul_mk, QuotientGroup, QuotientGroup.out_eq, out_eq, smul_mk
-/
theorem Quotient.mk_smul_out [QuotientAction X H] (b : X) (q : G ⧸ H) :
    QuotientGroup.mk (b • q.out) = b • q := by rw [← Quotient.smul_mk, QuotientGroup.out_eq']

@[to_additive]
/--
theorem `Quotient.coe_smul_out` / 定理 `Quotient.coe_smul_out`

English:
theorem Quotient.coe_smul_out
  given: [QuotientAction X H] (b : X) (q : G ⧸ H)
  statement: ↑(b • q.out) = b • q
  proof: by
  simp

中文:
定理 Quotient.coe_smul_out
  条件: [QuotientAction X H] (b : X) (q : G ⧸ H)
  结论: ↑(b • q.out) = b • q
  证明: by
  simp
-/
theorem Quotient.coe_smul_out [QuotientAction X H] (b : X) (q : G ⧸ H) : ↑(b • q.out) = b • q := by
  simp

/--
theorem `_root_.QuotientGroup.out_conj_pow_minimalPeriod_mem` / 定理 `_root_.QuotientGroup.out_conj_pow_minimalPeriod_mem`

English:
theorem _root_.QuotientGroup.out_conj_pow_minimalPeriod_mem
  given: (g : G) (q : G ⧸ H)
  proof: by
  rw [mul_assoc]; rw [← QuotientGroup.eq]; rw [QuotientGroup.out_eq']; rw [← smul_eq_mul]; rw [Quotient.mk_smul_out]; rw [eq_comm]; rw [pow_smul_eq_iff_minimalPeriod_dvd]

中文:
定理 _root_.QuotientGroup.out_conj_pow_minimalPeriod_mem
  条件: (g : G) (q : G ⧸ H)
  证明: by
  rw [mul_assoc]; rw [← QuotientGroup.eq]; rw [QuotientGroup.out_eq']; rw [← smul_eq_mul]; rw [Quotient.mk_smul_out]; rw [eq_comm]; rw [pow_smul_eq_iff_minimalPeriod_dvd]

Depends on / 依赖: Quotient, Quotient.mk_smul_out, QuotientGroup, QuotientGroup.eq, QuotientGroup.out_eq, eq_comm, mk_smul_out, mul_assoc, out_eq, pow_smul_eq_iff_minimalPeriod_dvd, smul_eq_mul
-/
theorem _root_.QuotientGroup.out_conj_pow_minimalPeriod_mem (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q * q.out in H := by
  rw [mul_assoc]; rw [← QuotientGroup.eq]; rw [QuotientGroup.out_eq']; rw [← smul_eq_mul]; rw [Quotient.mk_smul_out]; rw [eq_comm]; rw [pow_smul_eq_iff_minimalPeriod_dvd]

end QuotientAction

open QuotientGroup

/--
Definition of `_root_.MulActionHom.toQuotient` / `_root_.MulActionHom.toQuotient` 的定义

English:
definition _root_.MulActionHom.toQuotient
  signature: (H : Subgroup G)
  body: (↑); map_smul' := Quotient.smul_coe H

@[simp]

中文:
定义 _root_.MulActionHom.toQuotient
  签名: (H : Subgroup G)
  定义体: (↑); map_smul' := Quotient.smul_coe H

@[simp]

Depends on / 依赖: Quotient, Quotient.smul_coe, map_smul, smul_coe
-/
def _root_.MulActionHom.toQuotient (H : Subgroup G) : G ->[G] G ⧸ H where
  toFun := (↑); map_smul' := Quotient.smul_coe H

@[simp]
/--
theorem `_root_.MulActionHom.toQuotient_apply` / 定理 `_root_.MulActionHom.toQuotient_apply`

English:
theorem _root_.MulActionHom.toQuotient_apply
  given: (H : Subgroup G) (g : G)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 _root_.MulActionHom.toQuotient_apply
  条件: (H : Subgroup G) (g : G)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem _root_.MulActionHom.toQuotient_apply (H : Subgroup G) (g : G) :
    MulActionHom.toQuotient H g = g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coe_quotient_smul` / 定理 `coe_quotient_smul`

English:
theorem coe_quotient_smul
  statement: {H : Subgroup G} [H.Normal] [SMul G X]
  proof: by
  rw [← smul_one_smul (G ⧸ H) g x]; rw [← QuotientGroup.mk_one]; rw [Quotient.smul_coe]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive]

中文:
定理 coe_quotient_smul
  结论: {H : Subgroup G} [H.Normal] [SMul G X]
  证明: by
  rw [← smul_one_smul (G ⧸ H) g x]; rw [← QuotientGroup.mk_one]; rw [Quotient.smul_coe]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive]

Depends on / 依赖: Quotient, Quotient.smul_coe, QuotientGroup, QuotientGroup.mk_one, mk_one, mul_one, smul_coe, smul_eq_mul, smul_one_smul
-/
theorem coe_quotient_smul {H : Subgroup G} [H.Normal] [SMul G X]
    [MulAction (G ⧸ H) X] [IsScalarTower G (G ⧸ H) X] (g : G) (x : X) :
    (g : G ⧸ H) • x = g • x := by
  rw [← smul_one_smul (G ⧸ H) g x]; rw [← QuotientGroup.mk_one]; rw [Quotient.smul_coe]; rw [smul_eq_mul]; rw [mul_one]

@[to_additive]
/--
Instance `mulLeftCosetsCompSubtypeVal` / 实例 `mulLeftCosetsCompSubtypeVal`

English:
instance mulLeftCosetsCompSubtypeVal
  signature: (H I : Subgroup G)
  body: MulAction.compHom (G ⧸ H) (Subgroup.subtype I)

中文:
实例 mulLeftCosetsCompSubtypeVal
  签名: (H I : Subgroup G)
  定义体: MulAction.compHom (G ⧸ H) (Subgroup.subtype I)

Depends on / 依赖: MulAction, MulAction.compHom, Subgroup, Subgroup.subtype, compHom, subtype
-/
instance mulLeftCosetsCompSubtypeVal (H I : Subgroup G) : MulAction I (G ⧸ H) :=
  MulAction.compHom (G ⧸ H) (Subgroup.subtype I)

variable (G)
variable [MulAction G X] (x : X)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive /-- The canonical map from the quotient of the stabilizer to the set. -/]
/--
Definition of `ofQuotientStabilizer` / `ofQuotientStabilizer` 的定义

English:
definition ofQuotientStabilizer
  signature: (g : G ⧸ MulAction.stabilizer G x)
  body: Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]

@[to_additive (attr := simp)]

中文:
定义 ofQuotientStabilizer
  签名: (g : G ⧸ MulAction.stabilizer G x)
  定义体: Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]

@[to_additive (attr := simp)]

Depends on / 依赖: Quotient, Quotient.liftOn, congr_arg, leftRel_apply, leftRel_apply.mp, liftOn, mul_inv_cancel_left, smul_smul
-/
def ofQuotientStabilizer (g : G ⧸ MulAction.stabilizer G x) : X :=
  Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]

@[to_additive (attr := simp)]
/--
theorem `ofQuotientStabilizer_mk` / 定理 `ofQuotientStabilizer_mk`

English:
theorem ofQuotientStabilizer_mk
  given: (g : G)
  statement: ofQuotientStabilizer G x (QuotientGroup.mk g) = g • x
  proof: rfl

@[to_additive]

中文:
定理 ofQuotientStabilizer_mk
  条件: (g : G)
  结论: ofQuotientStabilizer G x (QuotientGroup.mk g) = g • x
  证明: rfl

@[to_additive]
-/
theorem ofQuotientStabilizer_mk (g : G) : ofQuotientStabilizer G x (QuotientGroup.mk g) = g • x :=
  rfl

@[to_additive]
/--
theorem `ofQuotientStabilizer_mem_orbit` / 定理 `ofQuotientStabilizer_mem_orbit`

English:
theorem ofQuotientStabilizer_mem_orbit
  given: (g)
  statement: ofQuotientStabilizer G x g in orbit G x
  proof: Quotient.inductionOn' g fun g => ⟨g, rfl⟩

@[to_additive]

中文:
定理 ofQuotientStabilizer_mem_orbit
  条件: (g)
  结论: ofQuotientStabilizer G x g in orbit G x
  证明: Quotient.inductionOn' g fun g => ⟨g, rfl⟩

@[to_additive]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem ofQuotientStabilizer_mem_orbit (g) : ofQuotientStabilizer G x g in orbit G x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩

@[to_additive]
/--
theorem `ofQuotientStabilizer_smul` / 定理 `ofQuotientStabilizer_smul`

English:
theorem ofQuotientStabilizer_smul
  given: (g : G) (g' : G ⧸ MulAction.stabilizer G x)
  proof: Quotient.inductionOn' g' fun _ => mul_smul _ _ _

@[to_additive]

中文:
定理 ofQuotientStabilizer_smul
  条件: (g : G) (g' : G ⧸ MulAction.stabilizer G x)
  证明: Quotient.inductionOn' g' fun _ => mul_smul _ _ _

@[to_additive]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, mul_smul
-/
theorem ofQuotientStabilizer_smul (g : G) (g' : G ⧸ MulAction.stabilizer G x) :
    ofQuotientStabilizer G x (g • g') = g • ofQuotientStabilizer G x g' :=
  Quotient.inductionOn' g' fun _ => mul_smul _ _ _

@[to_additive]
/--
theorem `injective_ofQuotientStabilizer` / 定理 `injective_ofQuotientStabilizer`

English:
theorem injective_ofQuotientStabilizer
  statement: Function.Injective (ofQuotientStabilizer G x)
  proof: fun y₁ y₂ =>
  Quotient.inductionOn₂' y₁ y₂ fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
Quotient.sound' by
      rw [leftRel_apply]
      change (g₁⁻¹ * g₂) • x = x
      rw [mul_smul]; rw [← H]; rw [inv_smul_smul]

中文:
定理 injective_ofQuotientStabilizer
  结论: Function.Injective (ofQuotientStabilizer G x)
  证明: fun y₁ y₂ =>
  Quotient.inductionOn₂' y₁ y₂ fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
Quotient.sound' by
      rw [leftRel_apply]
      change (g₁⁻¹ * g₂) • x = x
      rw [mul_smul]; rw [← H]; rw [inv_smul_smul]

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.sound, inv_smul_smul, leftRel_apply, mul_smul
-/
theorem injective_ofQuotientStabilizer : Function.Injective (ofQuotientStabilizer G x) :=
  fun y₁ y₂ =>
  Quotient.inductionOn₂' y₁ y₂ fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
Quotient.sound' by
      rw [leftRel_apply]
      change (g₁⁻¹ * g₂) • x = x
      rw [mul_smul]; rw [← H]; rw [inv_smul_smul]

/-- **Orbit-stabilizer theorem**. -/
@[to_additive /-- Orbit-stabilizer theorem. -/]
/--
Definition of `orbitEquivQuotientStabilizer` / `orbitEquivQuotientStabilizer` 的定义

English:
definition orbitEquivQuotientStabilizer
  signature: (b : X)
  body: Equiv.symm
    Equiv.ofBijective (fun g => ⟨ofQuotientStabilizer G b g, ofQuotientStabilizer_mem_orbit G b g⟩)
      ⟨fun x y hxy => injective_ofQuotientStabilizer G b (by convert! congr_arg Subtype.val hxy),
        fun ⟨_, ⟨g, hgb⟩⟩ => ⟨g, Subtype.ext hgb⟩⟩

中文:
定义 orbitEquivQuotientStabilizer
  签名: (b : X)
  定义体: Equiv.symm
    Equiv.ofBijective (fun g => ⟨ofQuotientStabilizer G b g, ofQuotientStabilizer_mem_orbit G b g⟩)
      ⟨fun x y hxy => injective_ofQuotientStabilizer G b (by convert! congr_arg Subtype.val hxy),
        fun ⟨_, ⟨g, hgb⟩⟩ => ⟨g, Subtype.ext hgb⟩⟩

Depends on / 依赖: Equiv.ofBijective, Equiv.symm, Subtype, Subtype.ext, Subtype.val, congr_arg, convert, injective_ofQuotientStabilizer, ofBijective, ofQuotientStabilizer, ofQuotientStabilizer_mem_orbit
-/
noncomputable def orbitEquivQuotientStabilizer (b : X) : orbit G b ≃ G ⧸ stabilizer G b :=
Equiv.symm
    Equiv.ofBijective (fun g => ⟨ofQuotientStabilizer G b g, ofQuotientStabilizer_mem_orbit G b g⟩)
      ⟨fun x y hxy => injective_ofQuotientStabilizer G b (by convert! congr_arg Subtype.val hxy),
        fun ⟨_, ⟨g, hgb⟩⟩ => ⟨g, Subtype.ext hgb⟩⟩

/-- Orbit-stabilizer theorem. -/
@[to_additive AddAction.orbitProdStabilizerEquivAddGroup /-- Orbit-stabilizer theorem. -/]
/--
Definition of `orbitProdStabilizerEquivGroup` / `orbitProdStabilizerEquivGroup` 的定义

English:
definition orbitProdStabilizerEquivGroup
  signature: (b : X)
  body: (Equiv.prodCongr (orbitEquivQuotientStabilizer G _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientProdSubgroup.symm

中文:
定义 orbitProdStabilizerEquivGroup
  签名: (b : X)
  定义体: (Equiv.prodCongr (orbitEquivQuotientStabilizer G _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientProdSubgroup.symm

Depends on / 依赖: Equiv.prodCongr, Equiv.refl, Subgroup, Subgroup.groupEquivQuotientProdSubgroup.symm, groupEquivQuotientProdSubgroup, orbitEquivQuotientStabilizer, prodCongr
-/
noncomputable def orbitProdStabilizerEquivGroup (b : X) : orbit G b × stabilizer G b ≃ G :=
  (Equiv.prodCongr (orbitEquivQuotientStabilizer G _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientProdSubgroup.symm

/-- Orbit-stabilizer theorem. -/
@[to_additive AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup
/-- Orbit-stabilizer theorem. -/]
/--
theorem `card_orbit_mul_card_stabilizer_eq_card_group` / 定理 `card_orbit_mul_card_stabilizer_eq_card_group`

English:
theorem card_orbit_mul_card_stabilizer_eq_card_group
  statement: (b : X) [Fintype G] [Fintype <| orbit G b]
  proof: by
  rw [← Fintype.card_prod]; rw [Fintype.card_congr (orbitProdStabilizerEquivGroup G b)]

@[to_additive (attr := simp)]

中文:
定理 card_orbit_mul_card_stabilizer_eq_card_group
  结论: (b : X) [Fintype G] [Fintype <| orbit G b]
  证明: by
  rw [← Fintype.card_prod]; rw [Fintype.card_congr (orbitProdStabilizerEquivGroup G b)]

@[to_additive (attr := simp)]

Depends on / 依赖: Fintype, Fintype.card_congr, Fintype.card_prod, card_congr, card_prod, orbitProdStabilizerEquivGroup
-/
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : X) [Fintype G] [Fintype <| orbit G b]
    [Fintype <| stabilizer G b] :
    Fintype.card (orbit G b) * Fintype.card (stabilizer G b) = Fintype.card G := by
  rw [← Fintype.card_prod]; rw [Fintype.card_congr (orbitProdStabilizerEquivGroup G b)]

@[to_additive (attr := simp)]
/--
theorem `orbitEquivQuotientStabilizer_symm_apply` / 定理 `orbitEquivQuotientStabilizer_symm_apply`

English:
theorem orbitEquivQuotientStabilizer_symm_apply
  given: (b : X) (g : G)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 orbitEquivQuotientStabilizer_symm_apply
  条件: (b : X) (g : G)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem orbitEquivQuotientStabilizer_symm_apply (b : X) (g : G) :
    ((orbitEquivQuotientStabilizer G b).symm g : X) = g • b :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `stabilizer_quotient` / 定理 `stabilizer_quotient`

English:
theorem stabilizer_quotient
  given: {G} [Group G] (H : Subgroup G)
  proof: by
  ext
  simp [QuotientGroup.eq]

中文:
定理 stabilizer_quotient
  条件: {G} [Group G] (H : Subgroup G)
  证明: by
  ext
  simp [QuotientGroup.eq]

Depends on / 依赖: QuotientGroup, QuotientGroup.eq
-/
theorem stabilizer_quotient {G} [Group G] (H : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  ext
  simp [QuotientGroup.eq]

variable (X)

local notation "Ω" => Quotient orbitRel G X

/-- **Class formula** : let `G` be a group acting on `X` and let `φ` be a function mapping each
orbit of `X` under this action (that is, each element of the quotient of `G` by the relation
`orbitRel G X`) to an element in this orbit. We provide a (noncomputable) bijection between `X`
and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω : Ω`. In most cases you'll want `φ`
to be `Quotient.out`, so we provide `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a
special case. -/
@[to_additive
    /-- **Class formula** : let `G` be an additive group acting on `X` and let `φ` be a function
    mapping each orbit of `X` under this action (that is, each element of the quotient of `X` by
    the relation `orbitRel G X`) to an element in this orbit. This definition is a (noncomputable)
    bijection between `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω : Ω`. In
    most cases you'll want `φ` to be `Quotient.out`, so we provide
      `AddAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a special case. -/]
/--
Definition of `selfEquivSigmaOrbitsQuotientStabilizer'` / `selfEquivSigmaOrbitsQuotientStabilizer'` 的定义

English:
definition selfEquivSigmaOrbitsQuotientStabilizer'
  signature: {φ : Ω -> X}
  body: calc
    X ≃ Σ ω : Ω, orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' G X
    _ ≃ Σ ω : Ω, G ⧸ stabilizer G (φ ω) :=
      Equiv.sigmaCongrRight fun ω =>
(Equiv.setCongr <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ).trans
          orbitEquivQuotientStabilizer G (φ ω)

中文:
定义 selfEquivSigmaOrbitsQuotientStabilizer'
  签名: {φ : Ω -> X}
  定义体: calc
    X ≃ Σ ω : Ω, orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' G X
    _ ≃ Σ ω : Ω, G ⧸ stabilizer G (φ ω) :=
      Equiv.sigmaCongrRight fun ω =>
(Equiv.setCongr <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ).trans
          orbitEquivQuotientStabilizer G (φ ω)

Depends on / 依赖: Equiv.setCongr, Equiv.sigmaCongrRight, Quotient, orbitEquivQuotientStabilizer, orbitRel, orbitRel.Quotient.orbit, orbitRel.Quotient.orbit_eq_orbit_out, orbit_eq_orbit_out, selfEquivSigmaOrbits, setCongr, sigmaCongrRight, stabilizer
-/
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω -> X}
    (hφ : LeftInverse Quotient.mk'' φ) : X ≃ Σ ω : Ω, G ⧸ stabilizer G (φ ω) :=
  calc
    X ≃ Σ ω : Ω, orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' G X
    _ ≃ Σ ω : Ω, G ⧸ stabilizer G (φ ω) :=
      Equiv.sigmaCongrRight fun ω =>
(Equiv.setCongr <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ).trans
          orbitEquivQuotientStabilizer G (φ ω)

/-- **Class formula**. This is a special case of
`MulAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out`. -/
@[to_additive
      /-- **Class formula**. This is a special case of
      `AddAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out`. -/]
/--
Definition of `selfEquivSigmaOrbitsQuotientStabilizer` / `selfEquivSigmaOrbitsQuotientStabilizer` 的定义

English:
definition selfEquivSigmaOrbitsQuotientStabilizer
  signature: : X ≃ Σ ω : Ω, G ⧸ stabilizer G ω.out
  body: selfEquivSigmaOrbitsQuotientStabilizer' G X Quotient.out_eq'

中文:
定义 selfEquivSigmaOrbitsQuotientStabilizer
  签名: : X ≃ Σ ω : Ω, G ⧸ stabilizer G ω.out
  定义体: selfEquivSigmaOrbitsQuotientStabilizer' G X Quotient.out_eq'

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq, selfEquivSigmaOrbitsQuotientStabilizer
-/
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer : X ≃ Σ ω : Ω, G ⧸ stabilizer G ω.out :=
  selfEquivSigmaOrbitsQuotientStabilizer' G X Quotient.out_eq'

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × Ω`, where `G` is a group acting on `X`
and `Ω = X/G` denotes the quotient of `X` by the relation `orbitRel G X`. -/
@[to_additive AddAction.sigmaFixedByEquivOrbitsProdAddGroup
      /-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
      `{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × Ω`, where `G` is an additive group
      acting on `X` and `Ω = X/G` denotes the quotient of `X` by the relation `orbitRel G X`. -/]
/--
Definition of `sigmaFixedByEquivOrbitsProdGroup` / `sigmaFixedByEquivOrbitsProdGroup` 的定义

English:
definition sigmaFixedByEquivOrbitsProdGroup
  signature: : (Σ g : G, fixedBy X g) ≃ Ω × G
  body: calc
    (Σ g : G, fixedBy X g) ≃ { ab : G × X // ab.1 • ab.2 = ab.2 } :=
      (Equiv.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : X × G // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm G X).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σ b : X, stabilizer G b :=
      Equiv.subtypeProdEquivSigmaSubtype f

中文:
定义 sigmaFixedByEquivOrbitsProdGroup
  签名: : (Σ g : G, fixedBy X g) ≃ Ω × G
  定义体: calc
    (Σ g : G, fixedBy X g) ≃ { ab : G × X // ab.1 • ab.2 = ab.2 } :=
      (Equiv.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : X × G // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm G X).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σ b : X, stabilizer G b :=
      Equiv.subtypeProdEquivSigmaSubtype f

Depends on / 依赖: Equiv.prodComm, Equiv.sigmaAssoc, Equiv.subtypeProdEquivSigmaSubtype, Iff.rfl, fixedBy, prodComm, selfEquivSigmaOrbits, sigmaAssoc, sigmaCongrLeft, stabilizer, subtypeEquiv, subtypeProdEquivSigmaSubtype
-/
noncomputable def sigmaFixedByEquivOrbitsProdGroup : (Σ g : G, fixedBy X g) ≃ Ω × G :=
  calc
    (Σ g : G, fixedBy X g) ≃ { ab : G × X // ab.1 • ab.2 = ab.2 } :=
      (Equiv.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : X × G // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm G X).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σ b : X, stabilizer G b :=
      Equiv.subtypeProdEquivSigmaSubtype fun (b : X) a => a in stabilizer G b
    _ ≃ Σ ωb : Σ ω : Ω, orbit G ω.out, stabilizer G (ωb.2 : X) :=
      (selfEquivSigmaOrbits G X).sigmaCongrLeft'
    _ ≃ Σ ω : Ω, Σ b : orbit G ω.out, stabilizer G (b : X) :=
      Equiv.sigmaAssoc fun (ω : Ω) (b : orbit G ω.out) => stabilizer G (b : X)
    _ ≃ Σ ω : Ω, Σ _ : orbit G ω.out, stabilizer G ω.out :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.sigmaCongrRight fun ⟨_, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σ ω : Ω, orbit G ω.out × stabilizer G ω.out :=
      Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _
    _ ≃ Σ _ : Ω, G := Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup G ω.out
    _ ≃ Ω × G := Equiv.sigmaEquivProd Ω G

/-- **Burnside's lemma** : given a finite group `G` acting on a type `X`, the sum the orders of the
stabilisers coincides with the number of orbits multiplied by the order of `G`. -/
@[to_additive (attr := wikidata Q1330377)
      AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
      /-- **Burnside's lemma** : given a finite additive group `G` acting on a type `X`,
      the sum the orders of the stabilisers coincides with the number of orbits multiplied by the
      order of `G`. -/]
/--
theorem `sum_card_fixedBy_eq_card_orbits_mul_card_group` / 定理 `sum_card_fixedBy_eq_card_orbits_mul_card_group`

English:
theorem sum_card_fixedBy_eq_card_orbits_mul_card_group
  statement: [Fintype G] [forall g : G, Fintype <| fixedBy X g]
  proof: by
  rw [← Fintype.card_prod]; rw [← Fintype.card_sigma]; rw [Fintype.card_congr (sigmaFixedByEquivOrbitsProdGroup G X)]

@[to_additive]

中文:
定理 sum_card_fixedBy_eq_card_orbits_mul_card_group
  结论: [Fintype G] [对任意 g : G, Fintype <| fixedBy X g]
  证明: by
  rw [← Fintype.card_prod]; rw [← Fintype.card_sigma]; rw [Fintype.card_congr (sigmaFixedByEquivOrbitsProdGroup G X)]

@[to_additive]

Depends on / 依赖: Fintype, Fintype.card_congr, Fintype.card_prod, Fintype.card_sigma, card_congr, card_prod, card_sigma, sigmaFixedByEquivOrbitsProdGroup
-/
theorem sum_card_fixedBy_eq_card_orbits_mul_card_group [Fintype G] [forall g : G, Fintype <| fixedBy X g]
    [Fintype Ω] : (∑ g : G, Fintype.card (fixedBy X g)) = Fintype.card Ω * Fintype.card G := by
  rw [← Fintype.card_prod]; rw [← Fintype.card_sigma]; rw [Fintype.card_congr (sigmaFixedByEquivOrbitsProdGroup G X)]

@[to_additive]
/--
Instance `isPretransitive_quotient` / 实例 `isPretransitive_quotient`

English:
instance isPretransitive_quotient
  signature: (G) [Group G] (H : Subgroup G)
  body: by
    { rintro ⟨x⟩ ⟨y⟩
      refine ⟨y * x⁻¹, QuotientGroup.eq.mpr ?_⟩
      simp only [smul_eq_mul, H.one_mem, inv_mul_cancel, inv_mul_cancel_right]}

中文:
实例 isPretransitive_quotient
  签名: (G) [Group G] (H : Subgroup G)
  定义体: by
    { rintro ⟨x⟩ ⟨y⟩
      refine ⟨y * x⁻¹, QuotientGroup.eq.mpr ?_⟩
      simp only [smul_eq_mul, H.one_mem, inv_mul_cancel, inv_mul_cancel_right]}

Depends on / 依赖: H.one_mem, QuotientGroup, QuotientGroup.eq.mpr, inv_mul_cancel, inv_mul_cancel_right, one_mem, smul_eq_mul
-/
instance isPretransitive_quotient (G) [Group G] (H : Subgroup G) : IsPretransitive G (G ⧸ H) where
  exists_smul_eq := by
    { rintro ⟨x⟩ ⟨y⟩
      refine ⟨y * x⁻¹, QuotientGroup.eq.mpr ?_⟩
      simp only [smul_eq_mul, H.one_mem, inv_mul_cancel, inv_mul_cancel_right]}

variable {G}

@[to_additive]
/--
Instance `finite_quotient_of_pretransitive_of_finite_quotient` / 实例 `finite_quotient_of_pretransitive_of_finite_quotient`

English:
instance finite_quotient_of_pretransitive_of_finite_quotient
  signature: [IsPretransitive G X] {H : Subgroup G}
  body: by
  rcases isEmpty_or_nonempty X with he | ⟨⟨b⟩⟩
  · exact Quotient.finite _
  · have h' : Finite (Quotient (rightRel H)) :=
      Finite.of_equiv _ (quotientRightRelEquivQuotientLeftRel _).symm
    let f : Quotient (rightRel H) -> orbitRel.Quotient H X :=
      fun a => Quotient.liftOn' a (fun g =

中文:
实例 finite_quotient_of_pretransitive_of_finite_quotient
  签名: [IsPretransitive G X] {H : Subgroup G}
  定义体: by
  rcases isEmpty_or_nonempty X with he | ⟨⟨b⟩⟩
  · exact Quotient.finite _
  · have h' : Finite (Quotient (rightRel H)) :=
      Finite.of_equiv _ (quotientRightRelEquivQuotientLeftRel _).symm
    let f : Quotient (rightRel H) -> orbitRel.Quotient H X :=
      fun a => Quotient.liftOn' a (fun g =

Depends on / 依赖: Finite, Finite.of_equiv, Finite.of_surjective, Quotient, Quotient.eq, Quotient.finite, Quotient.liftOn, Quotient.sur, Setoid, Setoid.symm, finite, isEmpty_or_nonempty, liftOn, mem_orbit_iff, mul_smul, of_equiv, of_surjective, orbitRel, orbitRel.Quotient, orbitRel_apply
-/
instance finite_quotient_of_pretransitive_of_finite_quotient [IsPretransitive G X] {H : Subgroup G}
[Finite (G ⧸ H)] : Finite orbitRel.Quotient H X := by
  rcases isEmpty_or_nonempty X with he | ⟨⟨b⟩⟩
  · exact Quotient.finite _
  · have h' : Finite (Quotient (rightRel H)) :=
      Finite.of_equiv _ (quotientRightRelEquivQuotientLeftRel _).symm
    let f : Quotient (rightRel H) -> orbitRel.Quotient H X :=
      fun a => Quotient.liftOn' a (fun g => ⟦g • b⟧) fun g₁ g₂ r => by
        replace r := Setoid.symm' _ r
        rw [rightRel_eq] at r
        simp only [Quotient.eq, orbitRel_apply, mem_orbit_iff]
        exact ⟨⟨g₁ * g₂⁻¹, r⟩, by simp [mul_smul]⟩
    exact Finite.of_surjective f ((Quotient.surjective_liftOn' _).2
      (Quotient.mk''_surjective.comp (MulAction.surjective_smul _ _)))

variable {X} in
/-- A bijection between the quotient of the action of a subgroup `H` on an orbit, and a
corresponding quotient expressed in terms of `Setoid.comap Subtype.val`. -/
@[to_additive /-- A bijection between the quotient of the action of an additive subgroup `H` on an
orbit, and a corresponding quotient expressed in terms of `Setoid.comap Subtype.val`. -/]
/--
Definition of `equivSubgroupOrbitsSetoidComap` / `equivSubgroupOrbitsSetoidComap` 的定义

English:
definition equivSubgroupOrbitsSetoidComap
  signature: (H : Subgroup G) (ω : Ω)
  body: fun q => q.liftOn' (fun x => ⟦⟨↑x, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx := x.property
    rwa [orbitRel.Quotient.mem_orbit] at hx⟩⟧) fun a b h => by
      simp only [← Quotient.eq, orbitRel.Quotient.subgroup_quotient_eq_iff] at h
      simp only [Quotient.eq] at h ⊢

中文:
定义 equivSubgroupOrbitsSetoidComap
  签名: (H : Subgroup G) (ω : Ω)
  定义体: fun q => q.liftOn' (fun x => ⟦⟨↑x, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx := x.property
    rwa [orbitRel.Quotient.mem_orbit] at hx⟩⟧) fun a b h => by
      simp only [← Quotient.eq, orbitRel.Quotient.subgroup_quotient_eq_iff] at h
      simp only [Quotient.eq] at h ⊢

Depends on / 依赖: Quotient, Quotient.eq, Quotient.mk, Set.mem_preimage, Set.mem_singleton_iff, Setoid, Setoid.c, _eq_mk, invFun, liftOn, mem_orbit, mem_preimage, mem_singleton_iff, orbitRel, orbitRel.Quotient.mem_orbit, orbitRel.Quotient.subgroup_quotient_eq_iff, property, q.liftOn, subgroup_quotient_eq_iff, x.property
-/
noncomputable def equivSubgroupOrbitsSetoidComap (H : Subgroup G) (ω : Ω) :
    orbitRel.Quotient H (orbitRel.Quotient.orbit ω) ≃
      Quotient ((orbitRel H X).comap (Subtype.val : Quotient.mk (orbitRel G X) ⁻¹' {ω} -> X)) where
  toFun := fun q => q.liftOn' (fun x => ⟦⟨↑x, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx := x.property
    rwa [orbitRel.Quotient.mem_orbit] at hx⟩⟧) fun a b h => by
      simp only [← Quotient.eq, orbitRel.Quotient.subgroup_quotient_eq_iff] at h
      simp only [Quotient.eq] at h ⊢
      exact h
  invFun := fun q => q.liftOn' (fun x => ⟦⟨↑x, by
    have hx := x.property
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rwa [orbitRel.Quotient.mem_orbit, @Quotient.mk''_eq_mk]⟩⟧) fun a b h => by
      rw [Setoid.comap_rel]; rw [← Quotient.eq'']; rw [@Quotient.mk''_eq_mk] at h
      simp only [orbitRel.Quotient.subgroup_quotient_eq_iff]
      exact h
  left_inv := by
    simp only [LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl
  right_inv := by
    simp only [Function.RightInverse, LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl

/-- A bijection between the orbits under the action of a subgroup `H` on `X`, and the orbits
under the action of `H` on each orbit under the action of `G`. -/
@[to_additive /-- A bijection between the orbits under the action of an additive subgroup `H` on
`X`, and the orbits under the action of `H` on each orbit under the action of `G`. -/]
/--
Definition of `equivSubgroupOrbits` / `equivSubgroupOrbits` 的定义

English:
definition equivSubgroupOrbits
  signature: (H : Subgroup G)
  body: (Setoid.sigmaQuotientEquivOfLe (orbitRel_subgroup_le H)).symm.trans
    (Equiv.sigmaCongrRight fun ω => (equivSubgroupOrbitsSetoidComap H ω).symm)

中文:
定义 equivSubgroupOrbits
  签名: (H : Subgroup G)
  定义体: (Setoid.sigmaQuotientEquivOfLe (orbitRel_subgroup_le H)).symm.trans
    (Equiv.sigmaCongrRight fun ω => (equivSubgroupOrbitsSetoidComap H ω).symm)

Depends on / 依赖: Equiv.sigmaCongrRight, Setoid, Setoid.sigmaQuotientEquivOfLe, equivSubgroupOrbitsSetoidComap, orbitRel_subgroup_le, sigmaCongrRight, sigmaQuotientEquivOfLe, symm.trans
-/
noncomputable def equivSubgroupOrbits (H : Subgroup G) :
    orbitRel.Quotient H X ≃ Σ ω : Ω, orbitRel.Quotient H (orbitRel.Quotient.orbit ω) :=
  (Setoid.sigmaQuotientEquivOfLe (orbitRel_subgroup_le H)).symm.trans
    (Equiv.sigmaCongrRight fun ω => (equivSubgroupOrbitsSetoidComap H ω).symm)

variable {X}

@[to_additive]
/--
Instance `finite_quotient_of_finite_quotient_of_finite_quotient` / 实例 `finite_quotient_of_finite_quotient_of_finite_quotient`

English:
instance finite_quotient_of_finite_quotient_of_finite_quotient
  signature: {H : Subgroup G}
  body: by
  rw [(equivSubgroupOrbits X H).finite_iff]
  infer_instance

中文:
实例 finite_quotient_of_finite_quotient_of_finite_quotient
  签名: {H : Subgroup G}
  定义体: by
  rw [(equivSubgroupOrbits X H).finite_iff]
  infer_instance

Depends on / 依赖: equivSubgroupOrbits, finite_iff, infer_instance
-/
instance finite_quotient_of_finite_quotient_of_finite_quotient {H : Subgroup G}
    [Finite (orbitRel.Quotient G X)] [Finite (G ⧸ H)] :
Finite orbitRel.Quotient H X := by
  rw [(equivSubgroupOrbits X H).finite_iff]
  infer_instance

/-- Given a group acting freely and transitively, an equivalence between the orbits under the
action of a subgroup and the quotient of the group by the subgroup. -/
@[to_additive /-- Given an additive group acting freely and transitively, an equivalence between the
orbits under the action of an additive subgroup and the quotient of the group by the subgroup. -/]
/--
Definition of `equivSubgroupOrbitsQuotientGroup` / `equivSubgroupOrbitsQuotientGroup` 的定义

English:
definition equivSubgroupOrbitsQuotientGroup
  signature: [IsPretransitive G X]
  body: fun q => q.liftOn' (fun y => (exists_smul_eq G y x).choose) (by
    intro y₁ y₂ h
    rw [orbitRel_apply] at h
    rw [Quotient.eq'']; rw [leftRel_eq]
    dsimp only
    rcases h with ⟨g, rfl⟩
    dsimp only
    suffices (exists_smul_eq G (g • y₂) x).choose = (exists_smul_eq G y₂ x).choose * g⁻¹ by


中文:
定义 equivSubgroupOrbitsQuotientGroup
  签名: [IsPretransitive G X]
  定义体: fun q => q.liftOn' (fun y => (exists_smul_eq G y x).choose) (by
    intro y₁ y₂ h
    rw [orbitRel_apply] at h
    rw [Quotient.eq'']; rw [leftRel_eq]
    dsimp only
    rcases h with ⟨g, rfl⟩
    dsimp only
    suffices (exists_smul_eq G (g • y₂) x).choose = (exists_smul_eq G y₂ x).choose * g⁻¹ by


Depends on / 依赖: IsCancelSMul, IsCancelSMul.right_cancel, Quotient, Quotient.eq, Subgroup, Subgroup.coe_inv, Subgroup.smul_def, choose_spec, coe_inv, exists_smul_eq, inv_mul_cancel_right, leftRel_eq, liftOn, orbitRel_apply, q.liftOn, right_cancel, smul_def, smul_smul
-/
noncomputable def equivSubgroupOrbitsQuotientGroup [IsPretransitive G X]
    [IsCancelSMul G X] (H : Subgroup G) :
    orbitRel.Quotient H X ≃ G ⧸ H where
  toFun := fun q => q.liftOn' (fun y => (exists_smul_eq G y x).choose) (by
    intro y₁ y₂ h
    rw [orbitRel_apply] at h
    rw [Quotient.eq'']; rw [leftRel_eq]
    dsimp only
    rcases h with ⟨g, rfl⟩
    dsimp only
    suffices (exists_smul_eq G (g • y₂) x).choose = (exists_smul_eq G y₂ x).choose * g⁻¹ by
      simp [this]
    refine IsCancelSMul.right_cancel _ _ (g • y₂) ?_
    rw [(exists_smul_eq G (g • y₂) x).choose_spec]; rw [Subgroup.smul_def]; rw [Subgroup.coe_inv]; rw [smul_smul]; rw [inv_mul_cancel_right]; rw [(exists_smul_eq G y₂ x).choose_spec])
  invFun := fun q => q.liftOn' (fun g => ⟦g⁻¹ • x⟧) (by
    intro g₁ g₂ h
    rw [leftRel_eq] at h
    rw [← @Quotient.mk''_eq_mk]; rw [Quotient.eq'']; rw [orbitRel_apply]
    exact ⟨⟨_, h⟩, by simp [mul_smul]⟩)
  left_inv := fun y => by
    cases y using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    rw [← @Quotient.mk''_eq_mk]; rw [Quotient.eq'']; rw [orbitRel_apply]
    convert! mem_orbit_self _
    rw [inv_smul_eq_iff]; rw [(exists_smul_eq G _ x).choose_spec]
  right_inv := fun g => by
    cases g using Quotient.inductionOn' with | _ g
    simp only [Quotient.liftOn'_mk'', QuotientGroup.mk]
    rw [Quotient.eq'']; rw [leftRel_eq]
    simp only
    convert! one_mem H
    rw [inv_mul_eq_one]; rw [eq_comm]; rw [← inv_mul_eq_one]; rw [← Subgroup.mem_bot]; rw [← IsCancelSMul.stabilizer_eq_bot (g⁻¹ • x)]; rw [mem_stabilizer_iff]; rw [mul_smul]; rw [(exists_smul_eq G (g⁻¹ • x) x).choose_spec]

/-- If `G` acts on `X` with trivial stabilizers, `X` is equivalent
to the product of the quotient of `X` by `G` and `G`.
See `MulAction.selfEquivOrbitsQuotientProd` with `φ = Quotient.out`. -/
@[to_additive selfEquivOrbitsQuotientProd' /-- If `G` acts freely on `X`, `X` is equivalent
to the product of the quotient of `X` by `G` and `G`.
See `AddAction.selfEquivOrbitsQuotientProd` with `φ = Quotient.out`. -/]
/--
Definition of `selfEquivOrbitsQuotientProd'` / `selfEquivOrbitsQuotientProd'` 的定义

English:
definition selfEquivOrbitsQuotientProd'
  body: (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' G X hφ).trans
    (Equiv.sigmaCongrRight <| fun _ =>
      (Subgroup.quotientEquivOfEq (h _)).trans (QuotientGroup.quotientEquivSelf G)).trans <|
    Equiv.sigmaEquivProd _ _

中文:
定义 selfEquivOrbitsQuotientProd'
  定义体: (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' G X hφ).trans
    (Equiv.sigmaCongrRight <| fun _ =>
      (Subgroup.quotientEquivOfEq (h _)).trans (QuotientGroup.quotientEquivSelf G)).trans <|
    Equiv.sigmaEquivProd _ _

Depends on / 依赖: Equiv.sigmaCongrRight, Equiv.sigmaEquivProd, MulAction, MulAction.selfEquivSigmaOrbitsQuotientStabilizer, QuotientGroup, QuotientGroup.quotientEquivSelf, Subgroup, Subgroup.quotientEquivOfEq, quotientEquivOfEq, quotientEquivSelf, selfEquivSigmaOrbitsQuotientStabilizer, sigmaCongrRight, sigmaEquivProd
-/
noncomputable def selfEquivOrbitsQuotientProd'
    {φ : Quotient (MulAction.orbitRel G X) -> X} (hφ : Function.LeftInverse Quotient.mk'' φ)
    (h : forall b : X, MulAction.stabilizer G b = ⊥) :
    X ≃ Quotient (MulAction.orbitRel G X) × G :=
(MulAction.selfEquivSigmaOrbitsQuotientStabilizer' G X hφ).trans
    (Equiv.sigmaCongrRight <| fun _ =>
      (Subgroup.quotientEquivOfEq (h _)).trans (QuotientGroup.quotientEquivSelf G)).trans <|
    Equiv.sigmaEquivProd _ _

/-- If `G` acts freely on `X`, `X` is equivalent to the product of the quotient of `X` by `G` and
`G`. -/
@[to_additive selfEquivOrbitsQuotientProd
  /-- If `G` acts freely on `X`, `X` is equivalent to the product of the quotient of `X` by
`G` and `G`. -/]
/--
Definition of `selfEquivOrbitsQuotientProd` / `selfEquivOrbitsQuotientProd` 的定义

English:
definition selfEquivOrbitsQuotientProd
  signature: (h : forall b : X, MulAction.stabilizer G b = ⊥)
  body: MulAction.selfEquivOrbitsQuotientProd' Quotient.out_eq' h

中文:
定义 selfEquivOrbitsQuotientProd
  签名: (h : 对任意 b : X, MulAction.stabilizer G b = ⊥)
  定义体: MulAction.selfEquivOrbitsQuotientProd' Quotient.out_eq' h

Depends on / 依赖: MulAction, MulAction.selfEquivOrbitsQuotientProd, Quotient, Quotient.out_eq, out_eq, selfEquivOrbitsQuotientProd
-/
noncomputable def selfEquivOrbitsQuotientProd (h : forall b : X, MulAction.stabilizer G b = ⊥) :
    X ≃ Quotient (MulAction.orbitRel G X) × G :=
  MulAction.selfEquivOrbitsQuotientProd' Quotient.out_eq' h

end MulAction

/--
theorem `ConjClasses.card_carrier` / 定理 `ConjClasses.card_carrier`

English:
theorem ConjClasses.card_carrier
  statement: {G : Type*} [Group G] [Fintype G] (g : G)
  proof: by
  classical
  rw [Fintype.card_congr <| ConjAct.toConjAct (G := G) |>.toEquiv]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g]; rw [Nat.mul_div_cancel]
  · simp_rw [ConjAct.orbit_eq_carrier_conjClasses]
  · exact Fintype.card_pos_iff.mpr inferInstance

中文:
定理 ConjClasses.card_carrier
  结论: {G : 类型} [Group G] [Fintype G] (g : G)
  证明: by
  classical
  rw [Fintype.card_congr <| ConjAct.toConjAct (G := G) |>.toEquiv]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g]; rw [Nat.mul_div_cancel]
  · simp_rw [ConjAct.orbit_eq_carrier_conjClasses]
  · exact Fintype.card_pos_iff.mpr inferInstance

Depends on / 依赖: ConjAct, ConjAct.orbit_eq_carrier_conjClasses, ConjAct.toConjAct, Fintype, Fintype.card_congr, Fintype.card_pos_iff.mpr, MulAction, MulAction.card_orbit_mul_card_stabilizer_eq_card_group, Nat.mul_div_cancel, card_congr, card_orbit_mul_card_stabilizer_eq_card_group, card_pos_iff, classical, mul_div_cancel, orbit_eq_carrier_conjClasses, simp_rw, toConjAct, toEquiv
-/
theorem ConjClasses.card_carrier {G : Type*} [Group G] [Fintype G] (g : G)
    [Fintype (ConjClasses.mk g).carrier] [Fintype <| MulAction.stabilizer (ConjAct G) g] :
    Fintype.card (ConjClasses.mk g).carrier =
      Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
  classical
  rw [Fintype.card_congr <| ConjAct.toConjAct (G := G) |>.toEquiv]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g]; rw [Nat.mul_div_cancel]
  · simp_rw [ConjAct.orbit_eq_carrier_conjClasses]
  · exact Fintype.card_pos_iff.mpr inferInstance

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

/--
theorem `normalCore_eq_ker` / 定理 `normalCore_eq_ker`

English:
theorem normalCore_eq_ker
  statement: H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker
  proof: by
  apply le_antisymm
  · intro g hg
    apply Equiv.Perm.ext
    refine fun q => QuotientGroup.induction_on q ?_
    refine fun g' => (MulAction.Quotient.smul_mk H g g').trans (QuotientGroup.eq.mpr ?_)
    rw [smul_eq_mul]; rw [mul_inv_rev]; rw [← inv_inv g']; rw [inv_inv]
    exact H.normalCore.i

中文:
定理 normalCore_eq_ker
  结论: H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker
  证明: by
  apply le_antisymm
  · intro g hg
    apply Equiv.Perm.ext
    refine fun q => QuotientGroup.induction_on q ?_
    refine fun g' => (MulAction.Quotient.smul_mk H g g').trans (QuotientGroup.eq.mpr ?_)
    rw [smul_eq_mul]; rw [mul_inv_rev]; rw [← inv_inv g']; rw [inv_inv]
    exact H.normalCore.i

Depends on / 依赖: Equiv.Perm.e, Equiv.Perm.ext, H.inv_mem_iff, H.normalCore.inv_mem, MulAction, MulAction.Quotient.smul_mk, Quotient, QuotientGroup, QuotientGroup.eq, QuotientGroup.eq.mpr, QuotientGroup.induction_on, Subgroup, Subgroup.normal_le_normalCore.mpr, induction_on, inv_inv, inv_mem, inv_mem_iff, le_antisymm, mul_inv_rev, mul_one
-/
theorem normalCore_eq_ker : H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker := by
  apply le_antisymm
  · intro g hg
    apply Equiv.Perm.ext
    refine fun q => QuotientGroup.induction_on q ?_
    refine fun g' => (MulAction.Quotient.smul_mk H g g').trans (QuotientGroup.eq.mpr ?_)
    rw [smul_eq_mul]; rw [mul_inv_rev]; rw [← inv_inv g']; rw [inv_inv]
    exact H.normalCore.inv_mem hg g'⁻¹
  · refine (Subgroup.normal_le_normalCore.mpr fun g hg => ?_)
    rw [← H.inv_mem_iff]; rw [← mul_one g⁻¹]; rw [← QuotientGroup.eq]; rw [← mul_one g]
    exact (MulAction.Quotient.smul_mk H g 1).symm.trans (Equiv.Perm.ext_iff.mp hg (1 : G))

open QuotientGroup

/--
Definition of `quotientCentralizerEmbedding` / `quotientCentralizerEmbedding` 的定义

English:
definition quotientCentralizerEmbedding
  signature: (g : G)
  body: ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
            (quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g))).symm.toEmbedding.trans
    ⟨fun x =>
      ⟨x * g⁻¹,
        let ⟨_, x, rfl⟩ := x
        ⟨x, g, rfl⟩⟩,
      fun _ _ => Subtype.ext ∘ mul_right_cancel ∘ Subtype.ext_i

中文:
定义 quotientCentralizerEmbedding
  签名: (g : G)
  定义体: ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
            (quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g))).symm.toEmbedding.trans
    ⟨fun x =>
      ⟨x * g⁻¹,
        let ⟨_, x, rfl⟩ := x
        ⟨x, g, rfl⟩⟩,
      fun _ _ => Subtype.ext ∘ mul_right_cancel ∘ Subtype.ext_i

Depends on / 依赖: ConjAct, ConjAct.stabilizer_eq_centralizer, MulAction, MulAction.orbitEquivQuotientStabilizer, Subtype, Subtype.ext, Subtype.ext_iff.mp, ext_iff, mul_right_cancel, orbitEquivQuotientStabilizer, quotientEquivOfEq, stabilizer_eq_centralizer, symm.toEmbedding.trans, toEmbedding
-/
noncomputable def quotientCentralizerEmbedding (g : G) :
    G ⧸ centralizer {g} ↪ commutatorSet G :=
  ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
            (quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g))).symm.toEmbedding.trans
    ⟨fun x =>
      ⟨x * g⁻¹,
        let ⟨_, x, rfl⟩ := x
        ⟨x, g, rfl⟩⟩,
      fun _ _ => Subtype.ext ∘ mul_right_cancel ∘ Subtype.ext_iff.mp⟩

/--
theorem `quotientCentralizerEmbedding_apply` / 定理 `quotientCentralizerEmbedding_apply`

English:
theorem quotientCentralizerEmbedding_apply
  given: (g : G) (x : G)
  proof: rfl

中文:
定理 quotientCentralizerEmbedding_apply
  条件: (g : G) (x : G)
  证明: rfl
-/
theorem quotientCentralizerEmbedding_apply (g : G) (x : G) :
    quotientCentralizerEmbedding g x = ⟨⁅x, g⁆, x, g, rfl⟩ :=
  rfl

/--
Definition of `quotientCenterEmbedding` / `quotientCenterEmbedding` 的定义

English:
definition quotientCenterEmbedding
  signature: {S : Set G} (hS : closure S = ⊤)
  body: (quotientEquivOfEq (center_eq_infi' hS)).toEmbedding.trans
    ((quotientiInfEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding (g : G)))

中文:
定义 quotientCenterEmbedding
  签名: {S : Set G} (hS : closure S = ⊤)
  定义体: (quotientEquivOfEq (center_eq_infi' hS)).toEmbedding.trans
    ((quotientiInfEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding (g : G)))

Depends on / 依赖: Embedding, Function, Function.Embedding.piCongrRight, center_eq_infi, piCongrRight, quotientCentralizerEmbedding, quotientEquivOfEq, quotientiInfEmbedding, toEmbedding, toEmbedding.trans
-/
noncomputable def quotientCenterEmbedding {S : Set G} (hS : closure S = ⊤) :
    G ⧸ center G ↪ S -> commutatorSet G :=
  (quotientEquivOfEq (center_eq_infi' hS)).toEmbedding.trans
    ((quotientiInfEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding (g : G)))

/--
theorem `quotientCenterEmbedding_apply` / 定理 `quotientCenterEmbedding_apply`

English:
theorem quotientCenterEmbedding_apply
  given: {S : Set G} (hS : closure S = ⊤) (g : G) (s : S)
  proof: rfl

中文:
定理 quotientCenterEmbedding_apply
  条件: {S : Set G} (hS : closure S = ⊤) (g : G) (s : S)
  证明: rfl
-/
theorem quotientCenterEmbedding_apply {S : Set G} (hS : closure S = ⊤) (g : G) (s : S) :
    quotientCenterEmbedding hS g s = ⟨⁅g, s⁆, g, s, rfl⟩ :=
  rfl

end Subgroup
