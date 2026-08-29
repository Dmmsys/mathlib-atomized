/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.WithOne.Defs

/-!
# More operations on `WithOne` and `WithZero`

This file defines various bundled morphisms on `WithOne` and `WithZero`
that were not available in `Algebra/Group/WithOne/Defs`.

## Main definitions

* `WithOne.lift`, `WithZero.lift`
* `WithOne.map`, `WithZero.map`
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
Instance `instInvolutiveInv` / 实例 `instInvolutiveInv`

English:
instance instInvolutiveInv
  signature: [InvolutiveInv α]
  body: (Option.map_map _ _ _).trans by simp_rw [inv_comp_inv, Option.map_id, id]

中文:
实例 instInvolutiveInv
  签名: [InvolutiveInv α]
  定义体: (Option.map_map _ _ _).trans by simp_rw [inv_comp_inv, Option.map_id, id]

Depends on / 依赖: Option.map_id, Option.map_map, inv_comp_inv, map_id, map_map, simp_rw
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) where
inv_inv a := (Option.map_map _ _ _).trans by simp_rw [inv_comp_inv, Option.map_id, id]

section

/-- `WithOne.coe` as a bundled morphism -/
@[to_additive (attr := simps apply) /-- `WithZero.coe` as a bundled morphism -/]
/--
Definition of `coeMulHom` / `coeMulHom` 的定义

English:
definition coeMulHom
  signature: [Mul α]
  body: coe
  map_mul' _ _ := rfl

中文:
定义 coeMulHom
  签名: [乘法 α]
  定义体: coe
  map_mul' _ _ := rfl
-/
def coeMulHom [Mul α] : α ->ₙ* WithOne α where
  toFun := coe
  map_mul' _ _ := rfl

end

section lift

variable [Mul α] [MulOneClass β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homomorphism. -/
@[to_additive /--
Lift an additive semigroup homomorphism `f` to a bundled additive monoid homomorphism. -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (α ->ₙ* β) ≃ (WithOne α ->* β) where
  body: { toFun := WithOne.recOneCoe 1 f, map_one' := rfl,
      map_mul' := fun x y => x.cases_on (by simp) (fun x => y.cases_on (by simp) (f.map_mul x)) }
  invFun F := F.toMulHom.comp coeMulHom
  right_inv F := MonoidHom.ext fun x => WithOne.cases_on x F.map_one.symm (fun _ => rfl)

中文:
定义 lift
  签名: : (α ->ₙ* β) ≃ (WithOne α ->* β) where
  定义体: { toFun := WithOne.recOneCoe 1 f, map_one' := rfl,
      map_mul' := fun x y => x.cases_on (by simp) (fun x => y.cases_on (by simp) (f.map_mul x)) }
  invFun F := F.toMulHom.comp coeMulHom
  right_inv F := MonoidHom.ext fun x => WithOne.cases_on x F.map_one.symm (fun _ => rfl)

Depends on / 依赖: F.map_one.symm, F.toMulHom.comp, MonoidHom, MonoidHom.ext, WithOne, WithOne.cases_on, WithOne.recOneCoe, cases_on, coeMulHom, f.map_mul, invFun, map_mul, map_one, recOneCoe, right_inv, toMulHom, x.cases_on, y.cases_on
-/
def lift : (α ->ₙ* β) ≃ (WithOne α ->* β) where
  toFun f :=
    { toFun := WithOne.recOneCoe 1 f, map_one' := rfl,
      map_mul' := fun x y => x.cases_on (by simp) (fun x => y.cases_on (by simp) (f.map_mul x)) }
  invFun F := F.toMulHom.comp coeMulHom
  right_inv F := MonoidHom.ext fun x => WithOne.cases_on x F.map_one.symm (fun _ => rfl)

variable (f : α ->ₙ* β)

@[to_additive (attr := simp)]
/--
theorem `lift_coe` / 定理 `lift_coe`

English:
theorem lift_coe
  given: (x : α)
  statement: lift f x = f x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 lift_coe
  条件: (x : α)
  结论: lift f x = f x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem lift_coe (x : α) : lift f x = f x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `lift_one` / 定理 `lift_one`

English:
theorem lift_one
  statement: lift f 1 = 1
  proof: rfl

@[to_additive]

中文:
定理 lift_one
  结论: lift f 1 = 1
  证明: rfl

@[to_additive]
-/
theorem lift_one : lift f 1 = 1 :=
  rfl

@[to_additive]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (f : WithOne α ->* β)
  statement: f = lift (f.toMulHom.comp coeMulHom)
  proof: (lift.apply_symm_apply f).symm

@[to_additive (attr := simp)]

中文:
定理 lift_unique
  条件: (f : WithOne α ->* β)
  结论: f = lift (f.toMulHom.comp coeMulHom)
  证明: (lift.apply_symm_apply f).symm

@[to_additive (attr := simp)]

Depends on / 依赖: apply_symm_apply, lift.apply_symm_apply
-/
theorem lift_unique (f : WithOne α ->* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm

@[to_additive (attr := simp)]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (f : WithOne α ->* β) (x : α)
  statement: lift.symm f x = f x
  proof: rfl

@[to_additive]

中文:
定理 lift_symm_apply
  条件: (f : WithOne α ->* β) (x : α)
  结论: lift.symm f x = f x
  证明: rfl

@[to_additive]
-/
theorem lift_symm_apply (f : WithOne α ->* β) (x : α) : lift.symm f x = f x := rfl

@[to_additive]
/--
lemma `lift_symm_injective_of_injective` / 引理 `lift_symm_injective_of_injective`

English:
lemma lift_symm_injective_of_injective
  given: {f : WithOne α ->* β} (hf : Function.Injective f)
  proof: fun _ _ => by simp [hf.eq_iff]

中文:
引理 lift_symm_injective_of_injective
  条件: {f : WithOne α ->* β} (hf : 函数.单射 f)
  证明: fun _ _ => by simp [hf.eq_iff]

Depends on / 依赖: eq_iff, hf.eq_iff
-/
lemma lift_symm_injective_of_injective {f : WithOne α ->* β} (hf : Function.Injective f) :
    Function.Injective (lift.symm f) :=
  fun _ _ => by simp [hf.eq_iff]

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `WithOne α` to `WithOne β` -/
@[to_additive /-- Given an additive map from `α → β` returns an additive monoid homomorphism from
`WithZero α` to `WithZero β` -/]
/--
Definition of `mapMulHom` / `mapMulHom` 的定义

English:
definition mapMulHom
  signature: (f : α ->ₙ* β)
  body: lift (coeMulHom.comp f)

@[to_additive (attr := simp)]

中文:
定义 mapMulHom
  签名: (f : α ->ₙ* β)
  定义体: lift (coeMulHom.comp f)

@[to_additive (attr := simp)]

Depends on / 依赖: coeMulHom, coeMulHom.comp
-/
def mapMulHom (f : α ->ₙ* β) : WithOne α ->* WithOne β :=
  lift (coeMulHom.comp f)

@[to_additive (attr := simp)]
/--
theorem `mapMulHom_coe` / 定理 `mapMulHom_coe`

English:
theorem mapMulHom_coe
  given: (f : α ->ₙ* β) (a : α)
  statement: mapMulHom f (a : WithOne α) = f a
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mapMulHom_coe
  条件: (f : α ->ₙ* β) (a : α)
  结论: mapMulHom f (a : WithOne α) = f a
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mapMulHom_coe (f : α ->ₙ* β) (a : α) : mapMulHom f (a : WithOne α) = f a :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mapMulHom_id` / 定理 `mapMulHom_id`

English:
theorem mapMulHom_id
  statement: mapMulHom (MulHom.id α) = MonoidHom.id (WithOne α)
  proof: by
  ext x
  induction x <;> rfl

@[to_additive]

中文:
定理 mapMulHom_id
  结论: mapMulHom (乘法半群态射.id α) = 幺半群态射.id (WithOne α)
  证明: by
  ext x
  induction x <;> rfl

@[to_additive]
-/
theorem mapMulHom_id : mapMulHom (MulHom.id α) = MonoidHom.id (WithOne α) := by
  ext x
  induction x <;> rfl

@[to_additive]
/--
theorem `mapMulHom_injective` / 定理 `mapMulHom_injective`

English:
theorem mapMulHom_injective
  given: {f : α ->ₙ* β} (hf : Function.Injective f)

中文:
定理 mapMulHom_injective
  条件: {f : α ->ₙ* β} (hf : 函数.单射 f)
-/
theorem mapMulHom_injective {f : α ->ₙ* β} (hf : Function.Injective f) :
    Function.Injective (mapMulHom f)
  | none, none, _ => rfl
  | (a₁ : α), (a₂ : α), H => by simpa [hf.eq_iff] using H

@[to_additive]
/--
theorem `mapMulHom_injective'` / 定理 `mapMulHom_injective'`

English:
theorem mapMulHom_injective'
  proof: fun f g h => MulHom.ext fun x => coe_injective by simp only [← mapMulHom_coe, h]

@[to_additive (attr := simp)]

中文:
定理 mapMulHom_injective'
  证明: fun f g h => MulHom.ext fun x => coe_injective by simp only [← mapMulHom_coe, h]

@[to_additive (attr := simp)]
-/
theorem mapMulHom_injective' :
    Function.Injective (WithOne.mapMulHom (α := α) (β := β)) :=
fun f g h => MulHom.ext fun x => coe_injective by simp only [← mapMulHom_coe, h]

@[to_additive (attr := simp)]
/--
theorem `mapMulHom_inj` / 定理 `mapMulHom_inj`

English:
theorem mapMulHom_inj
  given: {f g : α ->ₙ* β}
  statement: mapMulHom f = mapMulHom g ↔ f = g
  proof: mapMulHom_injective'.eq_iff

@[to_additive]

中文:
定理 mapMulHom_inj
  条件: {f g : α ->ₙ* β}
  结论: mapMulHom f = mapMulHom g ↔ f = g
  证明: mapMulHom_injective'.eq_iff

@[to_additive]

Depends on / 依赖: eq_iff, mapMulHom_injective
-/
theorem mapMulHom_inj {f g : α ->ₙ* β} : mapMulHom f = mapMulHom g ↔ f = g :=
  mapMulHom_injective'.eq_iff

@[to_additive]
/--
theorem `mapMulHom_mapMulHom` / 定理 `mapMulHom_mapMulHom`

English:
theorem mapMulHom_mapMulHom
  given: (f : α ->ₙ* β) (g : β ->ₙ* γ) (x)
  proof: by
  induction x <;> rfl

@[to_additive (attr := simp)]

中文:
定理 mapMulHom_mapMulHom
  条件: (f : α ->ₙ* β) (g : β ->ₙ* γ) (x)
  证明: by
  induction x <;> rfl

@[to_additive (attr := simp)]
-/
theorem mapMulHom_mapMulHom (f : α ->ₙ* β) (g : β ->ₙ* γ) (x) :
    mapMulHom g (mapMulHom f x) = mapMulHom (g.comp f) x := by
  induction x <;> rfl

@[to_additive (attr := simp)]
/--
theorem `mapMulHom_comp` / 定理 `mapMulHom_comp`

English:
theorem mapMulHom_comp
  given: (f : α ->ₙ* β) (g : β ->ₙ* γ)
  proof: MonoidHom.ext fun x => (mapMulHom_mapMulHom f g x).symm

中文:
定理 mapMulHom_comp
  条件: (f : α ->ₙ* β) (g : β ->ₙ* γ)
  证明: MonoidHom.ext fun x => (mapMulHom_mapMulHom f g x).symm

Depends on / 依赖: MonoidHom, MonoidHom.ext, mapMulHom_mapMulHom
-/
theorem mapMulHom_comp (f : α ->ₙ* β) (g : β ->ₙ* γ) :
    mapMulHom (g.comp f) = (mapMulHom g).comp (mapMulHom f) :=
  MonoidHom.ext fun x => (mapMulHom_mapMulHom f g x).symm

/-- A version of `Equiv.optionCongr` for `WithOne`. -/
@[to_additive (attr := simps apply) /-- A version of `Equiv.optionCongr` for `WithZero`. -/]
/--
Definition of `_root_.MulEquiv.withOneCongr` / `_root_.MulEquiv.withOneCongr` 的定义

English:
definition _root_.MulEquiv.withOneCongr
  signature: (e : α ≃* β)
  body: { mapMulHom e.toMulHom with
    toFun := mapMulHom e.toMulHom, invFun := mapMulHom e.symm.toMulHom,
    left_inv := (by induction · <;> simp)
    right_inv := (by induction · <;> simp) }

@[to_additive (attr := simp)]

中文:
定义 _root_.乘法等价.withOneCongr
  签名: (e : α ≃* β)
  定义体: { mapMulHom e.toMulHom with
    toFun := mapMulHom e.toMulHom, invFun := mapMulHom e.symm.toMulHom,
    left_inv := (by induction · <;> simp)
    right_inv := (by induction · <;> simp) }

@[to_additive (attr := simp)]

Depends on / 依赖: e.symm.toMulHom, e.toMulHom, invFun, left_inv, mapMulHom, right_inv, toMulHom
-/
def _root_.MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { mapMulHom e.toMulHom with
    toFun := mapMulHom e.toMulHom, invFun := mapMulHom e.symm.toMulHom,
    left_inv := (by induction · <;> simp)
    right_inv := (by induction · <;> simp) }

@[to_additive (attr := simp)]
/--
theorem `_root_.MulEquiv.withOneCongr_refl` / 定理 `_root_.MulEquiv.withOneCongr_refl`

English:
theorem _root_.MulEquiv.withOneCongr_refl
  statement: (MulEquiv.refl α).withOneCongr = MulEquiv.refl _
  proof: MulEquiv.toMonoidHom_injective mapMulHom_id

@[to_additive (attr := simp)]

中文:
定理 _root_.乘法等价.withOneCongr_refl
  结论: (乘法等价.refl α).withOneCongr = 乘法等价.refl _
  证明: MulEquiv.toMonoidHom_injective mapMulHom_id

@[to_additive (attr := simp)]

Depends on / 依赖: MulEquiv, MulEquiv.toMonoidHom_injective, mapMulHom_id, toMonoidHom_injective
-/
theorem _root_.MulEquiv.withOneCongr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective mapMulHom_id

@[to_additive (attr := simp)]
/--
theorem `_root_.MulEquiv.withOneCongr_symm` / 定理 `_root_.MulEquiv.withOneCongr_symm`

English:
theorem _root_.MulEquiv.withOneCongr_symm
  given: (e : α ≃* β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 _root_.乘法等价.withOneCongr_symm
  条件: (e : α ≃* β)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem _root_.MulEquiv.withOneCongr_symm (e : α ≃* β) :
    e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `_root_.MulEquiv.withOneCongr_trans` / 定理 `_root_.MulEquiv.withOneCongr_trans`

English:
theorem _root_.MulEquiv.withOneCongr_trans
  given: (e₁ : α ≃* β) (e₂ : β ≃* γ)
  proof: MulEquiv.toMonoidHom_injective (mapMulHom_comp _ _).symm

中文:
定理 _root_.乘法等价.withOneCongr_trans
  条件: (e₁ : α ≃* β) (e₂ : β ≃* γ)
  证明: MulEquiv.toMonoidHom_injective (mapMulHom_comp _ _).symm

Depends on / 依赖: MulEquiv, MulEquiv.toMonoidHom_injective, mapMulHom_comp, toMonoidHom_injective
-/
theorem _root_.MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.toMonoidHom_injective (mapMulHom_comp _ _).symm

end Map

end WithOne
