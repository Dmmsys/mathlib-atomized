/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`Group`, `AddGroup`, etc)
on the type of locally constant functions.

-/

@[expose] public section

namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: Y] : One (LocallyConstant X Y) where one
  body: const X 1

@[to_additive (attr := simp)]

中文:
实例 [One
  签名: Y] : One (LocallyConstant X Y) where one
  定义体: const X 1

@[to_additive (attr := simp)]
-/
instance [One Y] : One (LocallyConstant X Y) where one := const X 1

@[to_additive (attr := simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  given: [One Y]
  statement: ⇑(1 : LocallyConstant X Y) = (1 : X -> Y)
  proof: rfl

@[to_additive]

中文:
定理 coe_one
  条件: [One Y]
  结论: ⇑(1 : LocallyConstant X Y) = (1 : X -> Y)
  证明: rfl

@[to_additive]
-/
theorem coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X -> Y) :=
  rfl

@[to_additive]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: [One Y] (x : X)
  statement: (1 : LocallyConstant X Y) x = 1
  proof: rfl

@[to_additive]

中文:
定理 one_apply
  条件: [One Y] (x : X)
  结论: (1 : LocallyConstant X Y) x = 1
  证明: rfl

@[to_additive]
-/
theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: Y] : Inv (LocallyConstant X Y) where inv f
  body: ⟨f⁻¹, f.isLocallyConstant.inv⟩

@[to_additive (attr := simp)]

中文:
实例 [Inv
  签名: Y] : Inv (LocallyConstant X Y) where inv f
  定义体: ⟨f⁻¹, f.isLocallyConstant.inv⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.isLocallyConstant.inv, isLocallyConstant
-/
instance [Inv Y] : Inv (LocallyConstant X Y) where inv f := ⟨f⁻¹, f.isLocallyConstant.inv⟩

@[to_additive (attr := simp)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: [Inv Y] (f : LocallyConstant X Y)
  statement: ⇑(f⁻¹ : LocallyConstant X Y) = (f : X -> Y)⁻¹
  proof: rfl

@[to_additive]

中文:
定理 coe_inv
  条件: [Inv Y] (f : LocallyConstant X Y)
  结论: ⇑(f⁻¹ : LocallyConstant X Y) = (f : X -> Y)⁻¹
  证明: rfl

@[to_additive]
-/
theorem coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑(f⁻¹ : LocallyConstant X Y) = (f : X -> Y)⁻¹ :=
  rfl

@[to_additive]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: [Inv Y] (f : LocallyConstant X Y) (x : X)
  statement: f⁻¹ x = (f x)⁻¹
  proof: rfl

@[to_additive]

中文:
定理 inv_apply
  条件: [Inv Y] (f : LocallyConstant X Y) (x : X)
  结论: f⁻¹ x = (f x)⁻¹
  证明: rfl

@[to_additive]
-/
theorem inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: Y] : Mul (LocallyConstant X Y) where
  body: ⟨f * g, f.isLocallyConstant.mul g.isLocallyConstant⟩

@[to_additive (attr := simp)]

中文:
实例 [Mul
  签名: Y] : Mul (LocallyConstant X Y) where
  定义体: ⟨f * g, f.isLocallyConstant.mul g.isLocallyConstant⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.isLocallyConstant.mul, g.isLocallyConstant, isLocallyConstant
-/
instance [Mul Y] : Mul (LocallyConstant X Y) where
  mul f g := ⟨f * g, f.isLocallyConstant.mul g.isLocallyConstant⟩

@[to_additive (attr := simp)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [Mul Y] (f g : LocallyConstant X Y)
  statement: ⇑(f * g) = f * g
  proof: rfl

@[to_additive]

中文:
定理 coe_mul
  条件: [Mul Y] (f g : LocallyConstant X Y)
  结论: ⇑(f * g) = f * g
  证明: rfl

@[to_additive]
-/
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g :=
  rfl

@[to_additive]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [Mul Y] (f g : LocallyConstant X Y) (x : X)
  statement: (f * g) x = f x * g x
  proof: rfl

@[to_additive]

中文:
定理 mul_apply
  条件: [Mul Y] (f g : LocallyConstant X Y) (x : X)
  结论: (f * g) x = f x * g x
  证明: rfl

@[to_additive]
-/
theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: Y] : MulOneClass (LocallyConstant X Y)
  body: Function.Injective.mulOneClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

中文:
实例 [MulOneClass
  签名: Y] : MulOneClass (LocallyConstant X Y)
  定义体: Function.Injective.mulOneClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.mulOneClass, Injective, coe_injective, mulOneClass
-/
instance [MulOneClass Y] : MulOneClass (LocallyConstant X Y) :=
  Function.Injective.mulOneClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

/-- `DFunLike.coe` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `DFunLike.coe` as an `AddMonoidHom`. -/]
/--
Definition of `coeFnMonoidHom` / `coeFnMonoidHom` 的定义

English:
definition coeFnMonoidHom
  signature: [MulOneClass Y]
  body: DFunLike.coe
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 coeFnMonoidHom
  签名: [MulOneClass Y]
  定义体: DFunLike.coe
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: DFunLike, DFunLike.coe
-/
def coeFnMonoidHom [MulOneClass Y] : LocallyConstant X Y ->* X -> Y where
  toFun := DFunLike.coe
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive (attr := simps) /-- The constant-function embedding, as an additive monoid hom. -/]
/--
Definition of `constMonoidHom` / `constMonoidHom` 的定义

English:
definition constMonoidHom
  signature: [MulOneClass Y]
  body: const X
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 constMonoidHom
  签名: [MulOneClass Y]
  定义体: const X
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def constMonoidHom [MulOneClass Y] : Y ->* LocallyConstant X Y where
  toFun := const X
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: Y] : MulZeroClass (LocallyConstant X Y)
  body: Function.Injective.mulZeroClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

中文:
实例 [MulZeroClass
  签名: Y] : MulZeroClass (LocallyConstant X Y)
  定义体: Function.Injective.mulZeroClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.mulZeroClass, Injective, coe_injective, mulZeroClass
-/
instance [MulZeroClass Y] : MulZeroClass (LocallyConstant X Y) :=
  Function.Injective.mulZeroClass DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: Y] : MulZeroOneClass (LocallyConstant X Y)
  body: Function.Injective.mulZeroOneClass DFunLike.coe DFunLike.coe_injective rfl rfl fun _ _ => rfl

中文:
实例 [MulZeroOneClass
  签名: Y] : MulZeroOneClass (LocallyConstant X Y)
  定义体: Function.Injective.mulZeroOneClass DFunLike.coe DFunLike.coe_injective rfl rfl fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.mulZeroOneClass, Injective, coe_injective, mulZeroOneClass
-/
instance [MulZeroOneClass Y] : MulZeroOneClass (LocallyConstant X Y) :=
  Function.Injective.mulZeroOneClass DFunLike.coe DFunLike.coe_injective rfl rfl fun _ _ => rfl

section CharFn

variable (Y) [MulZeroOneClass Y] {U V : Set X}

/--
Definition of `charFn` / `charFn` 的定义

English:
definition charFn
  signature: (hU : IsClopen U)
  body: indicator 1 hU

中文:
定义 charFn
  签名: (hU : IsClopen U)
  定义体: indicator 1 hU

Depends on / 依赖: indicator
-/
noncomputable def charFn (hU : IsClopen U) : LocallyConstant X Y :=
  indicator 1 hU

/--
theorem `coe_charFn` / 定理 `coe_charFn`

English:
theorem coe_charFn
  given: (hU : IsClopen U)
  statement: (charFn Y hU : X -> Y) = Set.indicator U 1
  proof: rfl

中文:
定理 coe_charFn
  条件: (hU : IsClopen U)
  结论: (charFn Y hU : X -> Y) = Set.indicator U 1
  证明: rfl
-/
theorem coe_charFn (hU : IsClopen U) : (charFn Y hU : X -> Y) = Set.indicator U 1 :=
  rfl

/--
theorem `charFn_eq_one` / 定理 `charFn_eq_one`

English:
theorem charFn_eq_one
  given: [Nontrivial Y] (x : X) (hU : IsClopen U)
  statement: charFn Y hU x = (1 : Y) ↔ x in U
  proof: Set.indicator_eq_one_iff_mem _

中文:
定理 charFn_eq_one
  条件: [Nontrivial Y] (x : X) (hU : IsClopen U)
  结论: charFn Y hU x = (1 : Y) ↔ x in U
  证明: Set.indicator_eq_one_iff_mem _

Depends on / 依赖: Set.indicator_eq_one_iff_mem, indicator_eq_one_iff_mem
-/
theorem charFn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (1 : Y) ↔ x in U :=
  Set.indicator_eq_one_iff_mem _

/--
theorem `charFn_eq_zero` / 定理 `charFn_eq_zero`

English:
theorem charFn_eq_zero
  given: [Nontrivial Y] (x : X) (hU : IsClopen U)
  statement: charFn Y hU x = (0 : Y) ↔ x ∉ U
  proof: Set.indicator_eq_zero_iff_notMem _

中文:
定理 charFn_eq_zero
  条件: [Nontrivial Y] (x : X) (hU : IsClopen U)
  结论: charFn Y hU x = (0 : Y) ↔ x ∉ U
  证明: Set.indicator_eq_zero_iff_notMem _

Depends on / 依赖: Set.indicator_eq_zero_iff_notMem, indicator_eq_zero_iff_notMem
-/
theorem charFn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (0 : Y) ↔ x ∉ U :=
  Set.indicator_eq_zero_iff_notMem _

/--
theorem `charFn_inj` / 定理 `charFn_inj`

English:
theorem charFn_inj
  statement: [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
  proof: Set.indicator_one_inj Y coe_inj.mpr h

中文:
定理 charFn_inj
  结论: [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
  证明: Set.indicator_one_inj Y coe_inj.mpr h

Depends on / 依赖: Set.indicator_one_inj, coe_inj, coe_inj.mpr, indicator_one_inj
-/
theorem charFn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
    (h : charFn Y hU = charFn Y hV) : U = V :=
Set.indicator_one_inj Y coe_inj.mpr h

end CharFn

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: Y] : Div (LocallyConstant X Y) where
  body: ⟨f / g, f.isLocallyConstant.div g.isLocallyConstant⟩

@[to_additive]

中文:
实例 [Div
  签名: Y] : Div (LocallyConstant X Y) where
  定义体: ⟨f / g, f.isLocallyConstant.div g.isLocallyConstant⟩

@[to_additive]

Depends on / 依赖: f.isLocallyConstant.div, g.isLocallyConstant, isLocallyConstant
-/
instance [Div Y] : Div (LocallyConstant X Y) where
  div f g := ⟨f / g, f.isLocallyConstant.div g.isLocallyConstant⟩

@[to_additive]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: [Div Y] (f g : LocallyConstant X Y)
  statement: ⇑(f / g) = f / g
  proof: rfl

@[to_additive]

中文:
定理 coe_div
  条件: [Div Y] (f g : LocallyConstant X Y)
  结论: ⇑(f / g) = f / g
  证明: rfl

@[to_additive]
-/
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl

@[to_additive]
/--
theorem `div_apply` / 定理 `div_apply`

English:
theorem div_apply
  given: [Div Y] (f g : LocallyConstant X Y) (x : X)
  statement: (f / g) x = f x / g x
  proof: rfl

@[to_additive]

中文:
定理 div_apply
  条件: [Div Y] (f g : LocallyConstant X Y) (x : X)
  结论: (f / g) x = f x / g x
  证明: rfl

@[to_additive]
-/
theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: Y] : Semigroup (LocallyConstant X Y)
  body: Function.Injective.semigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl

中文:
实例 [Semigroup
  签名: Y] : Semigroup (LocallyConstant X Y)
  定义体: Function.Injective.semigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.semigroup, Injective, coe_injective, semigroup
-/
instance [Semigroup Y] : Semigroup (LocallyConstant X Y) :=
  Function.Injective.semigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemigroupWithZero
  signature: Y] : SemigroupWithZero (LocallyConstant X Y)
  body: Function.Injective.semigroupWithZero DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

@[to_additive]

中文:
实例 [SemigroupWithZero
  签名: Y] : SemigroupWithZero (LocallyConstant X Y)
  定义体: Function.Injective.semigroupWithZero DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.semigroupWithZero, Injective, coe_injective, semigroupWithZero
-/
instance [SemigroupWithZero Y] : SemigroupWithZero (LocallyConstant X Y) :=
  Function.Injective.semigroupWithZero DFunLike.coe DFunLike.coe_injective rfl fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: Y] : CommSemigroup (LocallyConstant X Y)
  body: Function.Injective.commSemigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl

中文:
实例 [CommSemigroup
  签名: Y] : CommSemigroup (LocallyConstant X Y)
  定义体: Function.Injective.commSemigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.commSemigroup, Injective, coe_injective, commSemigroup
-/
instance [CommSemigroup Y] : CommSemigroup (LocallyConstant X Y) :=
  Function.Injective.commSemigroup DFunLike.coe DFunLike.coe_injective fun _ _ => rfl

variable {α R : Type*}

@[to_additive]
/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [SMul α Y]
  body: f.map (n • ·)

@[to_additive (attr := simp)]

中文:
实例 smul
  签名: [SMul α Y]
  定义体: f.map (n • ·)

@[to_additive (attr := simp)]

Depends on / 依赖: f.map
-/
instance smul [SMul α Y] : SMul α (LocallyConstant X Y) where
  smul n f := f.map (n • ·)

@[to_additive (attr := simp)]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMul R Y] (r : R) (f : LocallyConstant X Y)
  statement: ⇑(r • f) = r • (f : X -> Y)
  proof: rfl

@[to_additive]

中文:
定理 coe_smul
  条件: [SMul R Y] (r : R) (f : LocallyConstant X Y)
  结论: ⇑(r • f) = r • (f : X -> Y)
  证明: rfl

@[to_additive]
-/
theorem coe_smul [SMul R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • (f : X -> Y) :=
  rfl

@[to_additive]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X)
  statement: (r • f) x = r • f x
  proof: rfl

@[to_additive existing LocallyConstant.smul]

中文:
定理 smul_apply
  条件: [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X)
  结论: (r • f) x = r • f x
  证明: rfl

@[to_additive existing LocallyConstant.smul]
-/
theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
  rfl

@[to_additive existing LocallyConstant.smul]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: Y α] : Pow (LocallyConstant X Y) α where
  body: f.map (· ^ n)

@[to_additive]

中文:
实例 [Pow
  签名: Y α] : Pow (LocallyConstant X Y) α where
  定义体: f.map (· ^ n)

@[to_additive]

Depends on / 依赖: f.map
-/
instance [Pow Y α] : Pow (LocallyConstant X Y) α where
  pow f n := f.map (· ^ n)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: Y] : Monoid (LocallyConstant X Y)
  body: Function.Injective.monoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [Monoid
  签名: Y] : Monoid (LocallyConstant X Y)
  定义体: Function.Injective.monoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.monoid, Injective, coe_injective, monoid
-/
instance [Monoid Y] : Monoid (LocallyConstant X Y) :=
  Function.Injective.monoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NatCast
  signature: Y] : NatCast (LocallyConstant X Y) where
  body: const X n

中文:
实例 [NatCast
  签名: Y] : 自然数Cast (LocallyConstant X Y) where
  定义体: const X n
-/
instance [NatCast Y] : NatCast (LocallyConstant X Y) where
  natCast n := const X n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IntCast
  signature: Y] : IntCast (LocallyConstant X Y) where
  body: const X n

中文:
实例 [IntCast
  签名: Y] : 整数Cast (LocallyConstant X Y) where
  定义体: const X n
-/
instance [IntCast Y] : IntCast (LocallyConstant X Y) where
  intCast n := const X n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoidWithOne
  signature: Y] : AddMonoidWithOne (LocallyConstant X Y)
  body: Function.Injective.addMonoidWithOne DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

@[to_additive]

中文:
实例 [AddMonoidWithOne
  签名: Y] : AddMonoidWithOne (LocallyConstant X Y)
  定义体: Function.Injective.addMonoidWithOne DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.addMonoidWithOne, Injective, addMonoidWithOne, coe_injective
-/
instance [AddMonoidWithOne Y] : AddMonoidWithOne (LocallyConstant X Y) :=
  Function.Injective.addMonoidWithOne DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: Y] : CommMonoid (LocallyConstant X Y)
  body: Function.Injective.commMonoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive]

中文:
实例 [CommMonoid
  签名: Y] : CommMonoid (LocallyConstant X Y)
  定义体: Function.Injective.commMonoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.commMonoid, Injective, coe_injective, commMonoid
-/
instance [CommMonoid Y] : CommMonoid (LocallyConstant X Y) :=
  Function.Injective.commMonoid DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: Y] : Group (LocallyConstant X Y)
  body: Function.Injective.group DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

中文:
实例 [Group
  签名: Y] : Group (LocallyConstant X Y)
  定义体: Function.Injective.group DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.group, Injective, coe_injective
-/
instance [Group Y] : Group (LocallyConstant X Y) :=
  Function.Injective.group DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: Y] : CommGroup (LocallyConstant X Y)
  body: Function.Injective.commGroup DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [CommGroup
  签名: Y] : CommGroup (LocallyConstant X Y)
  定义体: Function.Injective.commGroup DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.commGroup, Injective, coe_injective, commGroup
-/
instance [CommGroup Y] : CommGroup (LocallyConstant X Y) :=
  Function.Injective.commGroup DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Distrib
  signature: Y] : Distrib (LocallyConstant X Y)
  body: Function.Injective.distrib DFunLike.coe DFunLike.coe_injective (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [Distrib
  签名: Y] : Distrib (LocallyConstant X Y)
  定义体: Function.Injective.distrib DFunLike.coe DFunLike.coe_injective (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.distrib, Injective, coe_injective, distrib
-/
instance [Distrib Y] : Distrib (LocallyConstant X Y) :=
  Function.Injective.distrib DFunLike.coe DFunLike.coe_injective (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y)
  body: Function.Injective.nonUnitalNonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [NonUnitalNonAssocSemiring
  签名: Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y)
  定义体: Function.Injective.nonUnitalNonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonUnitalNonAssocSemiring, Injective, coe_injective, nonUnitalNonAssocSemiring
-/
instance [NonUnitalNonAssocSemiring Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalNonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: Y] : NonUnitalSemiring (LocallyConstant X Y)
  body: Function.Injective.nonUnitalSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [NonUnitalSemiring
  签名: Y] : NonUnitalSemiring (LocallyConstant X Y)
  定义体: Function.Injective.nonUnitalSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonUnitalSemiring, Injective, coe_injective, nonUnitalSemiring
-/
instance [NonUnitalSemiring Y] : NonUnitalSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: Y] : NonAssocSemiring (LocallyConstant X Y)
  body: Function.Injective.nonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 [NonAssocSemiring
  签名: Y] : NonAssocSemiring (LocallyConstant X Y)
  定义体: Function.Injective.nonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonAssocSemiring, Injective, coe_injective, nonAssocSemiring
-/
instance [NonAssocSemiring Y] : NonAssocSemiring (LocallyConstant X Y) :=
  Function.Injective.nonAssocSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/-- The constant-function embedding, as a ring hom. -/
@[simps]
/--
Definition of `constRingHom` / `constRingHom` 的定义

English:
definition constRingHom
  signature: [NonAssocSemiring Y]
  body: { constMonoidHom, constAddMonoidHom with toFun := const X }

中文:
定义 constRingHom
  签名: [NonAssocSemiring Y]
  定义体: { constMonoidHom, constAddMonoidHom with toFun := const X }

Depends on / 依赖: constAddMonoidHom, constMonoidHom
-/
def constRingHom [NonAssocSemiring Y] : Y ->+* LocallyConstant X Y :=
  { constMonoidHom, constAddMonoidHom with toFun := const X }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: Y] : Semiring (LocallyConstant X Y)
  body: Function.Injective.semiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 [Semiring
  签名: Y] : Semiring (LocallyConstant X Y)
  定义体: Function.Injective.semiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.semiring, Injective, coe_injective, semiring
-/
instance [Semiring Y] : Semiring (LocallyConstant X Y) :=
  Function.Injective.semiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: Y] : NonUnitalCommSemiring (LocallyConstant X Y)
  body: Function.Injective.nonUnitalCommSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [NonUnitalCommSemiring
  签名: Y] : NonUnitalCommSemiring (LocallyConstant X Y)
  定义体: Function.Injective.nonUnitalCommSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonUnitalCommSemiring, Injective, coe_injective, nonUnitalCommSemiring
-/
instance [NonUnitalCommSemiring Y] : NonUnitalCommSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalCommSemiring DFunLike.coe DFunLike.coe_injective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: Y] : CommSemiring (LocallyConstant X Y)
  body: Function.Injective.commSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 [CommSemiring
  签名: Y] : CommSemiring (LocallyConstant X Y)
  定义体: Function.Injective.commSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.commSemiring, Injective, coe_injective, commSemiring
-/
instance [CommSemiring Y] : CommSemiring (LocallyConstant X Y) :=
  Function.Injective.commSemiring DFunLike.coe DFunLike.coe_injective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: Y] : NonUnitalNonAssocRing (LocallyConstant X Y)
  body: Function.Injective.nonUnitalNonAssocRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [NonUnitalNonAssocRing
  签名: Y] : NonUnitalNonAssocRing (LocallyConstant X Y)
  定义体: Function.Injective.nonUnitalNonAssocRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonUnitalNonAssocRing, Injective, coe_injective, nonUnitalNonAssocRing
-/
instance [NonUnitalNonAssocRing Y] : NonUnitalNonAssocRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalNonAssocRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: Y] : NonUnitalRing (LocallyConstant X Y)
  body: Function.Injective.nonUnitalRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [NonUnitalRing
  签名: Y] : NonUnitalRing (LocallyConstant X Y)
  定义体: Function.Injective.nonUnitalRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonUnitalRing, Injective, coe_injective, nonUnitalRing
-/
instance [NonUnitalRing Y] : NonUnitalRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: Y] : NonAssocRing (LocallyConstant X Y)
  body: Function.Injective.nonAssocRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

中文:
实例 [NonAssocRing
  签名: Y] : NonAssocRing (LocallyConstant X Y)
  定义体: Function.Injective.nonAssocRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonAssocRing, Injective, coe_injective, nonAssocRing
-/
instance [NonAssocRing Y] : NonAssocRing (LocallyConstant X Y) :=
  Function.Injective.nonAssocRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: Y] : Ring (LocallyConstant X Y)
  body: Function.Injective.ring DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

中文:
实例 [Ring
  签名: Y] : Ring (LocallyConstant X Y)
  定义体: Function.Injective.ring DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.ring, Injective, coe_injective
-/
instance [Ring Y] : Ring (LocallyConstant X Y) :=
  Function.Injective.ring DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: Y] : NonUnitalCommRing (LocallyConstant X Y)
  body: Function.Injective.nonUnitalCommRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 [NonUnitalCommRing
  签名: Y] : NonUnitalCommRing (LocallyConstant X Y)
  定义体: Function.Injective.nonUnitalCommRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.nonUnitalCommRing, Injective, coe_injective, nonUnitalCommRing
-/
instance [NonUnitalCommRing Y] : NonUnitalCommRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalCommRing DFunLike.coe DFunLike.coe_injective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: Y] : CommRing (LocallyConstant X Y)
  body: Function.Injective.commRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

中文:
实例 [CommRing
  签名: Y] : CommRing (LocallyConstant X Y)
  定义体: Function.Injective.commRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

Depends on / 依赖: DFunLike, DFunLike.coe, DFunLike.coe_injective, Function, Function.Injective.commRing, Injective, coe_injective, commRing
-/
instance [CommRing Y] : CommRing (LocallyConstant X Y) :=
  Function.Injective.commRing DFunLike.coe DFunLike.coe_injective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

variable {R : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [MulAction R Y] : MulAction R (LocallyConstant X Y)
  body: Function.Injective.mulAction _ coe_injective fun _ _ => rfl

中文:
实例 [Monoid
  签名: R] [MulAction R Y] : MulAction R (LocallyConstant X Y)
  定义体: Function.Injective.mulAction _ coe_injective fun _ _ => rfl

Depends on / 依赖: Function, Function.Injective.mulAction, Injective, coe_injective, mulAction
-/
instance [Monoid R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  Function.Injective.mulAction _ coe_injective fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [AddMonoid Y] [DistribMulAction R Y] :
  body: Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl

中文:
实例 [Monoid
  签名: R] [AddMonoid Y] [DistribMulAction R Y] :
  定义体: Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, coeFnAddMonoidHom, coe_injective, distribMulAction
-/
instance [Monoid R] [AddMonoid Y] [DistribMulAction R Y] :
    DistribMulAction R (LocallyConstant X Y) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y)
  body: Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

中文:
实例 [Semiring
  签名: R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y)
  定义体: Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

Depends on / 依赖: Function, Function.Injective.module, Injective, coeFnAddMonoidHom, coe_injective, module
-/
instance [Semiring R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

section Algebra

variable [CommSemiring R] [Semiring Y] [Algebra R Y]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R (LocallyConstant X Y)
  body: constRingHom.comp algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

@[simp]

中文:
实例 :
  签名: Algebra R (LocallyConstant X Y)
  定义体: constRingHom.comp algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

@[simp]

Depends on / 依赖: algebraMap, constRingHom, constRingHom.comp
-/
instance : Algebra R (LocallyConstant X Y) where
algebraMap := constRingHom.comp algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

@[simp]
/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  given: (r : R)
  statement: ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X -> Y) r
  proof: rfl

中文:
定理 coe_algebraMap
  条件: (r : R)
  结论: ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X -> Y) r
  证明: rfl
-/
theorem coe_algebraMap (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X -> Y) r :=
  rfl

end Algebra

section coeFn

/--
Definition of `coeFnRingHom` / `coeFnRingHom` 的定义

English:
definition coeFnRingHom
  signature: [Semiring Y]
  body: coeFnMonoidHom
  __ := coeFnAddMonoidHom

中文:
定义 coeFnRingHom
  签名: [Semiring Y]
  定义体: coeFnMonoidHom
  __ := coeFnAddMonoidHom
-/
@[simps!] def coeFnRingHom [Semiring Y] : LocallyConstant X Y ->+* X -> Y where
  toMonoidHom := coeFnMonoidHom
  __ := coeFnAddMonoidHom

/--
Definition of `coeFnₗ` / `coeFnₗ` 的定义

English:
definition coeFnₗ
  signature: (R : Type*) [Semiring R] [AddCommMonoid Y]
  body: coeFnAddMonoidHom.toAddHom
  map_smul' _ _ := rfl

中文:
定义 coeFnₗ
  签名: (R : 类型) [Semiring R] [AddCommMonoid Y]
  定义体: coeFnAddMonoidHom.toAddHom
  map_smul' _ _ := rfl
-/
@[simps!] def coeFnₗ (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] : LocallyConstant X Y ->ₗ[R] X -> Y where
  toAddHom := coeFnAddMonoidHom.toAddHom
  map_smul' _ _ := rfl

/--
Definition of `coeFnAlgHom` / `coeFnAlgHom` 的定义

English:
definition coeFnAlgHom
  signature: (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
  body: coeFnRingHom
  commutes' _ := rfl

中文:
定义 coeFnAlgHom
  签名: (R : 类型) [CommSemiring R] [Semiring Y] [Algebra R Y]
  定义体: coeFnRingHom
  commutes' _ := rfl
-/
@[simps!] def coeFnAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] :
    LocallyConstant X Y ->ₐ[R] X -> Y where
  toRingHom := coeFnRingHom
  commutes' _ := rfl

end coeFn

section Eval

/-- Evaluation as a `MonoidHom` -/
@[to_additive (attr := simps!) /-- Evaluation as an `AddMonoidHom` -/]
/--
Definition of `evalMonoidHom` / `evalMonoidHom` 的定义

English:
definition evalMonoidHom
  signature: [MulOneClass Y] (x : X)
  body: (Pi.evalMonoidHom _ x).comp coeFnMonoidHom

中文:
定义 evalMonoidHom
  签名: [MulOneClass Y] (x : X)
  定义体: (Pi.evalMonoidHom _ x).comp coeFnMonoidHom

Depends on / 依赖: Pi.evalMonoidHom, coeFnMonoidHom, evalMonoidHom
-/
def evalMonoidHom [MulOneClass Y] (x : X) : LocallyConstant X Y ->* Y :=
  (Pi.evalMonoidHom _ x).comp coeFnMonoidHom

/--
Definition of `evalₗ` / `evalₗ` 的定义

English:
definition evalₗ
  signature: (R : Type*) [Semiring R] [AddCommMonoid Y]
  body: (LinearMap.proj x).comp (coeFnₗ R)

中文:
定义 evalₗ
  签名: (R : 类型) [Semiring R] [AddCommMonoid Y]
  定义体: (LinearMap.proj x).comp (coeFnₗ R)
-/
@[simps!] def evalₗ (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] (x : X) : LocallyConstant X Y ->ₗ[R] Y :=
  (LinearMap.proj x).comp (coeFnₗ R)

/--
Definition of `evalRingHom` / `evalRingHom` 的定义

English:
definition evalRingHom
  signature: [Semiring Y] (x : X)
  body: (Pi.evalRingHom _ x).comp coeFnRingHom

中文:
定义 evalRingHom
  签名: [Semiring Y] (x : X)
  定义体: (Pi.evalRingHom _ x).comp coeFnRingHom
-/
@[simps!] def evalRingHom [Semiring Y] (x : X) : LocallyConstant X Y ->+* Y :=
  (Pi.evalRingHom _ x).comp coeFnRingHom

/-- Evaluation as an `AlgHom` -/
@[simps!]
/--
Definition of `evalₐ` / `evalₐ` 的定义

English:
definition evalₐ
  signature: (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] (x : X)
  body: (Pi.evalAlgHom _ _ x).comp (coeFnAlgHom R)

中文:
定义 evalₐ
  签名: (R : 类型) [CommSemiring R] [Semiring Y] [Algebra R Y] (x : X)
  定义体: (Pi.evalAlgHom _ _ x).comp (coeFnAlgHom R)

Depends on / 依赖: Pi.evalAlgHom, coeFnAlgHom, evalAlgHom
-/
def evalₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] (x : X) :
    LocallyConstant X Y ->ₐ[R] Y :=
  (Pi.evalAlgHom _ _ x).comp (coeFnAlgHom R)

end Eval

section Comap

variable [TopologicalSpace Y] {Z : Type*}

/-- `LocallyConstant.comap` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `LocallyConstant.comap` as an `AddMonoidHom`. -/]
/--
Definition of `comapMonoidHom` / `comapMonoidHom` 的定义

English:
definition comapMonoidHom
  signature: [MulOneClass Z] (f : C(X, Y))
  body: comap f
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 comapMonoidHom
  签名: [MulOneClass Z] (f : C(X, Y))
  定义体: comap f
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def comapMonoidHom [MulOneClass Z] (f : C(X, Y)) :
    LocallyConstant Y Z ->* LocallyConstant X Z where
  toFun := comap f
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `LocallyConstant.comap` as a linear map. -/
@[simps!]
/--
Definition of `comapₗ` / `comapₗ` 的定义

English:
definition comapₗ
  signature: (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y))
  body: comap f
  map_add' := map_add (comapAddMonoidHom f)
  map_smul' _ _ := rfl

中文:
定义 comapₗ
  签名: (R : 类型) [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y))
  定义体: comap f
  map_add' := map_add (comapAddMonoidHom f)
  map_smul' _ _ := rfl
-/
def comapₗ (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y)) :
    LocallyConstant Y Z ->ₗ[R] LocallyConstant X Z where
  toFun := comap f
  map_add' := map_add (comapAddMonoidHom f)
  map_smul' _ _ := rfl

/-- `LocallyConstant.comap` as a `RingHom`. -/
@[simps!]
/--
Definition of `comapRingHom` / `comapRingHom` 的定义

English:
definition comapRingHom
  signature: [Semiring Z] (f : C(X, Y))
  body: comapMonoidHom f
  __ := (comapAddMonoidHom f)

中文:
定义 comapRingHom
  签名: [Semiring Z] (f : C(X, Y))
  定义体: comapMonoidHom f
  __ := (comapAddMonoidHom f)

Depends on / 依赖: comapMonoidHom
-/
def comapRingHom [Semiring Z] (f : C(X, Y)) :
    LocallyConstant Y Z ->+* LocallyConstant X Z where
  toMonoidHom := comapMonoidHom f
  __ := (comapAddMonoidHom f)

/-- `LocallyConstant.comap` as an `AlgHom` -/
@[simps!]
/--
Definition of `comapₐ` / `comapₐ` 的定义

English:
definition comapₐ
  signature: (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z]
  body: comapRingHom f
  commutes' _ := rfl

中文:
定义 comapₐ
  签名: (R : 类型) [CommSemiring R] [Semiring Z] [Algebra R Z]
  定义体: comapRingHom f
  commutes' _ := rfl

Depends on / 依赖: comapRingHom
-/
def comapₐ (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z]
    (f : C(X, Y)) : LocallyConstant Y Z ->ₐ[R] LocallyConstant X Z where
  toRingHom := comapRingHom f
  commutes' _ := rfl

/--
lemma `ker_comapₗ` / 引理 `ker_comapₗ`

English:
lemma ker_comapₗ
  statement: [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y))
  proof: LinearMap.ker_eq_bot_of_injective comap_injective _ hfs

中文:
引理 ker_comapₗ
  结论: [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y))
  证明: LinearMap.ker_eq_bot_of_injective comap_injective _ hfs

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot_of_injective, comap_injective, ker_eq_bot_of_injective
-/
lemma ker_comapₗ [Semiring R] [AddCommMonoid Z] [Module R Z] (f : C(X, Y))
    (hfs : Function.Surjective f) :
    LinearMap.ker (comapₗ R f : LocallyConstant Y Z ->ₗ[R] LocallyConstant X Z) = ⊥ :=
LinearMap.ker_eq_bot_of_injective comap_injective _ hfs

/-- `LocallyConstant.congrLeft` as a linear equivalence. -/
@[simps!]
/--
Definition of `congrLeftₗ` / `congrLeftₗ` 的定义

English:
definition congrLeftₗ
  signature: (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (e : X ≃ₜ Y)
  body: comapₗ R ⟨_, e.symm.continuous⟩
  __ := congrLeft e

中文:
定义 congrLeftₗ
  签名: (R : 类型) [Semiring R] [AddCommMonoid Z] [Module R Z] (e : X ≃ₜ Y)
  定义体: comapₗ R ⟨_, e.symm.continuous⟩
  __ := congrLeft e

Depends on / 依赖: continuous, e.symm.continuous
-/
def congrLeftₗ (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z where
  toLinearMap := comapₗ R ⟨_, e.symm.continuous⟩
  __ := congrLeft e

/-- `LocallyConstant.congrLeft` as a `RingEquiv`. -/
@[simps!]
/--
Definition of `congrLeftRingEquiv` / `congrLeftRingEquiv` 的定义

English:
definition congrLeftRingEquiv
  signature: [Semiring Z] (e : X ≃ₜ Y)
  body: congrLeft e
  __ := comapMonoidHom ⟨_, e.symm.continuous⟩
  __ := comapAddMonoidHom ⟨_, e.symm.continuous⟩

中文:
定义 congrLeftRingEquiv
  签名: [Semiring Z] (e : X ≃ₜ Y)
  定义体: congrLeft e
  __ := comapMonoidHom ⟨_, e.symm.continuous⟩
  __ := comapAddMonoidHom ⟨_, e.symm.continuous⟩

Depends on / 依赖: congrLeft
-/
def congrLeftRingEquiv [Semiring Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃+* LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapMonoidHom ⟨_, e.symm.continuous⟩
  __ := comapAddMonoidHom ⟨_, e.symm.continuous⟩

/-- `LocallyConstant.congrLeft` as an `AlgEquiv`. -/
@[simps!]
/--
Definition of `congrLeftₐ` / `congrLeftₐ` 的定义

English:
definition congrLeftₐ
  signature: (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z] (e : X ≃ₜ Y)
  body: congrLeft e
  __ := comapₐ R ⟨_, e.symm.continuous⟩

中文:
定义 congrLeftₐ
  签名: (R : 类型) [CommSemiring R] [Semiring Z] [Algebra R Z] (e : X ≃ₜ Y)
  定义体: congrLeft e
  __ := comapₐ R ⟨_, e.symm.continuous⟩

Depends on / 依赖: congrLeft
-/
def congrLeftₐ (R : Type*) [CommSemiring R] [Semiring Z] [Algebra R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₐ[R] LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapₐ R ⟨_, e.symm.continuous⟩

end Comap

section Map

variable {Z : Type*}

/-- `LocallyConstant.map` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `LocallyConstant.map` as an `AddMonoidHom`. -/]
/--
Definition of `mapMonoidHom` / `mapMonoidHom` 的定义

English:
definition mapMonoidHom
  signature: [MulOneClass Y] [MulOneClass Z] (f : Y ->* Z)
  body: map f
  map_one' := by aesop
  map_mul' := by aesop

中文:
定义 mapMonoidHom
  签名: [MulOneClass Y] [MulOneClass Z] (f : Y ->* Z)
  定义体: map f
  map_one' := by aesop
  map_mul' := by aesop
-/
def mapMonoidHom [MulOneClass Y] [MulOneClass Z] (f : Y ->* Z) :
    LocallyConstant X Y ->* LocallyConstant X Z where
  toFun := map f
  map_one' := by aesop
  map_mul' := by aesop

/-- `LocallyConstant.map` as a linear map. -/
@[simps!]
/--
Definition of `mapₗ` / `mapₗ` 的定义

English:
definition mapₗ
  signature: (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
  body: map f
  map_add' := by aesop
  map_smul' := by aesop

中文:
定义 mapₗ
  签名: (R : 类型) [Semiring R] [AddCommMonoid Y] [Module R Y]
  定义体: map f
  map_add' := by aesop
  map_smul' := by aesop
-/
def mapₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (f : Y ->ₗ[R] Z) :
    LocallyConstant X Y ->ₗ[R] LocallyConstant X Z where
  toFun := map f
  map_add' := by aesop
  map_smul' := by aesop

/-- `LocallyConstant.map` as a `RingHom`. -/
@[simps!]
/--
Definition of `mapRingHom` / `mapRingHom` 的定义

English:
definition mapRingHom
  signature: [Semiring Y] [Semiring Z] (f : Y ->+* Z)
  body: mapMonoidHom f
  __ := (mapAddMonoidHom f.toAddMonoidHom)

中文:
定义 mapRingHom
  签名: [Semiring Y] [Semiring Z] (f : Y ->+* Z)
  定义体: mapMonoidHom f
  __ := (mapAddMonoidHom f.toAddMonoidHom)

Depends on / 依赖: mapMonoidHom
-/
def mapRingHom [Semiring Y] [Semiring Z] (f : Y ->+* Z) :
    LocallyConstant X Y ->+* LocallyConstant X Z where
  toMonoidHom := mapMonoidHom f
  __ := (mapAddMonoidHom f.toAddMonoidHom)

/-- `LocallyConstant.map` as an `AlgHom` -/
@[simps!]
/--
Definition of `mapₐ` / `mapₐ` 的定义

English:
definition mapₐ
  signature: (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
  body: mapRingHom f
  commutes' _ := by aesop

中文:
定义 mapₐ
  签名: (R : 类型) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
  定义体: mapRingHom f
  commutes' _ := by aesop

Depends on / 依赖: mapRingHom
-/
def mapₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
    (f : Y ->ₐ[R] Z) : LocallyConstant X Y ->ₐ[R] LocallyConstant X Z where
  toRingHom := mapRingHom f
  commutes' _ := by aesop

/-- `LocallyConstant.congrRight` as a linear equivalence. -/
@[simps!]
/--
Definition of `congrRightₗ` / `congrRightₗ` 的定义

English:
definition congrRightₗ
  signature: (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
  body: mapₗ R e
  __ := congrRight e.toEquiv

中文:
定义 congrRightₗ
  签名: (R : 类型) [Semiring R] [AddCommMonoid Y] [Module R Y]
  定义体: mapₗ R e
  __ := congrRight e.toEquiv
-/
def congrRightₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (e : Y ≃ₗ[R] Z) :
    LocallyConstant X Y ≃ₗ[R] LocallyConstant X Z where
  toLinearMap := mapₗ R e
  __ := congrRight e.toEquiv

/-- `LocallyConstant.congrRight` as a `RingEquiv`. -/
@[simps!]
/--
Definition of `congrRightRingEquiv` / `congrRightRingEquiv` 的定义

English:
definition congrRightRingEquiv
  signature: [Semiring Y] [Semiring Z] (e : Y ≃+* Z)
  body: congrRight e
  __ := mapMonoidHom e.toMonoidHom
  __ := mapAddMonoidHom e.toAddMonoidHom

中文:
定义 congrRightRingEquiv
  签名: [Semiring Y] [Semiring Z] (e : Y ≃+* Z)
  定义体: congrRight e
  __ := mapMonoidHom e.toMonoidHom
  __ := mapAddMonoidHom e.toAddMonoidHom

Depends on / 依赖: congrRight
-/
def congrRightRingEquiv [Semiring Y] [Semiring Z] (e : Y ≃+* Z) :
    LocallyConstant X Y ≃+* LocallyConstant X Z where
  toEquiv := congrRight e
  __ := mapMonoidHom e.toMonoidHom
  __ := mapAddMonoidHom e.toAddMonoidHom

/-- `LocallyConstant.congrRight` as an `AlgEquiv`. -/
@[simps!]
/--
Definition of `congrRightₐ` / `congrRightₐ` 的定义

English:
definition congrRightₐ
  signature: (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
  body: congrRight e
  __ := mapₐ R e.toAlgHom

中文:
定义 congrRightₐ
  签名: (R : 类型) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
  定义体: congrRight e
  __ := mapₐ R e.toAlgHom

Depends on / 依赖: congrRight
-/
def congrRightₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] [Semiring Z] [Algebra R Z]
    (e : Y ≃ₐ[R] Z) : LocallyConstant X Y ≃ₐ[R] LocallyConstant X Z where
  toEquiv := congrRight e
  __ := mapₐ R e.toAlgHom

end Map

section Const

/-- `LocallyConstant.const` as a linear map. -/
@[simps!]
/--
Definition of `constₗ` / `constₗ` 的定义

English:
definition constₗ
  signature: (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
  body: const X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 constₗ
  签名: (R : 类型) [Semiring R] [AddCommMonoid Y] [Module R Y]
  定义体: const X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def constₗ (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y] :
    Y ->ₗ[R] LocallyConstant X Y where
  toFun := const X
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `LocallyConstant.const` as an `AlgHom` -/
@[simps!]
/--
Definition of `constₐ` / `constₐ` 的定义

English:
definition constₐ
  signature: (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
  body: constRingHom
  commutes' _ := rfl

中文:
定义 constₐ
  签名: (R : 类型) [CommSemiring R] [Semiring Y] [Algebra R Y]
  定义体: constRingHom
  commutes' _ := rfl

Depends on / 依赖: constRingHom
-/
def constₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] :
    Y ->ₐ[R] LocallyConstant X Y where
  toRingHom := constRingHom
  commutes' _ := rfl

end Const

end LocallyConstant
