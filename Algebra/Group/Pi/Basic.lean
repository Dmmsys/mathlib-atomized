/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Spread

/-!
# Instances and theorems on pi types

This file provides instances for the typeclass defined in `Algebra.Group.Defs`. More sophisticated
instances are defined in `Algebra.Group.Pi.Lemmas` files elsewhere.

## Porting note

This file relied on the `pi_instance` tactic, which was not available at the time of porting. The
comment `--pi_instance` is inserted before all fields which were previously derived by
`pi_instance`. See this Zulip discussion:
[https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/not.20porting.20pi_instance]
-/

@[expose] public section

-- We enforce to only import `Algebra.Group.Defs` and basic logic
assert_not_exists Set.range MonoidHom MonoidWithZero DenselyOrdered

universe u v₁ v₂ v₃

variable {I : Type u}

-- The indexing type
variable {α β γ : Type*}

-- The families of types already equipped with instances
variable {f : I -> Type v₁} {g : I -> Type v₂} {h : I -> Type v₃}
variable (x y : forall i, f i) (i : I)

namespace Pi

@[to_additive]
/--
Instance `isMulCommutative` / 实例 `isMulCommutative`

English:
instance isMulCommutative
  signature: [forall i, Mul (f i)] [forall i, IsMulCommutative (f i)]
  body: by ext; apply mul_comm'

@[to_additive]

中文:
实例 isMulCommutative
  签名: [对任意 i, 乘法 (f i)] [对任意 i, 是MulCommutative (f i)]
  定义体: by ext; apply mul_comm'

@[to_additive]

Depends on / 依赖: mul_comm
-/
instance isMulCommutative [forall i, Mul (f i)] [forall i, IsMulCommutative (f i)] :
    IsMulCommutative (forall i, f i) where
  is_comm.comm _ _ := by ext; apply mul_comm'

@[to_additive]
/--
Instance `commMagma` / 实例 `commMagma`

English:
instance commMagma
  signature: [forall i, CommMagma (f i)]
  body: by ext; apply mul_comm

@[to_additive]

中文:
实例 commMagma
  签名: [对任意 i, 交换原群 (f i)]
  定义体: by ext; apply mul_comm

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.image2, image2, mul_comm
-/
instance commMagma [forall i, CommMagma (f i)] : CommMagma (forall i, f i) where
  mul_comm _ _ := by ext; apply mul_comm

@[to_additive]
/--
Instance `semigroup` / 实例 `semigroup`

English:
instance semigroup
  signature: [forall i, Semigroup (f i)]
  body: by intros; ext; exact mul_assoc _ _ _

@[to_additive]

中文:
实例 semigroup
  签名: [对任意 i, 半群 (f i)]
  定义体: by intros; ext; exact mul_assoc _ _ _

@[to_additive]

Depends on / 依赖: Nonempty, Nonempty.of_image2_left, intros, mul_assoc, of_image2_left
-/
instance semigroup [forall i, Semigroup (f i)] : Semigroup (forall i, f i) where
  mul_assoc := by intros; ext; exact mul_assoc _ _ _

@[to_additive]
/--
Instance `commSemigroup` / 实例 `commSemigroup`

English:
instance commSemigroup
  signature: [forall i, CommSemigroup (f i)]

中文:
实例 commSemigroup
  签名: [对任意 i, 交换半群 (f i)]

Depends on / 依赖: Nonempty, Nonempty.of_image2_right, of_image2_right
-/
instance commSemigroup [forall i, CommSemigroup (f i)] : CommSemigroup (forall i, f i) where

@[to_additive]
/--
Instance `mulOneClass` / 实例 `mulOneClass`

English:
instance mulOneClass
  signature: [forall i, MulOneClass (f i)]
  body: by intros; ext; exact one_mul _
  mul_one := by intros; ext; exact mul_one _

@[to_additive]

中文:
实例 mulOneClass
  签名: [对任意 i, MulOne类 (f i)]
  定义体: by intros; ext; exact one_mul _
  mul_one := by intros; ext; exact mul_one _

@[to_additive]

Depends on / 依赖: intros, mul_one, one_mul
-/
instance mulOneClass [forall i, MulOneClass (f i)] : MulOneClass (forall i, f i) where
  one_mul := by intros; ext; exact one_mul _
  mul_one := by intros; ext; exact mul_one _

@[to_additive]
/--
Instance `invOneClass` / 实例 `invOneClass`

English:
instance invOneClass
  signature: [forall i, InvOneClass (f i)]
  body: by ext; exact inv_one

@[to_additive]

中文:
实例 invOneClass
  签名: [对任意 i, InvOne类 (f i)]
  定义体: by ext; exact inv_one

@[to_additive]

Depends on / 依赖: inv_one
-/
instance invOneClass [forall i, InvOneClass (f i)] : InvOneClass (forall i, f i) where
  inv_one := by ext; exact inv_one

@[to_additive]
/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: [forall i, Monoid (f i)]
  body: semigroup
  __ := mulOneClass
  npow := fun n x i => x i ^ n
  npow_zero := by intros; ext; exact Monoid.npow_zero _
  npow_succ := by intros; ext; exact Monoid.npow_succ _ _

@[to_additive]

中文:
实例 monoid
  签名: [对任意 i, 幺半群 (f i)]
  定义体: semigroup
  __ := mulOneClass
  npow := fun n x i => x i ^ n
  npow_zero := by intros; ext; exact Monoid.npow_zero _
  npow_succ := by intros; ext; exact Monoid.npow_succ _ _

@[to_additive]

Depends on / 依赖: semigroup
-/
instance monoid [forall i, Monoid (f i)] : Monoid (forall i, f i) where
  __ := semigroup
  __ := mulOneClass
  npow := fun n x i => x i ^ n
  npow_zero := by intros; ext; exact Monoid.npow_zero _
  npow_succ := by intros; ext; exact Monoid.npow_succ _ _

@[to_additive]
/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: [forall i, CommMonoid (f i)]

中文:
实例 commMonoid
  签名: [对任意 i, 交换幺半群 (f i)]
-/
instance commMonoid [forall i, CommMonoid (f i)] : CommMonoid (forall i, f i) where

@[to_additive Pi.subNegMonoid]
/--
Instance `divInvMonoid` / 实例 `divInvMonoid`

English:
instance divInvMonoid
  signature: [forall i, DivInvMonoid (f i)]
  body: fun z x i => x i ^ z
  div_eq_mul_inv := by intros; ext; exact div_eq_mul_inv _ _
  zpow_zero' := by intros; ext; exact DivInvMonoid.zpow_zero' _
  zpow_succ' := by intros; ext; exact DivInvMonoid.zpow_succ' _ _
  zpow_neg' := by intros; ext; exact DivInvMonoid.zpow_neg' _ _

@[to_additive]

中文:
实例 divInvMonoid
  签名: [对任意 i, 除逆幺半群 (f i)]
  定义体: fun z x i => x i ^ z
  div_eq_mul_inv := by intros; ext; exact div_eq_mul_inv _ _
  zpow_zero' := by intros; ext; exact DivInvMonoid.zpow_zero' _
  zpow_succ' := by intros; ext; exact DivInvMonoid.zpow_succ' _ _
  zpow_neg' := by intros; ext; exact DivInvMonoid.zpow_neg' _ _

@[to_additive]
-/
instance divInvMonoid [forall i, DivInvMonoid (f i)] : DivInvMonoid (forall i, f i) where
  zpow := fun z x i => x i ^ z
  div_eq_mul_inv := by intros; ext; exact div_eq_mul_inv _ _
  zpow_zero' := by intros; ext; exact DivInvMonoid.zpow_zero' _
  zpow_succ' := by intros; ext; exact DivInvMonoid.zpow_succ' _ _
  zpow_neg' := by intros; ext; exact DivInvMonoid.zpow_neg' _ _

@[to_additive]
/--
Instance `divInvOneMonoid` / 实例 `divInvOneMonoid`

English:
instance divInvOneMonoid
  signature: [forall i, DivInvOneMonoid (f i)]
  body: by ext; exact inv_one

@[to_additive]

中文:
实例 divInvOneMonoid
  签名: [对任意 i, DivInvOne幺半群 (f i)]
  定义体: by ext; exact inv_one

@[to_additive]

Depends on / 依赖: inv_one
-/
instance divInvOneMonoid [forall i, DivInvOneMonoid (f i)] : DivInvOneMonoid (forall i, f i) where
  inv_one := by ext; exact inv_one

@[to_additive]
/--
Instance `involutiveInv` / 实例 `involutiveInv`

English:
instance involutiveInv
  signature: [forall i, InvolutiveInv (f i)]
  body: by intros; ext; exact inv_inv _

@[to_additive]

中文:
实例 involutiveInv
  签名: [对任意 i, InvolutiveInv (f i)]
  定义体: by intros; ext; exact inv_inv _

@[to_additive]

Depends on / 依赖: intros, inv_inv
-/
instance involutiveInv [forall i, InvolutiveInv (f i)] : InvolutiveInv (forall i, f i) where
  inv_inv := by intros; ext; exact inv_inv _

@[to_additive]
/--
Instance `divisionMonoid` / 实例 `divisionMonoid`

English:
instance divisionMonoid
  signature: [forall i, DivisionMonoid (f i)]
  body: divInvMonoid
  __ := involutiveInv
  mul_inv_rev := by intros; ext; exact mul_inv_rev _ _
  inv_eq_of_mul := by intro _ _ h; ext; exact DivisionMonoid.inv_eq_of_mul _ _ (congrFun h _)

@[to_additive instSubtractionCommMonoid]

中文:
实例 divisionMonoid
  签名: [对任意 i, Division幺半群 (f i)]
  定义体: divInvMonoid
  __ := involutiveInv
  mul_inv_rev := by intros; ext; exact mul_inv_rev _ _
  inv_eq_of_mul := by intro _ _ h; ext; exact DivisionMonoid.inv_eq_of_mul _ _ (congrFun h _)

@[to_additive instSubtractionCommMonoid]

Depends on / 依赖: divInvMonoid
-/
instance divisionMonoid [forall i, DivisionMonoid (f i)] : DivisionMonoid (forall i, f i) where
  __ := divInvMonoid
  __ := involutiveInv
  mul_inv_rev := by intros; ext; exact mul_inv_rev _ _
  inv_eq_of_mul := by intro _ _ h; ext; exact DivisionMonoid.inv_eq_of_mul _ _ (congrFun h _)

@[to_additive instSubtractionCommMonoid]
/--
Instance `divisionCommMonoid` / 实例 `divisionCommMonoid`

English:
instance divisionCommMonoid
  signature: [forall i, DivisionCommMonoid (f i)]
  body: { divisionMonoid, commSemigroup with }

@[to_additive]

中文:
实例 divisionCommMonoid
  签名: [对任意 i, DivisionComm幺半群 (f i)]
  定义体: { divisionMonoid, commSemigroup with }

@[to_additive]

Depends on / 依赖: commSemigroup, divisionMonoid
-/
instance divisionCommMonoid [forall i, DivisionCommMonoid (f i)] : DivisionCommMonoid (forall i, f i) :=
  { divisionMonoid, commSemigroup with }

@[to_additive]
/--
Instance `group` / 实例 `group`

English:
instance group
  signature: [forall i, Group (f i)]
  body: by intros; ext; exact inv_mul_cancel _

@[to_additive]

中文:
实例 group
  签名: [对任意 i, 群 (f i)]
  定义体: by intros; ext; exact inv_mul_cancel _

@[to_additive]

Depends on / 依赖: intros, inv_mul_cancel
-/
instance group [forall i, Group (f i)] : Group (forall i, f i) where
  inv_mul_cancel := by intros; ext; exact inv_mul_cancel _

@[to_additive]
/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: [forall i, CommGroup (f i)]
  body: { group, commMonoid with }

中文:
实例 commGroup
  签名: [对任意 i, 交换群 (f i)]
  定义体: { group, commMonoid with }

Depends on / 依赖: commMonoid
-/
instance commGroup [forall i, CommGroup (f i)] : CommGroup (forall i, f i) := { group, commMonoid with }

/--
Instance `instIsLeftCancelMul` / 实例 `instIsLeftCancelMul`

English:
instance instIsLeftCancelMul
  signature: [forall i, Mul (f i)] [forall i, IsLeftCancelMul (f i)]
  body: funext fun _ => mul_left_cancel (congr_fun h _)

中文:
实例 instIsLeftCancelMul
  签名: [对任意 i, 乘法 (f i)] [对任意 i, 左乘消去 (f i)]
  定义体: funext fun _ => mul_left_cancel (congr_fun h _)
-/
@[to_additive] instance instIsLeftCancelMul [forall i, Mul (f i)] [forall i, IsLeftCancelMul (f i)] :
    IsLeftCancelMul (forall i, f i) where
  mul_left_cancel _ _ _ h := funext fun _ => mul_left_cancel (congr_fun h _)

/--
Instance `instIsRightCancelMul` / 实例 `instIsRightCancelMul`

English:
instance instIsRightCancelMul
  signature: [forall i, Mul (f i)] [forall i, IsRightCancelMul (f i)]
  body: funext fun _ => mul_right_cancel (congr_fun h _)

中文:
实例 instIsRightCancelMul
  签名: [对任意 i, 乘法 (f i)] [对任意 i, 右乘消去 (f i)]
  定义体: funext fun _ => mul_right_cancel (congr_fun h _)
-/
@[to_additive] instance instIsRightCancelMul [forall i, Mul (f i)] [forall i, IsRightCancelMul (f i)] :
    IsRightCancelMul (forall i, f i) where
  mul_right_cancel _ _ _ h := funext fun _ => mul_right_cancel (congr_fun h _)

/--
Instance `instIsCancelMul` / 实例 `instIsCancelMul`

English:
instance instIsCancelMul
  signature: [forall i, Mul (f i)] [forall i, IsCancelMul (f i)]

中文:
实例 instIsCancelMul
  签名: [对任意 i, 乘法 (f i)] [对任意 i, 是消去乘法 (f i)]
-/
@[to_additive] instance instIsCancelMul [forall i, Mul (f i)] [forall i, IsCancelMul (f i)] :
    IsCancelMul (forall i, f i) where

@[to_additive]
/--
Instance `leftCancelSemigroup` / 实例 `leftCancelSemigroup`

English:
instance leftCancelSemigroup
  signature: [forall i, LeftCancelSemigroup (f i)]
  body: { semigroup with mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]

中文:
实例 leftCancelSemigroup
  签名: [对任意 i, 左消去半群 (f i)]
  定义体: { semigroup with mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]

Depends on / 依赖: mul_left_cancel, semigroup
-/
instance leftCancelSemigroup [forall i, LeftCancelSemigroup (f i)] : LeftCancelSemigroup (forall i, f i) :=
  { semigroup with mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]
/--
Instance `rightCancelSemigroup` / 实例 `rightCancelSemigroup`

English:
instance rightCancelSemigroup
  signature: [forall i, RightCancelSemigroup (f i)]
  body: { semigroup with mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]

中文:
实例 rightCancelSemigroup
  签名: [对任意 i, 右消去半群 (f i)]
  定义体: { semigroup with mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]

Depends on / 依赖: mul_right_cancel, semigroup
-/
instance rightCancelSemigroup [forall i, RightCancelSemigroup (f i)] : RightCancelSemigroup (forall i, f i) :=
  { semigroup with mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]
/--
Instance `leftCancelMonoid` / 实例 `leftCancelMonoid`

English:
instance leftCancelMonoid
  signature: [forall i, LeftCancelMonoid (f i)]
  body: { leftCancelSemigroup, monoid with }

@[to_additive]

中文:
实例 leftCancelMonoid
  签名: [对任意 i, 左消去幺半群 (f i)]
  定义体: { leftCancelSemigroup, monoid with }

@[to_additive]

Depends on / 依赖: leftCancelSemigroup, monoid
-/
instance leftCancelMonoid [forall i, LeftCancelMonoid (f i)] : LeftCancelMonoid (forall i, f i) :=
  { leftCancelSemigroup, monoid with }

@[to_additive]
/--
Instance `rightCancelMonoid` / 实例 `rightCancelMonoid`

English:
instance rightCancelMonoid
  signature: [forall i, RightCancelMonoid (f i)]
  body: { rightCancelSemigroup, monoid with }

@[to_additive]

中文:
实例 rightCancelMonoid
  签名: [对任意 i, 右消去幺半群 (f i)]
  定义体: { rightCancelSemigroup, monoid with }

@[to_additive]

Depends on / 依赖: monoid, rightCancelSemigroup
-/
instance rightCancelMonoid [forall i, RightCancelMonoid (f i)] : RightCancelMonoid (forall i, f i) :=
  { rightCancelSemigroup, monoid with }

@[to_additive]
/--
Instance `cancelMonoid` / 实例 `cancelMonoid`

English:
instance cancelMonoid
  signature: [forall i, CancelMonoid (f i)]
  body: { leftCancelMonoid, rightCancelMonoid with }

@[to_additive]

中文:
实例 cancelMonoid
  签名: [对任意 i, 消去幺半群 (f i)]
  定义体: { leftCancelMonoid, rightCancelMonoid with }

@[to_additive]

Depends on / 依赖: leftCancelMonoid, rightCancelMonoid
-/
instance cancelMonoid [forall i, CancelMonoid (f i)] : CancelMonoid (forall i, f i) :=
  { leftCancelMonoid, rightCancelMonoid with }

@[to_additive]
/--
Instance `cancelCommMonoid` / 实例 `cancelCommMonoid`

English:
instance cancelCommMonoid
  signature: [forall i, CancelCommMonoid (f i)]
  body: { leftCancelMonoid, commMonoid with }

中文:
实例 cancelCommMonoid
  签名: [对任意 i, 消去交换幺半群 (f i)]
  定义体: { leftCancelMonoid, commMonoid with }

Depends on / 依赖: commMonoid, leftCancelMonoid
-/
instance cancelCommMonoid [forall i, CancelCommMonoid (f i)] : CancelCommMonoid (forall i, f i) :=
  { leftCancelMonoid, commMonoid with }

end Pi

namespace Function

section Extend

@[to_additive]
/--
theorem `extend_one` / 定理 `extend_one`

English:
theorem extend_one
  given: [One γ] (f : α -> β)
  statement: Function.extend f (1 : α -> γ) (1 : β -> γ) = 1
  proof: funext fun _ => by apply ite_self

@[to_additive]

中文:
定理 extend_one
  条件: [幺 γ] (f : α -> β)
  结论: 函数.extend f (1 : α -> γ) (1 : β -> γ) = 1
  证明: funext fun _ => by apply ite_self

@[to_additive]

Depends on / 依赖: ite_self
-/
theorem extend_one [One γ] (f : α -> β) : Function.extend f (1 : α -> γ) (1 : β -> γ) = 1 :=
  funext fun _ => by apply ite_self

@[to_additive]
/--
theorem `extend_mul` / 定理 `extend_mul`

English:
theorem extend_mul
  given: [Mul γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ)
  proof: by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

@[to_additive]

中文:
定理 extend_mul
  条件: [乘法 γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ)
  证明: by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

@[to_additive]

Depends on / 依赖: Function, Function.extend_def, classical, extend_def
-/
theorem extend_mul [Mul γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ) :
    Function.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂ e₂ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

@[to_additive]
/--
theorem `extend_inv` / 定理 `extend_inv`

English:
theorem extend_inv
  given: [Inv γ] (f : α -> β) (g : α -> γ) (e : β -> γ)
  proof: by
  classical
  funext x
  simp [Function.extend_def, apply_dite Inv.inv]

@[to_additive]

中文:
定理 extend_inv
  条件: [取逆 γ] (f : α -> β) (g : α -> γ) (e : β -> γ)
  证明: by
  classical
  funext x
  simp [Function.extend_def, apply_dite Inv.inv]

@[to_additive]

Depends on / 依赖: Function, Function.extend_def, Inv.inv, apply_dite, classical, extend_def
-/
theorem extend_inv [Inv γ] (f : α -> β) (g : α -> γ) (e : β -> γ) :
    Function.extend f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite Inv.inv]

@[to_additive]
/--
theorem `extend_div` / 定理 `extend_div`

English:
theorem extend_div
  given: [Div γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ)
  proof: by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

中文:
定理 extend_div
  条件: [除法 γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ)
  证明: by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

Depends on / 依赖: Function, Function.extend_def, classical, extend_def
-/
theorem extend_div [Div γ] (f : α -> β) (g₁ g₂ : α -> γ) (e₁ e₂ : β -> γ) :
    Function.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂ e₂ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]

end Extend

/--
lemma `comp_eq_const_iff` / 引理 `comp_eq_const_iff`

English:
lemma comp_eq_const_iff
  given: (b : β) (f : α -> β) {g : β -> γ} (hg : Injective g)
  proof: hg.comp_left.eq_iff' rfl

@[to_additive]

中文:
引理 comp_eq_const_iff
  条件: (b : β) (f : α -> β) {g : β -> γ} (hg : 单射 g)
  证明: hg.comp_left.eq_iff' rfl

@[to_additive]

Depends on / 依赖: comp_left, eq_iff, hg.comp_left.eq_iff
-/
lemma comp_eq_const_iff (b : β) (f : α -> β) {g : β -> γ} (hg : Injective g) :
    g ∘ f = Function.const _ (g b) ↔ f = Function.const _ b :=
  hg.comp_left.eq_iff' rfl

@[to_additive]
/--
lemma `comp_eq_one_iff` / 引理 `comp_eq_one_iff`

English:
lemma comp_eq_one_iff
  given: [One β] [One γ] (f : α -> β) {g : β -> γ} (hg : Injective g) (hg0 : g 1 = 1)
  proof: by
  simpa [hg0, const_one] using comp_eq_const_iff 1 f hg

@[to_additive]

中文:
引理 comp_eq_one_iff
  条件: [幺 β] [幺 γ] (f : α -> β) {g : β -> γ} (hg : 单射 g) (hg0 : g 1 = 1)
  证明: by
  simpa [hg0, const_one] using comp_eq_const_iff 1 f hg

@[to_additive]

Depends on / 依赖: comp_eq_const_iff, const_one
-/
lemma comp_eq_one_iff [One β] [One γ] (f : α -> β) {g : β -> γ} (hg : Injective g) (hg0 : g 1 = 1) :
    g ∘ f = 1 ↔ f = 1 := by
  simpa [hg0, const_one] using comp_eq_const_iff 1 f hg

@[to_additive]
/--
lemma `comp_ne_one_iff` / 引理 `comp_ne_one_iff`

English:
lemma comp_ne_one_iff
  given: [One β] [One γ] (f : α -> β) {g : β -> γ} (hg : Injective g) (hg0 : g 1 = 1)
  proof: (comp_eq_one_iff f hg hg0).ne

中文:
引理 comp_ne_one_iff
  条件: [幺 β] [幺 γ] (f : α -> β) {g : β -> γ} (hg : 单射 g) (hg0 : g 1 = 1)
  证明: (comp_eq_one_iff f hg hg0).ne

Depends on / 依赖: comp_eq_one_iff
-/
lemma comp_ne_one_iff [One β] [One γ] (f : α -> β) {g : β -> γ} (hg : Injective g) (hg0 : g 1 = 1) :
    g ∘ f != 1 ↔ f != 1 :=
  (comp_eq_one_iff f hg hg0).ne

end Function

/-- If the one function is surjective, the codomain is trivial. -/
@[to_additive (attr := instance_reducible)
  /-- If the zero function is surjective, the codomain is trivial. -/]
/--
Definition of `uniqueOfSurjectiveOne` / `uniqueOfSurjectiveOne` 的定义

English:
definition uniqueOfSurjectiveOne
  signature: (α : Type*) {β : Type*} [One β] (h : Function.Surjective (1 : α -> β))
  body: h.uniqueOfSurjectiveConst α (1 : β)

@[to_additive]

中文:
定义 uniqueOfSurjectiveOne
  签名: (α : 类型) {β : 类型} [幺 β] (h : 函数.满射 (1 : α -> β))
  定义体: h.uniqueOfSurjectiveConst α (1 : β)

@[to_additive]

Depends on / 依赖: h.uniqueOfSurjectiveConst, uniqueOfSurjectiveConst
-/
def uniqueOfSurjectiveOne (α : Type*) {β : Type*} [One β] (h : Function.Surjective (1 : α -> β)) :
    Unique β :=
  h.uniqueOfSurjectiveConst α (1 : β)

@[to_additive]
/--
theorem `Subsingleton.pi_mulSingle_eq` / 定理 `Subsingleton.pi_mulSingle_eq`

English:
theorem Subsingleton.pi_mulSingle_eq
  statement: {α : Type*} [DecidableEq I] [Subsingleton I] [One α]
  proof: funext fun j => by rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]

中文:
定理 子单例.pi_mulSingle_eq
  结论: {α : 类型} [DecidableEq I] [子单例 I] [幺 α]
  证明: funext fun j => by rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]

Depends on / 依赖: Pi.mulSingle_eq_same, Subsingleton, Subsingleton.elim, mulSingle_eq_same
-/
theorem Subsingleton.pi_mulSingle_eq {α : Type*} [DecidableEq I] [Subsingleton I] [One α]
    (i : I) (x : α) : Pi.mulSingle i x = fun _ => x :=
  funext fun j => by rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]

namespace Sum

variable (a a' : α -> γ) (b b' : β -> γ)

@[to_additive (attr := simp)]
/--
theorem `elim_one_one` / 定理 `elim_one_one`

English:
theorem elim_one_one
  given: [One γ]
  statement: Sum.elim (1 : α -> γ) (1 : β -> γ) = 1
  proof: Sum.elim_const_const 1

@[to_additive (attr := simp)]

中文:
定理 elim_one_one
  条件: [幺 γ]
  结论: 和.elim (1 : α -> γ) (1 : β -> γ) = 1
  证明: Sum.elim_const_const 1

@[to_additive (attr := simp)]

Depends on / 依赖: Sum.elim_const_const, elim_const_const
-/
theorem elim_one_one [One γ] : Sum.elim (1 : α -> γ) (1 : β -> γ) = 1 :=
  Sum.elim_const_const 1

@[to_additive (attr := simp)]
/--
theorem `elim_mulSingle_one` / 定理 `elim_mulSingle_one`

English:
theorem elim_mulSingle_one
  given: [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ)
  proof: by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]

@[to_additive (attr := simp)]

中文:
定理 elim_mulSingle_one
  条件: [DecidableEq α] [DecidableEq β] [幺 γ] (i : α) (c : γ)
  证明: by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.mulSingle, Sum.elim_update_left, elim_one_one, elim_update_left, mulSingle
-/
theorem elim_mulSingle_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ) :
    Sum.elim (Pi.mulSingle i c) (1 : β -> γ) = Pi.mulSingle (Sum.inl i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]

@[to_additive (attr := simp)]
/--
theorem `elim_one_mulSingle` / 定理 `elim_one_mulSingle`

English:
theorem elim_one_mulSingle
  given: [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ)
  proof: by
  simp only [Pi.mulSingle, Sum.elim_update_right, elim_one_one]

@[to_additive]

中文:
定理 elim_one_mulSingle
  条件: [DecidableEq α] [DecidableEq β] [幺 γ] (i : β) (c : γ)
  证明: by
  simp only [Pi.mulSingle, Sum.elim_update_right, elim_one_one]

@[to_additive]

Depends on / 依赖: Pi.mulSingle, Sum.elim_update_right, elim_one_one, elim_update_right, mulSingle, mul_mem_mul
-/
theorem elim_one_mulSingle [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ) :
    Sum.elim (1 : α -> γ) (Pi.mulSingle i c) = Pi.mulSingle (Sum.inr i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_right, elim_one_one]

@[to_additive]
/--
theorem `elim_inv_inv` / 定理 `elim_inv_inv`

English:
theorem elim_inv_inv
  given: [Inv γ]
  statement: Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹
  proof: (Sum.comp_elim Inv.inv a b).symm

@[to_additive]

中文:
定理 elim_inv_inv
  条件: [取逆 γ]
  结论: 和.elim a⁻¹ b⁻¹ = (和.elim a b)⁻¹
  证明: (Sum.comp_elim Inv.inv a b).symm

@[to_additive]

Depends on / 依赖: Inv.inv, Sum.comp_elim, comp_elim, hs.nonempty, ht.mul_left, mul_left, nonempty
-/
theorem elim_inv_inv [Inv γ] : Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹ :=
  (Sum.comp_elim Inv.inv a b).symm

@[to_additive]
/--
theorem `elim_mul_mul` / 定理 `elim_mul_mul`

English:
theorem elim_mul_mul
  given: [Mul γ]
  statement: Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.elim a' b'
  proof: by
  ext x
  cases x <;> rfl

@[to_additive]

中文:
定理 elim_mul_mul
  条件: [乘法 γ]
  结论: 和.elim (a * a') (b * b') = 和.elim a b * 和.elim a' b'
  证明: by
  ext x
  cases x <;> rfl

@[to_additive]

Depends on / 依赖: mul_mem_mul
-/
theorem elim_mul_mul [Mul γ] : Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.elim a' b' := by
  ext x
  cases x <;> rfl

@[to_additive]
/--
theorem `elim_div_div` / 定理 `elim_div_div`

English:
theorem elim_div_div
  given: [Div γ]
  statement: Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.elim a' b'
  proof: by
  ext x
  cases x <;> rfl

中文:
定理 elim_div_div
  条件: [除法 γ]
  结论: 和.elim (a / a') (b / b') = 和.elim a b / 和.elim a' b'
  证明: by
  ext x
  cases x <;> rfl
-/
theorem elim_div_div [Div γ] : Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.elim a' b' := by
  ext x
  cases x <;> rfl

end Sum
