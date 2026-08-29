/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Tactic.FastInstance

/-!
# Algebraic structures on the set of positive numbers

In this file we define various instances (`AddSemigroup`, `IsOrderedMonoid` etc) on the
type `{x : R // 0 < x}`. In each case we try to require the weakest possible typeclass
assumptions on `R` but possibly, there is a room for improvements.
-/

public section


open Function

namespace Positive

variable {M R : Type*}

section AddBasic

variable [AddMonoid M] [Preorder M] [AddLeftStrictMono M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add { x : M // 0 < x }
  body: ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Add { x : M // 0 < x }
  定义体: ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast]

Depends on / 依赖: add_pos
-/
instance : Add { x : M // 0 < x } :=
  ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : { x : M // 0 < x })
  statement: ↑(x + y) = (x + y : M)
  proof: rfl

中文:
定理 coe_add
  条件: (x y : { x : M // 0 < x })
  结论: ↑(x + y) = (x + y : M)
  证明: rfl
-/
theorem coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M) :=
  rfl

/--
Instance `addSemigroup` / 实例 `addSemigroup`

English:
instance addSemigroup
  signature: : AddSemigroup { x : M // 0 < x }
  body: fast_instance%
  Subtype.coe_injective.addSemigroup _ coe_add

中文:
实例 addSemigroup
  签名: : AddSemigroup { x : M // 0 < x }
  定义体: fast_instance%
  Subtype.coe_injective.addSemigroup _ coe_add

Depends on / 依赖: fast_instance
-/
instance addSemigroup : AddSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addSemigroup _ coe_add

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: {M : Type*} [AddCommMonoid M] [Preorder M]
  body: fast_instance%
  Subtype.coe_injective.addCommSemigroup _ coe_add

中文:
实例 addCommSemigroup
  签名: {M : 类型} [AddCommMonoid M] [Preorder M]
  定义体: fast_instance%
  Subtype.coe_injective.addCommSemigroup _ coe_add

Depends on / 依赖: fast_instance
-/
instance addCommSemigroup {M : Type*} [AddCommMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddCommSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addCommSemigroup _ coe_add

/--
Instance `addLeftCancelSemigroup` / 实例 `addLeftCancelSemigroup`

English:
instance addLeftCancelSemigroup
  signature: {M : Type*} [AddLeftCancelMonoid M] [Preorder M]
  body: fast_instance%
  Subtype.coe_injective.addLeftCancelSemigroup _ coe_add

中文:
实例 addLeftCancelSemigroup
  签名: {M : 类型} [AddLeftCancelMonoid M] [Preorder M]
  定义体: fast_instance%
  Subtype.coe_injective.addLeftCancelSemigroup _ coe_add

Depends on / 依赖: fast_instance
-/
instance addLeftCancelSemigroup {M : Type*} [AddLeftCancelMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddLeftCancelSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addLeftCancelSemigroup _ coe_add

/--
Instance `addRightCancelSemigroup` / 实例 `addRightCancelSemigroup`

English:
instance addRightCancelSemigroup
  signature: {M : Type*} [AddRightCancelMonoid M] [Preorder M]
  body: fast_instance%
  Subtype.coe_injective.addRightCancelSemigroup _ coe_add

中文:
实例 addRightCancelSemigroup
  签名: {M : 类型} [AddRightCancelMonoid M] [Preorder M]
  定义体: fast_instance%
  Subtype.coe_injective.addRightCancelSemigroup _ coe_add

Depends on / 依赖: fast_instance
-/
instance addRightCancelSemigroup {M : Type*} [AddRightCancelMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddRightCancelSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addRightCancelSemigroup _ coe_add

/--
Instance `addLeftStrictMono` / 实例 `addLeftStrictMono`

English:
instance addLeftStrictMono
  signature: : AddLeftStrictMono { x : M // 0 < x }
  body: ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 add_lt_add_right (show (y : M) < z from hyz) _⟩

中文:
实例 addLeftStrictMono
  签名: : AddLeftStrictMono { x : M // 0 < x }
  定义体: ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 add_lt_add_right (show (y : M) < z from hyz) _⟩

Depends on / 依赖: Subtype, Subtype.coe_lt_coe, add_lt_add_right, coe_lt_coe
-/
instance addLeftStrictMono : AddLeftStrictMono { x : M // 0 < x } :=
⟨fun _ y z hyz => Subtype.coe_lt_coe.1 add_lt_add_right (show (y : M) < z from hyz) _⟩

/--
Instance `addRightStrictMono` / 实例 `addRightStrictMono`

English:
instance addRightStrictMono
  signature: [AddRightStrictMono M]
  body: ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 add_lt_add_left (show (y : M) < z from hyz) _⟩

中文:
实例 addRightStrictMono
  签名: [AddRightStrictMono M]
  定义体: ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 add_lt_add_left (show (y : M) < z from hyz) _⟩

Depends on / 依赖: Subtype, Subtype.coe_lt_coe, add_lt_add_left, coe_lt_coe
-/
instance addRightStrictMono [AddRightStrictMono M] : AddRightStrictMono { x : M // 0 < x } :=
⟨fun _ y z hyz => Subtype.coe_lt_coe.1 add_lt_add_left (show (y : M) < z from hyz) _⟩

/--
Instance `addLeftReflectLT` / 实例 `addLeftReflectLT`

English:
instance addLeftReflectLT
  signature: [AddLeftReflectLT M]
  body: ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 lt_of_add_lt_add_left h⟩

中文:
实例 addLeftReflectLT
  签名: [AddLeftReflectLT M]
  定义体: ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 lt_of_add_lt_add_left h⟩

Depends on / 依赖: Subtype, Subtype.coe_lt_coe, coe_lt_coe, lt_of_add_lt_add_left
-/
instance addLeftReflectLT [AddLeftReflectLT M] : AddLeftReflectLT { x : M // 0 < x } :=
⟨fun _ _ _ h => Subtype.coe_lt_coe.1 lt_of_add_lt_add_left h⟩

/--
Instance `addRightReflectLT` / 实例 `addRightReflectLT`

English:
instance addRightReflectLT
  signature: [AddRightReflectLT M]
  body: ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 lt_of_add_lt_add_right h⟩

中文:
实例 addRightReflectLT
  签名: [AddRightReflectLT M]
  定义体: ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 lt_of_add_lt_add_right h⟩

Depends on / 依赖: Subtype, Subtype.coe_lt_coe, coe_lt_coe, lt_of_add_lt_add_right
-/
instance addRightReflectLT [AddRightReflectLT M] : AddRightReflectLT { x : M // 0 < x } :=
⟨fun _ _ _ h => Subtype.coe_lt_coe.1 lt_of_add_lt_add_right h⟩

/--
Instance `addLeftReflectLE` / 实例 `addLeftReflectLE`

English:
instance addLeftReflectLE
  signature: [AddLeftReflectLE M]
  body: Subtype.coe_le_coe.mp le_of_add_le_add_left h

中文:
实例 addLeftReflectLE
  签名: [AddLeftReflectLE M]
  定义体: Subtype.coe_le_coe.mp le_of_add_le_add_left h

Depends on / 依赖: Subtype, Subtype.coe_le_coe.mp, coe_le_coe, le_of_add_le_add_left
-/
instance addLeftReflectLE [AddLeftReflectLE M] : AddLeftReflectLE { x : M // 0 < x } where
le_of_add_le_add_left h := Subtype.coe_le_coe.mp le_of_add_le_add_left h

/--
Instance `addRightReflectLE` / 实例 `addRightReflectLE`

English:
instance addRightReflectLE
  signature: [AddRightReflectLE M]
  body: Subtype.coe_le_coe.mp le_of_add_le_add_right h

中文:
实例 addRightReflectLE
  签名: [AddRightReflectLE M]
  定义体: Subtype.coe_le_coe.mp le_of_add_le_add_right h

Depends on / 依赖: Subtype, Subtype.coe_le_coe.mp, coe_le_coe, le_of_add_le_add_right
-/
instance addRightReflectLE [AddRightReflectLE M] : AddRightReflectLE { x : M // 0 < x } where
le_of_add_le_add_right h := Subtype.coe_le_coe.mp le_of_add_le_add_right h

end AddBasic

/--
Instance `addLeftMono` / 实例 `addLeftMono`

English:
instance addLeftMono
  signature: [AddMonoid M] [PartialOrder M] [AddLeftStrictMono M]
  body: ⟨@fun _ _ _ h₁ => StrictMono.monotone (fun _ _ h => add_lt_add_right h _) h₁⟩

中文:
实例 addLeftMono
  签名: [AddMonoid M] [PartialOrder M] [AddLeftStrictMono M]
  定义体: ⟨@fun _ _ _ h₁ => StrictMono.monotone (fun _ _ h => add_lt_add_right h _) h₁⟩

Depends on / 依赖: StrictMono, StrictMono.monotone, add_lt_add_right, monotone
-/
instance addLeftMono [AddMonoid M] [PartialOrder M] [AddLeftStrictMono M] :
    AddLeftMono { x : M // 0 < x } :=
  ⟨@fun _ _ _ h₁ => StrictMono.monotone (fun _ _ h => add_lt_add_right h _) h₁⟩

section Mul

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul { x : R // 0 < x }
  body: ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp]

中文:
实例 :
  签名: Mul { x : R // 0 < x }
  定义体: ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp]

Depends on / 依赖: mul_pos
-/
instance : Mul { x : R // 0 < x } :=
  ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp]
/--
theorem `val_mul` / 定理 `val_mul`

English:
theorem val_mul
  given: (x y : { x : R // 0 < x })
  statement: ↑(x * y) = (x * y : R)
  proof: rfl

中文:
定理 val_mul
  条件: (x y : { x : R // 0 < x })
  结论: ↑(x * y) = (x * y : R)
  证明: rfl
-/
theorem val_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow { x : R // 0 < x } Nat
  body: ⟨fun x n => ⟨(x : R) ^ n, pow_pos x.2 n⟩⟩

@[simp]

中文:
实例 :
  签名: Pow { x : R // 0 < x } 自然数
  定义体: ⟨fun x n => ⟨(x : R) ^ n, pow_pos x.2 n⟩⟩

@[simp]

Depends on / 依赖: pow_pos
-/
instance : Pow { x : R // 0 < x } Nat :=
  ⟨fun x n => ⟨(x : R) ^ n, pow_pos x.2 n⟩⟩

@[simp]
/--
theorem `val_pow` / 定理 `val_pow`

English:
theorem val_pow
  given: (x : { x : R // 0 < x }) (n : Nat)
  proof: rfl

中文:
定理 val_pow
  条件: (x : { x : R // 0 < x }) (n : 自然数)
  证明: rfl
-/
theorem val_pow (x : { x : R // 0 < x }) (n : Nat) :
    ↑(x ^ n) = (x : R) ^ n :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Semigroup { x : R // 0 < x }
  body: fast_instance%
  Subtype.coe_injective.semigroup Subtype.val val_mul

中文:
实例 :
  签名: Semigroup { x : R // 0 < x }
  定义体: fast_instance%
  Subtype.coe_injective.semigroup Subtype.val val_mul

Depends on / 依赖: fast_instance
-/
instance : Semigroup { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.semigroup Subtype.val val_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Distrib { x : R // 0 < x }
  body: fast_instance%
  Subtype.coe_injective.distrib _ coe_add val_mul

中文:
实例 :
  签名: Distrib { x : R // 0 < x }
  定义体: fast_instance%
  Subtype.coe_injective.distrib _ coe_add val_mul

Depends on / 依赖: fast_instance
-/
instance : Distrib { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.distrib _ coe_add val_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One { x : R // 0 < x }
  body: ⟨⟨1, one_pos⟩⟩

@[simp]

中文:
实例 :
  签名: One { x : R // 0 < x }
  定义体: ⟨⟨1, one_pos⟩⟩

@[simp]

Depends on / 依赖: one_pos
-/
instance : One { x : R // 0 < x } :=
  ⟨⟨1, one_pos⟩⟩

@[simp]
/--
theorem `val_one` / 定理 `val_one`

English:
theorem val_one
  statement: ((1 : { x : R // 0 < x }) : R) = 1
  proof: rfl

中文:
定理 val_one
  结论: ((1 : { x : R // 0 < x }) : R) = 1
  证明: rfl
-/
theorem val_one : ((1 : { x : R // 0 < x }) : R) = 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid { x : R // 0 < x }
  body: fast_instance%
  Subtype.coe_injective.monoid _ val_one val_mul val_pow

中文:
实例 :
  签名: Monoid { x : R // 0 < x }
  定义体: fast_instance%
  Subtype.coe_injective.monoid _ val_one val_mul val_pow

Depends on / 依赖: fast_instance
-/
instance : Monoid { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.monoid _ val_one val_mul val_pow

end Mul

section mul_comm

/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: fast_instance%
  Subtype.coe_injective.commMonoid (M₂ := R) (Subtype.val) val_one val_mul val_pow

中文:
实例 commMonoid
  签名: [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: fast_instance%
  Subtype.coe_injective.commMonoid (M₂ := R) (Subtype.val) val_one val_mul val_pow

Depends on / 依赖: fast_instance
-/
instance commMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommMonoid { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.commMonoid (M₂ := R) (Subtype.val) val_one val_mul val_pow

/--
Instance `isOrderedMonoid` / 实例 `isOrderedMonoid`

English:
instance isOrderedMonoid
  signature: [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: Subtype.coe_le_coe.1 mul_le_mul_of_nonneg_right hxy c.2.le

中文:
实例 isOrderedMonoid
  签名: [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  定义体: Subtype.coe_le_coe.1 mul_le_mul_of_nonneg_right hxy c.2.le

Depends on / 依赖: Subtype, Subtype.coe_le_coe, coe_le_coe, mul_le_mul_of_nonneg_right
-/
instance isOrderedMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    IsOrderedMonoid { x : R // 0 < x } where
mul_le_mul_left _ _ hxy c := Subtype.coe_le_coe.1 mul_le_mul_of_nonneg_right hxy c.2.le

/--
Instance `isOrderedCancelMonoid` / 实例 `isOrderedCancelMonoid`

English:
instance isOrderedCancelMonoid
  signature: [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
  body: (mul_le_mul_iff_right₀ a.2).1

中文:
实例 isOrderedCancelMonoid
  签名: [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
  定义体: (mul_le_mul_iff_right₀ a.2).1
-/
instance isOrderedCancelMonoid [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    IsOrderedCancelMonoid { x : R // 0 < x } where
  le_of_mul_le_mul_left a _ _ := (mul_le_mul_iff_right₀ a.2).1

end mul_comm

end Positive
