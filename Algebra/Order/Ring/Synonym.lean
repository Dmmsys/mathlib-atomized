/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Ring.Defs

/-!
# Ring structure on the order type synonyms

Transfer algebraic instances from `R` to `Rᵒᵈ` and `Lex R`.
-/

public section


variable {R : Type*}

/-! ### Order dual -/

namespace OrderDual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Distrib
  signature: R] : Distrib Rᵒᵈ
  body: inferInstanceAs Distrib R

中文:
实例 [Distrib
  签名: R] : Distrib Rᵒᵈ
  定义体: inferInstanceAs Distrib R

Depends on / 依赖: Distrib
-/
instance [Distrib R] : Distrib Rᵒᵈ := inferInstanceAs Distrib R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [Add R] [LeftDistribClass R] : LeftDistribClass Rᵒᵈ
  body: inferInstanceAs LeftDistribClass R

中文:
实例 [Mul
  签名: R] [Add R] [LeftDistribClass R] : LeftDistribClass Rᵒᵈ
  定义体: inferInstanceAs LeftDistribClass R

Depends on / 依赖: LeftDistribClass
-/
instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass Rᵒᵈ :=
inferInstanceAs LeftDistribClass R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [Add R] [RightDistribClass R] : RightDistribClass Rᵒᵈ
  body: inferInstanceAs RightDistribClass R

中文:
实例 [Mul
  签名: R] [Add R] [RightDistribClass R] : RightDistribClass Rᵒᵈ
  定义体: inferInstanceAs RightDistribClass R
-/
instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass Rᵒᵈ :=
inferInstanceAs RightDistribClass R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] : NonUnitalNonAssocSemiring Rᵒᵈ
  body: inferInstanceAs NonUnitalNonAssocSemiring R

中文:
实例 [NonUnitalNonAssocSemiring
  签名: R] : NonUnitalNonAssocSemiring Rᵒᵈ
  定义体: inferInstanceAs NonUnitalNonAssocSemiring R
-/
instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring Rᵒᵈ :=
inferInstanceAs NonUnitalNonAssocSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NatCast
  signature: R] : NatCast Rᵒᵈ
  body: inferInstanceAs NatCast R

中文:
实例 [NatCast
  签名: R] : 自然数Cast Rᵒᵈ
  定义体: inferInstanceAs NatCast R
-/
instance [NatCast R] : NatCast Rᵒᵈ := inferInstanceAs NatCast R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IntCast
  signature: R] : IntCast Rᵒᵈ
  body: inferInstanceAs IntCast R

中文:
实例 [IntCast
  签名: R] : 整数Cast Rᵒᵈ
  定义体: inferInstanceAs IntCast R
-/
instance [IntCast R] : IntCast Rᵒᵈ := inferInstanceAs IntCast R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoidWithOne
  signature: R] : AddMonoidWithOne Rᵒᵈ
  body: inferInstanceAs AddMonoidWithOne R

中文:
实例 [AddMonoidWithOne
  签名: R] : AddMonoidWithOne Rᵒᵈ
  定义体: inferInstanceAs AddMonoidWithOne R
-/
instance [AddMonoidWithOne R] : AddMonoidWithOne Rᵒᵈ := inferInstanceAs AddMonoidWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoidWithOne
  signature: R] : AddCommMonoidWithOne Rᵒᵈ
  body: inferInstanceAs AddCommMonoidWithOne R

中文:
实例 [AddCommMonoidWithOne
  签名: R] : AddCommMonoidWithOne Rᵒᵈ
  定义体: inferInstanceAs AddCommMonoidWithOne R
-/
instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵒᵈ :=
inferInstanceAs AddCommMonoidWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroupWithOne
  signature: R] : AddGroupWithOne Rᵒᵈ
  body: inferInstanceAs AddGroupWithOne R

中文:
实例 [AddGroupWithOne
  签名: R] : AddGroupWithOne Rᵒᵈ
  定义体: inferInstanceAs AddGroupWithOne R
-/
instance [AddGroupWithOne R] : AddGroupWithOne Rᵒᵈ := inferInstanceAs AddGroupWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroupWithOne
  signature: R] : AddCommGroupWithOne Rᵒᵈ
  body: inferInstanceAs AddCommGroupWithOne R

中文:
实例 [AddCommGroupWithOne
  签名: R] : AddCommGroupWithOne Rᵒᵈ
  定义体: inferInstanceAs AddCommGroupWithOne R

Depends on / 依赖: AddCommGroupWithOne
-/
instance [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵒᵈ :=
inferInstanceAs AddCommGroupWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: R] : NonUnitalSemiring Rᵒᵈ
  body: inferInstanceAs NonUnitalSemiring R

中文:
实例 [NonUnitalSemiring
  签名: R] : NonUnitalSemiring Rᵒᵈ
  定义体: inferInstanceAs NonUnitalSemiring R
-/
instance [NonUnitalSemiring R] : NonUnitalSemiring Rᵒᵈ := inferInstanceAs NonUnitalSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: R] : NonAssocSemiring Rᵒᵈ
  body: inferInstanceAs NonAssocSemiring R

中文:
实例 [NonAssocSemiring
  签名: R] : NonAssocSemiring Rᵒᵈ
  定义体: inferInstanceAs NonAssocSemiring R
-/
instance [NonAssocSemiring R] : NonAssocSemiring Rᵒᵈ := inferInstanceAs NonAssocSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] : Semiring Rᵒᵈ
  body: inferInstanceAs Semiring R

中文:
实例 [Semiring
  签名: R] : Semiring Rᵒᵈ
  定义体: inferInstanceAs Semiring R
-/
instance [Semiring R] : Semiring Rᵒᵈ := inferInstanceAs Semiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: R] : NonUnitalCommSemiring Rᵒᵈ
  body: inferInstanceAs NonUnitalCommSemiring R

中文:
实例 [NonUnitalCommSemiring
  签名: R] : NonUnitalCommSemiring Rᵒᵈ
  定义体: inferInstanceAs NonUnitalCommSemiring R

Depends on / 依赖: NonUnitalCommSemiring
-/
instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵒᵈ :=
inferInstanceAs NonUnitalCommSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] : CommSemiring Rᵒᵈ
  body: inferInstanceAs CommSemiring R

中文:
实例 [CommSemiring
  签名: R] : CommSemiring Rᵒᵈ
  定义体: inferInstanceAs CommSemiring R

Depends on / 依赖: CommSemiring
-/
instance [CommSemiring R] : CommSemiring Rᵒᵈ := inferInstanceAs CommSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [HasDistribNeg R] : HasDistribNeg Rᵒᵈ
  body: inferInstanceAs HasDistribNeg R

中文:
实例 [Mul
  签名: R] [HasDistribNeg R] : HasDistribNeg Rᵒᵈ
  定义体: inferInstanceAs HasDistribNeg R

Depends on / 依赖: HasDistribNeg
-/
instance [Mul R] [HasDistribNeg R] : HasDistribNeg Rᵒᵈ := inferInstanceAs HasDistribNeg R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] : NonUnitalNonAssocRing Rᵒᵈ
  body: inferInstanceAs NonUnitalNonAssocRing R

中文:
实例 [NonUnitalNonAssocRing
  签名: R] : NonUnitalNonAssocRing Rᵒᵈ
  定义体: inferInstanceAs NonUnitalNonAssocRing R

Depends on / 依赖: NonUnitalNonAssocRing
-/
instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵒᵈ :=
inferInstanceAs NonUnitalNonAssocRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: R] : NonUnitalRing Rᵒᵈ
  body: inferInstanceAs NonUnitalRing R

中文:
实例 [NonUnitalRing
  签名: R] : NonUnitalRing Rᵒᵈ
  定义体: inferInstanceAs NonUnitalRing R

Depends on / 依赖: NonUnitalRing
-/
instance [NonUnitalRing R] : NonUnitalRing Rᵒᵈ := inferInstanceAs NonUnitalRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: R] : NonAssocRing Rᵒᵈ
  body: inferInstanceAs NonAssocRing R

中文:
实例 [NonAssocRing
  签名: R] : NonAssocRing Rᵒᵈ
  定义体: inferInstanceAs NonAssocRing R

Depends on / 依赖: NonAssocRing
-/
instance [NonAssocRing R] : NonAssocRing Rᵒᵈ := inferInstanceAs NonAssocRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] : Ring Rᵒᵈ
  body: inferInstanceAs Ring R

中文:
实例 [Ring
  签名: R] : Ring Rᵒᵈ
  定义体: inferInstanceAs Ring R
-/
instance [Ring R] : Ring Rᵒᵈ := inferInstanceAs Ring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: R] : NonUnitalCommRing Rᵒᵈ
  body: inferInstanceAs NonUnitalCommRing R

中文:
实例 [NonUnitalCommRing
  签名: R] : NonUnitalCommRing Rᵒᵈ
  定义体: inferInstanceAs NonUnitalCommRing R

Depends on / 依赖: NonUnitalCommRing
-/
instance [NonUnitalCommRing R] : NonUnitalCommRing Rᵒᵈ := inferInstanceAs NonUnitalCommRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] : CommRing Rᵒᵈ
  body: inferInstanceAs CommRing R

中文:
实例 [CommRing
  签名: R] : CommRing Rᵒᵈ
  定义体: inferInstanceAs CommRing R

Depends on / 依赖: CommRing
-/
instance [CommRing R] : CommRing Rᵒᵈ := inferInstanceAs CommRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] [IsDomain R] : IsDomain Rᵒᵈ
  body: inferInstanceAs IsDomain R

中文:
实例 [Ring
  签名: R] [IsDomain R] : IsDomain Rᵒᵈ
  定义体: inferInstanceAs IsDomain R
-/
instance [Ring R] [IsDomain R] : IsDomain Rᵒᵈ := inferInstanceAs IsDomain R

end OrderDual

open OrderDual

@[simp]
/--
theorem `toDual_natCast` / 定理 `toDual_natCast`

English:
theorem toDual_natCast
  given: [NatCast R] (n : Nat)
  statement: toDual (n : R) = n
  proof: rfl

@[simp]

中文:
定理 toDual_natCast
  条件: [自然数Cast R] (n : 自然数)
  结论: toDual (n : R) = n
  证明: rfl

@[simp]
-/
theorem toDual_natCast [NatCast R] (n : Nat) : toDual (n : R) = n :=
  rfl

@[simp]
/--
theorem `toDual_ofNat` / 定理 `toDual_ofNat`

English:
theorem toDual_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp]

中文:
定理 toDual_ofNat
  条件: [自然数Cast R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp]
-/
theorem toDual_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    (toDual (ofNat(n) : R)) = ofNat(n) :=
  rfl

@[simp]
/--
theorem `ofDual_natCast` / 定理 `ofDual_natCast`

English:
theorem ofDual_natCast
  given: [NatCast R] (n : Nat)
  statement: (ofDual n : R) = n
  proof: rfl

@[simp]

中文:
定理 ofDual_natCast
  条件: [自然数Cast R] (n : 自然数)
  结论: (ofDual n : R) = n
  证明: rfl

@[simp]
-/
theorem ofDual_natCast [NatCast R] (n : Nat) : (ofDual n : R) = n :=
  rfl

@[simp]
/--
theorem `ofDual_ofNat` / 定理 `ofDual_ofNat`

English:
theorem ofDual_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 ofDual_ofNat
  条件: [自然数Cast R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
theorem ofDual_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    (ofDual (ofNat(n) : Rᵒᵈ)) = ofNat(n) :=
  rfl

/--
lemma `toDual_intCast` / 引理 `toDual_intCast`

English:
lemma toDual_intCast
  given: [IntCast R] (n : Int)
  statement: toDual (n : R) = n
  proof: rfl

中文:
引理 toDual_intCast
  条件: [整数Cast R] (n : 整数)
  结论: toDual (n : R) = n
  证明: rfl
-/
@[simp] lemma toDual_intCast [IntCast R] (n : Int) : toDual (n : R) = n := rfl

/--
lemma `ofDual_intCast` / 引理 `ofDual_intCast`

English:
lemma ofDual_intCast
  given: [IntCast R] (n : Int)
  statement: (ofDual n : R) = n
  proof: rfl

中文:
引理 ofDual_intCast
  条件: [整数Cast R] (n : 整数)
  结论: (ofDual n : R) = n
  证明: rfl
-/
@[simp] lemma ofDual_intCast [IntCast R] (n : Int) : (ofDual n : R) = n := rfl

/-! ### Lexicographical order -/

namespace Lex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Distrib
  signature: R] : Distrib (Lex R)
  body: inferInstanceAs Distrib R

中文:
实例 [Distrib
  签名: R] : Distrib (Lex R)
  定义体: inferInstanceAs Distrib R

Depends on / 依赖: Distrib
-/
instance [Distrib R] : Distrib (Lex R) := inferInstanceAs Distrib R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [Add R] [LeftDistribClass R] : LeftDistribClass (Lex R)
  body: inferInstanceAs LeftDistribClass R

中文:
实例 [Mul
  签名: R] [Add R] [LeftDistribClass R] : LeftDistribClass (Lex R)
  定义体: inferInstanceAs LeftDistribClass R

Depends on / 依赖: LeftDistribClass
-/
instance [Mul R] [Add R] [LeftDistribClass R] : LeftDistribClass (Lex R) :=
inferInstanceAs LeftDistribClass R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [Add R] [RightDistribClass R] : RightDistribClass (Lex R)
  body: inferInstanceAs RightDistribClass R

中文:
实例 [Mul
  签名: R] [Add R] [RightDistribClass R] : RightDistribClass (Lex R)
  定义体: inferInstanceAs RightDistribClass R

Depends on / 依赖: RightDistribClass
-/
instance [Mul R] [Add R] [RightDistribClass R] : RightDistribClass (Lex R) :=
inferInstanceAs RightDistribClass R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] : NonUnitalNonAssocSemiring (Lex R)
  body: inferInstanceAs NonUnitalNonAssocSemiring R

中文:
实例 [NonUnitalNonAssocSemiring
  签名: R] : NonUnitalNonAssocSemiring (Lex R)
  定义体: inferInstanceAs NonUnitalNonAssocSemiring R

Depends on / 依赖: NonUnitalNonAssocSemiring
-/
instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (Lex R) :=
inferInstanceAs NonUnitalNonAssocSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: R] : NonUnitalSemiring (Lex R)
  body: inferInstanceAs NonUnitalSemiring R

中文:
实例 [NonUnitalSemiring
  签名: R] : NonUnitalSemiring (Lex R)
  定义体: inferInstanceAs NonUnitalSemiring R

Depends on / 依赖: NonUnitalSemiring
-/
instance [NonUnitalSemiring R] : NonUnitalSemiring (Lex R) := inferInstanceAs NonUnitalSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NatCast
  signature: R] : NatCast (Lex R)
  body: inferInstanceAs NatCast R

中文:
实例 [NatCast
  签名: R] : 自然数Cast (Lex R)
  定义体: inferInstanceAs NatCast R

Depends on / 依赖: NatCast
-/
instance [NatCast R] : NatCast (Lex R) := inferInstanceAs NatCast R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IntCast
  signature: R] : IntCast (Lex R)
  body: inferInstanceAs IntCast R

中文:
实例 [IntCast
  签名: R] : 整数Cast (Lex R)
  定义体: inferInstanceAs IntCast R

Depends on / 依赖: IntCast
-/
instance [IntCast R] : IntCast (Lex R) := inferInstanceAs IntCast R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoidWithOne
  signature: R] : AddMonoidWithOne (Lex R)
  body: inferInstanceAs AddMonoidWithOne R

中文:
实例 [AddMonoidWithOne
  签名: R] : AddMonoidWithOne (Lex R)
  定义体: inferInstanceAs AddMonoidWithOne R

Depends on / 依赖: AddMonoidWithOne
-/
instance [AddMonoidWithOne R] : AddMonoidWithOne (Lex R) := inferInstanceAs AddMonoidWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoidWithOne
  signature: R] : AddCommMonoidWithOne (Lex R)
  body: inferInstanceAs AddCommMonoidWithOne R

中文:
实例 [AddCommMonoidWithOne
  签名: R] : AddCommMonoidWithOne (Lex R)
  定义体: inferInstanceAs AddCommMonoidWithOne R

Depends on / 依赖: AddCommMonoidWithOne
-/
instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (Lex R) :=
inferInstanceAs AddCommMonoidWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroupWithOne
  signature: R] : AddGroupWithOne (Lex R)
  body: inferInstanceAs AddGroupWithOne R

中文:
实例 [AddGroupWithOne
  签名: R] : AddGroupWithOne (Lex R)
  定义体: inferInstanceAs AddGroupWithOne R

Depends on / 依赖: AddGroupWithOne
-/
instance [AddGroupWithOne R] : AddGroupWithOne (Lex R) := inferInstanceAs AddGroupWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroupWithOne
  signature: R] : AddCommGroupWithOne (Lex R)
  body: inferInstanceAs AddCommGroupWithOne R

中文:
实例 [AddCommGroupWithOne
  签名: R] : AddCommGroupWithOne (Lex R)
  定义体: inferInstanceAs AddCommGroupWithOne R

Depends on / 依赖: AddCommGroupWithOne
-/
instance [AddCommGroupWithOne R] : AddCommGroupWithOne (Lex R) :=
inferInstanceAs AddCommGroupWithOne R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: R] : NonAssocSemiring (Lex R)
  body: inferInstanceAs NonAssocSemiring R

中文:
实例 [NonAssocSemiring
  签名: R] : NonAssocSemiring (Lex R)
  定义体: inferInstanceAs NonAssocSemiring R

Depends on / 依赖: NonAssocSemiring
-/
instance [NonAssocSemiring R] : NonAssocSemiring (Lex R) := inferInstanceAs NonAssocSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] : Semiring (Lex R)
  body: inferInstanceAs Semiring R

中文:
实例 [Semiring
  签名: R] : Semiring (Lex R)
  定义体: inferInstanceAs Semiring R

Depends on / 依赖: Semiring
-/
instance [Semiring R] : Semiring (Lex R) := inferInstanceAs Semiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: R] : NonUnitalCommSemiring (Lex R)
  body: inferInstanceAs NonUnitalCommSemiring R

中文:
实例 [NonUnitalCommSemiring
  签名: R] : NonUnitalCommSemiring (Lex R)
  定义体: inferInstanceAs NonUnitalCommSemiring R

Depends on / 依赖: NonUnitalCommSemiring
-/
instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (Lex R) :=
inferInstanceAs NonUnitalCommSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] : CommSemiring (Lex R)
  body: inferInstanceAs CommSemiring R

中文:
实例 [CommSemiring
  签名: R] : CommSemiring (Lex R)
  定义体: inferInstanceAs CommSemiring R

Depends on / 依赖: CommSemiring
-/
instance [CommSemiring R] : CommSemiring (Lex R) := inferInstanceAs CommSemiring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: R] [HasDistribNeg R] : HasDistribNeg (Lex R)
  body: inferInstanceAs HasDistribNeg R

中文:
实例 [Mul
  签名: R] [HasDistribNeg R] : HasDistribNeg (Lex R)
  定义体: inferInstanceAs HasDistribNeg R

Depends on / 依赖: HasDistribNeg
-/
instance [Mul R] [HasDistribNeg R] : HasDistribNeg (Lex R) := inferInstanceAs HasDistribNeg R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] : NonUnitalNonAssocRing (Lex R)
  body: inferInstanceAs NonUnitalNonAssocRing R

中文:
实例 [NonUnitalNonAssocRing
  签名: R] : NonUnitalNonAssocRing (Lex R)
  定义体: inferInstanceAs NonUnitalNonAssocRing R

Depends on / 依赖: NonUnitalNonAssocRing
-/
instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (Lex R) :=
inferInstanceAs NonUnitalNonAssocRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: R] : NonUnitalRing (Lex R)
  body: inferInstanceAs NonUnitalRing R

中文:
实例 [NonUnitalRing
  签名: R] : NonUnitalRing (Lex R)
  定义体: inferInstanceAs NonUnitalRing R

Depends on / 依赖: NonUnitalRing
-/
instance [NonUnitalRing R] : NonUnitalRing (Lex R) := inferInstanceAs NonUnitalRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: R] : NonAssocRing (Lex R)
  body: inferInstanceAs NonAssocRing R

中文:
实例 [NonAssocRing
  签名: R] : NonAssocRing (Lex R)
  定义体: inferInstanceAs NonAssocRing R

Depends on / 依赖: NonAssocRing
-/
instance [NonAssocRing R] : NonAssocRing (Lex R) := inferInstanceAs NonAssocRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] : Ring (Lex R)
  body: inferInstanceAs Ring R

中文:
实例 [Ring
  签名: R] : Ring (Lex R)
  定义体: inferInstanceAs Ring R
-/
instance [Ring R] : Ring (Lex R) := inferInstanceAs Ring R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: R] : NonUnitalCommRing (Lex R)
  body: inferInstanceAs NonUnitalCommRing R

中文:
实例 [NonUnitalCommRing
  签名: R] : NonUnitalCommRing (Lex R)
  定义体: inferInstanceAs NonUnitalCommRing R

Depends on / 依赖: NonUnitalCommRing
-/
instance [NonUnitalCommRing R] : NonUnitalCommRing (Lex R) := inferInstanceAs NonUnitalCommRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] : CommRing (Lex R)
  body: inferInstanceAs CommRing R

中文:
实例 [CommRing
  签名: R] : CommRing (Lex R)
  定义体: inferInstanceAs CommRing R

Depends on / 依赖: CommRing
-/
instance [CommRing R] : CommRing (Lex R) := inferInstanceAs CommRing R

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] [IsDomain R] : IsDomain (Lex R)
  body: inferInstanceAs IsDomain R

中文:
实例 [Ring
  签名: R] [IsDomain R] : IsDomain (Lex R)
  定义体: inferInstanceAs IsDomain R

Depends on / 依赖: IsDomain
-/
instance [Ring R] [IsDomain R] : IsDomain (Lex R) := inferInstanceAs IsDomain R

end Lex

@[simp]
/--
theorem `toLex_natCast` / 定理 `toLex_natCast`

English:
theorem toLex_natCast
  given: [NatCast R] (n : Nat)
  statement: toLex (n : R) = n
  proof: rfl

@[simp]

中文:
定理 toLex_natCast
  条件: [自然数Cast R] (n : 自然数)
  结论: toLex (n : R) = n
  证明: rfl

@[simp]
-/
theorem toLex_natCast [NatCast R] (n : Nat) : toLex (n : R) = n :=
  rfl

@[simp]
/--
theorem `toLex_ofNat` / 定理 `toLex_ofNat`

English:
theorem toLex_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp]

中文:
定理 toLex_ofNat
  条件: [自然数Cast R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp]
-/
theorem toLex_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    toLex (ofNat(n) : R) = OfNat.ofNat n :=
  rfl

@[simp]
/--
theorem `ofLex_natCast` / 定理 `ofLex_natCast`

English:
theorem ofLex_natCast
  given: [NatCast R] (n : Nat)
  statement: (ofLex n : R) = n
  proof: rfl

@[simp]

中文:
定理 ofLex_natCast
  条件: [自然数Cast R] (n : 自然数)
  结论: (ofLex n : R) = n
  证明: rfl

@[simp]
-/
theorem ofLex_natCast [NatCast R] (n : Nat) : (ofLex n : R) = n :=
  rfl

@[simp]
/--
theorem `ofLex_ofNat` / 定理 `ofLex_ofNat`

English:
theorem ofLex_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 ofLex_ofNat
  条件: [自然数Cast R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

Depends on / 依赖: IntCast, toLex_intCast
-/
theorem ofLex_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    ofLex (ofNat(n) : Lex R) = OfNat.ofNat n :=
  rfl
/--
lemma `toLex_intCast` / 引理 `toLex_intCast`

English:
lemma toLex_intCast
  given: [IntCast R] (n : Int)
  statement: toLex (n : R) = n
  proof: rfl

中文:
引理 toLex_intCast
  条件: [整数Cast R] (n : 整数)
  结论: toLex (n : R) = n
  证明: rfl
-/
@[simp] lemma toLex_intCast [IntCast R] (n : Int) : toLex (n : R) = n := rfl

/--
lemma `ofLex_intCast` / 引理 `ofLex_intCast`

English:
lemma ofLex_intCast
  given: [IntCast R] (n : Int)
  statement: (ofLex n : R) = n
  proof: rfl

中文:
引理 ofLex_intCast
  条件: [整数Cast R] (n : 整数)
  结论: (ofLex n : R) = n
  证明: rfl
-/
@[simp] lemma ofLex_intCast [IntCast R] (n : Int) : (ofLex n : R) = n := rfl
