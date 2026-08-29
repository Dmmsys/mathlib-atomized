/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
module

public import Aesop
public import Mathlib.Order.Heyting.Basic

/-!
# (Generalized) Boolean algebras

This file sets up the theory of (generalized) Boolean algebras.

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

Generalized Boolean algebras may be less familiar, but they are essentially Boolean algebras which
do not necessarily have a top element (`⊤`) (and hence not all elements may have complements). One
example in mathlib is `Finset α`, the type of all finite subsets of an arbitrary
(not-necessarily-finite) type `α`.

`GeneralizedBooleanAlgebra α` is defined to be a distributive lattice with bottom (`⊥`) admitting
a *relative* complement operator, written using "set difference" notation as `x \ y` (`sdiff x y`).
For convenience, the `BooleanAlgebra` type class is defined to extend `GeneralizedBooleanAlgebra`
so that it is also bundled with a `\` operator.

(A terminological point: `x \ y` is the complement of `y` relative to the interval `[⊥, x]`. We do
not yet have relative complements for arbitrary intervals, as we do not even have lattice
intervals.)

## Main declarations

* `GeneralizedBooleanAlgebra`: a type class for generalized Boolean algebras
* `BooleanAlgebra`: a type class for Boolean algebras.
* `Prop.booleanAlgebra`: the Boolean algebra instance on `Prop`

## Implementation notes

The `sup_inf_sdiff` and `inf_inf_sdiff` axioms for the relative complement operator in
`GeneralizedBooleanAlgebra` are taken from
[Wikipedia](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations).

[Stone's paper introducing generalized Boolean algebras][Stone1935] does not define a relative
complement operator `a \ b` for all `a`, `b`. Instead, the postulates there amount to an assumption
that for all `a, b : α` where `a ≤ b`, the equations `x ⊔ a = b` and `x ⊓ a = ⊥` have a solution
`x`. `Disjoint.sdiff_unique` proves that this `x` is in fact `b \ a`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl
-/

@[expose] public section

assert_not_exists RelIso

open Function OrderDual

universe u v

variable {α : Type u} {β : Type*} {x y z : α}

/-!
### Generalized Boolean algebras
-/

/--
Definition of `GeneralizedBooleanAlgebra` / `GeneralizedBooleanAlgebra` 的定义

English:
class GeneralizedBooleanAlgebra
  parameters: (α : Type u)
  extends: DistribLattice α, SDiff α, Bot α
  axioms and operations (2):
    - sup_inf_sdiff : forall a b : α, a ⊓ b ⊔ a \ b = a
    - inf_inf_sdiff : forall a b : α, a ⊓ b ⊓ a \ b = ⊥

中文:
类 GeneralizedBooleanAlgebra
  参数: (α : 类型u)
  继承: DistribLattice α, SDiff α, Bot α
  公理与运算 (2 个):
    - sup_inf_sdiff : 对任意 a b : α, a ⊓ b ⊔ a \ b = a
    - inf_inf_sdiff : 对任意 a b : α, a ⊓ b ⊓ a \ b = ⊥
-/
class GeneralizedBooleanAlgebra (α : Type u) extends DistribLattice α, SDiff α, Bot α where
  /-- For any `a`, `b`, `(a ⊓ b) ⊔ (a / b) = a` -/
  sup_inf_sdiff : forall a b : α, a ⊓ b ⊔ a \ b = a
  /-- For any `a`, `b`, `(a ⊓ b) ⊓ (a / b) = ⊥` -/
  inf_inf_sdiff : forall a b : α, a ⊓ b ⊓ a \ b = ⊥

/-!
### Boolean algebras
-/


/--
Definition of `BooleanAlgebra` / `BooleanAlgebra` 的定义

English:
class BooleanAlgebra
  parameters: (α : Type u)
  axioms and operations (8):
    - inf_compl_le_bot : forall x : α, x ⊓ xᶜ <= ⊥
    - top_le_sup_compl : forall x : α, ⊤ <= x ⊔ xᶜ
    - le_top : forall a : α, a <= ⊤
    - bot_le : forall a : α, ⊥ <= a
    - sdiff : = fun x y => x ⊓ yᶜ
    - himp : = fun x y => y ⊔ xᶜ
    - sdiff_eq : forall x y : α, x \ y = x ⊓ yᶜ  [default: by aesop]
    - himp_eq : forall x y : α, x ⇨ y = y ⊔ xᶜ  [default: by aesop]

中文:
类 BooleanAlgebra
  参数: (α : 类型u)
  公理与运算 (8 个):
    - inf_compl_le_bot : 对任意 x : α, x ⊓ xᶜ <= ⊥
    - top_le_sup_compl : 对任意 x : α, ⊤ <= x ⊔ xᶜ
    - le_top : 对任意 a : α, a <= ⊤
    - bot_le : 对任意 a : α, ⊥ <= a
    - sdiff : = fun x y => x ⊓ yᶜ
    - himp : = fun x y => y ⊔ xᶜ
    - sdiff_eq : 对任意 x y : α, x \ y = x ⊓ yᶜ  [默认: by aesop]
    - himp_eq : 对任意 x y : α, x ⇨ y = y ⊔ xᶜ  [默认: by aesop]
-/
class BooleanAlgebra (α : Type u) extends
    DistribLattice α, Compl α, SDiff α, HImp α, Top α, Bot α where
  /-- The infimum of `x` and `xᶜ` is at most `⊥` -/
  inf_compl_le_bot : forall x : α, x ⊓ xᶜ <= ⊥
  /-- The supremum of `x` and `xᶜ` is at least `⊤` -/
  top_le_sup_compl : forall x : α, ⊤ <= x ⊔ xᶜ
  /-- `⊤` is the greatest element -/
  le_top : forall a : α, a <= ⊤
  /-- `⊥` is the least element -/
  bot_le : forall a : α, ⊥ <= a
  /-- `x \ y` is equal to `x ⊓ yᶜ` -/
  sdiff := fun x y => x ⊓ yᶜ
  /-- `x ⇨ y` is equal to `y ⊔ xᶜ` -/
  himp := fun x y => y ⊔ xᶜ
  /-- `x \ y` is equal to `x ⊓ yᶜ` -/
  sdiff_eq : forall x y : α, x \ y = x ⊓ yᶜ := by aesop
  /-- `x ⇨ y` is equal to `y ⊔ xᶜ` -/
  himp_eq : forall x y : α, x ⇨ y = y ⊔ xᶜ := by aesop

-- see Note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toBoundedOrder [h : BooleanAlgebra α] : BoundedOrder α :=
  { h with }

/--
Instance `Prop.instBooleanAlgebra` / 实例 `Prop.instBooleanAlgebra`

English:
instance Prop.instBooleanAlgebra
  signature: : BooleanAlgebra Prop where
  body: Prop.instHeytingAlgebra
  __ := GeneralizedHeytingAlgebra.toDistribLattice
  compl := Not
  himp_eq _ _ := propext imp_iff_or_not
  inf_compl_le_bot _ H := H.2 H.1
  top_le_sup_compl p _ := Classical.em p

中文:
实例 Prop.instBooleanAlgebra
  签名: : 布尔eanAlgebra 命题 where
  定义体: Prop.instHeytingAlgebra
  __ := GeneralizedHeytingAlgebra.toDistribLattice
  compl := Not
  himp_eq _ _ := propext imp_iff_or_not
  inf_compl_le_bot _ H := H.2 H.1
  top_le_sup_compl p _ := Classical.em p

Depends on / 依赖: Prop.instHeytingAlgebra, instHeytingAlgebra
-/
instance Prop.instBooleanAlgebra : BooleanAlgebra Prop where
  __ := Prop.instHeytingAlgebra
  __ := GeneralizedHeytingAlgebra.toDistribLattice
  compl := Not
  himp_eq _ _ := propext imp_iff_or_not
  inf_compl_le_bot _ H := H.2 H.1
  top_le_sup_compl p _ := Classical.em p

/--
Instance `Bool.instBooleanAlgebra` / 实例 `Bool.instBooleanAlgebra`

English:
instance Bool.instBooleanAlgebra
  signature: : BooleanAlgebra Bool where
  body: instBoundedOrder
  compl := not
  inf_compl_le_bot a := a.and_not_self.le
  top_le_sup_compl a := a.or_not_self.ge

中文:
实例 Bool.instBooleanAlgebra
  签名: : 布尔eanAlgebra 布尔 where
  定义体: instBoundedOrder
  compl := not
  inf_compl_le_bot a := a.and_not_self.le
  top_le_sup_compl a := a.or_not_self.ge

Depends on / 依赖: instBoundedOrder
-/
instance Bool.instBooleanAlgebra : BooleanAlgebra Bool where
  __ := instBoundedOrder
  compl := not
  inf_compl_le_bot a := a.and_not_self.le
  top_le_sup_compl a := a.or_not_self.ge

/--
theorem `Bool.sup_eq_bor` / 定理 `Bool.sup_eq_bor`

English:
theorem Bool.sup_eq_bor
  statement: (· ⊔ ·) = or
  proof: by dsimp

中文:
定理 Bool.sup_eq_bor
  结论: (· ⊔ ·) = or
  证明: by dsimp
-/
theorem Bool.sup_eq_bor : (· ⊔ ·) = or := by dsimp

/--
theorem `Bool.inf_eq_band` / 定理 `Bool.inf_eq_band`

English:
theorem Bool.inf_eq_band
  statement: (· ⊓ ·) = and
  proof: by dsimp

@[simp]

中文:
定理 Bool.inf_eq_band
  结论: (· ⊓ ·) = and
  证明: by dsimp

@[simp]
-/
theorem Bool.inf_eq_band : (· ⊓ ·) = and := by dsimp

@[simp]
/--
theorem `Bool.compl_eq_bnot` / 定理 `Bool.compl_eq_bnot`

English:
theorem Bool.compl_eq_bnot
  statement: Compl.compl = not
  proof: rfl

中文:
定理 Bool.compl_eq_bnot
  结论: Compl.compl = not
  证明: rfl
-/
theorem Bool.compl_eq_bnot : Compl.compl = not :=
  rfl

/--
Instance `PUnit.instBooleanAlgebra` / 实例 `PUnit.instBooleanAlgebra`

English:
instance PUnit.instBooleanAlgebra
  signature: : BooleanAlgebra PUnit where
  body: PUnit.instBiheytingAlgebra
  le_sup_inf := by simp
  inf_compl_le_bot _ := trivial
  top_le_sup_compl _ := trivial

中文:
实例 PUnit.instBooleanAlgebra
  签名: : 布尔eanAlgebra PUnit where
  定义体: PUnit.instBiheytingAlgebra
  le_sup_inf := by simp
  inf_compl_le_bot _ := trivial
  top_le_sup_compl _ := trivial

Depends on / 依赖: PUnit.instBiheytingAlgebra, instBiheytingAlgebra
-/
instance PUnit.instBooleanAlgebra : BooleanAlgebra PUnit where
  __ := PUnit.instBiheytingAlgebra
  le_sup_inf := by simp
  inf_compl_le_bot _ := trivial
  top_le_sup_compl _ := trivial

namespace DistribLattice

variable (α) [DistribLattice α]

/--
An alternative constructor for Boolean algebras:
a distributive lattice that is complemented is a Boolean algebra.

This is not an instance, because it creates data using choice.
-/
@[instance_reducible]
noncomputable
/--
Definition of `booleanAlgebraOfComplemented` / `booleanAlgebraOfComplemented` 的定义

English:
definition booleanAlgebraOfComplemented
  signature: [BoundedOrder α] [ComplementedLattice α]
  body: ((inferInstance : BoundedOrder α))
compl a := Classical.choose exists_isCompl a
  inf_compl_le_bot a := (Classical.choose_spec (exists_isCompl a)).disjoint.le_bot
  top_le_sup_compl a := (Classical.choose_spec (exists_isCompl a)).codisjoint.top_le

中文:
定义 booleanAlgebraOfComplemented
  签名: [BoundedOrder α] [ComplementedLattice α]
  定义体: ((inferInstance : BoundedOrder α))
compl a := Classical.choose exists_isCompl a
  inf_compl_le_bot a := (Classical.choose_spec (exists_isCompl a)).disjoint.le_bot
  top_le_sup_compl a := (Classical.choose_spec (exists_isCompl a)).codisjoint.top_le

Depends on / 依赖: BoundedOrder
-/
def booleanAlgebraOfComplemented [BoundedOrder α] [ComplementedLattice α] : BooleanAlgebra α where
  __ := ((inferInstance : BoundedOrder α))
compl a := Classical.choose exists_isCompl a
  inf_compl_le_bot a := (Classical.choose_spec (exists_isCompl a)).disjoint.le_bot
  top_le_sup_compl a := (Classical.choose_spec (exists_isCompl a)).codisjoint.top_le

end DistribLattice
