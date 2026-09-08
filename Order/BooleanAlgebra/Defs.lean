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

/-- A generalized Boolean algebra is a distributive lattice with `⊥` and a relative complement
operation `\` (called `sdiff`, after "set difference") satisfying `(a ⊓ b) ⊔ (a \ b) = a` and
`(a ⊓ b) ⊓ (a \ b) = ⊥`, i.e. `a \ b` is the complement of `b` in `a`.

This is a generalization of Boolean algebras which applies to `Finset α` for arbitrary
(not-necessarily-`Fintype`) `α`. -/
/-
**GeneralizedBooleanAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generalized Boolean algebra is a distributive lattice with `⊥` and a relative 
complement
operation `\` (called `sdiff`, after "set difference") satisfying `(a ⊓ b) ⊔ (a 
\ b) = a` and
`(a ⊓ b) ⊓ (a \ b) = ⊥`, i.e. `a \ b` is the complement of `b` in `a`.

This is a generalization of Boolean algebras which applies to `Finset α` for arb
itrary
(not-necessarily-`Fintype`) `α`.
-/
class GeneralizedBooleanAlgebra (α : Type u) extends DistribLattice α, SDiff α, Bot α where
  /-- For any `a`, `b`, `(a ⊓ b) ⊔ (a / b) = a` -/
  sup_inf_sdiff : ∀ a b : α, a ⊓ b ⊔ a \ b = a
  /-- For any `a`, `b`, `(a ⊓ b) ⊓ (a / b) = ⊥` -/
  inf_inf_sdiff : ∀ a b : α, a ⊓ b ⊓ a \ b = ⊥

/-!
### Boolean algebras
-/


/-- A Boolean algebra is a bounded distributive lattice with a complement operator `ᶜ` such that
`x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`. For convenience, it must also provide a set difference operation `\`
and a Heyting implication `⇨` satisfying `x \ y = x ⊓ yᶜ` and `x ⇨ y = y ⊔ xᶜ`.

This is a generalization of (classical) logic of propositions, or the powerset lattice.

Since `BoundedOrder`, `OrderBot`, and `OrderTop` are mixins that require `LE`
to be present at define-time, the `extends` mechanism does not work with them.
Instead, we extend using the underlying `Bot` and `Top` data typeclasses, and replicate the
order axioms of those classes here. A "forgetful" instance back to `BoundedOrder` is provided.
-/
/-
**BooleanAlgebra** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：BooleanAlgebra (α : Type u) extends DistribLattice α, Compl α, SDiff α, HI
mp α, Top α, Bot α where /-- The infimum of `x` and `xᶜ` is at most `⊥` -/ inf_c
ompl_le_bot : forall x : α, x ⊓ xᶜ <= ⊥ /-- The supremum of `x` and `xᶜ` is at l
east `⊤` -/ top_le_sup_compl : forall x : α, ⊤ <= x ⊔ xᶜ /-- `⊤` is the greatest
 element -/ le_top : forall a : α, a <= ⊤ /-- `⊥` is the least element -/ bot_le
 : forall a : α, ⊥ <= a /-- `x \ y` is equal to `x ⊓ yᶜ` -/ sdiff
参数：α : Type u。
继承自：DistribLattice α, Compl α, SDiff α, HImp α, Top α, Bot α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Boolean algebra is a bounded distributive lattice with a complement operator `
ᶜ` such that
`x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`. For convenience, it must also provide a set diffe
rence operation `\`
and a Heyting implication `⇨` satisfying `x \ y = x ⊓ yᶜ` and `x ⇨ y = y ⊔ xᶜ`.

This is a generalization of (classical) logic of propositions, or the powerset l
attice.

Since `BoundedOrder`, `OrderBot`, and `OrderTop` are mixins that require `LE`
to be present at define-time, the `extends` mechanism does not work with them.
Instead, we extend using the underlying `Bot` and `Top` data typeclasses, and re
plicate the
order axioms of those classes here. A "forgetful" instance back to `BoundedOrder
` is provided.
-/
class BooleanAlgebra (α : Type u) extends
    DistribLattice α, Compl α, SDiff α, HImp α, Top α, Bot α where
  /-- The infimum of `x` and `xᶜ` is at most `⊥` -/
  inf_compl_le_bot : ∀ x : α, x ⊓ xᶜ ≤ ⊥
  /-- The supremum of `x` and `xᶜ` is at least `⊤` -/
  top_le_sup_compl : ∀ x : α, ⊤ ≤ x ⊔ xᶜ
  /-- `⊤` is the greatest element -/
  le_top : ∀ a : α, a ≤ ⊤
  /-- `⊥` is the least element -/
  bot_le : ∀ a : α, ⊥ ≤ a
  /-- `x \ y` is equal to `x ⊓ yᶜ` -/
  sdiff := fun x y => x ⊓ yᶜ
  /-- `x ⇨ y` is equal to `y ⊔ xᶜ` -/
  himp := fun x y => y ⊔ xᶜ
  /-- `x \ y` is equal to `x ⊓ yᶜ` -/
  sdiff_eq : ∀ x y : α, x \ y = x ⊓ yᶜ := by aesop
  /-- `x ⇨ y` is equal to `y ⊔ xᶜ` -/
  himp_eq : ∀ x y : α, x ⇨ y = y ⊔ xᶜ := by aesop

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BooleanAlgebra.toBoundedOrder [h : BooleanAlgebra α] : BoundedOrder α :=
  { h with }
/-
**Prop.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prop.instBooleanAlgebra : BooleanAlgebra Prop where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribLattice.le_sup_inf`：∀ {α : Type u_1} [self : DistribLattice α] (x
 y z : α), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
-/
instance Prop.instBooleanAlgebra : BooleanAlgebra Prop where
  __ := Prop.instHeytingAlgebra
  __ := GeneralizedHeytingAlgebra.toDistribLattice
  compl := Not
  himp_eq _ _ := propext imp_iff_or_not
  inf_compl_le_bot _ H := H.2 H.1
  top_le_sup_compl p _ := Classical.em p
/-
**Bool.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.instBooleanAlgebra : BooleanAlgebra Bool where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bool.instBooleanAlgebra : BooleanAlgebra Bool where
  __ := instBoundedOrder
  compl := not
  inf_compl_le_bot a := a.and_not_self.le
  top_le_sup_compl a := a.or_not_self.ge
/-
**Bool.sup_eq_bor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.sup_eq_bor : (· ⊔ ·) = or
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.sup_eq_bor : (· ⊔ ·) = or := by dsimp
/-
**Bool.inf_eq_band** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.inf_eq_band : (· ⊓ ·) = and
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.inf_eq_band : (· ⊓ ·) = and := by dsimp

@[simp]
/-
**Bool.compl_eq_bnot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bool.compl_eq_bnot : Compl.compl = not
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bool.compl_eq_bnot : Compl.compl = not :=
  rfl
/-
**PUnit.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PUnit.instBooleanAlgebra : BooleanAlgebra PUnit where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
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
/-
**DistribLattice.booleanAlgebraOfComplemented** 是 Mathlib 中的一个定义，位于命名空间 `Distrib
Lattice`。
形式化陈述：booleanAlgebraOfComplemented [BoundedOrder α] [ComplementedLattice α] : Bo
oleanAlgebra α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def booleanAlgebraOfComplemented [BoundedOrder α] [ComplementedLattice α] : BooleanAlgebra α where
  __ := ((inferInstance : BoundedOrder α))
  compl a := Classical.choose <| exists_isCompl a
  inf_compl_le_bot a := (Classical.choose_spec (exists_isCompl a)).disjoint.le_bot
  top_le_sup_compl a := (Classical.choose_spec (exists_isCompl a)).codisjoint.top_le

end DistribLattice

