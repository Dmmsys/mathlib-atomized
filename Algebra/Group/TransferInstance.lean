/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.Fintype.Basic

/-!
# Transfer algebraic structures across `Equiv`s

In this file we prove lemmas of the following form: if `β` has a group structure and `α ≃ β`
then `α` has a group structure, and similarly for monoids, semigroups and so on.

### Implementation details

When adding new definitions that transfer type-classes across an equivalence, please use
`abbrev`. See note [reducible non-instances].
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

library_note «instance transfer via equivalence» /--
For many type classes, we have a definition that lets us transfer instances from one type to another
using an equivalence, such as `Equiv.mul` for `Mul`.
Constructing data instances in this way is discouraged because the resulting data is inefficient
to unfold. To somewhat mitigate this problem, in these definitions we don't write the
projections on `Equiv` in the usual way using `Equiv.symm` and `DFunLike.coe`, and instead use
`Equiv.toFun` and `Equiv.invFun` directly. As a result, unification has to do less unfolding.

Note also that when constructing data instances in this way, it usually helps to use
`fast_instance%` to get a faster instance.
-/

namespace Equiv
variable {M α β : Type*} (e : α ≃ β)

-- See note [instance transfer via equivalence]
/-- Transfer `One` across an `Equiv` -/
@[to_additive /-- Transfer `Zero` across an `Equiv` -/]
/--
Definition of `one` / `one` 的定义

English:
abbreviation one
  signature: [One β]
  body: e.invFun 1

@[to_additive]

中文:
缩写 one
  签名: [One β]
  定义体: e.invFun 1

@[to_additive]
-/
protected abbrev one [One β] : One α where one := e.invFun 1

@[to_additive]
/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  given: [One β]
  proof: e.one
    1 = e.symm 1 := rfl

中文:
引理 one_def
  条件: [One β]
  证明: e.one
    1 = e.symm 1 := rfl

Depends on / 依赖: e.one
-/
lemma one_def [One β] :
    letI := e.one
    1 = e.symm 1 := rfl

/-- Transfer `Mul` across an `Equiv` -/
@[to_additive /-- Transfer `Add` across an `Equiv` -/]
/--
Definition of `mul` / `mul` 的定义

English:
abbreviation mul
  signature: [Mul β]
  body: e.invFun (e.toFun x * e.toFun y)

@[to_additive]

中文:
缩写 mul
  签名: [Mul β]
  定义体: e.invFun (e.toFun x * e.toFun y)

@[to_additive]
-/
protected abbrev mul [Mul β] : Mul α where mul x y := e.invFun (e.toFun x * e.toFun y)

@[to_additive]
/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: [Mul β] (x y : α)
  proof: Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

中文:
引理 mul_def
  条件: [Mul β] (x y : α)
  证明: Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

Depends on / 依赖: Equiv.mul
-/
lemma mul_def [Mul β] (x y : α) :
    letI := Equiv.mul e
    x * y = e.symm (e x * e y) := rfl

/-- Transfer `Div` across an `Equiv` -/
@[to_additive /-- Transfer `Sub` across an `Equiv` -/]
/--
Definition of `div` / `div` 的定义

English:
abbreviation div
  signature: [Div β]
  body: ⟨fun x y => e.invFun (e.toFun x / e.toFun y)⟩

@[to_additive]

中文:
缩写 div
  签名: [Div β]
  定义体: ⟨fun x y => e.invFun (e.toFun x / e.toFun y)⟩

@[to_additive]
-/
protected abbrev div [Div β] : Div α :=
  ⟨fun x y => e.invFun (e.toFun x / e.toFun y)⟩

@[to_additive]
/--
lemma `div_def` / 引理 `div_def`

English:
lemma div_def
  given: [Div β] (x y : α)
  proof: Equiv.div e
    x / y = e.symm (e x / e y) := rfl

中文:
引理 div_def
  条件: [Div β] (x y : α)
  证明: Equiv.div e
    x / y = e.symm (e x / e y) := rfl

Depends on / 依赖: Equiv.div
-/
lemma div_def [Div β] (x y : α) :
    letI := Equiv.div e
    x / y = e.symm (e x / e y) := rfl

-- Porting note: this should be called `inv`,
-- but we already have an `Equiv.inv` (which perhaps should move to `Perm.inv`?)
/-- Transfer `Inv` across an `Equiv` -/
@[to_additive /-- Transfer `Neg` across an `Equiv` -/]
/--
Definition of `Inv` / `Inv` 的定义

English:
abbreviation Inv
  signature: [Inv β]
  body: e.invFun (e.toFun x)⁻¹

@[to_additive]

中文:
缩写 Inv
  签名: [Inv β]
  定义体: e.invFun (e.toFun x)⁻¹

@[to_additive]
-/
protected abbrev Inv [Inv β] : Inv α where inv x := e.invFun (e.toFun x)⁻¹

@[to_additive]
/--
lemma `inv_def` / 引理 `inv_def`

English:
lemma inv_def
  given: [Inv β] (x : α)
  proof: e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

中文:
引理 inv_def
  条件: [Inv β] (x : α)
  证明: e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

Depends on / 依赖: e.Inv
-/
lemma inv_def [Inv β] (x : α) :
    letI := e.Inv
    x⁻¹ = e.symm (e x)⁻¹ := rfl

variable (M) in
/-- Transfer `Pow` across an `Equiv` -/
@[to_additive (attr := to_additive /-- Transfer `VAdd` across an `Equiv` -/) smul
/-- Transfer `SMul` across an `Equiv` -/]
/--
Definition of `pow` / `pow` 的定义

English:
abbreviation pow
  signature: [Pow β M]
  body: e.invFun (e.toFun x ^ n)

@[to_additive (attr := to_additive) smul_def]

中文:
缩写 pow
  签名: [Pow β M]
  定义体: e.invFun (e.toFun x ^ n)

@[to_additive (attr := to_additive) smul_def]
-/
protected abbrev pow [Pow β M] : Pow α M where pow x n := e.invFun (e.toFun x ^ n)

@[to_additive (attr := to_additive) smul_def]
/--
lemma `pow_def` / 引理 `pow_def`

English:
lemma pow_def
  given: [Pow β M] (n : M) (x : α)
  proof: e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

中文:
引理 pow_def
  条件: [Pow β M] (n : M) (x : α)
  证明: e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

Depends on / 依赖: e.pow
-/
lemma pow_def [Pow β M] (n : M) (x : α) :
    letI := e.pow M
    x ^ n = e.symm (e x ^ n) := rfl

/-- An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β` where
the multiplicative structure on `α` is the one obtained by transporting a multiplicative structure
on `β` back along `e`. -/
@[to_additive /-- An equivalence `e : α ≃ β` gives an additive equivalence `α ≃+ β` where
the additive structure on `α` is the one obtained by transporting an additive structure
on `β` back along `e`. -/]
/--
Definition of `mulEquiv` / `mulEquiv` 的定义

English:
definition mulEquiv
  signature: (e : α ≃ β) [Mul β]
  body: Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        simp [mul_def] }

@[to_additive (attr := simp)]

中文:
定义 mulEquiv
  签名: (e : α ≃ β) [Mul β]
  定义体: Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        simp [mul_def] }

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.mul
-/
def mulEquiv (e : α ≃ β) [Mul β] :
    let _ := Equiv.mul e
    α ≃* β := by
  intros
  exact
    { e with
      map_mul' := fun x y => by
        simp [mul_def] }

@[to_additive (attr := simp)]
/--
lemma `mulEquiv_apply` / 引理 `mulEquiv_apply`

English:
lemma mulEquiv_apply
  given: (e : α ≃ β) [Mul β] (a : α)
  statement: (mulEquiv e) a = e a
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 mulEquiv_apply
  条件: (e : α ≃ β) [Mul β] (a : α)
  结论: (mulEquiv e) a = e a
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma mulEquiv_apply (e : α ≃ β) [Mul β] (a : α) : (mulEquiv e) a = e a := rfl

@[to_additive (attr := simp)]
/--
lemma `mulEquiv_symm_apply` / 引理 `mulEquiv_symm_apply`

English:
lemma mulEquiv_symm_apply
  given: (e : α ≃ β) [Mul β] (b : β)
  proof: Equiv.mul e
    (mulEquiv e).symm b = e.symm b := rfl

中文:
引理 mulEquiv_symm_apply
  条件: (e : α ≃ β) [Mul β] (b : β)
  证明: Equiv.mul e
    (mulEquiv e).symm b = e.symm b := rfl

Depends on / 依赖: Equiv.mul
-/
lemma mulEquiv_symm_apply (e : α ≃ β) [Mul β] (b : β) :
    letI := Equiv.mul e
    (mulEquiv e).symm b = e.symm b := rfl

/-- Transfer `Semigroup` across an `Equiv` -/
@[to_additive /-- Transfer `add_semigroup` across an `Equiv` -/]
/--
Definition of `semigroup` / `semigroup` 的定义

English:
abbreviation semigroup
  signature: [Semigroup β]
  body: by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _

中文:
缩写 semigroup
  签名: [Semigroup β]
  定义体: by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _
-/
protected abbrev semigroup [Semigroup β] : Semigroup α := by
  let mul := e.mul
  apply e.injective.semigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `CommSemigroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommSemigroup` across an `Equiv` -/]
/--
Definition of `commSemigroup` / `commSemigroup` 的定义

English:
abbreviation commSemigroup
  signature: [CommSemigroup β]
  body: by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _

中文:
缩写 commSemigroup
  签名: [CommSemigroup β]
  定义体: by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _
-/
protected abbrev commSemigroup [CommSemigroup β] : CommSemigroup α := by
  let mul := e.mul
  apply e.injective.commSemigroup _; intros; exact e.apply_symm_apply _

/-- Transfer `IsLeftCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsLeftCancelAdd` across an `Equiv` -/]
/--
lemma `isLeftCancelMul` / 引理 `isLeftCancelMul`

English:
lemma isLeftCancelMul
  given: [Mul β] [IsLeftCancelMul β]
  proof: e.mul
    IsLeftCancelMul α := by
  let := e.mul; exact e.injective.isLeftCancelMul _ fun _ _ => e.apply_symm_apply _

中文:
引理 isLeftCancelMul
  条件: [Mul β] [IsLeftCancelMul β]
  证明: e.mul
    IsLeftCancelMul α := by
  let := e.mul; exact e.injective.isLeftCancelMul _ fun _ _ => e.apply_symm_apply _
-/
protected lemma isLeftCancelMul [Mul β] [IsLeftCancelMul β] :
    letI := e.mul
    IsLeftCancelMul α := by
  let := e.mul; exact e.injective.isLeftCancelMul _ fun _ _ => e.apply_symm_apply _

/-- Transfer `IsRightCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsRightCancelAdd` across an `Equiv` -/]
/--
lemma `isRightCancelMul` / 引理 `isRightCancelMul`

English:
lemma isRightCancelMul
  given: [Mul β] [IsRightCancelMul β]
  proof: e.mul
    IsRightCancelMul α := by
  let := e.mul; exact e.injective.isRightCancelMul _ fun _ _ => e.apply_symm_apply _

中文:
引理 isRightCancelMul
  条件: [Mul β] [IsRightCancelMul β]
  证明: e.mul
    IsRightCancelMul α := by
  let := e.mul; exact e.injective.isRightCancelMul _ fun _ _ => e.apply_symm_apply _
-/
protected lemma isRightCancelMul [Mul β] [IsRightCancelMul β] :
    letI := e.mul
    IsRightCancelMul α := by
  let := e.mul; exact e.injective.isRightCancelMul _ fun _ _ => e.apply_symm_apply _

/-- Transfer `IsCancelMul` across an `Equiv` -/
@[to_additive /-- Transfer `IsCancelAdd` across an `Equiv` -/]
/--
lemma `isCancelMul` / 引理 `isCancelMul`

English:
lemma isCancelMul
  given: [Mul β] [IsCancelMul β]
  proof: e.mul
    IsCancelMul α := by
  let := e.mul; exact e.injective.isCancelMul _ fun _ _ => e.apply_symm_apply _

中文:
引理 isCancelMul
  条件: [Mul β] [IsCancelMul β]
  证明: e.mul
    IsCancelMul α := by
  let := e.mul; exact e.injective.isCancelMul _ fun _ _ => e.apply_symm_apply _
-/
protected lemma isCancelMul [Mul β] [IsCancelMul β] :
    letI := e.mul
    IsCancelMul α := by
  let := e.mul; exact e.injective.isCancelMul _ fun _ _ => e.apply_symm_apply _

/-- Transfer `MulOneClass` across an `Equiv` -/
@[to_additive /-- Transfer `AddZeroClass` across an `Equiv` -/]
/--
Definition of `mulOneClass` / `mulOneClass` 的定义

English:
abbreviation mulOneClass
  signature: [MulOneClass β]
  body: by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 mulOneClass
  签名: [MulOneClass β]
  定义体: by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev mulOneClass [MulOneClass β] : MulOneClass α := by
  let one := e.one
  let mul := e.mul
  apply e.injective.mulOneClass _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Monoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddMonoid` across an `Equiv` -/]
/--
Definition of `monoid` / `monoid` 的定义

English:
abbreviation monoid
  signature: [Monoid β]
  body: by
  let one := e.one
  let mul := e.mul
  let pow := e.pow Nat
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 monoid
  签名: [Monoid β]
  定义体: by
  let one := e.one
  let mul := e.mul
  let pow := e.pow Nat
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev monoid [Monoid β] : Monoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow Nat
  apply e.injective.monoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommMonoid` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommMonoid` across an `Equiv` -/]
/--
Definition of `commMonoid` / `commMonoid` 的定义

English:
abbreviation commMonoid
  signature: [CommMonoid β]
  body: by
  let one := e.one
  let mul := e.mul
  let pow := e.pow Nat
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 commMonoid
  签名: [CommMonoid β]
  定义体: by
  let one := e.one
  let mul := e.mul
  let pow := e.pow Nat
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev commMonoid [CommMonoid β] : CommMonoid α := by
  let one := e.one
  let mul := e.mul
  let pow := e.pow Nat
  apply e.injective.commMonoid _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Group` across an `Equiv` -/
@[to_additive /-- Transfer `AddGroup` across an `Equiv` -/]
/--
Definition of `group` / `group` 的定义

English:
abbreviation group
  signature: [Group β]
  body: by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow Nat
  let zpow := e.pow Int
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 group
  签名: [Group β]
  定义体: by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow Nat
  let zpow := e.pow Int
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev group [Group β] : Group α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow Nat
  let zpow := e.pow Int
  apply e.injective.group _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `CommGroup` across an `Equiv` -/
@[to_additive /-- Transfer `AddCommGroup` across an `Equiv` -/]
/--
Definition of `commGroup` / `commGroup` 的定义

English:
abbreviation commGroup
  signature: [CommGroup β]
  body: by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow Nat
  let zpow := e.pow Int
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 commGroup
  签名: [CommGroup β]
  定义体: by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow Nat
  let zpow := e.pow Int
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev commGroup [CommGroup β] : CommGroup α := by
  let one := e.one
  let mul := e.mul
  let inv := e.Inv
  let div := e.div
  let npow := e.pow Nat
  let zpow := e.pow Int
  apply e.injective.commGroup _ <;> intros <;> exact e.apply_symm_apply _

end Equiv

namespace Finite

/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/
@[to_additive
/-- Any finite group in universe `u` is equivalent to some finite group in universe `v`. -/]
/--
lemma `exists_type_univ_nonempty_mulEquiv.` / 引理 `exists_type_univ_nonempty_mulEquiv.`

English:
lemma exists_type_univ_nonempty_mulEquiv.{u,
  given: v} (G
  statement: Type u) [Group G] [Finite G] :
  proof: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let f : Fin n ≃ ULift (Fin n) := Equiv.ulift.symm
  let e : G ≃ ULift (Fin n) := e.trans f
  let groupH : Group (ULift (Fin n)) := e.symm.group
exact ⟨ULift (Fin n), groupH, inferInstance, ⟨MulEquiv.symm e.symm.mulEquiv⟩⟩

中文:
引理 exists_type_univ_nonempty_mulEquiv.{u,
  条件: v} (G
  结论: 类型u) [Group G] [Finite G] :
  证明: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let f : Fin n ≃ ULift (Fin n) := Equiv.ulift.symm
  let e : G ≃ ULift (Fin n) := e.trans f
  let groupH : Group (ULift (Fin n)) := e.symm.group
exact ⟨ULift (Fin n), groupH, inferInstance, ⟨MulEquiv.symm e.symm.mulEquiv⟩⟩

Depends on / 依赖: Equiv.ulift.symm, Finite, Finite.exists_equiv_fin, MulEquiv, MulEquiv.symm, e.symm.group, e.symm.mulEquiv, e.trans, exists_equiv_fin, groupH, mulEquiv
-/
lemma exists_type_univ_nonempty_mulEquiv.{u, v} (G : Type u) [Group G] [Finite G] :
    exists (G' : Type v) (_ : Group G') (_ : Fintype G'), Nonempty (G ≃* G') := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  let f : Fin n ≃ ULift (Fin n) := Equiv.ulift.symm
  let e : G ≃ ULift (Fin n) := e.trans f
  let groupH : Group (ULift (Fin n)) := e.symm.group
exact ⟨ULift (Fin n), groupH, inferInstance, ⟨MulEquiv.symm e.symm.mulEquiv⟩⟩

end Finite
