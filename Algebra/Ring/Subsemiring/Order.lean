/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FastInstance

/-!
# `Order`ed instances for `SubsemiringClass` and `Subsemiring`.
-/

@[expose] public section

namespace SubsemiringClass
variable {R S : Type*} [SetLike S R] (s : S)

/--
Instance `toIsOrderedRing` / 实例 `toIsOrderedRing`

English:
instance toIsOrderedRing
  signature: [Semiring R] [PartialOrder R] [IsOrderedRing R] [SubsemiringClass S R]
  body: Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

中文:
实例 toIsOrderedRing
  签名: [半环 R] [偏序 R] [是Ordered环 R] [子半环类 S R]
  定义体: Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedRing, Injective, Subtype, Subtype.val, isOrderedRing
-/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] [SubsemiringClass S R] :
    IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/--
Instance `toIsStrictOrderedRing` / 实例 `toIsStrictOrderedRing`

English:
instance toIsStrictOrderedRing
  signature: [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

中文:
实例 toIsStrictOrderedRing
  签名: [半环 R] [偏序 R] [是StrictOrdered环 R]
  定义体: Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

Depends on / 依赖: Function, Function.Injective.isStrictOrderedRing, Injective, Subtype, Subtype.val, isStrictOrderedRing
-/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [SubsemiringClass S R] : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end SubsemiringClass

namespace Subsemiring

variable {R : Type*}

/--
Instance `toIsOrderedRing` / 实例 `toIsOrderedRing`

English:
instance toIsOrderedRing
  signature: [Semiring R] [PartialOrder R] [IsOrderedRing R] (s : Subsemiring R)
  body: SubsemiringClass.toIsOrderedRing _

中文:
实例 toIsOrderedRing
  签名: [半环 R] [偏序 R] [是Ordered环 R] (s : 子半环 R)
  定义体: SubsemiringClass.toIsOrderedRing _

Depends on / 依赖: SubsemiringClass, SubsemiringClass.toIsOrderedRing, toIsOrderedRing
-/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] (s : Subsemiring R) :
    IsOrderedRing s :=
  SubsemiringClass.toIsOrderedRing _

/--
Instance `toIsStrictOrderedRing` / 实例 `toIsStrictOrderedRing`

English:
instance toIsStrictOrderedRing
  signature: [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  body: SubsemiringClass.toIsStrictOrderedRing _

中文:
实例 toIsStrictOrderedRing
  签名: [半环 R] [偏序 R] [是StrictOrdered环 R]
  定义体: SubsemiringClass.toIsStrictOrderedRing _

Depends on / 依赖: SubsemiringClass, SubsemiringClass.toIsStrictOrderedRing, toIsStrictOrderedRing
-/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    (s : Subsemiring R) : IsStrictOrderedRing s :=
  SubsemiringClass.toIsStrictOrderedRing _

section nonneg

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable (R) in
/-- The set of nonnegative elements in an ordered semiring, as a subsemiring. -/
@[simps]
/--
Definition of `nonneg` / `nonneg` 的定义

English:
definition nonneg
  signature: : Subsemiring R where
  body: AddSubmonoid.nonneg R
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one

中文:
定义 nonneg
  签名: : 子半环 R where
  定义体: AddSubmonoid.nonneg R
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one

Depends on / 依赖: AddSubmonoid, AddSubmonoid.nonneg, nonneg
-/
def nonneg : Subsemiring R where
  __ := AddSubmonoid.nonneg R
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one

/--
lemma `mem_nonneg` / 引理 `mem_nonneg`

English:
lemma mem_nonneg
  given: {x : R}
  statement: x in nonneg R ↔ 0 <= x
  proof: .rfl

中文:
引理 mem_nonneg
  条件: {x : R}
  结论: x in nonneg R ↔ 0 <= x
  证明: .rfl
-/
@[simp] lemma mem_nonneg {x : R} : x in nonneg R ↔ 0 <= x := .rfl

variable (R) in
@[simp]
/--
theorem `nonneg_toAddSubmonoid` / 定理 `nonneg_toAddSubmonoid`

English:
theorem nonneg_toAddSubmonoid
  statement: (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R
  proof: rfl

中文:
定理 nonneg_toAddSubmonoid
  结论: (nonneg R).toAddSubmonoid = 加法子幺半群.nonneg R
  证明: rfl
-/
theorem nonneg_toAddSubmonoid : (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R := rfl

end nonneg

end Subsemiring
