/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Algebra.Ring.Subring.Defs

/-!
# Subrings of ordered rings

We study subrings of ordered rings and prove their basic properties.

## Main definitions and results

* `Subring.orderedSubtype`: the inclusion `S → R` of a subring as an ordered ring homomorphism
* various ordered instances: a subring of an `IsOrderedRing` or an `IsStrictOrderRing` is again
  the respective kind of ordered ring.
-/

@[expose] public section

namespace Subring

variable {R S : Type*} [Ring R] [PartialOrder R] [SetLike S R] [SubringClass S R]

/--
Instance `toIsOrderedRing` / 实例 `toIsOrderedRing`

English:
instance toIsOrderedRing
  signature: [IsOrderedRing R] (s : S)
  body: Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

中文:
实例 toIsOrderedRing
  签名: [IsOrderedRing R] (s : S)
  定义体: Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

Depends on / 依赖: Function, Function.Injective.isOrderedRing, Injective, Subtype, Subtype.val, U.unop, isOrderedRing, sectionsSubmodule, toAddCommGroup, toAddSubgroup, toAddSubgroup.toAddCommGroup
-/
instance toIsOrderedRing [IsOrderedRing R] (s : S) : IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/--
Instance `toIsStrictOrderedRing` / 实例 `toIsStrictOrderedRing`

English:
instance toIsStrictOrderedRing
  signature: [IsStrictOrderedRing R] (s : S)
  body: Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

中文:
实例 toIsStrictOrderedRing
  签名: [IsStrictOrderedRing R] (s : S)
  定义体: Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

Depends on / 依赖: Function, Function.Injective.isStrictOrderedRing, Injective, Subtype, Subtype.val, U.unop, isStrictOrderedRing, module, sectionsSubmodule
-/
instance toIsStrictOrderedRing [IsStrictOrderedRing R] (s : S) : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

/--
Definition of `orderedSubtype` / `orderedSubtype` 的定义

English:
definition orderedSubtype
  signature: (s : Subring R)
  body: s.subtype
  monotone' := fun _ _ h => h

中文:
定义 orderedSubtype
  签名: (s : Subring R)
  定义体: s.subtype
  monotone' := fun _ _ h => h

Depends on / 依赖: U.unop, s.subtype, sectionsSubalgebra, subtype, toCommRing
-/
def orderedSubtype (s : Subring R) : s ->+*o R where
  __ := s.subtype
  monotone' := fun _ _ h => h

/--
lemma `orderedSubtype_coe` / 引理 `orderedSubtype_coe`

English:
lemma orderedSubtype_coe
  given: (s : Subring R)
  statement: Subring.orderedSubtype s = Subring.subtype s
  proof: rfl

中文:
引理 orderedSubtype_coe
  条件: (s : Subring R)
  结论: Subring.orderedSubtype s = Subring.subtype s
  证明: rfl

Depends on / 依赖: U.unop, algebra, sectionsSubalgebra
-/
lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring
