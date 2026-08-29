/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Regular.Basic

/-!
# Product of regular elements

## TODO

Move to `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`?
-/

public section


variable {R : Type*} {a b : R}

section CommMonoid

variable {ι R : Type*} [CommMonoid R] {s : Finset ι} {f : ι -> R}

/--
lemma `IsLeftRegular.prod` / 引理 `IsLeftRegular.prod`

English:
lemma IsLeftRegular.prod
  given: (h : forall i in s, IsLeftRegular (f i))
  proof: s.prod_induction _ _ (@IsLeftRegular.mul R _) isRegular_one.left h

中文:
引理 IsLeftRegular.prod
  条件: (h : 对任意 i in s, IsLeftRegular (f i))
  证明: s.prod_induction _ _ (@IsLeftRegular.mul R _) isRegular_one.left h

Depends on / 依赖: IsLeftRegular, IsLeftRegular.mul, isRegular_one, isRegular_one.left, prod_induction, s.prod_induction
-/
lemma IsLeftRegular.prod (h : forall i in s, IsLeftRegular (f i)) :
    IsLeftRegular (∏ i in s, f i) :=
  s.prod_induction _ _ (@IsLeftRegular.mul R _) isRegular_one.left h

/--
lemma `IsRightRegular.prod` / 引理 `IsRightRegular.prod`

English:
lemma IsRightRegular.prod
  given: (h : forall i in s, IsRightRegular (f i))
  proof: s.prod_induction _ _ (@IsRightRegular.mul R _) isRegular_one.right h

中文:
引理 IsRightRegular.prod
  条件: (h : 对任意 i in s, IsRightRegular (f i))
  证明: s.prod_induction _ _ (@IsRightRegular.mul R _) isRegular_one.right h

Depends on / 依赖: IsRightRegular, IsRightRegular.mul, isRegular_one, isRegular_one.right, prod_induction, s.prod_induction
-/
lemma IsRightRegular.prod (h : forall i in s, IsRightRegular (f i)) :
    IsRightRegular (∏ i in s, f i) :=
  s.prod_induction _ _ (@IsRightRegular.mul R _) isRegular_one.right h

/--
lemma `IsRegular.prod` / 引理 `IsRegular.prod`

English:
lemma IsRegular.prod
  given: (h : forall i in s, IsRegular (f i))
  proof: ⟨IsLeftRegular.prod fun a ha => (h a ha).left,
   IsRightRegular.prod fun a ha => (h a ha).right⟩

中文:
引理 IsRegular.prod
  条件: (h : 对任意 i in s, IsRegular (f i))
  证明: ⟨IsLeftRegular.prod fun a ha => (h a ha).left,
   IsRightRegular.prod fun a ha => (h a ha).right⟩

Depends on / 依赖: IsLeftRegular, IsLeftRegular.prod, IsRightRegular, IsRightRegular.prod
-/
lemma IsRegular.prod (h : forall i in s, IsRegular (f i)) :
    IsRegular (∏ i in s, f i) :=
  ⟨IsLeftRegular.prod fun a ha => (h a ha).left,
   IsRightRegular.prod fun a ha => (h a ha).right⟩

end CommMonoid
