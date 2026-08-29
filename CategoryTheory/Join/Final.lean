/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# (Co)Finality of the inclusions in joins of categories

This file records the fact that `inclLeft C D : C ⥤ C ⋆ D` is initial if `C` is connected.
Dually, `inclRight : C ⥤ C ⋆ D` is final if `D` is connected.

-/

@[expose] public section

namespace CategoryTheory.Join

variable (C D : Type*) [Category* C] [Category* D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `costructuredArrowEquiv` / `costructuredArrowEquiv` 的定义

English:
definition costructuredArrowEquiv
  signature: (d : D)
  body: CostructuredArrow.proj (inclLeft C D) (right d)
  inverse :=
    { obj c := .mk (edge c d)
      map f := CostructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 costructuredArrowEquiv
  签名: (d : D)
  定义体: CostructuredArrow.proj (inclLeft C D) (right d)
  inverse :=
    { obj c := .mk (edge c d)
      map f := CostructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, inclLeft
-/
def costructuredArrowEquiv (d : D) : CostructuredArrow (inclLeft C D) (right d) ≌ C where
  functor := CostructuredArrow.proj (inclLeft C D) (right d)
  inverse :=
    { obj c := .mk (edge c d)
      map f := CostructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `structuredArrowEquiv` / `structuredArrowEquiv` 的定义

English:
definition structuredArrowEquiv
  signature: (c : C)
  body: StructuredArrow.proj (left c) (inclRight C D)
  inverse :=
    { obj d := .mk (edge c d)
      map f := StructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 structuredArrowEquiv
  签名: (c : C)
  定义体: StructuredArrow.proj (left c) (inclRight C D)
  inverse :=
    { obj d := .mk (edge c d)
      map f := StructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: StructuredArrow, StructuredArrow.proj, inclRight
-/
def structuredArrowEquiv (c : C) : StructuredArrow (left c) (inclRight C D) ≌ D where
  functor := StructuredArrow.proj (left c) (inclRight C D)
  inverse :=
    { obj d := .mk (edge c d)
      map f := StructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsConnected
  signature: C] : (inclLeft C D).Initial where
  body: match x with
    | .left _ => isConnected_of_isTerminal _ CostructuredArrow.mkIdTerminal
    | .right d => isConnected_of_equivalent (costructuredArrowEquiv C D d).symm

中文:
实例 [IsConnected
  签名: C] : (inclLeft C D).Initial where
  定义体: match x with
    | .left _ => isConnected_of_isTerminal _ CostructuredArrow.mkIdTerminal
    | .right d => isConnected_of_equivalent (costructuredArrowEquiv C D d).symm
-/
instance [IsConnected C] : (inclLeft C D).Initial where
  out x := match x with
    | .left _ => isConnected_of_isTerminal _ CostructuredArrow.mkIdTerminal
    | .right d => isConnected_of_equivalent (costructuredArrowEquiv C D d).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsConnected
  signature: D] : (inclRight C D).Final where
  body: match x with
    | .left c => isConnected_of_equivalent (structuredArrowEquiv C D c).symm
    | .right _ => isConnected_of_isInitial _ (StructuredArrow.mkIdInitial (T := inclRight C D))

中文:
实例 [IsConnected
  签名: D] : (inclRight C D).Final where
  定义体: match x with
    | .left c => isConnected_of_equivalent (structuredArrowEquiv C D c).symm
    | .right _ => isConnected_of_isInitial _ (StructuredArrow.mkIdInitial (T := inclRight C D))
-/
instance [IsConnected D] : (inclRight C D).Final where
  out x := match x with
    | .left c => isConnected_of_equivalent (structuredArrowEquiv C D c).symm
    | .right _ => isConnected_of_isInitial _ (StructuredArrow.mkIdInitial (T := inclRight C D))

end CategoryTheory.Join
