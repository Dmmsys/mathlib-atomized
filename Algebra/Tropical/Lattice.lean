/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

# Order on tropical algebraic structure

This file defines the orders induced on tropical algebraic structures by the underlying type.

## Main declarations

* `ConditionallyCompleteLattice (Tropical R)`
* `ConditionallyCompleteLinearOrder (Tropical R)`

## Implementation notes

The order induced is the definitionally equal underlying order, which makes the proofs and
constructions quicker to implement.

-/

public section


variable {R S : Type*}

open Tropical

/--
Instance `instSemilatticeInfTropical` / 实例 `instSemilatticeInfTropical`

English:
instance instSemilatticeInfTropical
  signature: [SemilatticeInf R]
  body: { Tropical.instPartialOrderTropical with
    inf := fun x y => trop (untrop x ⊓ untrop y)
    le_inf := fun _ _ _ => @SemilatticeInf.le_inf R _ _ _ _
    inf_le_left := fun _ _ => inf_le_left
    inf_le_right := fun _ _ => inf_le_right }

中文:
实例 instSemilatticeInfTropical
  签名: [SemilatticeInf R]
  定义体: { Tropical.instPartialOrderTropical with
    inf := fun x y => trop (untrop x ⊓ untrop y)
    le_inf := fun _ _ _ => @SemilatticeInf.le_inf R _ _ _ _
    inf_le_left := fun _ _ => inf_le_left
    inf_le_right := fun _ _ => inf_le_right }

Depends on / 依赖: SemilatticeInf, SemilatticeInf.le_inf, Tropical, Tropical.instPartialOrderTropical, inf_le_left, inf_le_right, instPartialOrderTropical, le_inf, untrop
-/
instance instSemilatticeInfTropical [SemilatticeInf R] : SemilatticeInf (Tropical R) :=
  { Tropical.instPartialOrderTropical with
    inf := fun x y => trop (untrop x ⊓ untrop y)
    le_inf := fun _ _ _ => @SemilatticeInf.le_inf R _ _ _ _
    inf_le_left := fun _ _ => inf_le_left
    inf_le_right := fun _ _ => inf_le_right }

/--
Instance `instSemilatticeSupTropical` / 实例 `instSemilatticeSupTropical`

English:
instance instSemilatticeSupTropical
  signature: [SemilatticeSup R]
  body: { Tropical.instPartialOrderTropical with
    sup := fun x y => trop (untrop x ⊔ untrop y)
    sup_le := fun _ _ _ => @SemilatticeSup.sup_le R _ _ _ _
    le_sup_left := fun _ _ => le_sup_left
    le_sup_right := fun _ _ => le_sup_right }

中文:
实例 instSemilatticeSupTropical
  签名: [SemilatticeSup R]
  定义体: { Tropical.instPartialOrderTropical with
    sup := fun x y => trop (untrop x ⊔ untrop y)
    sup_le := fun _ _ _ => @SemilatticeSup.sup_le R _ _ _ _
    le_sup_left := fun _ _ => le_sup_left
    le_sup_right := fun _ _ => le_sup_right }

Depends on / 依赖: SemilatticeSup, SemilatticeSup.sup_le, Tropical, Tropical.instPartialOrderTropical, instPartialOrderTropical, le_sup_left, le_sup_right, sup_le, untrop
-/
instance instSemilatticeSupTropical [SemilatticeSup R] : SemilatticeSup (Tropical R) :=
  { Tropical.instPartialOrderTropical with
    sup := fun x y => trop (untrop x ⊔ untrop y)
    sup_le := fun _ _ _ => @SemilatticeSup.sup_le R _ _ _ _
    le_sup_left := fun _ _ => le_sup_left
    le_sup_right := fun _ _ => le_sup_right }

/--
Instance `instLatticeTropical` / 实例 `instLatticeTropical`

English:
instance instLatticeTropical
  signature: [Lattice R]
  body: { instSemilatticeInfTropical, instSemilatticeSupTropical with }

中文:
实例 instLatticeTropical
  签名: [格 R]
  定义体: { instSemilatticeInfTropical, instSemilatticeSupTropical with }

Depends on / 依赖: instSemilatticeInfTropical, instSemilatticeSupTropical
-/
instance instLatticeTropical [Lattice R] : Lattice (Tropical R) :=
  { instSemilatticeInfTropical, instSemilatticeSupTropical with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SupSet
  signature: R] : SupSet (Tropical R) where sSup s
  body: trop (sSup (untrop '' s))

中文:
实例 [上确界集
  签名: R] : 上确界集 (Tropical R) where sSup s
  定义体: trop (sSup (untrop '' s))

Depends on / 依赖: untrop
-/
instance [SupSet R] : SupSet (Tropical R) where sSup s := trop (sSup (untrop '' s))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InfSet
  signature: R] : InfSet (Tropical R) where sInf s
  body: trop (sInf (untrop '' s))

中文:
实例 [下确界集
  签名: R] : 下确界集 (Tropical R) where sInf s
  定义体: trop (sInf (untrop '' s))

Depends on / 依赖: untrop
-/
instance [InfSet R] : InfSet (Tropical R) where sInf s := trop (sInf (untrop '' s))

/--
Instance `instConditionallyCompleteLatticeTropical` / 实例 `instConditionallyCompleteLatticeTropical`

English:
instance instConditionallyCompleteLatticeTropical
  signature: [ConditionallyCompleteLattice R]
  body: .of_image untrop_le_iff isLUB_csSup (hn.image _) (untrop_monotone.map_bddAbove hb)
  isGLB_csInf _ hn hb :=
.of_image untrop_le_iff isGLB_csInf (hn.image _) (untrop_monotone.map_bddBelow hb)

中文:
实例 instConditionallyCompleteLatticeTropical
  签名: [条件完备格 R]
  定义体: .of_image untrop_le_iff isLUB_csSup (hn.image _) (untrop_monotone.map_bddAbove hb)
  isGLB_csInf _ hn hb :=
.of_image untrop_le_iff isGLB_csInf (hn.image _) (untrop_monotone.map_bddBelow hb)

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, hn.image, isGLB_csInf, isLUB_csSup, map_bddAbove, map_bddBelow, of_image, restrict, untrop_le_iff, untrop_monotone, untrop_monotone.map_bddAbove, untrop_monotone.map_bddBelow
-/
instance instConditionallyCompleteLatticeTropical [ConditionallyCompleteLattice R] :
    ConditionallyCompleteLattice (Tropical R) where
  isLUB_csSup _ hn hb :=
.of_image untrop_le_iff isLUB_csSup (hn.image _) (untrop_monotone.map_bddAbove hb)
  isGLB_csInf _ hn hb :=
.of_image untrop_le_iff isGLB_csInf (hn.image _) (untrop_monotone.map_bddBelow hb)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ConditionallyCompleteLinearOrder
  signature: R] : ConditionallyCompleteLinearOrder (Tropical R)
  body: { instConditionallyCompleteLatticeTropical, Tropical.instLinearOrderTropical with
    csSup_of_not_bddAbove := by
      intro s hs
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      simp only [sSup, Set.image_empty, trop_inj_iff]
      apply csSup_of_not_b

中文:
实例 [条件完备线性序
  签名: R] : 条件完备线性序 (Tropical R)
  定义体: { instConditionallyCompleteLatticeTropical, Tropical.instLinearOrderTropical with
    csSup_of_not_bddAbove := by
      intro s hs
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      simp only [sSup, Set.image_empty, trop_inj_iff]
      apply csSup_of_not_b

Depends on / 依赖: BddAbove, Equiv.range_eq_univ, Set.image_empty, Set.range, Set.univ, Tropical, Tropical.instLinearOrderTropical, bddAbove_image, contrapose, csInf_of_not_bddBelow, csSup_of_not_bddAbove, image_empty, instConditionallyCompleteLatticeTropical, instLinearOrderTropical, range_eq_univ, tropEqui, tropEquiv, tropEquiv.symm, tropOrderIso, tropOrderIso.symm
-/
instance [ConditionallyCompleteLinearOrder R] : ConditionallyCompleteLinearOrder (Tropical R) :=
  { instConditionallyCompleteLatticeTropical, Tropical.instLinearOrderTropical with
    csSup_of_not_bddAbove := by
      intro s hs
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      simp only [sSup, Set.image_empty, trop_inj_iff]
      apply csSup_of_not_bddAbove
      contrapose hs
      change BddAbove (tropOrderIso.symm '' s) at hs
      exact tropOrderIso.symm.bddAbove_image.1 hs
    csInf_of_not_bddBelow := by
      intro s hs
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      simp only [sInf, Set.image_empty, trop_inj_iff]
      apply csInf_of_not_bddBelow
      contrapose hs
      change BddBelow (tropOrderIso.symm '' s) at hs
      exact tropOrderIso.symm.bddBelow_image.1 hs }
