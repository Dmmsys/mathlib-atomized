/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Hom
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of root pairings

This file defines the category of root pairings, following the definition of category of root data
given in SGA III Exp. 21 Section 6.

## Main definitions:
* `RootPairingCat`: Objects are root pairings.

## TODO

* Forgetful functors
* Functions passing between module maps and root pairing homs

## Implementation details

This is mostly copied from `ModuleCat`.

-/

public section

open Set Function CategoryTheory

noncomputable section

universe v u

variable {R : Type u} [CommRing R]

/--
Definition of `RootPairingCat` / `RootPairingCat` 的定义

English:
structure RootPairingCat
  parameters: (R : Type u) [CommRing R]
  axioms and operations (8):
    - weight : Type v
    - [weightIsAddCommGroup : AddCommGroup weight]
    - [weightIsModule : Module R weight]
    - coweight : Type v
    - [coweightIsAddCommGroup : AddCommGroup coweight]
    - [coweightIsModule : Module R coweight]
    - index : Type v
    - pairing : RootPairing index R weight coweight

中文:
结构 RootPairing范畴
  参数: (R : 类型u) [交换环 R]
  公理与运算 (8 个):
    - weight : 类型v
    - [weightIsAddCommGroup : 加法交换群 weight]
    - [weightIsModule : 模 R weight]
    - coweight : 类型v
    - [coweightIsAddCommGroup : 加法交换群 coweight]
    - [coweightIsModule : 模 R coweight]
    - index : 类型v
    - pairing : RootPairing index R weight coweight
-/
structure RootPairingCat (R : Type u) [CommRing R] where
  /-- The weight space of a root pairing. -/
  weight : Type v
  [weightIsAddCommGroup : AddCommGroup weight]
  [weightIsModule : Module R weight]
  /-- The coweight space of a root pairing. -/
  coweight : Type v
  [coweightIsAddCommGroup : AddCommGroup coweight]
  [coweightIsModule : Module R coweight]
  /-- The set that indexes roots and coroots. -/
  index : Type v
  /-- The root pairing structure. -/
  pairing : RootPairing index R weight coweight

attribute [instance] RootPairingCat.weightIsAddCommGroup RootPairingCat.weightIsModule
attribute [instance] RootPairingCat.coweightIsAddCommGroup RootPairingCat.coweightIsModule

namespace RootPairingCat

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category.{v, max (v + 1) u} (RootPairingCat.{v} R) where
  body: RootPairing.Hom P.pairing Q.pairing
  id P := RootPairing.Hom.id P.pairing
  comp f g := RootPairing.Hom.comp g f

中文:
实例 category
  签名: : 范畴.{v, 最大值 (v + 1) u} (RootPairing范畴.{v} R) where
  定义体: RootPairing.Hom P.pairing Q.pairing
  id P := RootPairing.Hom.id P.pairing
  comp f g := RootPairing.Hom.comp g f

Depends on / 依赖: P.pairing, Q.pairing, RootPairing, RootPairing.Hom, pairing
-/
instance category : Category.{v, max (v + 1) u} (RootPairingCat.{v} R) where
  Hom P Q := RootPairing.Hom P.pairing Q.pairing
  id P := RootPairing.Hom.id P.pairing
  comp f g := RootPairing.Hom.comp g f

end RootPairingCat
