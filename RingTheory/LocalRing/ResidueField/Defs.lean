/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!

# Residue Field of local rings

## Main definitions

* `IsLocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.
* `IsLocalRing.residue`: The quotient map from a local ring to its residue field.
-/

@[expose] public section

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The residue field of a local ring is the quotient of the ring by its maximal ideal. -/
@[wikidata Q7315530]
/--
Definition of `ResidueField` / `ResidueField` 的定义

English:
definition ResidueField
  body: R ⧸ maximalIdeal R
deriving CommRing, Inhabited

中文:
定义 ResidueField
  定义体: R ⧸ maximalIdeal R
deriving CommRing, Inhabited

Depends on / 依赖: isProperMap_smul, maximalIdeal, pi_map
-/
def ResidueField :=
  R ⧸ maximalIdeal R
deriving CommRing, Inhabited

/--
Instance `ResidueField.field` / 实例 `ResidueField.field`

English:
instance ResidueField.field
  signature: : Field (ResidueField R)
  body: fast_instance% Ideal.Quotient.field (maximalIdeal R)

中文:
实例 ResidueField.field
  签名: : 域 (ResidueField R)
  定义体: fast_instance% Ideal.Quotient.field (maximalIdeal R)

Depends on / 依赖: Ideal.Quotient.field, Quotient, fast_instance, maximalIdeal
-/
noncomputable instance ResidueField.field : Field (ResidueField R) :=
  fast_instance% Ideal.Quotient.field (maximalIdeal R)

/--
Definition of `residue` / `residue` 的定义

English:
definition residue
  signature: : R ->+* ResidueField R
  body: Ideal.Quotient.mk _

中文:
定义 residue
  签名: : R ->+* ResidueField R
  定义体: Ideal.Quotient.mk _

Depends on / 依赖: Ideal.Quotient.mk, Quotient
-/
def residue : R ->+* ResidueField R :=
  Ideal.Quotient.mk _

end IsLocalRing
