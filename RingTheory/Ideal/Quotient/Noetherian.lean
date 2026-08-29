/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherian quotient rings and quotient modules
-/

public section

/--
Instance `Ideal.Quotient.isNoetherianRing` / 实例 `Ideal.Quotient.isNoetherianRing`

English:
instance Ideal.Quotient.isNoetherianRing
  signature: {R : Type*} [CommRing R] [IsNoetherianRing R]
  body: isNoetherianRing_iff.mpr isNoetherian_of_tower R inferInstance

中文:
实例 理想.商.isNoetherianRing
  签名: {R : 类型} [交换环 R] [是Noether环 R]
  定义体: isNoetherianRing_iff.mpr isNoetherian_of_tower R inferInstance

Depends on / 依赖: HasCountableBasis, HasCountableBasis.isCountablyGenerated, Set.to_countable, exists_antitone_basis, hb.nhds, isCountablyGenerated, isNoetherianRing_iff, isNoetherianRing_iff.mpr, isNoetherian_of_tower, l.exists_antitone_basis, to_countable
-/
instance Ideal.Quotient.isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
isNoetherianRing_iff.mpr isNoetherian_of_tower R inferInstance
