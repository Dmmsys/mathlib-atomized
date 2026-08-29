/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.RingTheory.Etale.Descent

/-!

# Local properties satisfying fpqc descent

In this file we provide instances that show that the following local properties satisfy fpqc
descent:

- locally of finite type
- locally of finite presentation
- smooth
- formally unramified
- étale

-/

public section

open CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  body: HasRingHomProperty.descendsAlong_flat RingHom.FiniteType.codescendsAlong_faithfullyFlat

中文:
实例 :
  签名: DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  定义体: HasRingHomProperty.descendsAlong_flat RingHom.FiniteType.codescendsAlong_faithfullyFlat

Depends on / 依赖: FiniteType, HasRingHomProperty, HasRingHomProperty.descendsAlong_flat, RingHom, RingHom.FiniteType.codescendsAlong_faithfullyFlat, codescendsAlong_faithfullyFlat, descendsAlong_flat
-/
instance : DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.FiniteType.codescendsAlong_faithfullyFlat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DescendsAlong @LocallyOfFinitePresentation (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  body: HasRingHomProperty.descendsAlong_flat RingHom.FinitePresentation.codescendsAlong_faithfullyFlat

中文:
实例 :
  签名: DescendsAlong @LocallyOfFinitePresentation (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  定义体: HasRingHomProperty.descendsAlong_flat RingHom.FinitePresentation.codescendsAlong_faithfullyFlat

Depends on / 依赖: FinitePresentation, HasRingHomProperty, HasRingHomProperty.descendsAlong_flat, RingHom, RingHom.FinitePresentation.codescendsAlong_faithfullyFlat, codescendsAlong_faithfullyFlat, descendsAlong_flat
-/
instance : DescendsAlong @LocallyOfFinitePresentation (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.FinitePresentation.codescendsAlong_faithfullyFlat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  body: HasRingHomProperty.descendsAlong_flat RingHom.Smooth.codescendsAlong_faithfullyFlat

中文:
实例 :
  签名: DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  定义体: HasRingHomProperty.descendsAlong_flat RingHom.Smooth.codescendsAlong_faithfullyFlat

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.descendsAlong_flat, RingHom, RingHom.Smooth.codescendsAlong_faithfullyFlat, Smooth, codescendsAlong_faithfullyFlat, descendsAlong_flat
-/
instance : DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Smooth.codescendsAlong_faithfullyFlat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DescendsAlong @FormallyUnramified (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  body: HasRingHomProperty.descendsAlong_flat RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat

中文:
实例 :
  签名: DescendsAlong @FormallyUnramified (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  定义体: HasRingHomProperty.descendsAlong_flat RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat

Depends on / 依赖: FormallyUnramified, HasRingHomProperty, HasRingHomProperty.descendsAlong_flat, RingHom, RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat, codescendsAlong_faithfullyFlat, descendsAlong_flat
-/
instance : DescendsAlong @FormallyUnramified (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  body: HasRingHomProperty.descendsAlong_flat RingHom.Etale.codescendsAlong_faithfullyFlat

中文:
实例 :
  签名: DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
  定义体: HasRingHomProperty.descendsAlong_flat RingHom.Etale.codescendsAlong_faithfullyFlat

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.descendsAlong_flat, RingHom, RingHom.Etale.codescendsAlong_faithfullyFlat, codescendsAlong_faithfullyFlat, descendsAlong_flat
-/
instance : DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Etale.codescendsAlong_faithfullyFlat

end AlgebraicGeometry
