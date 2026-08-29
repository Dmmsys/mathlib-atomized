/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.CategoryTheory.PUnit
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Fundamental groupoid of punit

The fundamental groupoid of punit is naturally isomorphic to `CategoryTheory.Discrete PUnit`
-/

@[expose] public section


noncomputable section

open CategoryTheory

universe u v

namespace Path

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (Path PUnit.unit PUnit.unit)
  body: ⟨fun x y => by ext⟩

中文:
实例 :
  签名: Subsingleton (Path PUnit.unit PUnit.unit)
  定义体: ⟨fun x y => by ext⟩
-/
instance : Subsingleton (Path PUnit.unit PUnit.unit) :=
  ⟨fun x y => by ext⟩

end Path

namespace FundamentalGroupoid

instance {x y : FundamentalGroupoid PUnit} : Subsingleton (x ⟶ y) := by
  convert_to! Subsingleton (Path.Homotopic.Quotient PUnit.unit PUnit.unit)
  apply Quotient.instSubsingletonQuotient

/-- Equivalence of groupoids between fundamental groupoid of punit and punit -/
@[simps]
/--
Definition of `punitEquivDiscretePUnit` / `punitEquivDiscretePUnit` 的定义

English:
definition punitEquivDiscretePUnit
  signature: : FundamentalGroupoid PUnit.{u + 1} ≌ Discrete PUnit.{v + 1} where
  body: Functor.star _
  inverse := (CategoryTheory.Functor.const _).obj ⟨PUnit.unit⟩
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := Iso.refl _

中文:
定义 punitEquivDiscretePUnit
  签名: : FundamentalGroupoid PUnit.{u + 1} ≌ Discrete PUnit.{v + 1} where
  定义体: Functor.star _
  inverse := (CategoryTheory.Functor.const _).obj ⟨PUnit.unit⟩
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := Iso.refl _

Depends on / 依赖: Functor, Functor.star
-/
def punitEquivDiscretePUnit : FundamentalGroupoid PUnit.{u + 1} ≌ Discrete PUnit.{v + 1} where
  functor := Functor.star _
  inverse := (CategoryTheory.Functor.const _).obj ⟨PUnit.unit⟩
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := Iso.refl _

end FundamentalGroupoid
