/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# `Discrete PUnit` has limits and colimits

Mostly for the sake of constructing trivial examples, we show all (co)cones into `Discrete PUnit`
are (co)limit (co)cones. We also show that such (co)cones exist, and that `Discrete PUnit` has all
(co)limits.
-/

@[expose] public section


universe v' v

open CategoryTheory

namespace CategoryTheory.Limits

variable {J : Type v} [Category.{v'} J] {F : J ⥤ Discrete PUnit}

/--
Definition of `punitCone` / `punitCone` 的定义

English:
definition punitCone
  signature: : Cone F
  body: ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).hom⟩

中文:
定义 punitCone
  签名: : 锥 F
  定义体: ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).hom⟩

Depends on / 依赖: Functor, Functor.punitExt, punitExt
-/
def punitCone : Cone F :=
  ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).hom⟩

/--
Definition of `punitCocone` / `punitCocone` 的定义

English:
definition punitCocone
  signature: : Cocone F
  body: ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).hom⟩

中文:
定义 punitCocone
  签名: : 余锥 F
  定义体: ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).hom⟩

Depends on / 依赖: Functor, Functor.punitExt, punitExt
-/
def punitCocone : Cocone F :=
  ⟨⟨⟨⟩⟩, (Functor.punitExt _ _).hom⟩

/--
Definition of `punitConeIsLimit` / `punitConeIsLimit` 的定义

English:
definition punitConeIsLimit
  signature: {c : Cone F}
  body: fun s => eqToHom (by simp [eq_iff_true_of_subsingleton])

中文:
定义 punitConeIsLimit
  签名: {c : 锥 F}
  定义体: fun s => eqToHom (by simp [eq_iff_true_of_subsingleton])

Depends on / 依赖: eqToHom, eq_iff_true_of_subsingleton
-/
def punitConeIsLimit {c : Cone F} : IsLimit c where
  lift := fun s => eqToHom (by simp [eq_iff_true_of_subsingleton])

/--
Definition of `punitCoconeIsColimit` / `punitCoconeIsColimit` 的定义

English:
definition punitCoconeIsColimit
  signature: {c : Cocone F}
  body: fun s => eqToHom (by simp [eq_iff_true_of_subsingleton])

中文:
定义 punitCoconeIsColimit
  签名: {c : 余锥 F}
  定义体: fun s => eqToHom (by simp [eq_iff_true_of_subsingleton])

Depends on / 依赖: eqToHom, eq_iff_true_of_subsingleton
-/
def punitCoconeIsColimit {c : Cocone F} : IsColimit c where
  desc := fun s => eqToHom (by simp [eq_iff_true_of_subsingleton])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfSize.{v', v} (Discrete PUnit)
  body: ⟨fun _ _ => ⟨fun _ => ⟨punitCone, punitConeIsLimit⟩⟩⟩

中文:
实例 :
  签名: 有LimitsOfSize.{v', v} (离散 命题单元)
  定义体: ⟨fun _ _ => ⟨fun _ => ⟨punitCone, punitConeIsLimit⟩⟩⟩

Depends on / 依赖: punitCone, punitConeIsLimit
-/
instance : HasLimitsOfSize.{v', v} (Discrete PUnit) :=
  ⟨fun _ _ => ⟨fun _ => ⟨punitCone, punitConeIsLimit⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimitsOfSize.{v', v} (Discrete PUnit)
  body: ⟨fun _ _ => ⟨fun _ => ⟨punitCocone, punitCoconeIsColimit⟩⟩⟩

中文:
实例 :
  签名: 有余limitsOfSize.{v', v} (离散 命题单元)
  定义体: ⟨fun _ _ => ⟨fun _ => ⟨punitCocone, punitCoconeIsColimit⟩⟩⟩

Depends on / 依赖: punitCocone, punitCoconeIsColimit
-/
instance : HasColimitsOfSize.{v', v} (Discrete PUnit) :=
  ⟨fun _ _ => ⟨fun _ => ⟨punitCocone, punitCoconeIsColimit⟩⟩⟩

end CategoryTheory.Limits
