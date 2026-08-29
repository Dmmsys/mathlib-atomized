/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Basic
public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.Light.Instances
/-!

# Discrete-underlying adjunction

Given a category `C` with sheafification with respect to the coherent topology on compact Hausdorff
spaces, we define a functor `C ⥤ Condensed C` which associates to an object of `C` the
corresponding "discrete" condensed object (see `Condensed.discrete`).

In `Condensed.discreteUnderlyingAdj` we prove that this functor is left adjoint to the forgetful
functor from `Condensed C` to `C`.

We also give the variant `LightCondensed.discreteUnderlyingAdj` for light condensed objects.

The file `Mathlib/Condensed/Discrete/Characterization.lean` defines a predicate `IsDiscrete` on
condensed and light condensed objects, and provides several conditions on a (light) condensed
set or module that characterize it as discrete.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite GrothendieckTopology

namespace Condensed

variable (C : Type w) [Category.{u + 1} C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]

/--
The discrete condensed object associated to an object of `C` is the constant sheaf at that object.
-/
@[simps!]
/--
Definition of `discrete` / `discrete` 的定义

English:
definition discrete
  signature: : C ⥤ Condensed.{u} C
  body: constantSheaf _ C

中文:
定义 discrete
  签名: : C ⥤ Condensed.{u} C
  定义体: constantSheaf _ C

Depends on / 依赖: constantSheaf
-/
noncomputable def discrete : C ⥤ Condensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the condensed object evaluated at a point.
This can be viewed as a sort of forgetful functor from `Condensed C` to `C`
-/
@[simps!]
/--
Definition of `underlying` / `underlying` 的定义

English:
definition underlying
  signature: : Condensed.{u} C ⥤ C
  body: (sheafSections _ _).obj ⟨CompHaus.of PUnit.{u + 1}⟩

中文:
定义 underlying
  签名: : Condensed.{u} C ⥤ C
  定义体: (sheafSections _ _).obj ⟨CompHaus.of PUnit.{u + 1}⟩

Depends on / 依赖: CompHaus, CompHaus.of, sheafSections
-/
noncomputable def underlying : Condensed.{u} C ⥤ C :=
  (sheafSections _ _).obj ⟨CompHaus.of PUnit.{u + 1}⟩

/--
Definition of `discreteUnderlyingAdj` / `discreteUnderlyingAdj` 的定义

English:
definition discreteUnderlyingAdj
  signature: : discrete C ⊣ underlying C
  body: constantSheafAdj _ _ CompHaus.isTerminalPUnit

中文:
定义 discreteUnderlyingAdj
  签名: : discrete C ⊣ underlying C
  定义体: constantSheafAdj _ _ CompHaus.isTerminalPUnit

Depends on / 依赖: CompHaus, CompHaus.isTerminalPUnit, constantSheafAdj, isTerminalPUnit
-/
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHaus.isTerminalPUnit

end Condensed

namespace LightCondensed

variable (C : Type w) [Category.{u} C] [HasSheafify (coherentTopology LightProfinite.{u}) C]

/--
The discrete light condensed object associated to an object of `C` is the constant sheaf at that
object.
-/
@[simps!]
/--
Definition of `discrete` / `discrete` 的定义

English:
definition discrete
  signature: : C ⥤ LightCondensed.{u} C
  body: constantSheaf _ C

中文:
定义 discrete
  签名: : C ⥤ LightCondensed.{u} C
  定义体: constantSheaf _ C

Depends on / 依赖: constantSheaf
-/
noncomputable def discrete : C ⥤ LightCondensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the light condensed object evaluated at a
point. This can be viewed as a sort of forgetful functor from `LightCondensed C` to `C`
-/
@[simps!]
/--
Definition of `underlying` / `underlying` 的定义

English:
definition underlying
  signature: : LightCondensed.{u} C ⥤ C
  body: (sheafSections _ _).obj (op (LightProfinite.of PUnit))

中文:
定义 underlying
  签名: : LightCondensed.{u} C ⥤ C
  定义体: (sheafSections _ _).obj (op (LightProfinite.of PUnit))

Depends on / 依赖: LightProfinite, LightProfinite.of, sheafSections
-/
noncomputable def underlying : LightCondensed.{u} C ⥤ C :=
  (sheafSections _ _).obj (op (LightProfinite.of PUnit))

/--
Definition of `discreteUnderlyingAdj` / `discreteUnderlyingAdj` 的定义

English:
definition discreteUnderlyingAdj
  signature: : discrete C ⊣ underlying C
  body: constantSheafAdj _ _ CompHausLike.isTerminalPUnit

中文:
定义 discreteUnderlyingAdj
  签名: : discrete C ⊣ underlying C
  定义体: constantSheafAdj _ _ CompHausLike.isTerminalPUnit

Depends on / 依赖: CompHausLike, CompHausLike.isTerminalPUnit, constantSheafAdj, isTerminalPUnit
-/
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHausLike.isTerminalPUnit

end LightCondensed

/--
Definition of `LightCondSet.discrete` / `LightCondSet.discrete` 的定义

English:
abbreviation LightCondSet.discrete
  body: LightCondensed.discrete Type u

中文:
缩写 LightCondSet.discrete
  定义体: LightCondensed.discrete Type u

Depends on / 依赖: LightCondensed, LightCondensed.discrete, discrete
-/
noncomputable abbrev LightCondSet.discrete := LightCondensed.discrete Type u

/--
Definition of `LightCondSet.underlying` / `LightCondSet.underlying` 的定义

English:
abbreviation LightCondSet.underlying
  body: LightCondensed.underlying Type u

中文:
缩写 LightCondSet.underlying
  定义体: LightCondensed.underlying Type u

Depends on / 依赖: LightCondensed, LightCondensed.underlying, underlying
-/
noncomputable abbrev LightCondSet.underlying := LightCondensed.underlying Type u

/--
Definition of `LightCondSet.discreteUnderlyingAdj` / `LightCondSet.discreteUnderlyingAdj` 的定义

English:
abbreviation LightCondSet.discreteUnderlyingAdj
  signature: : discrete ⊣ underlying
  body: LightCondensed.discreteUnderlyingAdj _

中文:
缩写 LightCondSet.discreteUnderlyingAdj
  签名: : discrete ⊣ underlying
  定义体: LightCondensed.discreteUnderlyingAdj _

Depends on / 依赖: LightCondensed, LightCondensed.discreteUnderlyingAdj, discreteUnderlyingAdj
-/
noncomputable abbrev LightCondSet.discreteUnderlyingAdj : discrete ⊣ underlying :=
  LightCondensed.discreteUnderlyingAdj _
