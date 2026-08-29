/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.Shrink

/-!
# Category of $R$-modules has enough injectives

We lift enough injectives of abelian groups to arbitrary $R$-modules by adjoint functors
`restrictScalars ⊣ coextendScalars`
-/

public section

open CategoryTheory

universe v u

variable (R : Type u) [Ring R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EnoughInjectives (ModuleCat.{v} Int)
  body: EnoughInjectives.of_equivalence (forget₂ (ModuleCat Int) AddCommGrpCat)

中文:
实例 :
  签名: 有足够单射 (模范畴.{v} 整数)
  定义体: EnoughInjectives.of_equivalence (forget₂ (ModuleCat Int) AddCommGrpCat)

Depends on / 依赖: AddCommGrpCat, EnoughInjectives, EnoughInjectives.of_equivalence, ModuleCat, of_equivalence
-/
instance : EnoughInjectives (ModuleCat.{v} Int) :=
  EnoughInjectives.of_equivalence (forget₂ (ModuleCat Int) AddCommGrpCat)

/--
lemma `ModuleCat.enoughInjectives` / 引理 `ModuleCat.enoughInjectives`

English:
lemma ModuleCat.enoughInjectives
  statement: EnoughInjectives (ModuleCat.{max v u} R)
  proof: EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap Int R))

中文:
引理 模范畴.enoughInjectives
  结论: 有足够单射 (模范畴.{最大值 v u} R)
  证明: EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap Int R))

Depends on / 依赖: EnoughInjectives, EnoughInjectives.of_adjunction, ModuleCat, ModuleCat.restrictCoextendScalarsAdj, algebraMap, of_adjunction, restrictCoextendScalarsAdj
-/
lemma ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R) :=
  EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap Int R))

open ModuleCat in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{v}
  signature: R] : EnoughInjectives (ModuleCat.{v} R)
  body: letI := enoughInjectives.{v} (Shrink.{v} R)
  EnoughInjectives.of_equivalence (restrictScalars (equivShrink R).symm.ringEquiv.toRingHom)

中文:
实例 [Small.{v}
  签名: R] : 有足够单射 (模范畴.{v} R)
  定义体: letI := enoughInjectives.{v} (Shrink.{v} R)
  EnoughInjectives.of_equivalence (restrictScalars (equivShrink R).symm.ringEquiv.toRingHom)

Depends on / 依赖: EnoughInjectives, EnoughInjectives.of_equivalence, Shrink, enoughInjectives, equivShrink, of_equivalence, restrictScalars, ringEquiv, symm.ringEquiv.toRingHom, toRingHom
-/
instance [Small.{v} R] : EnoughInjectives (ModuleCat.{v} R) :=
  letI := enoughInjectives.{v} (Shrink.{v} R)
  EnoughInjectives.of_equivalence (restrictScalars (equivShrink R).symm.ringEquiv.toRingHom)
