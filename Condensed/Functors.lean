/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.Condensed.Explicit

/-!
# Functors from categories of topological spaces to condensed sets

This file defines the embedding of the test objects (compact Hausdorff spaces) into condensed
sets.

## Main definitions

* `compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u}` is essentially the yoneda presheaf
  functor. We also define `profiniteToCondensed` and `stoneanToCondensed`.

-/

@[expose] public section

universe u v

open CategoryTheory Limits

section Universes

/--
Definition of `Condensed.ulift` / `Condensed.ulift` 的定义

English:
definition Condensed.ulift
  signature: : Condensed.{u} (Type u) ⥤ CondensedSet.{u}
  body: sheafCompose (coherentTopology CompHaus) uliftFunctor.{u + 1, u}

中文:
定义 Condensed.ulift
  签名: : Condensed.{u} (类型u) ⥤ CondensedSet.{u}
  定义体: sheafCompose (coherentTopology CompHaus) uliftFunctor.{u + 1, u}

Depends on / 依赖: CompHaus, coherentTopology, sheafCompose, uliftFunctor
-/
def Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u} :=
  sheafCompose (coherentTopology CompHaus) uliftFunctor.{u + 1, u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Condensed.ulift.Full
  body: show (sheafCompose _ _).Full from inferInstance

中文:
实例 :
  签名: Condensed.ulift.满
  定义体: show (sheafCompose _ _).Full from inferInstance

Depends on / 依赖: sheafCompose
-/
instance : Condensed.ulift.Full := show (sheafCompose _ _).Full from inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Condensed.ulift.Faithful
  body: show (sheafCompose _ _).Faithful from inferInstance

中文:
实例 :
  签名: Condensed.ulift.忠实
  定义体: show (sheafCompose _ _).Faithful from inferInstance

Depends on / 依赖: Faithful, sheafCompose
-/
instance : Condensed.ulift.Faithful := show (sheafCompose _ _).Faithful from inferInstance

end Universes

section Topology

/--
Definition of `compHausToCondensed'` / `compHausToCondensed'` 的定义

English:
definition compHausToCondensed'
  signature: : CompHaus.{u} ⥤ Condensed.{u} (Type u)
  body: (coherentTopology CompHaus).yoneda

中文:
定义 compHausToCondensed'
  签名: : CompHaus.{u} ⥤ Condensed.{u} (类型u)
  定义体: (coherentTopology CompHaus).yoneda

Depends on / 依赖: CompHaus, coherentTopology, yoneda
-/
def compHausToCondensed' : CompHaus.{u} ⥤ Condensed.{u} (Type u) :=
  (coherentTopology CompHaus).yoneda

/--
Definition of `compHausToCondensed` / `compHausToCondensed` 的定义

English:
definition compHausToCondensed
  signature: : CompHaus.{u} ⥤ CondensedSet.{u}
  body: compHausToCondensed' ⋙ Condensed.ulift

中文:
定义 compHausToCondensed
  签名: : CompHaus.{u} ⥤ CondensedSet.{u}
  定义体: compHausToCondensed' ⋙ Condensed.ulift

Depends on / 依赖: Condensed, Condensed.ulift, compHausToCondensed
-/
def compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u} :=
  compHausToCondensed' ⋙ Condensed.ulift

/--
Definition of `CompHaus.toCondensed` / `CompHaus.toCondensed` 的定义

English:
abbreviation CompHaus.toCondensed
  signature: (S : CompHaus.{u})
  body: compHausToCondensed.obj S

中文:
缩写 CompHaus.toCondensed
  签名: (S : CompHaus.{u})
  定义体: compHausToCondensed.obj S

Depends on / 依赖: compHausToCondensed, compHausToCondensed.obj
-/
abbrev CompHaus.toCondensed (S : CompHaus.{u}) : CondensedSet.{u} := compHausToCondensed.obj S

/--
Definition of `profiniteToCondensed` / `profiniteToCondensed` 的定义

English:
definition profiniteToCondensed
  signature: : Profinite.{u} ⥤ CondensedSet.{u}
  body: profiniteToCompHaus ⋙ compHausToCondensed

中文:
定义 profiniteToCondensed
  签名: : Profinite.{u} ⥤ CondensedSet.{u}
  定义体: profiniteToCompHaus ⋙ compHausToCondensed

Depends on / 依赖: compHausToCondensed, profiniteToCompHaus
-/
def profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u} :=
  profiniteToCompHaus ⋙ compHausToCondensed

/--
Definition of `Profinite.toCondensed` / `Profinite.toCondensed` 的定义

English:
abbreviation Profinite.toCondensed
  signature: (S : Profinite.{u})
  body: profiniteToCondensed.obj S

中文:
缩写 Profinite.toCondensed
  签名: (S : Profinite.{u})
  定义体: profiniteToCondensed.obj S

Depends on / 依赖: profiniteToCondensed, profiniteToCondensed.obj
-/
abbrev Profinite.toCondensed (S : Profinite.{u}) : CondensedSet.{u} := profiniteToCondensed.obj S

/--
Definition of `stoneanToCondensed` / `stoneanToCondensed` 的定义

English:
definition stoneanToCondensed
  signature: : Stonean.{u} ⥤ CondensedSet.{u}
  body: Stonean.toCompHaus ⋙ compHausToCondensed

中文:
定义 stoneanToCondensed
  签名: : Stonean.{u} ⥤ CondensedSet.{u}
  定义体: Stonean.toCompHaus ⋙ compHausToCondensed

Depends on / 依赖: Stonean, Stonean.toCompHaus, compHausToCondensed, toCompHaus
-/
def stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u} :=
  Stonean.toCompHaus ⋙ compHausToCondensed

/--
Definition of `Stonean.toCondensed` / `Stonean.toCondensed` 的定义

English:
abbreviation Stonean.toCondensed
  signature: (S : Stonean.{u})
  body: stoneanToCondensed.obj S

中文:
缩写 Stonean.toCondensed
  签名: (S : Stonean.{u})
  定义体: stoneanToCondensed.obj S

Depends on / 依赖: stoneanToCondensed, stoneanToCondensed.obj
-/
abbrev Stonean.toCondensed (S : Stonean.{u}) : CondensedSet.{u} := stoneanToCondensed.obj S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: compHausToCondensed'.Full
  body: inferInstanceAs ((coherentTopology CompHaus).yoneda).Full

中文:
实例 :
  签名: compHausToCondensed'.满
  定义体: inferInstanceAs ((coherentTopology CompHaus).yoneda).Full

Depends on / 依赖: CompHaus, coherentTopology, yoneda
-/
instance : compHausToCondensed'.Full :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: compHausToCondensed'.Faithful
  body: inferInstanceAs ((coherentTopology CompHaus).yoneda).Faithful

中文:
实例 :
  签名: compHausToCondensed'.忠实
  定义体: inferInstanceAs ((coherentTopology CompHaus).yoneda).Faithful

Depends on / 依赖: CompHaus, Faithful, coherentTopology, yoneda
-/
instance : compHausToCondensed'.Faithful :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: compHausToCondensed.Full
  body: inferInstanceAs (_ ⋙ _).Full

中文:
实例 :
  签名: compHausToCondensed.满
  定义体: inferInstanceAs (_ ⋙ _).Full
-/
instance : compHausToCondensed.Full := inferInstanceAs (_ ⋙ _).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: compHausToCondensed.Faithful
  body: inferInstanceAs (_ ⋙ _).Faithful

中文:
实例 :
  签名: compHausToCondensed.忠实
  定义体: inferInstanceAs (_ ⋙ _).Faithful

Depends on / 依赖: Faithful
-/
instance : compHausToCondensed.Faithful := inferInstanceAs (_ ⋙ _).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteCoproducts compHausToCondensed.{u}
  body: inferInstanceAs PreservesFiniteCoproducts (coherentTopology _).uliftYoneda

中文:
实例 :
  签名: 保持FiniteCoproducts compHausToCondensed.{u}
  定义体: inferInstanceAs PreservesFiniteCoproducts (coherentTopology _).uliftYoneda

Depends on / 依赖: PreservesFiniteCoproducts, coherentTopology, uliftYoneda
-/
instance : PreservesFiniteCoproducts compHausToCondensed.{u} :=
inferInstanceAs PreservesFiniteCoproducts (coherentTopology _).uliftYoneda

end Topology
