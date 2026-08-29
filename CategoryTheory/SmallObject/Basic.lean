/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

/-!
# The small object argument

Let `C` be a category. A class of morphisms `I : MorphismProperty C`
permits the small object argument (typeclass `HasSmallObjectArgument.{w} I`
where `w` is an auxiliary universe) if there exists a regular
cardinal `κ : Cardinal.{w}` such that `IsCardinalForSmallObjectArgument I κ`
holds. This technical condition is defined in the file
`Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean`. It involves certain
smallness conditions relative to `w`, the existence of certain colimits in `C`,
and for each object `A` which is the source of a morphism in `I`,
the `Hom(A, -)` functor (`coyoneda.obj (op A)`) should commute
to transfinite compositions of pushouts of coproducts of morphisms in `I`
(this condition is automatically satisfied for a suitable `κ` when `A` is a
presentable object of `C`, see the file `Mathlib/CategoryTheory/Presentable/Basic.lean`).

## Main results

Assuming `I` permits the small object argument, the two main results
obtained in this file are:
* the class `I.rlp.llp` of morphisms that have the left lifting property with
  respect to the maps that have the right lifting property with respect
  to `I` are exactly the retracts of transfinite compositions (indexed
  by a suitable well-ordered type `J`) of pushouts of coproducts of
  morphisms in `I`;
* morphisms in `C` have a functorial factorization as a morphism in
  `I.rlp.llp` followed by a morphism in `I.rlp`.

In the context of model categories, these results are known as Quillen's small object
argument (originally for `J := ℕ`). Actually, the more general construction by
transfinite induction already appeared in the proof of the existence of enough
injectives in abelian categories with AB5 and a generator by Grothendieck, who then
wrote that the "proof was essentially known". Indeed, the argument appeared
in *Homological algebra* by Cartan and Eilenberg (p. 9-10) in the case of modules,
and they mention that the result was initially obtained by Baer.

## Structure of the proof

The main part in the proof is the construction of the functorial factorization.
This involves a construction by transfinite induction. A general
procedure for constructions by transfinite
induction in categories (including the iteration of a functor)
is done in the file `Mathlib/CategoryTheory/SmallObject/TransfiniteIteration.lean`.
The factorization of the small object argument is obtained by doing
a transfinite iteration of a specific functor `Arrow C ⥤ Arrow C` which
is defined in the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` (this definition
involves coproducts and a pushout). These ingredients are combined
in the file `Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean`
where the main results are obtained under a `IsCardinalForSmallObjectArgument I κ`
assumption. The fact that the left lifting property with respect to
a class of morphisms is stable by transfinite compositions was obtained in
the file `Mathlib/CategoryTheory/SmallObject/TransfiniteCompositionLifting.lean`.

## References

- [Henri Cartan and Samuel Eilenberg, *Homological algebra*][cartan-eilenberg-1956]
- [Alexander Grothendieck, *Sur quelques points d'algèbre homologique*][grothendieck-1957]
- [Daniel G. Quillen, *Homotopical algebra*][Quillen1967]
- https://ncatlab.org/nlab/show/small+object+argument

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits SmallObject

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

/--
Definition of `HasSmallObjectArgument` / `HasSmallObjectArgument` 的定义

English:
class HasSmallObjectArgument
  parameters: : Prop where
  axioms and operations (1):
    - exists_cardinal : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType), IsCardinalForSmallObjectArgument I κ

中文:
类 有SmallObjectArgument
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_cardinal : 存在 (κ : 基数.{w}) (_ : Fact κ.是正则) (_ : 有底序 κ.ord.ToType), 是CardinalForSmallObjectArgument I κ
-/
class HasSmallObjectArgument : Prop where
  exists_cardinal : exists (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
    IsCardinalForSmallObjectArgument I κ

variable [HasSmallObjectArgument.{w} I]

/--
Definition of `smallObjectκ` / `smallObjectκ` 的定义

English:
definition smallObjectκ
  signature: : Cardinal.{w}
  body: (HasSmallObjectArgument.exists_cardinal (I := I)).choose

local instance smallObjectκ_isRegular : Fact I.smallObjectκ.IsRegular :=
  HasSmallObjectArgument.exists_cardinal.choose_spec.choose

中文:
定义 smallObjectκ
  签名: : 基数.{w}
  定义体: (HasSmallObjectArgument.exists_cardinal (I := I)).choose

local instance smallObjectκ_isRegular : Fact I.smallObjectκ.IsRegular :=
  HasSmallObjectArgument.exists_cardinal.choose_spec.choose

Depends on / 依赖: HasSmallObjectArgument, HasSmallObjectArgument.exists_cardinal, exists_cardinal
-/
noncomputable def smallObjectκ : Cardinal.{w} :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose

local instance smallObjectκ_isRegular : Fact I.smallObjectκ.IsRegular :=
  HasSmallObjectArgument.exists_cardinal.choose_spec.choose

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot I.smallObjectκ.ord.ToType
  body: HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose

中文:
实例 :
  签名: 有底序 I.smallObjectκ.ord.ToType
  定义体: HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose

Depends on / 依赖: HasSmallObjectArgument, HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose, choose_spec, exists_cardinal
-/
noncomputable instance : OrderBot I.smallObjectκ.ord.ToType :=
  HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose

/--
Instance `isCardinalForSmallObjectArgument_smallObjectκ` / 实例 `isCardinalForSmallObjectArgument_smallObjectκ`

English:
instance isCardinalForSmallObjectArgument_smallObjectκ
  signature: :
  body: HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose_spec

中文:
实例 isCardinalForSmallObjectArgument_smallObjectκ
  签名: :
  定义体: HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose_spec

Depends on / 依赖: HasSmallObjectArgument, HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose_spec, choose_spec, exists_cardinal
-/
instance isCardinalForSmallObjectArgument_smallObjectκ :
    IsCardinalForSmallObjectArgument.{w} I I.smallObjectκ :=
  HasSmallObjectArgument.exists_cardinal.choose_spec.choose_spec.choose_spec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFunctorialFactorization I.rlp.llp I.rlp
  body: hasFunctorialFactorization I I.smallObjectκ

中文:
实例 :
  签名: 有FunctorialFactorization I.rlp.llp I.rlp
  定义体: hasFunctorialFactorization I I.smallObjectκ

Depends on / 依赖: I.smallObject, hasFunctorialFactorization
-/
instance : HasFunctorialFactorization I.rlp.llp I.rlp :=
  hasFunctorialFactorization I I.smallObjectκ

/--
lemma `llp_rlp_of_hasSmallObjectArgument'` / 引理 `llp_rlp_of_hasSmallObjectArgument'`

English:
lemma llp_rlp_of_hasSmallObjectArgument'
  proof: llp_rlp_of_isCardinalForSmallObjectArgument' I I.smallObjectκ

中文:
引理 llp_rlp_of_hasSmallObjectArgument'
  证明: llp_rlp_of_isCardinalForSmallObjectArgument' I I.smallObjectκ

Depends on / 依赖: I.smallObject, llp_rlp_of_isCardinalForSmallObjectArgument
-/
lemma llp_rlp_of_hasSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{w} I).pushouts
        I.smallObjectκ.ord.ToType).retracts :=
  llp_rlp_of_isCardinalForSmallObjectArgument' I I.smallObjectκ

/--
lemma `llp_rlp_of_hasSmallObjectArgument` / 引理 `llp_rlp_of_hasSmallObjectArgument`

English:
lemma llp_rlp_of_hasSmallObjectArgument
  proof: llp_rlp_of_isCardinalForSmallObjectArgument I I.smallObjectκ

中文:
引理 llp_rlp_of_hasSmallObjectArgument
  证明: llp_rlp_of_isCardinalForSmallObjectArgument I I.smallObjectκ

Depends on / 依赖: I.smallObject, llp_rlp_of_isCardinalForSmallObjectArgument
-/
lemma llp_rlp_of_hasSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts :=
  llp_rlp_of_isCardinalForSmallObjectArgument I I.smallObjectκ

end MorphismProperty

end CategoryTheory
