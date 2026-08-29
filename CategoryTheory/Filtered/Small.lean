/-
Copyright (c) 2023 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Tactic.DepRewrite

/-!
# A functor from a small category to a filtered category factors through a small filtered category

A consequence of this is that if `C` is filtered and finally small, then `C` is also
"finally filtered-small", i.e., there is a final functor from a small filtered category to `C`.
This is occasionally useful, for example in the proof of the recognition theorem for ind-objects
(Proposition 6.1.5 in [Kashiwara2006]).
-/

@[expose] public section

universe w v v₁ u u₁

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IsFiltered

section filteredClosure

variable [IsFilteredOrEmpty C] {α : Type w} (f : α -> C)

/--
Inductive type `filteredClosure` / 归纳类型 `filteredClosure`

English:
inductive filteredClosure
  parameters: : ObjectProperty C
  constructors (3):
    - base: (x : α) -> filteredClosure (f x)
    - max: {j j' : C} -> filteredClosure j -> filteredClosure j' -> filteredClosure (max j j')
    - coeq: {j j' : C} -> filteredClosure j -> filteredClosure j' -> (f f' : j ⟶ j') -> filteredClosure (coeq f f')

中文:
归纳类型 filteredClosure
  参数: : Object命题erty C
  构造子 (3 个):
    - base: (x : α) -> filteredClosure (f x)
    - max: {j j' : C} -> filteredClosure j -> filteredClosure j' -> filteredClosure (max j j')
    - coeq: {j j' : C} -> filteredClosure j -> filteredClosure j' -> (f f' : j ⟶ j') -> filteredClosure (coeq f f')
-/
inductive filteredClosure : ObjectProperty C
  | base : (x : α) -> filteredClosure (f x)
  | max : {j j' : C} -> filteredClosure j -> filteredClosure j' -> filteredClosure (max j j')
  | coeq : {j j' : C} -> filteredClosure j -> filteredClosure j' -> (f f' : j ⟶ j') ->
      filteredClosure (coeq f f')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFilteredOrEmpty (filteredClosure f).FullSubcategory
  body: ⟨⟨max j.1 j'.1, filteredClosure.max j.2 j'.2⟩, ObjectProperty.homMk (leftToMax _ _),
      ObjectProperty.homMk (rightToMax _ _), trivial⟩
  cocone_maps {j j'} f f' :=
    ⟨⟨coeq f.hom f'.hom, filteredClosure.coeq j.2 j'.2 f.hom f'.hom⟩,
      ObjectProperty.homMk (coeqHom f.hom f'.hom),
      Objec

中文:
实例 :
  签名: IsFilteredOrEmpty (filteredClosure f).FullSubcategory
  定义体: ⟨⟨max j.1 j'.1, filteredClosure.max j.2 j'.2⟩, ObjectProperty.homMk (leftToMax _ _),
      ObjectProperty.homMk (rightToMax _ _), trivial⟩
  cocone_maps {j j'} f f' :=
    ⟨⟨coeq f.hom f'.hom, filteredClosure.coeq j.2 j'.2 f.hom f'.hom⟩,
      ObjectProperty.homMk (coeqHom f.hom f'.hom),
      Objec

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk, ObjectProperty.hom_ext, cocone_maps, coeqHom, coeq_condition, f.hom, filteredClosure, filteredClosure.coeq, filteredClosure.max, hom_ext, leftToMax, rightToMax
-/
instance : IsFilteredOrEmpty (filteredClosure f).FullSubcategory where
  cocone_objs j j' :=
    ⟨⟨max j.1 j'.1, filteredClosure.max j.2 j'.2⟩, ObjectProperty.homMk (leftToMax _ _),
      ObjectProperty.homMk (rightToMax _ _), trivial⟩
  cocone_maps {j j'} f f' :=
    ⟨⟨coeq f.hom f'.hom, filteredClosure.coeq j.2 j'.2 f.hom f'.hom⟩,
      ObjectProperty.homMk (coeqHom f.hom f'.hom),
      ObjectProperty.hom_ext _ (coeq_condition _ _)⟩

namespace FilteredClosureSmall
/-! Our goal for this section is to show that the size of the filtered closure of an `α`-indexed
    family of objects in `C` only depends on the size of `α` and the morphism types of `C`, not on
    the size of the objects of `C`. More precisely, if `α` lives in `Type w`, the objects of `C`
    live in `Type u` and the morphisms of `C` live in `Type v`, then we want
    `Small.{max v w} (FullSubcategory (filteredClosure f))`.

    The strategy is to define a type `AbstractFilteredClosure` which should be an inductive type
    similar to `filteredClosure`, which lives in the correct universe and surjects onto the full
    subcategory. The difficulty with this is that we need to define it at the same time as the map
    `AbstractFilteredClosure → C`, as the coequalizer constructor depends on the actual morphisms
    in `C`. This would require some kind of inductive-recursive definition, which Lean does not
    allow. Our solution is to define a function `ℕ → Σ t : Type (max v w), t → C` by (strong)
    induction and then take the union over all natural numbers, mimicking what one would do in a
    set-theoretic setting. -/

/--
Inductive type `InductiveStep` / 归纳类型 `InductiveStep`

English:
inductive InductiveStep
  parameters: (n : Nat) (X : forall (k : Nat), k < n -> Σ t : Type (max v w), t -> C)

中文:
归纳类型 InductiveStep
  参数: (n : 自然数) (X : 对任意 (k : 自然数), k < n -> Σ t : Type (max v w), t -> C)
-/
private inductive InductiveStep (n : Nat) (X : forall (k : Nat), k < n -> Σ t : Type (max v w), t -> C) :
    Type (max v w)
  | max : {k k' : Nat} -> (hk : k < n) -> (hk' : k' < n) -> (X _ hk).1 -> (X _ hk').1 -> InductiveStep n X
  | coeq : {k k' : Nat} -> (hk : k < n) -> (hk' : k' < n) -> (j : (X _ hk).1) -> (j' : (X _ hk').1) ->
      ((X _ hk).2 j ⟶ (X _ hk').2 j') -> ((X _ hk).2 j ⟶ (X _ hk').2 j') -> InductiveStep n X

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def inductiveStepRealization (n : Nat)

中文:
定义 noncomputable
  签名: def inductiveStep实数ization (n : 自然数)
-/
private noncomputable def inductiveStepRealization (n : Nat)
    (X : forall (k : Nat), k < n -> Σ t : Type (max v w), t -> C) : InductiveStep.{w} n X -> C
  | (InductiveStep.max hk hk' x y) => max ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.coeq _ _ _ _ f g) => coeq f g

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def bundledAbstractFilteredClosure

中文:
定义 noncomputable
  签名: def bundledAbstractFilteredClosure
-/
private noncomputable def bundledAbstractFilteredClosure :
    Nat -> Σ t : Type (max v w), t -> C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractFilteredClosure m)⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def AbstractFilteredClosure
  body: Σ n, (bundledAbstractFilteredClosure f n).1

中文:
定义 noncomputable
  签名: def AbstractFilteredClosure
  定义体: Σ n, (bundledAbstractFilteredClosure f n).1
-/
private noncomputable def AbstractFilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractFilteredClosure f n).1

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def abstractFilteredClosureRealization
  body: fun x => (bundledAbstractFilteredClosure f x.1).2 x.2

中文:
定义 noncomputable
  签名: def abstractFilteredClosure实数ization
  定义体: fun x => (bundledAbstractFilteredClosure f x.1).2 x.2
-/
private noncomputable def abstractFilteredClosureRealization : AbstractFilteredClosure f -> C :=
  fun x => (bundledAbstractFilteredClosure f x.1).2 x.2

end FilteredClosureSmall

set_option backward.defeqAttrib.useBackward true in
/--
theorem `small_fullSubcategory_filteredClosure` / 定理 `small_fullSubcategory_filteredClosure`

English:
theorem small_fullSubcategory_filteredClosure
  proof: by
  refine small_of_injective_of_exists (FilteredClosureSmall.abstractFilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
      refine ⟨⟨0, ?_⟩, ?_⟩
      · simp only [FilteredClosureSmall.bundledAbstractFilteredClosu

中文:
定理 small_fullSubcategory_filteredClosure
  证明: by
  refine small_of_injective_of_exists (FilteredClosureSmall.abstractFilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
      refine ⟨⟨0, ?_⟩, ?_⟩
      · simp only [FilteredClosureSmall.bundledAbstractFilteredClosu

Depends on / 依赖: FilteredClosureSmall, FilteredClosureSmall.abstractFilteredClosureRealization, FilteredClosureSmall.bundledAbstractFilteredClosure, FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory.ext, ULift.up, abstractFilteredClosureRealization, bundledAbstractFilteredClosure, small_of_injective_of_exists
-/
theorem small_fullSubcategory_filteredClosure :
    Small.{max v w} (filteredClosure f).FullSubcategory := by
  refine small_of_injective_of_exists (FilteredClosureSmall.abstractFilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
      refine ⟨⟨0, ?_⟩, ?_⟩
      · simp only [FilteredClosureSmall.bundledAbstractFilteredClosure]
        exact ULift.up x
      · simp only [FilteredClosureSmall.abstractFilteredClosureRealization,
          FilteredClosureSmall.bundledAbstractFilteredClosure]
        rfl
  | max hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [FilteredClosureSmall.bundledAbstractFilteredClosure]
      refine FilteredClosureSmall.InductiveStep.max ?_ ?_ x y
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [FilteredClosureSmall.abstractFilteredClosureRealization]
      rw! [FilteredClosureSmall.bundledAbstractFilteredClosure]
      rfl
  | coeq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [FilteredClosureSmall.bundledAbstractFilteredClosure]
      refine FilteredClosureSmall.InductiveStep.coeq ?_ ?_ x y g g'
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [FilteredClosureSmall.abstractFilteredClosureRealization]
      rw! [FilteredClosureSmall.bundledAbstractFilteredClosure]
      rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EssentiallySmall.{max v w} (filteredClosure f).FullSubcategory
  body: have : LocallySmall.{max v w} (filteredClosure f).FullSubcategory := locallySmall_max.{w, v, u}
  have := small_fullSubcategory_filteredClosure f
  essentiallySmall_of_small_of_locallySmall _

中文:
实例 :
  签名: EssentiallySmall.{max v w} (filteredClosure f).FullSubcategory
  定义体: have : LocallySmall.{max v w} (filteredClosure f).FullSubcategory := locallySmall_max.{w, v, u}
  have := small_fullSubcategory_filteredClosure f
  essentiallySmall_of_small_of_locallySmall _

Depends on / 依赖: FullSubcategory, LocallySmall, essentiallySmall_of_small_of_locallySmall, filteredClosure, locallySmall_max, small_fullSubcategory_filteredClosure
-/
instance : EssentiallySmall.{max v w} (filteredClosure f).FullSubcategory :=
  have : LocallySmall.{max v w} (filteredClosure f).FullSubcategory := locallySmall_max.{w, v, u}
  have := small_fullSubcategory_filteredClosure f
  essentiallySmall_of_small_of_locallySmall _

end filteredClosure

section

variable [IsFilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)

/--
Definition of `SmallFilteredIntermediate` / `SmallFilteredIntermediate` 的定义

English:
definition SmallFilteredIntermediate
  signature: : Type (max u₁ v)
  body: SmallModel.{max u₁ v} (filteredClosure F.obj).FullSubcategory

中文:
定义 SmallFilteredIntermediate
  签名: : Type (max u₁ v)
  定义体: SmallModel.{max u₁ v} (filteredClosure F.obj).FullSubcategory

Depends on / 依赖: F.obj, FullSubcategory, SmallModel, filteredClosure
-/
def SmallFilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (filteredClosure F.obj).FullSubcategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory (SmallFilteredIntermediate F)
  body: inferInstanceAs (SmallCategory (SmallModel (filteredClosure F.obj).FullSubcategory))

中文:
实例 :
  签名: SmallCategory (SmallFiltered整数ermediate F)
  定义体: inferInstanceAs (SmallCategory (SmallModel (filteredClosure F.obj).FullSubcategory))

Depends on / 依赖: F.obj, FullSubcategory, SmallCategory, SmallModel, filteredClosure
-/
noncomputable instance : SmallCategory (SmallFilteredIntermediate F) :=
  inferInstanceAs (SmallCategory (SmallModel (filteredClosure F.obj).FullSubcategory))

namespace SmallFilteredIntermediate

/--
Definition of `factoring` / `factoring` 的定义

English:
definition factoring
  signature: : D ⥤ SmallFilteredIntermediate F
  body: ObjectProperty.lift _ F filteredClosure.base ⋙ (equivSmallModel _).functor

中文:
定义 factoring
  签名: : D ⥤ SmallFiltered整数ermediate F
  定义体: ObjectProperty.lift _ F filteredClosure.base ⋙ (equivSmallModel _).functor

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, equivSmallModel, filteredClosure, filteredClosure.base, functor
-/
noncomputable def factoring : D ⥤ SmallFilteredIntermediate F :=
  ObjectProperty.lift _ F filteredClosure.base ⋙ (equivSmallModel _).functor

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : SmallFilteredIntermediate F ⥤ C
  body: (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

中文:
定义 inclusion
  签名: : SmallFiltered整数ermediate F ⥤ C
  定义体: (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

Depends on / 依赖: ObjectProperty, equivSmallModel, inverse
-/
noncomputable def inclusion : SmallFilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (inclusion F).Faithful
  body: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

中文:
实例 :
  签名: (inclusion F).Faithful
  定义体: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

Depends on / 依赖: Faithful, ObjectProperty, equivSmallModel, inverse
-/
instance : (inclusion F).Faithful :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (inclusion F).Full
  body: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

中文:
实例 :
  签名: (inclusion F).Full
  定义体: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

Depends on / 依赖: ObjectProperty, equivSmallModel, inverse
-/
noncomputable instance : (inclusion F).Full :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

/--
Definition of `factoringCompInclusion` / `factoringCompInclusion` 的定义

English:
definition factoringCompInclusion
  signature: : factoring F ⋙ inclusion F ≅ F
  body: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

中文:
定义 factoringCompInclusion
  签名: : factoring F ⋙ inclusion F ≅ F
  定义体: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

Depends on / 依赖: Equivalence, Equivalence.unitIso, Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, isoWhiskerLeft, isoWhiskerRight, unitIso
-/
noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFilteredOrEmpty (SmallFilteredIntermediate F)
  body: IsFilteredOrEmpty.of_equivalence (equivSmallModel _)

中文:
实例 :
  签名: IsFilteredOrEmpty (SmallFiltered整数ermediate F)
  定义体: IsFilteredOrEmpty.of_equivalence (equivSmallModel _)

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.of_equivalence, equivSmallModel, of_equivalence
-/
instance : IsFilteredOrEmpty (SmallFilteredIntermediate F) :=
  IsFilteredOrEmpty.of_equivalence (equivSmallModel _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: D] : IsFiltered (SmallFilteredIntermediate F)
  body: { (inferInstance : IsFilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

中文:
实例 [Nonempty
  签名: D] : IsFiltered (SmallFiltered整数ermediate F)
  定义体: { (inferInstance : IsFilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

Depends on / 依赖: IsFilteredOrEmpty, Nonempty, Nonempty.map, factoring, nonempty
-/
instance [Nonempty D] : IsFiltered (SmallFilteredIntermediate F) :=
  { (inferInstance : IsFilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

end SmallFilteredIntermediate

end

end IsFiltered

namespace IsCofiltered

section cofilteredClosure

variable [IsCofilteredOrEmpty C] {α : Type w} (f : α -> C)

/--
Inductive type `cofilteredClosure` / 归纳类型 `cofilteredClosure`

English:
inductive cofilteredClosure
  parameters: : ObjectProperty C
  constructors (3):
    - base: (x : α) -> cofilteredClosure (f x)
    - min: {j j' : C} -> cofilteredClosure j -> cofilteredClosure j' -> cofilteredClosure (min j j')
    - eq: {j j' : C} -> cofilteredClosure j -> cofilteredClosure j' -> (f f' : j ⟶ j') -> cofilteredClosure (eq f f')

中文:
归纳类型 cofilteredClosure
  参数: : Object命题erty C
  构造子 (3 个):
    - base: (x : α) -> cofilteredClosure (f x)
    - min: {j j' : C} -> cofilteredClosure j -> cofilteredClosure j' -> cofilteredClosure (min j j')
    - eq: {j j' : C} -> cofilteredClosure j -> cofilteredClosure j' -> (f f' : j ⟶ j') -> cofilteredClosure (eq f f')
-/
inductive cofilteredClosure : ObjectProperty C
  | base : (x : α) -> cofilteredClosure (f x)
  | min : {j j' : C} -> cofilteredClosure j -> cofilteredClosure j' -> cofilteredClosure (min j j')
  | eq : {j j' : C} -> cofilteredClosure j -> cofilteredClosure j' -> (f f' : j ⟶ j') ->
      cofilteredClosure (eq f f')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCofilteredOrEmpty (cofilteredClosure f).FullSubcategory
  body: ⟨⟨min j.1 j'.1, cofilteredClosure.min j.2 j'.2⟩,
    ObjectProperty.homMk (minToLeft _ _), ObjectProperty.homMk (minToRight _ _), trivial⟩
  cone_maps {j j'} f f' :=
    ⟨⟨eq f.hom f'.hom, cofilteredClosure.eq j.2 j'.2 f.hom f'.hom⟩,
    ObjectProperty.homMk (eqHom f.hom f'.hom), ObjectProperty.hom_

中文:
实例 :
  签名: IsCofilteredOrEmpty (cofilteredClosure f).FullSubcategory
  定义体: ⟨⟨min j.1 j'.1, cofilteredClosure.min j.2 j'.2⟩,
    ObjectProperty.homMk (minToLeft _ _), ObjectProperty.homMk (minToRight _ _), trivial⟩
  cone_maps {j j'} f f' :=
    ⟨⟨eq f.hom f'.hom, cofilteredClosure.eq j.2 j'.2 f.hom f'.hom⟩,
    ObjectProperty.homMk (eqHom f.hom f'.hom), ObjectProperty.hom_

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk, ObjectProperty.hom_ext, cofilteredClosure, cofilteredClosure.eq, cofilteredClosure.min, cone_maps, eq_condition, f.hom, hom_ext, minToLeft, minToRight
-/
instance : IsCofilteredOrEmpty (cofilteredClosure f).FullSubcategory where
  cone_objs j j' :=
    ⟨⟨min j.1 j'.1, cofilteredClosure.min j.2 j'.2⟩,
    ObjectProperty.homMk (minToLeft _ _), ObjectProperty.homMk (minToRight _ _), trivial⟩
  cone_maps {j j'} f f' :=
    ⟨⟨eq f.hom f'.hom, cofilteredClosure.eq j.2 j'.2 f.hom f'.hom⟩,
    ObjectProperty.homMk (eqHom f.hom f'.hom), ObjectProperty.hom_ext _ (eq_condition _ _)⟩

namespace CofilteredClosureSmall

/--
Inductive type `InductiveStep` / 归纳类型 `InductiveStep`

English:
inductive InductiveStep
  parameters: (n : Nat) (X : forall (k : Nat), k < n -> Σ t : Type (max v w), t -> C)

中文:
归纳类型 InductiveStep
  参数: (n : 自然数) (X : 对任意 (k : 自然数), k < n -> Σ t : Type (max v w), t -> C)
-/
private inductive InductiveStep (n : Nat) (X : forall (k : Nat), k < n -> Σ t : Type (max v w), t -> C) :
    Type (max v w)
  | min : {k k' : Nat} -> (hk : k < n) -> (hk' : k' < n) -> (X _ hk).1 -> (X _ hk').1 -> InductiveStep n X
  | eq : {k k' : Nat} -> (hk : k < n) -> (hk' : k' < n) -> (j : (X _ hk).1) -> (j' : (X _ hk').1) ->
      ((X _ hk).2 j ⟶ (X _ hk').2 j') -> ((X _ hk).2 j ⟶ (X _ hk').2 j') -> InductiveStep n X

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def inductiveStepRealization (n : Nat)

中文:
定义 noncomputable
  签名: def inductiveStep实数ization (n : 自然数)
-/
private noncomputable def inductiveStepRealization (n : Nat)
    (X : forall (k : Nat), k < n -> Σ t : Type (max v w), t -> C) : InductiveStep.{w} n X -> C
  | (InductiveStep.min hk hk' x y) => min ((X _ hk).2 x) ((X _ hk').2 y)
  | (InductiveStep.eq _ _ _ _ f g) => eq f g

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def bundledAbstractCofilteredClosure

中文:
定义 noncomputable
  签名: def bundledAbstractCofilteredClosure
-/
private noncomputable def bundledAbstractCofilteredClosure :
    Nat -> Σ t : Type (max v w), t -> C
  | 0 => ⟨ULift.{v} α, f ∘ ULift.down⟩
  | (n + 1) => ⟨_, inductiveStepRealization (n + 1) (fun m _ => bundledAbstractCofilteredClosure m)⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def AbstractCofilteredClosure
  body: Σ n, (bundledAbstractCofilteredClosure f n).1

中文:
定义 noncomputable
  签名: def AbstractCofilteredClosure
  定义体: Σ n, (bundledAbstractCofilteredClosure f n).1
-/
private noncomputable def AbstractCofilteredClosure : Type (max v w) :=
  Σ n, (bundledAbstractCofilteredClosure f n).1

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def abstractCofilteredClosureRealization
  body: fun x => (bundledAbstractCofilteredClosure f x.1).2 x.2

中文:
定义 noncomputable
  签名: def abstractCofilteredClosure实数ization
  定义体: fun x => (bundledAbstractCofilteredClosure f x.1).2 x.2
-/
private noncomputable def abstractCofilteredClosureRealization : AbstractCofilteredClosure f -> C :=
  fun x => (bundledAbstractCofilteredClosure f x.1).2 x.2

end CofilteredClosureSmall

set_option backward.defeqAttrib.useBackward true in
/--
theorem `small_fullSubcategory_cofilteredClosure` / 定理 `small_fullSubcategory_cofilteredClosure`

English:
theorem small_fullSubcategory_cofilteredClosure
  proof: by
  refine small_of_injective_of_exists
    (CofilteredClosureSmall.abstractCofilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
    refine ⟨⟨0, ?_⟩,?_⟩
    · simp only [CofilteredClosureSmall.bundledAbstractCofilter

中文:
定理 small_fullSubcategory_cofilteredClosure
  证明: by
  refine small_of_injective_of_exists
    (CofilteredClosureSmall.abstractCofilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
    refine ⟨⟨0, ?_⟩,?_⟩
    · simp only [CofilteredClosureSmall.bundledAbstractCofilter

Depends on / 依赖: CofilteredClosureSmall, CofilteredClosureSmall.abstractCofilteredClosureRealization, CofilteredClosureSmall.bundledAbstractCofilteredClosure, FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory.ext, ULift.up, abstractCofilteredClosureRealization, bundledAbstractCofilteredClosure, small_of_injective_of_exists
-/
theorem small_fullSubcategory_cofilteredClosure :
    Small.{max v w} (cofilteredClosure f).FullSubcategory := by
  refine small_of_injective_of_exists
    (CofilteredClosureSmall.abstractCofilteredClosureRealization f)
    (fun _ _ => ObjectProperty.FullSubcategory.ext) ?_
  rintro ⟨j, h⟩
  induction h with
  | base x =>
    refine ⟨⟨0, ?_⟩,?_⟩
    · simp only [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      exact ULift.up x
    · simp only [CofilteredClosureSmall.abstractCofilteredClosureRealization,
        CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      rfl
  | min hj₁ hj₂ ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      refine CofilteredClosureSmall.InductiveStep.min ?_ ?_ x y
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [CofilteredClosureSmall.abstractCofilteredClosureRealization]
      rw! [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      rfl
  | eq hj₁ hj₂ g g' ih ih' =>
    rcases ih with ⟨⟨n, x⟩, rfl⟩
    rcases ih' with ⟨⟨m, y⟩, rfl⟩
    refine ⟨⟨(Max.max n m).succ, ?_⟩, ?_⟩
    · simp only [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      refine CofilteredClosureSmall.InductiveStep.eq ?_ ?_ x y g g'
      all_goals apply Nat.lt_succ_of_le
      exacts [Nat.le_max_left _ _, Nat.le_max_right _ _]
    · simp only [CofilteredClosureSmall.abstractCofilteredClosureRealization]
      rw! [CofilteredClosureSmall.bundledAbstractCofilteredClosure]
      rfl
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EssentiallySmall.{max v w} (cofilteredClosure f).FullSubcategory
  body: have : LocallySmall.{max v w} (cofilteredClosure f).FullSubcategory :=
    locallySmall_max.{w, v, u}
  have := small_fullSubcategory_cofilteredClosure f
  essentiallySmall_of_small_of_locallySmall _

中文:
实例 :
  签名: EssentiallySmall.{max v w} (cofilteredClosure f).FullSubcategory
  定义体: have : LocallySmall.{max v w} (cofilteredClosure f).FullSubcategory :=
    locallySmall_max.{w, v, u}
  have := small_fullSubcategory_cofilteredClosure f
  essentiallySmall_of_small_of_locallySmall _

Depends on / 依赖: FullSubcategory, LocallySmall, cofilteredClosure, essentiallySmall_of_small_of_locallySmall, locallySmall_max, small_fullSubcategory_cofilteredClosure
-/
instance : EssentiallySmall.{max v w} (cofilteredClosure f).FullSubcategory :=
  have : LocallySmall.{max v w} (cofilteredClosure f).FullSubcategory :=
    locallySmall_max.{w, v, u}
  have := small_fullSubcategory_cofilteredClosure f
  essentiallySmall_of_small_of_locallySmall _

end cofilteredClosure

section

variable [IsCofilteredOrEmpty C] {D : Type u₁} [Category.{v₁} D] (F : D ⥤ C)

/--
Definition of `SmallCofilteredIntermediate` / `SmallCofilteredIntermediate` 的定义

English:
definition SmallCofilteredIntermediate
  signature: : Type (max u₁ v)
  body: SmallModel.{max u₁ v} (cofilteredClosure F.obj).FullSubcategory

中文:
定义 SmallCofilteredIntermediate
  签名: : Type (max u₁ v)
  定义体: SmallModel.{max u₁ v} (cofilteredClosure F.obj).FullSubcategory

Depends on / 依赖: F.obj, FullSubcategory, SmallModel, cofilteredClosure
-/
def SmallCofilteredIntermediate : Type (max u₁ v) :=
  SmallModel.{max u₁ v} (cofilteredClosure F.obj).FullSubcategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory (SmallCofilteredIntermediate F)
  body: inferInstanceAs (SmallCategory (SmallModel (cofilteredClosure F.obj).FullSubcategory))

中文:
实例 :
  签名: SmallCategory (SmallCofiltered整数ermediate F)
  定义体: inferInstanceAs (SmallCategory (SmallModel (cofilteredClosure F.obj).FullSubcategory))

Depends on / 依赖: F.obj, FullSubcategory, SmallCategory, SmallModel, cofilteredClosure
-/
noncomputable instance : SmallCategory (SmallCofilteredIntermediate F) :=
  inferInstanceAs (SmallCategory (SmallModel (cofilteredClosure F.obj).FullSubcategory))

namespace SmallCofilteredIntermediate

/--
Definition of `factoring` / `factoring` 的定义

English:
definition factoring
  signature: : D ⥤ SmallCofilteredIntermediate F
  body: ObjectProperty.lift _ F cofilteredClosure.base ⋙ (equivSmallModel _).functor

中文:
定义 factoring
  签名: : D ⥤ SmallCofiltered整数ermediate F
  定义体: ObjectProperty.lift _ F cofilteredClosure.base ⋙ (equivSmallModel _).functor

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, cofilteredClosure, cofilteredClosure.base, equivSmallModel, functor
-/
noncomputable def factoring : D ⥤ SmallCofilteredIntermediate F :=
  ObjectProperty.lift _ F cofilteredClosure.base ⋙ (equivSmallModel _).functor

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : SmallCofilteredIntermediate F ⥤ C
  body: (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

中文:
定义 inclusion
  签名: : SmallCofiltered整数ermediate F ⥤ C
  定义体: (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

Depends on / 依赖: ObjectProperty, equivSmallModel, inverse
-/
noncomputable def inclusion : SmallCofilteredIntermediate F ⥤ C :=
  (equivSmallModel _).inverse ⋙ ObjectProperty.ι _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (inclusion F).Faithful
  body: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

中文:
实例 :
  签名: (inclusion F).Faithful
  定义体: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

Depends on / 依赖: Faithful, ObjectProperty, equivSmallModel, inverse
-/
instance : (inclusion F).Faithful :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (inclusion F).Full
  body: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

中文:
实例 :
  签名: (inclusion F).Full
  定义体: inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

Depends on / 依赖: ObjectProperty, equivSmallModel, inverse
-/
noncomputable instance : (inclusion F).Full :=
  inferInstanceAs ((equivSmallModel _).inverse ⋙ ObjectProperty.ι _).Full

/--
Definition of `factoringCompInclusion` / `factoringCompInclusion` 的定义

English:
definition factoringCompInclusion
  signature: : factoring F ⋙ inclusion F ≅ F
  body: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

中文:
定义 factoringCompInclusion
  签名: : factoring F ⋙ inclusion F ≅ F
  定义体: Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

Depends on / 依赖: Equivalence, Equivalence.unitIso, Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, isoWhiskerLeft, isoWhiskerRight, unitIso
-/
noncomputable def factoringCompInclusion : factoring F ⋙ inclusion F ≅ F :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (Equivalence.unitIso _).symm _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCofilteredOrEmpty (SmallCofilteredIntermediate F)
  body: IsCofilteredOrEmpty.of_equivalence (equivSmallModel _)

中文:
实例 :
  签名: IsCofilteredOrEmpty (SmallCofiltered整数ermediate F)
  定义体: IsCofilteredOrEmpty.of_equivalence (equivSmallModel _)

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.of_equivalence, equivSmallModel, of_equivalence
-/
instance : IsCofilteredOrEmpty (SmallCofilteredIntermediate F) :=
  IsCofilteredOrEmpty.of_equivalence (equivSmallModel _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: D] : IsCofiltered (SmallCofilteredIntermediate F)
  body: { (inferInstance : IsCofilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

中文:
实例 [Nonempty
  签名: D] : IsCofiltered (SmallCofiltered整数ermediate F)
  定义体: { (inferInstance : IsCofilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

Depends on / 依赖: IsCofilteredOrEmpty, Nonempty, Nonempty.map, factoring, nonempty
-/
instance [Nonempty D] : IsCofiltered (SmallCofilteredIntermediate F) :=
  { (inferInstance : IsCofilteredOrEmpty _) with
    nonempty := Nonempty.map (factoring F).obj inferInstance }

end SmallCofilteredIntermediate

end

end IsCofiltered

end CategoryTheory
