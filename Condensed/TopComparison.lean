/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.Condensed.Basic
public import Mathlib.Topology.Category.TopCat.Yoneda

/-!

# The functor from topological spaces to condensed sets

This file builds on the API from the file `TopCat.Yoneda`. If the forgetful functor to `TopCat` has
nice properties, like preserving pullbacks and finite coproducts, then this Yoneda presheaf
satisfies the sheaf condition for the regular and extensive topologies respectively.

We apply this API to `CompHaus` and define the functor
`topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u}`.

-/

@[expose] public section

universe w w' v u

open CategoryTheory Opposite Limits regularTopology ContinuousMap Topology

variable {C : Type u} [Category.{v} C] (G : C ⥤ TopCat.{w})
  (X : Type w') [TopologicalSpace X]

/--
theorem `factorsThrough_of_pullbackCondition` / 定理 `factorsThrough_of_pullbackCondition`

English:
theorem factorsThrough_of_pullbackCondition
  statement: {Z B : C} {π : Z ⟶ B} [HasPullback π π]
  proof: by
  intro x y hxy
let xy : G.obj (pullback π π) := (PreservesPullback.iso G π π).inv
    (TopCat.pullbackIsoProdSubtype (G.map π) (G.map π)).inv ⟨(x, y), hxy⟩
  have ha' := congr_fun ha xy
  dsimp at ha'
  have h₁ : forall y, G.map (pullback.fst _ _) ((PreservesPullback.iso G π π).inv y) =
      pu

中文:
定理 factorsThrough_of_pullbackCondition
  结论: {Z B : C} {π : Z ⟶ B} [HasPullback π π]
  证明: by
  intro x y hxy
let xy : G.obj (pullback π π) := (PreservesPullback.iso G π π).inv
    (TopCat.pullbackIsoProdSubtype (G.map π) (G.map π)).inv ⟨(x, y), hxy⟩
  have ha' := congr_fun ha xy
  dsimp at ha'
  have h₁ : forall y, G.map (pullback.fst _ _) ((PreservesPullback.iso G π π).inv y) =
      pu

Depends on / 依赖: G.map, G.obj, PreservesPullback, PreservesPullback.iso, PreservesPullback.iso_inv_fst, TopCat, TopCat.pullbackIsoProdSubtype, congr_fun, iso_inv_fst, pullback, pullback.fst, pullback.snd, pullbackIsoProdSubtype
-/
theorem factorsThrough_of_pullbackCondition {Z B : C} {π : Z ⟶ B} [HasPullback π π]
    [PreservesLimit (cospan π π) G]
    {a : C(G.obj Z, X)}
    (ha : a ∘ (G.map (pullback.fst _ _)) = a ∘ (G.map (pullback.snd π π))) :
    Function.FactorsThrough a (G.map π) := by
  intro x y hxy
let xy : G.obj (pullback π π) := (PreservesPullback.iso G π π).inv
    (TopCat.pullbackIsoProdSubtype (G.map π) (G.map π)).inv ⟨(x, y), hxy⟩
  have ha' := congr_fun ha xy
  dsimp at ha'
  have h₁ : forall y, G.map (pullback.fst _ _) ((PreservesPullback.iso G π π).inv y) =
      pullback.fst (G.map π) (G.map π) y := by
    simp only [← PreservesPullback.iso_inv_fst]; intro y; rfl
  have h₂ : forall y, G.map (pullback.snd _ _) ((PreservesPullback.iso G π π).inv y) =
      pullback.snd (G.map π) (G.map π) y := by
    simp only [← PreservesPullback.iso_inv_snd]; intro y; rfl
  rw [h₁]; rw [h₂]; rw [TopCat.pullbackIsoProdSubtype_inv_fst_apply]; rw [TopCat.pullbackIsoProdSubtype_inv_snd_apply] at ha'
  simpa using ha'

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equalizerCondition_yonedaPresheaf` / 定理 `equalizerCondition_yonedaPresheaf`

English:
theorem equalizerCondition_yonedaPresheaf
  proof: by
  apply EqualizerCondition.mk
  intro Z B π _ _
  refine ⟨fun a b h => ?_, fun ⟨a, ha⟩ => ?_⟩
  · simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, TypeCat.Fun.coe_mk,
      Set.coe_ofPred, mapToEqualizer, Set.mem_ofPred_eq, ConcreteCategory.hom_ofHom,
      Subtype.mk.injEq, mk.injEq] at h
  

中文:
定理 equalizerCondition_yonedaPresheaf
  证明: by
  apply EqualizerCondition.mk
  intro Z B π _ _
  refine ⟨fun a b h => ?_, fun ⟨a, ha⟩ => ?_⟩
  · simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, TypeCat.Fun.coe_mk,
      Set.coe_ofPred, mapToEqualizer, Set.mem_ofPred_eq, ConcreteCategory.hom_ofHom,
      Subtype.mk.injEq, mk.injEq] at h
  

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, EqualizerCondition, EqualizerCondition.mk, Quiver, Quiver.Hom.unop_op, Set.coe_ofPred, Set.mem_ofPred_eq, Subtype, Subtype.mk.injEq, TypeCat, TypeCat.Fun.coe_mk, coe_mk, coe_ofPred, congr_fun, hom_ofHom, mapToEqualizer, mem_ofPred_eq, mk.in, mk.injEq
-/
theorem equalizerCondition_yonedaPresheaf
    [forall (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) G]
    (hq : forall (Z B : C) (π : Z ⟶ B) [EffectiveEpi π], IsQuotientMap (G.map π)) :
      EqualizerCondition (yonedaPresheaf G X) := by
  apply EqualizerCondition.mk
  intro Z B π _ _
  refine ⟨fun a b h => ?_, fun ⟨a, ha⟩ => ?_⟩
  · simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, TypeCat.Fun.coe_mk,
      Set.coe_ofPred, mapToEqualizer, Set.mem_ofPred_eq, ConcreteCategory.hom_ofHom,
      Subtype.mk.injEq, mk.injEq] at h
    simp only [yonedaPresheaf, unop_op]
    ext x
    obtain ⟨y, hy⟩ := (hq Z B π).surjective x
    rw [← hy]
    exact congr_fun h y
  · simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, mk.injEq, Set.mem_ofPred_eq] at ha
    simp only [yonedaPresheaf, comp, Quiver.Hom.unop_op, TypeCat.Fun.coe_mk,
      Set.coe_ofPred, mapToEqualizer, Set.mem_ofPred_eq, ConcreteCategory.hom_ofHom,
      Subtype.mk.injEq]
    simp only [yonedaPresheaf, unop_op] at a
    refine ⟨(hq Z B π).lift a (factorsThrough_of_pullbackCondition G X ha), ?_⟩
    congr 1
    exact DFunLike.ext'_iff.mp ((hq Z B π).lift_comp a (factorsThrough_of_pullbackCondition G X ha))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesFiniteCoproducts
  signature: G] :
  body: have := preservesFiniteProducts_op G
  ⟨fun _ => comp_preservesLimitsOfShape G.op (yonedaPresheaf' X)⟩

中文:
实例 [PreservesFiniteCoproducts
  签名: G] :
  定义体: have := preservesFiniteProducts_op G
  ⟨fun _ => comp_preservesLimitsOfShape G.op (yonedaPresheaf' X)⟩

Depends on / 依赖: G.op, comp_preservesLimitsOfShape, preservesFiniteProducts_op, yonedaPresheaf
-/
noncomputable instance [PreservesFiniteCoproducts G] :
    PreservesFiniteProducts (yonedaPresheaf G X) :=
  have := preservesFiniteProducts_op G
  ⟨fun _ => comp_preservesLimitsOfShape G.op (yonedaPresheaf' X)⟩

section

variable (P : TopCat.{u} -> Prop) (X : TopCat.{max u w})
    [CompHausLike.HasExplicitFiniteCoproducts.{0} P] [CompHausLike.HasExplicitPullbacks.{u} P]
    (hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Surjective f)

/--
The sheaf on `CompHausLike P` of continuous maps to a topological space.
-/
@[simps! obj_obj obj_map]
/--
Definition of `TopCat.toSheafCompHausLike` / `TopCat.toSheafCompHausLike` 的定义

English:
definition TopCat.toSheafCompHausLike
  signature: :
  body: CompHausLike.preregular hs
    Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj := yonedaPresheaf.{u, max u w} (CompHausLike.compHausLikeToTop.{u} P) X
  property := by
    have := CompHausLike.preregular hs
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizer

中文:
定义 TopCat.toSheafCompHausLike
  签名: :
  定义体: CompHausLike.preregular hs
    Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj := yonedaPresheaf.{u, max u w} (CompHausLike.compHausLikeToTop.{u} P) X
  property := by
    have := CompHausLike.preregular hs
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizer

Depends on / 依赖: CompHausLike, CompHausLike.preregular, preregular
-/
def TopCat.toSheafCompHausLike :
    have := CompHausLike.preregular hs
    Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj := yonedaPresheaf.{u, max u w} (CompHausLike.compHausLikeToTop.{u} P) X
  property := by
    have := CompHausLike.preregular hs
    rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    refine ⟨inferInstance, ?_⟩
    apply +allowSynthFailures equalizerCondition_yonedaPresheaf
      (CompHausLike.compHausLikeToTop.{u} P) X
    intro Z B π he
    exact .of_surjective_continuous (hs _ he) π.hom.hom.continuous

/--
`TopCat.toSheafCompHausLike` yields a functor from `TopCat.{max u w}` to
`Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))`.
-/
@[simps]
/--
Definition of `topCatToSheafCompHausLike` / `topCatToSheafCompHausLike` 的定义

English:
definition topCatToSheafCompHausLike
  signature: :
  body: CompHausLike.preregular hs
    TopCat.{max u w} ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj X := X.toSheafCompHausLike P hs
  map f := ⟨⟨fun _ => ↾fun g => f.hom.comp g, by aesop⟩⟩

中文:
定义 topCatToSheafCompHausLike
  签名: :
  定义体: CompHausLike.preregular hs
    TopCat.{max u w} ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj X := X.toSheafCompHausLike P hs
  map f := ⟨⟨fun _ => ↾fun g => f.hom.comp g, by aesop⟩⟩

Depends on / 依赖: CompHausLike, CompHausLike.preregular, preregular
-/
noncomputable def topCatToSheafCompHausLike :
    have := CompHausLike.preregular hs
    TopCat.{max u w} ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj X := X.toSheafCompHausLike P hs
  map f := ⟨⟨fun _ => ↾fun g => f.hom.comp g, by aesop⟩⟩

end

/--
Definition of `TopCat.toCondensedSet` / `TopCat.toCondensedSet` 的定义

English:
abbreviation TopCat.toCondensedSet
  signature: (X : TopCat.{u + 1})
  body: toSheafCompHausLike.{u + 1} _ X (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

中文:
缩写 TopCat.toCondensedSet
  签名: (X : TopCat.{u + 1})
  定义体: toSheafCompHausLike.{u + 1} _ X (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, effectiveEpi_tfae, toSheafCompHausLike
-/
noncomputable abbrev TopCat.toCondensedSet (X : TopCat.{u + 1}) : CondensedSet.{u} :=
  toSheafCompHausLike.{u + 1} _ X (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/--
Definition of `topCatToCondensedSet` / `topCatToCondensedSet` 的定义

English:
abbreviation topCatToCondensedSet
  signature: : TopCat.{u + 1} ⥤ CondensedSet.{u}
  body: topCatToSheafCompHausLike.{u + 1} _ (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

中文:
缩写 topCatToCondensedSet
  签名: : TopCat.{u + 1} ⥤ CondensedSet.{u}
  定义体: topCatToSheafCompHausLike.{u + 1} _ (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, effectiveEpi_tfae, topCatToSheafCompHausLike
-/
noncomputable abbrev topCatToCondensedSet : TopCat.{u + 1} ⥤ CondensedSet.{u} :=
  topCatToSheafCompHausLike.{u + 1} _ (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)
