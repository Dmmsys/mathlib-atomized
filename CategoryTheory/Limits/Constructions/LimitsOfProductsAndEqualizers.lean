/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

## TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

@[expose] public section


open CategoryTheory

open Opposite

namespace CategoryTheory.Limits

universe w v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]

-- We hide the "implementation details" inside a namespace
namespace HasLimitOfHasProductsOfHasEqualizers

variable {F : J ⥤ C} {c₁ : Fan F.obj} {c₂ : Fan fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2}
  (s t : c₁.pt ⟶ c₂.pt)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
@[simps]
/--
Definition of `buildLimit` / `buildLimit` 的定义

English:
definition buildLimit
  body: i.pt
  π :=
    { app := fun _ => i.ι ≫ c₁.π.app ⟨_⟩
      naturality := fun j₁ j₂ f => by
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← hs ⟨⟨_]; rw [_⟩]; rw [f⟩]; rw [i.condition_assoc]; rw [ht] }

中文:
定义 buildLimit
  定义体: i.pt
  π :=
    { app := fun _ => i.ι ≫ c₁.π.app ⟨_⟩
      naturality := fun j₁ j₂ f => by
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← hs ⟨⟨_]; rw [_⟩]; rw [f⟩]; rw [i.condition_assoc]; rw [ht] }

Depends on / 依赖: i.pt
-/
def buildLimit
    (hs : forall f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
    (ht : forall f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
    (i : Fork s t) : Cone F where
  pt := i.pt
  π :=
    { app := fun _ => i.ι ≫ c₁.π.app ⟨_⟩
      naturality := fun j₁ j₂ f => by
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← hs ⟨⟨_]; rw [_⟩]; rw [f⟩]; rw [i.condition_assoc]; rw [ht] }

variable
  (hs : forall f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : forall f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
  {i : Fork s t}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `buildIsLimit` / `buildIsLimit` 的定义

English:
definition buildIsLimit
  signature: (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i)
  body: by
    refine hi.lift (Fork.ofι ?_ ?_)
    · refine t₁.lift (Fan.mk _ fun j => ?_)
      apply q.π.app j
    · apply t₂.hom_ext
      intro ⟨j⟩
      simp [hs, ht]
  uniq q m w := hi.hom_ext (i.equalizer_ext (t₁.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

中文:
定义 buildIsLimit
  签名: (t₁ : 是极限 c₁) (t₂ : 是极限 c₂) (hi : 是极限 i)
  定义体: by
    refine hi.lift (Fork.ofι ?_ ?_)
    · refine t₁.lift (Fan.mk _ fun j => ?_)
      apply q.π.app j
    · apply t₂.hom_ext
      intro ⟨j⟩
      simp [hs, ht]
  uniq q m w := hi.hom_ext (i.equalizer_ext (t₁.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

Depends on / 依赖: Fan.mk, Fork.of, equalizer_ext, hi.hom_ext, hi.lift, hom_ext, i.equalizer_ext
-/
def buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit s t hs ht i) where
  lift q := by
    refine hi.lift (Fork.ofι ?_ ?_)
    · refine t₁.lift (Fan.mk _ fun j => ?_)
      apply q.π.app j
    · apply t₂.hom_ext
      intro ⟨j⟩
      simp [hs, ht]
  uniq q m w := hi.hom_ext (i.equalizer_ext (t₁.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

end HasLimitOfHasProductsOfHasEqualizers

open HasLimitOfHasProductsOfHasEqualizers

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitConeOfEqualizerAndProduct` / `limitConeOfEqualizerAndProduct` 的定义

English:
definition limitConeOfEqualizerAndProduct
  signature: (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
  body: _
  isLimit :=
    buildIsLimit (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨_⟩ ≫ F.map f.2)
      (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨f.1.2⟩) (by simp) (by simp)
      (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)

中文:
定义 limitConeOfEqualizerAndProduct
  签名: (F : J ⥤ C) [有极限 (离散.functor F.obj)]
  定义体: _
  isLimit :=
    buildIsLimit (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨_⟩ ≫ F.map f.2)
      (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨f.1.2⟩) (by simp) (by simp)
      (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)
-/
noncomputable def limitConeOfEqualizerAndProduct (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    LimitCone F where
  cone := _
  isLimit :=
    buildIsLimit (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨_⟩ ≫ F.map f.2)
      (Pi.lift fun f => limit.π (Discrete.functor F.obj) ⟨f.1.2⟩) (by simp) (by simp)
      (limit.isLimit _) (limit.isLimit _) (limit.isLimit _)

/--
theorem `hasLimit_of_equalizer_and_product` / 定理 `hasLimit_of_equalizer_and_product`

English:
theorem hasLimit_of_equalizer_and_product
  statement: (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
  proof: HasLimit.mk (limitConeOfEqualizerAndProduct F)

中文:
定理 hasLimit_of_equalizer_and_product
  结论: (F : J ⥤ C) [有极限 (离散.functor F.obj)]
  证明: HasLimit.mk (limitConeOfEqualizerAndProduct F)

Depends on / 依赖: HasLimit, HasLimit.mk, limitConeOfEqualizerAndProduct
-/
theorem hasLimit_of_equalizer_and_product (F : J ⥤ C) [HasLimit (Discrete.functor F.obj)]
    [HasLimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] [HasEqualizers C] :
    HasLimit F :=
  HasLimit.mk (limitConeOfEqualizerAndProduct F)

/--
Definition of `limitSubobjectProduct` / `limitSubobjectProduct` 的定义

English:
definition limitSubobjectProduct
  signature: [HasLimitsOfSize.{w, w} C] (F : J ⥤ C)
  body: have := hasFiniteLimits_of_hasLimitsOfSize C
  (limit.isoLimitCone (limitConeOfEqualizerAndProduct F)).hom ≫ equalizer.ι _ _

中文:
定义 limitSubobjectProduct
  签名: [有LimitsOfSize.{w, w} C] (F : J ⥤ C)
  定义体: have := hasFiniteLimits_of_hasLimitsOfSize C
  (limit.isoLimitCone (limitConeOfEqualizerAndProduct F)).hom ≫ equalizer.ι _ _

Depends on / 依赖: equalizer, hasFiniteLimits_of_hasLimitsOfSize, isoLimitCone, limit.isoLimitCone, limitConeOfEqualizerAndProduct
-/
noncomputable def limitSubobjectProduct [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    limit F ⟶ ∏ᶜ fun j => F.obj j :=
  have := hasFiniteLimits_of_hasLimitsOfSize C
  (limit.isoLimitCone (limitConeOfEqualizerAndProduct F)).hom ≫ equalizer.ι _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `limitSubobjectProduct_mono` / 实例 `limitSubobjectProduct_mono`

English:
instance limitSubobjectProduct_mono
  signature: [HasLimitsOfSize.{w, w} C] (F : J ⥤ C)
  body: mono_comp _ _

中文:
实例 limitSubobjectProduct_mono
  签名: [有LimitsOfSize.{w, w} C] (F : J ⥤ C)
  定义体: mono_comp _ _

Depends on / 依赖: mono_comp
-/
instance limitSubobjectProduct_mono [HasLimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Mono (limitSubobjectProduct F) :=
  mono_comp _ _

/-- Any category with products and equalizers has all limits. -/
@[stacks 002N]
/--
theorem `has_limits_of_hasEqualizers_and_products` / 定理 `has_limits_of_hasEqualizers_and_products`

English:
theorem has_limits_of_hasEqualizers_and_products
  given: [HasProducts.{w} C] [HasEqualizers C]
  proof: { has_limits_of_shape :=
    fun _ _ => { has_limit := fun F => hasLimit_of_equalizer_and_product F } }

中文:
定理 has_limits_of_hasEqualizers_and_products
  条件: [HasProducts.{w} C] [HasEqualizers C]
  证明: { has_limits_of_shape :=
    fun _ _ => { has_limit := fun F => hasLimit_of_equalizer_and_product F } }

Depends on / 依赖: hasLimit_of_equalizer_and_product, has_limit, has_limits_of_shape
-/
theorem has_limits_of_hasEqualizers_and_products [HasProducts.{w} C] [HasEqualizers C] :
    HasLimitsOfSize.{w, w} C :=
  { has_limits_of_shape :=
    fun _ _ => { has_limit := fun F => hasLimit_of_equalizer_and_product F } }

/-- Any category with finite products and equalizers has all finite limits. -/
@[stacks 002O]
/--
theorem `hasFiniteLimits_of_hasEqualizers_and_finite_products` / 定理 `hasFiniteLimits_of_hasEqualizers_and_finite_products`

English:
theorem hasFiniteLimits_of_hasEqualizers_and_finite_products
  statement: [HasFiniteProducts C]
  proof: { has_limit := fun F => hasLimit_of_equalizer_and_product F }

中文:
定理 hasFiniteLimits_of_hasEqualizers_and_finite_products
  结论: [有FiniteProducts C]
  证明: { has_limit := fun F => hasLimit_of_equalizer_and_product F }

Depends on / 依赖: hasLimit_of_equalizer_and_product, has_limit
-/
theorem hasFiniteLimits_of_hasEqualizers_and_finite_products [HasFiniteProducts C]
    [HasEqualizers C] : HasFiniteLimits C where
  out _ := { has_limit := fun F => hasLimit_of_equalizer_and_product F }

variable {D : Type u₂} [Category.{v₂} D]

section

variable [HasLimitsOfShape (Discrete J) C] [HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C]
  [HasEqualizers C]

variable (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
  -- [PreservesFiniteProducts G]
  [PreservesLimitsOfShape (Discrete.{w} J) G]
  [PreservesLimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesLimit_of_preservesEqualizers_and_product` / 引理 `preservesLimit_of_preservesEqualizers_and_product`

English:
lemma preservesLimit_of_preservesEqualizers_and_product
  proof: by
    let P := ∏ᶜ K.obj
    let Q := ∏ᶜ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.2
    let s : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨_⟩ ≫ K.map f.2
    let t : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨f.1.2⟩
    let I := equalizer s t
    let i : I ⟶ 

中文:
引理 preservesLimit_of_preservesEqualizers_and_product
  证明: by
    let P := ∏ᶜ K.obj
    let Q := ∏ᶜ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.2
    let s : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨_⟩ ≫ K.map f.2
    let t : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨f.1.2⟩
    let I := equalizer s t
    let i : I ⟶ 

Depends on / 依赖: Discrete, Discrete.functor, IsLimit, IsLimit.ofIsoLimit, K.map, K.obj, Pi.lift, buildIsLimit, equalizer, functor, isLimit, limit.isLimit, ofIsoLimit, p.fst, p.snd, preservesLimit_of_preserves_limit_cone
-/
lemma preservesLimit_of_preservesEqualizers_and_product :
    PreservesLimitsOfShape J G where
  preservesLimit {K} := by
    let P := ∏ᶜ K.obj
    let Q := ∏ᶜ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.2
    let s : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨_⟩ ≫ K.map f.2
    let t : P ⟶ Q := Pi.lift fun f => limit.π (Discrete.functor K.obj) ⟨f.1.2⟩
    let I := equalizer s t
    let i : I ⟶ P := equalizer.ι s t
    apply preservesLimit_of_preserves_limit_cone
        (buildIsLimit s t (by simp [P, s]) (by simp [P, t]) (limit.isLimit _)
          (limit.isLimit _) (limit.isLimit _))
    apply IsLimit.ofIsoLimit (buildIsLimit _ _ _ _ _ _ _) _
    · exact Fan.mk _ fun j => G.map (Pi.π _ j)
    · exact Fan.mk (G.obj Q) fun f => G.map (Pi.π _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp [P, Q, s, Fan.mk]
      simp only [← G.map_comp, limit.lift_π]
      congr
    · intro f
      dsimp [P, Q, t, Fan.mk]
      simp only [← G.map_comp, limit.lift_π]
      dsimp
    · apply Fork.ofι (G.map i)
      rw [← G.map_comp]; rw [← G.map_comp]
      apply congrArg G.map
      exact equalizer.condition s t
    · apply isLimitOfHasProductOfPreservesLimit
    · apply isLimitOfHasProductOfPreservesLimit
    · apply isLimitForkMapOfIsLimit
      apply equalizerIsEqualizer
    · refine Cone.ext (Iso.refl _) ?_
      intro j; dsimp [P, Q, I, i]; simp

end

/--
lemma `preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts` / 引理 `preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts`

English:
lemma preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts
  statement: [HasEqualizers C]
  proof: by
    intros
    apply preservesLimit_of_preservesEqualizers_and_product

中文:
引理 preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts
  结论: [HasEqualizers C]
  证明: by
    intros
    apply preservesLimit_of_preservesEqualizers_and_product

Depends on / 依赖: intros, preservesLimit_of_preservesEqualizers_and_product
-/
lemma preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts [HasEqualizers C]
    [HasFiniteProducts C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [PreservesFiniteProducts G] : PreservesFiniteLimits G where
  preservesFiniteLimits := by
    intros
    apply preservesLimit_of_preservesEqualizers_and_product


/--
lemma `preservesLimits_of_preservesEqualizers_and_products` / 引理 `preservesLimits_of_preservesEqualizers_and_products`

English:
lemma preservesLimits_of_preservesEqualizers_and_products
  statement: [HasEqualizers C]
  proof: preservesLimit_of_preservesEqualizers_and_product G

中文:
引理 preservesLimits_of_preservesEqualizers_and_products
  结论: [HasEqualizers C]
  证明: preservesLimit_of_preservesEqualizers_and_product G

Depends on / 依赖: preservesLimit_of_preservesEqualizers_and_product
-/
lemma preservesLimits_of_preservesEqualizers_and_products [HasEqualizers C]
    [HasProducts.{w} C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingParallelPair G]
    [forall J, PreservesLimitsOfShape (Discrete.{w} J) G] : PreservesLimitsOfSize.{w, w} G where
  preservesLimitsOfShape := preservesLimit_of_preservesEqualizers_and_product G

section

variable [HasLimitsOfShape (Discrete J) D] [HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) D]
  [HasEqualizers D]

variable (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesLimitsOfShape WalkingParallelPair G]
  [CreatesLimitsOfShape (Discrete.{w} J) G]
  [CreatesLimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

attribute [local instance] preservesLimit_of_preservesEqualizers_and_product in
/-- If a functor creates equalizers and the appropriate products, it creates limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfShapeOfCreatesEqualizersAndProducts` / `createsLimitsOfShapeOfCreatesEqualizersAndProducts` 的定义

English:
definition createsLimitsOfShapeOfCreatesEqualizersAndProducts
  signature: :
  body: have : HasLimitsOfShape (Discrete J) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasEqualizers C :=
      hasLimitsOfShape_of_h

中文:
定义 createsLimitsOfShapeOfCreatesEqualizersAndProducts
  签名: :
  定义体: have : HasLimitsOfShape (Discrete J) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasEqualizers C :=
      hasLimitsOfShape_of_h

Depends on / 依赖: Discrete, HasEqualizers, HasLimit, HasLimitsOfShape, createsLimitOfReflectsIsomorphismsOfPreserves, hasLimit_of_equalizer_and_product, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
noncomputable def createsLimitsOfShapeOfCreatesEqualizersAndProducts :
    CreatesLimitsOfShape J G where
  CreatesLimit {K} :=
    have : HasLimitsOfShape (Discrete J) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasEqualizers C :=
      hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
    have : HasLimit K := hasLimit_of_equalizer_and_product K
    createsLimitOfReflectsIsomorphismsOfPreserves

end

/-- If a functor creates equalizers and finite products, it creates finite limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts` / `createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts` 的定义

English:
definition createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts
  signature: [HasEqualizers D]
  body: createsLimitsOfShapeOfCreatesEqualizersAndProducts G

中文:
定义 createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts
  签名: [HasEqualizers D]
  定义体: createsLimitsOfShapeOfCreatesEqualizersAndProducts G

Depends on / 依赖: createsLimitsOfShapeOfCreatesEqualizersAndProducts
-/
noncomputable def createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts [HasEqualizers D]
    [HasFiniteProducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape WalkingParallelPair G]
    [CreatesFiniteProducts G] : CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ := createsLimitsOfShapeOfCreatesEqualizersAndProducts G

/-- If a functor creates equalizers and products, it creates limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsLimitsOfSizeOfCreatesEqualizersAndProducts` / `createsLimitsOfSizeOfCreatesEqualizersAndProducts` 的定义

English:
definition createsLimitsOfSizeOfCreatesEqualizersAndProducts
  signature: [HasEqualizers D]
  body: createsLimitsOfShapeOfCreatesEqualizersAndProducts G

中文:
定义 createsLimitsOfSizeOfCreatesEqualizersAndProducts
  签名: [HasEqualizers D]
  定义体: createsLimitsOfShapeOfCreatesEqualizersAndProducts G

Depends on / 依赖: createsLimitsOfShapeOfCreatesEqualizersAndProducts
-/
noncomputable def createsLimitsOfSizeOfCreatesEqualizersAndProducts [HasEqualizers D]
    [HasProducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape WalkingParallelPair G] [forall J, CreatesLimitsOfShape (Discrete.{w} J) G] :
    CreatesLimitsOfSize.{w, w} G where
  CreatesLimitsOfShape := createsLimitsOfShapeOfCreatesEqualizersAndProducts G

/--
theorem `hasFiniteLimits_of_hasTerminal_and_pullbacks` / 定理 `hasFiniteLimits_of_hasTerminal_and_pullbacks`

English:
theorem hasFiniteLimits_of_hasTerminal_and_pullbacks
  given: [HasTerminal C] [HasPullbacks C]
  proof: @hasFiniteLimits_of_hasEqualizers_and_finite_products C _
    (@hasFiniteProducts_of_has_binary_and_terminal C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
    (@hasEqualizers_of_hasPullbacks_and_binary_products C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C

中文:
定理 hasFiniteLimits_of_hasTerminal_and_pullbacks
  条件: [有终止 C] [有Pullbacks C]
  证明: @hasFiniteLimits_of_hasEqualizers_and_finite_products C _
    (@hasFiniteProducts_of_has_binary_and_terminal C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
    (@hasEqualizers_of_hasPullbacks_and_binary_products C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C

Depends on / 依赖: hasBinaryProducts_of_hasTerminal_and_pullbacks, hasEqualizers_of_hasPullbacks_and_binary_products, hasFiniteLimits_of_hasEqualizers_and_finite_products, hasFiniteProducts_of_has_binary_and_terminal
-/
theorem hasFiniteLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasFiniteLimits C :=
  @hasFiniteLimits_of_hasEqualizers_and_finite_products C _
    (@hasFiniteProducts_of_has_binary_and_terminal C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)
    (@hasEqualizers_of_hasPullbacks_and_binary_products C _
      (hasBinaryProducts_of_hasTerminal_and_pullbacks C) inferInstance)

/--
lemma `preservesFiniteLimits_of_preservesTerminal_and_pullbacks` / 引理 `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`

English:
lemma preservesFiniteLimits_of_preservesTerminal_and_pullbacks
  statement: [HasTerminal C]
  proof: by
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks G
  have : PreservesLimitsOfShape WalkingParallelPair G :=
    preservesEqualizers_of_preservesPull

中文:
引理 preservesFiniteLimits_of_preservesTerminal_and_pullbacks
  结论: [有终止 C]
  证明: by
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks G
  have : PreservesLimitsOfShape WalkingParallelPair G :=
    preservesEqualizers_of_preservesPull

Depends on / 依赖: Discrete, HasFiniteLimits, PreservesFiniteProducts, PreservesLimitsOfShape, WalkingPair, WalkingParallelPair, hasFiniteLimits_of_hasTerminal_and_pullbacks, of_preserves_binary_and_terminal, preservesBinaryProducts_of_preservesTerminal_and_pullbacks, preservesEqualizers_of_preservesPullbacks_and_binaryProducts, preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts
-/
lemma preservesFiniteLimits_of_preservesTerminal_and_pullbacks [HasTerminal C]
    [HasPullbacks C] (G : C ⥤ D) [PreservesLimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesLimitsOfShape WalkingCospan G] : PreservesFiniteLimits G := by
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks G
  have : PreservesLimitsOfShape WalkingParallelPair G :=
    preservesEqualizers_of_preservesPullbacks_and_binaryProducts G
  have : PreservesFiniteProducts G := .of_preserves_binary_and_terminal _
  exact preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts G

attribute [local instance] preservesFiniteLimits_of_preservesTerminal_and_pullbacks in
/-- If a functor creates terminal objects and pullbacks, it creates finite limits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating limits" in the literature, and whether or not the condition can be dropped seems to depend
on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsFiniteLimitsOfCreatesTerminalAndPullbacks` / `createsFiniteLimitsOfCreatesTerminalAndPullbacks` 的定义

English:
definition createsFiniteLimitsOfCreatesTerminalAndPullbacks
  signature: [HasTerminal D]
  body: { CreatesLimit :=
        have : HasTerminal C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasPullbacks C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
        createsL

中文:
定义 createsFiniteLimitsOfCreatesTerminalAndPullbacks
  签名: [有终止 D]
  定义体: { CreatesLimit :=
        have : HasTerminal C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasPullbacks C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
        createsL

Depends on / 依赖: CreatesLimit, HasFiniteLimits, HasPullbacks, HasTerminal, createsLimitOfReflectsIsomorphismsOfPreserves, hasFiniteLimits_of_hasTerminal_and_pullbacks, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
noncomputable def createsFiniteLimitsOfCreatesTerminalAndPullbacks [HasTerminal D]
    [HasPullbacks D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesLimitsOfShape (Discrete.{0} PEmpty) G] [CreatesLimitsOfShape WalkingCospan G] :
    CreatesFiniteLimits G where
  createsFiniteLimits _ _ _ :=
    { CreatesLimit :=
        have : HasTerminal C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasPullbacks C := hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape G
        have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
        createsLimitOfReflectsIsomorphismsOfPreserves }

/-!
We now dualize the above constructions, resorting to copy-paste.
-/


-- We hide the "implementation details" inside a namespace
namespace HasColimitOfHasCoproductsOfHasCoequalizers

variable {F : J ⥤ C} {c₁ : Cofan fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1} {c₂ : Cofan F.obj}
  (s t : c₁.pt ⟶ c₂.pt)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) Given the appropriate coproduct and coequalizer cocones,
build the cocone for `F` which is colimiting if the given cocones are also.
-/
@[simps]
/--
Definition of `buildColimit` / `buildColimit` 的定义

English:
definition buildColimit
  body: i.pt
  ι :=
    { app := fun _ => c₂.ι.app ⟨_⟩ ≫ i.π
      naturality := fun j₁ j₂ f => by
        dsimp
        have reassoced (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} {h : _ ⟶ W} :
          c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
            simp only [← Category.as

中文:
定义 buildColimit
  定义体: i.pt
  ι :=
    { app := fun _ => c₂.ι.app ⟨_⟩ ≫ i.π
      naturality := fun j₁ j₂ f => by
        dsimp
        have reassoced (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} {h : _ ⟶ W} :
          c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
            simp only [← Category.as

Depends on / 依赖: i.pt
-/
def buildColimit
    (hs : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
    (ht : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
    (i : Cofork s t) : Cocone F where
  pt := i.pt
  ι :=
    { app := fun _ => c₂.ι.app ⟨_⟩ ≫ i.π
      naturality := fun j₁ j₂ f => by
        dsimp
        have reassoced (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} {h : _ ⟶ W} :
          c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
            simp only [← Category.assoc, eq_whisker (hs f)]
        rw [Category.comp_id]; rw [← reassoced ⟨⟨_]; rw [_⟩]; rw [f⟩]; rw [i.condition]; rw [← Category.assoc]; rw [ht] }

variable
  (hs : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : forall f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
  {i : Cofork s t}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `buildIsColimit` / `buildIsColimit` 的定义

English:
definition buildIsColimit
  signature: (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i)
  body: by
    refine hi.desc (Cofork.ofπ ?_ ?_)
    · refine t₂.desc (Cofan.mk _ fun j => ?_)
      apply q.ι.app j
    · apply t₁.hom_ext
      intro ⟨j⟩
      have reassoced_s (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h :

中文:
定义 buildIsColimit
  签名: (t₁ : 是余极限 c₁) (t₂ : 是余极限 c₂) (hi : 是余极限 i)
  定义体: by
    refine hi.desc (Cofork.ofπ ?_ ?_)
    · refine t₂.desc (Cofan.mk _ fun j => ?_)
      apply q.ι.app j
    · apply t₁.hom_ext
      intro ⟨j⟩
      have reassoced_s (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h :

Depends on / 依赖: Category, Category.assoc, Cofan.mk, Cofork, Cofork.of, F.map, eq_whisker, f.fst.fst, f.fst.snd, f.snd, hi.desc, hom_ext, p.fst, p.snd, reassoced_s, reassoced_t
-/
def buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) :
    IsColimit (buildColimit s t hs ht i) where
  desc q := by
    refine hi.desc (Cofork.ofπ ?_ ?_)
    · refine t₂.desc (Cofan.mk _ fun j => ?_)
      apply q.ι.app j
    · apply t₁.hom_ext
      intro ⟨j⟩
      have reassoced_s (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ s ≫ h = F.map f.snd ≫ c₂.ι.app ⟨f.fst.snd⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (hs f)
      have reassoced_t (f : (p : J × J) × (p.fst ⟶ p.snd)) {W : C} (h : _ ⟶ W) :
        c₁.ι.app ⟨f⟩ ≫ t ≫ h = c₂.ι.app ⟨f.fst.fst⟩ ≫ h := by
          simp only [← Category.assoc]
          apply eq_whisker (ht f)
      simp [reassoced_s, reassoced_t]
  uniq q m w := hi.hom_ext (i.coequalizer_ext (t₂.hom_ext fun j => by simpa using w j.1))
  fac s j := by simp

end HasColimitOfHasCoproductsOfHasCoequalizers

open HasColimitOfHasCoproductsOfHasCoequalizers

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitCoconeOfCoequalizerAndCoproduct` / `colimitCoconeOfCoequalizerAndCoproduct` 的定义

English:
definition colimitCoconeOfCoequalizerAndCoproduct
  signature: (F : J ⥤ C)
  body: _
  isColimit :=
    buildIsColimit (Sigma.desc fun f => F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩)
      (Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩) (by simp) (by simp)
      (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)

中文:
定义 colimitCoconeOfCoequalizerAndCoproduct
  签名: (F : J ⥤ C)
  定义体: _
  isColimit :=
    buildIsColimit (Sigma.desc fun f => F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩)
      (Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩) (by simp) (by simp)
      (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
-/
noncomputable def colimitCoconeOfCoequalizerAndCoproduct (F : J ⥤ C)
    [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : ColimitCocone F where
  cocone := _
  isColimit :=
    buildIsColimit (Sigma.desc fun f => F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩)
      (Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩) (by simp) (by simp)
      (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)

/--
theorem `hasColimit_of_coequalizer_and_coproduct` / 定理 `hasColimit_of_coequalizer_and_coproduct`

English:
theorem hasColimit_of_coequalizer_and_coproduct
  statement: (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
  proof: HasColimit.mk (colimitCoconeOfCoequalizerAndCoproduct F)

中文:
定理 hasColimit_of_coequalizer_and_coproduct
  结论: (F : J ⥤ C) [有余极限 (离散.functor F.obj)]
  证明: HasColimit.mk (colimitCoconeOfCoequalizerAndCoproduct F)

Depends on / 依赖: HasColimit, HasColimit.mk, colimitCoconeOfCoequalizerAndCoproduct
-/
theorem hasColimit_of_coequalizer_and_coproduct (F : J ⥤ C) [HasColimit (Discrete.functor F.obj)]
    [HasColimit (Discrete.functor fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1)]
    [HasCoequalizers C] : HasColimit F :=
  HasColimit.mk (colimitCoconeOfCoequalizerAndCoproduct F)

/--
Definition of `colimitQuotientCoproduct` / `colimitQuotientCoproduct` 的定义

English:
definition colimitQuotientCoproduct
  signature: [HasColimitsOfSize.{w, w} C] (F : J ⥤ C)
  body: have := hasFiniteColimits_of_hasColimitsOfSize C
  coequalizer.π _ _ ≫ (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)).inv

中文:
定义 colimitQuotientCoproduct
  签名: [有余limitsOfSize.{w, w} C] (F : J ⥤ C)
  定义体: have := hasFiniteColimits_of_hasColimitsOfSize C
  coequalizer.π _ _ ≫ (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)).inv

Depends on / 依赖: coequalizer, colimit, colimit.isoColimitCocone, colimitCoconeOfCoequalizerAndCoproduct, hasFiniteColimits_of_hasColimitsOfSize, isoColimitCocone
-/
noncomputable def colimitQuotientCoproduct [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    ∐ (fun j => F.obj j) ⟶ colimit F :=
  have := hasFiniteColimits_of_hasColimitsOfSize C
  coequalizer.π _ _ ≫ (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)).inv

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `colimitQuotientCoproduct_epi` / 实例 `colimitQuotientCoproduct_epi`

English:
instance colimitQuotientCoproduct_epi
  signature: [HasColimitsOfSize.{w, w} C] (F : J ⥤ C)
  body: epi_comp _ _

中文:
实例 colimitQuotientCoproduct_epi
  签名: [有余limitsOfSize.{w, w} C] (F : J ⥤ C)
  定义体: epi_comp _ _

Depends on / 依赖: epi_comp
-/
instance colimitQuotientCoproduct_epi [HasColimitsOfSize.{w, w} C] (F : J ⥤ C) :
    Epi (colimitQuotientCoproduct F) :=
  epi_comp _ _

/-- Any category with coproducts and coequalizers has all colimits. -/
@[stacks 002P]
/--
theorem `has_colimits_of_hasCoequalizers_and_coproducts` / 定理 `has_colimits_of_hasCoequalizers_and_coproducts`

English:
theorem has_colimits_of_hasCoequalizers_and_coproducts
  given: [HasCoproducts.{w} C] [HasCoequalizers C]
  proof: fun _ _ =>
      { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

中文:
定理 has_colimits_of_hasCoequalizers_and_coproducts
  条件: [HasCoproducts.{w} C] [HasCoequalizers C]
  证明: fun _ _ =>
      { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }
-/
theorem has_colimits_of_hasCoequalizers_and_coproducts [HasCoproducts.{w} C] [HasCoequalizers C] :
    HasColimitsOfSize.{w, w} C where
  has_colimits_of_shape := fun _ _ =>
      { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

/-- Any category with finite coproducts and coequalizers has all finite colimits. -/
@[stacks 002Q]
/--
theorem `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` / 定理 `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`

English:
theorem hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
  statement: [HasFiniteCoproducts C]
  proof: { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

中文:
定理 hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
  结论: [有FiniteCoproducts C]
  证明: { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

Depends on / 依赖: hasColimit_of_coequalizer_and_coproduct, has_colimit
-/
theorem hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts [HasFiniteCoproducts C]
    [HasCoequalizers C] : HasFiniteColimits C where
  out _ := { has_colimit := fun F => hasColimit_of_coequalizer_and_coproduct F }

section

variable [HasColimitsOfShape (Discrete.{w} J) C]
  [HasColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) C] [HasCoequalizers C]

variable (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
  [PreservesColimitsOfShape (Discrete.{w} J) G]
  [PreservesColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesColimit_of_preservesCoequalizers_and_coproduct` / 引理 `preservesColimit_of_preservesCoequalizers_and_coproduct`

English:
lemma preservesColimit_of_preservesCoequalizers_and_coproduct
  proof: by
    let P := ∐ K.obj
    let Q := ∐ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.1
    let s : Q ⟶ P := Sigma.desc fun f => K.map f.2 ≫ colimit.ι (Discrete.functor K.obj) ⟨_⟩
    let t : Q ⟶ P := Sigma.desc fun f => colimit.ι (Discrete.functor K.obj) ⟨f.1.1⟩
    let I := coequalizer s t
    le

中文:
引理 preservesColimit_of_preservesCoequalizers_and_coproduct
  证明: by
    let P := ∐ K.obj
    let Q := ∐ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.1
    let s : Q ⟶ P := Sigma.desc fun f => K.map f.2 ≫ colimit.ι (Discrete.functor K.obj) ⟨_⟩
    let t : Q ⟶ P := Sigma.desc fun f => colimit.ι (Discrete.functor K.obj) ⟨f.1.1⟩
    let I := coequalizer s t
    le

Depends on / 依赖: Discrete, Discrete.functor, IsColimit, IsColimit.ofI, K.map, K.obj, Sigma.desc, buildIsColimit, coequalizer, colimit, colimit.isColimit, functor, isColimit, p.fst, p.snd, preservesColimit_of_preserves_colimit_cocone
-/
lemma preservesColimit_of_preservesCoequalizers_and_coproduct :
    PreservesColimitsOfShape J G where
  preservesColimit {K} := by
    let P := ∐ K.obj
    let Q := ∐ fun f : Σ p : J × J, p.fst ⟶ p.snd => K.obj f.1.1
    let s : Q ⟶ P := Sigma.desc fun f => K.map f.2 ≫ colimit.ι (Discrete.functor K.obj) ⟨_⟩
    let t : Q ⟶ P := Sigma.desc fun f => colimit.ι (Discrete.functor K.obj) ⟨f.1.1⟩
    let I := coequalizer s t
    let i : P ⟶ I := coequalizer.π s t
    apply preservesColimit_of_preserves_colimit_cocone
        (buildIsColimit s t (by simp [P, s]) (by simp [P, t]) (colimit.isColimit _)
          (colimit.isColimit _) (colimit.isColimit _))
    apply IsColimit.ofIsoColimit (buildIsColimit _ _ _ _ _ _ _) _
    · refine Cofan.mk (G.obj Q) fun j => G.map ?_
      apply Sigma.ι _ j
    -- fun j => G.map (Sigma.ι _ j)
    · exact Cofan.mk _ fun f => G.map (Sigma.ι _ f)
    · apply G.map s
    · apply G.map t
    · intro f
      dsimp [P, Q, s, Cofan.mk]
      simp only [← G.map_comp, colimit.ι_desc]
      congr
    · intro f
      dsimp [P, Q, t, Cofan.mk]
      simp only [← G.map_comp, colimit.ι_desc]
      dsimp
    · refine Cofork.ofπ (G.map i) ?_
      rw [← G.map_comp]; rw [← G.map_comp]
      apply congrArg G.map
      apply coequalizer.condition
    · apply isColimitOfHasCoproductOfPreservesColimit
    · apply isColimitOfHasCoproductOfPreservesColimit
    · apply isColimitCoforkMapOfIsColimit
      apply coequalizerIsCoequalizer
    refine Cocone.ext (Iso.refl _) ?_
    dsimp [i]
    simp

end

/--
lemma `preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts` / 引理 `preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts`

English:
lemma preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
  proof: by
    intro J sJ fJ
    apply preservesColimit_of_preservesCoequalizers_and_coproduct

中文:
引理 preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
  证明: by
    intro J sJ fJ
    apply preservesColimit_of_preservesCoequalizers_and_coproduct

Depends on / 依赖: preservesColimit_of_preservesCoequalizers_and_coproduct
-/
lemma preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    [HasCoequalizers C] [HasFiniteCoproducts C] (G : C ⥤ D)
    [PreservesColimitsOfShape WalkingParallelPair G]
    [PreservesFiniteCoproducts G] : PreservesFiniteColimits G where
  preservesFiniteColimits := by
    intro J sJ fJ
    apply preservesColimit_of_preservesCoequalizers_and_coproduct

/--
lemma `preservesColimits_of_preservesCoequalizers_and_coproducts` / 引理 `preservesColimits_of_preservesCoequalizers_and_coproducts`

English:
lemma preservesColimits_of_preservesCoequalizers_and_coproducts
  statement: [HasCoequalizers C]
  proof: preservesColimit_of_preservesCoequalizers_and_coproduct G

中文:
引理 preservesColimits_of_preservesCoequalizers_and_coproducts
  结论: [HasCoequalizers C]
  证明: preservesColimit_of_preservesCoequalizers_and_coproduct G

Depends on / 依赖: preservesColimit_of_preservesCoequalizers_and_coproduct
-/
lemma preservesColimits_of_preservesCoequalizers_and_coproducts [HasCoequalizers C]
    [HasCoproducts.{w} C] (G : C ⥤ D) [PreservesColimitsOfShape WalkingParallelPair G]
    [forall J, PreservesColimitsOfShape (Discrete.{w} J) G] : PreservesColimitsOfSize.{w, w} G where
  preservesColimitsOfShape := preservesColimit_of_preservesCoequalizers_and_coproduct G

section

variable [HasColimitsOfShape (Discrete J) D]
  [HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) D] [HasCoequalizers D]

variable (G : C ⥤ D) [G.ReflectsIsomorphisms] [CreatesColimitsOfShape WalkingParallelPair G]
  [CreatesColimitsOfShape (Discrete.{w} J) G]
  [CreatesColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) G]

attribute [local instance] preservesColimit_of_preservesCoequalizers_and_coproduct in
/-- If a functor creates coequalizers and the appropriate coproducts, it creates colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts` / `createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts` 的定义

English:
definition createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts
  signature: :
  body: have : HasColimitsOfShape (Discrete J) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasCoequalizers C :=
      has

中文:
定义 createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts
  签名: :
  定义体: have : HasColimitsOfShape (Discrete J) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasCoequalizers C :=
      has

Depends on / 依赖: Discrete, HasCoequalizers, HasColimit, HasColimitsOfShape, createsColimitOfReflectsIsomorphismsOfPreserves, hasColimit_of_coequalizer_and_coproduct, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/
noncomputable def createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts :
    CreatesColimitsOfShape J G where
  CreatesColimit {K} :=
    have : HasColimitsOfShape (Discrete J) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimitsOfShape (Discrete (Σ p : J × J, p.1 ⟶ p.2)) C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasCoequalizers C :=
      hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
    have : HasColimit K := hasColimit_of_coequalizer_and_coproduct K
    createsColimitOfReflectsIsomorphismsOfPreserves

end

/-- If a functor creates coequalizers and finite coproducts, it creates finite colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts` / `createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts` 的定义

English:
definition createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts
  signature: [HasCoequalizers D]
  body: createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

中文:
定义 createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts
  签名: [HasCoequalizers D]
  定义体: createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

Depends on / 依赖: createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts
-/
noncomputable def createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts [HasCoequalizers D]
    [HasFiniteCoproducts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape WalkingParallelPair G]
    [CreatesFiniteCoproducts G] : CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ := createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

/-- If a functor creates coequalizers and coproducts, it creates colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts` / `createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts` 的定义

English:
definition createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts
  signature: [HasCoequalizers D]
  body: createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

中文:
定义 createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts
  签名: [HasCoequalizers D]
  定义体: createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

Depends on / 依赖: createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts
-/
noncomputable def createsColimitsOfSizeOfCreatesCoequalizersAndCoproducts [HasCoequalizers D]
    [HasCoproducts.{w} D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape WalkingParallelPair G]
    [forall J, CreatesColimitsOfShape (Discrete.{w} J) G] : CreatesColimitsOfSize.{w, w} G where
  CreatesColimitsOfShape := createsColimitsOfShapeOfCreatesCoequalizersAndCoproducts G

/--
theorem `hasFiniteColimits_of_hasInitial_and_pushouts` / 定理 `hasFiniteColimits_of_hasInitial_and_pushouts`

English:
theorem hasFiniteColimits_of_hasInitial_and_pushouts
  given: [HasInitial C] [HasPushouts C]
  proof: @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts C _
    (@hasFiniteCoproducts_of_has_binary_and_initial C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
    (@hasCoequalizers_of_hasPushouts_and_binary_coproducts C _
      (hasBinaryCoproducts_of_hasInitial_and_

中文:
定理 hasFiniteColimits_of_hasInitial_and_pushouts
  条件: [HasInitial C] [有Pushouts C]
  证明: @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts C _
    (@hasFiniteCoproducts_of_has_binary_and_initial C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
    (@hasCoequalizers_of_hasPushouts_and_binary_coproducts C _
      (hasBinaryCoproducts_of_hasInitial_and_

Depends on / 依赖: hasBinaryCoproducts_of_hasInitial_and_pushouts, hasCoequalizers_of_hasPushouts_and_binary_coproducts, hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts, hasFiniteCoproducts_of_has_binary_and_initial
-/
theorem hasFiniteColimits_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasFiniteColimits C :=
  @hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts C _
    (@hasFiniteCoproducts_of_has_binary_and_initial C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)
    (@hasCoequalizers_of_hasPushouts_and_binary_coproducts C _
      (hasBinaryCoproducts_of_hasInitial_and_pushouts C) inferInstance)

/--
lemma `preservesFiniteColimits_of_preservesInitial_and_pushouts` / 引理 `preservesFiniteColimits_of_preservesInitial_and_pushouts`

English:
lemma preservesFiniteColimits_of_preservesInitial_and_pushouts
  statement: [HasInitial C]
  proof: by
  have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  have : PreservesColimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryCoproducts_of_preservesInitial_and_pushouts G
  have : PreservesColimitsOfShape (WalkingParallelPair) G :=
      (preservesCoequalizers_of_

中文:
引理 preservesFiniteColimits_of_preservesInitial_and_pushouts
  结论: [HasInitial C]
  证明: by
  have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  have : PreservesColimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryCoproducts_of_preservesInitial_and_pushouts G
  have : PreservesColimitsOfShape (WalkingParallelPair) G :=
      (preservesCoequalizers_of_

Depends on / 依赖: Discrete, HasFiniteColimits, PreservesColimitsOfShape, PreservesFiniteCoproducts, PreservesFiniteCoproducts.of_preserves_binary_and_, WalkingPair, WalkingParallelPair, hasFiniteColimits_of_hasInitial_and_pushouts, of_preserves_binary_and_, preservesBinaryCoproducts_of_preservesInitial_and_pushouts, preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts, preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
-/
lemma preservesFiniteColimits_of_preservesInitial_and_pushouts [HasInitial C]
    [HasPushouts C] (G : C ⥤ D) [PreservesColimitsOfShape (Discrete.{0} PEmpty) G]
    [PreservesColimitsOfShape WalkingSpan G] : PreservesFiniteColimits G := by
  have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  have : PreservesColimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryCoproducts_of_preservesInitial_and_pushouts G
  have : PreservesColimitsOfShape (WalkingParallelPair) G :=
      (preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts G)
  refine
    @preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _ _ _ _ _ _ G _ ?_
  refine ⟨fun _ => ?_⟩
  apply PreservesFiniteCoproducts.of_preserves_binary_and_initial G

attribute [local instance] preservesFiniteColimits_of_preservesInitial_and_pushouts in
/-- If a functor creates initial objects and pushouts, it creates finite colimits.

We additionally require the rather strong condition that the functor reflects isomorphisms. It is
unclear whether the statement remains true without this condition. There are various definitions of
"creating colimits" in the literature, and whether or not the condition can be dropped seems to
depend on the specific definition that is used. -/
@[instance_reducible]
/--
Definition of `createsFiniteColimitsOfCreatesInitialAndPushouts` / `createsFiniteColimitsOfCreatesInitialAndPushouts` 的定义

English:
definition createsFiniteColimitsOfCreatesInitialAndPushouts
  signature: [HasInitial D]
  body: { CreatesColimit :=
        have : HasInitial C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasPushouts C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  

中文:
定义 createsFiniteColimitsOfCreatesInitialAndPushouts
  签名: [HasInitial D]
  定义体: { CreatesColimit :=
        have : HasInitial C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasPushouts C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
  

Depends on / 依赖: CreatesColimit, HasFiniteColimits, HasInitial, HasPushouts, createsColimitOfReflectsIsomorphismsOfPreserves, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape, hasFiniteColimits_of_hasInitial_and_pushouts
-/
noncomputable def createsFiniteColimitsOfCreatesInitialAndPushouts [HasInitial D]
    [HasPushouts D] (G : C ⥤ D) [G.ReflectsIsomorphisms]
    [CreatesColimitsOfShape (Discrete.{0} PEmpty) G] [CreatesColimitsOfShape WalkingSpan G] :
    CreatesFiniteColimits G where
  createsFiniteColimits _ _ _ :=
    { CreatesColimit :=
        have : HasInitial C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasPushouts C := hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape G
        have : HasFiniteColimits C := hasFiniteColimits_of_hasInitial_and_pushouts
        createsColimitOfReflectsIsomorphismsOfPreserves }

end CategoryTheory.Limits
