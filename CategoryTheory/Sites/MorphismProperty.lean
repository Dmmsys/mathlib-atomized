/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# The site induced by a morphism property

Let `C` be a category with pullbacks and `P` be a multiplicative morphism property which is
stable under base change. Then `P` induces a pretopology, where coverings are given by presieves
whose elements satisfy `P`.

Standard examples of pretopologies in algebraic geometry, such as the étale site, are obtained from
this construction by intersecting with the pretopology of surjective families.

-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

namespace MorphismProperty

variable {P Q : MorphismProperty C}

/--
Definition of `precoverage` / `precoverage` 的定义

English:
definition precoverage
  signature: (P : MorphismProperty C)
  body: {S | forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> P f}

@[simp]

中文:
定义 precoverage
  签名: (P : Morphism命题erty C)
  定义体: {S | forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> P f}

@[simp]
-/
def precoverage (P : MorphismProperty C) : Precoverage C where
  coverings X := {S | forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> P f}

@[simp]
/--
lemma `ofArrows_mem_precoverage` / 引理 `ofArrows_mem_precoverage`

English:
lemma ofArrows_mem_precoverage
  given: {X : C} {ι : Type*} {Y : ι -> C} {f : forall i, Y i ⟶ X}
  proof: ⟨fun h i => h ⟨i⟩, fun h _ g ⟨i⟩ => h i⟩

@[simp, grind =]

中文:
引理 ofArrows_mem_precoverage
  条件: {X : C} {ι : 类型} {Y : ι -> C} {f : 对任意 i, Y i ⟶ X}
  证明: ⟨fun h i => h ⟨i⟩, fun h _ g ⟨i⟩ => h i⟩

@[simp, grind =]
-/
lemma ofArrows_mem_precoverage {X : C} {ι : Type*} {Y : ι -> C} {f : forall i, Y i ⟶ X} :
    .ofArrows Y f in precoverage P X ↔ forall i, P (f i) :=
  ⟨fun h i => h ⟨i⟩, fun h _ g ⟨i⟩ => h i⟩

@[simp, grind =]
/--
lemma `singleton_mem_precoverage` / 引理 `singleton_mem_precoverage`

English:
lemma singleton_mem_precoverage
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  simp [← Presieve.ofArrows_pUnit.{0}]

中文:
引理 singleton_mem_precoverage
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  simp [← Presieve.ofArrows_pUnit.{0}]

Depends on / 依赖: Presieve, Presieve.ofArrows_pUnit, ofArrows_pUnit
-/
lemma singleton_mem_precoverage {X Y : C} (f : X ⟶ Y) :
    .singleton f in precoverage P Y ↔ P f := by
  simp [← Presieve.ofArrows_pUnit.{0}]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsIdentities]
  signature: [P.RespectsIso]
  body: fun ⟨⟩ => P.of_isIso f

中文:
实例 [P.ContainsIdentities]
  签名: [P.RespectsIso]
  定义体: fun ⟨⟩ => P.of_isIso f

Depends on / 依赖: P.of_isIso, of_isIso
-/
instance [P.ContainsIdentities] [P.RespectsIso] : P.precoverage.HasIsos where
  mem_coverings_of_isIso f _ _ _ := fun ⟨⟩ => P.of_isIso f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderBaseChange]
  signature: : P.precoverage.IsStableUnderBaseChange where
  body: by
    obtain ⟨i⟩ := hg
    exact P.of_isPullback (h i).flip (hf ⟨i⟩)

中文:
实例 [P.IsStableUnderBaseChange]
  签名: : P.precoverage.IsStableUnderBaseChange where
  定义体: by
    obtain ⟨i⟩ := hg
    exact P.of_isPullback (h i).flip (hf ⟨i⟩)

Depends on / 依赖: P.of_isPullback, of_isPullback
-/
instance [P.IsStableUnderBaseChange] : P.precoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf T g W p₁ p₂ h Z g hg := by
    obtain ⟨i⟩ := hg
    exact P.of_isPullback (h i).flip (hf ⟨i⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderComposition]
  signature: : P.precoverage.IsStableUnderComposition where
  body: by
    intro ⟨i⟩
    exact P.comp_mem _ _ (hg _ ⟨i.2⟩) (hf ⟨i.1⟩)

中文:
实例 [P.IsStableUnderComposition]
  签名: : P.precoverage.IsStableUnderComposition where
  定义体: by
    intro ⟨i⟩
    exact P.comp_mem _ _ (hg _ ⟨i.2⟩) (hf ⟨i.1⟩)

Depends on / 依赖: P.comp_mem, comp_mem
-/
instance [P.IsStableUnderComposition] : P.precoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg Z p := by
    intro ⟨i⟩
    exact P.comp_mem _ _ (hg _ ⟨i.2⟩) (hf ⟨i.1⟩)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Precoverage.Small.{w} P.precoverage
  body: by
    constructor
    use PEmpty, PEmpty.elim
    simp

中文:
实例 :
  签名: Precoverage.Small.{w} P.precoverage
  定义体: by
    constructor
    use PEmpty, PEmpty.elim
    simp

Depends on / 依赖: PEmpty, PEmpty.elim
-/
instance : Precoverage.Small.{w} P.precoverage where
  zeroHypercoverSmall E := by
    constructor
    use PEmpty, PEmpty.elim
    simp

/--
lemma `precoverage_monotone` / 引理 `precoverage_monotone`

English:
lemma precoverage_monotone
  given: (hPQ : P <= Q)
  statement: precoverage P <= precoverage Q
  proof: fun _ _ hR _ _ hg => hPQ _ (hR hg)

中文:
引理 precoverage_monotone
  条件: (hPQ : P <= Q)
  结论: precoverage P <= precoverage Q
  证明: fun _ _ hR _ _ hg => hPQ _ (hR hg)
-/
lemma precoverage_monotone (hPQ : P <= Q) : precoverage P <= precoverage Q :=
  fun _ _ hR _ _ hg => hPQ _ (hR hg)

variable (P Q) in
/--
lemma `precoverage_inf` / 引理 `precoverage_inf`

English:
lemma precoverage_inf
  statement: precoverage (P ⊓ Q) = precoverage P ⊓ precoverage Q
  proof: by
  ext X R
  exact ⟨fun hS => ⟨fun _ _ hf => (hS hf).left, fun _ _ hf => (hS hf).right⟩,
    fun h => fun _ _ hf => ⟨h.left hf, h.right hf⟩⟩

@[simp, grind .]

中文:
引理 precoverage_inf
  结论: precoverage (P ⊓ Q) = precoverage P ⊓ precoverage Q
  证明: by
  ext X R
  exact ⟨fun hS => ⟨fun _ _ hf => (hS hf).left, fun _ _ hf => (hS hf).right⟩,
    fun h => fun _ _ hf => ⟨h.left hf, h.right hf⟩⟩

@[simp, grind .]

Depends on / 依赖: h.left, h.right
-/
lemma precoverage_inf : precoverage (P ⊓ Q) = precoverage P ⊓ precoverage Q := by
  ext X R
  exact ⟨fun hS => ⟨fun _ _ hf => (hS hf).left, fun _ _ hf => (hS hf).right⟩,
    fun h => fun _ _ hf => ⟨h.left hf, h.right hf⟩⟩

@[simp, grind .]
/--
lemma `bot_mem_precoverage` / 引理 `bot_mem_precoverage`

English:
lemma bot_mem_precoverage
  given: (X : C)
  statement: ⊥ in precoverage P X
  proof: fun _ _ h => h.elim

中文:
引理 bot_mem_precoverage
  条件: (X : C)
  结论: ⊥ in precoverage P X
  证明: fun _ _ h => h.elim

Depends on / 依赖: h.elim
-/
lemma bot_mem_precoverage (X : C) : ⊥ in precoverage P X := fun _ _ h => h.elim

/--
lemma `comap_precoverage` / 引理 `comap_precoverage`

English:
lemma comap_precoverage
  given: {D : Type*} [Category* D] (P : MorphismProperty D) (F : C ⥤ D)
  proof: by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

中文:
引理 comap_precoverage
  条件: {D : 类型} [Category* D] (P : Morphism命题erty D) (F : C ⥤ D)
  证明: by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

Depends on / 依赖: R.exists_eq_ofArrows, exists_eq_ofArrows
-/
lemma comap_precoverage {D : Type*} [Category* D] (P : MorphismProperty D) (F : C ⥤ D) :
    P.precoverage.comap F = (P.inverseImage F).precoverage := by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

/-- If `P` is stable under base change, this is the coverage on `C` where covering presieves
are those where every morphism satisfies `P`. -/
@[simps toPrecoverage]
/--
Definition of `coverage` / `coverage` 的定义

English:
definition coverage
  signature: (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks]
  body: precoverage P
  pullback X Y f S hS := by
    have : S.HasPullbacks f := ⟨fun {W} h hh => P.hasPullback _ (hS hh)⟩
    refine ⟨S.pullbackArrows f, ?_, .pullbackArrows f S⟩
    intro Z g ⟨W, a, h⟩
    have := S.hasPullback f h
    exact P.pullback_snd _ _ (hS h)

中文:
定义 coverage
  签名: (P : Morphism命题erty C) [P.IsStableUnderBaseChange] [P.HasPullbacks]
  定义体: precoverage P
  pullback X Y f S hS := by
    have : S.HasPullbacks f := ⟨fun {W} h hh => P.hasPullback _ (hS hh)⟩
    refine ⟨S.pullbackArrows f, ?_, .pullbackArrows f S⟩
    intro Z g ⟨W, a, h⟩
    have := S.hasPullback f h
    exact P.pullback_snd _ _ (hS h)

Depends on / 依赖: precoverage
-/
def coverage (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks] :
    Coverage C where
  __ := precoverage P
  pullback X Y f S hS := by
    have : S.HasPullbacks f := ⟨fun {W} h hh => P.hasPullback _ (hS hh)⟩
    refine ⟨S.pullbackArrows f, ?_, .pullbackArrows f S⟩
    intro Z g ⟨W, a, h⟩
    have := S.hasPullback f h
    exact P.pullback_snd _ _ (hS h)

/--
Definition of `grothendieckTopology` / `grothendieckTopology` 的定义

English:
abbreviation grothendieckTopology
  signature: (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks]
  body: P.coverage.toGrothendieck

中文:
缩写 grothendieckTopology
  签名: (P : Morphism命题erty C) [P.IsStableUnderBaseChange] [P.HasPullbacks]
  定义体: P.coverage.toGrothendieck

Depends on / 依赖: P.coverage.toGrothendieck, coverage, toGrothendieck
-/
abbrev grothendieckTopology (P : MorphismProperty C) [P.IsStableUnderBaseChange] [P.HasPullbacks] :
    GrothendieckTopology C :=
  P.coverage.toGrothendieck

section HasPullbacks

variable [P.IsStableUnderBaseChange] [HasPullbacks C]

/-- If `P` is a multiplicative morphism property which is stable under base change on a category
`C` with pullbacks, then `P` induces a pretopology, where coverings are given by presieves whose
elements satisfy `P`. -/
@[simps! toPrecoverage]
/--
Definition of `pretopology` / `pretopology` 的定义

English:
definition pretopology
  signature: (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  body: (precoverage P).toPretopology

中文:
定义 pretopology
  签名: (P : Morphism命题erty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  定义体: (precoverage P).toPretopology

Depends on / 依赖: precoverage, toPretopology
-/
def pretopology (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange] :
    Pretopology C :=
  (precoverage P).toPretopology

/--
lemma `coverage_eq_toCoverage_pretopology` / 引理 `coverage_eq_toCoverage_pretopology`

English:
lemma coverage_eq_toCoverage_pretopology
  given: [P.IsMultiplicative]
  proof: rfl

中文:
引理 coverage_eq_toCoverage_pretopology
  条件: [P.IsMultiplicative]
  证明: rfl
-/
lemma coverage_eq_toCoverage_pretopology [P.IsMultiplicative] :
    P.coverage = P.pretopology.toCoverage := rfl

/--
lemma `grothendieckTopology_eq_toGrothendieck_pretopology` / 引理 `grothendieckTopology_eq_toGrothendieck_pretopology`

English:
lemma grothendieckTopology_eq_toGrothendieck_pretopology
  given: [P.IsMultiplicative]
  proof: by
  rw [grothendieckTopology]; rw [coverage_eq_toCoverage_pretopology]; rw [Pretopology.toGrothendieck_toCoverage]

中文:
引理 grothendieckTopology_eq_toGrothendieck_pretopology
  条件: [P.IsMultiplicative]
  证明: by
  rw [grothendieckTopology]; rw [coverage_eq_toCoverage_pretopology]; rw [Pretopology.toGrothendieck_toCoverage]

Depends on / 依赖: Pretopology, Pretopology.toGrothendieck_toCoverage, coverage_eq_toCoverage_pretopology, grothendieckTopology, toGrothendieck_toCoverage
-/
lemma grothendieckTopology_eq_toGrothendieck_pretopology [P.IsMultiplicative] :
    P.grothendieckTopology = P.pretopology.toGrothendieck := by
  rw [grothendieckTopology]; rw [coverage_eq_toCoverage_pretopology]; rw [Pretopology.toGrothendieck_toCoverage]

section

variable {P Q : MorphismProperty C}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/--
lemma `pretopology_monotone` / 引理 `pretopology_monotone`

English:
lemma pretopology_monotone
  given: (hPQ : P <= Q)
  statement: P.pretopology <= Q.pretopology
  proof: precoverage_monotone hPQ

中文:
引理 pretopology_monotone
  条件: (hPQ : P <= Q)
  结论: P.pretopology <= Q.pretopology
  证明: precoverage_monotone hPQ

Depends on / 依赖: precoverage_monotone
-/
lemma pretopology_monotone (hPQ : P <= Q) : P.pretopology <= Q.pretopology :=
  precoverage_monotone hPQ

variable (P Q) in
/--
lemma `pretopology_inf` / 引理 `pretopology_inf`

English:
lemma pretopology_inf
  statement: (P ⊓ Q).pretopology = P.pretopology ⊓ Q.pretopology
  proof: by
  ext : 1
  simp only [pretopology_toPrecoverage, precoverage_inf]
  rfl

中文:
引理 pretopology_inf
  结论: (P ⊓ Q).pretopology = P.pretopology ⊓ Q.pretopology
  证明: by
  ext : 1
  simp only [pretopology_toPrecoverage, precoverage_inf]
  rfl

Depends on / 依赖: precoverage_inf, pretopology_toPrecoverage
-/
lemma pretopology_inf : (P ⊓ Q).pretopology = P.pretopology ⊓ Q.pretopology := by
  ext : 1
  simp only [pretopology_toPrecoverage, precoverage_inf]
  rfl

end

end HasPullbacks

end MorphismProperty

/--
Definition of `Precoverage.morphismProperty` / `Precoverage.morphismProperty` 的定义

English:
definition Precoverage.morphismProperty
  signature: (K : Precoverage C)
  body: fun _ Y f => exists R in K Y, R f

@[simp]

中文:
定义 Precoverage.morphismProperty
  签名: (K : Precoverage C)
  定义体: fun _ Y f => exists R in K Y, R f

@[simp]
-/
def Precoverage.morphismProperty (K : Precoverage C) : MorphismProperty C :=
  fun _ Y f => exists R in K Y, R f

@[simp]
/--
lemma `MorphismProperty.morphismProperty_precoverage` / 引理 `MorphismProperty.morphismProperty_precoverage`

English:
lemma MorphismProperty.morphismProperty_precoverage
  given: (P : MorphismProperty C)
  proof: by
  ext X Y f
  exact ⟨fun ⟨R, hR, hf⟩ => hR hf, fun hf => ⟨.singleton f, by simpa⟩⟩

中文:
引理 MorphismProperty.morphismProperty_precoverage
  条件: (P : Morphism命题erty C)
  证明: by
  ext X Y f
  exact ⟨fun ⟨R, hR, hf⟩ => hR hf, fun hf => ⟨.singleton f, by simpa⟩⟩

Depends on / 依赖: singleton
-/
lemma MorphismProperty.morphismProperty_precoverage (P : MorphismProperty C) :
    P.precoverage.morphismProperty = P := by
  ext X Y f
  exact ⟨fun ⟨R, hR, hf⟩ => hR hf, fun hf => ⟨.singleton f, by simpa⟩⟩

namespace Precoverage

variable {K L : Precoverage C} {P : MorphismProperty C}

/--
lemma `morphismProperty_le_iff_le_precoverage` / 引理 `morphismProperty_le_iff_le_precoverage`

English:
lemma morphismProperty_le_iff_le_precoverage
  proof: ⟨fun hle _ R hR _ _ hf => hle _ ⟨R, hR, hf⟩, fun hle _ _ _ ⟨_, hR, hf⟩ => hle _ hR hf⟩

中文:
引理 morphismProperty_le_iff_le_precoverage
  证明: ⟨fun hle _ R hR _ _ hf => hle _ ⟨R, hR, hf⟩, fun hle _ _ _ ⟨_, hR, hf⟩ => hle _ hR hf⟩
-/
lemma morphismProperty_le_iff_le_precoverage :
    K.morphismProperty <= P ↔ K <= P.precoverage :=
  ⟨fun hle _ R hR _ _ hf => hle _ ⟨R, hR, hf⟩, fun hle _ _ _ ⟨_, hR, hf⟩ => hle _ hR hf⟩

/--
lemma `galoisConnection_morphismProperty_precoverage` / 引理 `galoisConnection_morphismProperty_precoverage`

English:
lemma galoisConnection_morphismProperty_precoverage
  proof: @Precoverage.morphismProperty_le_iff_le_precoverage _ _

中文:
引理 galoisConnection_morphismProperty_precoverage
  证明: @Precoverage.morphismProperty_le_iff_le_precoverage _ _

Depends on / 依赖: MorphismProperty, MorphismProperty.precoverage, precoverage
-/
lemma galoisConnection_morphismProperty_precoverage :
    GaloisConnection (Precoverage.morphismProperty (C := C)) MorphismProperty.precoverage :=
  @Precoverage.morphismProperty_le_iff_le_precoverage _ _

/--
lemma `monotone_morphismProperty` / 引理 `monotone_morphismProperty`

English:
lemma monotone_morphismProperty
  statement: Monotone (Precoverage.morphismProperty (C := C))
  proof: Precoverage.galoisConnection_morphismProperty_precoverage.monotone_l

中文:
引理 monotone_morphismProperty
  结论: Monotone (Precoverage.morphism命题erty (C := C))
  证明: Precoverage.galoisConnection_morphismProperty_precoverage.monotone_l
-/
lemma monotone_morphismProperty : Monotone (Precoverage.morphismProperty (C := C)) :=
  Precoverage.galoisConnection_morphismProperty_precoverage.monotone_l

/--
lemma `le_precoverage_morphismProperty` / 引理 `le_precoverage_morphismProperty`

English:
lemma le_precoverage_morphismProperty
  statement: K <= K.morphismProperty.precoverage
  proof: galoisConnection_morphismProperty_precoverage.le_u_l _

@[simp]

中文:
引理 le_precoverage_morphismProperty
  结论: K <= K.morphism命题erty.precoverage
  证明: galoisConnection_morphismProperty_precoverage.le_u_l _

@[simp]

Depends on / 依赖: galoisConnection_morphismProperty_precoverage, galoisConnection_morphismProperty_precoverage.le_u_l, le_u_l
-/
lemma le_precoverage_morphismProperty : K <= K.morphismProperty.precoverage :=
  galoisConnection_morphismProperty_precoverage.le_u_l _

@[simp]
/--
lemma `morphismProperty_bot` / 引理 `morphismProperty_bot`

English:
lemma morphismProperty_bot
  statement: (⊥ : Precoverage C).morphismProperty = ⊥
  proof: Precoverage.galoisConnection_morphismProperty_precoverage.l_bot

@[simp]

中文:
引理 morphismProperty_bot
  结论: (⊥ : Precoverage C).morphism命题erty = ⊥
  证明: Precoverage.galoisConnection_morphismProperty_precoverage.l_bot

@[simp]

Depends on / 依赖: Precoverage, Precoverage.galoisConnection_morphismProperty_precoverage.l_bot, galoisConnection_morphismProperty_precoverage, l_bot
-/
lemma morphismProperty_bot : (⊥ : Precoverage C).morphismProperty = ⊥ :=
  Precoverage.galoisConnection_morphismProperty_precoverage.l_bot

@[simp]
/--
lemma `morphismProperty_sup` / 引理 `morphismProperty_sup`

English:
lemma morphismProperty_sup
  statement: (K ⊔ L).morphismProperty = K.morphismProperty ⊔ L.morphismProperty
  proof: Precoverage.galoisConnection_morphismProperty_precoverage.l_sup

中文:
引理 morphismProperty_sup
  结论: (K ⊔ L).morphism命题erty = K.morphism命题erty ⊔ L.morphism命题erty
  证明: Precoverage.galoisConnection_morphismProperty_precoverage.l_sup

Depends on / 依赖: Precoverage, Precoverage.galoisConnection_morphismProperty_precoverage.l_sup, galoisConnection_morphismProperty_precoverage, l_sup
-/
lemma morphismProperty_sup : (K ⊔ L).morphismProperty = K.morphismProperty ⊔ L.morphismProperty :=
  Precoverage.galoisConnection_morphismProperty_precoverage.l_sup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.HasIsos]
  signature: : K.morphismProperty.ContainsIdentities where
  body: ⟨.singleton (𝟙 X), K.mem_coverings_of_isIso _, by simp⟩

@[simp, grind .]

中文:
实例 [K.HasIsos]
  签名: : K.morphism命题erty.ContainsIdentities where
  定义体: ⟨.singleton (𝟙 X), K.mem_coverings_of_isIso _, by simp⟩

@[simp, grind .]

Depends on / 依赖: K.mem_coverings_of_isIso, mem_coverings_of_isIso, singleton
-/
instance [K.HasIsos] : K.morphismProperty.ContainsIdentities where
  id_mem X := ⟨.singleton (𝟙 X), K.mem_coverings_of_isIso _, by simp⟩

@[simp, grind .]
/--
lemma `ZeroHypercover.morphismProperty` / 引理 `ZeroHypercover.morphismProperty`

English:
lemma ZeroHypercover.morphismProperty
  given: {X : C} {E : ZeroHypercover.{w} K X} (i : E.I₀)
  proof: ⟨_, E.mem₀, ⟨i⟩⟩

中文:
引理 ZeroHypercover.morphismProperty
  条件: {X : C} {E : ZeroHypercover.{w} K X} (i : E.I₀)
  证明: ⟨_, E.mem₀, ⟨i⟩⟩

Depends on / 依赖: E.mem
-/
lemma ZeroHypercover.morphismProperty {X : C} {E : ZeroHypercover.{w} K X} (i : E.I₀) :
    K.morphismProperty (E.f i) :=
  ⟨_, E.mem₀, ⟨i⟩⟩

end Precoverage

@[simp]
/--
lemma `MorphismProperty.precoverage_top` / 引理 `MorphismProperty.precoverage_top`

English:
lemma MorphismProperty.precoverage_top
  statement: (⊤ : MorphismProperty C).precoverage = ⊤
  proof: Precoverage.galoisConnection_morphismProperty_precoverage.u_top

中文:
引理 MorphismProperty.precoverage_top
  结论: (⊤ : Morphism命题erty C).precoverage = ⊤
  证明: Precoverage.galoisConnection_morphismProperty_precoverage.u_top

Depends on / 依赖: Precoverage, Precoverage.galoisConnection_morphismProperty_precoverage.u_top, galoisConnection_morphismProperty_precoverage, u_top
-/
lemma MorphismProperty.precoverage_top : (⊤ : MorphismProperty C).precoverage = ⊤ :=
  Precoverage.galoisConnection_morphismProperty_precoverage.u_top

end CategoryTheory
