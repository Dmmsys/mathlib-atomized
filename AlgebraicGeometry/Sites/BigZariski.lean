/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.Topology.Category.TopCat.GrothendieckTopology

/-!
# The big Zariski site of schemes

In this file, we define the Zariski topology, as a Grothendieck topology on the
category `Scheme.{u}`: this is `Scheme.zariskiTopology.{u}`. If `X : Scheme.{u}`,
the Zariski topology on `Over X` can be obtained as `Scheme.zariskiTopology.over X`
(see `CategoryTheory.Sites.Over`.).

TODO:
* If `Y : Scheme.{u}`, define a continuous functor from the category of opens of `Y`
  to `Over Y`, and show that a presheaf on `Over Y` is a sheaf for the Zariski topology
  iff its "restriction" to the topological space `Z` is a sheaf for all `Z : Over Y`.
* We should have good notions of (pre)sheaves of `Type (u + 1)` (e.g. associated
  sheaf functor, pushforward, pullbacks) on `Scheme.{u}` for this topology. However,
  some constructions in the `CategoryTheory.Sites` folder currently assume that
  the site is a small category: this should be generalized. As a result,
  this big Zariski site can considered as a test case of the Grothendieck topology API
  for future applications to étale cohomology.

-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

/-- The Zariski pretopology on the category of schemes. -/
/-
**AlgebraicGeometry.Scheme.zariskiPretopology** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：zariskiPretopology : Pretopology Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Zariski pretopology on the category of schemes.
-/
def zariskiPretopology : Pretopology Scheme.{u} :=
  pretopology @IsOpenImmersion

/-- The Zariski topology on the category of schemes. -/
/-
**AlgebraicGeometry.Scheme.zariskiTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：zariskiTopology : GrothendieckTopology Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Zariski topology on the category of schemes.
-/
abbrev zariskiTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology IsOpenImmersion
/-
**AlgebraicGeometry.Scheme.zariskiTopology_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：zariskiTopology_eq : zariskiTopology.{u} = zariskiPretopology.toGrothendie
ck
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.instHasIsosPrecoverageOfContainsIdentitiesOfRes
pectsIso`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.Co
ntainsIdentities] [P.RespectsIso],   (AlgebraicGeometry.Scheme.precove…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用引理 `CategoryTheory.Precoverage.toGrothendieck_toPretopology_eq_toGrothendiec
k`：toGrothendieck_toPretopology_eq_toGrothendieck [IsStableUnderComposition J] [
IsStableUnderBaseChange J] [Limits.HasPullbacks C] [HasIsos J] …
-/
lemma zariskiTopology_eq : zariskiTopology.{u} = zariskiPretopology.toGrothendieck :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.subcanonical_zariskiTopology** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：subcanonical_zariskiTopology : zariskiTopology.Subcanonical
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`：
of_isSheaf_yoneda_obj (J : GrothendieckTopology C) (h : forall X, Presieve.IsShe
af J (yoneda.obj X)) : Subcanonical J where le_canonical
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBa
seChange`：∀ {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2} C] {J : Ca
tegoryTheory.Precoverage C} [J.HasPullbacks]   [J.IsStableUnderBaseCha…
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksPrecoverageOfHasPullbacks`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.HasPullbacks],  
 (AlgebraicGeometry.Scheme.precoverage P).HasPullbacks
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksIsOpenImmersion`：AlgebraicGeome
try.IsOpenImmersion.HasPullbacks
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.exists_cover_of_mem_pretopology`：∀ {P : Categor
yTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBaseCh
ange]   [inst_1 : P.IsMultiplicative] {X : Alg…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
-/
instance subcanonical_zariskiTopology : zariskiTopology.Subcanonical := by
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro X
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS x hx
  obtain ⟨(𝓤 : OpenCover Y), rfl⟩ := exists_cover_of_mem_pretopology hS
  let e : Y ⟶ X := 𝓤.glueMorphisms (fun j => x (𝓤.f _) (.mk _)) <| by
    intro i j
    apply hx
    exact Limits.pullback.condition
  refine ⟨e, ?_, ?_⟩
  · rintro Z e ⟨j⟩
    dsimp [e]
    rw [𝓤.ι_glueMorphisms]
  · intro e' h
    apply 𝓤.hom_ext
    intro j
    rw [𝓤.ι_glueMorphisms]
    exact h (𝓤.f j) (.mk j)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Scheme.forgetToTop.{u}.IsContinuous zariskiTopology TopCat.grothendieckTopology := by
  rw [zariskiTopology, grothendieckTopology]
  have : (precoverage IsOpenImmersion).PullbacksPreservedBy forgetToTop := by
    refine ⟨fun _ _ hR ↦ ⟨fun _ _ f _ hf _ ↦ ?_⟩⟩
    have : IsOpenImmersion f := hR.2 hf
    infer_instance
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  rw [TopCat.precoverage, Precoverage.comap_inf, precoverage]
  gcongr
  · rw [← Precoverage.comap_comp, forgetToTop_comp_forget]
  · rw [MorphismProperty.comap_precoverage]
    exact MorphismProperty.precoverage_monotone fun X Y f hf ↦ f.isOpenEmbedding

set_option backward.isDefEq.respectTransparency.types false in
/-- A Zariski-`1`-hypercover of a scheme where all components are affine. -/
@[simps! toPreOneHypercover_toPreZeroHypercover]
noncomputable
/-
**AlgebraicGeometry.Scheme.affineOneHypercover** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：affineOneHypercover (X : Scheme.{u}) : zariskiTopology.OneHypercover X
参数：X : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def affineOneHypercover (X : Scheme.{u}) : zariskiTopology.OneHypercover X :=
  .mk'
    (X.affineCover.refineOneHypercover fun i j ↦
      (pullback (X.affineCover.f i) (X.affineCover.f j)).affineCover.toPreZeroHypercover)
    X.affineCover.mem_grothendieckTopology
    fun i j ↦ by simpa using! Cover.mem_grothendieckTopology _

end Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Zariski sheaves preserve products. -/
/-
**AlgebraicGeometry.preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology**
 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology {F : Scheme.{u}
ᵒᵖ ⥤ Type v} {ι : Type*} [Small.{u} ι] [Small.{v} ι] (hF : Presieve.IsSheaf Sche
me.zariskiTopology F) : PreservesLimitsOfShape (Discrete ι) F
参数：hF : Presieve.IsSheaf Scheme.zariskiTopology F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_discrete`：preservesLimit
sOfShape_of_discrete (F : C ⥤ D) [forall (f : J -> C), PreservesLimit (Discrete.
functor f) F] : PreservesLimitsOfShape (Discre…
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用引理 `CategoryTheory.Presieve.preservesProduct_of_isSheafFor`：preservesProduct
_of_isSheafFor (hF' : (ofArrows X c.inj).IsSheafFor F) : PreservesLimit (Discret
e.functor (fun x => op (X x))) F
· 使用定理 `AlgebraicGeometry.instHasInitialScheme`：CategoryTheory.Limits.HasInitial
 AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSheafFor`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X : C} {J : CategoryTheory.GrothendieckTopology C}
   {P : CategoryTheory.Functor C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology`：bot_mem_grothendi
eckTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ in grothendieckTopology P X
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.Limits.CoproductDisjoint.isPullback_of_isInitial`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X : ι → C}   [
CategoryTheory.Limits.CoproductDisjoint X] {c : Categ…
· 使用定理 `CategoryTheory.Limits.CoproductsOfShapeDisjoint.coproductDisjoint`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {ι : Type u_2}   [self
 : CategoryTheory.Limits.CoproductsOfShapeDisjoint C ι]…
· 使用定理 `AlgebraicGeometry.instCoproductsOfShapeDisjointSchemeOfSmall`：∀ {σ : Typ
e v} [Small.{u, v} σ], CategoryTheory.Limits.CoproductsOfShapeDisjoint Algebraic
Geometry.Scheme σ
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Cover.mem_grothendieckTopology`：∀ {P : Category
Theory.MorphismProperty AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}
   (𝒰 : AlgebraicGeometry.Scheme.Cover (Algeb…

--- 原说明 ---
Zariski sheaves preserve products.
-/
lemma preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology {F : Scheme.{u}ᵒᵖ ⥤ Type v}
    {ι : Type*} [Small.{u} ι] [Small.{v} ι] (hF : Presieve.IsSheaf Scheme.zariskiTopology F) :
    PreservesLimitsOfShape (Discrete ι) F := by
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro X
  have (i : ι) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor <| unop ∘ X)) i) :=
    inferInstanceAs <| Mono (Sigma.ι _ _)
  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
      (Sigma.cocone (Discrete.functor <| unop ∘ X)) (coproductIsCoproduct' _) ?_ ?_
  · apply hF.isSheafFor
    convert! (⊥_ Scheme).bot_mem_grothendieckTopology
    rw [eq_bot_iff]
    rintro Y f ⟨g, _, _, ⟨i⟩, _⟩
    exact i.elim
  · intro i j
    exact CoproductDisjoint.isPullback_of_isInitial
      (coproductIsCoproduct' <| Discrete.functor <| unop ∘ X) initialIsInitial
  · exact hF.isSheafFor _ (sigmaOpenCover _).mem_grothendieckTopology

/-- Let `F` be a locally directed diagram of open immersions, i.e., a diagram of schemes
for which whenever `xᵢ ∈ Fᵢ` and `xⱼ ∈ Fⱼ` map to the same `xₖ ∈ Fₖ`, there exists
some `xₗ ∈ Fₗ` that maps to `xᵢ` and `xⱼ` (e.g, the diagram indexing a coproduct).
Then the colimit inclusions are a Zariski covering. -/
/-
**AlgebraicGeometry.ofArrows_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F` be a locally directed diagram of open immersions, i.e., a diagram of sch
emes
for which whenever `xᵢ ∈ Fᵢ` and `xⱼ ∈ Fⱼ` map to the same `xₖ ∈ Fₖ`, there exis
ts
some `xₗ ∈ Fₗ` that maps to `xᵢ` and `xⱼ` (e.g, the diagram indexing a coproduct
).
Then the colimit inclusions are a Zariski covering.
-/
lemma ofArrows_ι_mem_zariskiTopology_of_isColimit {J : Type*} [Category J]
    (F : J ⥤ Scheme.{u}) [∀ {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F.comp Scheme.forget).IsLocallyDirected] [Quiver.IsThin J] [Small.{u} J]
    (c : Cocone F) (hc : IsColimit c) :
    Sieve.ofArrows _ c.ι.app ∈ Scheme.zariskiTopology c.pt := by
  let iso : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  rw [← GrothendieckTopology.pullback_mem_iff_of_isIso (i := iso.inv)]
  apply GrothendieckTopology.superset_covering _ ?_ ?_
  · exact Sieve.ofArrows _ (colimit.ι F)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    exact ⟨_, 𝟙 _, c.ι.app i, ⟨i⟩, by simp [iso]⟩
  · exact (Scheme.IsLocallyDirected.openCover F).mem_grothendieckTopology

-- TODO: This holds more generally if `𝒰.J` is `u`-small and can be generalized
-- when we have `PreExtensive` categories
/-
**AlgebraicGeometry.Scheme.Cover.isSheafFor_sigma_iff** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Cover`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {F : Ca
tegoryTheory.Functor AlgebraicGeometry.Schemeᵒᵖ (Type u_1)}   [inst : AlgebraicG
eometry.IsZariskiLocalAtSource P],   CategoryTheory.Presieve.IsSheaf AlgebraicGe
ometry.Scheme.zariskiTopology F →     ∀ {S : AlgebraicGeometry.Scheme} (𝒰 : Alge
braicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) S)       [Fi
nite 𝒰.I₀],       CategoryTheory.Presieve.IsSheafFor F (CategoryTheory.Presieve.
ofArrows 𝒰.sigma.X 𝒰.sigma.f) ↔         CategoryTheory.Presieve.IsSheafFor F (Ca
tegoryTheory.Presieve.ofArrows 𝒰.X 𝒰.f)
参数：Type u_1；𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precove
rage P) S；CategoryTheory.Presieve.ofArrows 𝒰.sigma.X 𝒰.sigma.f；CategoryTheory.Pr
esieve.ofArrows 𝒰.X 𝒰.f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopo
logy`：preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology {F : Scheme.{u}
ᵒᵖ ⥤ Type v} {ι : Type*} [Small.{u} ι] [Small.{v} ι] (hF : Presiev…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSheafFor_sigmaDesc_iff`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {S : C} {ι : Type u_3} {X : ι → C}   (f
 : (i : ι) → X i ⟶ S) [inst_1 : (Categ…
· 使用定理 `CategoryTheory.Presieve.instHasPairwisePullbacksOfHasPullbacks`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.
Presieve X)   [CategoryTheory.Limits.HasPullbacks C]…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.IsVanKampenColimit.isUniversal`：∀ {J : Type v'} [inst : C
ategoryTheory.Category.{u', v'} J] {C : Type u} [inst_1 : CategoryTheory.Categor
y.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensiv
e C] {ι : Type u_1} [Finite ι]   {F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.instFinitaryExtensiveScheme`：CategoryTheory.FinitaryEx
tensive AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.PreZeroHypercover.presieve₀.eq_1`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {S : C} (E : CategoryTheory.PreZeroHypercover 
S),   E.presieve₀ = CategoryTheory.Pr…
· 使用引理 `AlgebraicGeometry.Scheme.Cover.presieve₀_sigma`：presieve₀_sigma {S : Sch
eme.{u}} (𝒰 : Cover.{v} (precoverage P) S) : 𝒰.sigma.presieve₀ = Presieve.single
ton (Sigma.desc 𝒰.f)
-/
lemma Scheme.Cover.isSheafFor_sigma_iff {P : MorphismProperty Scheme.{u}}
    {F : Scheme.{u}ᵒᵖ ⥤ Type*} [IsZariskiLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [Finite 𝒰.I₀] :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.X 𝒰.sigma.f) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.X 𝒰.f) := by
  have : PreservesLimitsOfShape (Discrete (𝒰.I₀ × 𝒰.I₀)) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  have : PreservesLimitsOfShape (Discrete 𝒰.I₀) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  let c : Cofan 𝒰.X := Cofan.mk _ (Sigma.ι 𝒰.X)
  rw [← Presieve.isSheafFor_sigmaDesc_iff 𝒰.f (coproductIsCoproduct _)
    (FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct _)).isUniversal]
  congr!
  rw [← PreZeroHypercover.presieve₀, 𝒰.presieve₀_sigma]
  rfl

end AlgebraicGeometry

