/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!

# Morphisms of finite presentation

A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation.

A morphism of schemes is of finite presentation if it is both locally of finite presentation and
quasi-compact. We do not provide a separate declaration for this, instead simply assume both
conditions.

We show that these properties are local, and are stable under compositions.

-/

public section


noncomputable section

open CategoryTheory Topology

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation. -/
@[mk_iff]
/-
**AlgebraicGeometry.LocallyOfFinitePresentation** 是 Mathlib 中的一个类，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：LocallyOfFinitePresentation (f : X ⟶ Y) : Prop where finitePresentation_ap
pLE (f) : forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineO
pen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.FinitePresentation  alias Scheme.
Hom.finitePresentation_appLE
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each 
affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation
.
-/
class LocallyOfFinitePresentation (f : X ⟶ Y) : Prop where
  finitePresentation_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FinitePresentation

alias Scheme.Hom.finitePresentation_appLE := LocallyOfFinitePresentation.finitePresentation_appLE

@[deprecated (since := "2026-01-20")]
alias LocallyOfFinitePresentation.finitePresentation_of_affine_subset :=
  Scheme.Hom.finitePresentation_appLE
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasRingHomProperty @LocallyOfFinitePresentation RingHom.FinitePresentation where
  isLocal_ringHomProperty := RingHom.finitePresentation_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFinitePresentation_iff, affineLocally_iff_forall_isAffineOpen]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) locallyOfFinitePresentation_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFinitePresentation f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderComposition @LocallyOfFinitePresentation :=
  HasRingHomProperty.stableUnderComposition RingHom.finitePresentation_stableUnderComposition

@[simp]
/-
**AlgebraicGeometry.LocallyOfFinitePresentation.SpecMap_iff** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.LocallyOfFinitePresentation`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S),   AlgebraicGeometry.LocallyOfFinitePres
entation (AlgebraicGeometry.Spec.map f) ↔     (CommRingCat.Hom.hom f).FinitePres
entation
参数：f : R ⟶ S；AlgebraicGeometry.Spec.map f；CommRingCat.Hom.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFinitePresentationFinit
ePresentation`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOf
FinitePresentation   fun {R S} [CommRing R] [CommRing S] => RingHom.FiniteP…
-/
lemma LocallyOfFinitePresentation.SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    LocallyOfFinitePresentation (Spec.map f) ↔ f.hom.FinitePresentation :=
  HasRingHomProperty.Spec_iff
/-
**AlgebraicGeometry.Scheme.Hom.finitePresentation_appTop** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine
 X] [AlgebraicGeometry.IsAffine Y]   [AlgebraicGeometry.LocallyOfFinitePresentat
ion f],   (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop f)).FinitePr
esentation
参数：f : X ⟶ Y；CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.appTop`：appTop (H : P f) [IsAffine 
X] [IsAffine Y] : Q f.appTop.hom
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFinitePresentationFinit
ePresentation`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOf
FinitePresentation   fun {R S} [CommRing R] [CommRing S] => RingHom.FiniteP…
-/
lemma Scheme.Hom.finitePresentation_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [LocallyOfFinitePresentation f] :
    f.appTop.hom.FinitePresentation :=
  HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ inferInstance
/-
**AlgebraicGeometry.locallyOfFinitePresentation_comp** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：locallyOfFinitePresentation_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶
 Z) [hf : LocallyOfFinitePresentation f] [hg : LocallyOfFinitePresentation g] : 
LocallyOfFinitePresentation (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFinitePrese
ntation`：CategoryTheory.MorphismProperty.IsStableUnderComposition @AlgebraicGeom
etry.LocallyOfFinitePresentation
-/
instance locallyOfFinitePresentation_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFinitePresentation f] [hg : LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg
/-
**AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange** 是 Math
lib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：locallyOfFinitePresentation_isStableUnderBaseChange : MorphismProperty.IsS
tableUnderBaseChange @LocallyOfFinitePresentation
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`：isStableUn
derBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsStableUnderBaseChan
ge
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFinitePresentationFinit
ePresentation`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOf
FinitePresentation   fun {R S} [CommRing R] [CommRing S] => RingHom.FiniteP…
· 使用定理 `RingHom.finitePresentation_isStableUnderBaseChange`：finitePresentation_i
sStableUnderBaseChange : IsStableUnderBaseChange @FinitePresentation
-/
instance locallyOfFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFinitePresentation :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.finitePresentation_isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation] at hf
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType]
  refine affineLocally_le (fun hf ↦ ?_) f hf
  exact RingHom.FiniteType.of_finitePresentation hf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Chevalley's Theorem**: The image of a locally constructible set under a
morphism of finite presentation is locally constructible. -/
@[stacks 054K]
-- `nonrec` is needed for `wlog`
nonrec lemma Scheme.Hom.isLocallyConstructible_image (f : X ⟶ Y)
    [hf : LocallyOfFinitePresentation f] [QuasiCompact f]
    {s : Set X} (hs : IsLocallyConstructible s) :
    IsLocallyConstructible (f '' s) := by
  wlog hY : ∃ R, Y = Spec R
  · refine .of_isOpenCover Y.affineCover.isOpenCover_opensRange fun i ↦ ?_
    have inst : LocallyOfFinitePresentation (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have inst : QuasiCompact (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    convert!
      (this (Y.affineCover.pullbackHom f i)
            (hs.preimage_of_isOpenEmbedding ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding)
            ⟨_, rfl⟩).preimage_of_isOpenEmbedding
        (Y.affineCover.f i).isoOpensRange.inv.isOpenEmbedding
    refine .trans ?_
      ((Scheme.homeoOfIso (Y.affineCover.f i).isoOpensRange).image_eq_preimage_symm _)
    apply Set.image_injective.mpr Subtype.val_injective
    rw [Set.image_preimage_eq_inter_range, ← Set.image_comp, ← Set.image_comp,
      Subtype.range_coe_subtype, Set.ofPred_mem_eq]
    change _ = (Y.affineCover.pullbackHom f i ≫
      (Y.affineCover.f i).isoOpensRange.hom ≫ Opens.ι _).base.hom '' _
    rw [Scheme.Hom.isoOpensRange_hom_ι, Cover.pullbackHom_map, Scheme.Hom.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range]
    simp [IsOpenImmersion.range_pullbackFst, Set.image_inter_preimage]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
    let 𝒰 := X.affineCover.finiteSubcover
    rw [← 𝒰.isOpenCover_opensRange.iUnion_inter s, Set.image_iUnion]
    refine .iUnion fun i ↦ ?_
    have inst : QuasiCompact (𝒰.f i ≫ f) :=
      HasAffineProperty.iff_of_isAffine.mpr (inferInstanceAs (CompactSpace (Spec _)))
    convert! this (hs.preimage_of_isOpenEmbedding (𝒰.f i).isOpenEmbedding) _ (𝒰.f i ≫ f) ⟨_, rfl⟩
    rw [Scheme.Hom.comp_base, ← TopCat.Hom.hom, ← TopCat.Hom.hom, TopCat.hom_comp,
      ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range, coe_opensRange]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hf
  exact (PrimeSpectrum.isConstructible_comap_image hf hs.isConstructible).isLocallyConstructible

/-- **Chevalley's Theorem**: The image of a constructible set under a
morphism of finite presentation into a qcqs scheme is constructible. -/
@[stacks 054J]
/-
**AlgebraicGeometry.Scheme.Hom.isConstructible_image** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFinitePresentation f]   [AlgebraicGeometry.QuasiCompact f] [CompactSpace ↥Y] [Q
uasiSeparatedSpace ↥Y] {s : Set ↥X},   Topology.IsConstructible s → Topology.IsC
onstructible (⇑f '' s)
参数：f : X ⟶ Y；⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsLocallyConstructible.isConstructible`：∀ {X : Type u_2} [inst 
: TopologicalSpace X] {s : Set X} [PrespectralSpace X] [QuasiSeparatedSpace X] [
CompactSpace X],   Topology.IsLocally…
· 使用定理 `AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat`：∀ {X : 
AlgebraicGeometry.Scheme}, PrespectralSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOfFinitePresent
ation f]   [AlgebraicGeometry.QuasiCompact f] {…
· 使用定理 `Topology.IsConstructible.isLocallyConstructible`：∀ {X : Type u_2} [inst 
: TopologicalSpace X] {s : Set X}, Topology.IsConstructible s → Topology.IsLocal
lyConstructible s

--- 原说明 ---
**Chevalley's Theorem**: The image of a constructible set under a
morphism of finite presentation into a qcqs scheme is constructible.
-/
lemma Scheme.Hom.isConstructible_image (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {s : Set X} (hs : IsConstructible s) :
    IsConstructible (f '' s) :=
  (f.isLocallyConstructible_image hs.isLocallyConstructible).isConstructible

@[stacks 054I]
/-
**AlgebraicGeometry.Scheme.Hom.isConstructible_preimage** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) {s : Set ↥Y},   Topology.Is
Constructible s → Topology.IsConstructible (⇑f ⁻¹' s)
参数：f : X ⟶ Y；⇑f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsConstructible.preimage`：∀ {X : Type u_2} {Y : Type u_3} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y} {s : Set Y},   
Continuous f →     (∀ (…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsRetrocompact_iff_isSpectralMap_subtypeVal`：IsRetrocompact_iff_isSpectr
alMap_subtypeVal : IsRetrocompact s ↔ IsSpectralMap (Subtype.val : s -> X)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.quasiCompact_iff_isSpectralMap`：quasiCompact_iff_isSpe
ctralMap : QuasiCompact f ↔ IsSpectralMap f
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
-/
lemma Scheme.Hom.isConstructible_preimage (f : X ⟶ Y) {s : Set Y} (hs : IsConstructible s) :
    IsConstructible (f ⁻¹' s) :=
  hs.preimage f.continuous fun t ht ht' ↦ IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    (quasiCompact_iff_isSpectralMap.mp
    (MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_morphismRestrict f ⟨t, ht⟩)
    (quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp ht'))))

end AlgebraicGeometry

