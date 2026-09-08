/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Universally open morphism

A morphism of schemes `f : X ⟶ Y` is universally open if `X ×[Y] Y' ⟶ Y'` is an open map
for all base change `Y' ⟶ Y`.

We show that being universally open is local at the target, and is stable under compositions and
base changes.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally open if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) an open map.
-/
@[mk_iff]
/-
**AlgebraicGeometry.UniversallyOpen** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is universally open if the base change `X ×[Y]
 Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) an open map.
-/
class UniversallyOpen (f : X ⟶ Y) : Prop where
  universally_isOpenMap : universally (topologically @IsOpenMap) f

@[deprecated (since := "2026-01-20")]
alias UniversallyOpen.out := UniversallyOpen.universally_isOpenMap
/-
**AlgebraicGeometry.Scheme.Hom.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Universa
llyOpen f], IsOpenMap ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.UniversallyOpen.universally_isOpenMap`：∀ {X Y : Algebr
aicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.UniversallyOpen f],   
(AlgebraicGeometry.topologically @IsOpenMap).…
· 使用引理 `CategoryTheory.IsPullback.of_id_snd`：of_id_snd : IsPullback f (𝟙 _) (𝟙 _
) f
-/
lemma Scheme.Hom.isOpenMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyOpen f] :
    IsOpenMap f := UniversallyOpen.universally_isOpenMap _ _ _ IsPullback.of_id_snd

namespace UniversallyOpen

/-
**AlgebraicGeometry.UniversallyOpen.eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.UniversallyOpen`。
形式化陈述：eq : @UniversallyOpen = universally (topologically @IsOpenMap)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.universallyOpen_iff`：∀ {X Y : AlgebraicGeometry.Scheme
} (f : X ⟶ Y),   AlgebraicGeometry.UniversallyOpen f ↔ (AlgebraicGeometry.topolo
gically @IsOpenMap).univers…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq : @UniversallyOpen = universally (topologically @IsOpenMap) := by
  ext X Y f; rw [universallyOpen_iff]
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsOpenImmersion f] : UniversallyOpen f := by
  rw [eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsOpenImmersion f' := MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isOpenEmbedding.isOpenMap
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RespectsIso @UniversallyOpen :=
  eq.symm ▸ inferInstance
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @UniversallyOpen :=
  eq.symm ▸ inferInstance
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderComposition (topologically @IsOpenMap) where
  comp_mem f g hf hg := IsOpenMap.comp (f := f) (g := g) hg hf
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderComposition @UniversallyOpen := by
  rw [eq]
  infer_instance
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyOpen f] [hg : UniversallyOpen g] : UniversallyOpen (f ≫ g) :=
  comp_mem _ _ _ hf hg
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @UniversallyOpen where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.UniversallyOpen.fst** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.UniversallyOpen`。
形式化陈述：fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyOpen g] : Un
iversallyOpen (pullback.fst f g)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pullback_fst`：pullback_fst {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong f] (H :
 P g) : P (pullback.fst f g)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme`：Cat
egoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Universa
llyOpen
-/
instance fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyOpen g] :
    UniversallyOpen (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.UniversallyOpen.snd** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.UniversallyOpen`。
形式化陈述：snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyOpen f] : Un
iversallyOpen (pullback.snd f g)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
· 使用定理 `AlgebraicGeometry.UniversallyOpen.instIsStableUnderBaseChangeScheme`：Cat
egoryTheory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.Universa
llyOpen
-/
instance snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyOpen f] :
    UniversallyOpen (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget @UniversallyOpen := by
  rw [eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isOpenMap_iff_restrictPreimage.mpr H
/-
**AlgebraicGeometry.UniversallyOpen.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.UniversallyOpen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtSource @UniversallyOpen := by
  rw [eq]
  exact universally_isZariskiLocalAtSource _

end UniversallyOpen

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- A generalizing morphism, locally of finite presentation is open. -/
@[stacks 01U1]
/-
**AlgebraicGeometry.isOpenMap_of_generalizingMap** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：isOpenMap_of_generalizingMap [LocallyOfFinitePresentation f] (hf : General
izingMap f) : IsOpenMap f
参数：hf : GeneralizingMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用引理 `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation`：isO
penMap_comap_of_hasGoingDown_of_finitePresentation [Algebra R S] [Algebra.HasGoi
ngDown R S] [Algebra.FinitePresentation R S] : IsOpenMap …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`：iff_general
izingMap_primeSpectrumComap : Algebra.HasGoingDown R S ↔ GeneralizingMap (PrimeS
pectrum.comap (algebraMap R S))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFinitePresentationFinit
ePresentation`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOf
FinitePresentation   fun {R S} [CommRing R] [CommRing S] => RingHom.FiniteP…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `AlgebraicGeometry.instIsZariskiLocalAtSourceTopologicallyIsOpenMap`：Alge
braicGeometry.IsZariskiLocalAtSource   (AlgebraicGeometry.topologically fun {α β
} [TopologicalSpace α] [TopologicalSpace β] => IsOpenMap…
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], 
  AlgebraicGeometry.LocallyOfFinitePresentation f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
· 使用定理 `AlgebraicGeometry.instIsZariskiLocalAtSourceTopologicallyGeneralizingMap
`：AlgebraicGeometry.IsZariskiLocalAtSource   (AlgebraicGeometry.topologically fu
n {α β} [TopologicalSpace α] [TopologicalSpace β] => Generaliz…
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`：iff_of_openCo
ver (𝒰 : Y.OpenCover) : P f ↔ forall i, P (𝒰.pullbackHom f i)
· 使用定理 `AlgebraicGeometry.instLocallyOfFinitePresentationSndScheme`：∀ {X Y Z : A
lgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.LocallyOfFin
itePresentation f],   AlgebraicGeometry.LocallyO…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`：of_isPullback {U
X UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY] {iX : UX ⟶ X} {f' : UX ⟶ U
Y} (h : IsPullback iX f' f iY) (H : P f) : P…
· 使用定理 `AlgebraicGeometry.instIsZariskiLocalAtTargetTopologicallyGeneralizingMap
`：AlgebraicGeometry.IsZariskiLocalAtTarget   (AlgebraicGeometry.topologically fu
n {α β} [TopologicalSpace α] [TopologicalSpace β] => Generaliz…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g

--- 原说明 ---
A generalizing morphism, locally of finite presentation is open.
-/
lemma isOpenMap_of_generalizingMap [LocallyOfFinitePresentation f]
    (hf : GeneralizingMap f) : IsOpenMap f := by
  change topologically IsOpenMap f
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically IsOpenMap) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback (P := topologically GeneralizingMap)
      (iY := Y.affineCover.f i) (IsPullback.of_hasPullback ..) hf
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := topologically IsOpenMap) X.affineCover]
    intro i
    refine this f _ _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtSource.comp (P := topologically GeneralizingMap) hf _
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  convert! PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  · rwa [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  · apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance

/-- Any flat morphism is generalizing. -/
/-
**AlgebraicGeometry.Flat.generalizingMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Flat`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Flat f],
 GeneralizingMap ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.of_isZariskiLocalAtSource_of_isZari
skiLocalAtTarget`：of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget [IsZariski
LocalAtTarget P] [IsZariskiLocalAtSource P] : HasRingHomProperty P (fun f => P…
· 使用定理 `AlgebraicGeometry.instIsZariskiLocalAtTargetTopologicallyGeneralizingMap
`：AlgebraicGeometry.IsZariskiLocalAtTarget   (AlgebraicGeometry.topologically fu
n {α β} [TopologicalSpace α] [TopologicalSpace β] => Generaliz…
· 使用定理 `AlgebraicGeometry.instIsZariskiLocalAtSourceTopologicallyGeneralizingMap
`：AlgebraicGeometry.IsZariskiLocalAtSource   (AlgebraicGeometry.topologically fu
n {α β} [TopologicalSpace α] [TopologicalSpace β] => Generaliz…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.iff_appLE`：iff_appLE : P f ↔ forall
 (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f.appLE U V e).hom
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`：iff_general
izingMap_primeSpectrumComap : Algebra.HasGoingDown R S ↔ GeneralizingMap (PrimeS
pectrum.comap (algebraMap R S))
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.appLE`：appLE (H : P f) (U : Y.affin
eOpens) (V : X.affineOpens) (e) : Q (f.appLE U V e).hom
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat

--- 原说明 ---
Any flat morphism is generalizing.
-/
lemma Flat.generalizingMap [Flat f] : GeneralizingMap f := by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  algebraize [(f.appLE U V e).hom]
  apply Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp
  convert! Algebra.HasGoingDown.of_flat
  exact HasRingHomProperty.appLE @Flat f ‹_› U V e

/-- A flat morphism, locally of finite presentation is universally open. -/
@[stacks 01UA]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A flat morphism, locally of finite presentation is universally open.
-/
instance (priority := low) UniversallyOpen.of_flat [Flat f] [LocallyOfFinitePresentation f] :
    UniversallyOpen f :=
  ⟨universally_mk' _ _ fun _ _ ↦ isOpenMap_of_generalizingMap _ (Flat.generalizingMap _)⟩

nonrec instance (priority := low) [IsIntegral Y] [Subsingleton Y] :
    UniversallyOpen f := by
  wlog hX : ∃ S, X = Spec S generalizing X
  · refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i ↦ this _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  wlog hY : ∃ K, Y = Spec K ∧ IsField K generalizing Y
  · have inst : Subsingleton (Spec Γ(Y, ⊤)) := Y.isoSpec.inv.homeomorph.subsingleton
    exact (MorphismProperty.cancel_right_of_respectsIso _ _ Y.isoSpec.hom).mp
      (this _ ⟨_, rfl, isField_of_isIntegral_of_subsingleton _⟩)
  obtain ⟨K, rfl, hK⟩ := hY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ⟨universally_mk' _ _ fun {T} g _ ↦ ?_⟩
  wlog hT : ∃ R, T = Spec R generalizing T
  · refine (IsZariskiLocalAtTarget.iff_of_openCover T.affineCover).mpr fun i ↦ ?_
    refine (MorphismProperty.cancel_left_of_respectsIso _
      ((pullbackRightPullbackFstIso ..).inv ≫ (pullbackSymmetry ..).hom) _).mp ?_
    simpa [Scheme.Cover.pullbackHom] using! this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hT
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom, ψ.hom]
  refine (MorphismProperty.cancel_left_of_respectsIso _ (pullbackSpecIso K R S).inv _).mp ?_
  convert_to! topologically _ (Spec.map <| CommRingCat.ofHom (algebraMap R (TensorProduct K R S)))
  · exact pullbackSpecIso_inv_fst ..
  let := hK.toField
  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field

end AlgebraicGeometry

