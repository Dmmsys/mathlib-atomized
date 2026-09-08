/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Étale morphisms

A morphism of schemes `f : X ⟶ Y` is étale if for each affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is étale.

## Main results

- `AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero`: Etale is equivalent to
  smooth of relative dimension `0`.

-/

@[expose] public section

universe t u

universe u₂ u₁ v₂ v₁

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is étale if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is étale. -/
@[mk_iff]
/-
**AlgebraicGeometry.Etale** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Etale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where etale_appLE (f) : forall
 {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <=
 f ⁻¹ᵁ U), (f.appLE U V e).hom.Etale  alias Scheme.Hom.etale_appLE
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is étale if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is étale.
-/
class Etale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  etale_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Etale

alias Scheme.Hom.etale_appLE := Etale.etale_appLE

@[deprecated (since := "2026-02-09")] alias IsEtale := Etale

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The property of scheme morphisms `Etale` is associated with the ring
homomorphism property `Etale`. -/
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of scheme morphisms `Etale` is associated with the ring
homomorphism property `Etale`.
-/
instance : HasRingHomProperty @Etale RingHom.Etale where
  isLocal_ringHomProperty := RingHom.Etale.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [etale_iff, affineLocally_iff_forall_isAffineOpen]

/-- Being étale is multiplicative. -/
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Being étale is multiplicative.
-/
instance : MorphismProperty.IsMultiplicative @Etale :=
  HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
    RingHom.Etale.containsIdentities

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition of étale morphisms is étale. -/
/-
**AlgebraicGeometry.Etale.etale_comp** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.Etale`。
形式化陈述：etale_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale f] [Etale g] : Etale (f ≫ g
)
参数：g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Etale.instIsMultiplicativeScheme`：CategoryTheory.Morph
ismProperty.IsMultiplicative @AlgebraicGeometry.Etale

--- 原说明 ---
The composition of étale morphisms is étale.
-/
instance etale_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Etale f› ‹Etale g›

/-- Etale is stable under base change. -/
/-
**AlgebraicGeometry.Etale.etale_isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.Etale`。
形式化陈述：etale_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @
Etale
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`：isStableUn
derBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsStableUnderBaseChan
ge
· 使用定理 `AlgebraicGeometry.Etale.instHasRingHomPropertyEtale`：AlgebraicGeometry.H
asRingHomProperty @AlgebraicGeometry.Etale fun {R S} [CommRing R] [CommRing S] =
> RingHom.Etale
· 使用定理 `RingHom.Etale.isStableUnderBaseChange`：RingHom.IsStableUnderBaseChange f
un {R S} [CommRing R] [CommRing S] => RingHom.Etale

--- 原说明 ---
Etale is stable under base change.
-/
instance etale_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Etale :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Etale.isStableUnderBaseChange

/-- Open immersions are étale. -/
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Open immersions are étale.
-/
instance (priority := 900) [IsOpenImmersion f] : Etale f :=
  HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale g] :
    Etale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale f] :
    Etale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [Etale f] : Etale (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Etale f] :
    Etale (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Etale`。
形式化陈述：eq_smoothOfRelativeDimension_zero : @Etale = @SmoothOfRelativeDimension 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.ext`：ext {P' : MorphismProperty Sch
eme.{u}} {Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Pr
op} [HasRingHomProperty P' Q']…
· 使用定理 `AlgebraicGeometry.Etale.instHasRingHomPropertyEtale`：AlgebraicGeometry.H
asRingHomProperty @AlgebraicGeometry.Etale fun {R S} [CommRing R] [CommRing S] =
> RingHom.Etale
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertySmoothOfRelativeDimensionLocally
IsStandardSmoothOfRelativeDimension`：∀ (n : ℕ),   AlgebraicGeometry.HasRingHomPr
operty (@AlgebraicGeometry.SmoothOfRelativeDimension n)     fun {R S} [CommRing 
R] [CommRing S] =…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero`：etale_iff_is
StandardSmoothOfRelativeDimension_zero : Etale f ↔ IsStandardSmoothOfRelativeDim
ension 0 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RingHom.locally_iff_of_localizationSpanTarget`：locally_iff_of_localizati
onSpanTarget (hPi : RespectsIso P) (hPs : OfLocalizationSpanTarget P) {R S : Typ
e u} [CommRing R] [CommRing S] (f :…
· 使用定理 `RingHom.Etale.respectsIso`：RingHom.RespectsIso fun {R S} [CommRing R] [C
ommRing S] => RingHom.Etale
· 使用定理 `RingHom.Etale.ofLocalizationSpanTarget`：RingHom.OfLocalizationSpanTarget
 fun {R S} [CommRing R] [CommRing S] => RingHom.Etale
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_smoothOfRelativeDimension_zero : @Etale = @SmoothOfRelativeDimension 0 := by
  apply HasRingHomProperty.ext
  introv
  have : @RingHom.Etale = @RingHom.IsStandardSmoothOfRelativeDimension 0 := by
    ext; apply RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero
  rw [← this, RingHom.locally_iff_of_localizationSpanTarget]
  · exact RingHom.Etale.respectsIso
  · exact RingHom.Etale.ofLocalizationSpanTarget
/-
**AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Etale`。
形式化陈述：iff_smoothOfRelativeDimension_zero : Etale f ↔ SmoothOfRelativeDimension 0
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero`：eq_smoothOfRe
lativeDimension_zero : @Etale = @SmoothOfRelativeDimension 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iff_smoothOfRelativeDimension_zero : Etale f ↔ SmoothOfRelativeDimension 0 f := by
  rw [eq_smoothOfRelativeDimension_zero]
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Etale f] : SmoothOfRelativeDimension 0 f := by
  rwa [← iff_smoothOfRelativeDimension_zero]
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Etale f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 0 f

open RingHom in
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [Etale f] : FormallyUnramified f where
  formallyUnramified_appLE {_} hU {_} hV e :=
    (f.etale_appLE hU hV e).formallyUnramified

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty
    @Etale (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
  exact inferInstanceAs <| Etale (pullback.diagonal f)

/-- If `f ≫ g` is étale and `g` unramified, then `f` is étale. -/
/-
**AlgebraicGeometry.Etale.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.E
tale`。
形式化陈述：of_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale (f ≫ g)] [LocallyOfFiniteType 
g] [FormallyUnramified g] : Etale f
参数：g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.Etale.instHasOfPostcompPropertySchemeMinMorphismProper
tyLocallyOfFiniteTypeFormallyUnramified`：CategoryTheory.MorphismProperty.HasOfPo
stcompProperty (@AlgebraicGeometry.Etale)   (@AlgebraicGeometry.LocallyOfFiniteT
ype ⊓ @AlgebraicGeome…

--- 原说明 ---
If `f ≫ g` is étale and `g` unramified, then `f` is étale.
-/
lemma of_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale (f ≫ g)] [LocallyOfFiniteType g]
    [FormallyUnramified g] : Etale f :=
  of_postcomp _ (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f g ⟨‹_›, ‹_›⟩ ‹_›
/-
**AlgebraicGeometry.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @Etale @Etale := by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @Etale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance
/-
**AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Etale`。
形式化陈述：iff_flat_and_formallyUnramified {f : X ⟶ Y} : Etale f ↔ Flat f ∧ FormallyU
nramified f ∧ LocallyOfFinitePresentation f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.etale_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶
 Y),   AlgebraicGeometry.Etale f ↔     ∀ {U : Y.Opens},       AlgebraicGeometry.
IsAffineOpen U → …
· 使用定理 `AlgebraicGeometry.flat_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ 
Y),   AlgebraicGeometry.Flat f ↔     ∀ {U : Y.Opens},       AlgebraicGeometry.Is
AffineOpen U →  …
· 使用定理 `AlgebraicGeometry.formallyUnramified_iff`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y),   AlgebraicGeometry.FormallyUnramified f ↔     ∀ {U : Y.Opens}
,       AlgebraicGeometry.IsAf…
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_iff`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.LocallyOfFinitePresentation f ↔  
   ∀ {U : Y.Opens},       AlgebraicGeom…
-/
lemma iff_flat_and_formallyUnramified {f : X ⟶ Y} :
    Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f := by
  rw [etale_iff, flat_iff, formallyUnramified_iff, locallyOfFinitePresentation_iff]
  grind [RingHom.Etale.iff_flat_and_formallyUnramified]
/-
**AlgebraicGeometry.Etale.of_formallyUnramified_of_flat** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Etale`。
形式化陈述：of_formallyUnramified_of_flat [Flat f] [FormallyUnramified f] [LocallyOfFi
nitePresentation f] : Etale f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified`：iff_flat_and_fo
rmallyUnramified {f : X ⟶ Y} : Etale f ↔ Flat f ∧ FormallyUnramified f ∧ Locally
OfFinitePresentation f
-/
lemma of_formallyUnramified_of_flat [Flat f] [FormallyUnramified f]
    [LocallyOfFinitePresentation f] :
    Etale f := by
  rw [Etale.iff_flat_and_formallyUnramified]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Etale

namespace Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-- The category `Etale X` is the category of schemes étale over `X`. -/
/-
**AlgebraicGeometry.Scheme.Etale** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sc
heme`。
形式化陈述：AlgebraicGeometry.Scheme → Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `Etale X` is the category of schemes étale over `X`.
-/
protected def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @Etale ⊤ X
deriving Category, HasPullbacks, HasFiniteLimits

variable (X : Scheme.{u})

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : X.Etale) : dsimp% Etale Y.hom := Y.prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} {Z Y : X.Etale} (f : Z ⟶ Y) : Etale f.left := by
  have : Etale (f.left ≫ Y.hom) := by rw [CategoryTheory.Over.w]; infer_instance
  exact Etale.of_comp f.left Y.hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from schemes étale over `X` to schemes over `X`. -/
/-
**AlgebraicGeometry.Scheme.Etale.forget** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Etale`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → CategoryTheory.Functor X.Etale (CategoryT
heory.Over X)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
The forgetful functor from schemes étale over `X` to schemes over `X`.
-/
def Etale.forget : X.Etale ⥤ Over X :=
  MorphismProperty.Over.forget @Etale ⊤ X

set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from schemes étale over `X` to schemes over `X` is fully faithful. -/
/-
**AlgebraicGeometry.Scheme.Etale.forgetFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.Etale`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → (AlgebraicGeometry.Scheme.Etale.forget X)
.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from schemes étale over `X` to schemes over `X` is fully f
aithful.
-/
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

-- Note: using `deriving Functor.Full/Faithful` in the declaration of `Etale.forget`
-- would "succeed", but it seems it would fail to create the next two instances
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Etale.forget X).Full :=
  (Etale.forgetFullyFaithful X).full
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Etale.forget X).Faithful :=
  (Etale.forgetFullyFaithful X).faithful

variable {X} in
/-- Constructor for objects in the étale site of a scheme `X`: it takes
an étale morphism `f : Y ⟶ X` as an input. -/
/-
**AlgebraicGeometry.Scheme.Etale.mk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry
.Scheme.Etale`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : Y ⟶ X) → [AlgebraicGeometry.Etale 
f] → X.Etale
参数：f : Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects in the étale site of a scheme `X`: it takes
an étale morphism `f : Y ⟶ X` as an input.
-/
abbrev Etale.mk {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] : X.Etale :=
  MorphismProperty.Over.mk _ f inferInstance

variable {X} in
@[simp]
/-
**AlgebraicGeometry.Scheme.Etale.forget_mk** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Etale`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : Y ⟶ X) [inst : AlgebraicGeometry.E
tale f],   (AlgebraicGeometry.Scheme.Etale.forget X).obj (AlgebraicGeometry.Sche
me.Etale.mk f) = CategoryTheory.Over.mk f
参数：f : Y ⟶ X；AlgebraicGeometry.Scheme.Etale.forget X；AlgebraicGeometry.Scheme.Et
ale.mk f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Etale.forget_mk {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    (Etale.forget X).obj (.mk f) = Over.mk f := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Etale.forget_obj_left** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Etale`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (Y : X.Etale), ((AlgebraicGeometry.Scheme
.Etale.forget X).obj Y).left = Y.left
参数：X : AlgebraicGeometry.Scheme；Y : X.Etale；(AlgebraicGeometry.Scheme.Etale.forg
et X).obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Etale.forget_obj_left (Y : X.Etale) :
    ((Etale.forget X).obj Y).left = Y.left := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Etale.forget_obj_hom** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Etale`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (Y : X.Etale), ((AlgebraicGeometry.Scheme
.Etale.forget X).obj Y).hom = Y.hom
参数：X : AlgebraicGeometry.Scheme；Y : X.Etale；(AlgebraicGeometry.Scheme.Etale.forg
et X).obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Etale.forget_obj_hom (Y : X.Etale) :
    ((Etale.forget X).obj Y).hom = Y.hom := rfl
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : X.Etale) : Etale (Y.left ↘ X) := Y.prop

/-- Induction principle for the objects of the small étale site of a scheme. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**AlgebraicGeometry.Scheme.Etale.rec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Etale`。
形式化陈述：(X : AlgebraicGeometry.Scheme) →   {motive : X.Etale → Sort u_1} →     ((Y
 : AlgebraicGeometry.Scheme) →         (f : Y ⟶ X) → (x : AlgebraicGeometry.Etal
e f) → motive (AlgebraicGeometry.Scheme.Etale.mk f)) →       (T : X.Etale) → mot
ive T
参数：Y : AlgebraicGeometry.Scheme；f : Y ⟶ X；x : AlgebraicGeometry.Etale f；Algebrai
cGeometry.Scheme.Etale.mk f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle for the objects of the small étale site of a scheme.
-/
def Etale.rec {motive : X.Etale → Sort*}
    (mk : ∀ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : Etale f), motive (Etale.mk f))
    (T : X.Etale) :
    motive T :=
  mk _ _ T.prop

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteLimits (Etale.forget X) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget _ ⊤ X))

end Scheme

end AlgebraicGeometry

