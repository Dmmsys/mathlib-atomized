/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Affine morphisms with additional ring hom property

In this file we define a constructor `affineAnd Q` for affine target morphism properties of schemes
from a property of ring homomorphisms `Q`: A morphism `f : X ⟶ Y` with affine target satisfies
`affineAnd Q` if it is an affine morphism (i.e. `X` is affine) and the induced ring map on global
sections satisfies `Q`.

`affineAnd Q` inherits most stability properties of `Q` and is local at the target if `Q` is local
at the (algebraic) source.

Typical examples of this are affine morphisms (where `Q` is trivial), finite morphisms
(where `Q` is module finite) or closed immersions (where `Q` is being surjective).

-/

@[expose] public section

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

section

variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

/-- This is the affine target morphism property where the source is affine and
the induced map of rings on global sections satisfies `P`. -/
/-
**AlgebraicGeometry.affineAnd** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：affineAnd : AffineTargetMorphismProperty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the affine target morphism property where the source is affine and
the induced map of rings on global sections satisfies `P`.
-/
def affineAnd : AffineTargetMorphismProperty :=
  fun X _ f ↦ IsAffine X ∧ Q (f.appTop).hom

@[simp]
/-
**AlgebraicGeometry.affineAnd_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：affineAnd_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] : affineAnd Q 
f ↔ IsAffine X ∧ Q (f.appTop).hom
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma affineAnd_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    affineAnd Q f ↔ IsAffine X ∧ Q (f.appTop).hom :=
  Iff.rfl

attribute [local simp] AffineTargetMorphismProperty.toProperty_apply

variable {Q}

set_option backward.isDefEq.respectTransparency false in
/-- If `P` respects isos, also `affineAnd P` respects isomorphisms. -/
/-
**AlgebraicGeometry.affineAnd_respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：affineAnd_respectsIso (hP : RingHom.RespectsIso Q) : (affineAnd Q).toPrope
rty.RespectsIso
参数：hP : RingHom.RespectsIso Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `RingHom.RespectsIso.cancel_left_isIso`：∀ {P : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P 
→     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If `P` respects isos, also `affineAnd P` respects isomorphisms.
-/
lemma affineAnd_respectsIso (hP : RingHom.RespectsIso Q) :
    (affineAnd Q).toProperty.RespectsIso := by
  refine RespectsIso.mk _ ?_ ?_
  · intro X Y Z e f ⟨hZ, ⟨hY, hf⟩⟩
    simpa [hP.cancel_right_isIso, IsAffine.of_isIso e.hom]
  · intro X Y Z e f ⟨hZ, hf⟩
    simpa [AffineTargetMorphismProperty.toProperty, IsAffine.of_isIso e.inv, hP.cancel_left_isIso]

set_option backward.isDefEq.respectTransparency false in
/-- `affineAnd P` is local if `P` is local on the (algebraic) source. -/
/-
**AlgebraicGeometry.affineAnd_isLocal** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：affineAnd_isLocal (hPi : RingHom.RespectsIso Q) (hQl : RingHom.Localizatio
nAwayPreserves Q) (hQs : RingHom.OfLocalizationSpan Q) : (affineAnd Q).IsLocal w
here respectsIso
参数：hPi : RingHom.RespectsIso Q；hQl : RingHom.LocalizationAwayPreserves Q；hQs : R
ingHom.OfLocalizationSpan Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.affineAnd_respectsIso`：affineAnd_respectsIso (hP : Rin
gHom.RespectsIso Q) : (affineAnd Q).toProperty.RespectsIso
· 使用定理 `AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen`：∀ {X : Alg
ebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X] (r : ↑(X.presheaf.obj (Opp
osite.op ⊤))),   AlgebraicGeometry.IsAffine ↑(X.ba…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `AlgebraicGeometry.morphismRestrict_appTop`：morphismRestrict_appTop {X Y 
: Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫ 
X.presheaf.map (eqToHom (image_…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_image_top`：ι_image_top : U.ι ''ᵁ ⊤ = U
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用引理 `AlgebraicGeometry.IsAffineOpen.app_basicOpen_eq_away_map`：app_basicOpen_
eq_away_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U) (
h : IsAffineOpen (f ⁻¹ᵁ U)) (r : Γ(Y, U)) : ha…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appTop.eq_1`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y),   AlgebraicGeometry.Scheme.Hom.appTop f = AlgebraicGeometry.Sc
heme.Hom.app f ⊤
· 使用定理 `AlgebraicGeometry.isLocalization_away_of_isAffine`：∀ {X : AlgebraicGeome
try.Scheme} [AlgebraicGeometry.IsAffine X] (r : ↑(X.presheaf.obj (Opposite.op ⊤)
)),   IsLocalization.Away r ↑(X.preshea…
· 使用引理 `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`：isAffine_of_isAffi
neOpen_basicOpen (s : Set Γ(X, ⊤)) (hs : Ideal.span s = ⊤) (hs₂ : forall i in s,
 IsAffineOpen (X.basicOpen i)) : IsAffine …
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RingHom.OfLocalizationSpan.ofIsLocalization'`：RingHom.OfLocalizationSpan
.ofIsLocalization' (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIs
o P) {R S : Type u} [CommRing R] […

--- 原说明 ---
`affineAnd P` is local if `P` is local on the (algebraic) source.
-/
lemma affineAnd_isLocal (hPi : RingHom.RespectsIso Q) (hQl : RingHom.LocalizationAwayPreserves Q)
    (hQs : RingHom.OfLocalizationSpan Q) : (affineAnd Q).IsLocal where
  respectsIso := affineAnd_respectsIso hPi
  to_basicOpen {X Y _} f r := fun ⟨hX, hf⟩ ↦ by
    simp only at hf
    constructor
    · simp only [Scheme.preimage_basicOpen, Opens.map_top]
      exact (isAffineOpen_top X).basicOpen _
    · dsimp only
      rw [morphismRestrict_appTop, CommRingCat.hom_comp, hPi.cancel_right_isIso]
      -- Not sure why the `show` fixes the following `rw` complaining about "motive is incorrect"
      change Q (Scheme.Hom.app f ((Y.basicOpen r).ι ''ᵁ ⊤)).hom
      rw [Scheme.Opens.ι_image_top]
      rw [(isAffineOpen_top Y).app_basicOpen_eq_away_map f (isAffineOpen_top X),
        CommRingCat.hom_comp, hPi.cancel_right_isIso, ← Scheme.Hom.appTop]
      dsimp only [Opens.map_top]
      apply hQl
      exact hf
  of_basicOpenCover {X Y _} f s hs hf := by
    dsimp [affineAnd] at hf
    have : IsAffine X := by
      apply isAffine_of_isAffineOpen_basicOpen (f.appTop '' s)
      · apply_fun Ideal.map (f.appTop).hom at hs
        rwa [Ideal.map_span, Ideal.map_top] at hs
      · rintro - ⟨r, hr, rfl⟩
        simp_rw [Scheme.preimage_basicOpen] at hf
        exact (hf ⟨r, hr⟩).left
    refine ⟨inferInstance, hQs.ofIsLocalization' hPi (f.appTop).hom s hs fun a ↦ ?_⟩
    refine ⟨Γ(Y, Y.basicOpen a.val), Γ(X, X.basicOpen (f.appTop a.val)), inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · exact (isAffineOpen_top X).isLocalization_basicOpen (f.appTop a.val)
    · obtain ⟨_, hf⟩ := hf a
      rw [morphismRestrict_appTop, CommRingCat.hom_comp, hPi.cancel_right_isIso] at hf
      -- Not sure why the `show` fixes the following `rw` complaining about "motive is incorrect"
      have hf : Q (Scheme.Hom.app f ((Y.basicOpen a.1).ι ''ᵁ ⊤)).hom := hf
      rw [Scheme.Opens.ι_image_top] at hf
      rw [(isAffineOpen_top Y).app_basicOpen_eq_away_map _ (isAffineOpen_top X)] at hf
      rwa [CommRingCat.hom_comp, hPi.cancel_right_isIso] at hf
/-
**AlgebraicGeometry.affineAnd_isLocal_of_propertyIsLocal** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：affineAnd_isLocal_of_propertyIsLocal (hPi : RingHom.PropertyIsLocal Q) : (
affineAnd Q).IsLocal
参数：hPi : RingHom.PropertyIsLocal Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.affineAnd_isLocal`：affineAnd_isLocal (hPi : RingHom.Re
spectsIso Q) (hQl : RingHom.LocalizationAwayPreserves Q) (hQs : RingHom.OfLocali
zationSpan Q) : (affineAn…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `RingHom.PropertyIsLocal.localizationAwayPreserves`：∀ {P : {R S : Type u}
 → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pr
opertyIsLocal P → RingHom.LocalizationA…
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpan`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.PropertyI
sLocal P → RingHom.OfLocalizatio…
-/
lemma affineAnd_isLocal_of_propertyIsLocal
    (hPi : RingHom.PropertyIsLocal Q) : (affineAnd Q).IsLocal :=
  affineAnd_isLocal hPi.respectsIso hPi.localizationAwayPreserves hPi.ofLocalizationSpan

/-- If `P` is stable under base change, so is `affineAnd P`. -/
/-
**AlgebraicGeometry.affineAnd_isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：affineAnd_isStableUnderBaseChange (hQi : RingHom.RespectsIso Q) (hQb : Rin
gHom.IsStableUnderBaseChange Q) : (affineAnd Q).IsStableUnderBaseChange
参数：hQi : RingHom.RespectsIso Q；hQb : RingHom.IsStableUnderBaseChange Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.affineAnd_respectsIso`：affineAnd_respectsIso (hP : Rin
gHom.RespectsIso Q) : (affineAnd Q).toProperty.RespectsIso
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsStableUnderBaseChange.m
k`：∀ (P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.Respects
Iso],   (∀ ⦃X Y S : AlgebraicGeometry.Scheme⦄ [inst : Algebraic…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1`：∀ {X Y S : 
AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.IsAffineHom
 g]   [AlgebraicGeometry.IsAffine X], AlgebraicGe…
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用定理 `RingHom.IsStableUnderBaseChange.pullback_fst_appTop`：∀ (P : {R S : Type 
u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop),   (RingHom
.IsStableUnderBaseChange fun {R S} [CommR…

--- 原说明 ---
If `P` is stable under base change, so is `affineAnd P`.
-/
lemma affineAnd_isStableUnderBaseChange (hQi : RingHom.RespectsIso Q)
    (hQb : RingHom.IsStableUnderBaseChange Q) :
    (affineAnd Q).IsStableUnderBaseChange := by
  have : (affineAnd Q).toProperty.RespectsIso := affineAnd_respectsIso hQi
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g ⟨hY, hg⟩
  exact ⟨inferInstance, hQb.pullback_fst_appTop _ hQi f _ hg⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.targetAffineLocally_affineAnd_iff** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：targetAffineLocally_affineAnd_iff (hQi : RingHom.RespectsIso Q) {X Y : Sch
eme.{u}} (f : X ⟶ Y) : targetAffineLocally (affineAnd Q) f ↔ forall U : Y.Opens,
 IsAffineOpen U -> IsAffineOpen (f ⁻¹ᵁ U) ∧ Q (f.app U).hom
参数：hQi : RingHom.RespectsIso Q；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `AlgebraicGeometry.morphismRestrict_app`：morphismRestrict_app {X Y : Sche
me.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) : (f ∣_ U).app V = f.ap
p (U.ι ''ᵁ V) ≫ X.presheaf.m…
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_image_top`：ι_image_top : U.ι ''ᵁ ⊤ = U
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma targetAffineLocally_affineAnd_iff (hQi : RingHom.RespectsIso Q)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    targetAffineLocally (affineAnd Q) f ↔ ∀ U : Y.Opens, IsAffineOpen U →
      IsAffineOpen (f ⁻¹ᵁ U) ∧ Q (f.app U).hom := by
  simp only [targetAffineLocally, affineAnd_apply, morphismRestrict_app, CommRingCat.hom_comp,
    hQi.cancel_right_isIso]
  refine ⟨fun hf U hU ↦ ?_, fun h U ↦ ?_⟩
  · obtain ⟨hfU, hf⟩ := hf ⟨U, hU⟩
    use hfU
    have hf : Q (Scheme.Hom.app f (((⟨U, hU⟩ : Y.affineOpens) : Y.Opens).ι ''ᵁ ⊤)).hom := hf
    rwa [Scheme.Opens.ι_image_top] at hf
  · refine ⟨(h U U.2).1, ?_⟩
    change Q (Scheme.Hom.app f ((U : Y.Opens).ι ''ᵁ ⊤)).hom
    rw [Scheme.Opens.ι_image_top]
    exact (h U U.2).2

/-- Variant of `targetAffineLocally_affineAnd_iff` where `IsAffineHom` is bundled. -/
/-
**AlgebraicGeometry.targetAffineLocally_affineAnd_iff'** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：targetAffineLocally_affineAnd_iff' (hQi : RingHom.RespectsIso Q) {X Y : Sc
heme.{u}} (f : X ⟶ Y) : targetAffineLocally (affineAnd Q) f ↔ IsAffineHom f ∧ fo
rall U : Y.Opens, IsAffineOpen U -> Q (f.app U).hom
参数：hQi : RingHom.RespectsIso Q；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_iff`：targetAffineLocally
_affineAnd_iff (hQi : RingHom.RespectsIso Q) {X Y : Scheme.{u}} (f : X ⟶ Y) : ta
rgetAffineLocally (affineAnd Q) f ↔ foral…
· 使用定理 `AlgebraicGeometry.isAffineHom_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f
 : X ⟶ Y),   AlgebraicGeometry.IsAffineHom f ↔     ∀ (U : Y.Opens),       Algebr
aicGeometry.IsAffineOpe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Variant of `targetAffineLocally_affineAnd_iff` where `IsAffineHom` is bundled.
-/
lemma targetAffineLocally_affineAnd_iff' (hQi : RingHom.RespectsIso Q)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    targetAffineLocally (affineAnd Q) f ↔
      IsAffineHom f ∧ ∀ U : Y.Opens, IsAffineOpen U → Q (f.app U).hom := by
  rw [targetAffineLocally_affineAnd_iff hQi, isAffineHom_iff]
  aesop

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.targetAffineLocally_affineAnd_iff_affineLocally** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：targetAffineLocally_affineAnd_iff_affineLocally (hQ : RingHom.PropertyIsLo
cal Q) {X Y : Scheme.{u}} (f : X ⟶ Y) : targetAffineLocally (affineAnd Q) f ↔ Is
AffineHom f ∧ affineLocally Q f
参数：hQ : RingHom.PropertyIsLocal Q；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_iff'`：targetAffineLocall
y_affineAnd_iff' (hQi : RingHom.RespectsIso Q) {X Y : Scheme.{u}} (f : X ⟶ Y) : 
targetAffineLocally (affineAnd Q) f ↔ IsAf…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `AlgebraicGeometry.isAffine_of_isAffineHom`：isAffine_of_isAffineHom [IsAf
fineHom f] [IsAffine Y] : IsAffine X
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.IsAffineHom.isAffine_preimage`：∀ {X Y : AlgebraicGeome
try.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsAffineHom f] (U : Y.Opens), 
  AlgebraicGeometry.IsAffineOpen U → …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `AlgebraicGeometry.morphismRestrict_appTop`：morphismRestrict_appTop {X Y 
: Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫ 
X.presheaf.map (eqToHom (image_…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_image_top`：ι_image_top : U.ι ''ᵁ ⊤ = U
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `AlgebraicGeometry.affineLocally_iff_affineOpens_le`：affineLocally_iff_af
fineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) : affineLocally.{u} P f ↔ forall (U 
: Y.affineOpens) (V : X.affineOpens) (e …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma targetAffineLocally_affineAnd_iff_affineLocally (hQ : RingHom.PropertyIsLocal Q)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    targetAffineLocally (affineAnd Q) f ↔ IsAffineHom f ∧ affineLocally Q f := by
  have : HasRingHomProperty (affineLocally Q) Q := ⟨hQ, rfl⟩
  rw [targetAffineLocally_affineAnd_iff' hQ.respectsIso]
  simp only [and_congr_right_iff]
  intro hf
  constructor
  · wlog hY : IsAffine Y
    · intro h
      rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := affineLocally Q)
        _ (iSup_affineOpens_eq_top _)]
      intro U
      have : IsAffine (f ⁻¹ᵁ U) := hf.isAffine_preimage U U.2
      rw [HasRingHomProperty.iff_of_isAffine (P := affineLocally Q),
        morphismRestrict_appTop, CommRingCat.hom_comp, hQ.respectsIso.cancel_right_isIso]
      apply h
      rw [Scheme.Opens.ι_image_top]
      exact U.2
    intro h
    have : IsAffine X := isAffine_of_isAffineHom f
    rw [HasRingHomProperty.iff_of_isAffine (P := affineLocally Q)]
    exact h ⊤ (isAffineOpen_top Y)
  · intro h U hU
    rw [affineLocally_iff_affineOpens_le] at h
    rw [f.app_eq_appLE]
    exact h ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hf.isAffine_preimage U hU⟩ (by simp)
/-
**AlgebraicGeometry.targetAffineLocally_affineAnd_eq_affineLocally** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：targetAffineLocally_affineAnd_eq_affineLocally (hQ : RingHom.PropertyIsLoc
al Q) : targetAffineLocally (affineAnd Q) = (@IsAffineHom ⊓ @affineLocally Q : M
orphismProperty Scheme.{u})
参数：hQ : RingHom.PropertyIsLocal Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_iff_affineLocally`：targe
tAffineLocally_affineAnd_iff_affineLocally (hQ : RingHom.PropertyIsLocal Q) {X Y
 : Scheme.{u}} (f : X ⟶ Y) : targetAffineLocally (affin…
-/
lemma targetAffineLocally_affineAnd_eq_affineLocally (hQ : RingHom.PropertyIsLocal Q) :
    targetAffineLocally (affineAnd Q) =
      (@IsAffineHom ⊓ @affineLocally Q : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact targetAffineLocally_affineAnd_iff_affineLocally hQ f

variable {W : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
/-
**AlgebraicGeometry.targetAffineLocally_affineAnd_le** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：targetAffineLocally_affineAnd_le (hQW : forall {R S : Type u} [CommRing R]
 [CommRing S] {f : R ->+* S}, Q f -> W f) : targetAffineLocally (affineAnd Q) <=
 targetAffineLocally (affineAnd W)
参数：hQW : forall {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S}, Q f -> 
W f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma targetAffineLocally_affineAnd_le
    (hQW : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, Q f → W f) :
    targetAffineLocally (affineAnd Q) ≤ targetAffineLocally (affineAnd W) := by
  intro X Y f h U
  exact ⟨(h U).1, hQW (h U).2⟩

end

section

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- If `P` is a morphism property affine locally defined by `affineAnd Q`, `P` is stable under
composition if `Q` is. -/
/-
**AlgebraicGeometry.HasAffineProperty.affineAnd_isStableUnderComposition** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}, 
  AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S} [
CommRing R] [CommRing S] => Q) →     (RingHom.StableUnderComposition fun {R S} [
CommRing R] [CommRing S] => Q) → P.IsStableUnderComposition
参数：R →+* S；AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q；
RingHom.StableUnderComposition fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `P` is a morphism property affine locally defined by `affineAnd Q`, `P` is st
able under
composition if `Q` is.
-/
lemma HasAffineProperty.affineAnd_isStableUnderComposition {P : MorphismProperty Scheme.{u}}
    (hA : HasAffineProperty P (affineAnd Q)) (hQ : RingHom.StableUnderComposition Q) :
    P.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    wlog hZ : IsAffine Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this hA hQ _ _ (IsZariskiLocalAtTarget.restrict hf _)
        (IsZariskiLocalAtTarget.restrict hg _) U.2
    rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))] at hg
    obtain ⟨hY, hg⟩ := hg
    rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))] at hf
    obtain ⟨hX, hf⟩ := hf
    rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))]
    exact ⟨hX, hQ _ _ hg hf⟩

/-- If `P` is a morphism property affine locally defined by `affineAnd Q`, `P` is stable under
base change if `Q` is. -/
/-
**AlgebraicGeometry.HasAffineProperty.affineAnd_isStableUnderBaseChange** 是 Math
lib 中的一个定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}, 
  AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S} [
CommRing R] [CommRing S] => Q) →     (RingHom.RespectsIso fun {R S} [CommRing R]
 [CommRing S] => Q) →       (RingHom.IsStableUnderBaseChange fun {R S} [CommRing
 R] [CommRing S] => Q) → P.IsStableUnderBaseChange
参数：R →+* S；AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q；
RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q；RingHom.IsStableUnd
erBaseChange fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.Aff
ineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.affineAnd_isStableUnderBaseChange`：affineAnd_isStableU
nderBaseChange (hQi : RingHom.RespectsIso Q) (hQb : RingHom.IsStableUnderBaseCha
nge Q) : (affineAnd Q).IsStableUnderBaseC…

--- 原说明 ---
If `P` is a morphism property affine locally defined by `affineAnd Q`, `P` is st
able under
base change if `Q` is.
-/
lemma HasAffineProperty.affineAnd_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    (_ : HasAffineProperty P (affineAnd Q)) (hQi : RingHom.RespectsIso Q)
    (hQb : RingHom.IsStableUnderBaseChange Q) :
    P.IsStableUnderBaseChange :=
  HasAffineProperty.isStableUnderBaseChange
    (AlgebraicGeometry.affineAnd_isStableUnderBaseChange hQi hQb)

/-- If `Q` contains identities and respects isomorphisms (i.e. is satisfied by isomorphisms),
and `P` is affine locally defined by `affineAnd Q`, then `P` contains identities. -/
/-
**AlgebraicGeometry.HasAffineProperty.affineAnd_containsIdentities** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}, 
  AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S} [
CommRing R] [CommRing S] => Q) →     (RingHom.RespectsIso fun {R S} [CommRing R]
 [CommRing S] => Q) →       (RingHom.ContainsIdentities fun {R S} [CommRing R] [
CommRing S] => Q) → P.ContainsIdentities
参数：R →+* S；AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q；
RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q；RingHom.ContainsIde
ntities fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_iff`：targetAffineLocally
_affineAnd_iff (hQi : RingHom.RespectsIso Q) {X Y : Scheme.{u}} (f : X ⟶ Y) : ta
rgetAffineLocally (affineAnd Q) f ↔ foral…

--- 原说明 ---
If `Q` contains identities and respects isomorphisms (i.e. is satisfied by isomo
rphisms),
and `P` is affine locally defined by `affineAnd Q`, then `P` contains identities
.
-/
lemma HasAffineProperty.affineAnd_containsIdentities {P : MorphismProperty Scheme.{u}}
    (hA : HasAffineProperty P (affineAnd Q)) (hQi : RingHom.RespectsIso Q)
    (hQ : RingHom.ContainsIdentities Q) :
    P.ContainsIdentities where
  id_mem X := by
    rw [eq_targetAffineLocally P, targetAffineLocally_affineAnd_iff hQi]
    intro U hU
    exact ⟨hU, hQ _⟩

/-- A convenience constructor for `HasAffineProperty P (affineAnd Q)`. The `IsAffineHom` is bundled,
since this goes well with defining morphism properties via `extends IsAffineHom`. -/
/-
**AlgebraicGeometry.HasAffineProperty.affineAnd_iff** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme), 
  (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q) →     (RingHom.
LocalizationAwayPreserves fun {R S} [CommRing R] [CommRing S] => Q) →       (Rin
gHom.OfLocalizationSpan fun {R S} [CommRing R] [CommRing S] => Q) →         (Alg
ebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S} [CommR
ing R] [CommRing S] => Q) ↔           ∀ {X Y : AlgebraicGeometry.Scheme} (f : X 
⟶ Y),             P f ↔               AlgebraicGeometry.IsAffineHom f ∧         
        ∀ (U : Y.Opens),                   AlgebraicGeometry.IsAffineOpen U → Q 
(CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U)))
参数：R →+* S；P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；RingHom.
RespectsIso fun {R S} [CommRing R] [CommRing S] => Q；RingHom.LocalizationAwayPre
serves fun {R S} [CommRing R] [CommRing S] => Q；RingHom.OfLocalizationSpan fun {
R S} [CommRing R] [CommRing S] => Q；AlgebraicGeometry.HasAffineProperty P (Algeb
raicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q) ↔           ∀ {
X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),             P f ↔               Alg
ebraicGeometry.IsAffineHom f ∧                 ∀ (U : Y.Opens),                 
  AlgebraicGeometry.IsAffineOpen U → Q (CommRingCat.Hom.hom (AlgebraicGeometry.S
cheme.Hom.app f U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_iff`：targetAffineLocally
_affineAnd_iff (hQi : RingHom.RespectsIso Q) {X Y : Scheme.{u}} (f : X ⟶ Y) : ta
rgetAffineLocally (affineAnd Q) f ↔ foral…
· 使用引理 `AlgebraicGeometry.affineAnd_isLocal`：affineAnd_isLocal (hPi : RingHom.Re
spectsIso Q) (hQl : RingHom.LocalizationAwayPreserves Q) (hQs : RingHom.OfLocali
zationSpan Q) : (affineAn…
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A convenience constructor for `HasAffineProperty P (affineAnd Q)`. The `IsAffine
Hom` is bundled,
since this goes well with defining morphism properties via `extends IsAffineHom`
.
-/
lemma HasAffineProperty.affineAnd_iff (P : MorphismProperty Scheme.{u})
    (hQi : RingHom.RespectsIso Q) (hQl : RingHom.LocalizationAwayPreserves Q)
    (hQs : RingHom.OfLocalizationSpan Q) :
    HasAffineProperty P (affineAnd Q) ↔
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ↔
        (IsAffineHom f ∧ ∀ U : Y.Opens, IsAffineOpen U → Q (f.app U).hom) := by
  simp_rw [isAffineHom_iff]
  refine ⟨fun h X Y f ↦ ?_, fun h ↦ ⟨affineAnd_isLocal hQi hQl hQs, ?_⟩⟩
  · rw [eq_targetAffineLocally P, targetAffineLocally_affineAnd_iff hQi]
    lia
  · ext X Y f
    rw [targetAffineLocally_affineAnd_iff hQi, h f]
    aesop

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.HasAffineProperty.affineAnd_le_isAffineHom** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme), 
  AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S} [
CommRing R] [CommRing S] => Q) →     P ≤ @AlgebraicGeometry.IsAffineHom
参数：R →+* S；P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；Algebrai
cGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine`：AlgebraicGeo
metry.HasAffineProperty @AlgebraicGeometry.IsAffineHom fun X x x_1 x_2 => Algebr
aicGeometry.IsAffine X
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma HasAffineProperty.affineAnd_le_isAffineHom (P : MorphismProperty Scheme.{u})
    (hA : HasAffineProperty P (affineAnd Q)) : P ≤ @IsAffineHom := by
  intro X Y f hf
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsAffineHom) _ (iSup_affineOpens_eq_top _)]
    intro U
    exact this P hA _ (IsZariskiLocalAtTarget.restrict hf _) U.2
  rw [HasAffineProperty.iff_of_isAffine (P := P) (Q := (affineAnd Q))] at hf
  rw [HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)]
  exact hf.1
/-
**AlgebraicGeometry.HasAffineProperty.affineAnd_eq_of_propertyIsLocal** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   {P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme
},   AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S
} [CommRing R] [CommRing S] => Q) →     ∀ [AlgebraicGeometry.HasRingHomProperty 
P' fun {R S} [CommRing R] [CommRing S] => Q],       P = @AlgebraicGeometry.IsAff
ineHom ⊓ P'
参数：R →+* S；AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_eq_affineLocally`：target
AffineLocally_affineAnd_eq_affineLocally (hQ : RingHom.PropertyIsLocal Q) : targ
etAffineLocally (affineAnd Q) = (@IsAffineHom ⊓ @affin…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`：eq_affineLocally 
: P = affineLocally Q
-/
lemma HasAffineProperty.affineAnd_eq_of_propertyIsLocal {P P' : MorphismProperty Scheme.{u}}
    (hP : HasAffineProperty P (affineAnd Q)) [HasRingHomProperty P' Q] :
    P = (@IsAffineHom ⊓ P' : MorphismProperty Scheme.{u}) := by
  rw [HasAffineProperty.eq_targetAffineLocally (P := P),
    targetAffineLocally_affineAnd_eq_affineLocally,
    HasRingHomProperty.eq_affineLocally (P := P')]
  exact HasRingHomProperty.isLocal_ringHomProperty P'
/-
**AlgebraicGeometry.HasAffineProperty.SpecMap_iff_of_affineAnd** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}, 
  AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S} [
CommRing R] [CommRing S] => Q) →     (RingHom.RespectsIso fun {R S} [CommRing R]
 [CommRing S] => Q) →       ∀ {R S : CommRingCat} (f : R ⟶ S), P (AlgebraicGeome
try.Spec.map f) ↔ Q (CommRingCat.Hom.hom f)
参数：R →+* S；AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q；
RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q；f : R ⟶ S；Algebraic
Geometry.Spec.map f；CommRingCat.Hom.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.affineAnd.eq_1`：∀ (Q : {R S : Type u} → [inst : CommRi
ng R] → [inst_1 : CommRing S] → (R →+* S) → Prop) (X x : AlgebraicGeometry.Schem
e)   (f : X ⟶ x) [inst…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
-/
lemma HasAffineProperty.SpecMap_iff_of_affineAnd {P : MorphismProperty Scheme.{u}}
    (hP : HasAffineProperty P (affineAnd Q)) (hQi : RingHom.RespectsIso Q)
    {R S : CommRingCat.{u}} (f : R ⟶ S) : P (Spec.map f) ↔ Q f.hom := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  rw [HasAffineProperty.iff_of_isAffine (P := P), affineAnd, and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty Q)
    (arrowIsoΓSpecOfIsAffine f).symm, inferInstance]
variable {Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
/-
**AlgebraicGeometry.HasAffineProperty.affineAnd_le_affineAnd** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q Q' : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (
R →+* S) → Prop}   {P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme},   AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {
R S} [CommRing R] [CommRing S] => Q) →     AlgebraicGeometry.HasAffineProperty P
' (AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q') →     
  (∀ {R S : Type u} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S}, Q f
 → Q' f) → P ≤ P'
参数：R →+* S；AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q；
AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q'；∀ {R S : T
ype u} [inst : CommRing R] [inst_1 : CommRing S] {f : R →+* S}, Q f → Q' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_le`：targetAffineLocally_
affineAnd_le (hQW : forall {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* 
S}, Q f -> W f) : targetAffineLocally (a…
-/
lemma HasAffineProperty.affineAnd_le_affineAnd {P P' : MorphismProperty Scheme.{u}}
    (hP : HasAffineProperty P (affineAnd Q)) (hP' : HasAffineProperty P' (affineAnd Q'))
    (hQQ' : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, Q f → Q' f) :
    P ≤ P' := by
  rw [HasAffineProperty.eq_targetAffineLocally (P := P),
    HasAffineProperty.eq_targetAffineLocally (P := P')]
  exact targetAffineLocally_affineAnd_le hQQ'

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasAffineProperty.coprodDesc_affineAnd** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}, 
  AlgebraicGeometry.HasAffineProperty P (AlgebraicGeometry.affineAnd fun {R S} [
CommRing R] [CommRing S] => Q) →     (RingHom.RespectsIso fun {R S} [CommRing R]
 [CommRing S] => Q) →       (∀ {R S T : Type u} [inst : CommRing R] [inst_1 : Co
mmRing S] [inst_2 : CommRing T] (f : R →+* S) (g : R →+* T),           Q f → Q g
 → Q (f.prod g)) →         ∀ {U V X : AlgebraicGeometry.Scheme} (f : U ⟶ X) (g :
 V ⟶ X),           P f → P g → P (CategoryTheory.Limits.coprod.desc f g)
参数：R →+* S；AlgebraicGeometry.affineAnd fun {R S} [CommRing R] [CommRing S] => Q；
RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q；∀ {R S T : Type u} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T] (f : R →+* S) (g
 : R →+* T),           Q f → Q g → Q (f.prod g)；f : U ⟶ X；g : V ⟶ X；CategoryTheo
ry.Limits.coprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.affineAnd_le_isAffineHom`：∀ {Q : {R 
S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop}   
(P : CategoryTheory.MorphismProperty AlgebraicGeom…
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
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.targetAffineLocally_affineAnd_iff`：targetAffineLocally
_affineAnd_iff (hQi : RingHom.RespectsIso Q) {X Y : Scheme.{u}} (f : X ⟶ Y) : ta
rgetAffineLocally (affineAnd Q) f ↔ foral…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.preimage`：∀ {X Y : AlgebraicGeometry.Sche
me} {U : Y.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ (f : X ⟶ Y) [Algeb
raicGeometry.IsAffineHom f], …
· 使用定理 `AlgebraicGeometry.instIsAffineHomDescScheme`：∀ {U V X : AlgebraicGeometr
y.Scheme} (f : U ⟶ X) (g : V ⟶ X) [AlgebraicGeometry.IsAffineHom f]   [Algebraic
Geometry.IsAffineHom g], Algebrai…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `CategoryTheory.Limits.prod.mapIso_hom`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
（共 39 条，此处仅展示前 30 条）
-/
lemma HasAffineProperty.coprodDesc_affineAnd {P : MorphismProperty Scheme.{u}}
    (hP : HasAffineProperty P (affineAnd Q)) (hQi : RingHom.RespectsIso Q)
    (hQ : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : R →+* T),
      Q f → Q g → Q (f.prod g))
    {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) (hf : P f) (hg : P g) :
    P (Limits.coprod.desc f g) := by
  have := HasAffineProperty.affineAnd_le_isAffineHom P hP f hf
  have := HasAffineProperty.affineAnd_le_isAffineHom P hP g hg
  rw [HasAffineProperty.eq_targetAffineLocally P, targetAffineLocally_affineAnd_iff hQi] at hf hg ⊢
  refine fun W hW ↦ ⟨hW.preimage _, ?_⟩
  let e : Γ(U ⨿ V, Limits.coprod.desc f g ⁻¹ᵁ W) ≅ Γ(U, f ⁻¹ᵁ W) ⨯ Γ(V, g ⁻¹ᵁ W) :=
    Scheme.coprodPresheafObjIso _ ≪≫ Limits.prod.mapIso
      (U.presheaf.mapIso (eqToIso (by simp [← Scheme.Hom.comp_preimage])).op)
      (V.presheaf.mapIso (eqToIso (by simp [← Scheme.Hom.comp_preimage])).op)
  rw [← hQi.cancel_right_isIso _ e.hom,
    ← CommRingCat.hom_comp, ← hQi.cancel_right_isIso _
    ((Limits.limit.isLimit _).conePointUniqueUpToIso (CommRingCat.prodFanIsLimit _ _)).hom,
    ← CommRingCat.hom_comp]
  have {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S × T) :
      Q (.comp (.fst _ _) f) → Q (.comp (.snd _ _) f) → Q f :=
    hQ (.comp (.fst _ _) f) (.comp (.snd _ _) f)
  refine this _ ?_ ?_
  · have : (Limits.coprod.desc f g).app W ≫ e.hom ≫ Limits.prod.fst = f.app W := by
      simp [e, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    convert! (hf W hW).2
    exact congr(($this).1)
  · have : (Limits.coprod.desc f g).app W ≫ e.hom ≫ Limits.prod.snd = g.app W := by
      simp [e, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    convert! (hg W hW).2
    exact congr(($this).1)

end

end AlgebraicGeometry

