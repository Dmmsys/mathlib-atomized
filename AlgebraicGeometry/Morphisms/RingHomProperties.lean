/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.Locally

/-!

# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that come from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `targetAffineLocally (affineAnd P)`: the preimage of an affine open `U = Spec A` is affine
  (`= Spec B`) and `A ⟶ B` satisfies `P`. (in `Mathlib/AlgebraicGeometry/Morphisms/AffineAnd.lean`)
- `affineLocally P`: For each pair of affine open `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`,
  the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on the source (`RingHom.RespectsIso P`, `RingHom.LocalizationPreserves P`,
`RingHom.OfLocalizationSpan`), and `targetAffineLocally (affine_and P)` will be local on
the target.

For the latter `P` should be local on the target (`RingHom.PropertyIsLocal P`), and
`affineLocally P` will be local on both the source and the target.
We also provide the following interface:

## `HasRingHomProperty`

`HasRingHomProperty P Q` is a type class asserting that `P` is local at the target and the source,
and for `f : Spec B ⟶ Spec A`, it is equivalent to the ring hom property `Q` on `Γ(f)`.

For `HasRingHomProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:
- `AlgebraicGeometry.HasRingHomProperty.iff_appLE`:
    `P f` if and only if `Q (f.appLE U V _)` for all affine `U : Opens Y` and `V : Opens X`.
- `AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover`:
    If `Y` is affine, `P f ↔ ∀ i, Q ((𝒰.map i ≫ f).appTop)` for an affine open cover `𝒰` of `X`.
- `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`:
    If `X` and `Y` are affine, then `P f ↔ Q (f.appTop)`.
- `AlgebraicGeometry.HasRingHomProperty.Spec_iff`:
    `P (Spec.map φ) ↔ Q φ`
- `AlgebraicGeometry.HasRingHomProperty.iff_of_iSup_eq_top`:
    If `Y` is affine, `P f ↔ ∀ i, Q (f.appLE ⊤ (U i) _)` for a family `U` of affine opens of `X`.
- `AlgebraicGeometry.HasRingHomProperty.of_isOpenImmersion`:
    If `f` is an open immersion then `P f`.
- `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`:
    If `Q` is stable under base change, then so is `P`.

We also provide the instances `P.IsMultiplicative`, `P.IsStableUnderComposition`,
`IsZariskiLocalAtTarget P`, `IsZariskiLocalAtSource P`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**RingHom.IsStableUnderBaseChange.pullback_fst_appTop** 是 Mathlib 中的一个定理，位于命名空间 
`RingHom.IsStableUnderBaseChange`。
形式化陈述：∀ (P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop),   (RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRi
ng S] => P) →     (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => P)
 →       ∀ {X Y S : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X] [Al
gebraicGeometry.IsAffine Y]         [AlgebraicGeometry.IsAffine S] (f : X ⟶ S) (
g : Y ⟶ S),         P (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop 
g)) →           P (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop (Cat
egoryTheory.Limits.pullback.fst f g)))
参数：P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) 
→ Prop；RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRing S] => P；
RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => P；f : X ⟶ S；g : Y ⟶ S
；CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop g)；CommRingCat.Hom.hom
 (AlgebraicGeometry.Scheme.Hom.appTop (CategoryTheory.Limits.pullback.fst f g))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_inv_fst`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_appTop`：comp_appTop {X Y Z : Scheme} (
f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).appTop = g.appTop ≫ f.appTop
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.AffineScheme.forgetToScheme_map`：∀ {X Y : CategoryTheo
ry.InducedCategory AlgebraicGeometry.Scheme CategoryTheory.ObjectProperty.FullSu
bcategory.obj}   (f : X ⟶ Y), Algebraic…
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `AlgebraicGeometry.AffineScheme.instIsEquivalenceOppositeCommRingCatRight
OpΓ`：AlgebraicGeometry.AffineScheme.Γ.rightOp.IsEquivalence
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_hom_fst`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `CategoryTheory.Limits.pushoutIsoUnopPullback_inl_hom`：pushoutIsoUnopPull
back_inl_hom {X Y Z : C} (f : X ⟶ Z) (g : X ⟶ Y) [HasPushout f g] : pushout.inl 
_ _ ≫ (pushoutIsoUnopPullback f g).hom = (…
· 使用定理 `RingHom.IsStableUnderBaseChange.pushout_inl`：∀ {P : {R S : Type u} → [in
st : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.IsStable
UnderBaseChange P →     RingHom.R…
-/
theorem IsStableUnderBaseChange.pullback_fst_appTop
    (hP : IsStableUnderBaseChange P) (hP' : RespectsIso P)
    {X Y S : Scheme} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (H : P g.appTop.hom) : P (pullback.fst f g).appTop.hom := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g)]
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, hP'.cancel_right_isIso,
    AffineScheme.forgetToScheme_map]
  have := congr_arg Quiver.Hom.unop
      (PreservesPullback.iso_hom_fst AffineScheme.Γ.rightOp (AffineScheme.ofHom f)
        (AffineScheme.ofHom g))
  simp only [AffineScheme.Γ, Functor.rightOp_obj, Functor.comp_obj, Functor.op_obj, unop_comp,
    AffineScheme.forgetToScheme_obj, Scheme.Γ_obj, Functor.rightOp_map, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, AffineScheme.forgetToScheme_map, Scheme.Γ_map] at this
  rw [← this, CommRingCat.hom_comp, hP'.cancel_right_isIso, ← pushoutIsoUnopPullback_inl_hom,
    CommRingCat.hom_comp, hP'.cancel_right_isIso]
  exact hP.pushout_inl hP' _ _ H

end RingHom

namespace AlgebraicGeometry

section affineLocally

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

/-- For `P` a property of ring homomorphisms, `sourceAffineLocally P` holds for `f : X ⟶ Y`
whenever `P` holds for the restriction of `f` on every affine open subset of `X`. -/
/-
**AlgebraicGeometry.sourceAffineLocally** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：sourceAffineLocally : AffineTargetMorphismProperty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `P` a property of ring homomorphisms, `sourceAffineLocally P` holds for `f :
 X ⟶ Y`
whenever `P` holds for the restriction of `f` on every affine open subset of `X`
.
-/
def sourceAffineLocally : AffineTargetMorphismProperty := fun X _ f _ =>
  ∀ U : X.affineOpens, P (f.appLE ⊤ U le_top).hom

/-- For `P` a property of ring homomorphisms, `affineLocally P` holds for `f : X ⟶ Y` if for each
affine open `U = Spec A ⊆ Y` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.
Also see `affineLocally_iff_affineOpens_le`. -/
/-
**AlgebraicGeometry.affineLocally** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：affineLocally : MorphismProperty Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `P` a property of ring homomorphisms, `affineLocally P` holds for `f : X ⟶ Y
` if for each
affine open `U = Spec A ⊆ Y` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` sa
tisfies `P`.
Also see `affineLocally_iff_affineOpens_le`.
-/
abbrev affineLocally : MorphismProperty Scheme.{u} :=
  targetAffineLocally (sourceAffineLocally P)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.sourceAffineLocally_respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso P) : (sourceAffi
neLocally P).toProperty.RespectsIso
参数：h₁ : RingHom.RespectsIso P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk`：respectsI
so_mk {P : AffineTargetMorphismProperty} (h₁ : forall {X Y Z} (e : X ≅ Y) (f : Y
 ⟶ Z) [IsAffine Z], P f -> P (e.hom ≫ f)) (h₂ : for…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`：appLE_comp_appLE {X Y Z :
 Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : g.appLE U V e₁ ≫ f.appLE V W e₂
 = (f ≫ g).appLE U W (e₂.trans ((Op…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`：image_of_isOpen
Immersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen (f ''ᵁ U)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_appLE`：comp_appLE {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (U V e) : (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e
· 使用定理 `RingHom.RespectsIso.cancel_left_isIso`：∀ {P : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P 
→     ∀ {R S T : CommRingCa…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
-/
theorem sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso P) :
    (sourceAffineLocally P).toProperty.RespectsIso := by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    have : IsIso (e.hom.appLE (e.hom ''ᵁ U) U.1 (e.hom.preimage_image_eq _).ge) :=
      inferInstanceAs (IsIso (e.hom.app _ ≫
        X.presheaf.map (eqToHom (e.hom.preimage_image_eq _).symm).op))
    rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ (e.hom ''ᵁ U) U.1 le_top (e.hom.preimage_image_eq _).ge,
      CommRingCat.hom_comp, h₁.cancel_right_isIso]
    exact H ⟨_, U.prop.image_of_isOpenImmersion e.hom⟩
  · introv H U
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, h₁.cancel_left_isIso]
    exact H U
/-
**AlgebraicGeometry.affineLocally_respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：affineLocally_respectsIso (h : RingHom.RespectsIso P) : (affineLocally P).
RespectsIso
参数：h : RingHom.RespectsIso P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instRespectsIsoSchemeTargetAffineLocallyOfToProperty`：
∀ (P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.RespectsIso
],   (AlgebraicGeometry.targetAffineLocally P).RespectsIso
· 使用定理 `AlgebraicGeometry.sourceAffineLocally_respectsIso`：sourceAffineLocally_r
espectsIso (h₁ : RingHom.RespectsIso P) : (sourceAffineLocally P).toProperty.Res
pectsIso
-/
theorem affineLocally_respectsIso (h : RingHom.RespectsIso P) : (affineLocally P).RespectsIso :=
  letI := sourceAffineLocally_respectsIso P h
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
open Scheme in
/-
**AlgebraicGeometry.sourceAffineLocally_morphismRestrict** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：sourceAffineLocally_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y
.Opens) (hU : IsAffineOpen U) : @sourceAffineLocally P _ _ (f ∣_ U) hU ↔ forall 
(V : X.affineOpens) (e : V.1 <= f ⁻¹ᵁ U), P (f.appLE U V e).hom
参数：f : X ⟶ Y；U : Y.Opens；hU : IsAffineOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.morphismRestrict_appLE`：morphismRestrict_appLE {X Y : 
Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e) : (f ∣_ U).appLE V W e = f.appLE (
U.ι ''ᵁ V) ((f ⁻¹ᵁ U).ι ''ᵁ W)…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_congr`：appLE_congr (e : V <= f ⁻¹ᵁ U)
 (e₁ : U = U') (e₂ : V = V') (P : forall {R S : CommRingCat.{u}} (_ : R ⟶ S), Pr
op) : P (f.appLE U V e) ↔ P (f…
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_image_top`：ι_image_top : U.ι ''ᵁ ⊤ = U
-/
theorem sourceAffineLocally_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    @sourceAffineLocally P _ _ (f ∣_ U) hU ↔
      ∀ (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U), P (f.appLE U V e).hom := by
  dsimp only [sourceAffineLocally]
  simp only [morphismRestrict_appLE]
  rw [(affineOpensRestrict (f ⁻¹ᵁ U)).forall_congr_left, Subtype.forall]
  refine forall₂_congr fun V h ↦ ?_
  have := (affineOpensRestrict (f ⁻¹ᵁ U)).apply_symm_apply ⟨V, h⟩
  exact f.appLE_congr _ (Opens.ι_image_top _) congr($(this).1.1) (fun f => P f.hom)
/-
**AlgebraicGeometry.affineLocally_iff_affineOpens_le** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：affineLocally_iff_affineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) : affineLo
cally.{u} P f ↔ forall (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 <= f ⁻¹ᵁ
 U.1), P (f.appLE U V e).hom
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.sourceAffineLocally_morphismRestrict`：sourceAffineLoca
lly_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffine
Open U) : @sourceAffineLocally P _ _ (f ∣_ U…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem affineLocally_iff_affineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} P f ↔
      ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), P (f.appLE U V e).hom :=
  forall_congr' fun U ↦ sourceAffineLocally_morphismRestrict P f U U.2
/-
**AlgebraicGeometry.affineLocally_iff_forall_isAffineOpen** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：affineLocally_iff_forall_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) : aff
ineLocally.{u} P f ↔ forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ 
: IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), P (f.appLE U V e).hom
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem affineLocally_iff_forall_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} P f ↔
      ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      P (f.appLE U V e).hom := by
  simp [affineLocally_iff_affineOpens_le, Scheme.affineOpens]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.sourceAffineLocally_isLocal** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：sourceAffineLocally_isLocal (h₁ : RingHom.RespectsIso P) (h₂ : RingHom.Loc
alizationAwayPreserves P) (h₃ : RingHom.OfLocalizationSpan P) : (sourceAffineLoc
ally P).IsLocal
参数：h₁ : RingHom.RespectsIso P；h₂ : RingHom.LocalizationAwayPreserves P；h₃ : Ring
Hom.OfLocalizationSpan P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.sourceAffineLocally_respectsIso`：sourceAffineLocally_r
espectsIso (h₁ : RingHom.RespectsIso P) : (sourceAffineLocally P).toProperty.Res
pectsIso
· 使用定理 `AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen`：∀ {X : Alg
ebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X] (r : ↑(X.presheaf.obj (Opp
osite.op ⊤))),   AlgebraicGeometry.IsAffine ↑(X.ba…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.sourceAffineLocally_morphismRestrict`：sourceAffineLoca
lly_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffine
Open U) : @sourceAffineLocally P _ _ (f ∣_ U…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_congr`：appLE_congr (e : V <= f ⁻¹ᵁ U)
 (e₁ : U = U') (e₂ : V = V') (P : forall {R S : CommRingCat.{u}} (_ : R ⟶ S), Pr
op) : P (f.appLE U V e) ↔ P (f…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.IsAffineOpen.appLE_eq_away_map`：appLE_eq_away_map {X Y
 : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV
 : IsAffineOpen V) (e) (r : Γ(Y, U)) :…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `RingHom.RespectsIso.isLocalization_away_iff`：∀ {P : {R S : Type u} → [in
st : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Respects
Iso P →     ∀ {R S : Type u} (R' …
· 使用引理 `CommRingCat.hom_ofHom`：hom_ofHom {R S : Type u} [CommRing R] [CommRing S
] (f : R ->+* S) : (ofHom f).hom = f
-/
theorem sourceAffineLocally_isLocal (h₁ : RingHom.RespectsIso P)
    (h₂ : RingHom.LocalizationAwayPreserves P) (h₃ : RingHom.OfLocalizationSpan P) :
    (sourceAffineLocally P).IsLocal := by
  constructor
  · exact sourceAffineLocally_respectsIso P h₁
  · intro X Y _ f r H
    rw [sourceAffineLocally_morphismRestrict]
    intro U hU
    have : X.basicOpen (f.appLE ⊤ U (by simp) r) = U := by
      simp only [Scheme.Hom.appLE, Opens.map_top, CommRingCat.comp_apply]
      rw [Scheme.basicOpen_res]
      simpa using hU
    rw [← f.appLE_congr (by simp [Scheme.Hom.appLE]) rfl this (fun f => P f.hom),
      IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2 _ r]
    simp only [CommRingCat.hom_ofHom]
    apply +allowSynthFailures h₂
    exact H U
  · introv hs hs' U
    apply h₃ _ _ hs
    intro r
    simp_rw [sourceAffineLocally_morphismRestrict] at hs'
    have := hs' r ⟨X.basicOpen (f.appLE ⊤ U le_top r.1), U.2.basicOpen (f.appLE ⊤ U le_top r.1)⟩
      (by simp [Scheme.Hom.appLE])
    rwa [IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2, CommRingCat.hom_ofHom,
      ← h₁.isLocalization_away_iff] at this

variable {P}
/-
**AlgebraicGeometry.affineLocally_le** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：affineLocally_le {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R 
->+* S) -> Prop} (hPQ : forall {R S : Type u} [CommRing R] [CommRing S] {f : R -
>+* S}, P f -> Q f) : affineLocally P <= affineLocally Q
参数：R ->+* S；hPQ : forall {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S}
, P f -> Q f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma affineLocally_le {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hPQ : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, P f → Q f) :
    affineLocally P ≤ affineLocally Q :=
  fun _ _ _ hf U V ↦ hPQ (hf U V)

open RingHom

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

set_option backward.isDefEq.respectTransparency.types false in
/-- If `P` holds for `f` over affine opens `U₂` of `Y` and `V₂` of `X` and `U₁` (resp. `V₁`) are
open affine neighborhoods of `x` (resp. `f.base x`), then `P` also holds for `f`
over some basic open of `U₁` (resp. `V₁`). -/
/-
**AlgebraicGeometry.exists_basicOpen_le_appLE_of_appLE_of_isAffine** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：exists_basicOpen_le_appLE_of_appLE_of_isAffine (hPa : StableUnderCompositi
onWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P) (x : X) (U₁ 
: Y.affineOpens) (U₂ : Y.affineOpens) (V₁ : X.affineOpens) (V₂ : X.affineOpens) 
(hx₁ : x in V₁.1) (hx₂ : x in V₂.1) (e₂ : V₂.1 <= f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U
₂ V₂ e₂).hom) (hfx₁ : f x in U₁.1) : exists (r : Γ(Y, U₁)) (s : Γ(X, V₁)) (_ : x
 in X.basicOpen s) (e : X.basicOpen s <= f ⁻¹ᵁ Y.basicOpen r), P (f.appLE (Y.bas
icOpen r) (X.basicOpen s) 
参数：hPa : StableUnderCompositionWithLocalizationAwayTarget P；hPl : LocalizationAw
ayPreserves P；x : X；U₁ : Y.affineOpens；U₂ : Y.affineOpens；V₁ : X.affineOpens；V₂ 
: X.affineOpens；hx₁ : x in V₁.1；hx₂ : x in V₂.1；e₂ : V₂.1 <= f ⁻¹ᵁ U₂.1；h₂ : P (
f.appLE U₂ V₂ e₂).hom；hfx₁ : f x in U₁.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.exists_basicOpen_le_affine_inter`：∀ {X : AlgebraicGeom
etry.Scheme} {U : X.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ {V : X.Op
ens},       AlgebraicGeometry.IsAffineOp…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_congr`：appLE_congr (e : V <= f ⁻¹ᵁ U)
 (e₁ : U = U') (e₂ : V = V') (P : forall {R S : CommRingCat.{u}} (_ : R ⟶ S), Pr
op) : P (f.appLE U V e) ↔ P (f…
· 使用引理 `AlgebraicGeometry.IsAffineOpen.appLE_eq_away_map`：appLE_eq_away_map {X Y
 : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV
 : IsAffineOpen V) (e) (r : Γ(Y, U)) :…

--- 原说明 ---
If `P` holds for `f` over affine opens `U₂` of `Y` and `V₂` of `X` and `U₁` (res
p. `V₁`) are
open affine neighborhoods of `x` (resp. `f.base x`), then `P` also holds for `f`
over some basic open of `U₁` (resp. `V₁`).
-/
lemma exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    (x : X) (U₁ : Y.affineOpens) (U₂ : Y.affineOpens) (V₁ : X.affineOpens) (V₂ : X.affineOpens)
    (hx₁ : x ∈ V₁.1) (hx₂ : x ∈ V₂.1) (e₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U₂ V₂ e₂).hom)
    (hfx₁ : f x ∈ U₁.1) :
    ∃ (r : Γ(Y, U₁)) (s : Γ(X, V₁)) (_ : x ∈ X.basicOpen s)
      (e : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r),
        P (f.appLE (Y.basicOpen r) (X.basicOpen s) e).hom := by
  obtain ⟨r, r', hBrr', hBfx⟩ := exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f x)
    ⟨hfx₁, e₂ hx₂⟩
  have ha : IsAffineOpen (X.basicOpen (f.appLE U₂ V₂ e₂ r')) := V₂.2.basicOpen _
  have hxa : x ∈ X.basicOpen (f.appLE U₂ V₂ e₂ r') := by
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro hx₂ (hBrr' ▸ hBfx)
  obtain ⟨s, s', hBss', hBx⟩ := exists_basicOpen_le_affine_inter V₁.2 ha x ⟨hx₁, hxa⟩
  have := V₂.2.isLocalization_basicOpen (f.appLE U₂ V₂ e₂ r')
  have := U₂.2.isLocalization_basicOpen r'
  have := ha.isLocalization_basicOpen s'
  have ers : X.basicOpen s ≤ f ⁻¹ᵁ Y.basicOpen r := by
    rw [hBss', hBrr']
    apply le_trans (X.basicOpen_le _)
    simp [Scheme.Hom.appLE]
  have heq : f.appLE (Y.basicOpen r') (X.basicOpen s') (hBrr' ▸ hBss' ▸ ers) =
      f.appLE (Y.basicOpen r') (X.basicOpen (f.appLE U₂ V₂ e₂ r')) (by simp [Scheme.Hom.appLE]) ≫
        CommRingCat.ofHom (algebraMap _ _) := by
    simp only [Scheme.Hom.appLE, homOfLE_leOfHom, Category.assoc]
    congr
    apply X.presheaf.map_comp
  refine ⟨r, s, hBx, ers, ?_⟩
  · rw [f.appLE_congr _ hBrr' hBss' (fun f => P f.hom), heq]
    apply hPa _ s' _
    rw [U₂.2.appLE_eq_away_map f V₂.2]
    exact hPl _ _ _ _ h₂

/-- If `P` holds for `f` over affine opens `U₂` of `Y` and `V₂` of `X` and `U₁` (resp. `V₁`) are
open neighborhoods of `x` (resp. `f.base x`), then `P` also holds for `f` over some affine open
`U'` of `Y` (resp. `V'` of `X`) that is contained in `U₁` (resp. `V₁`). -/
/-
**AlgebraicGeometry.exists_affineOpens_le_appLE_of_appLE** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：exists_affineOpens_le_appLE_of_appLE (hPa : StableUnderCompositionWithLoca
lizationAwayTarget P) (hPl : LocalizationAwayPreserves P) (x : X) (U₁ : Y.Opens)
 (U₂ : Y.affineOpens) (V₁ : X.Opens) (V₂ : X.affineOpens) (hx₁ : x in V₁) (hx₂ :
 x in V₂.1) (e₂ : V₂.1 <= f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U₂ V₂ e₂).hom) (hfx₁ : f 
x in U₁.1) : exists (U' : Y.affineOpens) (V' : X.affineOpens) (_ : U'.1 <= U₁) (
_ : V'.1 <= V₁) (_ : x in V'.1) (e : V'.1 <= f ⁻¹ᵁ U'.1), P (f.appLE U' V' e).ho
m
参数：hPa : StableUnderCompositionWithLocalizationAwayTarget P；hPl : LocalizationAw
ayPreserves P；x : X；U₁ : Y.Opens；U₂ : Y.affineOpens；V₁ : X.Opens；V₂ : X.affineOp
ens；hx₁ : x in V₁；hx₂ : x in V₂.1；e₂ : V₂.1 <= f ⁻¹ᵁ U₂.1；h₂ : P (f.appLE U₂ V₂ 
e₂).hom；hfx₁ : f x in U₁.1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`：exists_basicOpen_le 
{V : X.Opens} (x : V) (h : ↑x in U) : exists f : Γ(X, U), X.basicOpen f <= V ∧ ↑
x in X.basicOpen f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用引理 `AlgebraicGeometry.exists_basicOpen_le_appLE_of_appLE_of_isAffine`：exists
_basicOpen_le_appLE_of_appLE_of_isAffine (hPa : StableUnderCompositionWithLocali
zationAwayTarget P) (hPl : LocalizationAwayPreserves P…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U

--- 原说明 ---
If `P` holds for `f` over affine opens `U₂` of `Y` and `V₂` of `X` and `U₁` (res
p. `V₁`) are
open neighborhoods of `x` (resp. `f.base x`), then `P` also holds for `f` over s
ome affine open
`U'` of `Y` (resp. `V'` of `X`) that is contained in `U₁` (resp. `V₁`).
-/
lemma exists_affineOpens_le_appLE_of_appLE
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    (x : X) (U₁ : Y.Opens) (U₂ : Y.affineOpens) (V₁ : X.Opens) (V₂ : X.affineOpens)
    (hx₁ : x ∈ V₁) (hx₂ : x ∈ V₂.1) (e₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U₂ V₂ e₂).hom)
    (hfx₁ : f x ∈ U₁.1) :
    ∃ (U' : Y.affineOpens) (V' : X.affineOpens) (_ : U'.1 ≤ U₁) (_ : V'.1 ≤ V₁) (_ : x ∈ V'.1)
      (e : V'.1 ≤ f ⁻¹ᵁ U'.1), P (f.appLE U' V' e).hom := by
  obtain ⟨r, hBr, hBfx⟩ := U₂.2.exists_basicOpen_le ⟨f x, hfx₁⟩ (e₂ hx₂)
  obtain ⟨s, hBs, hBx⟩ := V₂.2.exists_basicOpen_le ⟨x, hx₁⟩ hx₂
  obtain ⟨r', s', hBx', e', hf'⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine hPa hPl x
    ⟨Y.basicOpen r, U₂.2.basicOpen _⟩ U₂ ⟨X.basicOpen s, V₂.2.basicOpen _⟩ V₂ hBx hx₂ e₂ h₂ hBfx
  exact ⟨⟨Y.basicOpen r', (U₂.2.basicOpen _).basicOpen _⟩,
    ⟨X.basicOpen s', (V₂.2.basicOpen _).basicOpen _⟩, le_trans (Y.basicOpen_le _) hBr,
    le_trans (X.basicOpen_le _) hBs, hBx', e', hf'⟩

end affineLocally

/--
`HasRingHomProperty P Q` is a type class asserting that `P` is local at the target and the source,
and for `f : Spec B ⟶ Spec A`, it is equivalent to the ring hom property `Q`.
To make the proofs easier, we state it instead as
1. `Q` is local (See `RingHom.PropertyIsLocal`)
2. `P f` if and only if `Q` holds for every `Γ(Y, U) ⟶ Γ(X, V)` for all affine `U`, `V`.
  See `HasRingHomProperty.iff_appLE`.
-/
/-
**AlgebraicGeometry.HasRingHomProperty** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme →   outParam ({R 
S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop) → 
Prop
参数：{R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Pr
op。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasRingHomProperty P Q` is a type class asserting that `P` is local at the targ
et and the source,
and for `f : Spec B ⟶ Spec A`, it is equivalent to the ring hom property `Q`.
To make the proofs easier, we state it instead as
1. `Q` is local (See `RingHom.PropertyIsLocal`)
2. `P f` if and only if `Q` holds for every `Γ(Y, U) ⟶ Γ(X, V)` for all affine `
U`, `V`.
  See `HasRingHomProperty.iff_appLE`.
-/
class HasRingHomProperty (P : MorphismProperty Scheme.{u})
    (Q : outParam (∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)) : Prop where
  isLocal_ringHomProperty : RingHom.PropertyIsLocal Q
  eq_affineLocally' : P = affineLocally Q

namespace HasRingHomProperty

variable (P : MorphismProperty Scheme.{u}) {Q} [HasRingHomProperty P Q]
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-
**AlgebraicGeometry.HasRingHomProperty.copy** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.HasRingHomProperty`。
形式化陈述：copy {P' : MorphismProperty Scheme.{u}} {Q' : forall {R S : Type u} [CommR
ing R] [CommRing S], (R ->+* S) -> Prop} (e : P = P') (e' : forall {R S : Type u
} [CommRing R] [CommRing S] (f : R ->+* S), Q f ↔ Q' f) : HasRingHomProperty P' 
Q'
参数：R ->+* S；e : P = P'；e' : forall {R S : Type u} [CommRing R] [CommRing S] (f :
 R ->+* S), Q f ↔ Q' f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma copy {P' : MorphismProperty Scheme.{u}}
    {Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (e : P = P') (e' : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S), Q f ↔ Q' f) :
    HasRingHomProperty P' Q' := by
  subst e
  have heq : @Q = @Q' := by
    ext R S _ _ f
    exact (e' f)
  rw [← heq]
  infer_instance
/-
**AlgebraicGeometry.HasRingHomProperty.eq_affineLocally** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：eq_affineLocally : P = affineLocally Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally'`：∀ {P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : outParam ({R S : Type u}
 → [inst : CommRing R] → [inst_1 : CommRing …
-/
lemma eq_affineLocally : P = affineLocally Q := eq_affineLocally'

@[local instance]
/-
**AlgebraicGeometry.HasRingHomProperty.HasAffineProperty** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：HasAffineProperty : HasAffineProperty P (sourceAffineLocally Q) where isLo
cal_affineProperty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.sourceAffineLocally_isLocal`：sourceAffineLocally_isLoc
al (h₁ : RingHom.RespectsIso P) (h₂ : RingHom.LocalizationAwayPreserves P) (h₃ :
 RingHom.OfLocalizationSpan P) : (s…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `RingHom.PropertyIsLocal.localizationAwayPreserves`：∀ {P : {R S : Type u}
 → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pr
opertyIsLocal P → RingHom.LocalizationA…
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpan`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.PropertyI
sLocal P → RingHom.OfLocalizatio…
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`：eq_affineLocally 
: P = affineLocally Q
-/
lemma HasAffineProperty : HasAffineProperty P (sourceAffineLocally Q) where
  isLocal_affineProperty := sourceAffineLocally_isLocal _
    (isLocal_ringHomProperty P).respectsIso
    (isLocal_ringHomProperty P).localizationAwayPreserves
    (isLocal_ringHomProperty P).ofLocalizationSpan
  eq_targetAffineLocally' := eq_affineLocally P

/-- This is only `inferInstance` because of the `@[local instance]` on `HasAffineProperty` above. -/
/-
**AlgebraicGeometry.HasRingHomProperty.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.HasRingHomProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is only `inferInstance` because of the `@[local instance]` on `HasAffinePro
perty` above.
-/
instance (priority := 900) : IsZariskiLocalAtTarget P := inferInstance
/-
**AlgebraicGeometry.HasRingHomProperty.appLE** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.HasRingHomProperty`。
形式化陈述：appLE (H : P f) (U : Y.affineOpens) (V : X.affineOpens) (e) : Q (f.appLE U
 V e).hom
参数：H : P f；U : Y.affineOpens；V : X.affineOpens；e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.affineLocally_iff_affineOpens_le`：affineLocally_iff_af
fineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) : affineLocally.{u} P f ↔ forall (U 
: Y.affineOpens) (V : X.affineOpens) (e …
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`：eq_affineLocally 
: P = affineLocally Q
-/
theorem appLE (H : P f) (U : Y.affineOpens) (V : X.affineOpens) (e) : Q (f.appLE U V e).hom := by
  rw [eq_affineLocally P, affineLocally_iff_affineOpens_le] at H
  exact H _ _ _
/-
**AlgebraicGeometry.HasRingHomProperty.appTop** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.HasRingHomProperty`。
形式化陈述：appTop (H : P f) [IsAffine X] [IsAffine Y] : Q f.appTop.hom
参数：H : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appTop.eq_1`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y),   AlgebraicGeometry.Scheme.Hom.appTop f = AlgebraicGeometry.Sc
heme.Hom.app f ⊤
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.appLE`：appLE (H : P f) (U : Y.affin
eOpens) (V : X.affineOpens) (e) : Q (f.appLE U V e).hom
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
-/
theorem appTop (H : P f) [IsAffine X] [IsAffine Y] : Q f.appTop.hom := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact appLE P f H ⟨_, isAffineOpen_top _⟩ ⟨_, isAffineOpen_top _⟩ _

include Q in
/-
**AlgebraicGeometry.HasRingHomProperty.comp_of_isOpenImmersion** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：comp_of_isOpenImmersion [IsOpenImmersion f] (H : P g) : P (f ≫ g)
参数：H : P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`：eq_affineLocally 
: P = affineLocally Q
· 使用定理 `AlgebraicGeometry.affineLocally_iff_affineOpens_le`：affineLocally_iff_af
fineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) : affineLocally.{u} P f ↔ forall (U 
: Y.affineOpens) (V : X.affineOpens) (e …
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`：appLE_comp_appLE {X Y Z :
 Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : g.appLE U V e₁ ≫ f.appLE V W e₂
 = (f ≫ g).appLE U W (e₂.trans ((Op…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`：image_of_isOpen
Immersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen (f ''ᵁ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem comp_of_isOpenImmersion [IsOpenImmersion f] (H : P g) :
    P (f ≫ g) := by
  rw [eq_affineLocally P, affineLocally_iff_affineOpens_le] at H ⊢
  intro U V e
  have : IsIso (f.appLE (f ''ᵁ V) V.1 (f.preimage_image_eq _).ge) :=
    inferInstanceAs (IsIso (f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq _).symm).op))
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ (f ''ᵁ V) V.1
    (Set.image_subset_iff.mpr e) (f.preimage_image_eq _).ge,
    CommRingCat.hom_comp,
    (isLocal_ringHomProperty P).respectsIso.cancel_right_isIso]
  exact H _ ⟨_, V.2.image_of_isOpenImmersion _⟩ _

variable {P f}
/-
**AlgebraicGeometry.HasRingHomProperty.iff_appLE** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.HasRingHomProperty`。
形式化陈述：iff_appLE : P f ↔ forall (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f
.appLE U V e).hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`：eq_affineLocally 
: P = affineLocally Q
· 使用定理 `AlgebraicGeometry.affineLocally_iff_affineOpens_le`：affineLocally_iff_af
fineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) : affineLocally.{u} P f ↔ forall (U 
: Y.affineOpens) (V : X.affineOpens) (e …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iff_appLE : P f ↔ ∀ (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f.appLE U V e).hom := by
  rw [eq_affineLocally P, affineLocally_iff_affineOpens_le]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasRingHomProperty.of_source_openCover** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：of_source_openCover [IsAffine Y] (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.
X i)] (H : forall i, Q ((𝒰.f i ≫ f).appTop.hom)) : P f
参数：𝒰 : X.OpenCover；𝒰.X i；H : forall i, Q ((𝒰.f i ≫ f).appTop.hom)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.HasAffineProperty`：HasAffinePropert
y : HasAffineProperty P (sourceAffineLocally Q) where isLocal_affineProperty
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `AlgebraicGeometry.of_affine_open_cover`：of_affine_open_cover {X : Scheme
} {P : X.affineOpens -> Prop} {ι} (U : ι -> X.affineOpens) (iSup_U : (⨆ i, U i :
 X.Opens) = ⊤) (V : X.affine…
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `RingHom.PropertyIsLocal.StableUnderCompositionWithLocalizationAwayTarget
`：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S
) → Prop},   RingHom.PropertyIsLocal P → RingHom.StableUnderCo…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用引理 `RingHom.OfLocalizationSpanTarget.ofIsLocalization`：RingHom.OfLocalizatio
nSpanTarget.ofIsLocalization (hP : RingHom.OfLocalizationSpanTarget P) (hP' : Ri
ngHom.RespectsIso P) {R S : Type u} [Co…
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpanTarget`：∀ {P : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pro
pertyIsLocal P → RingHom.OfLocalizatio…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 40 条，此处仅展示前 30 条）
-/
theorem of_source_openCover [IsAffine Y]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] (H : ∀ i, Q ((𝒰.f i ≫ f).appTop.hom)) :
    P f := by
  rw [HasAffineProperty.iff_of_isAffine (P := P)]
  intro U
  let S i : X.affineOpens := ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩
  induction U using of_affine_open_cover S 𝒰.iSup_opensRange with
  | basicOpen U r H =>
    simp_rw [Scheme.affineBasicOpen_coe,
      ← f.appLE_map (U := ⊤) le_top (homOfLE (X.basicOpen_le r)).op]
    have := U.2.isLocalization_basicOpen r
    exact (isLocal_ringHomProperty P).StableUnderCompositionWithLocalizationAwayTarget _ r _ H
  | openCover U s hs H =>
    apply (isLocal_ringHomProperty P).ofLocalizationSpanTarget.ofIsLocalization
      (isLocal_ringHomProperty P).respectsIso _ _ hs
    rintro r
    refine ⟨_, _, _, IsAffineOpen.isLocalization_basicOpen U.2 r, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    exact H r
  | hU i =>
    specialize H i
    rw [← (isLocal_ringHomProperty P).respectsIso.cancel_right_isIso _
      ((IsOpenImmersion.isoOfRangeEq (𝒰.f i) (S i).1.ι
      Subtype.range_coe.symm).inv.app _), ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
      IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, Scheme.Hom.comp_appTop,
      Scheme.Opens.ι_appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map] at H
    exact (f.appLE_congr _ rfl (by simp) (fun f => Q f.hom)).mp H
/-
**AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：iff_of_source_openCover [IsAffine Y] (𝒰 : X.OpenCover) [forall i, IsAffine
 (𝒰.X i)] : P f ↔ forall i, Q ((𝒰.f i ≫ f).appTop).hom
参数：𝒰 : X.OpenCover；𝒰.X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.appTop`：appTop (H : P f) [IsAffine 
X] [IsAffine Y] : Q f.appTop.hom
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.comp_of_isOpenImmersion`：comp_of_is
OpenImmersion [IsOpenImmersion f] (H : P g) : P (f ≫ g)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.of_source_openCover`：of_source_open
Cover [IsAffine Y] (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.X i)] (H : forall i,
 Q ((𝒰.f i ≫ f).appTop.hom)) : P f
-/
theorem iff_of_source_openCover [IsAffine Y] (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    P f ↔ ∀ i, Q ((𝒰.f i ≫ f).appTop).hom :=
  ⟨fun H i ↦ appTop P _ (comp_of_isOpenImmersion P (𝒰.f i) f H), of_source_openCover 𝒰⟩

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：iff_of_isAffine [IsAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover`：iff_of_sou
rce_openCover [IsAffine Y] (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.X i)] : P f 
↔ forall i, Q ((𝒰.f i ≫ f).appTop).hom
· 使用定理 `AlgebraicGeometry.instIsAffineXSchemeCoverOfIsIsoIsOpenImmersionId`：∀ {X
 : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X]   (i : (AlgebraicGeo
metry.Scheme.coverOfIsIso (CategoryTheory.CategoryStruct…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_of_isAffine [IsAffine X] [IsAffine Y] :
    P f ↔ Q (f.appTop).hom := by
  rw [iff_of_source_openCover (P := P) (Scheme.coverOfIsIso.{u} (𝟙 _))]
  simp +instances
/-
**AlgebraicGeometry.HasRingHomProperty.Spec_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.HasRingHomProperty`。
形式化陈述：Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality`：ΓSpecIso_naturality {R S :
 CommRingCat.{u}} (f : R ⟶ S) : (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecI
so R).hom ≫ f
· 使用定理 `RingHom.RespectsIso.cancel_left_isIso`：∀ {P : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P 
→     ∀ {R S T : CommRingCa…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    P (Spec.map φ) ↔ Q φ.hom := by
  have H := (isLocal_ringHomProperty P).respectsIso
  rw [iff_of_isAffine (P := P), ← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, H.cancel_left_isIso]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasRingHomProperty.of_iSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：of_iSup_eq_top [IsAffine Y] {ι : Type*} (U : ι -> X.affineOpens) (hU : ⨆ i
, (U i : Opens X) = ⊤) (H : forall i, Q (f.appLE ⊤ (U i).1 le_top).hom) : P f
参数：U : ι -> X.affineOpens；hU : ⨆ i, (U i : Opens X) = ⊤；H : forall i, Q (f.appLE
 ⊤ (U i).1 le_top).hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.of_source_openCover`：of_source_open
Cover [IsAffine Y] (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.X i)] (H : forall i,
 Q ((𝒰.f i ≫ f).appTop.hom)) : P f
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.openCoverOfIsOpenCover_f`：∀ {s : Type u_1} (X :
 AlgebraicGeometry.Scheme) (U : s → X.Opens) (hU : TopologicalSpace.IsOpenCover 
U) (i : s),   (X.openCoverOfIsOpenCover…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_appLE`：comp_appLE {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (U V e) : (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_appLE`：ι_appLE (V W e) : U.ι.appLE V W 
e = X.presheaf.map (homOfLE (x
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_congr`：appLE_congr (e : V <= f ⁻¹ᵁ U)
 (e₁ : U = U') (e₂ : V = V') (P : forall {R S : CommRingCat.{u}} (_ : R ⟶ S), Pr
op) : P (f.appLE U V e) ↔ P (f…
-/
theorem of_iSup_eq_top [IsAffine Y] {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i : Opens X) = ⊤)
    (H : ∀ i, Q (f.appLE ⊤ (U i).1 le_top).hom) :
    P f := by
  have (i : _) : IsAffine ((X.openCoverOfIsOpenCover _ hU).X i) := (U i).2
  refine of_source_openCover (X.openCoverOfIsOpenCover _ hU) fun i ↦ ?_
  simpa [Scheme.Hom.app_eq_appLE] using (f.appLE_congr _ rfl (by simp) (fun f => Q f.hom)).mp (H i)
/-
**AlgebraicGeometry.HasRingHomProperty.iff_of_iSup_eq_top** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：iff_of_iSup_eq_top [IsAffine Y] {ι : Type*} (U : ι -> X.affineOpens) (hU :
 ⨆ i, (U i : Opens X) = ⊤) : P f ↔ forall i, Q (f.appLE ⊤ (U i).1 le_top).hom
参数：U : ι -> X.affineOpens；hU : ⨆ i, (U i : Opens X) = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.appLE`：appLE (H : P f) (U : Y.affin
eOpens) (V : X.affineOpens) (e) : Q (f.appLE U V e).hom
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.of_iSup_eq_top`：of_iSup_eq_top [IsA
ffine Y] {ι : Type*} (U : ι -> X.affineOpens) (hU : ⨆ i, (U i : Opens X) = ⊤) (H
 : forall i, Q (f.appLE ⊤ (U i).1 le_top)…
-/
theorem iff_of_iSup_eq_top [IsAffine Y] {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i : Opens X) = ⊤) :
    P f ↔ ∀ i, Q (f.appLE ⊤ (U i).1 le_top).hom :=
  ⟨fun H _ ↦ appLE P f H ⟨_, isAffineOpen_top _⟩ _ le_top, of_iSup_eq_top U hU⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasRingHomProperty.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.HasRingHomProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtSource P := by
  apply HasAffineProperty.isZariskiLocalAtSource
  intro X Y f _ 𝒰
  simp_rw [← HasAffineProperty.iff_of_isAffine (P := P),
    iff_of_source_openCover 𝒰.affineRefinement.openCover,
    fun i ↦ iff_of_source_openCover (P := P) (f := 𝒰.f i ≫ f) (𝒰.X i).affineCover]
  simp [Scheme.OpenCover.affineRefinement, Sigma.forall]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasRingHomProperty.containsIdentities** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：containsIdentities (hP : RingHom.ContainsIdentities Q) : P.ContainsIdentit
ies where id_mem X
参数：hP : RingHom.ContainsIdentities Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.morphismRestrict_id`：morphismRestrict_id {X : Scheme.{
u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.id_appTop`：id_appTop {X : Scheme} : (𝟙 X :)
.appTop = 𝟙 _
-/
lemma containsIdentities (hP : RingHom.ContainsIdentities Q) : P.ContainsIdentities where
  id_mem X := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    have : IsAffine (𝟙 X ⁻¹ᵁ U.1) := U.2
    rw [morphismRestrict_id, iff_of_isAffine (P := P), Scheme.Hom.id_appTop]
    apply hP

set_option backward.isDefEq.respectTransparency false in
variable (P) in
open _root_.PrimeSpectrum in
/-
**AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty_of_isZariskiLocal
AtSource_of_isZariskiLocalAtTarget** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.
HasRingHomProperty`。
形式化陈述：isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarge
t [IsZariskiLocalAtTarget P] [IsZariskiLocalAtSource P] : RingHom.PropertyIsLoca
l fun f => P (Spec.map (CommRingCat.ofHom f))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.RespectsIso.isLocalization_away_iff`：∀ {P : {R S : Type u} → [in
st : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Respects
Iso P →     ∀ {R S : Type u} (R' …
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_openCover`：of_openCover (H :
 forall i, P (𝒰.f i ≫ f)) : P f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.AffineOpenCover.openCover_f`：∀ {X : AlgebraicGe
ometry.Scheme} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀), 𝒰.openCover.f j = 𝒰.f j
· 使用定理 `AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop_f`：∀ {R : CommR
ingCat} {ι : Type u_1} (s : ι → ↑R) (hs : Ideal.span (Set.range s) = ⊤) (i : ι),
   (AlgebraicGeometry.Scheme.affineOpenCoverOfSp…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top`：of_iSup_eq_top 
{ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) (H : forall i, P (f ∣_ U i)) : P f
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff`：iSup_basicOpen_eq_top_iff {ι : 
Type*} {f : ι -> R} : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span 
(Set.range f) = ⊤
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isLocalization`：∀ {R S : Type u_1} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (f : R) [IsLoca
lization.Away f S],   AlgebraicGeometry.I…
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
-/
lemma isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
    [IsZariskiLocalAtTarget P] [IsZariskiLocalAtSource P] :
    RingHom.PropertyIsLocal fun f ↦ P (Spec.map (CommRingCat.ofHom f)) := by
  have hP : RingHom.RespectsIso (fun f ↦ P (Spec.map (CommRingCat.ofHom f))) :=
    RingHom.toMorphismProperty_respectsIso_iff.mpr
      (inferInstanceAs (P.inverseImage Scheme.Spec).unop.RespectsIso)
  constructor
  · intro R S _ _ f r R' S' _ _ _ _ _ _ H
    refine (RingHom.RespectsIso.isLocalization_away_iff hP ..).mp ?_
    exact (MorphismProperty.arrow_mk_iso_iff P (SpecMapRestrictBasicOpenIso
      (CommRingCat.ofHom f) r)).mp (IsZariskiLocalAtTarget.restrict H (basicOpen r))
  · intro R S _ _ f s hs H
    apply IsZariskiLocalAtSource.of_openCover (Scheme.affineOpenCoverOfSpanRangeEqTop
      (fun i : s ↦ (i : S)) (by simpa)).openCover
    intro i
    simp only [CommRingCat.coe_of, ← Spec.map_comp,
      Scheme.AffineOpenCover.openCover_f, Scheme.affineOpenCoverOfSpanRangeEqTop_f]
    exact H i
  · intro R S _ _ f s hs H
    apply IsZariskiLocalAtTarget.of_iSup_eq_top _ (PrimeSpectrum.iSup_basicOpen_eq_top_iff
      (f := fun i : s ↦ (i : R)).mpr (by simpa))
    intro i
    exact (MorphismProperty.arrow_mk_iso_iff P (SpecMapRestrictBasicOpenIso
      (CommRingCat.ofHom f) i.1)).mpr (H i)
  · intro R S T _ _ _ _ r _ f hf
    have := AlgebraicGeometry.IsOpenImmersion.of_isLocalization (S := T) r
    change P (Spec.map (CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap _ _)))
    rw [Spec.map_comp]
    exact IsZariskiLocalAtSource.comp hf ..

open _root_.PrimeSpectrum in
variable (P) in
/-
**AlgebraicGeometry.HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLoc
alAtTarget** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget [IsZariskiLocalAtTarge
t P] [IsZariskiLocalAtSource P] : HasRingHomProperty P (fun f => P (Spec.map (Co
mmRingCat.ofHom f))) where isLocal_ringHomProperty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty_of_isZarisk
iLocalAtSource_of_isZariskiLocalAtTarget`：isLocal_ringHomProperty_of_isZariskiLo
calAtSource_of_isZariskiLocalAtTarget [IsZariskiLocalAtTarget P] [IsZariskiLocal
AtSource P] : RingHom.…
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
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
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
-/
lemma of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget [IsZariskiLocalAtTarget P]
    [IsZariskiLocalAtSource P] :
    HasRingHomProperty P (fun f ↦ P (Spec.map (CommRingCat.ofHom f))) where
  isLocal_ringHomProperty :=
    isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget P
  eq_affineLocally' := by
    let Q := affineLocally (fun f ↦ P (Spec.map (CommRingCat.ofHom f)))
    have : HasRingHomProperty Q (fun f ↦ P (Spec.map (CommRingCat.ofHom f))) :=
      ⟨isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget P, rfl⟩
    change P = Q
    ext X Y f
    wlog hY : ∃ R, Y = Spec R generalizing X Y
    · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) Y.affineCover,
        IsZariskiLocalAtTarget.iff_of_openCover (P := Q) Y.affineCover]
      refine forall_congr' fun _ ↦ this _ ⟨_, rfl⟩
    obtain ⟨S, rfl⟩ := hY
    wlog hX : ∃ R, X = Spec R generalizing X
    · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) X.affineCover,
        IsZariskiLocalAtSource.iff_of_openCover (P := Q) X.affineCover]
      refine forall_congr' fun _ ↦ this _ ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
    rw [HasRingHomProperty.Spec_iff (P := Q)]
    rfl
/-
**AlgebraicGeometry.HasRingHomProperty.inf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.HasRingHomProperty`。
形式化陈述：inf {P P' : MorphismProperty Scheme.{u}} {Q Q' : forall {R S : Type u} [Co
mmRing R] [CommRing S], (R ->+* S) -> Prop} [HasRingHomProperty P Q] [HasRingHom
Property P' Q'] : HasRingHomProperty (P ⊓ P') (fun f => Q f ∧ Q' f) where isLoca
l_ringHomProperty
参数：R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.PropertyIsLocal.and`：RingHom.PropertyIsLocal.and (hP : PropertyI
sLocal P) (hQ : PropertyIsLocal Q) : PropertyIsLocal (fun f => P f ∧ Q f) where 
localizationAwayP…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`：eq_affineLocally 
: P = affineLocally Q
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma inf {P P' : MorphismProperty Scheme.{u}}
    {Q Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] [HasRingHomProperty P' Q'] :
    HasRingHomProperty (P ⊓ P') (fun f ↦ Q f ∧ Q' f) where
  isLocal_ringHomProperty :=
    .and (HasRingHomProperty.isLocal_ringHomProperty P)
      (HasRingHomProperty.isLocal_ringHomProperty P')
  eq_affineLocally' := by
    rw [HasRingHomProperty.eq_affineLocally P, HasRingHomProperty.eq_affineLocally P']
    ext
    change _ ∧ _ ↔ _
    simp_rw [affineLocally_iff_affineOpens_le]
    grind
/-
**AlgebraicGeometry.HasRingHomProperty.stalkwise** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.HasRingHomProperty`。
形式化陈述：stalkwise {P} (hP : RingHom.RespectsIso P) : HasRingHomProperty (stalkwise
 P) fun {_ S _ _} φ => forall (p : Ideal S) (_ : p.IsPrime), P (Localization.loc
alRingHom _ p φ rfl)
参数：hP : RingHom.RespectsIso P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.stalkwiseIsZariskiLocalAtTarget_of_respectsIso`：stalkw
iseIsZariskiLocalAtTarget_of_respectsIso (hP : RingHom.RespectsIso P) : IsZarisk
iLocalAtTarget (stalkwise P)
· 使用引理 `AlgebraicGeometry.stalkwise_isZariskiLocalAtSource_of_respectsIso`：stalk
wise_isZariskiLocalAtSource_of_respectsIso (hP : RingHom.RespectsIso P) : IsZari
skiLocalAtSource (stalkwise P)
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `AlgebraicGeometry.stalkwise_SpecMap_iff`：stalkwise_SpecMap_iff (hP : Rin
gHom.RespectsIso P) {R S : CommRingCat} (φ : R ⟶ S) : stalkwise P (Spec.map φ) ↔
 forall (p : Ideal S) (_ : p.…
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.of_isZariskiLocalAtSource_of_isZari
skiLocalAtTarget`：of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget [IsZariski
LocalAtTarget P] [IsZariskiLocalAtSource P] : HasRingHomProperty P (fun f => P…
-/
lemma stalkwise {P} (hP : RingHom.RespectsIso P) :
    HasRingHomProperty (stalkwise P) fun {_ S _ _} φ ↦
      ∀ (p : Ideal S) (_ : p.IsPrime), P (Localization.localRingHom _ p φ rfl) := by
  have := stalkwiseIsZariskiLocalAtTarget_of_respectsIso hP
  have := stalkwise_isZariskiLocalAtSource_of_respectsIso hP
  convert!
    of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget (P := AlgebraicGeometry.stalkwise P) with R
    S _ _ φ
  exact (stalkwise_SpecMap_iff hP (CommRingCat.ofHom φ)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.HasRingHomProperty.stableUnderComposition** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：stableUnderComposition (hP : RingHom.StableUnderComposition Q) : P.IsStabl
eUnderComposition where comp_mem {X Y Z} f g hf hg
参数：hP : RingHom.StableUnderComposition Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.comp_of_isOpenImmersion`：comp_of_is
OpenImmersion [IsOpenImmersion f] (H : P g) : P (f ≫ g)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Cover.pullbackHom_map_assoc`：∀ {P : CategoryThe
ory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBaseChange
]   [inst_1 : AlgebraicGeometry.Scheme.IsJ…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`：of_isPullback {U
X UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY] {iX : UX ⟶ X} {f' : UX ⟶ U
Y} (h : IsPullback iX f' f iY) (H : P f) : P…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma stableUnderComposition (hP : RingHom.StableUnderComposition Q) :
    P.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ _ (IsZariskiLocalAtTarget.restrict hf _)
        (IsZariskiLocalAtTarget.restrict hg _) U.2
    wlog hY : IsAffine Y generalizing X Y
    · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Y.affineCover.pullback₁ f)]
      intro i
      rw [← Scheme.Cover.pullbackHom_map_assoc]
      exact this _ _ (IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hf)
        (comp_of_isOpenImmersion _ _ _ hg) inferInstance
    wlog hX : IsAffine X generalizing X
    · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) X.affineCover]
      intro i
      rw [← Category.assoc]
      exact this _ (comp_of_isOpenImmersion _ _ _ hf) inferInstance
    rw [iff_of_isAffine (P := P)] at hf hg ⊢
    exact hP _ _ hg hf
/-
**AlgebraicGeometry.HasRingHomProperty.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.HasRingHomProperty`。
形式化陈述：of_comp (H : forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T
], forall (f : R ->+* S) (g : S ->+* T), Q (g.comp f) -> Q g) {X Y Z : Scheme.{u
}} {f : X ⟶ Y} {g : Y ⟶ Z} (h : P (f ≫ g)) : P f
参数：H : forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T], forall (f
 : R ->+* S) (g : S ->+* T), Q (g.comp f) -> Q g；h : P (f ≫ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P ((U i).ι ≫ 
f)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.comp_of_isOpenImmersion`：comp_of_is
OpenImmersion [IsOpenImmersion f] (H : P g) : P (f ≫ g)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι_assoc`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (U : Y.Opens) {Z : AlgebraicGeometry.Scheme} (h : Y ⟶ Z),   C
ategoryTheory.CategoryStruct.com…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.iSup_preimage_eq_top`：iSup_preimage_eq_top 
{ι} {U : ι -> Opens Y} (hU : iSup U = ⊤) : ⨆ i, f ⁻¹ᵁ U i = ⊤
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
-/
theorem of_comp
    (H : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (g : S →+* T), Q (g.comp f) → Q g)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (h : P (f ≫ g)) : P f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H := comp_of_isOpenImmersion P (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    exact this H inferInstance
  wlog hY : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H := comp_of_isOpenImmersion P U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [iff_of_isAffine (P := P)] at h ⊢
  exact H _ _ h
/-
**AlgebraicGeometry.HasRingHomProperty.isMultiplicative** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：isMultiplicative (hPc : RingHom.StableUnderComposition Q) (hPi : RingHom.C
ontainsIdentities Q) : P.IsMultiplicative where comp_mem
参数：hPc : RingHom.StableUnderComposition Q；hPi : RingHom.ContainsIdentities Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.containsIdentities`：containsIdentit
ies (hP : RingHom.ContainsIdentities Q) : P.ContainsIdentities where id_mem X
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.comp_mem`：∀ {C 
: Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morphism
Property C}   [self : P.IsStableUnderComposition] {X Y …
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.stableUnderComposition`：stableUnder
Composition (hP : RingHom.StableUnderComposition Q) : P.IsStableUnderComposition
 where comp_mem {X Y Z} f g hf hg
-/
lemma isMultiplicative (hPc : RingHom.StableUnderComposition Q)
    (hPi : RingHom.ContainsIdentities Q) :
    P.IsMultiplicative where
  comp_mem := (stableUnderComposition hPc).comp_mem
  id_mem := (containsIdentities hPi).id_mem

include Q in
/-
**AlgebraicGeometry.HasRingHomProperty.of_isOpenImmersion** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：of_isOpenImmersion (hP : RingHom.ContainsIdentities Q) [IsOpenImmersion f]
 : P f
参数：hP : RingHom.ContainsIdentities Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`：of_isOpenIm
mersion [P.ContainsIdentities] [IsOpenImmersion f] : P f
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.containsIdentities`：containsIdentit
ies (hP : RingHom.ContainsIdentities Q) : P.ContainsIdentities where id_mem X
-/
lemma of_isOpenImmersion (hP : RingHom.ContainsIdentities Q) [IsOpenImmersion f] : P f :=
  haveI : P.ContainsIdentities := containsIdentities hP
  IsZariskiLocalAtSource.of_isOpenImmersion f

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：isStableUnderBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsSta
bleUnderBaseChange
参数：hP : RingHom.IsStableUnderBaseChange Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.Aff
ineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.HasAffineProperty`：HasAffinePropert
y : HasAffineProperty P (sourceAffineLocally Q) where isLocal_affineProperty
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsStableUnderBaseChange.m
k`：∀ (P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.Respects
Iso],   (∀ ⦃X Y S : AlgebraicGeometry.Scheme⦄ [inst : Algebraic…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `RingHom.IsStableUnderBaseChange.pullback_fst_appTop`：∀ (P : {R S : Type 
u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop),   (RingHom
.IsStableUnderBaseChange fun {R S} [CommR…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.openCoverOfRight_f`：∀ {X Y Z : Algebra
icGeometry.Scheme} (𝒰 : Y.OpenCover) (f : X ⟶ Z) (g : Y ⟶ Z) (i : 𝒰.I₀),   (Alge
braicGeometry.Scheme.Pullback.openCoverOfR…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.comp_of_isOpenImmersion`：comp_of_is
OpenImmersion [IsOpenImmersion f] (H : P g) : P (f ≫ g)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
-/
lemma isStableUnderBaseChange (hP : RingHom.IsStableUnderBaseChange Q) :
    P.IsStableUnderBaseChange := by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty P
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g H
  rw [← HasAffineProperty.iff_of_isAffine (P := P)] at H ⊢
  wlog hX : IsAffine Y generalizing Y
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P)
      (Scheme.Pullback.openCoverOfRight Y.affineCover f g)]
    intro i
    simp only [Scheme.Pullback.openCoverOfRight_f, limit.lift_π, PullbackCone.mk_π_app,
      Category.comp_id]
    apply this _ (comp_of_isOpenImmersion _ _ _ H) inferInstance
  rw [iff_of_isAffine (P := P)] at H ⊢
  exact hP.pullback_fst_appTop _ (isLocal_ringHomProperty P).respectsIso _ _ H

include Q in
/-
**AlgebraicGeometry.HasRingHomProperty.respects_isOpenImmersion_aux** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma respects_isOpenImmersion_aux
    (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    {X Y : Scheme.{u}} [IsAffine Y] {U : Y.Opens}
    (f : X ⟶ U.toScheme) (hf : P f) : P (f ≫ U.ι) := by
  wlog hYa : ∃ (a : Γ(Y, ⊤)), U = Y.basicOpen a generalizing X Y
  · obtain ⟨(Us : Set Y.Opens), hUs, heq⟩ := Opens.isBasis_iff_cover.mp (isBasis_basicOpen Y) U
    let V (s : Us) : X.Opens := f ⁻¹ᵁ U.ι ⁻¹ᵁ s
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) V]
    · intro s
      let f' : (V s).toScheme ⟶ U.ι ⁻¹ᵁ s := f ∣_ U.ι ⁻¹ᵁ s
      have hf' : P f' := IsZariskiLocalAtTarget.restrict hf _
      let e : (U.ι ⁻¹ᵁ s).toScheme ≅ s := IsOpenImmersion.isoOfRangeEq ((U.ι ⁻¹ᵁ s).ι ≫ U.ι) s.1.ι
        (by simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
          Opens.map_coe, Set.image_preimage_eq_iff, heq, Opens.coe_sSup] using! le_sSup s.2)
      have heq : (V s).ι ≫ f ≫ U.ι = f' ≫ e.hom ≫ s.1.ι := by
        simp only [V, IsOpenImmersion.isoOfRangeEq_hom_fac, f', e, morphismRestrict_ι_assoc]
      rw [heq, ← Category.assoc]
      refine this _ ?_ ?_
      · rwa [P.cancel_right_of_respectsIso]
      · obtain ⟨a, ha⟩ := hUs s.2
        use a, ha.symm
    · apply f.iSup_preimage_eq_top
      apply U.ι.image_injective
      simp only [U.ι.image_iSup, U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      conv_rhs => rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι, heq]
      ext : 1
      have (i : Us) : U ⊓ i.1 = i.1 := by simp [heq, le_sSup i.property]
      simp [this]
  obtain ⟨a, rfl⟩ := hYa
  wlog hX : IsAffine X generalizing X Y
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro V
    rw [← Category.assoc]
    exact this _ _ (IsZariskiLocalAtSource.comp hf _) V.2
  rw [HasRingHomProperty.iff_of_isAffine (P := P)] at hf ⊢
  exact hQ _ a _ hf

/-- Any property of scheme morphisms induced by a property of ring homomorphisms is stable
under composition with open immersions. -/
/-
**AlgebraicGeometry.HasRingHomProperty.respects_isOpenImmersion** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：respects_isOpenImmersion (hQ : RingHom.StableUnderCompositionWithLocalizat
ionAwaySource Q) : P.Respects @IsOpenImmersion where postcomp {X Y Z} i hi f hf
参数：hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac`：isoOfRangeEq_hom
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties.0.Algebra
icGeometry.HasRingHomProperty.respects_isOpenImmersion_aux`：∀ {P : CategoryTheor
y.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} → [inst : Com
mRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionMorphismRestrict`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens) [AlgebraicGeometry.IsOpenImmersion f
],   AlgebraicGeometry.IsOpenImmersion (f ∣…
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Any property of scheme morphisms induced by a property of ring homomorphisms is 
stable
under composition with open immersions.
-/
lemma respects_isOpenImmersion (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q) :
    P.Respects @IsOpenImmersion where
  postcomp {X Y Z} i hi f hf := by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ inferInstance _ (IsZariskiLocalAtTarget.restrict hf _) U.2
    let e : Y ≅ i.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by simp)
    rw [show f ≫ i = f ≫ e.hom ≫ i.opensRange.ι by simp [e], ← Category.assoc]
    exact respects_isOpenImmersion_aux hQ _ (by rwa [P.cancel_right_of_respectsIso])

open RingHom

omit [HasRingHomProperty P Q] in
/-- If `P` is induced by `Locally Q`, it suffices to check `Q` on affine open sets locally around
points of the source. -/
/-
**AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE_locally** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：iff_exists_appLE_locally (hQ : RingHom.StableUnderCompositionWithLocalizat
ionAwaySource Q) (hQi : RespectsIso Q) [HasRingHomProperty P (Locally Q)] : P f 
↔ forall (x : X), exists (U : Y.affineOpens) (V : X.affineOpens) (_ : x in V.1) 
(e : V.1 <= f ⁻¹ᵁ U.1), Q (f.appLE U V e).hom
参数：hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q；hQi : Respect
sIso Q；Locally Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.respects_isOpenImmersion`：respects_
isOpenImmersion (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q
) : P.Respects @IsOpenImmersion where postcomp {X Y…
· 使用引理 `RingHom.locally_stableUnderCompositionWithLocalizationAwaySource`：locall
y_stableUnderCompositionWithLocalizationAwaySource (hPa : StableUnderComposition
WithLocalizationAwaySource P) : StableUnderComposition…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用引理 `TopologicalSpace.Opens.mem_top`：mem_top (x : α) : x in (⊤ : Opens α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `RingHom.locally_iff_isLocalization`：locally_iff_isLocalization (hP : Res
pectsIso P) (f : R ->+* S) : Locally P f ↔ exists (s : Finset S) (_ : Ideal.span
 (s : Set S) = ⊤), foral…
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.iff_appLE`：iff_appLE : P f ↔ forall
 (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f.appLE U V e).hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.iSup_basicOpen_of_span_eq_top`：iSup_basicOpen_of_span_
eq_top {X : Scheme} (U) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) : (⨆ i in s, X
.basicOpen i) = U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_exists_resLE`：iff_exists_re
sLE [IsZariskiLocalAtTarget P] [P.RespectsRight @IsOpenImmersion] : P f ↔ forall
 x : X, exists (U : Y.Opens) (V : X.Opens) (_ :…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `P` is induced by `Locally Q`, it suffices to check `Q` on affine open sets l
ocally around
points of the source.
-/
lemma iff_exists_appLE_locally
    (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    (hQi : RespectsIso Q) [HasRingHomProperty P (Locally Q)] :
    P f ↔ ∀ (x : X), ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      Q (f.appLE U V e).hom := by
  have := respects_isOpenImmersion (P := P)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource hQ)
  refine ⟨fun hf x ↦ ?_,
      fun hf ↦ (IsZariskiLocalAtSource.iff_exists_resLE (P := P)).mpr <| fun x ↦ ?_⟩
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top <| f x)
    obtain ⟨V, hV, hx, e⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ U from hfx)
    simp_rw [HasRingHomProperty.iff_appLE (P := P), locally_iff_isLocalization hQi] at hf
    obtain ⟨s, hs, hfs⟩ := hf ⟨U, hU⟩ ⟨V, hV⟩ e
    apply iSup_basicOpen_of_span_eq_top at hs
    have : x ∈ (⨆ i ∈ s, X.basicOpen i) := hs.symm ▸ hx
    have : ∃ r ∈ s, x ∈ X.basicOpen r := by simpa using this
    obtain ⟨r, hr, hrs⟩ := this
    refine ⟨⟨U, hU⟩, ⟨X.basicOpen r, hV.basicOpen r⟩, hrs, (X.basicOpen_le r).trans e, ?_⟩
    rw [← f.appLE_map e (homOfLE (X.basicOpen_le r)).op]
    have : IsLocalization.Away r Γ(X, X.basicOpen r) := hV.isLocalization_basicOpen r
    exact hfs r hr _
  · obtain ⟨U, V, hxV, e, hf⟩ := hf x
    use U, V, hxV, e
    simp only [iff_of_isAffine (P := P), Scheme.Hom.appLE, homOfLE_leOfHom] at hf ⊢
    have : (toMorphismProperty (Locally Q)).RespectsIso := toMorphismProperty_respectsIso_iff.mp <|
      (isLocal_ringHomProperty P).respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (toMorphismProperty (Locally Q))
      (arrowResLEAppIso f U V e)).mpr (locally_of hQi _ hf)

/-- `P` can be checked locally around points of the source. -/
/-
**AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：iff_exists_appLE (hQ : StableUnderCompositionWithLocalizationAwaySource Q)
 : P f ↔ forall (x : X), exists (U : Y.affineOpens) (V : X.affineOpens) (_ : x i
n V.1) (e : V.1 <= f ⁻¹ᵁ U.1), Q (f.appLE U V e).hom
参数：hQ : StableUnderCompositionWithLocalizationAwaySource Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.copy`：copy {P' : MorphismProperty S
cheme.{u}} {Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> 
Prop} (e : P = P') (e' : forall…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `RingHom.locally_iff_of_localizationSpanTarget`：locally_iff_of_localizati
onSpanTarget (hPi : RespectsIso P) (hPs : OfLocalizationSpanTarget P) {R S : Typ
e u} [CommRing R] [CommRing S] (f :…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpanTarget`：∀ {P : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pro
pertyIsLocal P → RingHom.OfLocalizatio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE_locally`：iff_exist
s_appLE_locally (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q
) (hQi : RespectsIso Q) [HasRingHomProperty P (Loca…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`P` can be checked locally around points of the source.
-/
lemma iff_exists_appLE
    (hQ : StableUnderCompositionWithLocalizationAwaySource Q) : P f ↔
    ∀ (x : X), ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      Q (f.appLE U V e).hom := by
  have inst : HasRingHomProperty P Q := inferInstance
  have : HasRingHomProperty P (Locally Q) := by
    apply @copy (P := P) (P' := P) (Q := Q) (Q' := Locally Q)
    · infer_instance
    · rfl
    · intro R S _ _ f
      exact (locally_iff_of_localizationSpanTarget (isLocal_ringHomProperty P).respectsIso
        (isLocal_ringHomProperty P).ofLocalizationSpanTarget _).symm
  rw [iff_exists_appLE_locally (P := P) hQ]
  have : HasRingHomProperty P Q := inst
  apply (isLocal_ringHomProperty P (Q := Q)).respectsIso

omit [HasRingHomProperty P Q] in
/-
**AlgebraicGeometry.HasRingHomProperty.locally_of_iff** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：locally_of_iff (hQl : LocalizationAwayPreserves Q) (hQa : StableUnderCompo
sitionWithLocalizationAway Q) (h : forall {X Y : Scheme.{u}} (f : X ⟶ Y), P f ↔ 
forall (x : X), exists (U : Y.affineOpens) (V : X.affineOpens) (_ : x in V.1) (e
 : V.1 <= f ⁻¹ᵁ U.1), Q (f.appLE U V e).hom) : HasRingHomProperty P (Locally Q) 
where isLocal_ringHomProperty
参数：hQl : LocalizationAwayPreserves Q；hQa : StableUnderCompositionWithLocalizatio
nAway Q；h : forall {X Y : Scheme.{u}} (f : X ⟶ Y), P f ↔ forall (x : X), exists 
(U : Y.affineOpens) (V : X.affineOpens) (_ : x in V.1) (e : V.1 <= f ⁻¹ᵁ U.1), Q
 (f.appLE U V e).hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.locally_propertyIsLocal`：locally_propertyIsLocal (hPl : Localiza
tionAwayPreserves P) (hPa : StableUnderCompositionWithLocalizationAway P) : Prop
ertyIsLocal (Locally …
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE_locally`：iff_exist
s_appLE_locally (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q
) (hQi : RespectsIso Q) [HasRingHomProperty P (Loca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.StableUnderCompositionWithLocalizationAway.respectsIso`：RingHom.
StableUnderCompositionWithLocalizationAway.respectsIso (hP : StableUnderComposit
ionWithLocalizationAway P) : RespectsIso P where lef…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma locally_of_iff (hQl : LocalizationAwayPreserves Q)
    (hQa : StableUnderCompositionWithLocalizationAway Q)
    (h : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), P f ↔
      ∀ (x : X), ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      Q (f.appLE U V e).hom) : HasRingHomProperty P (Locally Q) where
  isLocal_ringHomProperty := locally_propertyIsLocal hQl hQa
  eq_affineLocally' := by
    have : HasRingHomProperty (affineLocally (Locally Q)) (Locally Q) :=
      ⟨locally_propertyIsLocal hQl hQa, rfl⟩
    ext X Y f
    rw [h, iff_exists_appLE_locally (P := affineLocally (Locally Q)) hQa.left hQa.respectsIso]

set_option backward.isDefEq.respectTransparency false in
/-- If `Q` is a property of ring maps that can be checked on prime ideals, the
associated property of scheme morphisms can be checked on stalks. -/
/-
**AlgebraicGeometry.HasRingHomProperty.of_stalkMap** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.HasRingHomProperty`。
形式化陈述：of_stalkMap (hQ : OfLocalizationPrime Q) (H : forall x, Q (f.stalkMap x).h
om) : P f
参数：hQ : OfLocalizationPrime Q；H : forall x, Q (f.stalkMap x).hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `RingHom.RespectsIso.arrow_mk_iso_iff`：∀ {P : {R S : Type u} → [inst : Co
mmRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.RespectsIso fu
n {R S} [CommRing R] [Comm…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `RingHom.RespectsIso.cancel_left_isIso`：∀ {P : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P 
→     ∀ {R S T : CommRingCa…
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P ((U i).ι ≫ 
f)
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If `Q` is a property of ring maps that can be checked on prime ideals, the
associated property of scheme morphisms can be checked on stalks.
-/
lemma of_stalkMap (hQ : OfLocalizationPrime Q) (H : ∀ x, Q (f.stalkMap x).hom) : P f := by
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
  wlog hY : IsAffine Y generalizing X Y f
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    refine this (fun x ↦ ?_) U.2
    exact (hQi.arrow_mk_iso_iff (AlgebraicGeometry.morphismRestrictStalkMap f U x)).mpr (H x.val)
  wlog hX : IsAffine X generalizing X f
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    refine this ?_ U.2
    intro x
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, hQi.cancel_right_isIso]
    exact H x.val
  wlog hXY : ∃ R S, Y = Spec R ∧ X = Spec S generalizing X Y
  · rw [← P.cancel_right_of_respectsIso (g := Y.isoSpec.hom)]
    rw [← P.cancel_left_of_respectsIso (f := X.isoSpec.inv)]
    refine this inferInstance (fun x ↦ ?_) inferInstance ?_
    · rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
        hQi.cancel_right_isIso, CommRingCat.hom_comp, hQi.cancel_left_isIso]
      apply H
    · use Γ(Y, ⊤), Γ(X, ⊤)
  obtain ⟨R, S, rfl, rfl⟩ := hXY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [Spec_iff (P := P)]
  apply hQ
  intro P hP
  specialize H ⟨P, hP⟩
  rwa [hQi.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ _)] at H

set_option backward.isDefEq.respectTransparency false in
/-- Let `Q` be a property of ring maps that implies `Q'` on stalks.
Then if the associated property of scheme morphisms holds for `f`, `Q'` holds on all stalks. -/
/-
**AlgebraicGeometry.HasRingHomProperty.stalkMap_of_respectsIso** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.HasRingHomProperty`。
形式化陈述：stalkMap_of_respectsIso {Q' : forall {R S : Type u} [CommRing R] [CommRing
 S], (R ->+* S) -> Prop} (hQ' : RingHom.RespectsIso Q') (hQ : forall {R S : Type
 u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f) (J : Ideal S) (_ : J.IsPr
ime), Q' (Localization.localRingHom _ J f rfl)) (hf : P f) (x : X) : Q' (f.stalk
Map x).hom
参数：R ->+* S；hQ' : RingHom.RespectsIso Q'；hQ : forall {R S : Type u} [CommRing R]
 [CommRing S] (f : R ->+* S) (_ : Q f) (J : Ideal S) (_ : J.IsPrime), Q' (Locali
zation.localRingHom _ J f rfl)；hf : P f；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.RespectsIso.arrow_mk_iso_iff`：∀ {P : {R S : Type u} → [inst : Co
mmRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.RespectsIso fu
n {R S} [CommRing R] [Comm…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.hom_inv_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (e : X ≅ Y) (x : ↥X), e.inv (e.hom x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.RespectsIso.cancel_left_isIso`：∀ {P : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P 
→     ∀ {R S T : CommRingCa…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用引理 `TopologicalSpace.Opens.mem_top`：mem_top (x : α) : x in (⊤ : Opens α)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.resLE`：resLE [IsZariskiLocalAtT
arget P] {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) (hf : P f) : P (f.resLE 
U V e)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Let `Q` be a property of ring maps that implies `Q'` on stalks.
Then if the associated property of scheme morphisms holds for `f`, `Q'` holds on
 all stalks.
-/
lemma stalkMap_of_respectsIso
    {Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ' : RingHom.RespectsIso Q')
    (hQ : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (_ : Q f)
      (J : Ideal S) (_ : J.IsPrime), Q' (Localization.localRingHom _ J f rfl))
    (hf : P f) (x : X) : Q' (f.stalkMap x).hom := by
  wlog h : IsAffine X ∧ IsAffine Y generalizing X Y f
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top <| f x)
    obtain ⟨V, hV, hx, e⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ U from hfx)
    rw [← hQ'.arrow_mk_iso_iff (Scheme.Hom.resLEStalkMap f e ⟨x, hx⟩)]
    exact this (IsZariskiLocalAtSource.resLE _ hf) _ ⟨hV, hU⟩
  obtain ⟨hX, hY⟩ := h
  wlog hXY : ∃ R S, Y = Spec R ∧ X = Spec S generalizing X Y
  · have : Q' ((X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom).stalkMap (X.isoSpec.hom x)).hom := by
      refine this ?_ (X.isoSpec.hom x) inferInstance inferInstance ?_
      · rwa [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
      · use Γ(Y, ⊤), Γ(X, ⊤)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      hQ'.cancel_right_isIso, CommRingCat.hom_comp, hQ'.cancel_left_isIso] at this
    have heq : (X.isoSpec.inv (X.isoSpec.hom x)) = x := by simp
    rwa [hQ'.arrow_mk_iso_iff (f.arrowStalkMapIsoOfEq heq)] at this
  obtain ⟨R, S, rfl, rfl⟩ := hXY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [hQ'.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ _)]
  rw [Spec_iff (P := P)] at hf
  apply hQ _ hf

/-- Let `Q` be a property of ring maps that is stable under localization.
Then if the associated property of scheme morphisms holds for `f`, `Q` holds on all stalks. -/
/-
**AlgebraicGeometry.HasRingHomProperty.stalkMap** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.HasRingHomProperty`。
形式化陈述：stalkMap (hQ : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+*
 S) (_ : Q f) (J : Ideal S) (_ : J.IsPrime), Q (Localization.localRingHom _ J f 
rfl)) (hf : P f) (x : X) : Q (f.stalkMap x).hom
参数：hQ : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f)
 (J : Ideal S) (_ : J.IsPrime), Q (Localization.localRingHom _ J f rfl)；hf : P f
；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.stalkMap_of_respectsIso`：stalkMap_o
f_respectsIso {Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) 
-> Prop} (hQ' : RingHom.RespectsIso Q') (hQ : fora…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty`：∀ (P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam ({R S : T
ype u} → [inst : CommRing R] → [inst_1 : CommRing …

--- 原说明 ---
Let `Q` be a property of ring maps that is stable under localization.
Then if the associated property of scheme morphisms holds for `f`, `Q` holds on 
all stalks.
-/
lemma stalkMap (hQ : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (_ : Q f)
      (J : Ideal S) (_ : J.IsPrime), Q (Localization.localRingHom _ J f rfl))
    (hf : P f) (x : X) : Q (f.stalkMap x).hom :=
  stalkMap_of_respectsIso (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso hQ hf x
/-
**AlgebraicGeometry.HasRingHomProperty.ext** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.HasRingHomProperty`。
形式化陈述：ext {P' : MorphismProperty Scheme.{u}} {Q' : forall {R S : Type u} [CommRi
ng R] [CommRing S], (R ->+* S) -> Prop} [HasRingHomProperty P' Q'] (h : forall {
R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S), Q f ↔ Q' f) : P = P'
参数：R ->+* S；h : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S), 
Q f ↔ Q' f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`：eq_affineLocally 
: P = affineLocally Q
· 使用定理 `AlgebraicGeometry.affineLocally_iff_affineOpens_le`：affineLocally_iff_af
fineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) : affineLocally.{u} P f ↔ forall (U 
: Y.affineOpens) (V : X.affineOpens) (e …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ext {P' : MorphismProperty Scheme.{u}}
    {Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P' Q']
    (h : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S), Q f ↔ Q' f) :
    P = P' := by
  ext f
  rw [HasRingHomProperty.eq_affineLocally (P := P), HasRingHomProperty.eq_affineLocally (P := P'),
    affineLocally_iff_affineOpens_le, affineLocally_iff_affineOpens_le]
  simp only [h]

end HasRingHomProperty

end AlgebraicGeometry

