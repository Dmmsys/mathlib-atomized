/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.RingTheory.RingHomProperties

/-!

# Constructors for properties of morphisms between schemes

This file provides some constructors to obtain morphism properties of schemes from other morphism
properties:

- `AffineTargetMorphismProperty.diagonal` : Given an affine target morphism property `P`,
  `P.diagonal f` holds if `P (pullback.mapDesc f₁ f₂ f)` holds for two affine open
  immersions `f₁` and `f₂`.
- `AffineTargetMorphismProperty.of`: Given a morphism property `P` of schemes,
  this is the restriction of `P` to morphisms with affine target. If `P` is local at the
  target, we have `(toAffineTargetMorphismProperty P).targetAffineLocally = P`, see:
  `MorphismProperty.targetAffineLocally_toAffineTargetMorphismProperty_eq_of_isZariskiLocalAtTarget`
- `MorphismProperty.topologically`: Given a property `P` of maps of topological spaces,
  `(topologically P) f` holds if `P` holds for the underlying continuous map of `f`.
- `MorphismProperty.stalkwise`: Given a property `P` of ring homomorphisms,
  `(stalkwise P) f` holds if `P` holds for all stalk maps.

Also provides API for showing the standard locality and stability properties for these
types of properties.

-/

@[expose] public section

universe u v w

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

section Diagonal

/-- The `AffineTargetMorphismProperty` associated to `(targetAffineLocally P).diagonal`.
See `diagonal_targetAffineLocally_eq_targetAffineLocally`.
-/
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.diagonal** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：AlgebraicGeometry.AffineTargetMorphismProperty → AlgebraicGeometry.AffineT
argetMorphismProperty
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g

--- 原说明 ---
The `AffineTargetMorphismProperty` associated to `(targetAffineLocally P).diagon
al`.
See `diagonal_targetAffineLocally_eq_targetAffineLocally`.
-/
def AffineTargetMorphismProperty.diagonal (P : AffineTargetMorphismProperty) :
    AffineTargetMorphismProperty :=
  fun {X _} f _ =>
    ∀ ⦃U₁ U₂ : Scheme⦄ (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：∀ (P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.Respe
ctsIso], P.diagonal.toProperty.RespectsIso
参数：P : AlgebraicGeometry.AffineTargetMorphismProperty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk`：respectsI
so_mk {P : AffineTargetMorphismProperty} (h₁ : forall {X Y Z} (e : X ≅ Y) (f : Y
 ⟶ Z) [IsAffine Z], P f -> P (e.hom ≫ f)) (h₂ : for…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.mapDesc_comp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ 
S)   (i' : S ⟶ S') [inst_1 : Cate…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_right_of_respectsI
so`：cancel_right_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty
.RespectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance AffineTargetMorphismProperty.diagonal_respectsIso (P : AffineTargetMorphismProperty)
    [P.toProperty.RespectsIso] : P.diagonal.toProperty.RespectsIso := by
  delta AffineTargetMorphismProperty.diagonal
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H _ _
    rw [pullback.mapDesc_comp, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
    apply H
  · introv H _ _
    rw [pullback.mapDesc_comp, P.cancel_right_of_respectsIso]
    apply H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasAffineProperty.diagonal_of_openCover** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   [inst :
 ∀ (i : 𝒰.I₀), AlgebraicGeometry.IsAffine (𝒰.X i)]   (𝒰' : (i : 𝒰.I₀) → (Categor
yTheory.Limits.pullback f (𝒰.f i)).OpenCover)   [inst_1 : ∀ (i : 𝒰.I₀) (j : (𝒰' 
i).I₀), AlgebraicGeometry.IsAffine ((𝒰' i).X j)],   (∀ (i : 𝒰.I₀) (j k : (𝒰' i).
I₀),       Q         (CategoryTheory.Limits.pullback.mapDesc ((𝒰' i).f j) ((𝒰' i
).f k)           (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i))) →     P.di
agonal f
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；f : X ⟶ Y；𝒰 : Y.
OpenCover；i : 𝒰.I₀；𝒰.X i；𝒰' : (i : 𝒰.I₀) → (CategoryTheory.Limits.pullback f (𝒰.
f i)).OpenCover；i : 𝒰.I₀；j : (𝒰' i).I₀；(𝒰' i).X j；∀ (i : 𝒰.I₀) (j k : (𝒰' i).I₀)
,       Q         (CategoryTheory.Limits.pullback.mapDesc ((𝒰' i).f j) ((𝒰' i).f
 k)           (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_openCover`：∀ {P : CategoryTheory.
MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTargetMo
rphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 32 条，此处仅展示前 30 条）
-/
theorem HasAffineProperty.diagonal_of_openCover (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} Y) [∀ i, IsAffine (𝒰.X i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{w} (pullback f (𝒰.f i))) [∀ i j, IsAffine ((𝒰' i).X j)]
    (h𝒰' : ∀ i j k,
      Q (pullback.mapDesc ((𝒰' i).f j) ((𝒰' i).f k) (𝒰.pullbackHom f i))) :
    P.diagonal f := by
  let := isLocal_affineProperty P
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) (pullback.snd _ _) (pullback.snd _ _)
  have i1 : ∀ i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  apply of_openCover 𝒱
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert!
    (Q.cancel_left_of_respectsIso
          ((pullbackDiagonalMapIso _ _ ((𝒰' i).f j) ((𝒰' i).f k)).inv ≫
            pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _)
          (pullback.snd _ _)).mp
      _
      using 1
  · simp
  · ext1 <;> simp
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      Category.comp_id]
    convert! h𝒰' i j k
    ext1 <;> simp [Scheme.Cover.pullbackHom]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.HasAffineProperty.diagonal_of_openCover_diagonal** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   [inst :
 ∀ (i : 𝒰.I₀), AlgebraicGeometry.IsAffine (𝒰.X i)],   (∀ (i : 𝒰.toPreZeroHyperco
ver.1), Q.diagonal (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i)) → P.diago
nal f
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；f : X ⟶ Y；𝒰 : Y.
OpenCover；i : 𝒰.I₀；𝒰.X i；∀ (i : 𝒰.toPreZeroHypercover.1), Q.diagonal (AlgebraicG
eometry.Scheme.Cover.pullbackHom 𝒰 f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.HasAffineProperty.diagonal_of_openCover`：∀ (P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affin
eTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
-/
theorem HasAffineProperty.diagonal_of_openCover_diagonal
    (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover Y) [∀ i, IsAffine (𝒰.X i)]
    (h𝒰 : ∀ i, Q.diagonal (𝒰.pullbackHom f i)) :
    P.diagonal f :=
  diagonal_of_openCover P f 𝒰 (fun _ ↦ Scheme.affineCover _)
    (fun _ _ _ ↦ h𝒰 _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasAffineProperty.diagonal_of_diagonal_of_isPullback** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y U V : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : U ⟶ Y}   [inst : A
lgebraicGeometry.IsAffine U] [AlgebraicGeometry.IsOpenImmersion g] {iV : V ⟶ X} 
{f' : V ⟶ U},   CategoryTheory.IsPullback iV f' f g → P.diagonal f → Q.diagonal 
f'
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso`：∀ (
P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.RespectsIso], 
P.diagonal.toProperty.RespectsIso
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_snd`：isoPullback_inv_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ snd = pullback.s
nd _ _
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIso.hom_fst`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : CategoryTheory.
Limits.HasPullbacks C]   {U V₁ V₂ : C} (f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIso.hom_snd`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : CategoryTheory.
Limits.HasPullbacks C]   {U V₁ V₂ : C} (f …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_isPullback`：∀ {P : CategoryTheory
.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTargetM
orphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion`：∀ {X Y S X' Y' S'
 : AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S
') (i₁ : X ⟶ X')   (i₂ : Y ⟶ Y') (i₃ : S ⟶ …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
（共 31 条，此处仅展示前 30 条）
-/
theorem HasAffineProperty.diagonal_of_diagonal_of_isPullback
    (P) {Q} [HasAffineProperty P Q]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y}
    [IsAffine U] [IsOpenImmersion g]
    {iV : V ⟶ X} {f' : V ⟶ U} (h : IsPullback iV f' f g) (H : P.diagonal f) :
    Q.diagonal f' := by
  let := isLocal_affineProperty P
  rw [← Q.diagonal.cancel_left_of_respectsIso h.isoPullback.inv,
    h.isoPullback_inv_snd]
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  rw [← Q.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert! HasAffineProperty.of_isPullback (P := P) (.of_hasPullback _ _) H
  · apply pullback.hom_ext <;> simp
  · infer_instance
  · infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.HasAffineProperty.diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.HasAffineProperty`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y}   [inst : AlgebraicGeometry
.IsAffine Y], Q.diagonal f ↔ P.diagonal f
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.diagonal_of_openCover`：∀ (P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affin
eTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instIsAffineXSchemeCoverOfIsIsoIsOpenImmersionId`：∀ {X
 : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X]   (i : (AlgebraicGeo
metry.Scheme.coverOfIsIso (CategoryTheory.CategoryStruct…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso`：∀ (
P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.RespectsIso], 
P.diagonal.toProperty.RespectsIso
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.diagonal_of_diagonal_of_isPullback`：
∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicG
eometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用引理 `CategoryTheory.IsPullback.of_id_fst`：of_id_fst : IsPullback (𝟙 _) f f (𝟙
 _)
-/
theorem HasAffineProperty.diagonal_iff
    (P) {Q} [HasAffineProperty P Q] {X Y : Scheme.{u}} {f : X ⟶ Y} [IsAffine Y] :
    Q.diagonal f ↔ P.diagonal f := by
  let := isLocal_affineProperty P
  refine ⟨fun hf ↦ ?_, diagonal_of_diagonal_of_isPullback P .of_id_fst⟩
  rw [← Q.diagonal.cancel_left_of_respectsIso
    (pullback.fst (f := f) (g := 𝟙 Y)), pullback.condition, Category.comp_id] at hf
  let 𝒰 := X.affineCover.pushforwardIso (inv (pullback.fst (f := f) (g := 𝟙 Y)))
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  exact HasAffineProperty.diagonal_of_openCover.{u, u, u} P f (Scheme.coverOfIsIso (𝟙 _))
    (fun _ ↦ 𝒰) (fun _ _ _ ↦ hf _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_of_openCover_source** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：∀ {Q : AlgebraicGeometry.AffineTargetMorphismProperty} [Q.IsLocal] {X Y : 
AlgebraicGeometry.Scheme} (f : X ⟶ Y)   (𝒰 : X.OpenCover) [inst : ∀ (i : 𝒰.I₀), 
AlgebraicGeometry.IsAffine (𝒰.X i)] [inst_1 : AlgebraicGeometry.IsAffine Y],   (
∀ (i j : 𝒰.I₀), Q (CategoryTheory.Limits.pullback.mapDesc (𝒰.f i) (𝒰.f j) f)) → 
Q.diagonal f
参数：f : X ⟶ Y；𝒰 : X.OpenCover；i : 𝒰.I₀；𝒰.X i；∀ (i j : 𝒰.I₀), Q (CategoryTheory.Li
mits.pullback.mapDesc (𝒰.f i) (𝒰.f j) f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.diagonal_iff`：∀ (P : CategoryTheory.
MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.AffineTargetMo
rphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instTargetAffineLocallyOfIsLocal`：∀ 
(Q : AlgebraicGeometry.AffineTargetMorphismProperty) [Q.IsLocal],   AlgebraicGeo
metry.HasAffineProperty (AlgebraicGeometry.targetAffineLoc…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_openCover`：∀ {P : CategoryTheory.
MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTargetMo
rphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pullback_fst_map_snd_isPullback`：pullback_fst_map_
snd_isPullback : IsPullback (fst _ _ ≫ i₁ ≫ fst _ _) (map i₁ i₂ (i₁ ≫ snd _ _) (
i₂ ≫ snd _ _) _ _ _ (Category.id_comp _).sy…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.map.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [i
nst_1 : CategoryTheory.Limits.HasPu…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
-/
theorem AffineTargetMorphismProperty.diagonal_of_openCover_source
    {Q : AffineTargetMorphismProperty} [Q.IsLocal]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} X) [∀ i, IsAffine (𝒰.X i)]
    [IsAffine Y] (h𝒰 : ∀ i j, Q (pullback.mapDesc (𝒰.f i) (𝒰.f j) f)) :
    Q.diagonal f := by
  rw [HasAffineProperty.diagonal_iff (targetAffineLocally Q)]
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight.{u} 𝒰 𝒰 f f
  have i1 : ∀ i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  refine HasAffineProperty.of_openCover (P := targetAffineLocally Q) 𝒱 fun i ↦ ?_
  dsimp [𝒱, Scheme.Cover.pullbackHom]
  have : IsPullback (pullback.fst _ _ ≫ 𝒰.f _) (pullback.mapDesc (𝒰.f i.1) (𝒰.f i.2) f)
      (pullback.diagonal f) (pullback.map _ _ _ _ (𝒰.f _) (𝒰.f _) (𝟙 Y) (by simp) (by simp)) :=
    .of_iso (pullback_fst_map_snd_isPullback f (𝟙 _) (𝒰.f i.1 ≫ pullback.lift (𝟙 _) f)
      (𝒰.f i.2 ≫ pullback.lift (𝟙 _) f)) (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      (pullback.fst _ _) (by simp) (by simp))) (.refl _) (pullback.congrHom (by simp) (by simp))
      (.refl _) (by simp) (by cat_disch) (by simp) (by cat_disch)
  rw [← Q.cancel_left_of_respectsIso this.isoPullback.hom, IsPullback.isoPullback_hom_snd]
  exact h𝒰 _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.HasAffineProperty.diagonal_affineProperty_isLocal** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {Q : AlgebraicGeometry.AffineTargetMorphismProperty} [Q.IsLocal], Q.diag
onal.IsLocal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso`：∀ (
P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.RespectsIso], 
P.diagonal.toProperty.RespectsIso
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `AlgebraicGeometry.HasAffineProperty.diagonal_of_diagonal_of_isPullback`：
∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicG
eometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instTargetAffineLocallyOfIsLocal`：∀ 
(Q : AlgebraicGeometry.AffineTargetMorphismProperty) [Q.IsLocal],   AlgebraicGeo
metry.HasAffineProperty (AlgebraicGeometry.targetAffineLoc…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen`：∀ {X : Alg
ebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X] (r : ↑(X.presheaf.obj (Opp
osite.op ⊤))),   AlgebraicGeometry.IsAffine ↑(X.ba…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.HasAffineProperty.diagonal_iff`：∀ (P : CategoryTheory.
MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.AffineTargetMo
rphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.iSup_basicOpen_eq_self_iff`：iSup_basicOpe
n_eq_self_iff {s : Set Γ(X, U)} : ⨆ f : s, X.basicOpen (f : Γ(X, U)) = U ↔ Ideal
.span s = ⊤
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.diagonal_of_openCover_diagonal`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeome
try.AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.arrow_mk_iso_iff`：arrow_m
k_iso_iff (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] {X Y X' 
Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : Arrow.mk…
-/
instance HasAffineProperty.diagonal_affineProperty_isLocal
    {Q : AffineTargetMorphismProperty} [Q.IsLocal] :
    Q.diagonal.IsLocal where
  respectsIso := inferInstance
  to_basicOpen {_ Y} _ f r hf :=
    diagonal_of_diagonal_of_isPullback (targetAffineLocally Q)
      (isPullback_morphismRestrict f (Y.basicOpen r)).flip
      ((diagonal_iff (targetAffineLocally Q)).mp hf)
  of_basicOpenCover {X Y} _ f s hs hs' := by
    refine (diagonal_iff (targetAffineLocally Q)).mpr ?_
    let 𝒰 := Y.openCoverOfIsOpenCover _
      ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)
    have (i : _) : IsAffine (𝒰.X i) := (isAffineOpen_top Y).basicOpen i.1
    refine diagonal_of_openCover_diagonal (targetAffineLocally Q) f 𝒰 ?_
    intro i
    exact (Q.diagonal.arrow_mk_iso_iff
      (morphismRestrictEq _ (by simp [𝒰]) ≪≫ morphismRestrictOpensRange _ _)).mp (hs' i)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P) {Q} [HasAffineProperty P Q] : HasAffineProperty P.diagonal Q.diagonal where
  isLocal_affineProperty := letI := HasAffineProperty.isLocal_affineProperty P; inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    let := HasAffineProperty.isLocal_affineProperty P
    constructor
    · exact fun H U ↦ HasAffineProperty.diagonal_of_diagonal_of_isPullback P
        (isPullback_morphismRestrict f U).flip H
    · exact fun H ↦ HasAffineProperty.diagonal_of_openCover_diagonal P f Y.affineCover
        (fun i ↦ of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) H)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P) [IsZariskiLocalAtTarget P] : IsZariskiLocalAtTarget P.diagonal :=
  letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  inferInstance

open MorphismProperty in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty Scheme)
    [P.HasOfPostcompProperty @IsOpenImmersion] [P.RespectsRight @IsOpenImmersion]
    [IsZariskiLocalAtSource P] : IsZariskiLocalAtSource P.diagonal := by
  let g {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens) :=
    pullback.map (U.ι ≫ f) (U.ι ≫ f) f f U.ι U.ι (𝟙 Y) (by simp) (by simp)
  refine IsZariskiLocalAtSource.mk' (fun {X Y} f U hf ↦ ?_) (fun {X Y} f {ι} U hU hf ↦ ?_)
  · change P _
    apply P.of_postcomp (W' := @IsOpenImmersion) (pullback.diagonal (U.ι ≫ f)) (g f U) inferInstance
    rw [← pullback.comp_diagonal]
    apply IsZariskiLocalAtSource.comp
    exact hf
  · change P _
    refine IsZariskiLocalAtSource.of_iSup_eq_top U hU fun i ↦ ?_
    rw [pullback.comp_diagonal]
    exact RespectsRight.postcomp (P := P) (Q := @IsOpenImmersion) (g _ _) inferInstance _ (hf i)

end Diagonal

section Universally

/-
**AlgebraicGeometry.universally_isZariskiLocalAtTarget** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：universally_isZariskiLocalAtTarget (P : MorphismProperty Scheme) (hP₂ : fo
rall {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι -> Y.Opens) (_ : IsOpenC
over U), (forall i, P (f ∣_ U i)) -> P f) : IsZariskiLocalAtTarget P.universally
参数：P : MorphismProperty Scheme；hP₂ : forall {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : 
Type u} (U : ι -> Y.Opens) (_ : IsOpenCover U), (forall i, P (f ∣_ U i)) -> P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.mk'`：∀ {P : CategoryTheory.Morp
hismProperty AlgebraicGeometry.Scheme} [P.RespectsIso],   (∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) (U : Y.O…
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.paste_vert_iff`：paste_vert_iff {X₁₁ X₁₂ X₂₁ X₂
₂ X₃₁ X₃₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ 
⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ …
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι_assoc`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (U : Y.Opens) {Z : AlgebraicGeometry.Scheme} (h : Y ⟶ Z),   C
ategoryTheory.CategoryStruct.com…
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι_assoc`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U = V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),  
 CategoryTheory.CategoryStruct.com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
-/
theorem universally_isZariskiLocalAtTarget (P : MorphismProperty Scheme)
    (hP₂ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
      (_ : IsOpenCover U), (∀ i, P (f ∣_ U i)) → P f) : IsZariskiLocalAtTarget P.universally := by
  apply IsZariskiLocalAtTarget.mk'
  · exact fun {X Y} f U => P.universally.of_isPullback
      (isPullback_morphismRestrict f U).flip
  · intro X Y f ι U hU H X' Y' i₁ i₂ f' h
    apply hP₂ _ (fun i ↦ i₂ ⁻¹ᵁ U i)
    · simp only [IsOpenCover, ← top_le_iff] at hU ⊢
      rintro x -
      simpa using @hU (i₂ x) trivial
    · rintro i
      refine H _ ((X'.isoOfEq ?_).hom ≫ i₁ ∣_ _) (i₂ ∣_ _) _ ?_
      · exact congr($(h.1.1) ⁻¹ᵁ U i)
      · rw [← (isPullback_morphismRestrict f _).paste_vert_iff]
        · simp only [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
          exact (isPullback_morphismRestrict f' (i₂ ⁻¹ᵁ U i)).paste_vert h
        · rw [← cancel_mono (Scheme.Opens.ι _)]
          simp [morphismRestrict_ι_assoc, h.1.1]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.universally_isZariskiLocalAtSource** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：universally_isZariskiLocalAtSource (P : MorphismProperty Scheme) [IsZarisk
iLocalAtSource P] : IsZariskiLocalAtSource P.universally
参数：P : MorphismProperty Scheme。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHyperco
ver`：mk_of_iff_of_zeroHypercover [P.RespectsIso] (H : forall {X Y : C} (f : X ⟶ 
Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X), P f ↔ forall i…
· 使用引理 `CategoryTheory.MorphismProperty.universally_mk'`：universally_mk' (P : Mo
rphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y) (H : forall {T : C} (f :
 T ⟶ Y) [HasPullback f g], P (pullbac…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_hom_fst`：pullbackLeftPu
llbackSndIso_hom_fst : (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.fst _ 
_ = pullback.fst _ _ ≫ pullback.fst _ _
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
-/
lemma universally_isZariskiLocalAtSource (P : MorphismProperty Scheme)
    [IsZariskiLocalAtSource P] : IsZariskiLocalAtSource P.universally := by
  refine .mk_of_iff_of_zeroHypercover ?_
  intro X Y f 𝒰
  refine ⟨fun hf i ↦ ?_, fun hf ↦ ?_⟩
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [← P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso g f _).hom,
      pullbackLeftPullbackSndIso_hom_fst]
    exact IsZariskiLocalAtSource.comp (hf _ _ _ (IsPullback.of_hasPullback ..)) _
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (𝒰.pullback₁ <| pullback.snd g f)]
    intro i
    dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f]
    rw [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso]
    exact hf i _ _ _ (IsPullback.of_hasPullback ..)

end Universally

section Topologically

/-- `topologically P` holds for a morphism if the underlying topological map satisfies `P`. -/
/-
**AlgebraicGeometry.topologically** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：topologically (P : forall {α β : Type u} [TopologicalSpace α] [Topological
Space β] (_ : α -> β), Prop) : MorphismProperty Scheme.{u}
参数：P : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α ->
 β), Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`topologically P` holds for a morphism if the underlying topological map satisfi
es `P`.
-/
def topologically
    (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop) :
    MorphismProperty Scheme.{u} := fun _ _ f => P f

variable (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop)

/-- If a property of maps of topological spaces is stable under composition, the induced
morphism property of schemes is stable under composition. -/
/-
**AlgebraicGeometry.topologically_isStableUnderComposition** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：topologically_isStableUnderComposition (hP : forall {α β γ : Type u} [Topo
logicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] (f : α -> β) (g : β ->
 γ) (_ : P f) (_ : P g), P (g ∘ f)) : (topologically P).IsStableUnderComposition
 where comp_mem {X Y Z} f g hf hg
参数：hP : forall {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [Topol
ogicalSpace γ] (f : α -> β) (g : β -> γ) (_ : P f) (_ : P g), P (g ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a property of maps of topological spaces is stable under composition, the ind
uced
morphism property of schemes is stable under composition.
-/
lemma topologically_isStableUnderComposition
    (hP : ∀ {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α → β) (g : β → γ) (_ : P f) (_ : P g), P (g ∘ f)) :
    (topologically P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    simp only [topologically, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hP _ _ hf hg

/-- If a property of maps of topological spaces is satisfied by all homeomorphisms,
every isomorphism of schemes satisfies the induced property. -/
/-
**AlgebraicGeometry.topologically_iso_le** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：topologically_iso_le (hP : forall {α β : Type u} [TopologicalSpace α] [Top
ologicalSpace β] (f : α ≃ₜ β), P f) : MorphismProperty.isomorphisms Scheme <= (t
opologically P)
参数：hP : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃
ₜ β), P f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a property of maps of topological spaces is satisfied by all homeomorphisms,
every isomorphism of schemes satisfies the induced property.
-/
lemma topologically_iso_le
    (hP : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f) :
    MorphismProperty.isomorphisms Scheme ≤ (topologically P) := by
  intro X Y e (he : IsIso e)
  exact hP (TopCat.homeoOfIso (asIso e.base))

/-- If a property of maps of topological spaces is satisfied by homeomorphisms and is stable
under composition, the induced property on schemes respects isomorphisms. -/
/-
**AlgebraicGeometry.topologically_respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：topologically_respectsIso (hP₁ : forall {α β : Type u} [TopologicalSpace α
] [TopologicalSpace β] (f : α ≃ₜ β), P f) (hP₂ : forall {α β γ : Type u} [Topolo
gicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] (f : α -> β) (g : β -> γ
) (_ : P f) (_ : P g), P (g ∘ f)) : (topologically P).RespectsIso
参数：hP₁ : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α 
≃ₜ β), P f；hP₂ : forall {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace 
β] [TopologicalSpace γ] (f : α -> β) (g : β -> γ) (_ : P f) (_ : P g), P (g ∘ f)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isStableUnderComposition`：topologically_
isStableUnderComposition (hP : forall {α β γ : Type u} [TopologicalSpace α] [Top
ologicalSpace β] [TopologicalSpace γ] (f : α -…
· 使用定理 `CategoryTheory.MorphismProperty.respectsIso_of_isStableUnderComposition`
：respectsIso_of_isStableUnderComposition {P : MorphismProperty C} [P.IsStableUnd
erComposition] (hP : isomorphisms C <= P) : RespectsIso P
· 使用引理 `AlgebraicGeometry.topologically_iso_le`：topologically_iso_le (hP : foral
l {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f) : 
MorphismProperty.isomorphism…

--- 原说明 ---
If a property of maps of topological spaces is satisfied by homeomorphisms and i
s stable
under composition, the induced property on schemes respects isomorphisms.
-/
lemma topologically_respectsIso
    (hP₁ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f)
    (hP₂ : ∀ {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α → β) (g : β → γ) (_ : P f) (_ : P g), P (g ∘ f)) :
      (topologically P).RespectsIso :=
  have : (topologically P).IsStableUnderComposition :=
    topologically_isStableUnderComposition P hP₂
  MorphismProperty.respectsIso_of_isStableUnderComposition (topologically_iso_le P hP₁)

/-- To check that a topologically defined morphism property is local at the target,
we may check the corresponding properties on topological spaces. -/
/-
**AlgebraicGeometry.topologically_isZariskiLocalAtTarget** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：topologically_isZariskiLocalAtTarget [(topologically P).RespectsIso] (hP₂ 
: forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α -> β) (
s : Set β) (_ : Continuous f) (_ : IsOpen s), P f -> P (s.restrictPreimage f)) (
hP₃ : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α -> 
β) {ι : Type u} (U : ι -> Opens β) (_ : IsOpenCover U) (_ : Continuous f), (fora
ll i, P ((U i).carrier.restrictPreimage f)) -> P f) : IsZariskiLocalAtTarget (to
pologically P)
参数：topologically P；hP₂ : forall {α β : Type u} [TopologicalSpace α] [Topological
Space β] (f : α -> β) (s : Set β) (_ : Continuous f) (_ : IsOpen s), P f -> P (s
.restrictPreimage f)；hP₃ : forall {α β : Type u} [TopologicalSpace α] [Topologic
alSpace β] (f : α -> β) {ι : Type u} (U : ι -> Opens β) (_ : IsOpenCover U) (_ :
 Continuous f), (forall i, P ((U i).carrier.restrictPreimage f)) -> P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.mk'`：∀ {P : CategoryTheory.Morp
hismProperty AlgebraicGeometry.Scheme} [P.RespectsIso],   (∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) (U : Y.O…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.morphismRestrict_base`：morphismRestrict_base {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) : ⇑(f ∣_ U) = U.1.restrictPreimage f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
To check that a topologically defined morphism property is local at the target,
we may check the corresponding properties on topological spaces.
-/
lemma topologically_isZariskiLocalAtTarget [(topologically P).RespectsIso]
    (hP₂ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) (s : Set β)
      (_ : Continuous f) (_ : IsOpen s), P f → P (s.restrictPreimage f))
    (hP₃ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) {ι : Type u}
      (U : ι → Opens β) (_ : IsOpenCover U) (_ : Continuous f),
      (∀ i, P ((U i).carrier.restrictPreimage f)) → P f) :
    IsZariskiLocalAtTarget (topologically P) := by
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    simp_rw [topologically, morphismRestrict_base]
    exact hP₂ f U.carrier f.continuous U.2 hf
  · intro X Y f ι U hU hf
    apply hP₃ f U hU f.continuous fun i ↦ ?_
    rw [← morphismRestrict_base]
    exact hf i

/-- A variant of `topologically_isZariskiLocalAtTarget`
that takes one iff statement instead of two implications. -/
/-
**AlgebraicGeometry.topologically_isZariskiLocalAtTarget'** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：topologically_isZariskiLocalAtTarget' [(topologically P).RespectsIso] (hP 
: forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α -> β) {
ι : Type u} (U : ι -> Opens β) (_ : IsOpenCover U) (_ : Continuous f), P f ↔ (fo
rall i, P ((U i).carrier.restrictPreimage f))) : IsZariskiLocalAtTarget (topolog
ically P)
参数：topologically P；hP : forall {α β : Type u} [TopologicalSpace α] [TopologicalS
pace β] (f : α -> β) {ι : Type u} (U : ι -> Opens β) (_ : IsOpenCover U) (_ : Co
ntinuous f), P f ↔ (forall i, P ((U i).carrier.restrictPreimage f))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtTarget`：topologically_is
ZariskiLocalAtTarget [(topologically P).RespectsIso] (hP₂ : forall {α β : Type u
} [TopologicalSpace α] [TopologicalSpace β] …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.eq_1`：∀ {ι : Type u_1} {X : Type u_2} [inst
 : TopologicalSpace X] (u : ι → TopologicalSpace.Opens X),   TopologicalSpace.Is
OpenCover u = (iSup u =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A variant of `topologically_isZariskiLocalAtTarget`
that takes one iff statement instead of two implications.
-/
lemma topologically_isZariskiLocalAtTarget' [(topologically P).RespectsIso]
    (hP : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) {ι : Type u}
      (U : ι → Opens β) (_ : IsOpenCover U) (_ : Continuous f),
      P f ↔ (∀ i, P ((U i).carrier.restrictPreimage f))) :
    IsZariskiLocalAtTarget (topologically P) := by
  refine topologically_isZariskiLocalAtTarget P ?_ (fun f _ U hU hU' ↦ (hP f U hU hU').mpr)
  introv hf hs H
  refine (hP f (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ?_ hf).mp H ⟨1⟩
  rw [IsOpenCover, ← top_le_iff]
  exact le_iSup (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ⟨0⟩
/-
**AlgebraicGeometry.topologically_isZariskiLocalAtSource** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：topologically_isZariskiLocalAtSource [(topologically P).RespectsIso] (hP₁ 
: forall {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y) (
_ : Continuous f) (U : Opens X), P f -> P (f ∘ ((↑) : U -> X))) (hP₂ : forall {X
 Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y) (_ : Continu
ous f) {ι : Type u} (U : ι -> Opens X), IsOpenCover U -> (forall i, P (f ∘ ((↑) 
: U i -> X))) -> P f) : IsZariskiLocalAtSource (topologically P)
参数：topologically P；hP₁ : forall {X Y : Type u} [TopologicalSpace X] [Topological
Space Y] (f : X -> Y) (_ : Continuous f) (U : Opens X), P f -> P (f ∘ ((↑) : U -
> X))；hP₂ : forall {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f :
 X -> Y) (_ : Continuous f) {ι : Type u} (U : ι -> Opens X), IsOpenCover U -> (f
orall i, P (f ∘ ((↑) : U i -> X))) -> P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.mk'`：∀ {P : CategoryTheory.Morp
hismProperty AlgebraicGeometry.Scheme} [P.RespectsIso],   (∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) (U : X.O…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
-/
lemma topologically_isZariskiLocalAtSource [(topologically P).RespectsIso]
    (hP₁ : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
      (_ : Continuous f) (U : Opens X), P f → P (f ∘ ((↑) : U → X)))
    (hP₂ : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
      (_ : Continuous f) {ι : Type u} (U : ι → Opens X),
      IsOpenCover U → (∀ i, P (f ∘ ((↑) : U i → X))) → P f) :
    IsZariskiLocalAtSource (topologically P) := by
  apply IsZariskiLocalAtSource.mk'
  · introv hf
    exact hP₁ f f.continuous _ hf
  · introv hU hf
    exact hP₂ f f.continuous _ hU hf

/-- A variant of `topologically_isZariskiLocalAtSource`
that takes one iff statement instead of two implications. -/
/-
**AlgebraicGeometry.topologically_isZariskiLocalAtSource'** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：topologically_isZariskiLocalAtSource' [(topologically P).RespectsIso] (hP 
: forall {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y) {
ι : Type u} (U : ι -> Opens X) (_ : IsOpenCover U) (_ : Continuous f), P f ↔ (fo
rall i, P (f ∘ ((↑) : U i -> X)))) : IsZariskiLocalAtSource (topologically P)
参数：topologically P；hP : forall {X Y : Type u} [TopologicalSpace X] [TopologicalS
pace Y] (f : X -> Y) {ι : Type u} (U : ι -> Opens X) (_ : IsOpenCover U) (_ : Co
ntinuous f), P f ↔ (forall i, P (f ∘ ((↑) : U i -> X)))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.topologically_isZariskiLocalAtSource`：topologically_is
ZariskiLocalAtSource [(topologically P).RespectsIso] (hP₁ : forall {X Y : Type u
} [TopologicalSpace X] [TopologicalSpace Y] …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsOpenCover.eq_1`：∀ {ι : Type u_1} {X : Type u_2} [inst
 : TopologicalSpace X] (u : ι → TopologicalSpace.Opens X),   TopologicalSpace.Is
OpenCover u = (iSup u =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
A variant of `topologically_isZariskiLocalAtSource`
that takes one iff statement instead of two implications.
-/
lemma topologically_isZariskiLocalAtSource' [(topologically P).RespectsIso]
    (hP : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) {ι : Type u}
      (U : ι → Opens X) (_ : IsOpenCover U) (_ : Continuous f),
      P f ↔ (∀ i, P (f ∘ ((↑) : U i → X)))) :
    IsZariskiLocalAtSource (topologically P) := by
  refine topologically_isZariskiLocalAtSource P ?_ (fun f hf _ U hU hf' ↦ (hP f U hU hf).mpr hf')
  introv hf hs
  refine (hP f (![⊤, U] ∘ Equiv.ulift) ?_ hf).mp hs ⟨1⟩
  rw [IsOpenCover, ← top_le_iff]
  exact le_iSup (![⊤, U] ∘ Equiv.ulift) ⟨0⟩

end Topologically

/-- `stalkwise P` holds for a morphism if all stalks satisfy `P`. -/
/-
**AlgebraicGeometry.stalkwise** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：stalkwise (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S)
 -> Prop) : MorphismProperty Scheme.{u}
参数：P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`stalkwise P` holds for a morphism if all stalks satisfy `P`.
-/
def stalkwise (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) :
    MorphismProperty Scheme.{u} :=
  fun _ _ f => ∀ x, P (f.stalkMap x).hom

section Stalkwise

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- If `P` respects isos, then `stalkwise P` respects isos. -/
/-
**AlgebraicGeometry.stalkwise_respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：stalkwise_respectsIso (hP : RingHom.RespectsIso P) : (stalkwise P).Respect
sIso where precomp {X Y Z} e (he : IsIso e) f hf
参数：hP : RingHom.RespectsIso P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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

--- 原说明 ---
If `P` respects isos, then `stalkwise P` respects isos.
-/
lemma stalkwise_respectsIso (hP : RingHom.RespectsIso P) :
    (stalkwise P).RespectsIso where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.RespectsIso.cancel_right_isIso hP _ _).mpr <| hf (e x)
  postcomp {X Y Z} e (he : IsIso _) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.RespectsIso.cancel_left_isIso hP _ _).mpr <| hf x

/-- If `P` respects isos, then `stalkwise P` is local at the target. -/
/-
**AlgebraicGeometry.stalkwiseIsZariskiLocalAtTarget_of_respectsIso** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：stalkwiseIsZariskiLocalAtTarget_of_respectsIso (hP : RingHom.RespectsIso P
) : IsZariskiLocalAtTarget (stalkwise P)
参数：hP : RingHom.RespectsIso P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用引理 `AlgebraicGeometry.stalkwise_respectsIso`：stalkwise_respectsIso (hP : Rin
gHom.RespectsIso P) : (stalkwise P).RespectsIso where precomp {X Y Z} e (he : Is
Iso e) f hf
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.mk'`：∀ {P : CategoryTheory.Morp
hismProperty AlgebraicGeometry.Scheme} [P.RespectsIso],   (∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) (U : Y.O…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i

--- 原说明 ---
If `P` respects isos, then `stalkwise P` is local at the target.
-/
lemma stalkwiseIsZariskiLocalAtTarget_of_respectsIso (hP : RingHom.RespectsIso P) :
    IsZariskiLocalAtTarget (stalkwise P) := by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf x
    apply ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f U x).mpr <| hf _
  · intro X Y f ι U hU hf x
    have hy : f x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f (U i) ⟨x, hi⟩).mp <| hf i ⟨x, hi⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `P` respects isos, then `stalkwise P` is local at the source. -/
/-
**AlgebraicGeometry.stalkwise_isZariskiLocalAtSource_of_respectsIso** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：stalkwise_isZariskiLocalAtSource_of_respectsIso (hP : RingHom.RespectsIso 
P) : IsZariskiLocalAtSource (stalkwise P)
参数：hP : RingHom.RespectsIso P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.stalkwise_respectsIso`：stalkwise_respectsIso (hP : Rin
gHom.RespectsIso P) : (stalkwise P).RespectsIso where precomp {X Y Z} e (he : Is
Iso e) f hf
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.mk'`：∀ {P : CategoryTheory.Morp
hismProperty AlgebraicGeometry.Scheme} [P.RespectsIso],   (∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) (U : X.O…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `P` respects isos, then `stalkwise P` is local at the source.
-/
lemma stalkwise_isZariskiLocalAtSource_of_respectsIso (hP : RingHom.RespectsIso P) :
    IsZariskiLocalAtSource (stalkwise P) := by
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtSource.mk'
  · intro X Y f U hf x
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, hP.cancel_right_isIso]
    exact hf _
  · intro X Y f ι U hU hf x
    have hy : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    rw [← hP.cancel_right_isIso _ ((U i).ι.stalkMap ⟨x, hi⟩)]
    simpa [Scheme.Hom.stalkMap_comp] using hf i ⟨x, hi⟩
/-
**AlgebraicGeometry.stalkwise_SpecMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：stalkwise_SpecMap_iff (hP : RingHom.RespectsIso P) {R S : CommRingCat} (φ 
: R ⟶ S) : stalkwise P (Spec.map φ) ↔ forall (p : Ideal S) (_ : p.IsPrime), P (L
ocalization.localRingHom _ p φ.hom rfl)
参数：hP : RingHom.RespectsIso P；φ : R ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
-/
lemma stalkwise_SpecMap_iff (hP : RingHom.RespectsIso P) {R S : CommRingCat} (φ : R ⟶ S) :
    stalkwise P (Spec.map φ) ↔ ∀ (p : Ideal S) (_ : p.IsPrime),
      P (Localization.localRingHom _ p φ.hom rfl) := by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  trans ∀ (p : PrimeSpectrum S), P (Localization.localRingHom _ p.asIdeal φ.hom rfl)
  · exact forall_congr' fun p ↦
      (RingHom.toMorphismProperty P).arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso _ _)
  · exact ⟨fun H p hp ↦ H ⟨p, hp⟩, fun H p ↦ H p.1 p.2⟩

end Stalkwise

namespace AffineTargetMorphismProperty

/-- If `P` is local at the target, to show that `P` is stable under base change, it suffices to
check this for base change along a morphism of affine schemes. -/
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.isStableUnderBaseChange_of_isSt
ableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLoc
alAtTarget (P : MorphismProperty Scheme) [IsZariskiLocalAtTarget P] (hP₂ : (of P
).IsStableUnderBaseChange) : P.IsStableUnderBaseChange
参数：P : MorphismProperty Scheme；hP₂ : (of P).IsStableUnderBaseChange。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.Aff
ineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_isZariskiLocalAtTarget`：∀ (P : Ca
tegoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsZar
iskiLocalAtTarget P],   AlgebraicGeometry.HasAffine…

--- 原说明 ---
If `P` is local at the target, to show that `P` is stable under base change, it 
suffices to
check this for base change along a morphism of affine schemes.
-/
lemma isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget
    (P : MorphismProperty Scheme) [IsZariskiLocalAtTarget P]
    (hP₂ : (of P).IsStableUnderBaseChange) :
    P.IsStableUnderBaseChange :=
  letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  HasAffineProperty.isStableUnderBaseChange hP₂

end AffineTargetMorphismProperty

end AlgebraicGeometry

