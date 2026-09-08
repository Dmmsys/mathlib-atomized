/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.RingTheory.Finiteness.Prod

/-!

# Finite morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is finite if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is finite.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is finite.

Also see `AlgebraicGeometry.IsFinite.finite_preimage_singleton` in
`Mathlib/AlgebraicGeometry/Fiber.lean` for the fact that finite morphisms have finite fibers.

-/

public section

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsFinite** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：IsFinite {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where fin
ite_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.Finite  alias Sc
heme.Hom.finite_app
参数：f : X ⟶ Y。
继承自：IsAffineHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite.
-/
class IsFinite {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  finite_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.Finite

alias Scheme.Hom.finite_app := IsFinite.finite_app

namespace IsFinite

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasAffineProperty @IsFinite
    (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom) := by
  change HasAffineProperty @IsFinite (affineAnd RingHom.Finite)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  simp [isFinite_iff]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderComposition @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderComposition inferInstance
    RingHom.finite_stableUnderComposition

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange inferInstance
    RingHom.finite_respectsIso RingHom.finite_isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContainsIdentities @IsFinite :=
  HasAffineProperty.affineAnd_containsIdentities inferInstance
    RingHom.finite_respectsIso RingHom.finite_containsIdentities
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMultiplicative @IsFinite where

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.IsFinite.SpecMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.IsFinite`。
形式化陈述：SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) : IsFinite (Spec.map f) ↔ 
f.hom.Finite
参数：f : R ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrier
ObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop`：AlgebraicG
eometry.HasAffineProperty @AlgebraicGeometry.IsFinite fun X x f x_1 =>   Algebra
icGeometry.IsAffine X ∧ (CommRingCat.Hom.hom (Alge…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `RingHom.RespectsIso.arrow_mk_iso_iff`：∀ {P : {R S : Type u} → [inst : Co
mmRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.RespectsIso fu
n {R S} [CommRing R] [Comm…
· 使用定理 `RingHom.finite_respectsIso`：finite_respectsIso : RespectsIso @Finite
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsFinite (Spec.map f) ↔ f.hom.Finite := by
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite), and_iff_right (by infer_instance),
    RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsIso f] : IsFinite f := of_isIso @IsFinite f

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Z : Scheme.{u}} (g : Y ⟶ Z) [IsFinite f] [IsFinite g] : IsFinite (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g ‹IsFinite f› ‹IsFinite g›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite g] : IsFinite (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite f] : IsFinite (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [IsFinite f] : IsFinite (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsFinite`。
形式化陈述：iff_isIntegralHom_and_locallyOfFiniteType : IsFinite f ↔ IsIntegralHom f ∧
 LocallyOfFiniteType f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrier
ObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop`：AlgebraicG
eometry.HasAffineProperty @AlgebraicGeometry.IsFinite fun X x f x_1 =>   Algebra
icGeometry.IsAffine X ∧ (CommRingCat.Hom.hom (Alge…
· 使用定理 `RingHom.finite_iff_isIntegral_and_finiteType`：RingHom.finite_iff_isInteg
ral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f.FiniteType
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOfFiniteType fun {
R S} [CommRing R] [CommRing S] =>   RingHom.FiniteType
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
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iff_isIntegralHom_and_locallyOfFiniteType :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f := by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    simp_rw [this, forall_and]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite),
    HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom),
    RingHom.finite_iff_isIntegral_and_finiteType, ← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ ↦
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).symm
/-
**AlgebraicGeometry.IsFinite.eq_inf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
.IsFinite`。
形式化陈述：eq_inf : @IsFinite = (@IsIntegralHom ⊓ @LocallyOfFiniteType : MorphismProp
erty Scheme)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`：if
f_isIntegralHom_and_locallyOfFiniteType : IsFinite f ↔ IsIntegralHom f ∧ Locally
OfFiniteType f
-/
lemma eq_inf :
    @IsFinite = (@IsIntegralHom ⊓ @LocallyOfFiniteType : MorphismProperty Scheme) := by
  ext; exact IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsFinite f] : IsIntegralHom f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).1
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsFinite f] : LocallyOfFiniteType f :=
  ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp ‹_›).2

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsFinite._root_.AlgebraicGeometry.IsClosedImmersion.iff_isFi
nite_and_mono** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono :
    IsClosedImmersion f ↔ IsFinite f ∧ Mono f := by
  wlog hY : IsAffine Y
  · rw [← monomorphisms.iff, IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := monomorphisms _) Y.affineCover]
    simp_rw [this, forall_and]
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion),
    HasAffineProperty.iff_of_isAffine (P := @IsFinite),
    RingHom.surjective_iff_epi_and_finite, @and_comm (Epi _), ← and_assoc]
  refine and_congr_right fun ⟨_, _⟩ ↦
    Iff.trans ?_ (arrow_mk_iso_iff (monomorphisms _) (arrowIsoSpecΓOfIsAffine f).symm)
  trans Mono (f.app ⊤).op
  · exact ⟨fun h ↦ inferInstance, fun h ↦ show Epi (f.app ⊤).op.unop by infer_instance⟩
  exact (Functor.mono_map_iff_mono Scheme.Spec _).symm
/-
**AlgebraicGeometry.IsFinite._root_.AlgebraicGeometry.IsClosedImmersion.eq_isFin
ite_inf_mono** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.IsClosedImmersion.eq_isFinite_inf_mono :
    @IsClosedImmersion = (@IsFinite ⊓ monomorphisms Scheme : MorphismProperty _) := by
  ext; exact IsClosedImmersion.iff_isFinite_and_mono _
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) (f : X ⟶ Y) [IsClosedImmersion f] : IsFinite f :=
  ((IsClosedImmersion.iff_isFinite_and_mono f).mp ‹_›).1
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsFinite @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsFinite _)
/-
**AlgebraicGeometry.IsFinite.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y.IsFinite`。
形式化陈述：of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite (f ≫ g)] [IsSeparated g] : IsFin
ite f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.IsFinite.instHasOfPostcompPropertySchemeIsSeparated`：C
ategoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.IsFinite
 @AlgebraicGeometry.IsSeparated
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite (f ≫ g)] [IsSeparated g] :
    IsFinite f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›
/-
**AlgebraicGeometry.IsFinite.comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.IsFinite`。
形式化陈述：comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsFinite g] : IsFinite (f ≫ g) ↔ IsFinit
e f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsFinite.of_comp`：of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsF
inite (f ≫ g)] [IsSeparated g] : IsFinite f
· 使用引理 `AlgebraicGeometry.IsSeparated.of_isAffineHom`：of_isAffineHom [h : IsAffi
neHom f] : IsSeparated f
· 使用定理 `AlgebraicGeometry.IsFinite.toIsAffineHom`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsFinite f], AlgebraicGeometry.IsAffi
neHom f
· 使用定理 `AlgebraicGeometry.IsFinite.instCompScheme`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) {Z : AlgebraicGeometry.Scheme} (g : Y ⟶ Z) [AlgebraicGeometry.
IsFinite f]   [AlgebraicGeometr…
-/
lemma comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsFinite g] :
    IsFinite (f ≫ g) ↔ IsFinite f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsFin
ite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsFinite f] [IsFinite g] :
    IsFinite (Limits.coprod.desc f g) := by
  refine HasAffineProperty.coprodDesc_affineAnd inferInstance RingHom.finite_respectsIso
    ?_ _ _ ‹_› ‹_›
  intros R S T _ _ _ f g _ _
  algebraize [f, g]
  refine RingHom.finite_algebraMap.mpr inferInstance

end IsFinite

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.finite_appTop** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine
 Y] [AlgebraicGeometry.IsFinite f],   (CommRingCat.Hom.hom (AlgebraicGeometry.Sc
heme.Hom.appTop f)).Finite
参数：f : X ⟶ Y；CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appTop f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrier
ObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop`：AlgebraicG
eometry.HasAffineProperty @AlgebraicGeometry.IsFinite fun X x f x_1 =>   Algebra
icGeometry.IsAffine X ∧ (CommRingCat.Hom.hom (Alge…
-/
lemma Scheme.Hom.finite_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsFinite f] :
    f.appTop.hom.Finite :=
  (HasAffineProperty.iff_of_isAffine (P := @IsFinite).mp inferInstance).2

set_option backward.isDefEq.respectTransparency.types false in
/-- If `X` is a Jacobson scheme and `k` is a field,
`Spec(k) ⟶ X` is finite iff it is (locally) of finite type.
(The statement is more general to allow the empty scheme as well) -/
/-
**AlgebraicGeometry.isFinite_iff_locallyOfFiniteType_of_jacobsonSpace** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isFinite_iff_locallyOfFiniteType_of_jacobsonSpace {X Y : Scheme.{u}} {f : 
X ⟶ Y} [Subsingleton X] [IsReduced X] [JacobsonSpace Y] : IsFinite f ↔ LocallyOf
FiniteType f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `AlgebraicGeometry.IsFinite.instLocallyOfFiniteType`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.Loc
allyOfFiniteType f
· 使用定理 `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeo
metry.IsFinite f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instOfIsEmptyCarrierCarrierCommRingC
at`：∀ {X Y : AlgebraicGeometry.Scheme} [IsEmpty ↥X] (f : X ⟶ Y), AlgebraicGeomet
ry.IsClosedImmersion f
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.affine_isIntegral_iff`：affine_isIntegral_iff (R : Comm
RingCat) : IsIntegral (Spec R) ↔ IsDomain R
· 使用定理 `AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced`：isIntegra
l_of_irreducibleSpace_of_isReduced [IsReduced X] [H : IrreducibleSpace X] : IsIn
tegral X
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsFinite.SpecMap_iff`：SpecMap_iff {R S : CommRingCat.{
u}} (f : R ⟶ S) : IsFinite (Spec.map f) ↔ f.hom.Finite
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOfFiniteType fun {
R S} [CommRing R] [CommRing S] =>   RingHom.FiniteType
· 使用定理 `PrimeSpectrum.t1Space_iff_isField`：t1Space_iff_isField [IsDomain R] : T1
Space (PrimeSpectrum R) ↔ IsField R
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace`：isJacobsonRing_iff_jacob
sonSpace : IsJacobsonRing R ↔ JacobsonSpace (PrimeSpectrum R)
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用引理 `finite_of_finite_type_of_isJacobsonRing`：finite_of_finite_type_of_isJaco
bsonRing (R S : Type*) [CommRing R] [Field S] [Algebra R S] [IsJacobsonRing R] [
Algebra.FiniteType R S] : Mod…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.instIsAffineOfFiniteOfDiscreteTopologyCarrierCarrierCo
mmRingCat`：∀ {X : AlgebraicGeometry.Scheme} [Finite ↥X] [DiscreteTopology ↥X], A
lgebraicGeometry.IsAffine X
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrier
ObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop`：AlgebraicG
eometry.HasAffineProperty @AlgebraicGeometry.IsFinite fun X x f x_1 =>   Algebra
icGeometry.IsAffine X ∧ (CommRingCat.Hom.hom (Alge…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If `X` is a Jacobson scheme and `k` is a field,
`Spec(k) ⟶ X` is finite iff it is (locally) of finite type.
(The statement is more general to allow the empty scheme as well)
-/
lemma isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    {X Y : Scheme.{u}} {f : X ⟶ Y} [Subsingleton X] [IsReduced X] [JacobsonSpace Y] :
    IsFinite f ↔ LocallyOfFiniteType f := by
  wlog hY : ∃ S, Y = Spec S generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
    have inst (i) := ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding.injective.subsingleton
    have inst (i) := isReduced_of_isOpenImmersion ((Y.affineCover.pullback₁ f).f i)
    have inst (i) := JacobsonSpace.of_isOpenEmbedding (Y.affineCover.f i).isOpenEmbedding
    exact forall_congr' fun i ↦ this ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hY
  wlog hX : ∃ R, X = Spec R generalizing X
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) X.isoSpec.inv,
      ← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType) X.isoSpec.inv]
    have inst := X.isoSpec.inv.isOpenEmbedding.injective.subsingleton
    refine this ⟨_, rfl⟩
  cases isEmpty_or_nonempty X
  · exact ⟨inferInstance, inferInstance⟩
  have : IrreducibleSpace X := ⟨‹_›⟩
  obtain ⟨R, rfl⟩ := hX
  have : IsDomain R := (affine_isIntegral_iff R).mp (isIntegral_of_irreducibleSpace_of_isReduced _)
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [IsFinite.SpecMap_iff, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := (PrimeSpectrum.t1Space_iff_isField (R := R)).mp (show T1Space (Spec R) by infer_instance)
  let := this.toField
  let := φ.hom.toAlgebra
  have := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr ‹_›
  change Module.Finite _ _ ↔ Algebra.FiniteType _ _
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ finite_of_finite_type_of_isJacobsonRing _ _⟩

@[stacks 01TB "(1) => (3)"]
/-
**AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints** 是 Math
lib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [JacobsonSpace ↥Y] [Algebra
icGeometry.LocallyOfFiniteType f],   closedPoints ↥X ⊆ ⇑f ⁻¹' closedPoints ↥Y
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion`：∀ {X : Algeb
raicGeometry.Scheme} {x : ↥X}, IsClosed {x} ↔ AlgebraicGeometry.IsClosedImmersio
n (X.fromSpecResidueField x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.isFinite_iff_locallyOfFiniteType_of_jacobsonSpace`：isF
inite_iff_locallyOfFiniteType_of_jacobsonSpace {X Y : Scheme.{u}} {f : X ⟶ Y} [S
ubsingleton X] [IsReduced X] [JacobsonSpace Y] : IsFinite…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `AlgebraicGeometry.instIsReducedSpecOfIsReducedCarrier`：∀ {R : CommRingCa
t} [H : IsReduced ↑R], AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec R)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `AlgebraicGeometry.IsFinite.instLocallyOfFiniteType`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.Loc
allyOfFiniteType f
· 使用定理 `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeo
metry.IsFinite f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `AlgebraicGeometry.Scheme.range_fromSpecResidueField`：range_fromSpecResid
ueField (x : X.carrier) : Set.range (X.fromSpecResidueField x) = {x}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedMap`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], IsClosedMap ⇑f
· 使用定理 `AlgebraicGeometry.IsIntegralHom.instUniversallyClosed`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsIntegralHom f],   AlgebraicGe
ometry.UniversallyClosed f
· 使用定理 `AlgebraicGeometry.IsFinite.instIsIntegralHom`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.IsIntegra
lHom f
-/
lemma Scheme.Hom.closePoints_subset_preimage_closedPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [JacobsonSpace Y] [LocallyOfFiniteType f] :
    closedPoints X ⊆ f ⁻¹' closedPoints Y := by
  intro x hx
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  simpa [Set.range_comp, Scheme.range_fromSpecResidueField] using
    (X.fromSpecResidueField x ≫ f).isClosedMap.isClosed_range

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 01TB "(1) => (2)"]
/-
**AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isClosed_singleton_iff_locallyOfFiniteType {X : Scheme.{u}} [JacobsonSpace
 X] {x : X} : IsClosed {x} ↔ LocallyOfFiniteType (X.fromSpecResidueField x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion`：∀ {X : Algeb
raicGeometry.Scheme} {x : ↥X}, IsClosed {x} ↔ AlgebraicGeometry.IsClosedImmersio
n (X.fromSpecResidueField x)
· 使用定理 `AlgebraicGeometry.IsFinite.instLocallyOfFiniteType`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f], AlgebraicGeometry.Loc
allyOfFiniteType f
· 使用定理 `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeo
metry.IsFinite f
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints`：∀
 {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [JacobsonSpace ↥Y] [AlgebraicGeome
try.LocallyOfFiniteType f],   closedPoints ↥X ⊆ ⇑f ⁻¹' clos…
· 使用引理 `IsLocalRing.isClosed_singleton_closedPoint`：isClosed_singleton_closedPoi
nt : IsClosed {closedPoint R}
-/
lemma isClosed_singleton_iff_locallyOfFiniteType {X : Scheme.{u}} [JacobsonSpace X] {x : X} :
    IsClosed {x} ↔ LocallyOfFiniteType (X.fromSpecResidueField x) := by
  constructor
  · exact fun H ↦ have := isClosed_singleton_iff_isClosedImmersion.mp H; inferInstance
  · intro H
    simpa using (X.fromSpecResidueField x).closePoints_subset_preimage_closedPoints
      (IsLocalRing.isClosed_singleton_closedPoint _)

end AlgebraicGeometry

