/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.RingTheory.RingHom.Integral

/-!

# Integral morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is integral if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is integral.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is integral.

-/

public section

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is integral if the preimage of any affine open subset of `Y` is
affine and the induced ring hom on sections is integral. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsIntegralHom** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：IsIntegralHom {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f wher
e isIntegral_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsInteg
ral  alias Scheme.Hom.isIntegral_app
参数：f : X ⟶ Y。
继承自：IsAffineHom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `X ⟶ Y` is integral if the preimage of any affine open sub
set of `Y` is
affine and the induced ring hom on sections is integral.
-/
class IsIntegralHom {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  isIntegral_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral

alias Scheme.Hom.isIntegral_app := IsIntegralHom.isIntegral_app

namespace IsIntegralHom

variable {X Y Z S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.hasAffineProperty** 是 Mathlib 中的一个实例，位于命名空间 `A
lgebraicGeometry.IsIntegralHom`。
形式化陈述：hasAffineProperty : HasAffineProperty @IsIntegralHom fun X _ f _ => IsAffi
ne X ∧ RingHom.IsIntegral (f.app ⊤).hom
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.affineAnd_iff`：∀ {Q : {R S : Type u}
 → [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop}   (P : Catego
ryTheory.MorphismProperty AlgebraicGeom…
· 使用定理 `RingHom.isIntegral_respectsIso`：isIntegral_respectsIso : RespectsIso fun
 f => f.IsIntegral
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用定理 `RingHom.isIntegral_isStableUnderBaseChange`：isIntegral_isStableUnderBase
Change : IsStableUnderBaseChange fun f => f.IsIntegral
· 使用定理 `RingHom.isIntegral_ofLocalizationSpan`：isIntegral_ofLocalizationSpan : O
fLocalizationSpan (RingHom.IsIntegral ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance hasAffineProperty : HasAffineProperty @IsIntegralHom
    fun X _ f _ ↦ IsAffine X ∧ RingHom.IsIntegral (f.app ⊤).hom := by
  change HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.isIntegral_respectsIso
    RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves.away
    RingHom.isIntegral_ofLocalizationSpan]
  simp [isIntegralHom_iff]
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderComposition @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderComposition (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_stableUnderComposition
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderBaseChange @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_respectsIso RingHom.isIntegral_isStableUnderBaseChange
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) (f : X ⟶ Y) [IsClosedImmersion f] : IsIntegralHom f where
  isIntegral_app U hU := (RingHom.Finite.of_surjective _ (f.app_surjective U hU)).to_isIntegral
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMultiplicative @IsIntegralHom where
  id_mem _ := inferInstance
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g] : IsIntegralHom (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ ‹_› ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ S) (g : Y ⟶ S) [IsIntegralHom g] : IsIntegralHom (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ S) (g : Y ⟶ S) [IsIntegralHom f] : IsIntegralHom (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [IsIntegralHom f] : IsIntegralHom (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsIntegralHom @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsIntegralHom _)
/-
**AlgebraicGeometry.IsIntegralHom.of_comp** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.IsIntegralHom`。
形式化陈述：of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom (f ≫ g)] [IsSeparated g] : 
IsIntegralHom f
参数：f : X ⟶ Y；g : Y ⟶ Z；f ≫ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.IsIntegralHom.instHasOfPostcompPropertySchemeIsSeparat
ed`：CategoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.IsI
ntegralHom @AlgebraicGeometry.IsSeparated
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom (f ≫ g)] [IsSeparated g] :
    IsIntegralHom f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›
/-
**AlgebraicGeometry.IsIntegralHom.comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.IsIntegralHom`。
形式化陈述：comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsIntegralHom g] : IsIntegralHom (f ≫ g)
 ↔ IsIntegralHom f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsIntegralHom.of_comp`：of_comp (f : X ⟶ Y) (g : Y ⟶ Z)
 [IsIntegralHom (f ≫ g)] [IsSeparated g] : IsIntegralHom f
· 使用引理 `AlgebraicGeometry.IsSeparated.of_isAffineHom`：of_isAffineHom [h : IsAffi
neHom f] : IsSeparated f
· 使用定理 `AlgebraicGeometry.IsIntegralHom.toIsAffineHom`：∀ {X Y : AlgebraicGeometr
y.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsIntegralHom f],   AlgebraicGeo
metry.IsAffineHom f
· 使用定理 `AlgebraicGeometry.IsIntegralHom.instCompScheme`：∀ {X Y Z : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsIntegralHom f]   [Alge
braicGeometry.IsIntegralHom g], Alge…
-/
lemma comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) ↔ IsIntegralHom f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.SpecMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.IsIntegralHom`。
形式化陈述：SpecMap_iff {R S : CommRingCat} {φ : R ⟶ S} : IsIntegralHom (Spec.map φ) ↔
 φ.hom.IsIntegral
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `RingHom.isIntegral_respectsIso`：isIntegral_respectsIso : RespectsIso fun
 f => f.IsIntegral
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
-/
lemma SpecMap_iff {R S : CommRingCat} {φ : R ⟶ S} :
    IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom), and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
    (arrowIsoΓSpecOfIsAffine φ).symm, inferInstance]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMultiplicative @IsIntegralHom where
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (Limits.coprod.desc f g) := by
  refine hasAffineProperty.coprodDesc_affineAnd RingHom.isIntegral_respectsIso ?_ _ _ ‹_› ‹_›
  intros R S T _ _ _ f g _ _
  algebraize [f, g]
  refine algebraMap_isIntegral_iff.mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.
IsIntegralHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (f : X ⟶ Y) [IsIntegralHom f] :
    UniversallyClosed f := by
  revert X Y f ‹IsIntegralHom f›
  rw [universallyClosed_eq, ← IsStableUnderBaseChange.universally_eq (P := @IsIntegralHom)]
  apply universally_mono
  intro X Y f
  wlog hY : ∃ R, Y = Spec R generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := topologically _) Y.affineCover]
    exact fun a i ↦ this _ ⟨_, rfl⟩ (a i)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · intro H
    have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := topologically _) X.isoSpec.inv]
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv] at H
    exact this _ ⟨_, rfl⟩ H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [SpecMap_iff]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom** 是 Math
lib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsIntegralHom`。
形式化陈述：iff_universallyClosed_and_isAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y} : IsI
ntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsIntegralHom.instUniversallyClosed`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsIntegralHom f],   AlgebraicGe
ometry.UniversallyClosed f
· 使用定理 `AlgebraicGeometry.IsIntegralHom.toIsAffineHom`：∀ {X Y : AlgebraicGeometr
y.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsIntegralHom f],   AlgebraicGeo
metry.IsAffineHom f
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsIntegralHom.SpecMap_iff`：SpecMap_iff {R S : CommRing
Cat} {φ : R ⟶ S} : IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral
· 使用引理 `PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom`：isIntegral_of_
isClosedMap_comap_mapRingHom (h : IsClosedMap (comap (mapRingHom f))) : f.IsInte
gral
· 使用定理 `AlgebraicGeometry.UniversallyClosed.universally_isClosedMap`：∀ {X Y : Al
gebraicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.UniversallyClosed 
f],   (AlgebraicGeometry.topologically @IsClosedM…
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用引理 `AlgebraicGeometry.isPullback_SpecMap_of_isPushout`：isPullback_SpecMap_of
_isPushout {A B C P : CommRingCat} (f : A ⟶ B) (g : A ⟶ C) (inl : B ⟶ P) (inr : 
C ⟶ P) (h : IsPushout f g inl inr) : Is…
· 使用引理 `CommRingCat.isPushout_of_isPushout`：isPushout_of_isPushout (R S A B : Ty
pe u) [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S] [Algebra
 S B] [Algebra R A] [Alg…
· 使用定理 `instIsScalarTowerPolynomial`：∀ (R : Type u_1) (S : Type u_2) (A : Type u
_3) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [i
nst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsPushoutPolynomial`：∀ (R : Type u_1) [inst : CommSemiring R] {S : T
ype u_4} [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   Algebra.IsPushout R
 S (Polynomia…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.isAffine_of_isAffineHom`：isAffine_of_isAffineHom [IsAf
fineHom f] [IsAffine Y] : IsAffine X
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f],   Al
gebraicGeometry.UniversallyClosed f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instOfIsIsoScheme`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.IsClos
edImmersion f
· 使用定理 `AlgebraicGeometry.instIsAffineHomCompScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsAffineHom f]   [Algebraic
Geometry.IsAffineHom g], Algebrai…
· 使用定理 `AlgebraicGeometry.IsIntegralHom.instOfIsClosedImmersion`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f],   Algeb
raicGeometry.IsIntegralHom f
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
（共 34 条，此处仅展示前 30 条）
-/
lemma iff_universallyClosed_and_isAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y} :
    IsIntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  clear * -
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover]
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) Y.affineCover] at H₁
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsAffineHom) Y.affineCover] at H₂
    exact fun _ ↦ this inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv]
    exact this _ inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
  rw [SpecMap_iff]
  apply PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom
  algebraize [φ.1, Polynomial.mapRingHom φ.1]
  exact H₁.universally_isClosedMap (Spec.map (CommRingCat.ofHom Polynomial.C))
    (Spec.map (CommRingCat.ofHom Polynomial.C)) (Spec.map _)
    (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S))).flip
/-
**AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsIntegralHom`。
形式化陈述：eq_universallyClosed_inf_isAffineHom : @IsIntegralHom = (@UniversallyClose
d ⊓ @IsAffineHom : MorphismProperty Scheme)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom`：i
ff_universallyClosed_and_isAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y} : IsIntegral
Hom f ↔ UniversallyClosed f ∧ IsAffineHom f
-/
lemma eq_universallyClosed_inf_isAffineHom :
    @IsIntegralHom = (@UniversallyClosed ⊓ @IsAffineHom : MorphismProperty Scheme) := by
  ext
  exact iff_universallyClosed_and_isAffineHom

end IsIntegralHom

end AlgebraicGeometry

