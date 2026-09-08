/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth morphisms and their fibers

## Main results

- `Smooth.of_smooth_fiberToSpecResidueField`: A flat morphism, locally of
  finite presentation and smooth fibers is smooth.

-/

public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- If `f : X ⟶ Y` is locally of finite presentation, flat and has smooth fibers, then `f` is
smooth. -/
/-
**AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Smooth`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFinitePresentation f]   [AlgebraicGeometry.Flat f],   (∀ (y : ↥Y), AlgebraicGeo
metry.Smooth (AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField f y)) →     A
lgebraicGeometry.Smooth f
参数：f : X ⟶ Y；∀ (y : ↥Y), AlgebraicGeometry.Smooth (AlgebraicGeometry.Scheme.Hom.
fiberToSpecResidueField f y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertySmoothSmooth`：AlgebraicGeometry.
HasRingHomProperty @AlgebraicGeometry.Smooth fun {R S} [CommRing R] [CommRing S]
 => RingHom.Smooth
· 使用定理 `Algebra.Smooth.of_formallySmooth_fiber`：∀ {R : Type u_1} {S : Type u_2} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Flat R 
S]   [Algebra.FinitePresenta…
· 使用定理 `AlgebraicGeometry.Flat.instHasRingHomPropertyFlat`：AlgebraicGeometry.Has
RingHomProperty @AlgebraicGeometry.Flat fun {R S} [CommRing R] [CommRing S] => R
ingHom.Flat
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFinitePresentationFinit
ePresentation`：AlgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOf
FinitePresentation   fun {R S} [CommRing R] [CommRing S] => RingHom.FiniteP…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RingHom.formallySmooth_algebraMap`：formallySmooth_algebraMap [Algebra R 
S] : (algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S
· 使用引理 `RingHom.Smooth.formallySmooth`：formallySmooth {f : R ->+* S} (hf : f.Smo
oth) : f.FormallySmooth
· 使用引理 `CommRingCat.hom_ofHom`：hom_ofHom {R S : Type u} [CommRing R] [CommRing S
] (f : R ->+* S) : (ofHom f).hom = f
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], 
  AlgebraicGeometry.LocallyOfFinitePresentation f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Flat.instOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeometry.Fl
at f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField.eq_1`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) (y : ↥Y),   AlgebraicGeometry.Scheme.Hom.fiber
ToSpecResidueField f y =     CategoryTheory.Lim…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd`：pullbackR
ightPullbackFstIso_inv_snd_snd : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
· 使用定理 `AlgebraicGeometry.instSmoothOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeometry.S
mooth f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.instSmoothSndScheme`：∀ {X Y S : AlgebraicGeometry.Sche
me} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.Smooth f],   AlgebraicGeometry.Sm
ooth (CategoryTheory.Limits…
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : X ⟶ Y` is locally of finite presentation, flat and has smooth fibers, th
en `f` is
smooth.
-/
lemma Smooth.of_smooth_fiberToSpecResidueField [LocallyOfFinitePresentation f] [Flat f]
    (h : ∀ y, Smooth (f.fiberToSpecResidueField y)) :
    Smooth f := by
  wlog h : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Smooth) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ (fun y ↦ ?_) ⟨_, rfl⟩
    apply MorphismProperty.of_isPullback
    · exact isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback _ _) _
    · infer_instance
  obtain ⟨R, rfl⟩ := h
  wlog h : ∃ S, X = Spec S generalizing f X
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) X.affineCover]
    intro i
    have _ (y) : Smooth (pullback.snd f ((Spec R).fromSpecResidueField y)) :=
      inferInstanceAs <| Smooth (f.fiberToSpecResidueField y)
    refine this _ (fun y ↦ ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨S, rfl⟩ := h
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [HasRingHomProperty.Spec_iff] at *
  algebraize [φ.hom]
  refine Algebra.Smooth.of_formallySmooth_fiber fun p hp ↦ ?_
  rw [← RingHom.formallySmooth_algebraMap]
  refine RingHom.Smooth.formallySmooth ?_
  rw [← CommRingCat.hom_ofHom (algebraMap p.ResidueField (p.Fiber ↑S)),
    ← HasRingHomProperty.Spec_iff (P := @Smooth), ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth)
    (Spec.fiberToSpecResidueFieldIso R S ⟨p, hp⟩)]
  exact h ⟨p, hp⟩

end AlgebraicGeometry

