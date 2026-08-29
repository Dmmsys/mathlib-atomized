/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import Mathlib.RingTheory.FreeCommRing
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Constructions of (co)limits in `CommRingCat`

In this file we provide the explicit (co)cones for various (co)limits in `CommRingCat`, including
* tensor product is the pushout
* tensor product over `ℤ` is the binary coproduct
* `ℤ` is the initial object
* `0` is the strict terminal object
* Cartesian product is the product
* arbitrary direct product of a family of rings is the product object (Pi object)
* `RingHom.eqLocus` is the equalizer

-/

@[expose] public section

universe u u'

open CategoryTheory Limits TensorProduct

namespace CommRingCat

section Pushout

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/--
Definition of `pushoutCocone` / `pushoutCocone` 的定义

English:
definition pushoutCocone
  signature: : Limits.PushoutCocone
  body: by
  fapply Limits.PushoutCocone.mk
  · exact CommRingCat.of (A otimes[R] B)
· exact ofHom Algebra.TensorProduct.includeLeftRingHom (A := A)
· exact ofHom Algebra.TensorProduct.includeRight.toRingHom (A := B)
  · ext r
    trans algebraMap R (A otimes[R] B) r
    · exact Algebra.TensorProduct.includ

中文:
定义 pushoutCocone
  签名: : Limits.PushoutCocone
  定义体: by
  fapply Limits.PushoutCocone.mk
  · exact CommRingCat.of (A otimes[R] B)
· exact ofHom Algebra.TensorProduct.includeLeftRingHom (A := A)
· exact ofHom Algebra.TensorProduct.includeRight.toRingHom (A := B)
  · ext r
    trans algebraMap R (A otimes[R] B) r
    · exact Algebra.TensorProduct.includ

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft.commutes, Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.includeRight.commutes, Algebra.TensorProduct.includeRight.toRingHom, CommRingCat, CommRingCat.of, Limits, Limits.PushoutCocone.mk, PushoutCocone, TensorProduct, algebraMap, commutes, fapply, includeLeft, includeLeftRingHom, includeRight, otimes, toRingHom
-/
def pushoutCocone : Limits.PushoutCocone
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) := by
  fapply Limits.PushoutCocone.mk
  · exact CommRingCat.of (A otimes[R] B)
· exact ofHom Algebra.TensorProduct.includeLeftRingHom (A := A)
· exact ofHom Algebra.TensorProduct.includeRight.toRingHom (A := B)
  · ext r
    trans algebraMap R (A otimes[R] B) r
    · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm

@[simp]
/--
theorem `pushoutCocone_inl` / 定理 `pushoutCocone_inl`

English:
theorem pushoutCocone_inl
  proof: rfl

@[simp]

中文:
定理 pushoutCocone_inl
  证明: rfl

@[simp]
-/
theorem pushoutCocone_inl :
    (pushoutCocone R A B).inl = ofHom (Algebra.TensorProduct.includeLeftRingHom (A := A)) :=
  rfl

@[simp]
/--
theorem `pushoutCocone_inr` / 定理 `pushoutCocone_inr`

English:
theorem pushoutCocone_inr
  proof: rfl

@[simp]

中文:
定理 pushoutCocone_inr
  证明: rfl

@[simp]

Depends on / 依赖: Nonempty, Nonempty.intro, overPushforwardOverAdj
-/
theorem pushoutCocone_inr :
    (pushoutCocone R A B).inr = ofHom (Algebra.TensorProduct.includeRight.toRingHom (A := B)) :=
  rfl

@[simp]
/--
theorem `pushoutCocone_pt` / 定理 `pushoutCocone_pt`

English:
theorem pushoutCocone_pt
  proof: rfl

中文:
定理 pushoutCocone_pt
  证明: rfl
-/
theorem pushoutCocone_pt :
    (pushoutCocone R A B).pt = CommRingCat.of (A otimes[R] B) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pushoutCoconeIsColimit` / `pushoutCoconeIsColimit` 的定义

English:
definition pushoutCoconeIsColimit
  signature: : Limits.IsColimit (pushoutCocone R A B)
  body: Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra (s.inl.hom.comp (algebraMap R A))
    let f' : A ->ₐ[R] s.pt :=
      { s.inl.hom with
        commutes' := fun r => rfl }
    let g' : B ->ₐ[R] s.pt :=
      { s.inr.hom with
commutes' := DFunLike.congr_fun congrArg Hom.

中文:
定义 pushoutCoconeIsColimit
  签名: : Limits.是余极限 (pushoutCocone R A B)
  定义体: Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra (s.inl.hom.comp (algebraMap R A))
    let f' : A ->ₐ[R] s.pt :=
      { s.inl.hom with
        commutes' := fun r => rfl }
    let g' : B ->ₐ[R] s.pt :=
      { s.inr.hom with
commutes' := DFunLike.congr_fun congrArg Hom.

Depends on / 依赖: Algebra, DFunLike, DFunLike.congr_fun, Hom.hom, Limits, Limits.PushoutCocone.isColimitAux, Limits.WalkingSpan.Hom.fst, Limits.WalkingSpan.Hom.snd, PushoutCocone, RingHom, RingHom.toAlgebra, WalkingSpan, algebraMap, commutes, congr_fun, infer_instance, isColimitAux, naturality, otimes, pushoutCocone
-/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone R A B) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra (s.inl.hom.comp (algebraMap R A))
    let f' : A ->ₐ[R] s.pt :=
      { s.inl.hom with
        commutes' := fun r => rfl }
    let g' : B ->ₐ[R] s.pt :=
      { s.inr.hom with
commutes' := DFunLike.congr_fun congrArg Hom.hom
          ((s.ι.naturality Limits.WalkingSpan.Hom.snd).trans
            (s.ι.naturality Limits.WalkingSpan.Hom.fst).symm) }
    letI : Algebra R (pushoutCocone R A B).pt := show Algebra R (A otimes[R] B) by infer_instance
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use ofHom (AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g'))
    simp only [pushoutCocone_inl, pushoutCocone_inr]
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_left_apply (A := A) _ _ x
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_right_apply (B := B) _ _ x
    intro h eq1 eq2
    let h' : A otimes[R] B ->ₐ[R] s.pt :=
      { h.hom with
        commutes' := fun r => by
          change h (algebraMap R A r otimesₜ[R] 1) = s.inl (algebraMap R A r)
          rw [← eq1]
          simp only [pushoutCocone_pt, coe_of]
          rfl }
    suffices h' = Algebra.TensorProduct.productMap f' g' by
      ext x
      change h' x = Algebra.TensorProduct.productMap f' g' x
      rw [this]
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [f', g', ← eq1, pushoutCocone_pt, ← eq2, AlgHom.toRingHom_eq_coe,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.coe_mk]
    change _ = h (a otimesₜ 1) * h (1 otimesₜ b)
    rw [← h.hom.map_mul]; rw [Algebra.TensorProduct.tmul_mul_tmul]; rw [mul_one]; rw [one_mul]
    rfl

/--
lemma `isPushout_tensorProduct` / 引理 `isPushout_tensorProduct`

English:
lemma isPushout_tensorProduct
  statement: (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  proof: by
    ext
    simp
  isColimit' := ⟨pushoutCoconeIsColimit R A B⟩

中文:
引理 isPushout_tensorProduct
  结论: (R A B : 类型u) [交换环 R] [交换环 A] [交换环 B]
  证明: by
    ext
    simp
  isColimit' := ⟨pushoutCoconeIsColimit R A B⟩

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeftRingHom, TensorProduct, includeLeftRingHom, otimes
-/
lemma isPushout_tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    IsPushout (ofHom <| algebraMap R A) (ofHom <| algebraMap R B)
      (ofHom (S := A otimes[R] B) <| Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := A otimes[R] B) <| Algebra.TensorProduct.includeRight.toRingHom) where
  w := by
    ext
    simp
  isColimit' := ⟨pushoutCoconeIsColimit R A B⟩

/--
lemma `isPushout_of_isPushout` / 引理 `isPushout_of_isPushout`

English:
lemma isPushout_of_isPushout
  statement: (R S A B : Type u) [CommRing R] [CommRing S]
  proof: (isPushout_tensorProduct R S A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Algebra.IsPushout.equiv R S A B).toCommRingCatIso (by simp) (by simp)
    (by ext; simp [Algebra.IsPushout.equiv_tmul]) (by ext; simp [Algebra.IsPushout.equiv_tmul])

中文:
引理 isPushout_of_isPushout
  结论: (R S A B : 类型u) [交换环 R] [交换环 S]
  证明: (isPushout_tensorProduct R S A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Algebra.IsPushout.equiv R S A B).toCommRingCatIso (by simp) (by simp)
    (by ext; simp [Algebra.IsPushout.equiv_tmul]) (by ext; simp [Algebra.IsPushout.equiv_tmul])

Depends on / 依赖: Algebra, Algebra.IsPushout.equiv, Algebra.IsPushout.equiv_tmul, IsPushout, Iso.refl, equiv_tmul, isPushout_tensorProduct, of_iso, toCommRingCatIso
-/
lemma isPushout_of_isPushout (R S A B : Type u) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] :
    IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R A))
      (ofHom (algebraMap S B)) (ofHom (algebraMap A B)) :=
  (isPushout_tensorProduct R S A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Algebra.IsPushout.equiv R S A B).toCommRingCatIso (by simp) (by simp)
    (by ext; simp [Algebra.IsPushout.equiv_tmul]) (by ext; simp [Algebra.IsPushout.equiv_tmul])

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `isPushout_iff_isPushout` / 引理 `isPushout_iff_isPushout`

English:
lemma isPushout_iff_isPushout
  statement: {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  proof: by
  refine ⟨fun h => ?_, fun h => isPushout_of_isPushout ..⟩
  let e : R' otimes[R] S ≃+* S' := ((CommRingCat.isPushout_tensorProduct R R' S).isoPushout ≪≫
      h.isoPushout.symm).commRingCatIsoToRingEquiv
  have h2 (r : R') : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (r ot

中文:
引理 isPushout_iff_isPushout
  结论: {R S : 类型u} [交换环 R] [交换环 S] [代数 R S]
  证明: by
  refine ⟨fun h => ?_, fun h => isPushout_of_isPushout ..⟩
  let e : R' otimes[R] S ≃+* S' := ((CommRingCat.isPushout_tensorProduct R R' S).isoPushout ≪≫
      h.isoPushout.symm).commRingCatIsoToRingEquiv
  have h2 (r : R') : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (r ot

Depends on / 依赖: CommRingCat, CommRingCat.isPushout_tensorProduct, RingHom, RingHom.coe_c, coe_c, commRingCatIsoToRingEquiv, h.inl_isoPushout_inv, h.isoPushout.symm, hom_comp, inl_isoPushout_hom, inl_isoPushout_inv, isPushout_of_isPushout, isPushout_tensorProduct, isoPushout, isoPushout.hom, otimes, pushout, pushout.inl
-/
lemma isPushout_iff_isPushout {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    IsPushout (ofHom <| algebraMap R R') (ofHom <| algebraMap R S)
      (ofHom <| algebraMap R' S') (ofHom <| algebraMap S S') ↔ Algebra.IsPushout R R' S S' := by
  refine ⟨fun h => ?_, fun h => isPushout_of_isPushout ..⟩
  let e : R' otimes[R] S ≃+* S' := ((CommRingCat.isPushout_tensorProduct R R' S).isoPushout ≪≫
      h.isoPushout.symm).commRingCatIsoToRingEquiv
  have h2 (r : R') : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (r otimesₜ 1) = (pushout.inl (ofHom _) (ofHom _)) r :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inl_isoPushout_hom).hom r)
  have h3 (x : R') := congr($(h.inl_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h3
  let e' : R' otimes[R] S ≃ₐ[R'] S' := {
    __ := e
    commutes' r := by simp [Iso.commRingCatIsoToRingEquiv, h2, e, h3] }
  refine Algebra.IsPushout.of_equiv e' ?_
  ext s
  have h1 : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (algebraMap S (R' otimes[R] S) s) = (pushout.inr (ofHom _) (ofHom _)) s :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inr_isoPushout_hom).hom s)
  have h4 (x : S) := congr($(h.inr_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h4
  simp [Iso.commRingCatIsoToRingEquiv, h1, e', e, h4]

/--
lemma `isPushout_of_isLocalization` / 引理 `isPushout_of_isLocalization`

English:
lemma isPushout_of_isLocalization
  statement: {R S Rₘ Sₘ : Type u}
  proof: by
  algebraize [f, fₘ, fₘ.comp (algebraMap R Rₘ)]
  have : IsScalarTower R S Sₘ := .of_algebraMap_eq' H
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := ‹_›
  exact CommRingCat.isPushout_iff_isPushout.mpr (Algebra.isPushout_of_isLocalization M _ _ _)

中文:
引理 isPushout_of_isLocalization
  结论: {R S Rₘ Sₘ : 类型u}
  证明: by
  algebraize [f, fₘ, fₘ.comp (algebraMap R Rₘ)]
  have : IsScalarTower R S Sₘ := .of_algebraMap_eq' H
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := ‹_›
  exact CommRingCat.isPushout_iff_isPushout.mpr (Algebra.isPushout_of_isLocalization M _ _ _)

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Algebra.isPushout_of_isLocalization, CommRingCat, CommRingCat.isPushout_iff_isPushout.mpr, IsLocalization, IsScalarTower, algebraMap, algebraMapSubmonoid, algebraize, isPushout_iff_isPushout, isPushout_of_isLocalization, of_algebraMap_eq
-/
lemma isPushout_of_isLocalization {R S Rₘ Sₘ : Type u}
    [CommRing R] [CommRing Rₘ] [Algebra R Rₘ] [CommRing S] [CommRing Sₘ] [Algebra S Sₘ]
    (f : R ->+* S) (fₘ : Rₘ ->+* Sₘ) (H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).comp f)
    (M : Submonoid R) [IsLocalization M Rₘ] [IsLocalization (M.map f) Sₘ] :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (algebraMap R Rₘ))
      (CommRingCat.ofHom (algebraMap S Sₘ)) (CommRingCat.ofHom fₘ) := by
  algebraize [f, fₘ, fₘ.comp (algebraMap R Rₘ)]
  have : IsScalarTower R S Sₘ := .of_algebraMap_eq' H
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := ‹_›
  exact CommRingCat.isPushout_iff_isPushout.mpr (Algebra.isPushout_of_isLocalization M _ _ _)

/--
lemma `closure_range_union_range_eq_top_of_isPushout` / 引理 `closure_range_union_range_eq_top_of_isPushout`

English:
lemma closure_range_union_range_eq_top_of_isPushout
  proof: by
  algebraize [f.hom, g.hom]
  let e := ((isPushout_tensorProduct R A B).isoIsPushout A B H).commRingCatIsoToRingEquiv
  rw [← Subring.comap_map_eq_self_of_injective e.symm.injective (.closure _)]; rw [RingHom.map_closure]; rw [← top_le_iff]; rw [← Subring.map_le_iff_le_comap]; rw [Set.image_union

中文:
引理 closure_range_union_range_eq_top_of_isPushout
  证明: by
  algebraize [f.hom, g.hom]
  let e := ((isPushout_tensorProduct R A B).isoIsPushout A B H).commRingCatIsoToRingEquiv
  rw [← Subring.comap_map_eq_self_of_injective e.symm.injective (.closure _)]; rw [RingHom.map_closure]; rw [← top_le_iff]; rw [← Subring.map_le_iff_le_comap]; rw [Set.image_union

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, IsPushout, IsPushout.inl_isoIsPushout_inv, IsPushout.inr_isoIsPushout_inv, RingHom, RingHom.coe_comp, RingHom.map_closure, Set.image_union, Set.range_comp, Subring, Subring.comap_map_eq_self_of_injective, Subring.map_le_iff_le_comap, algebraize, closure, coe_comp, comap_map_eq_self_of_injective, commRingCatIsoToRingEquiv, e.symm.injective, f.hom
-/
lemma closure_range_union_range_eq_top_of_isPushout
    {R A B X : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B} {a : A ⟶ X} {b : B ⟶ X}
    (H : IsPushout f g a b) :
    Subring.closure (Set.range a union Set.range b) = ⊤ := by
  algebraize [f.hom, g.hom]
  let e := ((isPushout_tensorProduct R A B).isoIsPushout A B H).commRingCatIsoToRingEquiv
  rw [← Subring.comap_map_eq_self_of_injective e.symm.injective (.closure _)]; rw [RingHom.map_closure]; rw [← top_le_iff]; rw [← Subring.map_le_iff_le_comap]; rw [Set.image_union]
  simp only [AlgHom.toRingHom_eq_coe, ← Set.range_comp, ← RingHom.coe_comp]
  rw [← hom_comp]; rw [← hom_comp]; rw [IsPushout.inl_isoIsPushout_inv]; rw [IsPushout.inr_isoIsPushout_inv]; rw [hom_ofHom]; rw [hom_ofHom]
  exact le_top.trans (Algebra.TensorProduct.closure_range_union_range_eq_top R A B).ge

end Pushout

section BinaryCoproduct

variable (A B : CommRingCat.{u})

/-- The tensor product `A ⊗[ℤ] B` forms a cocone for `A` and `B`. -/
@[simps! pt ι]
/--
Definition of `coproductCocone` / `coproductCocone` 的定义

English:
definition coproductCocone
  signature: : BinaryCofan A B
  body: BinaryCofan.mk
    (ofHom (Algebra.TensorProduct.includeLeft (S := Int)).toRingHom : A ⟶ of (A otimes[Int] B))
    (ofHom (Algebra.TensorProduct.includeRight (R := Int)).toRingHom : B ⟶ of (A otimes[Int] B))

@[simp]

中文:
定义 coproductCocone
  签名: : BinaryCofan A B
  定义体: BinaryCofan.mk
    (ofHom (Algebra.TensorProduct.includeLeft (S := Int)).toRingHom : A ⟶ of (A otimes[Int] B))
    (ofHom (Algebra.TensorProduct.includeRight (R := Int)).toRingHom : B ⟶ of (A otimes[Int] B))

@[simp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, BinaryCofan, BinaryCofan.mk, TensorProduct, includeLeft, includeRight, otimes, toRingHom
-/
def coproductCocone : BinaryCofan A B :=
  BinaryCofan.mk
    (ofHom (Algebra.TensorProduct.includeLeft (S := Int)).toRingHom : A ⟶ of (A otimes[Int] B))
    (ofHom (Algebra.TensorProduct.includeRight (R := Int)).toRingHom : B ⟶ of (A otimes[Int] B))

@[simp]
/--
theorem `coproductCocone_inl` / 定理 `coproductCocone_inl`

English:
theorem coproductCocone_inl
  proof: rfl

@[simp]

中文:
定理 coproductCocone_inl
  证明: rfl

@[simp]

Depends on / 依赖: toRingHom
-/
theorem coproductCocone_inl :
    (coproductCocone A B).inl = ofHom (Algebra.TensorProduct.includeLeft (S := Int)).toRingHom := rfl

@[simp]
/--
theorem `coproductCocone_inr` / 定理 `coproductCocone_inr`

English:
theorem coproductCocone_inr
  proof: rfl

中文:
定理 coproductCocone_inr
  证明: rfl

Depends on / 依赖: toRingHom
-/
theorem coproductCocone_inr :
    (coproductCocone A B).inr = ofHom (Algebra.TensorProduct.includeRight (R := Int)).toRingHom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product `A ⊗[ℤ] B` is a coproduct for `A` and `B`. -/
@[simps]
/--
Definition of `coproductCoconeIsColimit` / `coproductCoconeIsColimit` 的定义

English:
definition coproductCoconeIsColimit
  signature: : IsColimit (coproductCocone A B) where
  body: ofHom (Algebra.TensorProduct.lift s.inl.hom.toIntAlgHom s.inr.hom.toIntAlgHom
      (fun _ _ => by apply Commute.all)).toRingHom
  fac (s : BinaryCofan A B) := fun ⟨j⟩ => by cases j <;> ext a <;> simp
  uniq (s : BinaryCofan A B) := by
    rintro ⟨m : A otimes[Int] B ->+* s.pt⟩ hm
    apply CommRing

中文:
定义 coproductCoconeIsColimit
  签名: : 是余极限 (coproductCocone A B) where
  定义体: ofHom (Algebra.TensorProduct.lift s.inl.hom.toIntAlgHom s.inr.hom.toIntAlgHom
      (fun _ _ => by apply Commute.all)).toRingHom
  fac (s : BinaryCofan A B) := fun ⟨j⟩ => by cases j <;> ext a <;> simp
  uniq (s : BinaryCofan A B) := by
    rintro ⟨m : A otimes[Int] B ->+* s.pt⟩ hm
    apply CommRing

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.TensorProduct.liftEquiv.symm.injective, Algebra.TensorProduct.liftEquiv_symm_apply_coe, BinaryCofan, CommRingCat, CommRingCat.hom_ext, Commute, Commute.all, Prod.mk.injEq, RingHom, RingHom.toIntAlgHom_injective, Subtype, Subtype.ext, TensorProduct, hom_ext, injective, liftEquiv, liftEquiv_symm_apply_coe, otimes
-/
def coproductCoconeIsColimit : IsColimit (coproductCocone A B) where
  desc (s : BinaryCofan A B) :=
    ofHom (Algebra.TensorProduct.lift s.inl.hom.toIntAlgHom s.inr.hom.toIntAlgHom
      (fun _ _ => by apply Commute.all)).toRingHom
  fac (s : BinaryCofan A B) := fun ⟨j⟩ => by cases j <;> ext a <;> simp
  uniq (s : BinaryCofan A B) := by
    rintro ⟨m : A otimes[Int] B ->+* s.pt⟩ hm
    apply CommRingCat.hom_ext
    apply RingHom.toIntAlgHom_injective
    apply Algebra.TensorProduct.liftEquiv.symm.injective
    apply Subtype.ext
    rw [Algebra.TensorProduct.liftEquiv_symm_apply_coe]; rw [Prod.mk.injEq]
    constructor
    · ext a
      simp [map_one, mul_one, ← hm (Discrete.mk WalkingPair.left)]
    · ext b
      simp [map_one, ← hm (Discrete.mk WalkingPair.right)]

/--
Definition of `coproductColimitCocone` / `coproductColimitCocone` 的定义

English:
definition coproductColimitCocone
  signature: : Limits.ColimitCocone (pair A B)
  body: ⟨_, coproductCoconeIsColimit A B⟩

中文:
定义 coproductColimitCocone
  签名: : Limits.余极限余锥 (pair A B)
  定义体: ⟨_, coproductCoconeIsColimit A B⟩

Depends on / 依赖: coproductCoconeIsColimit
-/
def coproductColimitCocone : Limits.ColimitCocone (pair A B) :=
  ⟨_, coproductCoconeIsColimit A B⟩

end BinaryCoproduct


section Terminal

instance (X : CommRingCat.{u}) : Unique (X ⟶ CommRingCat.of.{u} PUnit) :=
⟨⟨ofHom ⟨1, rfl, by simp⟩⟩, fun f => by ext⟩

/--
Definition of `punitIsTerminal` / `punitIsTerminal` 的定义

English:
definition punitIsTerminal
  signature: : IsTerminal (CommRingCat.of.{u} PUnit)
  body: IsTerminal.ofUnique _

中文:
定义 punitIsTerminal
  签名: : 是终止 (交换环范畴.of.{u} 命题单元)
  定义体: IsTerminal.ofUnique _

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit) :=
  IsTerminal.ofUnique _

/--
Instance `commRingCat_hasStrictTerminalObjects` / 实例 `commRingCat_hasStrictTerminalObjects`

English:
instance commRingCat_hasStrictTerminalObjects
  signature: : HasStrictTerminalObjects CommRingCat.{u}
  body: by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine ⟨ofHom ⟨1, rfl, by simp⟩, ?_, ?_⟩
  · ext
  · ext x
    have e : (0 : X) = 1 := by
      rw [← f.hom.map_one]; rw [← f.hom.map_zero]
    replace e : 0 * x = 1 * x := congr_arg (· * x) e
    rw [one_

中文:
实例 commRingCat_hasStrictTerminalObjects
  签名: : 有StrictTerminalObjects 交换环范畴.{u}
  定义体: by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine ⟨ofHom ⟨1, rfl, by simp⟩, ?_, ?_⟩
  · ext
  · ext x
    have e : (0 : X) = 1 := by
      rw [← f.hom.map_one]; rw [← f.hom.map_zero]
    replace e : 0 * x = 1 * x := congr_arg (· * x) e
    rw [one_

Depends on / 依赖: CommRingCat, CommRingCat.of, congr_arg, f.hom.map_one, f.hom.map_zero, hasStrictTerminalObjects_of_terminal_is_strict, map_one, map_zero, one_mul, replace, zero_mul
-/
instance commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCat.{u} := by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine ⟨ofHom ⟨1, rfl, by simp⟩, ?_, ?_⟩
  · ext
  · ext x
    have e : (0 : X) = 1 := by
      rw [← f.hom.map_one]; rw [← f.hom.map_zero]
    replace e : 0 * x = 1 * x := congr_arg (· * x) e
    rw [one_mul]; rw [zero_mul]; rw [← f.hom.map_zero] at e
    exact e

/--
theorem `subsingleton_of_isTerminal` / 定理 `subsingleton_of_isTerminal`

English:
theorem subsingleton_of_isTerminal
  given: {X : CommRingCat} (hX : IsTerminal X)
  statement: Subsingleton X
  proof: (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)

中文:
定理 subsingleton_of_isTerminal
  条件: {X : 交换环范畴} (hX : 是终止 X)
  结论: 子单例 X
  证明: (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)

Depends on / 依赖: IsFiniteType, Subsingleton, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr, generators, generators.ofEpi, hX.uniqueUpToIso, infer_instance, punitIsTerminal, subsingleton_congr, toEquiv, uniqueUpToIso
-/
theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)

/--
Definition of `zIsInitial` / `zIsInitial` 的定义

English:
definition zIsInitial
  signature: : IsInitial (CommRingCat.of Int)
  body: IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| Int.castRingHom R⟩,
fun a => hom_ext a.hom.ext_int _⟩)

中文:
定义 zIsInitial
  签名: : IsInitial (交换环范畴.of 整数)
  定义体: IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| Int.castRingHom R⟩,
fun a => hom_ext a.hom.ext_int _⟩)

Depends on / 依赖: Int.castRingHom, IsInitial, IsInitial.ofUnique, a.hom.ext_int, castRingHom, ext_int, hom_ext, ofUnique
-/
def zIsInitial : IsInitial (CommRingCat.of Int) :=
  IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| Int.castRingHom R⟩,
fun a => hom_ext a.hom.ext_int _⟩)

/--
Definition of `isInitial` / `isInitial` 的定义

English:
definition isInitial
  signature: : IsInitial (CommRingCat.of (ULift.{u} Int))
  body: IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| (Int.castRingHom R).comp ULift.ringEquiv.toRingHom⟩,
    fun _ => by
      ext : 1
      rw [← RingHom.cancel_right (f := (ULift.ringEquiv.{0]; rw [u} (R := Int)).symm.toRingHom)
        (hf := ULift.ringEquiv.symm.surjective)]
      apply RingHom.ext_int

中文:
定义 isInitial
  签名: : IsInitial (交换环范畴.of (类型层提升.{u} 整数))
  定义体: IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| (Int.castRingHom R).comp ULift.ringEquiv.toRingHom⟩,
    fun _ => by
      ext : 1
      rw [← RingHom.cancel_right (f := (ULift.ringEquiv.{0]; rw [u} (R := Int)).symm.toRingHom)
        (hf := ULift.ringEquiv.symm.surjective)]
      apply RingHom.ext_int

Depends on / 依赖: Int.castRingHom, IsInitial, IsInitial.ofUnique, RingHom, RingHom.cancel_right, RingHom.ext_int, ULift.ringEquiv, ULift.ringEquiv.symm.surjective, ULift.ringEquiv.toRingHom, cancel_right, castRingHom, ext_int, ofUnique, ringEquiv, surjective, symm.toRingHom, toRingHom
-/
def isInitial : IsInitial (CommRingCat.of (ULift.{u} Int)) :=
  IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| (Int.castRingHom R).comp ULift.ringEquiv.toRingHom⟩,
    fun _ => by
      ext : 1
      rw [← RingHom.cancel_right (f := (ULift.ringEquiv.{0]; rw [u} (R := Int)).symm.toRingHom)
        (hf := ULift.ringEquiv.symm.surjective)]
      apply RingHom.ext_int⟩)

end Terminal

section Product

variable (A B : CommRingCat.{u})

/-- The product in `CommRingCat` is the Cartesian product. This is the binary fan. -/
@[simps! pt]
/--
Definition of `prodFan` / `prodFan` 的定义

English:
definition prodFan
  signature: : BinaryFan A B
  body: BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)

中文:
定义 prodFan
  签名: : BinaryFan A B
  定义体: BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)

Depends on / 依赖: BinaryFan, BinaryFan.mk, CommRingCat, CommRingCat.ofHom, RingHom, RingHom.fst, RingHom.snd
-/
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `prodFanIsLimit` / `prodFanIsLimit` 的定义

English:
definition prodFanIsLimit
  signature: : IsLimit (prodFan A B) where
  body: ofHom RingHom.prod (c.π.app ⟨WalkingPair.left⟩).hom (c.π.app ⟨WalkingPair.right⟩).hom
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right] <;> rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, Bi

中文:
定义 prodFanIsLimit
  签名: : 是极限 (prodFan A B) where
  定义体: ofHom RingHom.prod (c.π.app ⟨WalkingPair.left⟩).hom (c.π.app ⟨WalkingPair.right⟩).hom
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right] <;> rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, Bi

Depends on / 依赖: RingHom, RingHom.prod, WalkingPair, WalkingPair.left, WalkingPair.right
-/
def prodFanIsLimit : IsLimit (prodFan A B) where
lift c := ofHom RingHom.prod (c.π.app ⟨WalkingPair.left⟩).hom (c.π.app ⟨WalkingPair.right⟩).hom
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right] <;> rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, BinaryFan.snd s x)
    have eq1 : (m ≫ (A.prodFan B).fst) x = (BinaryFan.fst s) x :=
      ConcreteCategory.congr_hom (h ⟨WalkingPair.left⟩) x
    have eq2 : (m ≫ (A.prodFan B).snd) x = (BinaryFan.snd s) x :=
      ConcreteCategory.congr_hom (h ⟨WalkingPair.right⟩) x
    rw [← eq1]; rw [← eq2]
    simp [prodFan]

end Product

section Pi

variable {ι : Type u} (R : ι -> CommRingCat.{u})

/--
The categorical product of rings is the Cartesian product of rings. This is its `Fan`.
-/
@[simps! pt]
/--
Definition of `piFan` / `piFan` 的定义

English:
definition piFan
  signature: : Fan R
  body: Fan.mk (CommRingCat.of ((i : ι) -> R i)) (fun i => ofHom <| Pi.evalRingHom _ i)

中文:
定义 piFan
  签名: : Fan R
  定义体: Fan.mk (CommRingCat.of ((i : ι) -> R i)) (fun i => ofHom <| Pi.evalRingHom _ i)

Depends on / 依赖: CommRingCat, CommRingCat.of, Fan.mk, Pi.evalRingHom, evalRingHom
-/
def piFan : Fan R :=
  Fan.mk (CommRingCat.of ((i : ι) -> R i)) (fun i => ofHom <| Pi.evalRingHom _ i)

/--
Definition of `piFanIsLimit` / `piFanIsLimit` 的定义

English:
definition piFanIsLimit
  signature: : IsLimit (piFan R) where
  body: ofHom RingHom.pi fun i => (s.π.1 ⟨i⟩).hom
  fac s i := by rfl
uniq _ _ h := hom_ext DFunLike.ext _ _ fun x => funext fun i =>
    DFunLike.congr_fun (congrArg Hom.hom <| h ⟨i⟩) x

中文:
定义 piFanIsLimit
  签名: : 是极限 (piFan R) where
  定义体: ofHom RingHom.pi fun i => (s.π.1 ⟨i⟩).hom
  fac s i := by rfl
uniq _ _ h := hom_ext DFunLike.ext _ _ fun x => funext fun i =>
    DFunLike.congr_fun (congrArg Hom.hom <| h ⟨i⟩) x

Depends on / 依赖: RingHom, RingHom.pi
-/
def piFanIsLimit : IsLimit (piFan R) where
lift s := ofHom RingHom.pi fun i => (s.π.1 ⟨i⟩).hom
  fac s i := by rfl
uniq _ _ h := hom_ext DFunLike.ext _ _ fun x => funext fun i =>
    DFunLike.congr_fun (congrArg Hom.hom <| h ⟨i⟩) x

/--
Definition of `piIsoPi` / `piIsoPi` 的定义

English:
definition piIsoPi
  signature: : ∏ᶜ R ≅ CommRingCat.of ((i : ι) -> R i)
  body: limit.isoLimitCone ⟨_, piFanIsLimit R⟩

中文:
定义 piIsoPi
  签名: : ∏ᶜ R ≅ 交换环范畴.of ((i : ι) -> R i)
  定义体: limit.isoLimitCone ⟨_, piFanIsLimit R⟩

Depends on / 依赖: isoLimitCone, limit.isoLimitCone, piFanIsLimit
-/
noncomputable def piIsoPi : ∏ᶜ R ≅ CommRingCat.of ((i : ι) -> R i) :=
  limit.isoLimitCone ⟨_, piFanIsLimit R⟩

/--
Definition of `_root_.RingEquiv.piEquivPi` / `_root_.RingEquiv.piEquivPi` 的定义

English:
definition _root_.RingEquiv.piEquivPi
  signature: (R : ι -> Type u) [forall i, CommRing (R i)]
  body: (piIsoPi (CommRingCat.of <| R ·)).commRingCatIsoToRingEquiv

中文:
定义 _root_.环等价.piEquivPi
  签名: (R : ι -> 类型u) [对任意 i, 交换环 (R i)]
  定义体: (piIsoPi (CommRingCat.of <| R ·)).commRingCatIsoToRingEquiv

Depends on / 依赖: CommRingCat, CommRingCat.of, commRingCatIsoToRingEquiv, piIsoPi
-/
noncomputable def _root_.RingEquiv.piEquivPi (R : ι -> Type u) [forall i, CommRing (R i)] :
    (∏ᶜ (fun i : ι => CommRingCat.of (R i)) : CommRingCat.{u}) ≃+* ((i : ι) -> R i) :=
  (piIsoPi (CommRingCat.of <| R ·)).commRingCatIsoToRingEquiv

end Pi

namespace Limits

variable {J : Type u'} [SmallCategory J] (F : J ⥤ CommRingCat.{u}) {c : Cone F}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isUnit_iff_forall_isUnit` / 定理 `isUnit_iff_forall_isUnit`

English:
theorem isUnit_iff_forall_isUnit
  given: (hc : IsLimit c) (r : c.pt)
  statement: IsUnit r ↔
  proof: by
  refine ⟨fun h _ => h.map _, fun h => ?_⟩
  simp only [isUnit_iff_exists_inv] at h ⊢
  choose inv h_inv using h
  have map_inv {j k : J} (f : j ⟶ k) : F.map f (inv j) = inv k := by
    have h := congr(F.map f $(h_inv j))
    have : F.map f (c.π.app j r) = c.π.app k r :=
      DFunLike.congr_fun 

中文:
定理 isUnit_iff_对任意_isUnit
  条件: (hc : 是极限 c) (r : c.pt)
  结论: 是单位 r ↔
  证明: by
  refine ⟨fun h _ => h.map _, fun h => ?_⟩
  simp only [isUnit_iff_exists_inv] at h ⊢
  choose inv h_inv using h
  have map_inv {j k : J} (f : j ⟶ k) : F.map f (inv j) = inv k := by
    have h := congr(F.map f $(h_inv j))
    have : F.map f (c.π.app j r) = c.π.app k r :=
      DFunLike.congr_fun 

Depends on / 依赖: CommRingCat, CommRingCat.of, DFunLike, DFunLike.congr_fun, F.map, Hom.hom, congr_fun, h.map, h_inv, infer_instance, inv_r, isUnit_iff_exists_inv, map_inv, map_mul, map_one, mul_assoc, mul_comm, mul_one, nth_rw, one_mul
-/
theorem isUnit_iff_forall_isUnit (hc : IsLimit c) (r : c.pt) : IsUnit r ↔
    forall (j : J), IsUnit (c.π.app j r) := by
  refine ⟨fun h _ => h.map _, fun h => ?_⟩
  simp only [isUnit_iff_exists_inv] at h ⊢
  choose inv h_inv using h
  have map_inv {j k : J} (f : j ⟶ k) : F.map f (inv j) = inv k := by
    have h := congr(F.map f $(h_inv j))
    have : F.map f (c.π.app j r) = c.π.app k r :=
      DFunLike.congr_fun (congr(Hom.hom $(c.w f))) r
    rw [map_mul]; rw [map_one]; rw [this] at h
    rw [← mul_one (F.map f (inv j))]; rw [← h_inv k]; rw [← mul_assoc]
    nth_rw 2 [mul_comm]; rw [h, one_mul]
  let inv_r : Cone F := .mk (CommRingCat.of (FreeCommRing PUnit)) {
    app j := ConcreteCategory.ofHom (FreeCommRing.lift (fun _ => inv j))
    naturality j k f := by
      ext1; change FreeCommRing.lift (fun _ => inv k) = _
      ext; simp [map_inv f] }
  use hc.lift inv_r (FreeCommRing.of PUnit.unit)
  refine Concrete.isLimit_ext _ hc _ _ fun j => ?_
  rw [RingHom.map_mul]; rw [RingHom.map_one]; convert h_inv j
  change (hc.lift inv_r ≫ c.π.app j) (FreeCommRing.of PUnit.unit) = inv j
  rw [IsLimit.fac]; exact FreeCommRing.lift_of ..

-- The assumption `hj` can be generalized to a zigzag-like assumption of finite steps.
/--
theorem `π_isLocalHom` / 定理 `π_isLocalHom`

English:
theorem π_isLocalHom
  statement: (hc : IsLimit c) (j : J) (hj : forall (x : c.pt), IsUnit (c.π.app j x) ->
  proof: by
  refine ⟨fun (x : c.pt) hx => (?_ : IsUnit x)⟩
  rw [isUnit_iff_forall_isUnit F hc]; intro i
  obtain ⟨k, f, g, lh, eq⟩ := hj x hx i
  exact lh.map_nonunit _ (eq ▸ hx.map _)

中文:
定理 π_isLocalHom
  结论: (hc : 是极限 c) (j : J) (hj : 对任意 (x : c.pt), 是单位 (c.π.app j x) ->
  证明: by
  refine ⟨fun (x : c.pt) hx => (?_ : IsUnit x)⟩
  rw [isUnit_iff_forall_isUnit F hc]; intro i
  obtain ⟨k, f, g, lh, eq⟩ := hj x hx i
  exact lh.map_nonunit _ (eq ▸ hx.map _)

Depends on / 依赖: IsUnit, c.pt, hx.map, isUnit_iff_forall_isUnit, lh.map_nonunit, map_nonunit
-/
theorem π_isLocalHom (hc : IsLimit c) (j : J) (hj : forall (x : c.pt), IsUnit (c.π.app j x) ->
    forall (i : J), exists (k : J) (f : i ⟶ k) (g : j ⟶ k), IsLocalHom (F.map f).hom ∧
      F.map f (c.π.app i x) = F.map g (c.π.app j x)) :
    IsLocalHom (c.π.app j).hom := by
  refine ⟨fun (x : c.pt) hx => (?_ : IsUnit x)⟩
  rw [isUnit_iff_forall_isUnit F hc]; intro i
  obtain ⟨k, f, g, lh, eq⟩ := hj x hx i
  exact lh.map_nonunit _ (eq ▸ hx.map _)

/--
theorem `isLocalRing` / 定理 `isLocalRing`

English:
theorem isLocalRing
  statement: (hc : IsLimit c) (j : J) [IsLocalRing (F.obj j)]
  proof: by
  have := π_isLocalHom F hc j hj
  apply RingHom.domain_isLocalRing (c.π.app j).hom

中文:
定理 isLocalRing
  结论: (hc : 是极限 c) (j : J) [是局部环 (F.obj j)]
  证明: by
  have := π_isLocalHom F hc j hj
  apply RingHom.domain_isLocalRing (c.π.app j).hom

Depends on / 依赖: RingHom, RingHom.domain_isLocalRing, domain_isLocalRing
-/
theorem isLocalRing (hc : IsLimit c) (j : J) [IsLocalRing (F.obj j)]
    (hj : forall (x : c.pt), IsUnit (c.π.app j x) -> forall (i : J), exists (k : J) (f : i ⟶ k) (g : j ⟶ k),
      IsLocalHom (F.map f).hom ∧ F.map f (c.π.app i x) = F.map g (c.π.app j x)) :
    IsLocalRing c.pt := by
  have := π_isLocalHom F hc j hj
  apply RingHom.domain_isLocalRing (c.π.app j).hom

end Limits

section Equalizer

variable {A B : CommRingCat.{u}} (f g : A ⟶ B)

/--
Definition of `equalizerFork` / `equalizerFork` 的定义

English:
definition equalizerFork
  signature: : Fork f g
  body: Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f.hom g.hom).subtype) by
      ext ⟨x, e⟩
      simpa using e

中文:
定义 equalizerFork
  签名: : 叉 f g
  定义体: Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f.hom g.hom).subtype) by
      ext ⟨x, e⟩
      simpa using e

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Fork.of, RingHom, RingHom.eqLocus, eqLocus, f.hom, g.hom, subtype
-/
def equalizerFork : Fork f g :=
Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f.hom g.hom).subtype) by
      ext ⟨x, e⟩
      simpa using e

/--
Definition of `equalizerForkIsLimit` / `equalizerForkIsLimit` 的定义

English:
definition equalizerForkIsLimit
  signature: : IsLimit (equalizerFork f g)
  body: by
  fapply Fork.IsLimit.mk'
  intro s
use ofHom s.ι.hom.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x :)
  constructor
  · ext
    rfl
  · intro m hm
    ext x
exact Subtype.ext RingHom.congr_fun (congrArg Hom.hom hm) x

中文:
定义 equalizerForkIsLimit
  签名: : 是极限 (equalizerFork f g)
  定义体: by
  fapply Fork.IsLimit.mk'
  intro s
use ofHom s.ι.hom.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x :)
  constructor
  · ext
    rfl
  · intro m hm
    ext x
exact Subtype.ext RingHom.congr_fun (congrArg Hom.hom hm) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Fork.IsLimit.mk, Hom.hom, IsLimit, M.property, RingHom, RingHom.congr_fun, Subtype, Subtype.ext, codRestrict, condition, congr_fun, congr_hom, fapply, hom.codRestrict, property, s.condition
-/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  intro s
use ofHom s.ι.hom.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x :)
  constructor
  · ext
    rfl
  · intro m hm
    ext x
exact Subtype.ext RingHom.congr_fun (congrArg Hom.hom hm) x

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (equalizerFork f g).ι.hom
  body: inferInstanceAs IsLocalHom (f.hom.eqLocus g.hom).subtype

中文:
实例 :
  签名: 是Local态射 (equalizerFork f g).ι.hom
  定义体: inferInstanceAs IsLocalHom (f.hom.eqLocus g.hom).subtype

Depends on / 依赖: IsLocalHom, eqLocus, f.hom.eqLocus, g.hom, subtype
-/
instance : IsLocalHom (equalizerFork f g).ι.hom :=
inferInstanceAs IsLocalHom (f.hom.eqLocus g.hom).subtype

open WalkingParallelPair WalkingParallelPairHom Opposite

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `equalizer_ι_isLocalHom` / 实例 `equalizer_ι_isLocalHom`

English:
instance equalizer_ι_isLocalHom
  signature: (F : WalkingParallelPair ⥤ CommRingCat.{u})
  body: by
  refine Limits.π_isLocalHom _ (limit.isLimit _) zero fun x hx i => ?_
  rcases i with _ | _
  · exact ⟨zero, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, 𝟙 _, left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π, RingHom.id_apply]
    ex

中文:
实例 equalizer_ι_isLocalHom
  签名: (F : WalkingParallelPair ⥤ 交换环范畴.{u})
  定义体: by
  refine Limits.π_isLocalHom _ (limit.isLimit _) zero fun x hx i => ?_
  rcases i with _ | _
  · exact ⟨zero, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, 𝟙 _, left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π, RingHom.id_apply]
    ex

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, IsFinitePresentation, IsFinitePresentation.exists_quasicoherentData, Limits, RingHom, RingHom.id_apply, cone_x, exists_quasicoherentData, hom_id, id_apply, isLimit, limit.cone_, limit.cone_x, limit.isLimit, limit.w_apply, map_id, w_apply
-/
instance equalizer_ι_isLocalHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F WalkingParallelPair.zero).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) zero fun x hx i => ?_
  rcases i with _ | _
  · exact ⟨zero, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, 𝟙 _, left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π, RingHom.id_apply]
    exact (limit.w_apply F left x).symm

/--
theorem `equalizer_limit_isLocalRing` / 定理 `equalizer_limit_isLocalRing`

English:
theorem equalizer_limit_isLocalRing
  statement: (F : WalkingParallelPair ⥤ CommRingCat.{u})
  proof: RingHom.domain_isLocalRing (limit.π F WalkingParallelPair.zero).hom

中文:
定理 equalizer_limit_isLocalRing
  结论: (F : WalkingParallelPair ⥤ 交换环范畴.{u})
  证明: RingHom.domain_isLocalRing (limit.π F WalkingParallelPair.zero).hom

Depends on / 依赖: IsFinitePresentation, IsFinitePresentation.exists_quasicoherentData, RingHom, RingHom.domain_isLocalRing, WalkingParallelPair, WalkingParallelPair.zero, domain_isLocalRing, exists_quasicoherentData, localGeneratorsData
-/
theorem equalizer_limit_isLocalRing (F : WalkingParallelPair ⥤ CommRingCat.{u})
    [IsLocalRing (F.obj zero)] : IsLocalRing ↑(limit F) :=
  RingHom.domain_isLocalRing (limit.π F WalkingParallelPair.zero).hom

/--
Instance `equalizer_ι_isLocalHom'` / 实例 `equalizer_ι_isLocalHom'`

English:
instance equalizer_ι_isLocalHom'
  signature: (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u})
  body: by
  refine Limits.π_isLocalHom _ (limit.isLimit _) (op one) fun x hx i => ?_
  rcases i with _ | _
  · refine ⟨op zero, 𝟙 _, op left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π,
      RingHom.id_apply]
    exact (limit.w_apply F (op left) x).

中文:
实例 equalizer_ι_isLocalHom'
  签名: (F : WalkingParallelPairᵒᵖ ⥤ 交换环范畴.{u})
  定义体: by
  refine Limits.π_isLocalHom _ (limit.isLimit _) (op one) fun x hx i => ?_
  rcases i with _ | _
  · refine ⟨op zero, 𝟙 _, op left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π,
      RingHom.id_apply]
    exact (limit.w_apply F (op left) x).

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, Limits, RingHom, RingHom.id_apply, cone_x, hom_id, id_apply, isLimit, limit.cone_, limit.cone_x, limit.isLimit, limit.w_apply, map_id, w_apply
-/
instance equalizer_ι_isLocalHom' (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F (op one)).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) (op one) fun x hx i => ?_
  rcases i with _ | _
  · refine ⟨op zero, 𝟙 _, op left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π,
      RingHom.id_apply]
    exact (limit.w_apply F (op left) x).symm
  · exact ⟨op one, 𝟙 _, 𝟙 _, inferInstance, by simp⟩

end Equalizer

section Pullback

variable {A B C : CommRingCat.{u}}

/--
Definition of `pullbackCone` / `pullbackCone` 的定义

English:
definition pullbackCone
  signature: (f : A ⟶ C) (g : B ⟶ C)
  body: PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.

中文:
定义 pullbackCone
  签名: (f : A ⟶ C) (g : B ⟶ C)
  定义体: PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, PullbackCone, PullbackCone.mk, RingHom, RingHom.eqLocus, RingHom.fst, RingHom.snd, eqLocus, f.hom.comp, g.hom.comp, subtype
-/
def pullbackCone (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
  PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (by
      ext ⟨x, e⟩
      simpa [CommRingCat.ofHom] using e)

/--
Definition of `pullbackConeIsLimit` / `pullbackConeIsLimit` 的定义

English:
definition pullbackConeIsLimit
  signature: (f : A ⟶ C) (g : B ⟶ C)
  body: by
  fapply PullbackCone.IsLimit.mk
  · intro s
    refine ofHom ((s.fst.hom.prod s.snd.hom).codRestrict _ ?_)
    intro x
    exact congr_arg (fun f : s.pt ->+* C => f x) (congrArg Hom.hom s.condition)
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
refine hom_ext Ri

中文:
定义 pullbackConeIsLimit
  签名: (f : A ⟶ C) (g : B ⟶ C)
  定义体: by
  fapply PullbackCone.IsLimit.mk
  · intro s
    refine ofHom ((s.fst.hom.prod s.snd.hom).codRestrict _ ?_)
    intro x
    exact congr_arg (fun f : s.pt ->+* C => f x) (congrArg Hom.hom s.condition)
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
refine hom_ext Ri

Depends on / 依赖: Hom.hom, IsLimit, PullbackCone, PullbackCone.IsLimit.mk, RingHom, RingHom.ext, Subtype, Subtype.ext, codRestrict, condition, congr_arg, fapply, hom_ext, s.condition, s.fst.hom.prod, s.pt, s.snd.hom
-/
def pullbackConeIsLimit (f : A ⟶ C) (g : B ⟶ C) :
    IsLimit (pullbackCone f g) := by
  fapply PullbackCone.IsLimit.mk
  · intro s
    refine ofHom ((s.fst.hom.prod s.snd.hom).codRestrict _ ?_)
    intro x
    exact congr_arg (fun f : s.pt ->+* C => f x) (congrArg Hom.hom s.condition)
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
refine hom_ext RingHom.ext fun (x : s.pt) => Subtype.ext ?_
    change (m x).1 = (_, _)
    have eq1 := (congr_arg (fun f : s.pt ->+* A => f x) (congrArg Hom.hom e₁) :)
    have eq2 := (congr_arg (fun f : s.pt ->+* B => f x) (congrArg Hom.hom e₂) :)
    rw [← eq1]; rw [← eq2]
    rfl

open WalkingCospan

/--
Instance `pullbackFst_isLocalHom` / 实例 `pullbackFst_isLocalHom`

English:
instance pullbackFst_isLocalHom
  signature: (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom]
  body: by
  refine Limits.π_isLocalHom _ (limit.isLimit _) left fun x hx i => ?_
  rcases i with _ | _ | _
  · exact ⟨one, 𝟙 _, Hom.inl, inferInstance, by simp; rfl⟩
  · exact ⟨left, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, Hom.inr, Hom.inl, ‹_›, ?_⟩
.symm exact DFunLike.congr_fun (congr(Hom.hom 

中文:
实例 pullbackFst_isLocalHom
  签名: (f : A ⟶ C) (g : B ⟶ C) [是Local态射 g.hom]
  定义体: by
  refine Limits.π_isLocalHom _ (limit.isLimit _) left fun x hx i => ?_
  rcases i with _ | _ | _
  · exact ⟨one, 𝟙 _, Hom.inl, inferInstance, by simp; rfl⟩
  · exact ⟨left, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, Hom.inr, Hom.inl, ‹_›, ?_⟩
.symm exact DFunLike.congr_fun (congr(Hom.hom 

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Hom.hom, Hom.inl, Hom.inr, Limits, condition, congr_fun, isLimit, limit.isLimit, pullback, pullback.condition
-/
instance pullbackFst_isLocalHom (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] :
    IsLocalHom (pullback.fst f g).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) left fun x hx i => ?_
  rcases i with _ | _ | _
  · exact ⟨one, 𝟙 _, Hom.inl, inferInstance, by simp; rfl⟩
  · exact ⟨left, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, Hom.inr, Hom.inl, ‹_›, ?_⟩
.symm exact DFunLike.congr_fun (congr(Hom.hom $(pullback.condition (f := f) (g := g)))) x

/--
theorem `pullback_isLocalRing` / 定理 `pullback_isLocalRing`

English:
theorem pullback_isLocalRing
  given: (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] [IsLocalRing A]
  proof: RingHom.domain_isLocalRing (pullback.fst f g).hom

中文:
定理 pullback_isLocalRing
  条件: (f : A ⟶ C) (g : B ⟶ C) [是Local态射 g.hom] [是局部环 A]
  证明: RingHom.domain_isLocalRing (pullback.fst f g).hom

Depends on / 依赖: RingHom, RingHom.domain_isLocalRing, domain_isLocalRing, pullback, pullback.fst
-/
theorem pullback_isLocalRing (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] [IsLocalRing A] :
    IsLocalRing ↑(pullback f g) :=
  RingHom.domain_isLocalRing (pullback.fst f g).hom

end Pullback

end CommRingCat
