/-
Copyright (c) 2024 Qi Ge, Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Ge, Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.LinearAlgebra
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Underlying topological space of fibre product of schemes

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes. In this file we describe the underlying
topological space of `pullback f g`, i.e. the fiber product `X ×[S] Y`.

## Main results

- `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`: The bijective correspondence between the points
  of `X ×[S] Y` and pairs `(z, p)` of triples `z = (x, y, s)` with `f x = s = g y` and
  prime ideals `q` of `κ(x) ⊗[κ(s)] κ(y)`.
- `AlgebraicGeometry.Scheme.Pullback.exists_preimage`: For every triple `(x, y, s)` with
  `f x = s = g y`, there exists `z : X ×[S] Y` lying above `x` and `y`.

We also give the ranges of `pullback.fst`, `pullback.snd` and `pullback.map`.

-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace IsLocalRing TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/--
Definition of `Triplet` / `Triplet` 的定义

English:
structure Triplet
  parameters: {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  axioms and operations (5):
    - x : X
    - y : Y
    - s : S
    - hx : f x = s
    - hy : g y = s

中文:
结构 Triplet
  参数: {X Y S : 概形.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  公理与运算 (5 个):
    - x : X
    - y : Y
    - s : S
    - hx : f x = s
    - hy : g y = s
-/
structure Triplet {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) where
  /-- The point of `X`. -/
  x : X
  /-- The point of `Y`. -/
  y : Y
  /-- The point of `S` below `x` and `y`. -/
  s : S
  hx : f x = s
  hy : g y = s

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace Triplet

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {t₁ t₂ : Triplet f g} (ex : t₁.x = t₂.x) (ey : t₁.y = t₂.y)
  statement: t₁ = t₂
  proof: by
  cases t₁; cases t₂; simp; aesop

中文:
引理 ext
  条件: {t₁ t₂ : Triplet f g} (ex : t₁.x = t₂.x) (ey : t₁.y = t₂.y)
  结论: t₁ = t₂
  证明: by
  cases t₁; cases t₂; simp; aesop
-/
protected lemma ext {t₁ t₂ : Triplet f g} (ex : t₁.x = t₂.x) (ey : t₁.y = t₂.y) : t₁ = t₂ := by
  cases t₁; cases t₂; simp; aesop

/-- Make a triplet from `x : X` and `y : Y` such that `f x = g y`. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (x : X) (y : Y) (h : f x = g y)
  body: x
  y := y
  s := g y
  hx := h
  hy := rfl

中文:
定义 mk'
  签名: (x : X) (y : Y) (h : f x = g y)
  定义体: x
  y := y
  s := g y
  hx := h
  hy := rfl
-/
def mk' (x : X) (y : Y) (h : f x = g y) : Triplet f g where
  x := x
  y := y
  s := g y
  hx := h
  hy := rfl

/--
Definition of `tensor` / `tensor` 的定义

English:
definition tensor
  signature: (T : Triplet f g)
  body: pushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)

中文:
定义 tensor
  签名: (T : Triplet f g)
  定义体: pushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)

Depends on / 依赖: S.residueFieldCongr, T.hx, T.hy, f.residueFieldMap, g.residueFieldMap, pushout, residueFieldCongr, residueFieldMap
-/
def tensor (T : Triplet f g) : CommRingCat :=
  pushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)

instance (T : Triplet f g) : Nontrivial T.tensor :=
  CommRingCat.nontrivial_of_isPushout_of_isField (Field.toIsField _)
    (IsPushout.of_hasPushout _ _)

/--
Definition of `tensorInl` / `tensorInl` 的定义

English:
definition tensorInl
  signature: (T : Triplet f g)
  body: pushout.inl _ _

中文:
定义 tensorInl
  签名: (T : Triplet f g)
  定义体: pushout.inl _ _

Depends on / 依赖: pushout, pushout.inl
-/
def tensorInl (T : Triplet f g) : X.residueField T.x ⟶ T.tensor := pushout.inl _ _

/--
Definition of `tensorInr` / `tensorInr` 的定义

English:
definition tensorInr
  signature: (T : Triplet f g)
  body: pushout.inr _ _

中文:
定义 tensorInr
  签名: (T : Triplet f g)
  定义体: pushout.inr _ _

Depends on / 依赖: pushout, pushout.inr
-/
def tensorInr (T : Triplet f g) : Y.residueField T.y ⟶ T.tensor := pushout.inr _ _

/--
lemma `isPullback_SpecMap_tensor` / 引理 `isPullback_SpecMap_tensor`

English:
lemma isPullback_SpecMap_tensor
  given: (T : Triplet f g)
  statement: CategoryTheory.IsPullback
  proof: isPullback_SpecMap_pushout _ _

中文:
引理 isPullback_SpecMap_tensor
  条件: (T : Triplet f g)
  结论: 范畴论.是拉回
  证明: isPullback_SpecMap_pushout _ _

Depends on / 依赖: isPullback_SpecMap_pushout
-/
lemma isPullback_SpecMap_tensor (T : Triplet f g) : CategoryTheory.IsPullback
    (Spec.map T.tensorInl) (Spec.map T.tensorInr)
        (Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x))
          (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
  isPullback_SpecMap_pushout _ _

section Congr

/--
Definition of `tensorCongr` / `tensorCongr` 的定义

English:
definition tensorCongr
  signature: {T₁ T₂ : Triplet f g} (e : T₁ = T₂)
  body: eqToIso (by subst e; rfl)

@[simp]

中文:
定义 tensorCongr
  签名: {T₁ T₂ : Triplet f g} (e : T₁ = T₂)
  定义体: eqToIso (by subst e; rfl)

@[simp]

Depends on / 依赖: eqToIso
-/
def tensorCongr {T₁ T₂ : Triplet f g} (e : T₁ = T₂) :
    T₁.tensor ≅ T₂.tensor :=
  eqToIso (by subst e; rfl)

@[simp]
/--
lemma `tensorCongr_refl` / 引理 `tensorCongr_refl`

English:
lemma tensorCongr_refl
  given: {x : Triplet f g}
  proof: rfl

@[simp]

中文:
引理 tensorCongr_refl
  条件: {x : Triplet f g}
  证明: rfl

@[simp]
-/
lemma tensorCongr_refl {x : Triplet f g} :
    tensorCongr (refl x) = Iso.refl _ := rfl

@[simp]
/--
lemma `tensorCongr_symm` / 引理 `tensorCongr_symm`

English:
lemma tensorCongr_symm
  given: {x y : Triplet f g} (e : x = y)
  proof: rfl

@[simp]

中文:
引理 tensorCongr_symm
  条件: {x y : Triplet f g} (e : x = y)
  证明: rfl

@[simp]
-/
lemma tensorCongr_symm {x y : Triplet f g} (e : x = y) :
    (tensorCongr e).symm = tensorCongr e.symm := rfl

@[simp]
/--
lemma `tensorCongr_inv` / 引理 `tensorCongr_inv`

English:
lemma tensorCongr_inv
  given: {x y : Triplet f g} (e : x = y)
  proof: rfl

@[simp]

中文:
引理 tensorCongr_inv
  条件: {x y : Triplet f g} (e : x = y)
  证明: rfl

@[simp]
-/
lemma tensorCongr_inv {x y : Triplet f g} (e : x = y) :
    (tensorCongr e).inv = (tensorCongr e.symm).hom := rfl

@[simp]
/--
lemma `tensorCongr_trans` / 引理 `tensorCongr_trans`

English:
lemma tensorCongr_trans
  given: {x y z : Triplet f g} (e : x = y) (e' : y = z)
  proof: by
  subst e e'
  rfl

@[reassoc (attr := simp)]

中文:
引理 tensorCongr_trans
  条件: {x y z : Triplet f g} (e : x = y) (e' : y = z)
  证明: by
  subst e e'
  rfl

@[reassoc (attr := simp)]
-/
lemma tensorCongr_trans {x y z : Triplet f g} (e : x = y) (e' : y = z) :
    tensorCongr e ≪≫ tensorCongr e' =
      tensorCongr (e.trans e') := by
  subst e e'
  rfl

@[reassoc (attr := simp)]
/--
lemma `tensorCongr_trans_hom` / 引理 `tensorCongr_trans_hom`

English:
lemma tensorCongr_trans_hom
  given: {x y z : Triplet f g} (e : x = y) (e' : y = z)
  proof: by
  subst e e'
  rfl

中文:
引理 tensorCongr_trans_hom
  条件: {x y z : Triplet f g} (e : x = y) (e' : y = z)
  证明: by
  subst e e'
  rfl
-/
lemma tensorCongr_trans_hom {x y z : Triplet f g} (e : x = y) (e' : y = z) :
    (tensorCongr e).hom ≫ (tensorCongr e').hom =
      (tensorCongr (e.trans e')).hom := by
  subst e e'
  rfl

end Congr

variable (T : Triplet f g)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `SpecMap_tensorInl_fromSpecResidueField` / 引理 `SpecMap_tensorInl_fromSpecResidueField`

English:
lemma SpecMap_tensorInl_fromSpecResidueField
  proof: by
  simp only [residueFieldCongr_inv, Category.assoc, tensorInl, tensorInr,
    ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← residueFieldCongr_fromSpecResidueField T.hx.symm]; rw [← residueFieldCongr_fromSpecResidueField T.hy.symm]
  simp only [← Category.assoc, ← Spec.map_comp, pushout.condition]

中文:
引理 SpecMap_tensorInl_fromSpecResidueField
  证明: by
  simp only [residueFieldCongr_inv, Category.assoc, tensorInl, tensorInr,
    ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← residueFieldCongr_fromSpecResidueField T.hx.symm]; rw [← residueFieldCongr_fromSpecResidueField T.hy.symm]
  simp only [← Category.assoc, ← Spec.map_comp, pushout.condition]

Depends on / 依赖: Category, Category.assoc, Hom.SpecMap_residueFieldMap_fromSpecResidueField, Spec.map_comp, SpecMap_residueFieldMap_fromSpecResidueField, T.hx.symm, T.hy.symm, condition, map_comp, pushout, pushout.condition, residueFieldCongr_fromSpecResidueField, residueFieldCongr_inv, tensorInl, tensorInr
-/
lemma SpecMap_tensorInl_fromSpecResidueField :
    (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x) ≫ f =
      (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y) ≫ g := by
  simp only [residueFieldCongr_inv, Category.assoc, tensorInl, tensorInr,
    ← Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← residueFieldCongr_fromSpecResidueField T.hx.symm]; rw [← residueFieldCongr_fromSpecResidueField T.hy.symm]
  simp only [← Category.assoc, ← Spec.map_comp, pushout.condition]

/--
Definition of `SpecTensorTo` / `SpecTensorTo` 的定义

English:
definition SpecTensorTo
  signature: : Spec T.tensor ⟶ pullback f g
  body: pullback.lift (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x)
    (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y)
    (SpecMap_tensorInl_fromSpecResidueField _)

中文:
定义 SpecTensorTo
  签名: : Spec T.tensor ⟶ pullback f g
  定义体: pullback.lift (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x)
    (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y)
    (SpecMap_tensorInl_fromSpecResidueField _)

Depends on / 依赖: Spec.map, SpecMap_tensorInl_fromSpecResidueField, T.tensorInl, T.tensorInr, X.fromSpecResidueField, Y.fromSpecResidueField, fromSpecResidueField, pullback, pullback.lift, tensorInl, tensorInr
-/
def SpecTensorTo : Spec T.tensor ⟶ pullback f g :=
  pullback.lift (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x)
    (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y)
    (SpecMap_tensorInl_fromSpecResidueField _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `fst_SpecTensorTo_apply` / 引理 `fst_SpecTensorTo_apply`

English:
lemma fst_SpecTensorTo_apply
  given: (p : Spec T.tensor)
  proof: by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

中文:
引理 fst_SpecTensorTo_apply
  条件: (p : Spec T.tensor)
  证明: by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, SpecTensorTo, comp_apply
-/
lemma fst_SpecTensorTo_apply (p : Spec T.tensor) :
    pullback.fst f g (T.SpecTensorTo p) = T.x := by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `snd_SpecTensorTo_apply` / 引理 `snd_SpecTensorTo_apply`

English:
lemma snd_SpecTensorTo_apply
  given: (p : Spec T.tensor)
  proof: by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

@[reassoc (attr := simp)]

中文:
引理 snd_SpecTensorTo_apply
  条件: (p : Spec T.tensor)
  证明: by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, SpecTensorTo, comp_apply
-/
lemma snd_SpecTensorTo_apply (p : Spec T.tensor) :
    pullback.snd f g (T.SpecTensorTo p) = T.y := by
  simp only [SpecTensorTo]
  rw [← Scheme.Hom.comp_apply]
  simp

@[reassoc (attr := simp)]
/--
lemma `specTensorTo_fst` / 引理 `specTensorTo_fst`

English:
lemma specTensorTo_fst
  proof: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

中文:
引理 specTensorTo_fst
  证明: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
lemma specTensorTo_fst :
    T.SpecTensorTo ≫ pullback.fst f g = Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/--
lemma `specTensorTo_snd` / 引理 `specTensorTo_snd`

English:
lemma specTensorTo_snd
  proof: pullback.lift_snd _ _ _

中文:
引理 specTensorTo_snd
  证明: pullback.lift_snd _ _ _

Depends on / 依赖: lift_snd, pullback, pullback.lift_snd
-/
lemma specTensorTo_snd :
    T.SpecTensorTo ≫ pullback.snd f g = Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y :=
  pullback.lift_snd _ _ _

/-- Given `t : X ×[S] Y`, it maps to `X` and `Y` with same image in `S`, yielding a
`Triplet f g`. -/
@[simps]
/--
Definition of `ofPoint` / `ofPoint` 的定义

English:
definition ofPoint
  signature: (t : ↑(pullback f g))
  body: ⟨pullback.fst f g t, pullback.snd f g t, _, rfl,
    congr($(pullback.condition (f := f) (g := g)) t).symm⟩

@[simp]

中文:
定义 ofPoint
  签名: (t : ↑(pullback f g))
  定义体: ⟨pullback.fst f g t, pullback.snd f g t, _, rfl,
    congr($(pullback.condition (f := f) (g := g)) t).symm⟩

@[simp]

Depends on / 依赖: condition, pullback, pullback.condition, pullback.fst, pullback.snd
-/
def ofPoint (t : ↑(pullback f g)) : Triplet f g :=
  ⟨pullback.fst f g t, pullback.snd f g t, _, rfl,
    congr($(pullback.condition (f := f) (g := g)) t).symm⟩

@[simp]
/--
lemma `ofPoint_SpecTensorTo` / 引理 `ofPoint_SpecTensorTo`

English:
lemma ofPoint_SpecTensorTo
  given: (T : Triplet f g) (p : Spec T.tensor)
  proof: by
  ext <;> simp

中文:
引理 ofPoint_SpecTensorTo
  条件: (T : Triplet f g) (p : Spec T.tensor)
  证明: by
  ext <;> simp
-/
lemma ofPoint_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    ofPoint (T.SpecTensorTo p) = T := by
  ext <;> simp

end Triplet

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `residueFieldCongr_inv_residueFieldMap_ofPoint` / 引理 `residueFieldCongr_inv_residueFieldMap_ofPoint`

English:
lemma residueFieldCongr_inv_residueFieldMap_ofPoint
  given: (t : ↑(pullback f g))
  proof: by
  simp [← residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr pullback.condition]

中文:
引理 residueFieldCongr_inv_residueFieldMap_ofPoint
  条件: (t : ↑(pullback f g))
  证明: by
  simp [← residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr pullback.condition]

Depends on / 依赖: Scheme, Scheme.Hom.residueFieldMap_congr, condition, pullback, pullback.condition, residueFieldMap_comp, residueFieldMap_congr
-/
lemma residueFieldCongr_inv_residueFieldMap_ofPoint (t : ↑(pullback f g)) :
    ((S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫ f.residueFieldMap (Triplet.ofPoint t).x) ≫
      (pullback.fst f g).residueFieldMap t = ((S.residueFieldCongr (Triplet.ofPoint t).hy).inv ≫
          g.residueFieldMap (Triplet.ofPoint t).y) ≫ (pullback.snd f g).residueFieldMap t := by
  simp [← residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr pullback.condition]

/--
Definition of `ofPointTensor` / `ofPointTensor` 的定义

English:
definition ofPointTensor
  signature: (t : ↑(pullback f g))
  body: pushout.desc
    ((pullback.fst f g).residueFieldMap t)
    ((pullback.snd f g).residueFieldMap t)
    (residueFieldCongr_inv_residueFieldMap_ofPoint t)

中文:
定义 ofPointTensor
  签名: (t : ↑(pullback f g))
  定义体: pushout.desc
    ((pullback.fst f g).residueFieldMap t)
    ((pullback.snd f g).residueFieldMap t)
    (residueFieldCongr_inv_residueFieldMap_ofPoint t)

Depends on / 依赖: pullback, pullback.fst, pullback.snd, pushout, pushout.desc, residueFieldCongr_inv_residueFieldMap_ofPoint, residueFieldMap
-/
def ofPointTensor (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).tensor ⟶ (pullback f g).residueField t :=
  pushout.desc
    ((pullback.fst f g).residueFieldMap t)
    ((pullback.snd f g).residueFieldMap t)
    (residueFieldCongr_inv_residueFieldMap_ofPoint t)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ofPointTensor_SpecTensorTo` / 引理 `ofPointTensor_SpecTensorTo`

English:
lemma ofPointTensor_SpecTensorTo
  given: (t : ↑(pullback f g))
  proof: by
  apply pullback.hom_ext
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_fst]
    rw [← pushout.inl_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t)]; rw [Spec.map_comp]
    rfl
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_snd]
    rw [← pushout.inr_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t)]; rw [Spec.map_comp]
    rfl

中文:
引理 ofPointTensor_SpecTensorTo
  条件: (t : ↑(pullback f g))
  证明: by
  apply pullback.hom_ext
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_fst]
    rw [← pushout.inl_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t)]; rw [Spec.map_comp]
    rfl
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_snd]
    rw [← pushout.inr_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t)]; rw [Spec.map_comp]
    rfl

Depends on / 依赖: Category, Category.assoc, Scheme, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Spec.map_comp, SpecMap_residueFieldMap_fromSpecResidueField, Triplet, Triplet.specTensorTo_fst, Triplet.specTensorTo_snd, hom_ext, inl_desc, inr_desc, map_comp, pullback, pullback.hom_ext, pushout, pushout.inl_desc, pushout.inr_desc, residueFieldCongr_inv_residueFieldMap_ofPoint, specTensorTo_fst
-/
lemma ofPointTensor_SpecTensorTo (t : ↑(pullback f g)) :
    Spec.map (ofPointTensor t) ≫ (Triplet.ofPoint t).SpecTensorTo =
      (pullback f g).fromSpecResidueField t := by
  apply pullback.hom_ext
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_fst]
    rw [← pushout.inl_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t)]; rw [Spec.map_comp]
    rfl
  · rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp only [Category.assoc, Triplet.specTensorTo_snd]
    rw [← pushout.inr_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint t)]; rw [Spec.map_comp]
    rfl

/--
Definition of `SpecOfPoint` / `SpecOfPoint` 的定义

English:
definition SpecOfPoint
  signature: (t : ↑(pullback f g))
  body: Spec.map (ofPointTensor t) (⊥ : PrimeSpectrum _)

中文:
定义 SpecOfPoint
  签名: (t : ↑(pullback f g))
  定义体: Spec.map (ofPointTensor t) (⊥ : PrimeSpectrum _)

Depends on / 依赖: PrimeSpectrum, Spec.map, ofPointTensor
-/
def SpecOfPoint (t : ↑(pullback f g)) : Spec (Triplet.ofPoint t).tensor :=
    Spec.map (ofPointTensor t) (⊥ : PrimeSpectrum _)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `SpecTensorTo_SpecOfPoint` / 引理 `SpecTensorTo_SpecOfPoint`

English:
lemma SpecTensorTo_SpecOfPoint
  given: (t : ↑(pullback f g))
  proof: by
  simp [SpecOfPoint, ← Scheme.Hom.comp_apply, ofPointTensor_SpecTensorTo]

@[reassoc (attr := simp)]

中文:
引理 SpecTensorTo_SpecOfPoint
  条件: (t : ↑(pullback f g))
  证明: by
  simp [SpecOfPoint, ← Scheme.Hom.comp_apply, ofPointTensor_SpecTensorTo]

@[reassoc (attr := simp)]

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, SpecOfPoint, comp_apply, ofPointTensor_SpecTensorTo
-/
lemma SpecTensorTo_SpecOfPoint (t : ↑(pullback f g)) :
    (Triplet.ofPoint t).SpecTensorTo (SpecOfPoint t) = t := by
  simp [SpecOfPoint, ← Scheme.Hom.comp_apply, ofPointTensor_SpecTensorTo]

@[reassoc (attr := simp)]
/--
lemma `tensorCongr_SpecTensorTo` / 引理 `tensorCongr_SpecTensorTo`

English:
lemma tensorCongr_SpecTensorTo
  given: {T T' : Triplet f g} (h : T = T')
  proof: by
  subst h
  simp only [Triplet.tensorCongr_refl, Iso.refl_hom, Spec.map_id, Category.id_comp]

中文:
引理 tensorCongr_SpecTensorTo
  条件: {T T' : Triplet f g} (h : T = T')
  证明: by
  subst h
  simp only [Triplet.tensorCongr_refl, Iso.refl_hom, Spec.map_id, Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, Iso.refl_hom, Spec.map_id, Triplet, Triplet.tensorCongr_refl, id_comp, map_id, refl_hom, tensorCongr_refl
-/
lemma tensorCongr_SpecTensorTo {T T' : Triplet f g} (h : T = T') :
    Spec.map (Triplet.tensorCongr h).hom ≫ T.SpecTensorTo = T'.SpecTensorTo := by
  subst h
  simp only [Triplet.tensorCongr_refl, Iso.refl_hom, Spec.map_id, Category.id_comp]

/--
lemma `Triplet.Spec_ofPointTensor_SpecTensorTo` / 引理 `Triplet.Spec_ofPointTensor_SpecTensorTo`

English:
lemma Triplet.Spec_ofPointTensor_SpecTensorTo
  given: (T : Triplet f g) (p : Spec T.tensor)
  proof: by
  apply T.isPullback_SpecMap_tensor.hom_ext
  · rw [← cancel_mono <| X.fromSpecResidueField T.x]
    simp_rw [Category.assoc, ← T.specTensorTo_fst, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]; rw [ofPointTensor_SpecTensorTo_assoc]
  · rw [← cancel_mono <| Y.fromSpecResidueField T.y]
    simp_rw [Category.assoc, ← T.specTensorTo_snd, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]; rw [ofPointTensor_SpecTensorTo_assoc]

中文:
引理 Triplet.Spec_ofPointTensor_SpecTensorTo
  条件: (T : Triplet f g) (p : Spec T.tensor)
  证明: by
  apply T.isPullback_SpecMap_tensor.hom_ext
  · rw [← cancel_mono <| X.fromSpecResidueField T.x]
    simp_rw [Category.assoc, ← T.specTensorTo_fst, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]; rw [ofPointTensor_SpecTensorTo_assoc]
  · rw [← cancel_mono <| Y.fromSpecResidueField T.y]
    simp_rw [Category.assoc, ← T.specTensorTo_snd, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]; rw [ofPointTensor_SpecTensorTo_assoc]

Depends on / 依赖: Category, Category.assoc, Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, SpecMap_residueFieldMap_fromSpecResidueField_assoc, T.isPullback_SpecMap_tensor.hom_ext, T.specTensorTo_fst, T.specTensorTo_snd, X.fromSpecResidueField, Y.fromSpecResidueField, cancel_mono, fromSpecResidueField, hom_ext, isPullback_SpecMap_tensor, isRegular, ofPointTensor_SpecTensorTo_, ofPointTensor_SpecTensorTo_assoc, simp_rw, specTensorTo_fst, specTensorTo_snd, tensorCongr_SpecTensorTo_assoc
-/
lemma Triplet.Spec_ofPointTensor_SpecTensorTo (T : Triplet f g) (p : Spec T.tensor) :
    Spec.map (Hom.residueFieldMap T.SpecTensorTo p) ≫
      Spec.map (ofPointTensor (T.SpecTensorTo p)) ≫
      Spec.map (tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom =
    (Spec T.tensor).fromSpecResidueField p := by
  apply T.isPullback_SpecMap_tensor.hom_ext
  · rw [← cancel_mono <| X.fromSpecResidueField T.x]
    simp_rw [Category.assoc, ← T.specTensorTo_fst, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]; rw [ofPointTensor_SpecTensorTo_assoc]
  · rw [← cancel_mono <| Y.fromSpecResidueField T.y]
    simp_rw [Category.assoc, ← T.specTensorTo_snd, tensorCongr_SpecTensorTo_assoc]
    rw [← Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]; rw [ofPointTensor_SpecTensorTo_assoc]

/--
lemma `carrierEquiv_eq_iff` / 引理 `carrierEquiv_eq_iff`

English:
lemma carrierEquiv_eq_iff
  given: {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor}
  proof: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨T, _⟩ := T₁
    obtain ⟨T', _⟩ := T₂
    rintro ⟨rfl : T = T', e⟩
    simpa [e]

中文:
引理 carrierEquiv_eq_iff
  条件: {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor}
  证明: by
  constructor
  · rintro rfl
    simp
  · obtain ⟨T, _⟩ := T₁
    obtain ⟨T', _⟩ := T₂
    rintro ⟨rfl : T = T', e⟩
    simpa [e]

Depends on / 依赖: Fin.castSucc_eq_zero_iff, Fin.castSucc_zero, Fin.ext_iff, Fin.succ, IsIndex, castSucc_eq_zero_iff, castSucc_zero, ext_iff, hs.simplex_fst_castSucc, i.zero_le, isIndex, mem_range_left, monotone_apply, ne_last, pairingCore, s.hd, s.index, s.isIndex, s.x.cast, simplex
-/
lemma carrierEquiv_eq_iff {T₁ T₂ : Σ T : Triplet f g, Spec T.tensor} :
    T₁ = T₂ ↔ exists e : T₁.1 = T₂.1, Spec.map (Triplet.tensorCongr e).inv T₁.2 = T₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨T, _⟩ := T₁
    obtain ⟨T', _⟩ := T₂
    rintro ⟨rfl : T = T', e⟩
    simpa [e]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `carrierEquiv` / `carrierEquiv` 的定义

English:
definition carrierEquiv
  signature: : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where
  body: ⟨.ofPoint t, SpecOfPoint t⟩
  invFun T := T.1.SpecTensorTo T.2
  left_inv := SpecTensorTo_SpecOfPoint
  right_inv := by
    intro ⟨T, p⟩
    apply carrierEquiv_eq_iff.mpr
    use T.ofPoint_SpecTensorTo p
    have : Spec.map (Hom.residueFieldMap T.SpecTensorTo p) (⊥ : PrimeSpectrum _) =
        (⊥ : PrimeSpectrum _) :=
      (PrimeSpectrum.instUnique).uniq _
    simp only [SpecOfPoint, Triplet.tensorCongr_inv, ← this, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply]
    simp [Triplet.Spec_ofPointTensor_SpecTensorTo]

中文:
定义 carrierEquiv
  签名: : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where
  定义体: ⟨.ofPoint t, SpecOfPoint t⟩
  invFun T := T.1.SpecTensorTo T.2
  left_inv := SpecTensorTo_SpecOfPoint
  right_inv := by
    intro ⟨T, p⟩
    apply carrierEquiv_eq_iff.mpr
    use T.ofPoint_SpecTensorTo p
    have : Spec.map (Hom.residueFieldMap T.SpecTensorTo p) (⊥ : PrimeSpectrum _) =
        (⊥ : PrimeSpectrum _) :=
      (PrimeSpectrum.instUnique).uniq _
    simp only [SpecOfPoint, Triplet.tensorCongr_inv, ← this, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply]
    simp [Triplet.Spec_ofPointTensor_SpecTensorTo]

Depends on / 依赖: SpecOfPoint, ofPoint
-/
def carrierEquiv : ↑(pullback f g) ≃ Σ T : Triplet f g, Spec T.tensor where
  toFun t := ⟨.ofPoint t, SpecOfPoint t⟩
  invFun T := T.1.SpecTensorTo T.2
  left_inv := SpecTensorTo_SpecOfPoint
  right_inv := by
    intro ⟨T, p⟩
    apply carrierEquiv_eq_iff.mpr
    use T.ofPoint_SpecTensorTo p
    have : Spec.map (Hom.residueFieldMap T.SpecTensorTo p) (⊥ : PrimeSpectrum _) =
        (⊥ : PrimeSpectrum _) :=
      (PrimeSpectrum.instUnique).uniq _
    simp only [SpecOfPoint, Triplet.tensorCongr_inv, ← this, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply]
    simp [Triplet.Spec_ofPointTensor_SpecTensorTo]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `carrierEquiv_symm_fst` / 引理 `carrierEquiv_symm_fst`

English:
lemma carrierEquiv_symm_fst
  given: (T : Triplet f g) (p : Spec T.tensor)
  proof: by
  simp [carrierEquiv]

中文:
引理 carrierEquiv_symm_fst
  条件: (T : Triplet f g) (p : Spec T.tensor)
  证明: by
  simp [carrierEquiv]

Depends on / 依赖: carrierEquiv
-/
lemma carrierEquiv_symm_fst (T : Triplet f g) (p : Spec T.tensor) :
    pullback.fst f g (carrierEquiv.symm ⟨T, p⟩) = T.x := by
  simp [carrierEquiv]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `carrierEquiv_symm_snd` / 引理 `carrierEquiv_symm_snd`

English:
lemma carrierEquiv_symm_snd
  given: (T : Triplet f g) (p : Spec T.tensor)
  proof: by
  simp [carrierEquiv]

中文:
引理 carrierEquiv_symm_snd
  条件: (T : Triplet f g) (p : Spec T.tensor)
  证明: by
  simp [carrierEquiv]

Depends on / 依赖: Fin.eq_castSucc_of_ne_last, Fin.last, carrierEquiv, dif_pos, eq_castSucc_of_ne_last, infer_instance, pairing, pairing_castSucc
-/
lemma carrierEquiv_symm_snd (T : Triplet f g) (p : Spec T.tensor) :
    pullback.snd f g (carrierEquiv.symm ⟨T, p⟩) = T.y := by
  simp [carrierEquiv]

/--
lemma `Triplet.exists_preimage` / 引理 `Triplet.exists_preimage`

English:
lemma Triplet.exists_preimage
  given: (T : Triplet f g)
  proof: ⟨carrierEquiv.symm ⟨T, Nonempty.some inferInstance⟩, by simp⟩

中文:
引理 Triplet.存在_preimage
  条件: (T : Triplet f g)
  证明: ⟨carrierEquiv.symm ⟨T, Nonempty.some inferInstance⟩, by simp⟩

Depends on / 依赖: Fin.castSucc_succ, Nonempty, Nonempty.some, carrierEquiv, carrierEquiv.symm, castSucc_succ, infer_instance, pairing_castSucc
-/
lemma Triplet.exists_preimage (T : Triplet f g) :
    exists t : ↑(pullback f g), pullback.fst f g t = T.x ∧ pullback.snd f g t = T.y :=
  ⟨carrierEquiv.symm ⟨T, Nonempty.some inferInstance⟩, by simp⟩

/--
lemma `exists_preimage_pullback` / 引理 `exists_preimage_pullback`

English:
lemma exists_preimage_pullback
  given: (x : X) (y : Y) (h : f x = g y)
  proof: (Pullback.Triplet.mk' x y h).exists_preimage

中文:
引理 存在_preimage_pullback
  条件: (x : X) (y : Y) (h : f x = g y)
  证明: (Pullback.Triplet.mk' x y h).exists_preimage

Depends on / 依赖: Pullback, Pullback.Triplet.mk, Triplet, exists_preimage
-/
lemma exists_preimage_pullback (x : X) (y : Y) (h : f x = g y) :
    exists z : ↑(pullback f g), pullback.fst f g z = x ∧ pullback.snd f g z = y :=
  (Pullback.Triplet.mk' x y h).exists_preimage

/--
lemma `_root_.AlgebraicGeometry.Scheme.isEmpty_pullback_iff` / 引理 `_root_.AlgebraicGeometry.Scheme.isEmpty_pullback_iff`

English:
lemma _root_.AlgebraicGeometry.Scheme.isEmpty_pullback_iff
  given: {f : X ⟶ S} {g : Y ⟶ S}
  proof: by
  refine ⟨?_, Scheme.isEmpty_pullback f g⟩
  rw [Set.disjoint_iff_forall_ne]
  contrapose!
  rintro ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, e⟩
  obtain ⟨z, -⟩ := exists_preimage_pullback x y e
  exact ⟨z⟩

中文:
引理 _root_.AlgebraicGeometry.概形.isEmpty_pullback_iff
  条件: {f : X ⟶ S} {g : Y ⟶ S}
  证明: by
  refine ⟨?_, Scheme.isEmpty_pullback f g⟩
  rw [Set.disjoint_iff_forall_ne]
  contrapose!
  rintro ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, e⟩
  obtain ⟨z, -⟩ := exists_preimage_pullback x y e
  exact ⟨z⟩

Depends on / 依赖: Scheme, Scheme.isEmpty_pullback, Set.disjoint_iff_forall_ne, contrapose, disjoint_iff_forall_ne, exists_preimage_pullback, isEmpty_pullback
-/
lemma _root_.AlgebraicGeometry.Scheme.isEmpty_pullback_iff {f : X ⟶ S} {g : Y ⟶ S} :
    IsEmpty ↑(Limits.pullback f g) ↔ Disjoint (Set.range f) (Set.range g) := by
  refine ⟨?_, Scheme.isEmpty_pullback f g⟩
  rw [Set.disjoint_iff_forall_ne]
  contrapose!
  rintro ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, e⟩
  obtain ⟨z, -⟩ := exists_preimage_pullback x y e
  exact ⟨z⟩

instance (priority := low) [Nonempty X] [Nonempty Y] [Subsingleton S] :
    Nonempty ↑(pullback f g) := by
  have : Nonempty S := .map f ‹_›
  rw [← not_isEmpty_iff]; rw [AlgebraicGeometry.Scheme.isEmpty_pullback_iff]; rw [Set.not_disjoint_iff]
  exact ⟨Nonempty.some ‹_›, Function.surjective_to_subsingleton _ _,
    Function.surjective_to_subsingleton _ _⟩

variable (f g)

/--
lemma `range_fst` / 引理 `range_fst`

English:
lemma range_fst
  statement: Set.range (pullback.fst f g) = f ⁻¹' Set.range g
  proof: by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ => ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' x y hy.symm)
    use a, ha.left

中文:
引理 range_fst
  结论: 集合.range (pullback.fst f g) = f ⁻¹' 集合.range g
  证明: by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ => ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' x y hy.symm)
    use a, ha.left

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, Set.mem_preimage, Set.mem_range, Triplet, Triplet.exists_preimage, Triplet.mk, comp_apply, condition, exists_preimage, ha.left, hy.symm, mem_preimage, mem_range, pullback, pullback.condition
-/
lemma range_fst : Set.range (pullback.fst f g) = f ⁻¹' Set.range g := by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ => ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' x y hy.symm)
    use a, ha.left

/--
lemma `range_snd` / 引理 `range_snd`

English:
lemma range_snd
  statement: Set.range (pullback.snd f g) = g ⁻¹' Set.range f
  proof: by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ => ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, ← pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' y x hy)
    use a, ha.right

中文:
引理 range_snd
  结论: 集合.range (pullback.snd f g) = g ⁻¹' 集合.range f
  证明: by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ => ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, ← pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' y x hy)
    use a, ha.right

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, Set.mem_preimage, Set.mem_range, Triplet, Triplet.exists_preimage, Triplet.mk, comp_apply, condition, exists_preimage, ha.right, mem_preimage, mem_range, pullback, pullback.condition
-/
lemma range_snd : Set.range (pullback.snd f g) = g ⁻¹' Set.range f := by
  ext x
  refine ⟨?_, fun ⟨y, hy⟩ => ?_⟩
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_preimage, Set.mem_range, ← Scheme.Hom.comp_apply, ← pullback.condition]
    simp
  · obtain ⟨a, ha⟩ := Triplet.exists_preimage (Triplet.mk' y x hy)
    use a, ha.right

/--
lemma `range_fst_comp` / 引理 `range_fst_comp`

English:
lemma range_fst_comp
  proof: by
  simp [Set.range_comp, range_fst, Set.image_preimage_eq_range_inter]

中文:
引理 range_fst_comp
  证明: by
  simp [Set.range_comp, range_fst, Set.image_preimage_eq_range_inter]

Depends on / 依赖: Set.image_preimage_eq_range_inter, Set.range_comp, image_preimage_eq_range_inter, range_comp, range_fst
-/
lemma range_fst_comp :
    Set.range (pullback.fst f g ≫ f) = Set.range f inter Set.range g := by
  simp [Set.range_comp, range_fst, Set.image_preimage_eq_range_inter]

/--
lemma `range_snd_comp` / 引理 `range_snd_comp`

English:
lemma range_snd_comp
  proof: by
  rw [← pullback.condition]; rw [range_fst_comp]

中文:
引理 range_snd_comp
  证明: by
  rw [← pullback.condition]; rw [range_fst_comp]

Depends on / 依赖: condition, pullback, pullback.condition, range_fst_comp
-/
lemma range_snd_comp :
    Set.range (pullback.snd f g ≫ g) = Set.range f inter Set.range g := by
  rw [← pullback.condition]; rw [range_fst_comp]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_map` / 引理 `range_map`

English:
lemma range_map
  statement: {X' Y' S' : Scheme.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
  proof: by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · use pullback.fst f g t
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]
      simp
    · use pullback.snd f g t
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]
      simp
  · intro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let T₁ : Triplet (pullback.fst f' g') i₁ := Triplet.mk' z x hx.symm
    obtain ⟨w₁, hw₁⟩ := T₁.exists_preimage
    let T₂ : Triplet (pullback.snd f' g') i₂ := Triplet.mk' z y hy.symm
    obtain ⟨w₂, hw₂⟩ := T₂.exists_preimage
    let T : Triplet (pullback.fst (pullback.fst f' g') i₁) (pullback.fst (pullback.snd f' g') i₂) :=
Triplet.mk' w₁ w₂ by simp [hw₁.left, hw₂.left, T₁, T₂]
    obtain ⟨t, _, ht₂⟩ := T.exists_preimage
    use (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).hom t
    rw [pullback_map_eq_pullbackFstFstIso_inv]; rw [← Scheme.Hom.comp_apply]; rw [Iso.hom_inv_id_assoc]
    simp [ht₂, T, hw₂.left, T₂]

中文:
引理 range_map
  结论: {X' Y' S' : 概形.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
  证明: by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · use pullback.fst f g t
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]
      simp
    · use pullback.snd f g t
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]
      simp
  · intro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let T₁ : Triplet (pullback.fst f' g') i₁ := Triplet.mk' z x hx.symm
    obtain ⟨w₁, hw₁⟩ := T₁.exists_preimage
    let T₂ : Triplet (pullback.snd f' g') i₂ := Triplet.mk' z y hy.symm
    obtain ⟨w₂, hw₂⟩ := T₂.exists_preimage
    let T : Triplet (pullback.fst (pullback.fst f' g') i₁) (pullback.fst (pullback.snd f' g') i₂) :=
Triplet.mk' w₁ w₂ by simp [hw₁.left, hw₂.left, T₁, T₂]
    obtain ⟨t, _, ht₂⟩ := T.exists_preimage
    use (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).hom t
    rw [pullback_map_eq_pullbackFstFstIso_inv]; rw [← Scheme.Hom.comp_apply]; rw [Iso.hom_inv_id_assoc]
    simp [ht₂, T, hw₂.left, T₂]

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, Triplet, Triplet.mk, comp_apply, exists_preimage, hx.symm, hy.symm, pullback, pullback.fst, pullback.snd
-/
lemma range_map {X' Y' S' : Scheme.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) =
      pullback.fst f' g' ⁻¹' Set.range i₁ inter pullback.snd f' g' ⁻¹' Set.range i₂ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · use pullback.fst f g t
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]
      simp
    · use pullback.snd f g t
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]
      simp
  · intro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    let T₁ : Triplet (pullback.fst f' g') i₁ := Triplet.mk' z x hx.symm
    obtain ⟨w₁, hw₁⟩ := T₁.exists_preimage
    let T₂ : Triplet (pullback.snd f' g') i₂ := Triplet.mk' z y hy.symm
    obtain ⟨w₂, hw₂⟩ := T₂.exists_preimage
    let T : Triplet (pullback.fst (pullback.fst f' g') i₁) (pullback.fst (pullback.snd f' g') i₂) :=
Triplet.mk' w₁ w₂ by simp [hw₁.left, hw₂.left, T₁, T₂]
    obtain ⟨t, _, ht₂⟩ := T.exists_preimage
    use (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).hom t
    rw [pullback_map_eq_pullbackFstFstIso_inv]; rw [← Scheme.Hom.comp_apply]; rw [Iso.hom_inv_id_assoc]
    simp [ht₂, T, hw₂.left, T₂]

end Pullback

/--
Instance `isJointlySurjectivePreserving` / 实例 `isJointlySurjectivePreserving`

English:
instance isJointlySurjectivePreserving
  signature: (P : MorphismProperty Scheme.{u})
  body: by
    obtain ⟨a, b, h⟩ := Pullback.exists_preimage_pullback x y hxy
    use a

中文:
实例 isJointlySurjectivePreserving
  签名: (P : MorphismProperty 概形.{u})
  定义体: by
    obtain ⟨a, b, h⟩ := Pullback.exists_preimage_pullback x y hxy
    use a

Depends on / 依赖: Pullback, Pullback.exists_preimage_pullback, exists_preimage_pullback
-/
instance isJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) :
    IsJointlySurjectivePreserving P where
  exists_preimage_fst_triplet_of_prop {X Y S} f g _ hg x y hxy := by
    obtain ⟨a, b, h⟩ := Pullback.exists_preimage_pullback x y hxy
    use a

/--
lemma `pullbackComparison_forget_surjective` / 引理 `pullbackComparison_forget_surjective`

English:
lemma pullbackComparison_forget_surjective
  given: {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  proof: by
refine .of_comp_left (fun x => ?_)
    injective_of_mono (Types.pullbackIsoPullback (forget.map f) (forget.map g)).hom
  obtain ⟨z, h1, h2⟩ := Pullback.exists_preimage_pullback (f := f) (g := g) x.1.1 x.1.2 x.2
  use z
  ext
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_fst]
    rwa [← types_comp_apply (g := pullback.fst _ _), pullbackComparison_comp_fst]
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_snd]
    rwa [← types_comp_apply (g := pullback.snd _ _), pullbackComparison_comp_snd]

中文:
引理 pullbackComparison_forget_surjective
  条件: {X Y S : 概形.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  证明: by
refine .of_comp_left (fun x => ?_)
    injective_of_mono (Types.pullbackIsoPullback (forget.map f) (forget.map g)).hom
  obtain ⟨z, h1, h2⟩ := Pullback.exists_preimage_pullback (f := f) (g := g) x.1.1 x.1.2 x.2
  use z
  ext
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_fst]
    rwa [← types_comp_apply (g := pullback.fst _ _), pullbackComparison_comp_fst]
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_snd]
    rwa [← types_comp_apply (g := pullback.snd _ _), pullbackComparison_comp_snd]

Depends on / 依赖: Function, Function.comp_apply, Pullback, Pullback.exists_preimage_pullback, Types.pullbackIsoPullback, Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_snd, comp_apply, exists_preimage_pullback, forget, forget.map, injective_of_mono, of_comp_left, pullback, pullback.fst, pullback.snd, pullbackCompariso, pullbackComparison_comp_fst, pullbackIsoPullback, pullbackIsoPullback_hom_fst
-/
lemma pullbackComparison_forget_surjective {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Function.Surjective (pullbackComparison forget f g) := by
refine .of_comp_left (fun x => ?_)
    injective_of_mono (Types.pullbackIsoPullback (forget.map f) (forget.map g)).hom
  obtain ⟨z, h1, h2⟩ := Pullback.exists_preimage_pullback (f := f) (g := g) x.1.1 x.1.2 x.2
  use z
  ext
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_fst]
    rwa [← types_comp_apply (g := pullback.fst _ _), pullbackComparison_comp_fst]
  · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_snd]
    rwa [← types_comp_apply (g := pullback.snd _ _), pullbackComparison_comp_snd]

instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Epi (pullbackComparison Scheme.forgetToTop f g) := by
  refine (CategoryTheory.forget TopCat).epi_of_epi_map ?_
  rw [← CategoryTheory.epi_comp_iff_of_isIso _
    (pullbackComparison (CategoryTheory.forget TopCat) (forgetToTop.map f) (forgetToTop.map g))]; rw [← _root_.CategoryTheory.Limits.pullbackComparison_comp]; rw [epi_iff_surjective]
  apply Scheme.pullbackComparison_forget_surjective _ _

/--
lemma `exists_preimage_of_isPullback` / 引理 `exists_preimage_of_isPullback`

English:
lemma exists_preimage_of_isPullback
  statement: {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
  proof: by
  let e := h.isoPullback
  obtain ⟨z, hzl, hzr⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x y hxy
  use h.isoPullback.inv.base z
  simp [← Scheme.Hom.comp_apply, hzl, hzr]

中文:
引理 存在_preimage_of_isPullback
  结论: {P X Y Z : 概形.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
  证明: by
  let e := h.isoPullback
  obtain ⟨z, hzl, hzr⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x y hxy
  use h.isoPullback.inv.base z
  simp [← Scheme.Hom.comp_apply, hzl, hzr]

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback, Pullback, Scheme, Scheme.Hom.comp_apply, comp_apply, exists_preimage_pullback, h.isoPullback, h.isoPullback.inv.base, isoPullback
-/
lemma exists_preimage_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y)
    (hxy : f.base x = g.base y) :
    exists (p : P), fst.base p = x ∧ snd.base p = y := by
  let e := h.isoPullback
  obtain ⟨z, hzl, hzr⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x y hxy
  use h.isoPullback.inv.base z
  simp [← Scheme.Hom.comp_apply, hzl, hzr]

/--
lemma `image_preimage_eq_of_isPullback` / 引理 `image_preimage_eq_of_isPullback`

English:
lemma image_preimage_eq_of_isPullback
  statement: {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
  proof: by
  refine subset_antisymm ?_ (fun x hx => ?_)
  · rw [Set.image_subset_iff, ← Set.preimage_comp, ← TopCat.coe_comp, ← Hom.comp_base, ← h.1.1]
    rw [Hom.comp_base]; rw [TopCat.coe_comp]; rw [← Set.image_subset_iff]; rw [Set.image_comp]
    exact Set.image_mono (Set.image_preimage_subset _ _)
  · obtain ⟨y, hy, heq⟩ := hx
    obtain ⟨o, hl, hr⟩ := exists_preimage_of_isPullback h y x heq
    use o
    simpa [hl, hr]

中文:
引理 image_preimage_eq_of_isPullback
  结论: {P X Y Z : 概形.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
  证明: by
  refine subset_antisymm ?_ (fun x hx => ?_)
  · rw [Set.image_subset_iff, ← Set.preimage_comp, ← TopCat.coe_comp, ← Hom.comp_base, ← h.1.1]
    rw [Hom.comp_base]; rw [TopCat.coe_comp]; rw [← Set.image_subset_iff]; rw [Set.image_comp]
    exact Set.image_mono (Set.image_preimage_subset _ _)
  · obtain ⟨y, hy, heq⟩ := hx
    obtain ⟨o, hl, hr⟩ := exists_preimage_of_isPullback h y x heq
    use o
    simpa [hl, hr]

Depends on / 依赖: Hom.comp_base, Set.image_comp, Set.image_mono, Set.image_preimage_subset, Set.image_subset_iff, Set.preimage_comp, TopCat, TopCat.coe_comp, coe_comp, comp_base, exists_preimage_of_isPullback, image_comp, image_mono, image_preimage_subset, image_subset_iff, preimage_comp, subset_antisymm
-/
lemma image_preimage_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (s : Set X) :
    snd.base '' fst.base ⁻¹' s = g.base ⁻¹' f.base '' s := by
  refine subset_antisymm ?_ (fun x hx => ?_)
  · rw [Set.image_subset_iff, ← Set.preimage_comp, ← TopCat.coe_comp, ← Hom.comp_base, ← h.1.1]
    rw [Hom.comp_base]; rw [TopCat.coe_comp]; rw [← Set.image_subset_iff]; rw [Set.image_comp]
    exact Set.image_mono (Set.image_preimage_subset _ _)
  · obtain ⟨y, hy, heq⟩ := hx
    obtain ⟨o, hl, hr⟩ := exists_preimage_of_isPullback h y x heq
    use o
    simpa [hl, hr]

end Scheme

namespace Surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderBaseChange @Surjective
  body: by
  refine .mk' ?_
  introv hg
  simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
  rw [hg]; rw [Set.preimage_univ]

中文:
实例 :
  签名: MorphismProperty.是StableUnderBaseChange @满射
  定义体: by
  refine .mk' ?_
  introv hg
  simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
  rw [hg]; rw [Set.preimage_univ]

Depends on / 依赖: Pullback, Scheme, Scheme.Pullback.range_fst, Set.preimage_univ, Set.range_eq_univ, introv, preimage_univ, range_eq_univ, range_fst, surjective_iff
-/
instance : MorphismProperty.IsStableUnderBaseChange @Surjective := by
  refine .mk' ?_
  introv hg
  simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
  rw [hg]; rw [Set.preimage_univ]

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective g] :
    Surjective (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective f] :
    Surjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

end AlgebraicGeometry.Surjective
