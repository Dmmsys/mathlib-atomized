/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Functorial constructions of ideal sheaves

We define the pullback and pushforward of ideal sheaves in this file.

## Main definitions
- `AlgebraicGeometry.Scheme.IdealSheafData.comap`: The pullback of an ideal sheaf.
- `AlgebraicGeometry.Scheme.IdealSheafData.map`: The pushforward of an ideal sheaf.
- `AlgebraicGeometry.Scheme.IdealSheafData.map_gc`:
  The Galois connection between pullback and pushforward.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

namespace Scheme.IdealSheafData

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (I : Y.IdealSheafData) (f : X ⟶ Y)
  body: (pullback.fst f I.subschemeι).ker

中文:
定义 comap
  签名: (I : Y.IdealSheafData) (f : X ⟶ Y)
  定义体: (pullback.fst f I.subschemeι).ker

Depends on / 依赖: I.subscheme, pullback, pullback.fst
-/
def comap (I : Y.IdealSheafData) (f : X ⟶ Y) : X.IdealSheafData :=
  (pullback.fst f I.subschemeι).ker

/--
Definition of `comapIso` / `comapIso` 的定义

English:
definition comapIso
  signature: (I : Y.IdealSheafData) (f : X ⟶ Y)
  body: (asIso (pullback.fst f I.subschemeι).toImage).symm

@[reassoc (attr := simp)]

中文:
定义 comapIso
  签名: (I : Y.IdealSheafData) (f : X ⟶ Y)
  定义体: (asIso (pullback.fst f I.subschemeι).toImage).symm

@[reassoc (attr := simp)]

Depends on / 依赖: I.subscheme, pullback, pullback.fst, toImage
-/
def comapIso (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).subscheme ≅ pullback f I.subschemeι :=
  (asIso (pullback.fst f I.subschemeι).toImage).symm

@[reassoc (attr := simp)]
/--
lemma `comapIso_inv_subschemeι` / 引理 `comapIso_inv_subschemeι`

English:
lemma comapIso_inv_subschemeι
  given: (I : Y.IdealSheafData) (f : X ⟶ Y)
  proof: (pullback.fst f I.subschemeι).toImage_imageι

@[reassoc (attr := simp)]

中文:
引理 comapIso_inv_subschemeι
  条件: (I : Y.IdealSheafData) (f : X ⟶ Y)
  证明: (pullback.fst f I.subschemeι).toImage_imageι

@[reassoc (attr := simp)]

Depends on / 依赖: I.subscheme, pullback, pullback.fst
-/
lemma comapIso_inv_subschemeι (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comapIso f).inv ≫ (I.comap f).subschemeι = pullback.fst _ _ :=
  (pullback.fst f I.subschemeι).toImage_imageι

@[reassoc (attr := simp)]
/--
lemma `comapIso_hom_fst` / 引理 `comapIso_hom_fst`

English:
lemma comapIso_hom_fst
  given: (I : Y.IdealSheafData) (f : X ⟶ Y)
  proof: by
  rw [← comapIso_inv_subschemeι]; rw [Iso.hom_inv_id_assoc]

中文:
引理 comapIso_hom_fst
  条件: (I : Y.IdealSheafData) (f : X ⟶ Y)
  证明: by
  rw [← comapIso_inv_subschemeι]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, hom_inv_id_assoc
-/
lemma comapIso_hom_fst (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comapIso f).hom ≫ pullback.fst _ _ = (I.comap f).subschemeι := by
  rw [← comapIso_inv_subschemeι]; rw [Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `comap_comp` / 引理 `comap_comp`

English:
lemma comap_comp
  given: (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  let e : pullback f (I.comap g).subschemeι ≅ pullback (f ≫ g) I.subschemeι :=
    asIso (pullback.map _ _ _ _ (𝟙 _) (I.comapIso g).hom (𝟙 _) (by simp) (by simp)) ≪≫
      pullbackRightPullbackFstIso _ _ _
  rw [comap]; rw [comap]; rw [← Scheme.Hom.ker_comp_of_isIso e.hom]
  simp [e]

@[simp]

中文:
引理 comap_comp
  条件: (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  let e : pullback f (I.comap g).subschemeι ≅ pullback (f ≫ g) I.subschemeι :=
    asIso (pullback.map _ _ _ _ (𝟙 _) (I.comapIso g).hom (𝟙 _) (by simp) (by simp)) ≪≫
      pullbackRightPullbackFstIso _ _ _
  rw [comap]; rw [comap]; rw [← Scheme.Hom.ker_comp_of_isIso e.hom]
  simp [e]

@[simp]

Depends on / 依赖: CosimplicialObject, I.comap, I.comapIso, I.subscheme, Scheme, Scheme.Hom.ker_comp_of_isIso, comapIso, e.hom, infer_instance, ker_comp_of_isIso, pullback, pullback.map, pullbackRightPullbackFstIso
-/
lemma comap_comp (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    I.comap (f ≫ g) = (I.comap g).comap f := by
  let e : pullback f (I.comap g).subschemeι ≅ pullback (f ≫ g) I.subschemeι :=
    asIso (pullback.map _ _ _ _ (𝟙 _) (I.comapIso g).hom (𝟙 _) (by simp) (by simp)) ≪≫
      pullbackRightPullbackFstIso _ _ _
  rw [comap]; rw [comap]; rw [← Scheme.Hom.ker_comp_of_isIso e.hom]
  simp [e]

@[simp]
/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (I : Z.IdealSheafData)
  proof: by
  rw [comap]; rw [← Scheme.Hom.ker_comp_of_isIso (inv (pullback.snd _ _))]; rw [pullback_inv_snd_fst_of_left_isIso]; rw [IsIso.inv_id]; rw [Category.comp_id]; rw [ker_subschemeι]

@[simp]

中文:
引理 comap_id
  条件: (I : Z.IdealSheafData)
  证明: by
  rw [comap]; rw [← Scheme.Hom.ker_comp_of_isIso (inv (pullback.snd _ _))]; rw [pullback_inv_snd_fst_of_left_isIso]; rw [IsIso.inv_id]; rw [Category.comp_id]; rw [ker_subschemeι]

@[simp]

Depends on / 依赖: Category, Category.comp_id, IsIso.inv_id, Scheme, Scheme.Hom.ker_comp_of_isIso, comp_id, inv_id, ker_comp_of_isIso, pullback, pullback.snd, pullback_inv_snd_fst_of_left_isIso
-/
lemma comap_id (I : Z.IdealSheafData) :
    I.comap (𝟙 _) = I := by
  rw [comap]; rw [← Scheme.Hom.ker_comp_of_isIso (inv (pullback.snd _ _))]; rw [pullback_inv_snd_fst_of_left_isIso]; rw [IsIso.inv_id]; rw [Category.comp_id]; rw [ker_subschemeι]

@[simp]
/--
lemma `support_comap` / 引理 `support_comap`

English:
lemma support_comap
  given: (I : Y.IdealSheafData) (f : X ⟶ Y)
  proof: by
  ext1
  rw [comap]; rw [Scheme.Hom.support_ker]; rw [Pullback.range_fst]; rw [range_subschemeι]; rw [TopologicalSpace.Closeds.coe_preimage]; rw [(I.support.isClosed.preimage f.continuous).closure_eq]

中文:
引理 support_comap
  条件: (I : Y.IdealSheafData) (f : X ⟶ Y)
  证明: by
  ext1
  rw [comap]; rw [Scheme.Hom.support_ker]; rw [Pullback.range_fst]; rw [range_subschemeι]; rw [TopologicalSpace.Closeds.coe_preimage]; rw [(I.support.isClosed.preimage f.continuous).closure_eq]

Depends on / 依赖: Closeds, CosimplicialObject, I.support.isClosed.preimage, Pullback, Pullback.range_fst, Scheme, Scheme.Hom.support_ker, TopologicalSpace, TopologicalSpace.Closeds.coe_preimage, closure_eq, coe_preimage, continuous, f.continuous, infer_instance, isClosed, preimage, range_fst, support, support_ker
-/
lemma support_comap (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).support = I.support.preimage f.continuous := by
  ext1
  rw [comap]; rw [Scheme.Hom.support_ker]; rw [Pullback.range_fst]; rw [range_subschemeι]; rw [TopologicalSpace.Closeds.coe_preimage]; rw [(I.support.isClosed.preimage f.continuous).closure_eq]

/--
lemma `ker_fst_of_isClosedImmersion` / 引理 `ker_fst_of_isClosedImmersion`

English:
lemma ker_fst_of_isClosedImmersion
  given: (i : Z ⟶ Y) (f : X ⟶ Y) [IsClosedImmersion i]
  proof: by
  delta IdealSheafData.comap
  rw [← Hom.ker_comp_of_isIso (pullback.map f i f i.imageι (𝟙 _) (i.toImage) (𝟙 _)
    (by simp) (by simp))]; rw [pullback.lift_fst]; rw [Category.comp_id]

中文:
引理 ker_fst_of_isClosedImmersion
  条件: (i : Z ⟶ Y) (f : X ⟶ Y) [是闭浸入 i]
  证明: by
  delta IdealSheafData.comap
  rw [← Hom.ker_comp_of_isIso (pullback.map f i f i.imageι (𝟙 _) (i.toImage) (𝟙 _)
    (by simp) (by simp))]; rw [pullback.lift_fst]; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, Hom.ker_comp_of_isIso, IdealSheafData, IdealSheafData.comap, comp_id, i.image, i.toImage, ker_comp_of_isIso, lift_fst, pullback, pullback.lift_fst, pullback.map, toImage
-/
lemma ker_fst_of_isClosedImmersion (i : Z ⟶ Y) (f : X ⟶ Y) [IsClosedImmersion i] :
    (pullback.fst f i).ker = i.ker.comap f := by
  delta IdealSheafData.comap
  rw [← Hom.ker_comp_of_isIso (pullback.map f i f i.imageι (𝟙 _) (i.toImage) (𝟙 _)
    (by simp) (by simp))]; rw [pullback.lift_fst]; rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.AlgebraicGeometry.isPullback_of_isClosedImmersion` / 引理 `_root_.AlgebraicGeometry.isPullback_of_isClosedImmersion`

English:
lemma _root_.AlgebraicGeometry.isPullback_of_isClosedImmersion
  proof: by
  suffices IsIso (pullback.lift _ _ h) by
    simpa using (IsPullback.of_vert_isIso (show CommSq iX (pullback.lift iX Zf h)
      (𝟙 X) (pullback.fst _ _) from ⟨by simp⟩)).paste_vert (IsPullback.of_hasPullback f iY)
  refine IsClosedImmersion.isIso_of_ker_eq iX (pullback.fst f iY) _ (by simp) ?_


中文:
引理 _root_.AlgebraicGeometry.isPullback_of_isClosedImmersion
  证明: by
  suffices IsIso (pullback.lift _ _ h) by
    simpa using (IsPullback.of_vert_isIso (show CommSq iX (pullback.lift iX Zf h)
      (𝟙 X) (pullback.fst _ _) from ⟨by simp⟩)).paste_vert (IsPullback.of_hasPullback f iY)
  refine IsClosedImmersion.isIso_of_ker_eq iX (pullback.fst f iY) _ (by simp) ?_


Depends on / 依赖: CommSq, IsClosedImmersion, IsClosedImmersion.isIso_of_ker_eq, IsPullback, IsPullback.of_hasPullback, IsPullback.of_vert_isIso, isIso_of_ker_eq, ker_fst_of_isClosedImmersion, of_hasPullback, of_vert_isIso, paste_vert, pullback, pullback.fst, pullback.lift
-/
lemma _root_.AlgebraicGeometry.isPullback_of_isClosedImmersion
    {ZX ZY X Y : Scheme} (iX : ZX ⟶ X) (iY : ZY ⟶ Y) (Zf : ZX ⟶ ZY) (f : X ⟶ Y)
    [IsClosedImmersion iX] [IsClosedImmersion iY]
    (h : iX ≫ f = Zf ≫ iY) (h' : iY.ker.comap f = iX.ker) : IsPullback iX Zf f iY := by
  suffices IsIso (pullback.lift _ _ h) by
    simpa using (IsPullback.of_vert_isIso (show CommSq iX (pullback.lift iX Zf h)
      (𝟙 X) (pullback.fst _ _) from ⟨by simp⟩)).paste_vert (IsPullback.of_hasPullback f iY)
  refine IsClosedImmersion.isIso_of_ker_eq iX (pullback.fst f iY) _ (by simp) ?_
  rw [ker_fst_of_isClosedImmersion]; rw [h']

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (I : X.IdealSheafData) (f : X ⟶ Y)
  body: (I.subschemeι ≫ f).ker

中文:
定义 map
  签名: (I : X.IdealSheafData) (f : X ⟶ Y)
  定义体: (I.subschemeι ≫ f).ker

Depends on / 依赖: I.subscheme
-/
def map (I : X.IdealSheafData) (f : X ⟶ Y) : Y.IdealSheafData :=
  (I.subschemeι ≫ f).ker

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `le_map_iff_comap_le` / 引理 `le_map_iff_comap_le`

English:
lemma le_map_iff_comap_le
  given: {I : X.IdealSheafData} {f : X ⟶ Y} {J : Y.IdealSheafData}
  proof: by
  constructor
  · intro H
    rw [← I.ker_subschemeι]; rw [← pullback.lift_fst (f := f) (g := J.subschemeι) I.subschemeι
      ((I.subschemeι ≫ f).toImage ≫ inclusion H) (by simp)]
    exact Hom.le_ker_comp _ _
  · intro H
    have : (inclusion H ≫ (J.comapIso f).hom ≫ pullback.snd _ _) ≫ J.subsc

中文:
引理 le_map_iff_comap_le
  条件: {I : X.IdealSheafData} {f : X ⟶ Y} {J : Y.IdealSheafData}
  证明: by
  constructor
  · intro H
    rw [← I.ker_subschemeι]; rw [← pullback.lift_fst (f := f) (g := J.subschemeι) I.subschemeι
      ((I.subschemeι ≫ f).toImage ≫ inclusion H) (by simp)]
    exact Hom.le_ker_comp _ _
  · intro H
    have : (inclusion H ≫ (J.comapIso f).hom ≫ pullback.snd _ _) ≫ J.subsc

Depends on / 依赖: Hom.le_ker_comp, I.ker_subscheme, I.subscheme, J.comapIso, J.ker_subscheme, J.subscheme, comapIso, condition, inclusion, le_ker_comp, lift_fst, pullback, pullback.condition, pullback.lift_fst, pullback.snd, toImage
-/
lemma le_map_iff_comap_le {I : X.IdealSheafData} {f : X ⟶ Y} {J : Y.IdealSheafData} :
    J <= I.map f ↔ J.comap f <= I := by
  constructor
  · intro H
    rw [← I.ker_subschemeι]; rw [← pullback.lift_fst (f := f) (g := J.subschemeι) I.subschemeι
      ((I.subschemeι ≫ f).toImage ≫ inclusion H) (by simp)]
    exact Hom.le_ker_comp _ _
  · intro H
    have : (inclusion H ≫ (J.comapIso f).hom ≫ pullback.snd _ _) ≫ J.subschemeι =
        I.subschemeι ≫ f := by simp [← pullback.condition]
    rw [map]; rw [← J.ker_subschemeι]; rw [← this]
    exact Hom.le_ker_comp _ _

section gc

variable (I I₁ I₂ : X.IdealSheafData) (J J₁ J₂ : Y.IdealSheafData) (f : X ⟶ Y)

/--
lemma `map_gc` / 引理 `map_gc`

English:
lemma map_gc
  statement: GaloisConnection (comap · f) (map · f)
  proof: fun _ _ => le_map_iff_comap_le.symm

中文:
引理 map_gc
  结论: GaloisConnection (comap · f) (map · f)
  证明: fun _ _ => le_map_iff_comap_le.symm

Depends on / 依赖: le_map_iff_comap_le, le_map_iff_comap_le.symm
-/
lemma map_gc : GaloisConnection (comap · f) (map · f) := fun _ _ => le_map_iff_comap_le.symm

section
set_option linter.style.whitespace false -- manual alignment is not recognised

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  statement: Monotone (map · f)
  proof: (map_gc f).monotone_u

中文:
引理 map_mono
  结论: 递增 (map · f)
  证明: (map_gc f).monotone_u

Depends on / 依赖: map_gc, monotone_u
-/
lemma map_mono : Monotone (map · f) := (map_gc f).monotone_u
/--
lemma `comap_mono` / 引理 `comap_mono`

English:
lemma comap_mono
  statement: Monotone (comap · f)
  proof: (map_gc f).monotone_l

中文:
引理 comap_mono
  结论: 递增 (comap · f)
  证明: (map_gc f).monotone_l

Depends on / 依赖: map_gc, monotone_l
-/
lemma comap_mono : Monotone (comap · f) := (map_gc f).monotone_l
/--
lemma `le_map_comap` / 引理 `le_map_comap`

English:
lemma le_map_comap
  statement: J <= (J.comap f).map f
  proof: (map_gc f).le_u_l J

中文:
引理 le_map_comap
  结论: J <= (J.comap f).map f
  证明: (map_gc f).le_u_l J

Depends on / 依赖: le_u_l, map_gc
-/
lemma le_map_comap : J <= (J.comap f).map f := (map_gc f).le_u_l J
/--
lemma `comap_map_le` / 引理 `comap_map_le`

English:
lemma comap_map_le
  statement: (I.map f).comap f <= I
  proof: (map_gc f).l_u_le I

中文:
引理 comap_map_le
  结论: (I.map f).comap f <= I
  证明: (map_gc f).l_u_le I

Depends on / 依赖: l_u_le, map_gc
-/
lemma comap_map_le : (I.map f).comap f <= I := (map_gc f).l_u_le I
/--
lemma `map_top` / 引理 `map_top`

English:
lemma map_top
  statement: map ⊤ f = ⊤
  proof: (map_gc f).u_top

中文:
引理 map_top
  结论: map ⊤ f = ⊤
  证明: (map_gc f).u_top
-/
@[simp] lemma map_top : map ⊤ f = ⊤ := (map_gc f).u_top
/--
lemma `comap_bot` / 引理 `comap_bot`

English:
lemma comap_bot
  statement: comap ⊥ f = ⊥
  proof: (map_gc f).l_bot

中文:
引理 comap_bot
  结论: comap ⊥ f = ⊥
  证明: (map_gc f).l_bot
-/
@[simp] lemma comap_bot : comap ⊥ f = ⊥ := (map_gc f).l_bot
/--
lemma `map_inf` / 引理 `map_inf`

English:
lemma map_inf
  statement: map (I₁ ⊓ I₂) f = map I₁ f ⊓ map I₂ f
  proof: (map_gc f).u_inf

中文:
引理 map_inf
  结论: map (I₁ ⊓ I₂) f = map I₁ f ⊓ map I₂ f
  证明: (map_gc f).u_inf
-/
@[simp] lemma map_inf : map (I₁ ⊓ I₂) f = map I₁ f ⊓ map I₂ f := (map_gc f).u_inf
/--
lemma `comap_sup` / 引理 `comap_sup`

English:
lemma comap_sup
  statement: comap (J₁ ⊔ J₂) f = comap J₁ f ⊔ comap J₂ f
  proof: (map_gc f).l_sup

中文:
引理 comap_sup
  结论: comap (J₁ ⊔ J₂) f = comap J₁ f ⊔ comap J₂ f
  证明: (map_gc f).l_sup
-/
@[simp] lemma comap_sup : comap (J₁ ⊔ J₂) f = comap J₁ f ⊔ comap J₂ f := (map_gc f).l_sup

end

end gc

@[simp]
/--
lemma `map_bot` / 引理 `map_bot`

English:
lemma map_bot
  given: (f : X ⟶ Y)
  statement: map ⊥ f = f.ker
  proof: by
  simp [map, Scheme.Hom.ker_comp_of_isIso]

@[simp]

中文:
引理 map_bot
  条件: (f : X ⟶ Y)
  结论: map ⊥ f = f.ker
  证明: by
  simp [map, Scheme.Hom.ker_comp_of_isIso]

@[simp]

Depends on / 依赖: Scheme, Scheme.Hom.ker_comp_of_isIso, ker_comp_of_isIso
-/
lemma map_bot (f : X ⟶ Y) : map ⊥ f = f.ker := by
  simp [map, Scheme.Hom.ker_comp_of_isIso]

@[simp]
/--
lemma `comap_top` / 引理 `comap_top`

English:
lemma comap_top
  given: (f : X ⟶ Y)
  statement: comap ⊤ f = ⊤
  proof: by
  rw [comap]; rw [Hom.ker_eq_top_iff_isEmpty]
  exact Function.isEmpty (pullback.snd f _)

@[simp]

中文:
引理 comap_top
  条件: (f : X ⟶ Y)
  结论: comap ⊤ f = ⊤
  证明: by
  rw [comap]; rw [Hom.ker_eq_top_iff_isEmpty]
  exact Function.isEmpty (pullback.snd f _)

@[simp]

Depends on / 依赖: Function, Function.isEmpty, Hom.ker_eq_top_iff_isEmpty, isEmpty, ker_eq_top_iff_isEmpty, pullback, pullback.snd
-/
lemma comap_top (f : X ⟶ Y) : comap ⊤ f = ⊤ := by
  rw [comap]; rw [Hom.ker_eq_top_iff_isEmpty]
  exact Function.isEmpty (pullback.snd f _)

@[simp]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (I : X.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  apply le_antisymm
  · rw [le_map_iff_comap_le, le_map_iff_comap_le, ← comap_comp]; exact comap_map_le _ _
  · rw [le_map_iff_comap_le, comap_comp]
    exact (comap_mono _ (comap_map_le _ _)).trans (comap_map_le _ _)

@[simp]

中文:
引理 map_comp
  条件: (I : X.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  apply le_antisymm
  · rw [le_map_iff_comap_le, le_map_iff_comap_le, ← comap_comp]; exact comap_map_le _ _
  · rw [le_map_iff_comap_le, comap_comp]
    exact (comap_mono _ (comap_map_le _ _)).trans (comap_map_le _ _)

@[simp]

Depends on / 依赖: comap_comp, comap_map_le, comap_mono, le_antisymm, le_map_iff_comap_le
-/
lemma map_comp (I : X.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    I.map (f ≫ g) = (I.map f).map g := by
  apply le_antisymm
  · rw [le_map_iff_comap_le, le_map_iff_comap_le, ← comap_comp]; exact comap_map_le _ _
  · rw [le_map_iff_comap_le, comap_comp]
    exact (comap_mono _ (comap_map_le _ _)).trans (comap_map_le _ _)

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (I : Z.IdealSheafData)
  proof: by
  simp [map]

中文:
引理 map_id
  条件: (I : Z.IdealSheafData)
  证明: by
  simp [map]
-/
lemma map_id (I : Z.IdealSheafData) :
    I.map (𝟙 _) = I := by
  simp [map]

/--
lemma `map_ker` / 引理 `map_ker`

English:
lemma map_ker
  given: (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: f.ker.map g = (f ≫ g).ker
  proof: by
  simp [← map_bot]

中文:
引理 map_ker
  条件: (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: f.ker.map g = (f ≫ g).ker
  证明: by
  simp [← map_bot]

Depends on / 依赖: map_bot
-/
lemma map_ker (f : X ⟶ Y) (g : Y ⟶ Z) : f.ker.map g = (f ≫ g).ker := by
  simp [← map_bot]

/--
lemma `_root_.AlgebraicGeometry.Scheme.Hom.ker_comp` / 引理 `_root_.AlgebraicGeometry.Scheme.Hom.ker_comp`

English:
lemma _root_.AlgebraicGeometry.Scheme.Hom.ker_comp
  proof: (map_ker f g).symm

中文:
引理 _root_.AlgebraicGeometry.概形.态射.ker_comp
  证明: (map_ker f g).symm

Depends on / 依赖: map_ker
-/
lemma _root_.AlgebraicGeometry.Scheme.Hom.ker_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).ker = f.ker.map g := (map_ker f g).symm

/--
lemma `map_vanishingIdeal` / 引理 `map_vanishingIdeal`

English:
lemma map_vanishingIdeal
  given: {X Y : Scheme} (f : X ⟶ Y) (Z : TopologicalSpace.Closeds X)
  proof: by
  apply le_antisymm
  · rw [map, ← le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
    refine .trans ?_ (Hom.range_subset_ker_support _)
    rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_subschemeι]; rw [coe_support_vanishingIdeal]
  · simp

中文:
引理 map_vanishingIdeal
  条件: {X Y : 概形} (f : X ⟶ Y) (Z : 拓扑空间.Closeds X)
  证明: by
  apply le_antisymm
  · rw [map, ← le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
    refine .trans ?_ (Hom.range_subset_ker_support _)
    rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_subschemeι]; rw [coe_support_vanishingIdeal]
  · simp

Depends on / 依赖: Closeds, Hom.range_subset_ker_support, Scheme, Scheme.Hom.comp_base, Set.image_subset_iff, Set.range_comp, SetLike, SetLike.coe_subset_coe, TopCat, TopCat.coe_comp, TopologicalSpace, TopologicalSpace.Closeds.closure_le, closure_le, coe_comp, coe_subset_coe, coe_support_vanishingIdeal, comp_base, image_subset_iff, le_antisymm, le_map_iff_comap_le
-/
lemma map_vanishingIdeal {X Y : Scheme} (f : X ⟶ Y) (Z : TopologicalSpace.Closeds X) :
    (vanishingIdeal Z).map f = vanishingIdeal (.closure (f '' Z)) := by
  apply le_antisymm
  · rw [map, ← le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
    refine .trans ?_ (Hom.range_subset_ker_support _)
    rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_subschemeι]; rw [coe_support_vanishingIdeal]
  · simp [le_map_iff_comap_le, ← le_support_iff_le_vanishingIdeal, ← Set.image_subset_iff,
      subset_closure, ← SetLike.coe_subset_coe]

@[simp]
/--
lemma `support_map` / 引理 `support_map`

English:
lemma support_map
  given: (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f]
  proof: by
  ext1
  rw [map]; rw [Scheme.Hom.support_ker]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_subschemeι]; rw [TopologicalSpace.Closeds.coe_closure]

中文:
引理 support_map
  条件: (I : X.IdealSheafData) (f : X ⟶ Y) [拟紧 f]
  证明: by
  ext1
  rw [map]; rw [Scheme.Hom.support_ker]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_subschemeι]; rw [TopologicalSpace.Closeds.coe_closure]

Depends on / 依赖: Closeds, Scheme, Scheme.Hom.comp_base, Scheme.Hom.support_ker, Set.range_comp, TopCat, TopCat.coe_comp, TopologicalSpace, TopologicalSpace.Closeds.coe_closure, coe_closure, coe_comp, comp_base, range_comp, support_ker
-/
lemma support_map (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f] :
    (I.map f).support = .closure (f '' I.support) := by
  ext1
  rw [map]; rw [Scheme.Hom.support_ker]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [range_subschemeι]; rw [TopologicalSpace.Closeds.coe_closure]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ideal_map` / 引理 `ideal_map`

English:
lemma ideal_map
  statement: (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens)
  proof: by
  have : RingHom.ker (I.subschemeObjIso ⟨_, H⟩).inv.hom = ⊥ :=
    RingHom.ker_coe_equiv (I.subschemeObjIso ⟨_, H⟩).symm.commRingCatIsoToRingEquiv
  simp [map, ← RingHom.comap_ker, subschemeι_app _ ⟨_, H⟩,
    this, ← RingHom.ker_eq_comap_bot]

中文:
引理 ideal_map
  结论: (I : X.IdealSheafData) (f : X ⟶ Y) [拟紧 f] (U : Y.affineOpens)
  证明: by
  have : RingHom.ker (I.subschemeObjIso ⟨_, H⟩).inv.hom = ⊥ :=
    RingHom.ker_coe_equiv (I.subschemeObjIso ⟨_, H⟩).symm.commRingCatIsoToRingEquiv
  simp [map, ← RingHom.comap_ker, subschemeι_app _ ⟨_, H⟩,
    this, ← RingHom.ker_eq_comap_bot]

Depends on / 依赖: I.subschemeObjIso, RingHom, RingHom.comap_ker, RingHom.ker, RingHom.ker_coe_equiv, RingHom.ker_eq_comap_bot, comap_ker, commRingCatIsoToRingEquiv, inv.hom, ker_coe_equiv, ker_eq_comap_bot, subschemeObjIso, symm.commRingCatIsoToRingEquiv
-/
lemma ideal_map (I : X.IdealSheafData) (f : X ⟶ Y) [QuasiCompact f] (U : Y.affineOpens)
    (H : IsAffineOpen (f ⁻¹ᵁ U)) :
    (I.map f).ideal U = (I.ideal ⟨_, H⟩).comap (f.app U).hom := by
  have : RingHom.ker (I.subschemeObjIso ⟨_, H⟩).inv.hom = ⊥ :=
    RingHom.ker_coe_equiv (I.subschemeObjIso ⟨_, H⟩).symm.commRingCatIsoToRingEquiv
  simp [map, ← RingHom.comap_ker, subschemeι_app _ ⟨_, H⟩,
    this, ← RingHom.ker_eq_comap_bot]

/--
lemma `ideal_map_of_isAffineHom` / 引理 `ideal_map_of_isAffineHom`

English:
lemma ideal_map_of_isAffineHom
  proof: ideal_map I f U (U.2.preimage f)

中文:
引理 ideal_map_of_isAffineHom
  证明: ideal_map I f U (U.2.preimage f)

Depends on / 依赖: ideal_map, preimage
-/
lemma ideal_map_of_isAffineHom
    (I : X.IdealSheafData) (f : X ⟶ Y) [IsAffineHom f] (U : Y.affineOpens) :
    (I.map f).ideal U = (I.ideal ⟨_, U.2.preimage f⟩).comap (f.app U).hom :=
  ideal_map I f U (U.2.preimage f)

/--
lemma `ideal_comap_of_isOpenImmersion` / 引理 `ideal_comap_of_isOpenImmersion`

English:
lemma ideal_comap_of_isOpenImmersion
  proof: by
  refine (ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _
    (IsPullback.of_hasPullback f I.subschemeι) U).trans ?_
  simp

中文:
引理 ideal_comap_of_isOpenImmersion
  证明: by
  refine (ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _
    (IsPullback.of_hasPullback f I.subschemeι) U).trans ?_
  simp

Depends on / 依赖: I.subscheme, IsPullback, IsPullback.of_hasPullback, Truncated, infer_instance, ker_ideal_of_isPullback_of_isOpenImmersion, of_hasPullback
-/
lemma ideal_comap_of_isOpenImmersion
    (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] (U : X.affineOpens) :
    (I.comap f).ideal U = (I.ideal ⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩).comap
      (f.appIso U).inv.hom := by
  refine (ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _
    (IsPullback.of_hasPullback f I.subschemeι) U).trans ?_
  simp

/--
Definition of `subschemeMap` / `subschemeMap` 的定义

English:
definition subschemeMap
  signature: (I : X.IdealSheafData) (J : Y.IdealSheafData)
  body: IsClosedImmersion.lift J.subschemeι (I.subschemeι ≫ f) (by simpa using! H)

@[reassoc (attr := simp)]

中文:
定义 subschemeMap
  签名: (I : X.IdealSheafData) (J : Y.IdealSheafData)
  定义体: IsClosedImmersion.lift J.subschemeι (I.subschemeι ≫ f) (by simpa using! H)

@[reassoc (attr := simp)]

Depends on / 依赖: I.subscheme, IsClosedImmersion, IsClosedImmersion.lift, J.subscheme
-/
def subschemeMap (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (f : X ⟶ Y) (H : J <= I.map f) : I.subscheme ⟶ J.subscheme :=
  IsClosedImmersion.lift J.subschemeι (I.subschemeι ≫ f) (by simpa using! H)

@[reassoc (attr := simp)]
/--
lemma `subschemeMap_subschemeι` / 引理 `subschemeMap_subschemeι`

English:
lemma subschemeMap_subschemeι
  statement: (I : X.IdealSheafData) (J : Y.IdealSheafData)
  proof: IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]

中文:
引理 subschemeMap_subschemeι
  结论: (I : X.IdealSheafData) (J : Y.IdealSheafData)
  证明: IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsClosedImmersion, IsClosedImmersion.lift_fac, Truncated, infer_instance, lift_fac
-/
lemma subschemeMap_subschemeι (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (f : X ⟶ Y) (H : J <= I.map f) : subschemeMap I J f H ≫ J.subschemeι = I.subschemeι ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
/--
lemma `comapIso_hom_snd` / 引理 `comapIso_hom_snd`

English:
lemma comapIso_hom_snd
  given: (I : Y.IdealSheafData) (f : X ⟶ Y)
  proof: by
  rw [← cancel_mono I.subschemeι]
  simp [← pullback.condition]

中文:
引理 comapIso_hom_snd
  条件: (I : Y.IdealSheafData) (f : X ⟶ Y)
  证明: by
  rw [← cancel_mono I.subschemeι]
  simp [← pullback.condition]

Depends on / 依赖: I.subscheme, cancel_mono, condition, pullback, pullback.condition
-/
lemma comapIso_hom_snd (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comapIso f).hom ≫ pullback.snd _ _ = subschemeMap _ _ f (I.le_map_comap f) := by
  rw [← cancel_mono I.subschemeι]
  simp [← pullback.condition]

end Scheme.IdealSheafData

end AlgebraicGeometry
