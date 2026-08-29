/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# The category of abelian groups has finite biproducts
-/

@[expose] public section

open CategoryTheory Limits

universe w u

namespace AddCommGrpCat

-- As `AddCommGrpCat` is preadditive, and has all limits, it automatically has biproducts.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasBinaryBiproducts AddCommGrpCat
  body: HasBinaryBiproducts.of_hasBinaryProducts

中文:
实例 :
  签名: HasBinaryBiproducts AddCommGrpCat
  定义体: HasBinaryBiproducts.of_hasBinaryProducts

Depends on / 依赖: HasBinaryBiproducts, HasBinaryBiproducts.of_hasBinaryProducts, of_hasBinaryProducts
-/
instance : HasBinaryBiproducts AddCommGrpCat :=
  HasBinaryBiproducts.of_hasBinaryProducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteBiproducts AddCommGrpCat
  body: HasFiniteBiproducts.of_hasFiniteProducts

中文:
实例 :
  签名: HasFiniteBiproducts AddCommGrpCat
  定义体: HasFiniteBiproducts.of_hasFiniteProducts

Depends on / 依赖: HasFiniteBiproducts, HasFiniteBiproducts.of_hasFiniteProducts, of_hasFiniteProducts
-/
instance : HasFiniteBiproducts AddCommGrpCat :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `AddCommGrpCat`, using
`AddCommGrpCat.of (G × H)`.
-/
@[simps! cone_pt isLimit_lift]
/--
Definition of `binaryProductLimitCone` / `binaryProductLimitCone` 的定义

English:
definition binaryProductLimitCone
  signature: (G H : AddCommGrpCat.{u})
  body: BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

@[simp]

中文:
定义 binaryProductLimitCone
  签名: (G H : AddCommGrpCat.{u})
  定义体: BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.fst, AddMonoidHom.snd, BinaryFan, BinaryFan.mk
-/
def binaryProductLimitCone (G H : AddCommGrpCat.{u}) : Limits.LimitCone (pair G H) where
  cone := BinaryFan.mk (ofHom (AddMonoidHom.fst G H)) (ofHom (AddMonoidHom.snd G H))
  isLimit := BinaryFan.IsLimit.mk _ (fun l r => ofHom (AddMonoidHom.prod l.hom r.hom))
    (fun _ _ => rfl) (fun _ _ => rfl) (by cat_disch)

@[simp]
/--
theorem `binaryProductLimitCone_cone_π_app_left` / 定理 `binaryProductLimitCone_cone_π_app_left`

English:
theorem binaryProductLimitCone_cone_π_app_left
  given: (G H : AddCommGrpCat.{u})
  proof: rfl

@[simp]

中文:
定理 binaryProductLimitCone_cone_π_app_left
  条件: (G H : AddCommGrpCat.{u})
  证明: rfl

@[simp]
-/
theorem binaryProductLimitCone_cone_π_app_left (G H : AddCommGrpCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.left⟩ = ofHom (AddMonoidHom.fst G H) :=
  rfl

@[simp]
/--
theorem `binaryProductLimitCone_cone_π_app_right` / 定理 `binaryProductLimitCone_cone_π_app_right`

English:
theorem binaryProductLimitCone_cone_π_app_right
  given: (G H : AddCommGrpCat.{u})
  proof: rfl

中文:
定理 binaryProductLimitCone_cone_π_app_right
  条件: (G H : AddCommGrpCat.{u})
  证明: rfl
-/
theorem binaryProductLimitCone_cone_π_app_right (G H : AddCommGrpCat.{u}) :
    (binaryProductLimitCone G H).cone.π.app ⟨WalkingPair.right⟩ = ofHom (AddMonoidHom.snd G H) :=
  rfl

/--
Definition of `biprodIsoProd` / `biprodIsoProd` 的定义

English:
definition biprodIsoProd
  signature: (G H : AddCommGrpCat.{u})
  body: IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit

@[simp, elementwise]

中文:
定义 biprodIsoProd
  签名: (G H : AddCommGrpCat.{u})
  定义体: IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit

@[simp, elementwise]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, IsLimit, IsLimit.conePointUniqueUpToIso, binaryProductLimitCone, conePointUniqueUpToIso, isLimit
-/
noncomputable def biprodIsoProd (G H : AddCommGrpCat.{u}) :
    (G ⊞ H : AddCommGrpCat) ≅ AddCommGrpCat.of (G × H) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit G H) (binaryProductLimitCone G H).isLimit

@[simp, elementwise]
/--
theorem `biprodIsoProd_inv_comp_fst` / 定理 `biprodIsoProd_inv_comp_fst`

English:
theorem biprodIsoProd_inv_comp_fst
  given: (G H : AddCommGrpCat.{u})
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]

中文:
定理 biprodIsoProd_inv_comp_fst
  条件: (G H : AddCommGrpCat.{u})
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingPair, WalkingPair.left, conePointUniqueUpToIso_inv_comp
-/
theorem biprodIsoProd_inv_comp_fst (G H : AddCommGrpCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.fst = ofHom (AddMonoidHom.fst G H) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
/--
theorem `biprodIsoProd_inv_comp_snd` / 定理 `biprodIsoProd_inv_comp_snd`

English:
theorem biprodIsoProd_inv_comp_snd
  given: (G H : AddCommGrpCat.{u})
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

@[elementwise]

中文:
定理 biprodIsoProd_inv_comp_snd
  条件: (G H : AddCommGrpCat.{u})
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

@[elementwise]

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingPair, WalkingPair.right, conePointUniqueUpToIso_inv_comp
-/
theorem biprodIsoProd_inv_comp_snd (G H : AddCommGrpCat.{u}) :
    (biprodIsoProd G H).inv ≫ biprod.snd = ofHom (AddMonoidHom.snd G H) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

@[elementwise]
/--
lemma `biprodIsoProd_inv_comp_desc` / 引理 `biprodIsoProd_inv_comp_desc`

English:
lemma biprodIsoProd_inv_comp_desc
  given: {G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H ⟶ K)
  proof: by
  simp [biprod.desc_eq, ← biprodIsoProd_inv_comp_fst, ← biprodIsoProd_inv_comp_snd]

中文:
引理 biprodIsoProd_inv_comp_desc
  条件: {G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H ⟶ K)
  证明: by
  simp [biprod.desc_eq, ← biprodIsoProd_inv_comp_fst, ← biprodIsoProd_inv_comp_snd]

Depends on / 依赖: biprod, biprod.desc_eq, biprodIsoProd_inv_comp_fst, biprodIsoProd_inv_comp_snd, desc_eq
-/
lemma biprodIsoProd_inv_comp_desc {G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H ⟶ K) :
    (biprodIsoProd G H).inv ≫ biprod.desc f g =
      ofHom (AddMonoidHom.fst G H) ≫ f + ofHom (AddMonoidHom.snd G H) ≫ g := by
  simp [biprod.desc_eq, ← biprodIsoProd_inv_comp_fst, ← biprodIsoProd_inv_comp_snd]

namespace HasLimit

variable {J : Type w} (f : J -> AddCommGrpCat.{max w u})

set_option backward.defeqAttrib.useBackward true in
/-- The map from an arbitrary cone over an indexed family of abelian groups
to the Cartesian product of those groups.
-/
@[simps!]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (s : Fan f)
  body: ofHom
  { toFun x j := s.π.app ⟨j⟩ x
    map_zero' := by
      simp only [Functor.const_obj_obj, map_zero]
      rfl
    map_add' x y := by
      simp only [Functor.const_obj_obj, map_add]
      rfl }

中文:
定义 lift
  签名: (s : Fan f)
  定义体: ofHom
  { toFun x j := s.π.app ⟨j⟩ x
    map_zero' := by
      simp only [Functor.const_obj_obj, map_zero]
      rfl
    map_add' x y := by
      simp only [Functor.const_obj_obj, map_add]
      rfl }

Depends on / 依赖: Functor, Functor.const_obj_obj, const_obj_obj, map_add, map_zero
-/
def lift (s : Fan f) : s.pt ⟶ AddCommGrpCat.of (forall j, f j) :=
  ofHom
  { toFun x j := s.π.app ⟨j⟩ x
    map_zero' := by
      simp only [Functor.const_obj_obj, map_zero]
      rfl
    map_add' x y := by
      simp only [Functor.const_obj_obj, map_add]
      rfl }

/-- Construct limit data for a product in `AddCommGrpCat`, using
`AddCommGrpCat.of (∀ j, F.obj j)`.
-/
@[simps]
/--
Definition of `productLimitCone` / `productLimitCone` 的定义

English:
definition productLimitCone
  signature: : Limits.LimitCone (Discrete.functor f) where
  body: { pt := AddCommGrpCat.of (forall j, f j)
π := Discrete.natTrans fun j => ofHom Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact CategoryTheory.congr_fun (w ⟨j⟩) x }

中文:
定义 productLimitCone
  签名: : Limits.LimitCone (Discrete.functor f) where
  定义体: { pt := AddCommGrpCat.of (forall j, f j)
π := Discrete.natTrans fun j => ofHom Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact CategoryTheory.congr_fun (w ⟨j⟩) x }

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, CategoryTheory, CategoryTheory.congr_fun, Discrete, Discrete.natTrans, Pi.evalAddMonoidHom, congr_fun, evalAddMonoidHom, isLimit, j.as, natTrans
-/
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := AddCommGrpCat.of (forall j, f j)
π := Discrete.natTrans fun j => ofHom Pi.evalAddMonoidHom (fun j => f j) j.as }
  isLimit :=
    { lift := lift.{_, u} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact CategoryTheory.congr_fun (w ⟨j⟩) x }

end HasLimit

open HasLimit

variable {J : Type} [Finite J]

/--
Definition of `biproductIsoPi` / `biproductIsoPi` 的定义

English:
definition biproductIsoPi
  signature: (f : J -> AddCommGrpCat.{u})
  body: IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]

中文:
定义 biproductIsoPi
  签名: (f : J -> AddCommGrpCat.{u})
  定义体: IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, biproduct, biproduct.isLimit, conePointUniqueUpToIso, isLimit, productLimitCone
-/
noncomputable def biproductIsoPi (f : J -> AddCommGrpCat.{u}) :
    (⨁ f : AddCommGrpCat) ≅ AddCommGrpCat.of (forall j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]
/--
theorem `biproductIsoPi_inv_comp_π` / 定理 `biproductIsoPi_inv_comp_π`

English:
theorem biproductIsoPi_inv_comp_π
  given: (f : J -> AddCommGrpCat.{u}) (j : J)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

中文:
定理 biproductIsoPi_inv_comp_π
  条件: (f : J -> AddCommGrpCat.{u}) (j : J)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
theorem biproductIsoPi_inv_comp_π (f : J -> AddCommGrpCat.{u}) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (Pi.evalAddMonoidHom (fun j => f j) j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end AddCommGrpCat
