/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The category of `R`-modules has finite biproducts
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace ModuleCat

variable {R : Type u} [Ring R]

-- As `ModuleCat R` is preadditive, and has all limits, it automatically has biproducts.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasBinaryBiproducts (ModuleCat.{v} R)
  body: HasBinaryBiproducts.of_hasBinaryProducts

中文:
实例 :
  签名: 有BinaryBiproducts (模范畴.{v} R)
  定义体: HasBinaryBiproducts.of_hasBinaryProducts

Depends on / 依赖: HasBinaryBiproducts, HasBinaryBiproducts.of_hasBinaryProducts, of_hasBinaryProducts
-/
instance : HasBinaryBiproducts (ModuleCat.{v} R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteBiproducts (ModuleCat.{v} R)
  body: HasFiniteBiproducts.of_hasFiniteProducts

中文:
实例 :
  签名: 有FiniteBiproducts (模范畴.{v} R)
  定义体: HasFiniteBiproducts.of_hasFiniteProducts

Depends on / 依赖: Finite, HasFiniteBiproducts, HasFiniteBiproducts.of_hasFiniteProducts, Module, Module.Finite, ModuleCat, ModuleCat.homLinearEquiv.symm, homLinearEquiv, of_hasFiniteProducts
-/
instance : HasFiniteBiproducts (ModuleCat.{v} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- We now construct explicit limit data,
-- so we can compare the biproducts to the usual unbundled constructions.
/-- Construct limit data for a binary product in `ModuleCat R`, using `ModuleCat.of R (M × N)`.
-/
@[simps cone_pt isLimit_lift]
/--
Definition of `binaryProductLimitCone` / `binaryProductLimitCone` 的定义

English:
definition binaryProductLimitCone
  signature: (M N : ModuleCat.{v} R)
  body: { pt := ModuleCat.of R (M × N)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (ofHom <| LinearMap.fst R M N) (ofHom <| LinearMap.snd R M N)
          naturality := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  isLimit :=
    { lift := fun 

中文:
定义 binaryProductLimitCone
  签名: (M N : 模范畴.{v} R)
  定义体: { pt := ModuleCat.of R (M × N)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (ofHom <| LinearMap.fst R M N) (ofHom <| LinearMap.snd R M N)
          naturality := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  isLimit :=
    { lift := fun 

Depends on / 依赖: Discrete, Discrete.casesOn, Finite, InducedCategory, InducedCategory.homLinearEquiv.symm, LinearMap, LinearMap.fst, LinearMap.prod, LinearMap.snd, Module, Module.Finite, ModuleCat, ModuleCat.of, V.obj, W.obj, WalkingPair, WalkingPair.casesOn, WalkingPair.left, WalkingPair.right, casesOn
-/
def binaryProductLimitCone (M N : ModuleCat.{v} R) : Limits.LimitCone (pair M N) where
  cone :=
    { pt := ModuleCat.of R (M × N)
      π :=
        { app := fun j =>
            Discrete.casesOn j fun j =>
              WalkingPair.casesOn j (ofHom <| LinearMap.fst R M N) (ofHom <| LinearMap.snd R M N)
          naturality := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟨⟨⟩⟩⟩ <;> rfl } }
  isLimit :=
    { lift := fun s => ofHom <| LinearMap.prod
        (s.π.app ⟨WalkingPair.left⟩).hom
        (s.π.app ⟨WalkingPair.right⟩).hom
      fac := by rintro s (⟨⟩ | ⟨⟩) <;> rfl
      uniq := fun s m w => by
        simp_rw [← w ⟨WalkingPair.left⟩, ← w ⟨WalkingPair.right⟩]
        rfl }

@[simp]
/--
theorem `binaryProductLimitCone_cone_π_app_left` / 定理 `binaryProductLimitCone_cone_π_app_left`

English:
theorem binaryProductLimitCone_cone_π_app_left
  given: (M N : ModuleCat.{v} R)
  proof: rfl

@[simp]

中文:
定理 binaryProductLimitCone_cone_π_app_left
  条件: (M N : 模范畴.{v} R)
  证明: rfl

@[simp]
-/
theorem binaryProductLimitCone_cone_π_app_left (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.left⟩ = ofHom (LinearMap.fst R M N) :=
  rfl

@[simp]
/--
theorem `binaryProductLimitCone_cone_π_app_right` / 定理 `binaryProductLimitCone_cone_π_app_right`

English:
theorem binaryProductLimitCone_cone_π_app_right
  given: (M N : ModuleCat.{v} R)
  proof: rfl

中文:
定理 binaryProductLimitCone_cone_π_app_right
  条件: (M N : 模范畴.{v} R)
  证明: rfl
-/
theorem binaryProductLimitCone_cone_π_app_right (M N : ModuleCat.{v} R) :
    (binaryProductLimitCone M N).cone.π.app ⟨WalkingPair.right⟩ = ofHom (LinearMap.snd R M N) :=
  rfl

/--
Definition of `biprodIsoProd` / `biprodIsoProd` 的定义

English:
definition biprodIsoProd
  signature: (M N : ModuleCat.{v} R)
  body: IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit

@[simp, elementwise]

中文:
定义 biprodIsoProd
  签名: (M N : 模范畴.{v} R)
  定义体: IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit

@[simp, elementwise]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, IsLimit, IsLimit.conePointUniqueUpToIso, binaryProductLimitCone, conePointUniqueUpToIso, isLimit
-/
noncomputable def biprodIsoProd (M N : ModuleCat.{v} R) :
    (M ⊞ N : ModuleCat.{v} R) ≅ ModuleCat.of R (M × N) :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit M N) (binaryProductLimitCone M N).isLimit

@[simp, elementwise]
/--
theorem `biprodIsoProd_inv_comp_fst` / 定理 `biprodIsoProd_inv_comp_fst`

English:
theorem biprodIsoProd_inv_comp_fst
  given: (M N : ModuleCat.{v} R)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]

中文:
定理 biprodIsoProd_inv_comp_fst
  条件: (M N : 模范畴.{v} R)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingPair, WalkingPair.left, conePointUniqueUpToIso_inv_comp
-/
theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.fst = ofHom (LinearMap.fst R M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

@[simp, elementwise]
/--
theorem `biprodIsoProd_inv_comp_snd` / 定理 `biprodIsoProd_inv_comp_snd`

English:
theorem biprodIsoProd_inv_comp_snd
  given: (M N : ModuleCat.{v} R)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

中文:
定理 biprodIsoProd_inv_comp_snd
  条件: (M N : 模范畴.{v} R)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingPair, WalkingPair.right, conePointUniqueUpToIso_inv_comp
-/
theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat.{v} R) :
    (biprodIsoProd M N).inv ≫ biprod.snd = ofHom (LinearMap.snd R M N) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

namespace HasLimit

variable {J : Type w} (f : J -> ModuleCat.{max w v} R)

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
  { toFun := fun x j => s.π.app ⟨j⟩ x
    map_add' := fun x y => by
      simp only [Functor.const_obj_obj, map_add]
      rfl
    map_smul' := fun r x => by
      simp only [Functor.const_obj_obj, map_smul]
      rfl }

中文:
定义 lift
  签名: (s : Fan f)
  定义体: ofHom
  { toFun := fun x j => s.π.app ⟨j⟩ x
    map_add' := fun x y => by
      simp only [Functor.const_obj_obj, map_add]
      rfl
    map_smul' := fun r x => by
      simp only [Functor.const_obj_obj, map_smul]
      rfl }

Depends on / 依赖: Functor, Functor.const_obj_obj, const_obj_obj, map_add, map_smul
-/
def lift (s : Fan f) : s.pt ⟶ ModuleCat.of R (forall j, f j) :=
  ofHom
  { toFun := fun x j => s.π.app ⟨j⟩ x
    map_add' := fun x y => by
      simp only [Functor.const_obj_obj, map_add]
      rfl
    map_smul' := fun r x => by
      simp only [Functor.const_obj_obj, map_smul]
      rfl }

/-- Construct limit data for a product in `ModuleCat R`, using `ModuleCat.of R (∀ j, F.obj j)`.
-/
@[simps]
/--
Definition of `productLimitCone` / `productLimitCone` 的定义

English:
definition productLimitCone
  signature: : Limits.LimitCone (Discrete.functor f) where
  body: { pt := ModuleCat.of R (forall j, f j)
      π := Discrete.natTrans fun j => ofHom (LinearMap.proj j.as : (forall j, f j) ->ₗ[R] f j.as) }
  isLimit :=
    { lift := lift.{_, v} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact congr_arg (fun g : s.pt ⟶ f j =>

中文:
定义 productLimitCone
  签名: : Limits.极限锥 (离散.functor f) where
  定义体: { pt := ModuleCat.of R (forall j, f j)
      π := Discrete.natTrans fun j => ofHom (LinearMap.proj j.as : (forall j, f j) ->ₗ[R] f j.as) }
  isLimit :=
    { lift := lift.{_, v} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact congr_arg (fun g : s.pt ⟶ f j =>

Depends on / 依赖: Discrete, Discrete.natTrans, LinearMap, LinearMap.proj, ModuleCat, ModuleCat.of, congr_arg, isLimit, j.as, natTrans, s.pt
-/
def productLimitCone : Limits.LimitCone (Discrete.functor f) where
  cone :=
    { pt := ModuleCat.of R (forall j, f j)
      π := Discrete.natTrans fun j => ofHom (LinearMap.proj j.as : (forall j, f j) ->ₗ[R] f j.as) }
  isLimit :=
    { lift := lift.{_, v} f
      fac := fun _ _ => rfl
      uniq := fun s m w => by
        ext x j
        exact congr_arg (fun g : s.pt ⟶ f j => (g : s.pt -> f j) x) (w ⟨j⟩) }

end HasLimit

open HasLimit

variable {J : Type} (f : J -> ModuleCat.{v} R)

/--
Definition of `biproductIsoPi` / `biproductIsoPi` 的定义

English:
definition biproductIsoPi
  signature: [Finite J] (f : J -> ModuleCat.{v} R)
  body: IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]

中文:
定义 biproductIsoPi
  签名: [有限 J] (f : J -> 模范畴.{v} R)
  定义体: IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, biproduct, biproduct.isLimit, conePointUniqueUpToIso, isLimit, productLimitCone
-/
noncomputable def biproductIsoPi [Finite J] (f : J -> ModuleCat.{v} R) :
    ((⨁ f) : ModuleCat.{v} R) ≅ ModuleCat.of R (forall j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (productLimitCone f).isLimit

@[simp, elementwise]
/--
theorem `biproductIsoPi_inv_comp_π` / 定理 `biproductIsoPi_inv_comp_π`

English:
theorem biproductIsoPi_inv_comp_π
  given: [Finite J] (f : J -> ModuleCat.{v} R) (j : J)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

中文:
定理 biproductIsoPi_inv_comp_π
  条件: [有限 J] (f : J -> 模范畴.{v} R) (j : J)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp
-/
theorem biproductIsoPi_inv_comp_π [Finite J] (f : J -> ModuleCat.{v} R) (j : J) :
    (biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (LinearMap.proj j : (forall j, f j) ->ₗ[R] f j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end ModuleCat

section SplitExact
open ModuleCat
section universe_monomorphic

variable {R : Type u} {A M B : Type v} [Ring R] [AddCommGroup A] [Module R A] [AddCommGroup B]
  [Module R B] [AddCommGroup M] [Module R M]

variable {j : A ->ₗ[R] M} {g : M ->ₗ[R] B}


set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def lequivProdOfRightSplitExact' {f : B ->ₗ[R] M} (hj : Function.Injective j)
  body: ((ShortComplex.Splitting.ofExactOfSection _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.mono_iff_injective])).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearEquiv

中文:
定义 noncomputable
  签名: def lequivProdOfRightSplitExact' {f : B ->ₗ[R] M} (hj : 函数.单射 j)
  定义体: ((ShortComplex.Splitting.ofExactOfSection _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.mono_iff_injective])).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearEquiv
-/
private noncomputable def lequivProdOfRightSplitExact' {f : B ->ₗ[R] M} (hj : Function.Injective j)
    (exac : LinearMap.range j = LinearMap.ker g) (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  ((ShortComplex.Splitting.ofExactOfSection _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.mono_iff_injective])).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearEquiv

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def lequivProdOfLeftSplitExact' {f : M ->ₗ[R] A} (hg : Function.Surjective g)
  body: ((ShortComplex.Splitting.ofExactOfRetraction _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ModuleCat.ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.epi_iff_surjective] using! hg)).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearE

中文:
定义 noncomputable
  签名: def lequivProdOfLeftSplitExact' {f : M ->ₗ[R] A} (hg : 函数.满射 g)
  定义体: ((ShortComplex.Splitting.ofExactOfRetraction _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ModuleCat.ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.epi_iff_surjective] using! hg)).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearE
-/
private noncomputable def lequivProdOfLeftSplitExact' {f : M ->ₗ[R] A} (hg : Function.Surjective g)
    (exac : LinearMap.range j = LinearMap.ker g) (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  ((ShortComplex.Splitting.ofExactOfRetraction _
    (ShortComplex.Exact.moduleCat_of_range_eq_ker (ModuleCat.ofHom j)
    (ModuleCat.ofHom g) exac) (ModuleCat.ofHom f) (hom_ext h)
    (by simpa only [ModuleCat.epi_iff_surjective] using! hg)).isoBinaryBiproduct ≪≫
    biprodIsoProd _ _).symm.toLinearEquiv

end universe_monomorphic

section universe_polymorphic

universe uA uM uB
variable {R : Type u} {A : Type uA} {M : Type uM} {B : Type uB}
variable [Ring R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup M]
variable [Module R A] [Module R B] [Module R M]

variable {j : A ->ₗ[R] M} {g : M ->ₗ[R] B}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `lequivProdOfRightSplitExact` / `lequivProdOfRightSplitExact` 的定义

English:
definition lequivProdOfRightSplitExact
  signature: {f : B ->ₗ[R] M} (hj : Function.Injective j)
  body: have := lequivProdOfRightSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
 

中文:
定义 lequivProdOfRightSplitExact
  签名: {f : B ->ₗ[R] M} (hj : 函数.单射 j)
  定义体: have := lequivProdOfRightSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
 

Depends on / 依赖: LinearMap, LinearMap.ker_comp, LinearMap.range_comp, Submodule, Submodule.comap_equiv_eq_map_symm, ULift.moduleEquiv.symm.toLinearMap, ULift.moduleEquiv.toLinearMap, comap_equiv_eq_map_symm, ker_comp, lequivProdOfRightSplitExact, moduleEquiv, range_comp, toLinearMap
-/
noncomputable def lequivProdOfRightSplitExact {f : B ->ₗ[R] M} (hj : Function.Injective j)
    (exac : LinearMap.range j = LinearMap.ker g) (h : g.comp f = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  have := lequivProdOfRightSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
    (g := ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap)
    (by simpa using hj)
    (by simp [LinearMap.range_comp, LinearMap.ker_comp, exac, Submodule.comap_equiv_eq_map_symm])
    (by ext x; simpa using congr($h x.down))
  ULift.moduleEquiv.symm.prodCongr ULift.moduleEquiv.symm ≪≫ₗ this ≪≫ₗ ULift.moduleEquiv

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `lequivProdOfLeftSplitExact` / `lequivProdOfLeftSplitExact` 的定义

English:
definition lequivProdOfLeftSplitExact
  signature: {f : M ->ₗ[R] A} (hg : Function.Surjective g)
  body: have := lequivProdOfLeftSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
  

中文:
定义 lequivProdOfLeftSplitExact
  签名: {f : M ->ₗ[R] A} (hg : 函数.满射 g)
  定义体: have := lequivProdOfLeftSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
  

Depends on / 依赖: Finite, LinearMap, LinearMap.ker_comp, LinearMap.range_comp, Module, Module.Finite.equiv_iff, ModuleCat, ModuleCat.coprodIsoDirectSum, Submodule, Submodule.comap_equiv_eq_map_symm, ULift.moduleEquiv.symm.toLinearMap, ULift.moduleEquiv.toLinearMap, classical, comap_equiv_eq_map_symm, coprodIsoDirectSum, equiv_iff, ker_comp, lequivProdOfLeftSplitExact, moduleEquiv, range_comp
-/
noncomputable def lequivProdOfLeftSplitExact {f : M ->ₗ[R] A} (hg : Function.Surjective g)
    (exac : LinearMap.range j = LinearMap.ker g) (h : f.comp j = LinearMap.id) : (A × B) ≃ₗ[R] M :=
  have := lequivProdOfLeftSplitExact'
    (A := ULift.{max uA uM uB} A) (M := ULift.{max uA uM uB} M) (B := ULift.{max uA uM uB} B)
    (f := ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap)
    (j := ULift.moduleEquiv.symm.toLinearMap ∘ₗ j ∘ₗ ULift.moduleEquiv.toLinearMap)
    (g := ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ ULift.moduleEquiv.toLinearMap)
    (by simpa using hg)
    (by simp [LinearMap.range_comp, LinearMap.ker_comp, exac, Submodule.comap_equiv_eq_map_symm])
    (by ext x; simpa using congr($h x.down))
  ULift.moduleEquiv.symm.prodCongr ULift.moduleEquiv.symm ≪≫ₗ this ≪≫ₗ ULift.moduleEquiv

end universe_polymorphic

end SplitExact
