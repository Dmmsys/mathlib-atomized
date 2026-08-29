/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# The concrete products in the category of modules are products in the categorical sense.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {ι : Type v} (Z : ι -> ModuleCat.{max v w} R)

section product

/--
Definition of `productCone` / `productCone` 的定义

English:
definition productCone
  signature: : Fan Z
  body: Fan.mk (ModuleCat.of R (forall i : ι, Z i)) fun i =>
    ofHom (LinearMap.proj i : (forall i : ι, Z i) ->ₗ[R] Z i)

中文:
定义 productCone
  签名: : Fan Z
  定义体: Fan.mk (ModuleCat.of R (forall i : ι, Z i)) fun i =>
    ofHom (LinearMap.proj i : (forall i : ι, Z i) ->ₗ[R] Z i)

Depends on / 依赖: Fan.mk, LinearMap, LinearMap.proj, ModuleCat, ModuleCat.of
-/
def productCone : Fan Z :=
  Fan.mk (ModuleCat.of R (forall i : ι, Z i)) fun i =>
    ofHom (LinearMap.proj i : (forall i : ι, Z i) ->ₗ[R] Z i)

/--
Definition of `productConeIsLimit` / `productConeIsLimit` 的定义

English:
definition productConeIsLimit
  signature: : IsLimit (productCone Z) where
  body: ofHom (LinearMap.pi fun j => (s.π.app ⟨j⟩).hom : s.pt ->ₗ[R] forall i : ι, Z i)
  uniq s m w := by
    ext x
    funext i
    exact DFunLike.congr_fun (congr_arg Hom.hom (w ⟨i⟩)) x

中文:
定义 productConeIsLimit
  签名: : 是极限 (productCone Z) where
  定义体: ofHom (LinearMap.pi fun j => (s.π.app ⟨j⟩).hom : s.pt ->ₗ[R] forall i : ι, Z i)
  uniq s m w := by
    ext x
    funext i
    exact DFunLike.congr_fun (congr_arg Hom.hom (w ⟨i⟩)) x

Depends on / 依赖: LinearMap, LinearMap.pi, s.pt
-/
def productConeIsLimit : IsLimit (productCone Z) where
  lift s := ofHom (LinearMap.pi fun j => (s.π.app ⟨j⟩).hom : s.pt ->ₗ[R] forall i : ι, Z i)
  uniq s m w := by
    ext x
    funext i
    exact DFunLike.congr_fun (congr_arg Hom.hom (w ⟨i⟩)) x

-- While we could use this to construct a `HasProducts (ModuleCat R)` instance,
-- we already have `HasLimits (ModuleCat R)` in `Algebra.Category.ModuleCat.Limits`.
variable [HasProduct Z]

/--
Definition of `piIsoPi` / `piIsoPi` 的定义

English:
definition piIsoPi
  signature: : ∏ᶜ Z ≅ ModuleCat.of R (forall i, Z i)
  body: limit.isoLimitCone ⟨_, productConeIsLimit Z⟩

中文:
定义 piIsoPi
  签名: : ∏ᶜ Z ≅ 模范畴.of R (对任意 i, Z i)
  定义体: limit.isoLimitCone ⟨_, productConeIsLimit Z⟩

Depends on / 依赖: isoLimitCone, limit.isoLimitCone, productConeIsLimit
-/
noncomputable def piIsoPi : ∏ᶜ Z ≅ ModuleCat.of R (forall i, Z i) :=
  limit.isoLimitCone ⟨_, productConeIsLimit Z⟩

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
/--
theorem `piIsoPi_inv_kernel_ι` / 定理 `piIsoPi_inv_kernel_ι`

English:
theorem piIsoPi_inv_kernel_ι
  given: (i : ι)
  proof: limit.isoLimitCone_inv_π _ _

@[simp, elementwise]

中文:
定理 piIsoPi_inv_kernel_ι
  条件: (i : ι)
  证明: limit.isoLimitCone_inv_π _ _

@[simp, elementwise]

Depends on / 依赖: limit.isoLimitCone_inv_
-/
theorem piIsoPi_inv_kernel_ι (i : ι) :
    (piIsoPi Z).inv ≫ Pi.π Z i = ofHom (LinearMap.proj i : (forall i : ι, Z i) ->ₗ[R] Z i) :=
  limit.isoLimitCone_inv_π _ _

@[simp, elementwise]
/--
theorem `piIsoPi_hom_ker_subtype` / 定理 `piIsoPi_hom_ker_subtype`

English:
theorem piIsoPi_hom_ker_subtype
  given: (i : ι)
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)

中文:
定理 piIsoPi_hom_ker_subtype
  条件: (i : ι)
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)

Depends on / 依赖: Discrete, Discrete.mk, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, conePointUniqueUpToIso_inv_comp, isLimit, limit.isLimit
-/
theorem piIsoPi_hom_ker_subtype (i : ι) :
    (piIsoPi Z).hom ≫ ofHom (LinearMap.proj i : (forall i : ι, Z i) ->ₗ[R] Z i) = Pi.π Z i :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)

end product

section coproduct

open DirectSum

variable [DecidableEq ι]

/--
Definition of `coproductCocone` / `coproductCocone` 的定义

English:
definition coproductCocone
  signature: : Cofan Z
  body: Cofan.mk (ModuleCat.of R (⨁ i : ι, Z i)) fun i => ofHom (DirectSum.lof R ι (fun i => Z i) i)

中文:
定义 coproductCocone
  签名: : Cofan Z
  定义体: Cofan.mk (ModuleCat.of R (⨁ i : ι, Z i)) fun i => ofHom (DirectSum.lof R ι (fun i => Z i) i)

Depends on / 依赖: Cofan.mk, DirectSum, DirectSum.lof, ModuleCat, ModuleCat.of
-/
def coproductCocone : Cofan Z :=
  Cofan.mk (ModuleCat.of R (⨁ i : ι, Z i)) fun i => ofHom (DirectSum.lof R ι (fun i => Z i) i)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coproductCoconeIsColimit` / `coproductCoconeIsColimit` 的定义

English:
definition coproductCoconeIsColimit
  signature: : IsColimit (coproductCocone Z) where
  body: ofHom DirectSum.toModule R ι _ fun i => (s.ι.app ⟨i⟩).hom
  fac := by
    rintro s ⟨i⟩
    ext (x : Z i)
    simpa only [Discrete.functor_obj_eq_as, coproductCocone, Cofan.mk_pt, Functor.const_obj_obj,
      Cofan.mk_ι_app, hom_comp, LinearMap.coe_comp, Function.comp_apply] using!
      DirectSum.toModule_lof (ι := ι) R (M := fun i => Z i) i x
  uniq := by
    rintro s f h
    ext : 1
    refine DirectSum.linearMap_ext _ fun i => ?_
    ext x
    simpa only [LinearMap.coe_comp, Function.comp_apply, hom_ofHom, toModule_lof] using!
      congr($(h ⟨i⟩) x)

中文:
定义 coproductCoconeIsColimit
  签名: : 是余极限 (coproductCocone Z) where
  定义体: ofHom DirectSum.toModule R ι _ fun i => (s.ι.app ⟨i⟩).hom
  fac := by
    rintro s ⟨i⟩
    ext (x : Z i)
    simpa only [Discrete.functor_obj_eq_as, coproductCocone, Cofan.mk_pt, Functor.const_obj_obj,
      Cofan.mk_ι_app, hom_comp, LinearMap.coe_comp, Function.comp_apply] using!
      DirectSum.toModule_lof (ι := ι) R (M := fun i => Z i) i x
  uniq := by
    rintro s f h
    ext : 1
    refine DirectSum.linearMap_ext _ fun i => ?_
    ext x
    simpa only [LinearMap.coe_comp, Function.comp_apply, hom_ofHom, toModule_lof] using!
      congr($(h ⟨i⟩) x)

Depends on / 依赖: DirectSum, DirectSum.toModule, toModule
-/
def coproductCoconeIsColimit : IsColimit (coproductCocone Z) where
desc s := ofHom DirectSum.toModule R ι _ fun i => (s.ι.app ⟨i⟩).hom
  fac := by
    rintro s ⟨i⟩
    ext (x : Z i)
    simpa only [Discrete.functor_obj_eq_as, coproductCocone, Cofan.mk_pt, Functor.const_obj_obj,
      Cofan.mk_ι_app, hom_comp, LinearMap.coe_comp, Function.comp_apply] using!
      DirectSum.toModule_lof (ι := ι) R (M := fun i => Z i) i x
  uniq := by
    rintro s f h
    ext : 1
    refine DirectSum.linearMap_ext _ fun i => ?_
    ext x
    simpa only [LinearMap.coe_comp, Function.comp_apply, hom_ofHom, toModule_lof] using!
      congr($(h ⟨i⟩) x)

variable [HasCoproduct Z]

/--
Definition of `coprodIsoDirectSum` / `coprodIsoDirectSum` 的定义

English:
definition coprodIsoDirectSum
  signature: : ∐ Z ≅ ModuleCat.of R (⨁ i, Z i)
  body: colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit Z⟩

@[simp, elementwise]

中文:
定义 coprodIsoDirectSum
  签名: : ∐ Z ≅ 模范畴.of R (⨁ i, Z i)
  定义体: colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit Z⟩

@[simp, elementwise]

Depends on / 依赖: colimit, colimit.isoColimitCocone, coproductCoconeIsColimit, isoColimitCocone
-/
noncomputable def coprodIsoDirectSum : ∐ Z ≅ ModuleCat.of R (⨁ i, Z i) :=
  colimit.isoColimitCocone ⟨_, coproductCoconeIsColimit Z⟩

@[simp, elementwise]
/--
theorem `ι_coprodIsoDirectSum_hom` / 定理 `ι_coprodIsoDirectSum_hom`

English:
theorem ι_coprodIsoDirectSum_hom
  given: (i : ι)
  proof: colimit.isoColimitCocone_ι_hom _ _

@[simp, elementwise]

中文:
定理 ι_coprodIsoDirectSum_hom
  条件: (i : ι)
  证明: colimit.isoColimitCocone_ι_hom _ _

@[simp, elementwise]

Depends on / 依赖: FunLike, colimit, colimit.isoColimitCocone_
-/
theorem ι_coprodIsoDirectSum_hom (i : ι) :
    Sigma.ι Z i ≫ (coprodIsoDirectSum Z).hom = ofHom (DirectSum.lof R ι (fun i => Z i) i) :=
  colimit.isoColimitCocone_ι_hom _ _

@[simp, elementwise]
/--
theorem `lof_coprodIsoDirectSum_inv` / 定理 `lof_coprodIsoDirectSum_inv`

English:
theorem lof_coprodIsoDirectSum_inv
  given: (i : ι)
  proof: (coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _

中文:
定理 lof_coprodIsoDirectSum_inv
  条件: (i : ι)
  证明: (coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _

Depends on / 依赖: colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, coproductCoconeIsColimit, isColimit
-/
theorem lof_coprodIsoDirectSum_inv (i : ι) :
    ofHom (DirectSum.lof R ι (fun i => Z i) i) ≫ (coprodIsoDirectSum Z).inv = Sigma.ι Z i :=
  (coproductCoconeIsColimit Z).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) _

end coproduct

end ModuleCat
