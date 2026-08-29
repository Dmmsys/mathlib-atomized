/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Pushout-products of simplicial sets

Results about pushout-products and pullback-homs in the category of simplicial sets.

-/

@[expose] public section

universe v u

namespace SSet

open CategoryTheory MonoidalCategory

variable {X Y : SSet.{u}} (S : X.Subcomplex) (T : Y.Subcomplex)

namespace Subcomplex

namespace unionProd

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion `(S.unionProd T).toSSet ⟶ X ⊗ Y` is isomorphic to the pushout-product
`S.ι □ T.ι`. -/
@[simps! -isSimp]
noncomputable
/--
Definition of `ιIso` / `ιIso` 的定义

English:
definition ιIso
  signature: : Arrow.mk (S.unionProd T).ι ≅ S.ι □ T.ι
  body: Arrow.isoMk' _ _ (isPushout S T).isoPushout (Iso.refl _)
    (by
      apply (unionProd.isPushout S T).hom_ext <;>
      simp [Limits.pushout.inl_desc, Limits.pushout.inr_desc])

中文:
定义 ιIso
  签名: : Arrow.mk (S.unionProd T).ι ≅ S.ι □ T.ι
  定义体: Arrow.isoMk' _ _ (isPushout S T).isoPushout (Iso.refl _)
    (by
      apply (unionProd.isPushout S T).hom_ext <;>
      simp [Limits.pushout.inl_desc, Limits.pushout.inr_desc])

Depends on / 依赖: Arrow.isoMk, Iso.refl, Limits, Limits.pushout.inl_desc, Limits.pushout.inr_desc, hom_ext, inl_desc, inr_desc, isPushout, isoPushout, pushout, unionProd, unionProd.isPushout
-/
def ιIso : Arrow.mk (S.unionProd T).ι ≅ S.ι □ T.ι :=
  Arrow.isoMk' _ _ (isPushout S T).isoPushout (Iso.refl _)
    (by
      apply (unionProd.isPushout S T).hom_ext <;>
      simp [Limits.pushout.inl_desc, Limits.pushout.inr_desc])

/-- Given subcomplexes `S` and `T` of simplicial sets, this if a `Functor.PushoutObjObj`
structure for the chosen binary products on `SSet`, with point `S.unionProd T`. -/
@[simps]
/--
Definition of `pushoutObjObj` / `pushoutObjObj` 的定义

English:
definition pushoutObjObj
  signature: : (curriedTensor _).PushoutObjObj S.ι T.ι where
  body: S.unionProd T
  inl := unionProd.ι₁ S T
  inr := unionProd.ι₂ S T
  isPushout := unionProd.isPushout S T
  ι := (S.unionProd T).ι

中文:
定义 pushoutObjObj
  签名: : (curriedTensor _).PushoutObjObj S.ι T.ι where
  定义体: S.unionProd T
  inl := unionProd.ι₁ S T
  inr := unionProd.ι₂ S T
  isPushout := unionProd.isPushout S T
  ι := (S.unionProd T).ι

Depends on / 依赖: S.unionProd, unionProd
-/
noncomputable def pushoutObjObj : (curriedTensor _).PushoutObjObj S.ι T.ι where
  pt := S.unionProd T
  inl := unionProd.ι₁ S T
  inr := unionProd.ι₂ S T
  isPushout := unionProd.isPushout S T
  ι := (S.unionProd T).ι

end unionProd

end Subcomplex

end SSet
