/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# (Co)products in functor categories

Given `f : α → D ⥤ C`, we prove the isomorphisms
`(∏ᶜ f).obj d ≅ ∏ᶜ (fun s => (f s).obj d)` and `(∐ f).obj d ≅ ∐ (fun s => (f s).obj d)`.

-/

@[expose] public section

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {α : Type w}

section Product

variable [HasLimitsOfShape (Discrete α) C]

/--
Definition of `piObjIso` / `piObjIso` 的定义

English:
definition piObjIso
  signature: (f : α -> D ⥤ C) (d : D)
  body: limitObjIsoLimitCompEvaluation (Discrete.functor f) d ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

中文:
定义 piObjIso
  签名: (f : α -> D ⥤ C) (d : D)
  定义体: limitObjIsoLimitCompEvaluation (Discrete.functor f) d ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

Depends on / 依赖: Discrete, Discrete.compNatIsoDiscrete, Discrete.functor, HasLimit, HasLimit.isoOfNatIso, compNatIsoDiscrete, functor, isoOfNatIso, limitObjIsoLimitCompEvaluation
-/
noncomputable def piObjIso (f : α -> D ⥤ C) (d : D) : (∏ᶜ f).obj d ≅ ∏ᶜ (fun s => (f s).obj d) :=
  limitObjIsoLimitCompEvaluation (Discrete.functor f) d ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `piObjIso_hom_comp_π` / 定理 `piObjIso_hom_comp_π`

English:
theorem piObjIso_hom_comp_π
  given: (f : α -> D ⥤ C) (d : D) (s : α)
  proof: by
  simp [piObjIso]

中文:
定理 piObjIso_hom_comp_π
  条件: (f : α -> D ⥤ C) (d : D) (s : α)
  证明: by
  simp [piObjIso]

Depends on / 依赖: piObjIso
-/
theorem piObjIso_hom_comp_π (f : α -> D ⥤ C) (d : D) (s : α) :
    (piObjIso f d).hom ≫ Pi.π (fun s => (f s).obj d) s = (Pi.π f s).app d := by
  simp [piObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `piObjIso_inv_comp_π` / 定理 `piObjIso_inv_comp_π`

English:
theorem piObjIso_inv_comp_π
  given: (f : α -> D ⥤ C) (d : D) (s : α)
  proof: by
  simp [piObjIso]

中文:
定理 piObjIso_inv_comp_π
  条件: (f : α -> D ⥤ C) (d : D) (s : α)
  证明: by
  simp [piObjIso]

Depends on / 依赖: piObjIso
-/
theorem piObjIso_inv_comp_π (f : α -> D ⥤ C) (d : D) (s : α) :
    (piObjIso f d).inv ≫ (Pi.π f s).app d = Pi.π (fun s => (f s).obj d) s := by
  simp [piObjIso]

end Product

section Coproduct

variable [HasColimitsOfShape (Discrete α) C]

/--
Definition of `sigmaObjIso` / `sigmaObjIso` 的定义

English:
definition sigmaObjIso
  signature: (f : α -> D ⥤ C) (d : D)
  body: colimitObjIsoColimitCompEvaluation (Discrete.functor f) d ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

中文:
定义 sigmaObjIso
  签名: (f : α -> D ⥤ C) (d : D)
  定义体: colimitObjIsoColimitCompEvaluation (Discrete.functor f) d ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

Depends on / 依赖: Discrete, Discrete.compNatIsoDiscrete, Discrete.functor, HasColimit, HasColimit.isoOfNatIso, colimitObjIsoColimitCompEvaluation, compNatIsoDiscrete, functor, isoOfNatIso
-/
noncomputable def sigmaObjIso (f : α -> D ⥤ C) (d : D) : (∐ f).obj d ≅ ∐ (fun s => (f s).obj d) :=
  colimitObjIsoColimitCompEvaluation (Discrete.functor f) d ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_comp_sigmaObjIso_hom` / 定理 `ι_comp_sigmaObjIso_hom`

English:
theorem ι_comp_sigmaObjIso_hom
  given: (f : α -> D ⥤ C) (d : D) (s : α)
  proof: by
  simp [sigmaObjIso]

中文:
定理 ι_comp_sigmaObjIso_hom
  条件: (f : α -> D ⥤ C) (d : D) (s : α)
  证明: by
  simp [sigmaObjIso]

Depends on / 依赖: sigmaObjIso
-/
theorem ι_comp_sigmaObjIso_hom (f : α -> D ⥤ C) (d : D) (s : α) :
    (Sigma.ι f s).app d ≫ (sigmaObjIso f d).hom = Sigma.ι (fun s => (f s).obj d) s := by
  simp [sigmaObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_comp_sigmaObjIso_inv` / 定理 `ι_comp_sigmaObjIso_inv`

English:
theorem ι_comp_sigmaObjIso_inv
  given: (f : α -> D ⥤ C) (d : D) (s : α)
  proof: by
  simp [sigmaObjIso]

中文:
定理 ι_comp_sigmaObjIso_inv
  条件: (f : α -> D ⥤ C) (d : D) (s : α)
  证明: by
  simp [sigmaObjIso]

Depends on / 依赖: sigmaObjIso
-/
theorem ι_comp_sigmaObjIso_inv (f : α -> D ⥤ C) (d : D) (s : α) :
    Sigma.ι (fun s => (f s).obj d) s ≫ (sigmaObjIso f d).inv = (Sigma.ι f s).app d := by
  simp [sigmaObjIso]

end Coproduct

end CategoryTheory.Limits
