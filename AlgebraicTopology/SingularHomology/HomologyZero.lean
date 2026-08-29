/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Singular homology in degree 0

The main definition in this file is `TopCat.singularHomology₀Iso` which is an
isomorphism `((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) ↦ R)`
for any `X : TopCat`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits AlgebraicTopology Simplicial

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

namespace TopCat

variable (X : TopCat.{w}) (R : C)

/--
Definition of `singularHomology₀Iso` / `singularHomology₀Iso` 的定义

English:
definition singularHomology₀Iso
  signature: :
  body: SSet.homology₀Iso _ _ ≪≫
    (sigmaConst.obj R).mapIso zerothHomotopyEquiv.toIso.symm

中文:
定义 singularHomology₀Iso
  签名: :
  定义体: SSet.homology₀Iso _ _ ≪≫
    (sigmaConst.obj R).mapIso zerothHomotopyEquiv.toIso.symm

Depends on / 依赖: SSet.homology, mapIso, sigmaConst, sigmaConst.obj, zerothHomotopyEquiv, zerothHomotopyEquiv.toIso.symm
-/
noncomputable def singularHomology₀Iso :
    ((singularHomologyFunctor C 0).obj R).obj X ≅ ∐ (fun (_ : ZerothHomotopy X) => R) :=
  SSet.homology₀Iso _ _ ≪≫
    (sigmaConst.obj R).mapIso zerothHomotopyEquiv.toIso.symm

/--
Definition of `singularHomology₀ε` / `singularHomology₀ε` 的定义

English:
definition singularHomology₀ε
  signature: :
  body: SSet.homology₀ε _ _

中文:
定义 singularHomology₀ε
  签名: :
  定义体: SSet.homology₀ε _ _

Depends on / 依赖: SSet.homology
-/
noncomputable def singularHomology₀ε :
    ((singularHomologyFunctor C 0).obj R).obj X ⟶ R :=
  SSet.homology₀ε _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `singularHomology₀Iso_sigma_desc_id` / 引理 `singularHomology₀Iso_sigma_desc_id`

English:
lemma singularHomology₀Iso_sigma_desc_id
  proof: by
  dsimp only [singularHomology₀Iso, singularHomology₀ε, SSet.homology₀ε]
  cat_disch

中文:
引理 singularHomology₀Iso_sigma_desc_id
  证明: by
  dsimp only [singularHomology₀Iso, singularHomology₀ε, SSet.homology₀ε]
  cat_disch

Depends on / 依赖: SSet.homology, cat_disch
-/
lemma singularHomology₀Iso_sigma_desc_id :
    (singularHomology₀Iso X R).hom ≫ Sigma.desc (fun _ => 𝟙 R) = singularHomology₀ε X R := by
  dsimp only [singularHomology₀Iso, singularHomology₀ε, SSet.homology₀ε]
  cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PathConnectedSpace
  signature: X] : IsIso (X.singularHomology₀ε R)
  body: inferInstanceAs (IsIso ((toSSet.obj X).homology₀ε R))

中文:
实例 [PathConnectedSpace
  签名: X] : IsIso (X.singularHomology₀ε R)
  定义体: inferInstanceAs (IsIso ((toSSet.obj X).homology₀ε R))

Depends on / 依赖: toSSet, toSSet.obj
-/
instance [PathConnectedSpace X] : IsIso (X.singularHomology₀ε R) :=
  inferInstanceAs (IsIso ((toSSet.obj X).homology₀ε R))

end TopCat
