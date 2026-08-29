/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Homology of simplicial sets in degree 0

The main definition in this file is `SSet.homology₀Iso` which is
an isomorphism `X.homology R 0 ≅ ∐ (fun (_ : π₀ X) ↦ R)` for any simplicial
set `X`.

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits AlgebraicTopology Simplicial TypeCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

namespace SSet

variable (X : SSet) (R : C)

/--
Definition of `π₀.fromChainComplexXZero` / `π₀.fromChainComplexXZero` 的定义

English:
definition π₀.fromChainComplexXZero
  signature: :
  body: (sigmaConst.obj _).map (↾π₀.mk)

中文:
定义 π₀.fromChainComplexXZero
  签名: :
  定义体: (sigmaConst.obj _).map (↾π₀.mk)

Depends on / 依赖: sigmaConst, sigmaConst.obj
-/
noncomputable def π₀.fromChainComplexXZero :
    (X.chainComplex R).X 0 ⟶ ∐ (fun (_ : π₀ X) => R) :=
  (sigmaConst.obj _).map (↾π₀.mk)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `π₀.comp_fromChainComplexXZero` / 引理 `π₀.comp_fromChainComplexXZero`

English:
lemma π₀.comp_fromChainComplexXZero
  given: (x : X _⦋0⦌)
  proof: by
  simp [π₀.fromChainComplexXZero, ιChainComplex]

@[reassoc (attr := simp)]

中文:
引理 π₀.comp_fromChainComplexXZero
  条件: (x : X _⦋0⦌)
  证明: by
  simp [π₀.fromChainComplexXZero, ιChainComplex]

@[reassoc (attr := simp)]

Depends on / 依赖: fromChainComplexXZero
-/
lemma π₀.comp_fromChainComplexXZero (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ π₀.fromChainComplexXZero X R =
    Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) := by
  simp [π₀.fromChainComplexXZero, ιChainComplex]

@[reassoc (attr := simp)]
/--
lemma `π₀.d_fromChainComplexXZero` / 引理 `π₀.d_fromChainComplexXZero`

English:
lemma π₀.d_fromChainComplexXZero
  given: (n : Nat)
  proof: by
  by_cases! hn : n != 1
  · rw [HomologicalComplex.shape _ _ _ (by simp; lia), zero_comp]
  · subst hn
    ext x
    simp [π₀.sound (Edge.mk' x)]

中文:
引理 π₀.d_fromChainComplexXZero
  条件: (n : 自然数)
  证明: by
  by_cases! hn : n != 1
  · rw [HomologicalComplex.shape _ _ _ (by simp; lia), zero_comp]
  · subst hn
    ext x
    simp [π₀.sound (Edge.mk' x)]

Depends on / 依赖: Edge.mk, HomologicalComplex, HomologicalComplex.shape, zero_comp
-/
lemma π₀.d_fromChainComplexXZero (n : Nat) :
    (X.chainComplex R).d n 0 ≫ π₀.fromChainComplexXZero X R = 0 := by
  by_cases! hn : n != 1
  · rw [HomologicalComplex.shape _ _ _ (by simp; lia), zero_comp]
  · subst hn
    ext x
    simp [π₀.sound (Edge.mk' x)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCokernelCoforkChainComplexDOneZero` / `isColimitCokernelCoforkChainComplexDOneZero` 的定义

English:
definition isColimitCokernelCoforkChainComplexDOneZero
  signature: :
  body: by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    (Preadditive.isColimitCokernelCoforkOfCofork
      ((isColimitMapCoconeCoforkEquiv _ _).1
        (isColimitOfPreserves (sigmaConst.obj R) X.isColimitCoforkπ₀)))
  · refine parallelPair.ext (-Iso.refl _) (Iso.refl _) ?_ (by simp)
    simp [c

中文:
定义 isColimitCokernelCoforkChainComplexDOneZero
  签名: :
  定义体: by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    (Preadditive.isColimitCokernelCoforkOfCofork
      ((isColimitMapCoconeCoforkEquiv _ _).1
        (isColimitOfPreserves (sigmaConst.obj R) X.isColimitCoforkπ₀)))
  · refine parallelPair.ext (-Iso.refl _) (Iso.refl _) ?_ (by simp)
    simp [c

Depends on / 依赖: Cofork, Cofork.ext, IsColimit, IsColimit.equivOfNatIsoOfIso, Iso.refl, Preadditive, Preadditive.isColimitCokernelCoforkOfCofork, SSet.chainComplexFunctor, X.isColimitCofork, chainComplex, chainComplexFunctor, equivOfNatIsoOfIso, fromChainComplexXZero, isColimitCokernelCoforkOfCofork, isColimitMapCoconeCoforkEquiv, isColimitOfPreserves, parallelPair, parallelPair.ext, sigmaConst, sigmaConst.obj
-/
noncomputable def isColimitCokernelCoforkChainComplexDOneZero :
    IsColimit (CokernelCofork.ofπ _ (π₀.d_fromChainComplexXZero X R 1)) := by
  refine (IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    (Preadditive.isColimitCokernelCoforkOfCofork
      ((isColimitMapCoconeCoforkEquiv _ _).1
        (isColimitOfPreserves (sigmaConst.obj R) X.isColimitCoforkπ₀)))
  · refine parallelPair.ext (-Iso.refl _) (Iso.refl _) ?_ (by simp)
    simp [chainComplex, SSet.chainComplexFunctor, sub_eq_neg_add]
  · refine Cofork.ext (Iso.refl _) ?_
    ext
    simp [chainComplex, SSet.chainComplexFunctor, π₀.fromChainComplexXZero]

/-- A homology data saying that the singular homology in degree `0`
of a simplicial set with coefficients in `R` identify to a coproduct
of copies of `X` indexed by `π₀ X`. -/
@[simps! left_K left_H right_Q right_H]
/--
Definition of `homologyData₀` / `homologyData₀` 的定义

English:
definition homologyData₀
  signature: :
  body: ShortComplex.HomologyData.ofIsColimitCokernelCofork _ (by cat_disch) _
    (isColimitCokernelCoforkChainComplexDOneZero X R)

中文:
定义 homologyData₀
  签名: :
  定义体: ShortComplex.HomologyData.ofIsColimitCokernelCofork _ (by cat_disch) _
    (isColimitCokernelCoforkChainComplexDOneZero X R)

Depends on / 依赖: HomologyData, ShortComplex, ShortComplex.HomologyData.ofIsColimitCokernelCofork, cat_disch, isColimitCokernelCoforkChainComplexDOneZero, ofIsColimitCokernelCofork
-/
noncomputable def homologyData₀ :
    ((X.chainComplex R).sc' 1 0 0).HomologyData :=
  ShortComplex.HomologyData.ofIsColimitCokernelCofork _ (by cat_disch) _
    (isColimitCokernelCoforkChainComplexDOneZero X R)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `homologyData₀_left_π` / 引理 `homologyData₀_left_π`

English:
lemma homologyData₀_left_π
  proof: rfl

中文:
引理 homologyData₀_left_π
  证明: rfl
-/
lemma homologyData₀_left_π :
    dsimp% (X.homologyData₀ R).left.π = π₀.fromChainComplexXZero X R := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `homologyData₀_left_i` / 引理 `homologyData₀_left_i`

English:
lemma homologyData₀_left_i
  proof: rfl

中文:
引理 homologyData₀_left_i
  证明: rfl
-/
lemma homologyData₀_left_i :
    dsimp% (X.homologyData₀ R).left.i = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `homologyData₀_left_liftK` / 引理 `homologyData₀_left_liftK`

English:
lemma homologyData₀_left_liftK
  given: {T : C} (f : T ⟶ (X.chainComplex R).X 0)
  proof: ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_liftK ..

中文:
引理 homologyData₀_left_liftK
  条件: {T : C} (f : T ⟶ (X.chainComplex R).X 0)
  证明: ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_liftK ..

Depends on / 依赖: LeftHomologyData, ShortComplex, ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_liftK, ofIsColimitCokernelCofork_liftK
-/
lemma homologyData₀_left_liftK {T : C} (f : T ⟶ (X.chainComplex R).X 0) :
    dsimp% (X.homologyData₀ R).left.liftK f (by cat_disch) = f :=
  ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_liftK ..

variable [CategoryWithHomology C]

/--
Definition of `homology₀Iso` / `homology₀Iso` 的定义

English:
definition homology₀Iso
  signature: :
  body: ShortComplex.homologyMapIso (HomologicalComplex.isoSc' _ 1 0 0 (by simp) (by simp)) ≪≫
    (X.homologyData₀ R).left.homologyIso

中文:
定义 homology₀Iso
  签名: :
  定义体: ShortComplex.homologyMapIso (HomologicalComplex.isoSc' _ 1 0 0 (by simp) (by simp)) ≪≫
    (X.homologyData₀ R).left.homologyIso

Depends on / 依赖: HomologicalComplex, HomologicalComplex.isoSc, ShortComplex, ShortComplex.homologyMapIso, X.homologyData, homologyIso, homologyMapIso, left.homologyIso
-/
noncomputable def homology₀Iso :
    X.homology R 0 ≅ ∐ (fun (_ : π₀ X) => R) :=
  ShortComplex.homologyMapIso (HomologicalComplex.isoSc' _ 1 0 0 (by simp) (by simp)) ≪≫
    (X.homologyData₀ R).left.homologyIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom` / 引理 `liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom`

English:
lemma liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
  given: (x : X _⦋0⦌)
  proof: by
  simp [homology₀Iso, HomologicalComplex.homologyπ, SSet.homology,
    HomologicalComplex.liftCycles]

中文:
引理 liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
  条件: (x : X _⦋0⦌)
  证明: by
  simp [homology₀Iso, HomologicalComplex.homologyπ, SSet.homology,
    HomologicalComplex.liftCycles]
-/
lemma liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom (x : X _⦋0⦌) :
    (X.chainComplex R).liftCycles (k := X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex R).homologyπ 0 ≫ (X.homology₀Iso R).hom =
    Sigma.ι (fun (_ : π₀ X) => R) (π₀.mk x) := by
  simp [homology₀Iso, HomologicalComplex.homologyπ, SSet.homology,
    HomologicalComplex.liftCycles]

/--
Definition of `homology₀ε` / `homology₀ε` 的定义

English:
definition homology₀ε
  signature: : X.homology R 0 ⟶ R
  body: (X.homology₀Iso R).hom ≫ Sigma.desc (fun _ => 𝟙 R)

中文:
定义 homology₀ε
  签名: : X.homology R 0 ⟶ R
  定义体: (X.homology₀Iso R).hom ≫ Sigma.desc (fun _ => 𝟙 R)

Depends on / 依赖: Sigma.desc, X.homology
-/
noncomputable def homology₀ε : X.homology R 0 ⟶ R :=
  (X.homology₀Iso R).hom ≫ Sigma.desc (fun _ => 𝟙 R)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `liftCycles_ιChainComplex_homologyπ_homology₀ε` / 引理 `liftCycles_ιChainComplex_homologyπ_homology₀ε`

English:
lemma liftCycles_ιChainComplex_homologyπ_homology₀ε
  given: (x : X _⦋0⦌)
  proof: by
  simp [homology₀ε]

中文:
引理 liftCycles_ιChainComplex_homologyπ_homology₀ε
  条件: (x : X _⦋0⦌)
  证明: by
  simp [homology₀ε]
-/
lemma liftCycles_ιChainComplex_homologyπ_homology₀ε (x : X _⦋0⦌) :
    (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex R).homologyπ 0 ≫ X.homology₀ε R = 𝟙 R := by
  simp [homology₀ε]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.IsConnected]
  signature: : IsIso (X.homology₀ε R)
  body: by
  dsimp [homology₀ε]
  simp only [isIso_comp_left_iff]
  let x : π₀ X := Classical.arbitrary _
  refine ⟨Sigma.ι (fun _ => R) x, ?_, by simp⟩
  ext y
  obtain rfl : x = y := by subsingleton
  simp

中文:
实例 [X.IsConnected]
  签名: : IsIso (X.homology₀ε R)
  定义体: by
  dsimp [homology₀ε]
  simp only [isIso_comp_left_iff]
  let x : π₀ X := Classical.arbitrary _
  refine ⟨Sigma.ι (fun _ => R) x, ?_, by simp⟩
  ext y
  obtain rfl : x = y := by subsingleton
  simp

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, isIso_comp_left_iff, subsingleton
-/
instance [X.IsConnected] : IsIso (X.homology₀ε R) := by
  dsimp [homology₀ε]
  simp only [isIso_comp_left_iff]
  let x : π₀ X := Classical.arbitrary _
  refine ⟨Sigma.ι (fun _ => R) x, ?_, by simp⟩
  ext y
  obtain rfl : x = y := by subsingleton
  simp

end SSet
