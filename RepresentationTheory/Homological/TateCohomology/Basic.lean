/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yaël Dillies
-/
module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence


/-!
# Tate Cohomology

This file defines the Tate cohomology of finite groups by taking homology of the Tate complex. We
define the Tate complex by connecting the inhomogeneous chain complex with the inhomogeneous
cochain complex using the norm map.

## Key definitions

* `Rep.tateNorm`: the map induced by the norm map from the zeroth term of the inhomogeneous chain
  complex to the zeroth term of the inhomogeneous cochain complex.

* `tateComplex`: the Tate complex defined by connecting the inhomogeneous chain complex and
  cochain complex using the Tate norm.

* `tateComplexFunctor`: the functor taking a representation of `G` to its Tate complex.

* `tateCohomologyFunctor`: the functor taking a representation of `G` to its `n`-th Tate
  cohomology group.

* `isoGroupCohomology`: the isomorphism between the `n`-th Tate cohomology and
  `n`-th group cohomology for `n : ℕ` non-zero.

* `isoGroupHomology`: the isomorphism between the `-n-1`-th Tate cohomology and `n`-th group
  homology for `n : ℕ` non-zero.

## Main Results

* `δ_naturality`: the naturality of the connecting homomorphism in the long exact sequence of Tate
  cohomology.

## Tags

Tate cohomology, homological algebra

This file comes from a collaborative work in 2025 ClassFieldTheory workshop, see
https://github.com/kbuzzard/ClassFieldTheory/ for more information.
-/

@[expose] public noncomputable section

universe u v

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (M : Rep R G) {X Y : Rep R G}

open CategoryTheory groupCohomology groupHomology

/--
Definition of `Rep.tateNorm` / `Rep.tateNorm` 的定义

English:
definition Rep.tateNorm
  signature: : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0
  body: (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom ≫ (cochainsIso₀ M).inv

中文:
定义 Rep.tateNorm
  签名: : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0
  定义体: (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom ≫ (cochainsIso₀ M).inv

Depends on / 依赖: M.norm.toModuleCatHom, toModuleCatHom
-/
def Rep.tateNorm : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom ≫ (cochainsIso₀ M).inv

/--
lemma `Rep.tateNorm_eq` / 引理 `Rep.tateNorm_eq`

English:
lemma Rep.tateNorm_eq
  proof: by
  ext
  simp_all [tateNorm, chainsIso₀, cochainsIso₀, Unique.eq_default]

@[reassoc (attr := simp), elementwise]

中文:
引理 Rep.tateNorm_eq
  证明: by
  ext
  simp_all [tateNorm, chainsIso₀, cochainsIso₀, Unique.eq_default]

@[reassoc (attr := simp), elementwise]

Depends on / 依赖: Unique, Unique.eq_default, eq_default, tateNorm
-/
lemma Rep.tateNorm_eq :
    M.tateNorm = ModuleCat.ofHom (Finsupp.lsum R fun _ => LinearMap.pi fun _ => M.ρ.norm) := by
  ext
  simp_all [tateNorm, chainsIso₀, cochainsIso₀, Unique.eq_default]

@[reassoc (attr := simp), elementwise]
/--
lemma `Rep.norm_comp_d_eq_zero` / 引理 `Rep.norm_comp_d_eq_zero`

English:
lemma Rep.norm_comp_d_eq_zero
  statement: M.norm.toModuleCatHom ≫ d₀₁ M = 0
  proof: by
  ext
  simp [Pi.zero_apply _]

中文:
引理 Rep.norm_comp_d_eq_zero
  结论: M.norm.toModuleCatHom ≫ d₀₁ M = 0
  证明: by
  ext
  simp [Pi.zero_apply _]

Depends on / 依赖: Pi.zero_apply, zero_apply
-/
lemma Rep.norm_comp_d_eq_zero : M.norm.toModuleCatHom ≫ d₀₁ M = 0 := by
  ext
  simp [Pi.zero_apply _]

/--
lemma `Rep.tateNorm_comp_d` / 引理 `Rep.tateNorm_comp_d`

English:
lemma Rep.tateNorm_comp_d
  statement: tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0
  proof: by
  simp [tateNorm, eq_d₀₁_comp_inv M]

@[simp]

中文:
引理 Rep.tateNorm_comp_d
  结论: tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0
  证明: by
  simp [tateNorm, eq_d₀₁_comp_inv M]

@[simp]

Depends on / 依赖: tateNorm
-/
lemma Rep.tateNorm_comp_d : tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 := by
  simp [tateNorm, eq_d₀₁_comp_inv M]

@[simp]
/--
lemma `Rep.comp_eq_zero` / 引理 `Rep.comp_eq_zero`

English:
lemma Rep.comp_eq_zero
  statement: d₁₀ M ≫ M.norm.toModuleCatHom = 0
  proof: by
  ext
  simp [d₁₀_single M]

中文:
引理 Rep.comp_eq_zero
  结论: d₁₀ M ≫ M.norm.toModuleCatHom = 0
  证明: by
  ext
  simp [d₁₀_single M]
-/
lemma Rep.comp_eq_zero : d₁₀ M ≫ M.norm.toModuleCatHom = 0 := by
  ext
  simp [d₁₀_single M]

/--
lemma `Rep.d_comp_tateNorm` / 引理 `Rep.d_comp_tateNorm`

English:
lemma Rep.d_comp_tateNorm
  statement: (inhomogeneousChains M).d 1 0 ≫ M.tateNorm = 0
  proof: by
  simp only [tateNorm, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
  simp [← comp_d₁₀_eq _]

中文:
引理 Rep.d_comp_tateNorm
  结论: (inhomogeneousChains M).d 1 0 ≫ M.tateNorm = 0
  证明: by
  simp only [tateNorm, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
  simp [← comp_d₁₀_eq _]

Depends on / 依赖: Category, Category.assoc, Preadditive, Preadditive.IsIso.comp_right_eq_zero, comp_right_eq_zero, tateNorm
-/
lemma Rep.d_comp_tateNorm : (inhomogeneousChains M).d 1 0 ≫ M.tateNorm = 0 := by
  simp only [tateNorm, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
  simp [← comp_d₁₀_eq _]

/-- The Tate norm connecting complexes of inhomogeneous chains and cochains. -/
@[simps]
/--
Definition of `tateComplexConnectData` / `tateComplexConnectData` 的定义

English:
definition tateComplexConnectData
  signature: :
  body: M.tateNorm
  comp_d₀ := Rep.d_comp_tateNorm _
  d₀_comp := Rep.tateNorm_comp_d _

中文:
定义 tateComplexConnectData
  签名: :
  定义体: M.tateNorm
  comp_d₀ := Rep.d_comp_tateNorm _
  d₀_comp := Rep.tateNorm_comp_d _

Depends on / 依赖: M.tateNorm, tateNorm
-/
def tateComplexConnectData :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := M.tateNorm
  comp_d₀ := Rep.d_comp_tateNorm _
  d₀_comp := Rep.tateNorm_comp_d _

/--
Definition of `tateComplex` / `tateComplex` 的定义

English:
abbreviation tateComplex
  signature: : CochainComplex (ModuleCat R) Int
  body: CochainComplex.ConnectData.cochainComplex (tateComplexConnectData M)

中文:
缩写 tateComplex
  签名: : CochainComplex (ModuleCat R) 整数
  定义体: CochainComplex.ConnectData.cochainComplex (tateComplexConnectData M)

Depends on / 依赖: CochainComplex, CochainComplex.ConnectData.cochainComplex, ConnectData, cochainComplex, tateComplexConnectData
-/
abbrev tateComplex : CochainComplex (ModuleCat R) Int :=
  CochainComplex.ConnectData.cochainComplex (tateComplexConnectData M)

/--
lemma `tateComplex_d_neg_one` / 引理 `tateComplex_d_neg_one`

English:
lemma tateComplex_d_neg_one
  statement: (tateComplex M).d (-1) 0 = M.tateNorm
  proof: rfl

中文:
引理 tateComplex_d_neg_one
  结论: (tateComplex M).d (-1) 0 = M.tateNorm
  证明: rfl
-/
lemma tateComplex_d_neg_one : (tateComplex M).d (-1) 0 = M.tateNorm := rfl

/--
lemma `tateComplex_d_ofNat` / 引理 `tateComplex_d_ofNat`

English:
lemma tateComplex_d_ofNat
  given: (n : Nat)
  proof: rfl

中文:
引理 tateComplex_d_ofNat
  条件: (n : 自然数)
  证明: rfl
-/
lemma tateComplex_d_ofNat (n : Nat) :
    (tateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

/--
lemma `tateComplex_d_neg` / 引理 `tateComplex_d_neg`

English:
lemma tateComplex_d_neg
  given: (n : Nat)
  proof: rfl

中文:
引理 tateComplex_d_neg
  条件: (n : 自然数)
  证明: rfl
-/
lemma tateComplex_d_neg (n : Nat) :
    (tateComplex M).d (-(n + 2 : Int)) (-(n + 1 : Int)) = (inhomogeneousChains M).d (n + 1) n := rfl

/-- The chain map on the Tate complex induced by a morphism of representations. -/
@[reducible]
/--
Definition of `tateComplex.map` / `tateComplex.map` 的定义

English:
definition tateComplex.map
  signature: (φ : X ⟶ Y)
  body: by
  refine CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsMap (.id G) φ) ?_
  ext
  simp [Rep.tateNorm_eq, Representation.norm, Rep.hom_comm_apply]

@[simp]

中文:
定义 tateComplex.map
  签名: (φ : X ⟶ Y)
  定义体: by
  refine CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsMap (.id G) φ) ?_
  ext
  simp [Rep.tateNorm_eq, Representation.norm, Rep.hom_comm_apply]

@[simp]

Depends on / 依赖: CochainComplex, CochainComplex.ConnectData.map, ConnectData, Rep.hom_comm_apply, Rep.tateNorm_eq, Representation, Representation.norm, chainsMap, cochainsMap, hom_comm_apply, tateNorm_eq
-/
def tateComplex.map (φ : X ⟶ Y) : tateComplex X ⟶ tateComplex Y := by
  refine CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsMap (.id G) φ) ?_
  ext
  simp [Rep.tateNorm_eq, Representation.norm, Rep.hom_comm_apply]

@[simp]
/--
lemma `tateComplex.map_zero` / 引理 `tateComplex.map_zero`

English:
lemma tateComplex.map_zero
  statement: tateComplex.map (0 : X ⟶ Y) = 0
  proof: by cat_disch

中文:
引理 tateComplex.map_zero
  结论: tateComplex.map (0 : X ⟶ Y) = 0
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma tateComplex.map_zero : tateComplex.map (0 : X ⟶ Y) = 0 := by cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
lemma `tateComplex.map_add` / 引理 `tateComplex.map_add`

English:
lemma tateComplex.map_add
  given: (f g : X ⟶ Y)
  statement: tateComplex.map (f + g) =
  proof: by
  ext (i | i) : 1
  · rfl
  · ext1
    simp only [CochainComplex.ConnectData.map_f, chainsMap_id_f_hom_eq_mapRange, Rep.add_hom,
      Representation.IntertwiningMap.add_toLinearMap, HomologicalComplex.add_f_apply,
      ModuleCat.hom_add]
    ext; simp

中文:
引理 tateComplex.map_add
  条件: (f g : X ⟶ Y)
  结论: tateComplex.map (f + g) =
  证明: by
  ext (i | i) : 1
  · rfl
  · ext1
    simp only [CochainComplex.ConnectData.map_f, chainsMap_id_f_hom_eq_mapRange, Rep.add_hom,
      Representation.IntertwiningMap.add_toLinearMap, HomologicalComplex.add_f_apply,
      ModuleCat.hom_add]
    ext; simp

Depends on / 依赖: CochainComplex, CochainComplex.ConnectData.map_f, ConnectData, HomologicalComplex, HomologicalComplex.add_f_apply, IntertwiningMap, ModuleCat, ModuleCat.hom_add, Rep.add_hom, Representation, Representation.IntertwiningMap.add_toLinearMap, add_f_apply, add_hom, add_toLinearMap, chainsMap_id_f_hom_eq_mapRange, hom_add, map_f
-/
lemma tateComplex.map_add (f g : X ⟶ Y) : tateComplex.map (f + g) =
    tateComplex.map f + tateComplex.map g := by
  ext (i | i) : 1
  · rfl
  · ext1
    simp only [CochainComplex.ConnectData.map_f, chainsMap_id_f_hom_eq_mapRange, Rep.add_hom,
      Representation.IntertwiningMap.add_toLinearMap, HomologicalComplex.add_f_apply,
      ModuleCat.hom_add]
    ext; simp

variable (R G) in
/-- The functor taking a representation of `G` to its Tate complex. -/
@[simps]
/--
Definition of `tateComplexFunctor` / `tateComplexFunctor` 的定义

English:
definition tateComplexFunctor
  signature: : Rep R G ⥤ CochainComplex (ModuleCat R) Int where
  body: tateComplex M
  map := tateComplex.map
  map_comp f g := by
    simp [tateComplex.map, CochainComplex.ConnectData.map_comp_map, ← chainsMap_comp]
    rfl

中文:
定义 tateComplexFunctor
  签名: : Rep R G ⥤ CochainComplex (ModuleCat R) 整数 where
  定义体: tateComplex M
  map := tateComplex.map
  map_comp f g := by
    simp [tateComplex.map, CochainComplex.ConnectData.map_comp_map, ← chainsMap_comp]
    rfl

Depends on / 依赖: tateComplex
-/
def tateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) Int where
  obj M := tateComplex M
  map := tateComplex.map
  map_comp f g := by
    simp [tateComplex.map, CochainComplex.ConnectData.map_comp_map, ← chainsMap_comp]
    rfl

/--
Definition of `tateCohomologyFunctor` / `tateCohomologyFunctor` 的定义

English:
definition tateCohomologyFunctor
  signature: (n : Int)
  body: tateComplexFunctor R G ⋙ HomologicalComplex.homologyFunctor _ _ n

中文:
定义 tateCohomologyFunctor
  签名: (n : 整数)
  定义体: tateComplexFunctor R G ⋙ HomologicalComplex.homologyFunctor _ _ n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyFunctor, homologyFunctor, tateComplexFunctor
-/
def tateCohomologyFunctor (n : Int) : Rep R G ⥤ ModuleCat R :=
  tateComplexFunctor R G ⋙ HomologicalComplex.homologyFunctor _ _ n

/--
Definition of `tateCohomology` / `tateCohomology` 的定义

English:
abbreviation tateCohomology
  signature: (n : Int)
  body: (tateCohomologyFunctor n).obj M

中文:
缩写 tateCohomology
  签名: (n : 整数)
  定义体: (tateCohomologyFunctor n).obj M

Depends on / 依赖: tateCohomologyFunctor
-/
abbrev tateCohomology (n : Int) : ModuleCat R := (tateCohomologyFunctor n).obj M

namespace TateCohomology

section Exact

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tateComplexFunctor (R := R) (G := G)).PreservesZeroMorphisms
  body: by simp

中文:
实例 :
  签名: (tateComplexFunctor (R := R) (G := G)).PreservesZeroMorphisms
  定义体: by simp

Depends on / 依赖: PreservesZeroMorphisms
-/
instance : (tateComplexFunctor (R := R) (G := G)).PreservesZeroMorphisms where
  map_zero X Y := by simp

/--
Definition of `tateComplex.evalNonneg` / `tateComplex.evalNonneg` 的定义

English:
definition tateComplex.evalNonneg
  signature: (n : Nat)
  body: .refl _

中文:
定义 tateComplex.evalNonneg
  签名: (n : 自然数)
  定义体: .refl _
-/
def tateComplex.evalNonneg (n : Nat) :
    tateComplexFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up Int) n ≅
    cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up Nat) n :=
  .refl _

/--
Definition of `tateComplex.evalNeg` / `tateComplex.evalNeg` 的定义

English:
definition tateComplex.evalNeg
  signature: (n : Nat)
  body: .refl _

中文:
定义 tateComplex.evalNeg
  签名: (n : 自然数)
  定义体: .refl _
-/
def tateComplex.evalNeg (n : Nat) : tateComplexFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R)
    (ComplexShape.up Int) (.negSucc n) ≅ chainsFunctor R G ⋙
    HomologicalComplex.eval (ModuleCat R) (ComplexShape.down Nat) n :=
  .refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tateComplexFunctor R G).PreservesZeroMorphisms

中文:
实例 :
  签名: (tateComplexFunctor R G).PreservesZeroMorphisms
-/
instance : (tateComplexFunctor R G).PreservesZeroMorphisms where

/--
lemma `map_tateComplexFunctor_shortExact` / 引理 `map_tateComplexFunctor_shortExact`

English:
lemma map_tateComplexFunctor_shortExact
  given: {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
  proof: by
  simp only [HomologicalComplex.shortExact_iff_degreewise_shortExact , ← ShortComplex.map_comp]
  rintro (_ | _)
  · exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso _ (tateComplex.evalNonneg _).symm)
 map_cochainsFunctor_eval_shortExact hS _
  · exact ShortComplex.shortExact_of_iso (

中文:
引理 map_tateComplexFunctor_shortExact
  条件: {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
  证明: by
  simp only [HomologicalComplex.shortExact_iff_degreewise_shortExact , ← ShortComplex.map_comp]
  rintro (_ | _)
  · exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso _ (tateComplex.evalNonneg _).symm)
 map_cochainsFunctor_eval_shortExact hS _
  · exact ShortComplex.shortExact_of_iso (

Depends on / 依赖: HomologicalComplex, HomologicalComplex.shortExact_iff_degreewise_shortExact, ShortComplex, ShortComplex.mapNatIso, ShortComplex.map_comp, ShortComplex.shortExact_of_iso, evalNeg, evalNonneg, mapNatIso, map_chainsFunctor_eval_shortExact, map_cochainsFunctor_eval_shortExact, map_comp, shortExact_iff_degreewise_shortExact, shortExact_of_iso, tateComplex, tateComplex.evalNeg, tateComplex.evalNonneg
-/
lemma map_tateComplexFunctor_shortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact) :
    (S.map (tateComplexFunctor R G)).ShortExact := by
  simp only [HomologicalComplex.shortExact_iff_degreewise_shortExact , ← ShortComplex.map_comp]
  rintro (_ | _)
  · exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso _ (tateComplex.evalNonneg _).symm)
 map_cochainsFunctor_eval_shortExact hS _
  · exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso _ (tateComplex.evalNeg _).symm)
 map_chainsFunctor_eval_shortExact hS _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (tateComplexFunctor R G).Additive
  body: tateComplex.map_add ..

中文:
实例 :
  签名: (tateComplexFunctor R G).Additive
  定义体: tateComplex.map_add ..

Depends on / 依赖: map_add, tateComplex, tateComplex.map_add
-/
instance : (tateComplexFunctor R G).Additive where
  map_add := tateComplex.map_add ..

/--
Instance `preservesFiniteLimits_tateComplexFunctor` / 实例 `preservesFiniteLimits_tateComplexFunctor`

English:
instance preservesFiniteLimits_tateComplexFunctor
  signature: :
  body: (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ => map_tateComplexFunctor_shortExact).1

中文:
实例 preservesFiniteLimits_tateComplexFunctor
  签名: :
  定义体: (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ => map_tateComplexFunctor_shortExact).1

Depends on / 依赖: exact_tfae, exact_tfae.out, map_tateComplexFunctor_shortExact, tateComplexFunctor
-/
instance preservesFiniteLimits_tateComplexFunctor :
    Limits.PreservesFiniteLimits (tateComplexFunctor R G) :=
  (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ => map_tateComplexFunctor_shortExact).1

/--
Instance `preservesFiniteColimits_tateComplexFunctor` / 实例 `preservesFiniteColimits_tateComplexFunctor`

English:
instance preservesFiniteColimits_tateComplexFunctor
  signature: :
  body: (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ => map_tateComplexFunctor_shortExact).2

中文:
实例 preservesFiniteColimits_tateComplexFunctor
  签名: :
  定义体: (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ => map_tateComplexFunctor_shortExact).2

Depends on / 依赖: exact_tfae, exact_tfae.out, map_tateComplexFunctor_shortExact, tateComplexFunctor
-/
instance preservesFiniteColimits_tateComplexFunctor :
    Limits.PreservesFiniteColimits (tateComplexFunctor R G) :=
  (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ => map_tateComplexFunctor_shortExact).2

end Exact

/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int)
  body: (map_tateComplexFunctor_shortExact hS).δ n (n + 1) rfl

中文:
缩写 δ
  签名: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : 整数)
  定义体: (map_tateComplexFunctor_shortExact hS).δ n (n + 1) rfl

Depends on / 依赖: map_tateComplexFunctor_shortExact
-/
noncomputable abbrev δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int) :
    tateCohomology S.X₃ n ⟶ tateCohomology S.X₁ (n + 1) :=
  (map_tateComplexFunctor_shortExact hS).δ n (n + 1) rfl

/--
lemma `map_δ` / 引理 `map_δ`

English:
lemma map_δ
  given: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int)
  proof: (map_tateComplexFunctor_shortExact hS).comp_δ _ _ _

中文:
引理 map_δ
  条件: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : 整数)
  证明: (map_tateComplexFunctor_shortExact hS).comp_δ _ _ _

Depends on / 依赖: map_tateComplexFunctor_shortExact
-/
lemma map_δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int) :
    (tateCohomologyFunctor n).map S.g ≫ δ hS n = 0 :=
  (map_tateComplexFunctor_shortExact hS).comp_δ _ _ _

/--
lemma `δ_map` / 引理 `δ_map`

English:
lemma δ_map
  given: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int)
  proof: (map_tateComplexFunctor_shortExact hS).δ_comp _ _ _

中文:
引理 δ_map
  条件: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : 整数)
  证明: (map_tateComplexFunctor_shortExact hS).δ_comp _ _ _

Depends on / 依赖: map_tateComplexFunctor_shortExact
-/
lemma δ_map {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int) :
    δ hS n ≫ (tateCohomologyFunctor (n + 1)).map S.f = 0 :=
  (map_tateComplexFunctor_shortExact hS).δ_comp _ _ _

/--
lemma `exact₃` / 引理 `exact₃`

English:
lemma exact₃
  given: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int)
  proof: (map_tateComplexFunctor_shortExact hS).homology_exact₃ ..

中文:
引理 exact₃
  条件: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : 整数)
  证明: (map_tateComplexFunctor_shortExact hS).homology_exact₃ ..

Depends on / 依赖: map_tateComplexFunctor_shortExact
-/
lemma exact₃ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int) :
    (ShortComplex.mk _ _ (map_δ hS n)).Exact :=
  (map_tateComplexFunctor_shortExact hS).homology_exact₃ ..

/--
lemma `exact₁` / 引理 `exact₁`

English:
lemma exact₁
  given: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int)
  proof: (map_tateComplexFunctor_shortExact hS).homology_exact₁ ..

中文:
引理 exact₁
  条件: {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : 整数)
  证明: (map_tateComplexFunctor_shortExact hS).homology_exact₁ ..

Depends on / 依赖: map_tateComplexFunctor_shortExact
-/
lemma exact₁ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : Int) :
    (ShortComplex.mk _ _ (δ_map hS n)).Exact :=
  (map_tateComplexFunctor_shortExact hS).homology_exact₁ ..

/--
lemma `δ_naturality` / 引理 `δ_naturality`

English:
lemma δ_naturality
  statement: {X1 X2 : ShortComplex (Rep R G)}
  proof: HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor R G).mapShortComplex.map F)
    (map_tateComplexFunctor_shortExact hX1) (map_tateComplexFunctor_shortExact hX2) i (i + 1) rfl

中文:
引理 δ_naturality
  结论: {X1 X2 : ShortComplex (Rep R G)}
  证明: HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor R G).mapShortComplex.map F)
    (map_tateComplexFunctor_shortExact hX1) (map_tateComplexFunctor_shortExact hX2) i (i + 1) rfl

Depends on / 依赖: HomologicalComplex, HomologicalComplex.HomologySequence, HomologySequence, mapShortComplex, mapShortComplex.map, map_tateComplexFunctor_shortExact, tateComplexFunctor
-/
lemma δ_naturality {X1 X2 : ShortComplex (Rep R G)}
    (hX1 : X1.ShortExact) (hX2 : X2.ShortExact) (F : X1 ⟶ X2) (i : Int) :
    TateCohomology.δ hX1 i ≫ (tateCohomologyFunctor (i + 1)).map F.τ₁ =
    (tateCohomologyFunctor i).map F.τ₃ ≫ TateCohomology.δ hX2 i :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor R G).mapShortComplex.map F)
    (map_tateComplexFunctor_shortExact hX1) (map_tateComplexFunctor_shortExact hX2) i (i + 1) rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoGroupCohomology` / `isoGroupCohomology` 的定义

English:
definition isoGroupCohomology
  signature: (n : Nat) [NeZero n]
  body: NatIso.ofComponents (fun M => (tateComplexConnectData M).homologyIsoPos _ _ rfl) fun {X Y} f => by
    simp [tateCohomologyFunctor, CochainComplex.ConnectData.homologyMap_map_of_eq_succ (n := n)]

中文:
定义 isoGroupCohomology
  签名: (n : 自然数) [NeZero n]
  定义体: NatIso.ofComponents (fun M => (tateComplexConnectData M).homologyIsoPos _ _ rfl) fun {X Y} f => by
    simp [tateCohomologyFunctor, CochainComplex.ConnectData.homologyMap_map_of_eq_succ (n := n)]

Depends on / 依赖: CochainComplex, CochainComplex.ConnectData.homologyMap_map_of_eq_succ, ConnectData, NatIso, NatIso.ofComponents, homologyIsoPos, homologyMap_map_of_eq_succ, ofComponents, tateCohomologyFunctor, tateComplexConnectData
-/
def isoGroupCohomology (n : Nat) [NeZero n] :
    tateCohomologyFunctor n ≅ groupCohomology.functor.{u} R G n :=
  NatIso.ofComponents (fun M => (tateComplexConnectData M).homologyIsoPos _ _ rfl) fun {X Y} f => by
    simp [tateCohomologyFunctor, CochainComplex.ConnectData.homologyMap_map_of_eq_succ (n := n)]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoGroupHomology` / `isoGroupHomology` 的定义

English:
definition isoGroupHomology
  signature: (m : Int) (n : Nat) (hmn : m = -(n + 1)) [NeZero n]
  body: NatIso.ofComponents (fun M => (tateComplexConnectData M).homologyIsoNeg _ _ hmn) fun {X Y} f => by
    simp [tateCohomologyFunctor,
      CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ (hmn := hmn)]

中文:
定义 isoGroupHomology
  签名: (m : 整数) (n : 自然数) (hmn : m = -(n + 1)) [NeZero n]
  定义体: NatIso.ofComponents (fun M => (tateComplexConnectData M).homologyIsoNeg _ _ hmn) fun {X Y} f => by
    simp [tateCohomologyFunctor,
      CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ (hmn := hmn)]

Depends on / 依赖: CochainComplex, CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ, ConnectData, NatIso, NatIso.ofComponents, homologyIsoNeg, homologyMap_map_of_eq_neg_succ, ofComponents, tateCohomologyFunctor, tateComplexConnectData
-/
def isoGroupHomology (m : Int) (n : Nat) (hmn : m = -(n + 1)) [NeZero n] :
    tateCohomologyFunctor m ≅ groupHomology.functor R G n :=
  NatIso.ofComponents (fun M => (tateComplexConnectData M).homologyIsoNeg _ _ hmn) fun {X Y} f => by
    simp [tateCohomologyFunctor,
      CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ (hmn := hmn)]

end TateCohomology
