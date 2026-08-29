/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Properties of the geometric realization

In this file, we introduce some API in order to study the geometric
realization functor (and its right adjoint the singular simplicial set functor):
* `SimplexCategory.toTopHomeo`: the homeomorphism between the geometric
realization of `Δ[n]` and `stdSimplex ℝ (Fin (n + 1))`;
* `TopCat.toSSetObj₀Equiv : toSSet.obj X _⦋0⦌ ≃ X` for `X : TopCat`;
* `SSet.stdSimplex.toTopObjIsoI : |Δ[1]| ≅ TopCat.I`;
* `SSet.stdSimplex.toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I`:
the morphism corresponding to `toTopObjIsoI.hom` by adjunction.

-/

@[expose] public section

universe u

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopCat.toSSet.{u}.Monoidal
  body: .ofChosenFiniteProducts _

中文:
实例 :
  签名: TopCat.toSSet.{u}.Monoidal
  定义体: .ofChosenFiniteProducts _

Depends on / 依赖: ofChosenFiniteProducts
-/
noncomputable instance : TopCat.toSSet.{u}.Monoidal := .ofChosenFiniteProducts _

open CategoryTheory MonoidalCategory Simplicial Opposite

namespace SimplexCategory

open SSet

/--
Definition of `toTopHomeo` / `toTopHomeo` 的定义

English:
definition toTopHomeo
  signature: (n : SimplexCategory)
  body: (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift

中文:
定义 toTopHomeo
  签名: (n : SimplexCategory)
  定义体: (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift

Depends on / 依赖: Homeomorph, Homeomorph.ulift, TopCat, TopCat.homeoOfIso, homeoOfIso, toTopSimplex
-/
noncomputable def toTopHomeo (n : SimplexCategory) :
    |stdSimplex.{u}.obj n| ≃ₜ stdSimplex Real (Fin (n.len + 1)) :=
  (TopCat.homeoOfIso (toTopSimplex.{u}.app n)).trans Homeomorph.ulift

/--
lemma `toTopHomeo_naturality` / 引理 `toTopHomeo_naturality`

English:
lemma toTopHomeo_naturality
  given: {n m : SimplexCategory} (f : n ⟶ m)
  proof: by
  ext x : 1
  exact ULift.up_injective (ConcreteCategory.congr_hom ((forget TopCat).congr_map
    (toTopSimplex.hom.naturality f)) x)

中文:
引理 toTopHomeo_naturality
  条件: {n m : SimplexCategory} (f : n ⟶ m)
  证明: by
  ext x : 1
  exact ULift.up_injective (ConcreteCategory.congr_hom ((forget TopCat).congr_map
    (toTopSimplex.hom.naturality f)) x)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, TopCat, ULift.up_injective, congr_hom, congr_map, forget, naturality, toTopSimplex, toTopSimplex.hom.naturality, up_injective
-/
lemma toTopHomeo_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    toTopHomeo m ∘ SSet.toTop.{u}.map (SSet.stdSimplex.map f) =
    stdSimplex.map f ∘ n.toTopHomeo := by
  ext x : 1
  exact ULift.up_injective (ConcreteCategory.congr_hom ((forget TopCat).congr_map
    (toTopSimplex.hom.naturality f)) x)

/--
lemma `toTopHomeo_naturality_apply` / 引理 `toTopHomeo_naturality_apply`

English:
lemma toTopHomeo_naturality_apply
  statement: {n m : SimplexCategory} (f : n ⟶ m)
  proof: congr_fun (toTopHomeo_naturality f) x

中文:
引理 toTopHomeo_naturality_apply
  结论: {n m : SimplexCategory} (f : n ⟶ m)
  证明: congr_fun (toTopHomeo_naturality f) x

Depends on / 依赖: congr_fun, toTopHomeo_naturality
-/
lemma toTopHomeo_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : |stdSimplex.obj n|) :
    m.toTopHomeo ((SSet.toTop.{u}.map (SSet.stdSimplex.map f) x)) =
      (_root_.stdSimplex.map f) (n.toTopHomeo x) :=
  congr_fun (toTopHomeo_naturality f) x

/--
lemma `toTopHomeo_symm_naturality` / 引理 `toTopHomeo_symm_naturality`

English:
lemma toTopHomeo_symm_naturality
  given: {n m : SimplexCategory} (f : n ⟶ m)
  proof: by
  ext x : 1
  exact ConcreteCategory.congr_hom ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _

中文:
引理 toTopHomeo_symm_naturality
  条件: {n m : SimplexCategory} (f : n ⟶ m)
  证明: by
  ext x : 1
  exact ConcreteCategory.congr_hom ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, congr_map, forget, naturality, toTopSimplex, toTopSimplex.inv.naturality
-/
lemma toTopHomeo_symm_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    m.toTopHomeo.symm ∘ stdSimplex.map f =
      (SSet.toTop.{u}.map (SSet.stdSimplex.map f)).hom ∘ n.toTopHomeo.symm := by
  ext x : 1
  exact ConcreteCategory.congr_hom ((forget _).congr_map
    (toTopSimplex.inv.naturality f)) _

/--
lemma `toTopHomeo_symm_naturality_apply` / 引理 `toTopHomeo_symm_naturality_apply`

English:
lemma toTopHomeo_symm_naturality_apply
  statement: {n m : SimplexCategory} (f : n ⟶ m)
  proof: congr_fun (toTopHomeo_symm_naturality f) x

中文:
引理 toTopHomeo_symm_naturality_apply
  结论: {n m : SimplexCategory} (f : n ⟶ m)
  证明: congr_fun (toTopHomeo_symm_naturality f) x

Depends on / 依赖: congr_fun, toTopHomeo_symm_naturality
-/
lemma toTopHomeo_symm_naturality_apply {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex Real (Fin (n.len + 1))) :
    m.toTopHomeo.symm (stdSimplex.map f x) =
      SSet.toTop.{u}.map (SSet.stdSimplex.map f) (n.toTopHomeo.symm x) :=
  congr_fun (toTopHomeo_symm_naturality f) x

end SimplexCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (stdSimplex Real (Fin (⦋0⦌.len + 1)))
  body: inferInstanceAs (Unique (stdSimplex Real (Fin 1)))

中文:
实例 :
  签名: Unique (stdSimplex 实数 (Fin (⦋0⦌.len + 1)))
  定义体: inferInstanceAs (Unique (stdSimplex Real (Fin 1)))

Depends on / 依赖: Unique, stdSimplex
-/
instance : Unique (stdSimplex Real (Fin (⦋0⦌.len + 1))) :=
  inferInstanceAs (Unique (stdSimplex Real (Fin 1)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique |(Δ[0] : SSet.{u})|
  body: ⦋0⦌.toTopHomeo.unique

中文:
实例 :
  签名: Unique |(Δ[0] : SSet.{u})|
  定义体: ⦋0⦌.toTopHomeo.unique

Depends on / 依赖: toTopHomeo, toTopHomeo.unique, unique
-/
noncomputable instance : Unique |(Δ[0] : SSet.{u})| := ⦋0⦌.toTopHomeo.unique

namespace TopCat

/-- Given `X : TopCat`, this is the bijection between `0`-simplices
of the singular simplicial set of `X` and `X`. -/
@[simps! -isSimp apply symm_apply]
/--
Definition of `toSSetObj₀Equiv` / `toSSetObj₀Equiv` 的定义

English:
definition toSSetObj₀Equiv
  signature: {X : TopCat.{u}}
  body: (toSSetObjEquiv X _).trans
    { toFun f := f.1 (default : _)
      invFun x := ⟨fun _ => x, by fun_prop⟩
      left_inv _ := by
        ext x
        obtain rfl := Subsingleton.elim x default
        rfl
      right_inv _ := rfl }

@[simp]

中文:
定义 toSSetObj₀Equiv
  签名: {X : TopCat.{u}}
  定义体: (toSSetObjEquiv X _).trans
    { toFun f := f.1 (default : _)
      invFun x := ⟨fun _ => x, by fun_prop⟩
      left_inv _ := by
        ext x
        obtain rfl := Subsingleton.elim x default
        rfl
      right_inv _ := rfl }

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, fun_prop, invFun, left_inv, right_inv, toSSetObjEquiv
-/
noncomputable def toSSetObj₀Equiv {X : TopCat.{u}} :
    toSSet.obj X _⦋0⦌ ≃ X :=
  (toSSetObjEquiv X _).trans
    { toFun f := f.1 (default : _)
      invFun x := ⟨fun _ => x, by fun_prop⟩
      left_inv _ := by
        ext x
        obtain rfl := Subsingleton.elim x default
        rfl
      right_inv _ := rfl }

@[simp]
/--
lemma `toSSet_map_const` / 引理 `toSSet_map_const`

English:
lemma toSSet_map_const
  given: (X : TopCat.{u}) {Y : TopCat.{u}} (y : Y)
  proof: rfl

中文:
引理 toSSet_map_const
  条件: (X : TopCat.{u}) {Y : TopCat.{u}} (y : Y)
  证明: rfl
-/
lemma toSSet_map_const (X : TopCat.{u}) {Y : TopCat.{u}} (y : Y) :
    toSSet.map (TopCat.const (X := X) y) =
      SSet.const (toSSetObj₀Equiv.symm y) :=
  rfl

/--
lemma `toSSetObjEquiv_symm_naturality` / 引理 `toSSetObjEquiv_symm_naturality`

English:
lemma toSSetObjEquiv_symm_naturality
  statement: {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
  proof: rfl

@[simp]

中文:
引理 toSSetObjEquiv_symm_naturality
  结论: {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
  证明: rfl

@[simp]
-/
lemma toSSetObjEquiv_symm_naturality {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (g : C((stdSimplex Real (Fin (m.len + 1))), X)) :
    (toSSet.obj X).map f.op ((X.toSSetObjEquiv _).symm g) =
      (X.toSSetObjEquiv _).symm (g.comp ⟨stdSimplex.map f, by continuity⟩) :=
  rfl

@[simp]
/--
lemma `toSSetObjEquiv_naturality_apply` / 引理 `toSSetObjEquiv_naturality_apply`

English:
lemma toSSetObjEquiv_naturality_apply
  statement: {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
  proof: rfl

@[simp]

中文:
引理 toSSetObjEquiv_naturality_apply
  结论: {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
  证明: rfl

@[simp]
-/
lemma toSSetObjEquiv_naturality_apply {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : (toSSet.obj X).obj (op m)) (z : stdSimplex Real (Fin (n.len + 1))) :
    dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).map f.op x) z =
      X.toSSetObjEquiv _ x (stdSimplex.map f z) :=
  rfl

@[simp]
/--
lemma `toSSetObjEquiv_δ_apply` / 引理 `toSSetObjEquiv_δ_apply`

English:
lemma toSSetObjEquiv_δ_apply
  statement: {X : TopCat.{u}} {n : Nat}
  proof: rfl

@[simp]

中文:
引理 toSSetObjEquiv_δ_apply
  结论: {X : TopCat.{u}} {n : 自然数}
  证明: rfl

@[simp]
-/
lemma toSSetObjEquiv_δ_apply {X : TopCat.{u}} {n : Nat}
    (x : toSSet.obj X _⦋n + 1⦌) (i : Fin (n + 2)) (z : stdSimplex Real (Fin (n + 1))) :
    dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).δ i x) z =
      X.toSSetObjEquiv _ x (stdSimplex.map i.succAbove z) :=
  rfl

@[simp]
/--
lemma `toSSetObjEquiv_σ_apply` / 引理 `toSSetObjEquiv_σ_apply`

English:
lemma toSSetObjEquiv_σ_apply
  statement: {X : TopCat.{u}} {n : Nat}
  proof: rfl

中文:
引理 toSSetObjEquiv_σ_apply
  结论: {X : TopCat.{u}} {n : 自然数}
  证明: rfl
-/
lemma toSSetObjEquiv_σ_apply {X : TopCat.{u}} {n : Nat}
    (x : toSSet.obj X _⦋n⦌) (i : Fin (n + 1)) (z : stdSimplex Real (Fin (n + 2))) :
    dsimp% X.toSSetObjEquiv _ ((toSSet.obj X).σ i x) z =
      X.toSSetObjEquiv _ x (stdSimplex.map i.predAbove z) :=
  rfl

end TopCat

/--
lemma `sSetTopAdj_homEquiv_stdSimplex_zero` / 引理 `sSetTopAdj_homEquiv_stdSimplex_zero`

English:
lemma sSetTopAdj_homEquiv_stdSimplex_zero
  statement: {X : TopCat.{u}}
  proof: by
  have : sSetTopAdj.unit.app Δ[0] =
      SSet.const (TopCat.toSSetObj₀Equiv.symm default) :=
    SSet.yonedaEquiv.injective (TopCat.toSSetObj₀Equiv.injective (by subsingleton))
  rw [Adjunction.homEquiv_unit]; rw [TopCat.toSSetObj₀Equiv_symm_apply]; rw [this]
  rfl

中文:
引理 sSetTopAdj_homEquiv_stdSimplex_zero
  结论: {X : TopCat.{u}}
  证明: by
  have : sSetTopAdj.unit.app Δ[0] =
      SSet.const (TopCat.toSSetObj₀Equiv.symm default) :=
    SSet.yonedaEquiv.injective (TopCat.toSSetObj₀Equiv.injective (by subsingleton))
  rw [Adjunction.homEquiv_unit]; rw [TopCat.toSSetObj₀Equiv_symm_apply]; rw [this]
  rfl

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Equiv.injective, Equiv.symm, SSet.const, SSet.yonedaEquiv.injective, TopCat, TopCat.toSSetObj, homEquiv_unit, injective, sSetTopAdj, sSetTopAdj.unit.app, subsingleton, yonedaEquiv
-/
lemma sSetTopAdj_homEquiv_stdSimplex_zero {X : TopCat.{u}}
    (f : |Δ[0]| ⟶ X) :
    sSetTopAdj.homEquiv Δ[0] X f =
      SSet.const (TopCat.toSSetObj₀Equiv.symm (f default)) := by
  have : sSetTopAdj.unit.app Δ[0] =
      SSet.const (TopCat.toSSetObj₀Equiv.symm default) :=
    SSet.yonedaEquiv.injective (TopCat.toSSetObj₀Equiv.injective (by subsingleton))
  rw [Adjunction.homEquiv_unit]; rw [TopCat.toSSetObj₀Equiv_symm_apply]; rw [this]
  rfl

/--
Definition of `TopCat.stdSimplexHomeomorphI` / `TopCat.stdSimplexHomeomorphI` 的定义

English:
definition TopCat.stdSimplexHomeomorphI
  signature: :
  body: stdSimplexHomeomorphUnitInterval.trans Homeomorph.ulift.symm

@[simp]

中文:
定义 TopCat.stdSimplexHomeomorphI
  签名: :
  定义体: stdSimplexHomeomorphUnitInterval.trans Homeomorph.ulift.symm

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.ulift.symm, stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.trans
-/
def TopCat.stdSimplexHomeomorphI :
    _root_.stdSimplex Real (Fin 2) ≃ₜ TopCat.I.{u} :=
  stdSimplexHomeomorphUnitInterval.trans Homeomorph.ulift.symm

@[simp]
/--
lemma `TopCat.stdSimplexHomeomorphI_vertex_zero` / 引理 `TopCat.stdSimplexHomeomorphI_vertex_zero`

English:
lemma TopCat.stdSimplexHomeomorphI_vertex_zero
  proof: rfl

@[simp]

中文:
引理 TopCat.stdSimplexHomeomorphI_vertex_zero
  证明: rfl

@[simp]
-/
lemma TopCat.stdSimplexHomeomorphI_vertex_zero :
    TopCat.stdSimplexHomeomorphI.{u} (stdSimplex.vertex 0) = 0 := rfl

@[simp]
/--
lemma `TopCat.stdSimplexHomeomorphI_vertex_one` / 引理 `TopCat.stdSimplexHomeomorphI_vertex_one`

English:
lemma TopCat.stdSimplexHomeomorphI_vertex_one
  proof: rfl

@[simp]

中文:
引理 TopCat.stdSimplexHomeomorphI_vertex_one
  证明: rfl

@[simp]
-/
lemma TopCat.stdSimplexHomeomorphI_vertex_one :
    TopCat.stdSimplexHomeomorphI.{u} (stdSimplex.vertex 1) = 1 := rfl

@[simp]
/--
lemma `TopCat.stdSimplexHomeomorphI_symm_zero` / 引理 `TopCat.stdSimplexHomeomorphI_symm_zero`

English:
lemma TopCat.stdSimplexHomeomorphI_symm_zero
  proof: by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_zero]

@[simp]

中文:
引理 TopCat.stdSimplexHomeomorphI_symm_zero
  证明: by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_zero]

@[simp]

Depends on / 依赖: TopCat, TopCat.stdSimplexHomeomorphI_vertex_zero, stdSimplexHomeomorphI_vertex_zero
-/
lemma TopCat.stdSimplexHomeomorphI_symm_zero :
    TopCat.stdSimplexHomeomorphI.{u}.symm 0 = stdSimplex.vertex 0 := by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_zero]

@[simp]
/--
lemma `TopCat.stdSimplexHomeomorphI_symm_one` / 引理 `TopCat.stdSimplexHomeomorphI_symm_one`

English:
lemma TopCat.stdSimplexHomeomorphI_symm_one
  proof: by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_one]

中文:
引理 TopCat.stdSimplexHomeomorphI_symm_one
  证明: by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_one]

Depends on / 依赖: TopCat, TopCat.stdSimplexHomeomorphI_vertex_one, stdSimplexHomeomorphI_vertex_one
-/
lemma TopCat.stdSimplexHomeomorphI_symm_one :
    TopCat.stdSimplexHomeomorphI.{u}.symm 1 = stdSimplex.vertex 1 := by
  simp [← TopCat.stdSimplexHomeomorphI_vertex_one]

namespace SSet.stdSimplex

/--
Definition of `toTopObjIsoI` / `toTopObjIsoI` 的定义

English:
definition toTopObjIsoI
  signature: :
  body: TopCat.isoOfHomeo ((SimplexCategory.toTopHomeo _).trans TopCat.stdSimplexHomeomorphI)

中文:
定义 toTopObjIsoI
  签名: :
  定义体: TopCat.isoOfHomeo ((SimplexCategory.toTopHomeo _).trans TopCat.stdSimplexHomeomorphI)

Depends on / 依赖: SimplexCategory, SimplexCategory.toTopHomeo, TopCat, TopCat.isoOfHomeo, TopCat.stdSimplexHomeomorphI, isoOfHomeo, stdSimplexHomeomorphI, toTopHomeo
-/
noncomputable def toTopObjIsoI :
    |(Δ[1] : SSet.{u})| ≅ TopCat.I.{u} :=
  TopCat.isoOfHomeo ((SimplexCategory.toTopHomeo _).trans TopCat.stdSimplexHomeomorphI)

/--
Definition of `toSSetObjI` / `toSSetObjI` 的定义

English:
definition toSSetObjI
  signature: : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I.{u}
  body: sSetTopAdj.homEquiv _ _ toTopObjIsoI.hom

@[simp]

中文:
定义 toSSetObjI
  签名: : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I.{u}
  定义体: sSetTopAdj.homEquiv _ _ toTopObjIsoI.hom

@[simp]

Depends on / 依赖: homEquiv, sSetTopAdj, sSetTopAdj.homEquiv, toTopObjIsoI, toTopObjIsoI.hom
-/
noncomputable def toSSetObjI : Δ[1] ⟶ TopCat.toSSet.obj TopCat.I.{u} :=
  sSetTopAdj.homEquiv _ _ toTopObjIsoI.hom

@[simp]
/--
lemma `δ_one_toSSetObjI` / 引理 `δ_one_toSSetObjI`

English:
lemma δ_one_toSSetObjI
  proof: by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left]; rw [sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 1)).hom) default)) = 0 := by
    rw

中文:
引理 δ_one_toSSetObjI
  证明: by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left]; rw [sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 1)).hom) default)) = 0 := by
    rw

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left, SimplexCategory, SimplexCategory.toTopHomeo_naturality_apply, Subsingleton, Subsingleton.elim, TopCat, TopCat.stdSimplexHomeomorphI, homEquiv_naturality_left, map_vertex, sSetTopAdj_homEquiv_stdSimplex_zero, stdSimplex, stdSimplex.map_vertex, stdSimplex.vertex, stdSimplexHomeomorphI, stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval_zero, toSSetObjI, toTopHomeo, toTopHomeo_naturality_apply
-/
lemma δ_one_toSSetObjI :
    stdSimplex.δ 1 ≫ toSSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 0) := by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left]; rw [sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 1)).hom) default)) = 0 := by
    rw [← stdSimplexHomeomorphUnitInterval_zero]
    congr 1
    refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0)]; rw [stdSimplex.map_vertex]
    rfl
  exact congr_arg ULift.up.{u} this

@[simp]
/--
lemma `δ_zero_toSSetObjI` / 引理 `δ_zero_toSSetObjI`

English:
lemma δ_zero_toSSetObjI
  proof: by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left]; rw [sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 0)).hom) default)) = 1 := by
    rw

中文:
引理 δ_zero_toSSetObjI
  证明: by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left]; rw [sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 0)).hom) default)) = 1 := by
    rw

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left, SimplexCategory, SimplexCategory.toTopHomeo_naturality_apply, Subsingleton, Subsingleton.elim, TopCat, TopCat.stdSimplexHomeomorphI, homEquiv_naturality_left, map_vertex, sSetTopAdj_homEquiv_stdSimplex_zero, stdSimplex, stdSimplex.map_vertex, stdSimplex.vertex, stdSimplexHomeomorphI, stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval_one, toSSetObjI, toTopHomeo, toTopHomeo_naturality_apply
-/
lemma δ_zero_toSSetObjI :
    dsimp% stdSimplex.δ 0 ≫ toSSetObjI.{u} = SSet.const (TopCat.toSSetObj₀Equiv.symm 1) := by
  dsimp only [toSSetObjI, toTopObjIsoI, TopCat.stdSimplexHomeomorphI]
  rw [← Adjunction.homEquiv_naturality_left]; rw [sSetTopAdj_homEquiv_stdSimplex_zero]
  congr 2
  have : stdSimplexHomeomorphUnitInterval (⦋1⦌.toTopHomeo
      (((toTop.{u}.map (stdSimplex.δ 0)).hom) default)) = 1 := by
    rw [← stdSimplexHomeomorphUnitInterval_one]
    congr 1
    refine (SimplexCategory.toTopHomeo_naturality_apply _ _).trans ?_
    rw [Subsingleton.elim (⦋0⦌.toTopHomeo default) (stdSimplex.vertex 0)]; rw [stdSimplex.map_vertex]
    rfl
  exact congr_arg ULift.up.{u} this

@[simp]
/--
lemma `toSSetObj_app_const_zero` / 引理 `toSSetObj_app_const_zero`

English:
lemma toSSetObj_app_const_zero
  proof: by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 1 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_one_eq_const]
  · simp

@[simp]

中文:
引理 toSSetObj_app_const_zero
  证明: by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 1 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_one_eq_const]
  · simp

@[simp]

Depends on / 依赖: injective, stdSimplex, toSSetObjI, yonedaEquiv, yonedaEquiv.symm.injective, yonedaEquiv_symm_comp
-/
lemma toSSetObj_app_const_zero :
    toSSetObjI.app (op ⦋0⦌) (const _ 0 _) = TopCat.toSSetObj₀Equiv.symm 0 := by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 1 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_one_eq_const]
  · simp

@[simp]
/--
lemma `toSSetObj_app_const_one` / 引理 `toSSetObj_app_const_one`

English:
lemma toSSetObj_app_const_one
  proof: by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 0 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_zero_eq_const]
  · simp

中文:
引理 toSSetObj_app_const_one
  证明: by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 0 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_zero_eq_const]
  · simp

Depends on / 依赖: injective, stdSimplex, toSSetObjI, yonedaEquiv, yonedaEquiv.symm.injective, yonedaEquiv_symm_comp
-/
lemma toSSetObj_app_const_one :
    toSSetObjI.app (op ⦋0⦌) (const _ 1 _) = TopCat.toSSetObj₀Equiv.symm 1 := by
  apply yonedaEquiv.symm.injective
  trans stdSimplex.δ 0 ≫ toSSetObjI
  · simp [← yonedaEquiv_symm_comp, stdSimplex.δ_zero_eq_const]
  · simp

open Functor.Monoidal in
@[reassoc (attr := simp)]
/--
lemma `ι₀_whiskerLeft_toSSetObjI_μ` / 引理 `ι₀_whiskerLeft_toSSetObjI_μ`

English:
lemma ι₀_whiskerLeft_toSSetObjI_μ
  given: (X : TopCat.{u})
  proof: by
  rw [← cancel_mono (μIso _ _ _).inv]; rw [Category.assoc]; rw [Category.assoc]; rw [μIso_inv]; rw [μ_δ]; rw [Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

中文:
引理 ι₀_whiskerLeft_toSSetObjI_μ
  条件: (X : TopCat.{u})
  证明: by
  rw [← cancel_mono (μIso _ _ _).inv]; rw [Category.assoc]; rw [Category.assoc]; rw [μIso_inv]; rw [μ_δ]; rw [Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.hom_ext, Category, Category.assoc, Category.comp_id, Functor, Functor.map_comp, cancel_mono, comp_id, hom_ext, map_comp
-/
lemma ι₀_whiskerLeft_toSSetObjI_μ (X : TopCat.{u}) :
    SSet.ι₀ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₀ := by
  rw [← cancel_mono (μIso _ _ _).inv]; rw [Category.assoc]; rw [Category.assoc]; rw [μIso_inv]; rw [μ_δ]; rw [Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

open Functor.Monoidal in
@[reassoc (attr := simp)]
/--
lemma `ι₁_whiskerLeft_toSSetObjI_μ` / 引理 `ι₁_whiskerLeft_toSSetObjI_μ`

English:
lemma ι₁_whiskerLeft_toSSetObjI_μ
  given: (X : TopCat.{u})
  proof: by
  rw [← cancel_mono (μIso _ _ _).inv]; rw [Category.assoc]; rw [Category.assoc]; rw [μIso_inv]; rw [μ_δ]; rw [Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

中文:
引理 ι₁_whiskerLeft_toSSetObjI_μ
  条件: (X : TopCat.{u})
  证明: by
  rw [← cancel_mono (μIso _ _ _).inv]; rw [Category.assoc]; rw [Category.assoc]; rw [μIso_inv]; rw [μ_δ]; rw [Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.hom_ext, Category, Category.assoc, Category.comp_id, Functor, Functor.map_comp, cancel_mono, comp_id, hom_ext, map_comp
-/
lemma ι₁_whiskerLeft_toSSetObjI_μ (X : TopCat.{u}) :
    SSet.ι₁ ≫ TopCat.toSSet.obj X ◁ SSet.stdSimplex.toSSetObjI ≫
      Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I = TopCat.toSSet.map TopCat.ι₁ := by
  rw [← cancel_mono (μIso _ _ _).inv]; rw [Category.assoc]; rw [Category.assoc]; rw [μIso_inv]; rw [μ_δ]; rw [Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext <;> simp [← Functor.map_comp]

end SSet.stdSimplex
