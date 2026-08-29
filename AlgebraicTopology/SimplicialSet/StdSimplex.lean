/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Finset
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Order.Preorder.Finite

/-!
# The standard simplex

We define the standard simplices `Δ[n]` as simplicial sets.
See files `SimplicialSet.Boundary` and `SimplicialSet.Horn`
for their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open Simplicial`.)

-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial Opposite

namespace SSet

/--
Definition of `stdSimplex` / `stdSimplex` 的定义

English:
definition stdSimplex
  signature: : CosimplicialObject SSet.{u}
  body: uliftYoneda

@[inherit_doc SSet.stdSimplex]
scoped[Simplicial] notation3 "Δ[" n "]" => SSet.stdSimplex.obj (SimplexCategory.mk n)

中文:
定义 stdSimplex
  签名: : CosimplicialObject SSet.{u}
  定义体: uliftYoneda

@[inherit_doc SSet.stdSimplex]
scoped[Simplicial] notation3 "Δ[" n "]" => SSet.stdSimplex.obj (SimplexCategory.mk n)

Depends on / 依赖: uliftYoneda
-/
def stdSimplex : CosimplicialObject SSet.{u} := uliftYoneda

@[inherit_doc SSet.stdSimplex]
scoped[Simplicial] notation3 "Δ[" n "]" => SSet.stdSimplex.obj (SimplexCategory.mk n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited SSet
  body: ⟨Δ[0]⟩

中文:
实例 :
  签名: 可居 SSet
  定义体: ⟨Δ[0]⟩
-/
instance : Inhabited SSet :=
  ⟨Δ[0]⟩

instance {n} : Inhabited (SSet.Truncated n) :=
⟨(truncation n).obj Δ[0]⟩

namespace stdSimplex

open Finset Opposite SimplexCategory

/--
Definition of `fullyFaithful` / `fullyFaithful` 的定义

English:
abbreviation fullyFaithful
  signature: : stdSimplex.{u}.FullyFaithful
  body: ULiftYoneda.fullyFaithful SimplexCategory

中文:
缩写 fullyFaithful
  签名: : stdSimplex.{u}.满忠实
  定义体: ULiftYoneda.fullyFaithful SimplexCategory

Depends on / 依赖: SimplexCategory, ULiftYoneda, ULiftYoneda.fullyFaithful, fullyFaithful
-/
abbrev fullyFaithful : stdSimplex.{u}.FullyFaithful :=
  ULiftYoneda.fullyFaithful SimplexCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: stdSimplex.{u}.Full
  body: fullyFaithful.full

中文:
实例 :
  签名: stdSimplex.{u}.满
  定义体: fullyFaithful.full

Depends on / 依赖: fullyFaithful, fullyFaithful.full
-/
instance : stdSimplex.{u}.Full := fullyFaithful.full
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: stdSimplex.{u}.Faithful
  body: fullyFaithful.faithful

@[simp]

中文:
实例 :
  签名: stdSimplex.{u}.忠实
  定义体: fullyFaithful.faithful

@[simp]

Depends on / 依赖: faithful, fullyFaithful, fullyFaithful.faithful
-/
instance : stdSimplex.{u}.Faithful := fullyFaithful.faithful

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (n : SimplexCategory)
  proof: CategoryTheory.Functor.map_id _ _

中文:
引理 map_id
  条件: (n : 单纯形范畴)
  证明: CategoryTheory.Functor.map_id _ _

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, map_id
-/
lemma map_id (n : SimplexCategory) :
    (SSet.stdSimplex.map (SimplexCategory.Hom.mk OrderHom.id : n ⟶ n)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/--
Definition of `objEquiv` / `objEquiv` 的定义

English:
definition objEquiv
  signature: {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
  body: Equiv.ulift.{u, 0}

中文:
定义 objEquiv
  签名: {n : 单纯形范畴} {m : SimplexCategoryᵒᵖ}
  定义体: Equiv.ulift.{u, 0}

Depends on / 依赖: Equiv.ulift
-/
def objEquiv {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} :
    (stdSimplex.{u}.obj n).obj m ≃ (m.unop ⟶ n) :=
  Equiv.ulift.{u, 0}

instance (n : SimplexCategory) (m : SimplexCategoryᵒᵖ) :
    DecidableEq ((stdSimplex.{u}.obj n).obj m) :=
  fun a b => decidable_of_iff (stdSimplex.objEquiv a = stdSimplex.objEquiv b) (by simp)

/-- If `x : Δ[n] _⦋d⦌` and `i : Fin (d + 1)`, we may evaluate `x i : Fin (n + 1)`. -/
instance (n i : Nat) : FunLike (Δ[n] _⦋i⦌) (Fin (i + 1)) (Fin (n + 1)) where
  coe x j := (objEquiv x).toOrderHom j
  coe_injective _ _ h := objEquiv.injective (by ext : 3; apply congr_fun h)

/--
lemma `monotone_apply` / 引理 `monotone_apply`

English:
lemma monotone_apply
  given: {n i : Nat} (x : Δ[n] _⦋i⦌)
  proof: (objEquiv x).toOrderHom.monotone

@[ext]

中文:
引理 monotone_apply
  条件: {n i : 自然数} (x : Δ[n] _⦋i⦌)
  证明: (objEquiv x).toOrderHom.monotone

@[ext]

Depends on / 依赖: monotone, objEquiv, toOrderHom, toOrderHom.monotone
-/
lemma monotone_apply {n i : Nat} (x : Δ[n] _⦋i⦌) :
    Monotone (fun (j : Fin (i + 1)) => x j) :=
  (objEquiv x).toOrderHom.monotone

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {n d : Nat} (x y : Δ[n] _⦋d⦌) (h : forall (i : Fin (d + 1)), x i = y i)
  statement: x = y
  proof: DFunLike.ext _ _ h

@[simp]

中文:
引理 ext
  条件: {n d : 自然数} (x y : Δ[n] _⦋d⦌) (h : 对任意 (i : 有限集 (d + 1)), x i = y i)
  结论: x = y
  证明: DFunLike.ext _ _ h

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
lemma ext {n d : Nat} (x y : Δ[n] _⦋d⦌) (h : forall (i : Fin (d + 1)), x i = y i) : x = y :=
  DFunLike.ext _ _ h

@[simp]
/--
lemma `objEquiv_toOrderHom_apply` / 引理 `objEquiv_toOrderHom_apply`

English:
lemma objEquiv_toOrderHom_apply
  statement: {n i : Nat}
  proof: rfl

中文:
引理 objEquiv_toOrderHom_apply
  结论: {n i : 自然数}
  证明: rfl
-/
lemma objEquiv_toOrderHom_apply {n i : Nat}
    (x : (stdSimplex.{u} ^⦋n⦌).obj (op ⦋i⦌)) (j : Fin (i + 1)) :
    DFunLike.coe (F := Fin (i + 1) ->o Fin (n + 1))
      ((DFunLike.coe (F := Δ[n].obj (op ⦋i⦌) ≃ (⦋i⦌ ⟶ ⦋n⦌))
        objEquiv x)).toOrderHom j = x j :=
  rfl

/--
lemma `objEquiv_symm_comp` / 引理 `objEquiv_symm_comp`

English:
lemma objEquiv_symm_comp
  statement: {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ}
  proof: rfl

中文:
引理 objEquiv_symm_comp
  结论: {n n' : 单纯形范畴} {m : SimplexCategoryᵒᵖ}
  证明: rfl
-/
lemma objEquiv_symm_comp {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) (g : n ⟶ n') :
    objEquiv.{u}.symm (f ≫ g) =
      (stdSimplex.map g).app _ (objEquiv.{u}.symm f) := rfl

/--
lemma `map_objEquiv_symm` / 引理 `map_objEquiv_symm`

English:
lemma map_objEquiv_symm
  statement: {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ}
  proof: rfl

@[simp]

中文:
引理 map_objEquiv_symm
  结论: {n : 单纯形范畴} {m m' : SimplexCategoryᵒᵖ}
  证明: rfl

@[simp]
-/
lemma map_objEquiv_symm {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) (g : m ⟶ m') :
    (stdSimplex.{u}.obj n).map g (objEquiv.symm f) =
      objEquiv.symm (g.unop ≫ f) :=
  rfl

@[simp]
/--
lemma `objEquiv_symm_apply` / 引理 `objEquiv_symm_apply`

English:
lemma objEquiv_symm_apply
  given: {n m : Nat} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1))
  proof: rfl

@[simp]

中文:
引理 objEquiv_symm_apply
  条件: {n m : 自然数} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : 有限集 (m + 1))
  证明: rfl

@[simp]
-/
lemma objEquiv_symm_apply {n m : Nat} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (objEquiv.{u}.symm f : Δ[n] _⦋m⦌) i = f.toOrderHom i := rfl

@[simp]
/--
lemma `δ_objEquiv_symm_apply` / 引理 `δ_objEquiv_symm_apply`

English:
lemma δ_objEquiv_symm_apply
  proof: by
  rfl

@[simp]

中文:
引理 δ_objEquiv_symm_apply
  证明: by
  rfl

@[simp]

Depends on / 依赖: SimplexCategory
-/
lemma δ_objEquiv_symm_apply
    {n : Nat} {m : SimplexCategory} (f : .mk (n + 1) ⟶ m) (i : Fin (n + 2)) :
    dsimp% (stdSimplex.obj _).δ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n⦌)).symm (SimplexCategory.δ i ≫ f) := by
  rfl

@[simp]
/--
lemma `σ_objEquiv_symm_apply` / 引理 `σ_objEquiv_symm_apply`

English:
lemma σ_objEquiv_symm_apply
  proof: by
  rfl

中文:
引理 σ_objEquiv_symm_apply
  证明: by
  rfl

Depends on / 依赖: SimplexCategory
-/
lemma σ_objEquiv_symm_apply
    {n : Nat} {m : SimplexCategory} (f : .mk n ⟶ m) (i : Fin (n + 1)) :
    dsimp% (stdSimplex.obj _).σ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n + 1⦌)).symm (SimplexCategory.σ i ≫ f) := by
  rfl

/--
Definition of `objMk` / `objMk` 的定义

English:
abbreviation objMk
  signature: {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
  body: objEquiv.symm (Hom.mk f)

@[simp]

中文:
缩写 objMk
  签名: {n : 单纯形范畴} {m : SimplexCategoryᵒᵖ}
  定义体: objEquiv.symm (Hom.mk f)

@[simp]

Depends on / 依赖: Hom.mk, objEquiv, objEquiv.symm
-/
abbrev objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : Fin (len m.unop + 1) ->o Fin (n.len + 1)) :
    (stdSimplex.{u}.obj n).obj m :=
  objEquiv.symm (Hom.mk f)

@[simp]
/--
lemma `objMk_apply` / 引理 `objMk_apply`

English:
lemma objMk_apply
  given: {n m : Nat} (f : Fin (m + 1) ->o Fin (n + 1)) (i : Fin (m + 1))
  proof: rfl

中文:
引理 objMk_apply
  条件: {n m : 自然数} (f : 有限集 (m + 1) ->o 有限集 (n + 1)) (i : 有限集 (m + 1))
  证明: rfl
-/
lemma objMk_apply {n m : Nat} (f : Fin (m + 1) ->o Fin (n + 1)) (i : Fin (m + 1)) :
    objMk.{u} (n := ⦋n⦌) (m := op ⦋m⦌) f i = f i :=
  rfl

/--
lemma `objMk_bijective` / 引理 `objMk_bijective`

English:
lemma objMk_bijective
  given: {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
  proof: (objEquiv.trans homEquivOrderHom).symm.bijective

中文:
引理 objMk_bijective
  条件: {n : 单纯形范畴} {m : SimplexCategoryᵒᵖ}
  证明: (objEquiv.trans homEquivOrderHom).symm.bijective
-/
lemma objMk_bijective {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} :
    Function.Bijective (objMk (n := n) (m := m)) :=
  (objEquiv.trans homEquivOrderHom).symm.bijective

/--
Definition of `asOrderHom` / `asOrderHom` 的定义

English:
definition asOrderHom
  signature: {n} {m} (α : Δ[n].obj m)
  body: α.down.toOrderHom

中文:
定义 asOrderHom
  签名: {n} {m} (α : Δ[n].obj m)
  定义体: α.down.toOrderHom

Depends on / 依赖: down.toOrderHom, toOrderHom
-/
def asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin (n + 1)) :=
  α.down.toOrderHom

/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  statement: {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SimplexCategory}
  proof: by
  rfl

@[simp]

中文:
引理 map_apply
  结论: {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : 单纯形范畴}
  证明: by
  rfl

@[simp]
-/
lemma map_apply {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SimplexCategory}
    (x : (stdSimplex.{u}.obj n).obj m₁) :
    (stdSimplex.{u}.obj n).map f x = objEquiv.symm (f.unop ≫ objEquiv x) := by
  rfl

@[simp]
/--
lemma `coe_asOrderHom_objEquiv_symm` / 引理 `coe_asOrderHom_objEquiv_symm`

English:
lemma coe_asOrderHom_objEquiv_symm
  given: {n m : Nat} (α : ⦋n⦌ ⟶ ⦋m⦌)
  proof: rfl

中文:
引理 coe_asOrderHom_objEquiv_symm
  条件: {n m : 自然数} (α : ⦋n⦌ ⟶ ⦋m⦌)
  证明: rfl
-/
lemma coe_asOrderHom_objEquiv_symm {n m : Nat} (α : ⦋n⦌ ⟶ ⦋m⦌) :
    ⇑(asOrderHom (objEquiv.{u}.symm α)) = α := rfl

end stdSimplex

/--
Definition of `yonedaEquiv` / `yonedaEquiv` 的定义

English:
definition yonedaEquiv
  signature: {X : SSet.{u}} {n : SimplexCategory}
  body: uliftYonedaEquiv

中文:
定义 yonedaEquiv
  签名: {X : SSet.{u}} {n : 单纯形范畴}
  定义体: uliftYonedaEquiv

Depends on / 依赖: uliftYonedaEquiv
-/
def yonedaEquiv {X : SSet.{u}} {n : SimplexCategory} :
    (stdSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  uliftYonedaEquiv

instance (X : SSet.{u}) (n : SimplexCategory) [DecidableEq (X.obj (op n))] :
    DecidableEq (stdSimplex.obj n ⟶ X) :=
  fun a b => decidable_of_iff (yonedaEquiv a = yonedaEquiv b) (by simp)

@[simp]
/--
lemma `_root_.SSet.yonedaEquiv_symm_comp` / 引理 `_root_.SSet.yonedaEquiv_symm_comp`

English:
lemma _root_.SSet.yonedaEquiv_symm_comp
  statement: {X Y : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
  proof: uliftYonedaEquiv_symm_comp ..

中文:
引理 _root_.SSet.yonedaEquiv_symm_comp
  结论: {X Y : SSet.{u}} {n : 单纯形范畴} (x : X.obj (op n))
  证明: uliftYonedaEquiv_symm_comp ..

Depends on / 依赖: uliftYonedaEquiv_symm_comp
-/
lemma _root_.SSet.yonedaEquiv_symm_comp {X Y : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    (f : X ⟶ Y) :
    yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app _ x) :=
  uliftYonedaEquiv_symm_comp ..

set_option backward.isDefEq.respectTransparency false in
/--
lemma `_root_.SSet.yonedaEquiv_const` / 引理 `_root_.SSet.yonedaEquiv_const`

English:
lemma _root_.SSet.yonedaEquiv_const
  given: {X : SSet.{u}} (x : X _⦋0⦌)
  proof: by
  simp [yonedaEquiv, uliftYonedaEquiv]

@[simp]

中文:
引理 _root_.SSet.yonedaEquiv_const
  条件: {X : SSet.{u}} (x : X _⦋0⦌)
  证明: by
  simp [yonedaEquiv, uliftYonedaEquiv]

@[simp]

Depends on / 依赖: uliftYonedaEquiv, yonedaEquiv
-/
lemma _root_.SSet.yonedaEquiv_const {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv (const x : Δ[0] ⟶ X) = x := by
  simp [yonedaEquiv, uliftYonedaEquiv]

@[simp]
/--
lemma `_root_.SSet.yonedaEquiv_symm_zero` / 引理 `_root_.SSet.yonedaEquiv_symm_zero`

English:
lemma _root_.SSet.yonedaEquiv_symm_zero
  given: {X : SSet.{u}} (x : X _⦋0⦌)
  proof: by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_const]

中文:
引理 _root_.SSet.yonedaEquiv_symm_zero
  条件: {X : SSet.{u}} (x : X _⦋0⦌)
  证明: by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_const]

Depends on / 依赖: injective, yonedaEquiv, yonedaEquiv.injective, yonedaEquiv_const
-/
lemma _root_.SSet.yonedaEquiv_symm_zero {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv.symm x = const x := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_const]

/--
lemma `yonedaEquiv_map` / 引理 `yonedaEquiv_map`

English:
lemma yonedaEquiv_map
  given: {n m : SimplexCategory} (f : n ⟶ m)
  proof: yonedaEquiv.symm.injective rfl

@[deprecated (since := "2026-03-21")] alias stdSimplex.yonedaEquiv_map := yonedaEquiv_map

@[simp]

中文:
引理 yonedaEquiv_map
  条件: {n m : 单纯形范畴} (f : n ⟶ m)
  证明: yonedaEquiv.symm.injective rfl

@[deprecated (since := "2026-03-21")] alias stdSimplex.yonedaEquiv_map := yonedaEquiv_map

@[simp]

Depends on / 依赖: injective, yonedaEquiv, yonedaEquiv.symm.injective
-/
lemma yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m) :
    yonedaEquiv.{u} (stdSimplex.map f) = stdSimplex.objEquiv.symm f :=
  yonedaEquiv.symm.injective rfl

@[deprecated (since := "2026-03-21")] alias stdSimplex.yonedaEquiv_map := yonedaEquiv_map

@[simp]
/--
lemma `yonedaEquiv_symm_app` / 引理 `yonedaEquiv_symm_app`

English:
lemma yonedaEquiv_symm_app
  statement: {S : SSet} (n : SimplexCategory) (x : S.obj (op n))
  proof: rfl

@[simp]

中文:
引理 yonedaEquiv_symm_app
  结论: {S : SSet} (n : 单纯形范畴) (x : S.obj (op n))
  证明: rfl

@[simp]
-/
lemma yonedaEquiv_symm_app {S : SSet} (n : SimplexCategory) (x : S.obj (op n))
    (α : (stdSimplex.obj n).obj (op n)) :
    (yonedaEquiv.symm x).app (op n) α = S.map (SSet.stdSimplex.objEquiv α).op x := rfl

@[simp]
/--
lemma `yonedaEquiv_symm_stdSimplex_id` / 引理 `yonedaEquiv_symm_stdSimplex_id`

English:
lemma yonedaEquiv_symm_stdSimplex_id
  given: (n : SimplexCategory)
  proof: yonedaEquiv.symm_apply_eq.mpr rfl

中文:
引理 yonedaEquiv_symm_stdSimplex_id
  条件: (n : 单纯形范畴)
  证明: yonedaEquiv.symm_apply_eq.mpr rfl

Depends on / 依赖: stdSimplex, stdSimplex.obj
-/
lemma yonedaEquiv_symm_stdSimplex_id (n : SimplexCategory) :
    yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm (β := n ⟶ _) (𝟙 n)) = 𝟙 (stdSimplex.obj n) :=
  yonedaEquiv.symm_apply_eq.mpr rfl

open Finset Opposite SimplexCategory

/--
lemma `yonedaEquiv_symm_app_objEquiv_symm` / 引理 `yonedaEquiv_symm_app_objEquiv_symm`

English:
lemma yonedaEquiv_symm_app_objEquiv_symm
  statement: {X : SSet.{u}} {n : SimplexCategory}
  proof: rfl

中文:
引理 yonedaEquiv_symm_app_objEquiv_symm
  结论: {X : SSet.{u}} {n : 单纯形范畴}
  证明: rfl
-/
lemma yonedaEquiv_symm_app_objEquiv_symm {X : SSet.{u}} {n : SimplexCategory}
    (x : X.obj (op n)) {m : SimplexCategoryᵒᵖ} (f : unop m ⟶ n) :
    dsimp% (yonedaEquiv.symm x).app _ (stdSimplex.objEquiv.symm f) =
      X.map f.op x :=
  rfl

/--
lemma `opObjEquiv_yonedaEquiv_const` / 引理 `opObjEquiv_yonedaEquiv_const`

English:
lemma opObjEquiv_yonedaEquiv_const
  given: {X : SSet.{u}} {n : SimplexCategory} (x : X.op _⦋0⦌)
  proof: rfl

中文:
引理 opObjEquiv_yonedaEquiv_const
  条件: {X : SSet.{u}} {n : 单纯形范畴} (x : X.op _⦋0⦌)
  证明: rfl

Depends on / 依赖: yonedaEquiv
-/
lemma opObjEquiv_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x : X.op _⦋0⦌) :
    opObjEquiv (n := op n) (yonedaEquiv (const x)) =
      yonedaEquiv (const (opObjEquiv x)) := rfl

/--
lemma `opObjEquiv_symm_yonedaEquiv_const` / 引理 `opObjEquiv_symm_yonedaEquiv_const`

English:
lemma opObjEquiv_symm_yonedaEquiv_const
  given: {X : SSet.{u}} {n : SimplexCategory} (x : X _⦋0⦌)
  proof: rfl

中文:
引理 opObjEquiv_symm_yonedaEquiv_const
  条件: {X : SSet.{u}} {n : 单纯形范畴} (x : X _⦋0⦌)
  证明: rfl

Depends on / 依赖: yonedaEquiv
-/
lemma opObjEquiv_symm_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x : X _⦋0⦌) :
    (opObjEquiv (n := op n)).symm (yonedaEquiv (const x)) =
      yonedaEquiv (const (opObjEquiv.symm x)) := rfl

namespace stdSimplex

/--
lemma `δ_apply` / 引理 `δ_apply`

English:
lemma δ_apply
  given: {n d : Nat} (x : (Δ[n] _⦋d + 1⦌ : Type u)) (i : Fin (d + 2)) (j : Fin (d + 1))
  proof: rfl

中文:
引理 δ_apply
  条件: {n d : 自然数} (x : (Δ[n] _⦋d + 1⦌ : 类型u)) (i : 有限集 (d + 2)) (j : 有限集 (d + 1))
  证明: rfl
-/
lemma δ_apply {n d : Nat} (x : (Δ[n] _⦋d + 1⦌ : Type u)) (i : Fin (d + 2)) (j : Fin (d + 1)) :
    Δ[n].δ i x j = x (i.succAbove j) := rfl

/--
lemma `σ_apply` / 引理 `σ_apply`

English:
lemma σ_apply
  given: {n d : Nat} (x : (Δ[n] _⦋d⦌ : Type u)) (i : Fin (d + 1)) (j : Fin (d + 2))
  proof: rfl

@[simp]

中文:
引理 σ_apply
  条件: {n d : 自然数} (x : (Δ[n] _⦋d⦌ : 类型u)) (i : 有限集 (d + 1)) (j : 有限集 (d + 2))
  证明: rfl

@[simp]
-/
lemma σ_apply {n d : Nat} (x : (Δ[n] _⦋d⦌ : Type u)) (i : Fin (d + 1)) (j : Fin (d + 2)) :
    Δ[n].σ i x j = x (i.predAbove j) := rfl

@[simp]
/--
lemma `objEquiv_yonedaEquiv_id` / 引理 `objEquiv_yonedaEquiv_id`

English:
lemma objEquiv_yonedaEquiv_id
  given: (n : Nat)
  proof: rfl

中文:
引理 objEquiv_yonedaEquiv_id
  条件: (n : 自然数)
  证明: rfl
-/
lemma objEquiv_yonedaEquiv_id (n : Nat) :
    dsimp% objEquiv (yonedaEquiv.{u} (𝟙 Δ[n])) = 𝟙 _ := rfl

/--
lemma `map_objEquiv_op_apply` / 引理 `map_objEquiv_op_apply`

English:
lemma map_objEquiv_op_apply
  proof: by
  rfl

中文:
引理 map_objEquiv_op_apply
  证明: by
  rfl
-/
lemma map_objEquiv_op_apply
    {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    {m : SimplexCategoryᵒᵖ} (y : (stdSimplex.obj n).obj m) :
    dsimp% X.map (stdSimplex.objEquiv y).op x = (yonedaEquiv.symm x).app m y := by
  rfl

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (n : Nat) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ)
  body: objMk (OrderHom.const _ k)

@[simp]

中文:
定义 const
  签名: (n : 自然数) (k : 有限集 (n + 1)) (m : SimplexCategoryᵒᵖ)
  定义体: objMk (OrderHom.const _ k)

@[simp]

Depends on / 依赖: OrderHom, OrderHom.const
-/
def const (n : Nat) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m :=
  objMk (OrderHom.const _ k)

@[simp]
/--
lemma `const_down_toOrderHom` / 引理 `const_down_toOrderHom`

English:
lemma const_down_toOrderHom
  given: (n : Nat) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ)
  proof: rfl

中文:
引理 const_down_toOrderHom
  条件: (n : 自然数) (k : 有限集 (n + 1)) (m : SimplexCategoryᵒᵖ)
  证明: rfl
-/
lemma const_down_toOrderHom (n : Nat) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) :
    (const n k m).down.toOrderHom = OrderHom.const _ k :=
  rfl

/-- The `0`-simplices of `Δ[n]` identify to the elements in `Fin (n + 1)`. -/
@[simps]
/--
Definition of `obj₀Equiv` / `obj₀Equiv` 的定义

English:
definition obj₀Equiv
  signature: {n : Nat}
  body: x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl

中文:
定义 obj₀Equiv
  签名: {n : 自然数}
  定义体: x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl
-/
def obj₀Equiv {n : Nat} : Δ[n] _⦋0⦌ ≃ Fin (n + 1) where
  toFun x := x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl

/--
lemma `δ_one_eq_const` / 引理 `δ_one_eq_const`

English:
lemma δ_one_eq_const
  statement: stdSimplex.{u}.δ (1 : Fin 2) = SSet.const (obj₀Equiv.symm 0)
  proof: by
  decide

中文:
引理 δ_one_eq_const
  结论: stdSimplex.{u}.δ (1 : 有限集 2) = SSet.const (obj₀Equiv.symm 0)
  证明: by
  decide
-/
lemma δ_one_eq_const : stdSimplex.{u}.δ (1 : Fin 2) = SSet.const (obj₀Equiv.symm 0) := by
  decide

/--
lemma `δ_zero_eq_const` / 引理 `δ_zero_eq_const`

English:
lemma δ_zero_eq_const
  statement: stdSimplex.{u}.δ (0 : Fin 2) = SSet.const (obj₀Equiv.symm 1)
  proof: by
  decide

中文:
引理 δ_zero_eq_const
  结论: stdSimplex.{u}.δ (0 : 有限集 2) = SSet.const (obj₀Equiv.symm 1)
  证明: by
  decide
-/
lemma δ_zero_eq_const : stdSimplex.{u}.δ (0 : Fin 2) = SSet.const (obj₀Equiv.symm 1) := by
  decide

/--
Definition of `edge` / `edge` 的定义

English:
definition edge
  signature: (n : Nat) (a b : Fin (n + 1)) (hab : a <= b)
  body: by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab

中文:
定义 edge
  签名: (n : 自然数) (a b : 有限集 (n + 1)) (hab : a <= b)
  定义体: by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab

Depends on / 依赖: Fin.forall_fin_one, Fin.mk_le_mk.mpr, Fin.monotone_iff_le_succ, forall_fin_one, len_mk, mk_le_mk, monotone_iff_le_succ, unop_op
-/
def edge (n : Nat) (a b : Fin (n + 1)) (hab : a <= b) : Δ[n] _⦋1⦌ := by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab

/--
lemma `coe_edge_down_toOrderHom` / 引理 `coe_edge_down_toOrderHom`

English:
lemma coe_edge_down_toOrderHom
  given: (n : Nat) (a b : Fin (n + 1)) (hab : a <= b)
  proof: rfl

中文:
引理 coe_edge_down_toOrderHom
  条件: (n : 自然数) (a b : 有限集 (n + 1)) (hab : a <= b)
  证明: rfl
-/
lemma coe_edge_down_toOrderHom (n : Nat) (a b : Fin (n + 1)) (hab : a <= b) :
    ↑(edge n a b hab).down.toOrderHom = ![a, b] :=
  rfl

/--
Definition of `triangle` / `triangle` 的定义

English:
definition triangle
  signature: {n : Nat} (a b c : Fin (n + 1)) (hab : a <= b) (hbc : b <= c)
  body: by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, true_and]

中文:
定义 triangle
  签名: {n : 自然数} (a b c : 有限集 (n + 1)) (hab : a <= b) (hbc : b <= c)
  定义体: by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, true_and]

Depends on / 依赖: Fin.forall_fin_two, Fin.monotone_iff_le_succ, forall_fin_two, len_mk, monotone_iff_le_succ, true_and, unop_op
-/
def triangle {n : Nat} (a b c : Fin (n + 1)) (hab : a <= b) (hbc : b <= c) : Δ[n] _⦋2⦌ := by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, true_and]

/--
lemma `coe_triangle_down_toOrderHom` / 引理 `coe_triangle_down_toOrderHom`

English:
lemma coe_triangle_down_toOrderHom
  given: {n : Nat} (a b c : Fin (n + 1)) (hab : a <= b) (hbc : b <= c)
  proof: rfl

中文:
引理 coe_triangle_down_toOrderHom
  条件: {n : 自然数} (a b c : 有限集 (n + 1)) (hab : a <= b) (hbc : b <= c)
  证明: rfl
-/
lemma coe_triangle_down_toOrderHom {n : Nat} (a b c : Fin (n + 1)) (hab : a <= b) (hbc : b <= c) :
    ↑(triangle a b c hab hbc).down.toOrderHom = ![a, b, c] :=
  rfl

attribute [local simp] image_subset_iff

/-- Given `S : Finset (Fin (n + 1))`, this is the corresponding face of `Δ[n]`,
as a subcomplex. -/
@[simps -isSimp obj]
/--
Definition of `face` / `face` 的定义

English:
definition face
  signature: {n : Nat} (S : Finset (Fin (n + 1)))
  body: Set.ofPred (fun f => Finset.image (objEquiv f).toOrderHom ⊤ <= S)
  map {U V} i := by aesop

中文:
定义 face
  签名: {n : 自然数} (S : 有限集 (有限集 (n + 1)))
  定义体: Set.ofPred (fun f => Finset.image (objEquiv f).toOrderHom ⊤ <= S)
  map {U V} i := by aesop

Depends on / 依赖: Finset, Finset.image, Set.ofPred, objEquiv, ofPred, toOrderHom
-/
def face {n : Nat} (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
  obj U := Set.ofPred (fun f => Finset.image (objEquiv f).toOrderHom ⊤ <= S)
  map {U V} i := by aesop

attribute [local simp] face_obj

@[simp]
/--
lemma `mem_face_iff` / 引理 `mem_face_iff`

English:
lemma mem_face_iff
  given: {n : Nat} (S : Finset (Fin (n + 1))) {d : Nat} (x : (Δ[n] : SSet.{u}) _⦋d⦌)
  proof: by
  simp

中文:
引理 mem_face_iff
  条件: {n : 自然数} (S : 有限集 (有限集 (n + 1))) {d : 自然数} (x : (Δ[n] : SSet.{u}) _⦋d⦌)
  证明: by
  simp
-/
lemma mem_face_iff {n : Nat} (S : Finset (Fin (n + 1))) {d : Nat} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x in (face S).obj _ ↔ forall (i : Fin (d + 1)), x i in S := by
  simp

/--
lemma `face_inter_face` / 引理 `face_inter_face`

English:
lemma face_inter_face
  given: {n : Nat} (S₁ S₂ : Finset (Fin (n + 1)))
  proof: by
  aesop

@[simp]

中文:
引理 face_inter_face
  条件: {n : 自然数} (S₁ S₂ : 有限集 (有限集 (n + 1)))
  证明: by
  aesop

@[simp]
-/
lemma face_inter_face {n : Nat} (S₁ S₂ : Finset (Fin (n + 1))) :
    face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂) := by
  aesop

@[simp]
/--
lemma `face_empty` / 引理 `face_empty`

English:
lemma face_empty
  given: (n : Nat)
  proof: by
  ext
  simpa using Finset.univ_neq_empty _

@[simp]

中文:
引理 face_empty
  条件: (n : 自然数)
  证明: by
  ext
  simpa using Finset.univ_neq_empty _

@[simp]

Depends on / 依赖: Finset, Finset.univ_neq_empty, univ_neq_empty
-/
lemma face_empty (n : Nat) :
    face.{u} (∅ : Finset (Fin (n + 1))) = ⊥ := by
  ext
  simpa using Finset.univ_neq_empty _

@[simp]
/--
lemma `face_univ` / 引理 `face_univ`

English:
lemma face_univ
  given: (n : Nat)
  proof: by
  ext
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  apply Finset.subset_univ

中文:
引理 face_univ
  条件: (n : 自然数)
  证明: by
  ext
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  apply Finset.subset_univ

Depends on / 依赖: Finset, Finset.subset_univ, Set.mem_univ, Set.top_eq_univ, Subfunctor, Subfunctor.top_obj, iff_true, mem_univ, subset_univ, top_eq_univ, top_obj
-/
lemma face_univ (n : Nat) :
    face.{u} (.univ : Finset (Fin (n + 1))) = ⊤ := by
  ext
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  apply Finset.subset_univ

end stdSimplex

/--
lemma `yonedaEquiv_comp` / 引理 `yonedaEquiv_comp`

English:
lemma yonedaEquiv_comp
  statement: {X Y : SSet.{u}} {n : SimplexCategory}
  proof: rfl

@[simp high]

中文:
引理 yonedaEquiv_comp
  结论: {X Y : SSet.{u}} {n : 单纯形范畴}
  证明: rfl

@[simp high]
-/
lemma yonedaEquiv_comp {X Y : SSet.{u}} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ X) (g : X ⟶ Y) :
    yonedaEquiv (f ≫ g) = g.app _ (yonedaEquiv f) := rfl

@[simp high]
/--
lemma `yonedaEquiv_symm_app_id` / 引理 `yonedaEquiv_symm_app_id`

English:
lemma yonedaEquiv_symm_app_id
  given: {X : SSet.{u}} {n : Nat} (x : X _⦋n⦌)
  proof: by
  simp

中文:
引理 yonedaEquiv_symm_app_id
  条件: {X : SSet.{u}} {n : 自然数} (x : X _⦋n⦌)
  证明: by
  simp
-/
lemma yonedaEquiv_symm_app_id {X : SSet.{u}} {n : Nat} (x : X _⦋n⦌) :
    (yonedaEquiv.symm x).app _ (yonedaEquiv (𝟙 _)) = x := by
  simp

/--
lemma `yonedaEquiv_naturality` / 引理 `yonedaEquiv_naturality`

English:
lemma yonedaEquiv_naturality
  statement: {X : SSet} {m n : SimplexCategory}
  proof: uliftYonedaEquiv_naturality _ _

@[reassoc]

中文:
引理 yonedaEquiv_naturality
  结论: {X : SSet} {m n : 单纯形范畴}
  证明: uliftYonedaEquiv_naturality _ _

@[reassoc]

Depends on / 依赖: uliftYonedaEquiv_naturality
-/
lemma yonedaEquiv_naturality {X : SSet} {m n : SimplexCategory}
    (f : m ⟶ n) (g : stdSimplex.obj n ⟶ X) :
    X.map f.op (yonedaEquiv g) = yonedaEquiv (stdSimplex.map f ≫ g) :=
  uliftYonedaEquiv_naturality _ _

@[reassoc]
/--
lemma `yonedaEquiv_symm_naturality_left` / 引理 `yonedaEquiv_symm_naturality_left`

English:
lemma yonedaEquiv_symm_naturality_left
  statement: {X : SSet} {m n : SimplexCategory}
  proof: by
  rw [yonedaEquiv.eq_symm_apply]; rw [← yonedaEquiv_naturality]; rw [yonedaEquiv.apply_symm_apply]

中文:
引理 yonedaEquiv_symm_naturality_left
  结论: {X : SSet} {m n : 单纯形范畴}
  证明: by
  rw [yonedaEquiv.eq_symm_apply]; rw [← yonedaEquiv_naturality]; rw [yonedaEquiv.apply_symm_apply]

Depends on / 依赖: apply_symm_apply, eq_symm_apply, yonedaEquiv, yonedaEquiv.apply_symm_apply, yonedaEquiv.eq_symm_apply, yonedaEquiv_naturality
-/
lemma yonedaEquiv_symm_naturality_left {X : SSet} {m n : SimplexCategory}
    (f : m ⟶ n) (g : X.obj (Opposite.op n)) :
    stdSimplex.map f ≫ yonedaEquiv.symm g = yonedaEquiv.symm (X.map f.op g) := by
  rw [yonedaEquiv.eq_symm_apply]; rw [← yonedaEquiv_naturality]; rw [yonedaEquiv.apply_symm_apply]

/--
lemma `stdSimplex.δ_comp_yonedaEquiv_symm` / 引理 `stdSimplex.δ_comp_yonedaEquiv_symm`

English:
lemma stdSimplex.δ_comp_yonedaEquiv_symm
  proof: yonedaEquiv_symm_naturality_left ..

中文:
引理 stdSimplex.δ_comp_yonedaEquiv_symm
  证明: yonedaEquiv_symm_naturality_left ..

Depends on / 依赖: yonedaEquiv_symm_naturality_left
-/
lemma stdSimplex.δ_comp_yonedaEquiv_symm
    {X : SSet.{u}} {n : Nat} (x : X _⦋n + 1⦌) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.δ i x) :=
  yonedaEquiv_symm_naturality_left ..

/--
lemma `stdSimplex.σ_comp_yonedaEquiv_symm` / 引理 `stdSimplex.σ_comp_yonedaEquiv_symm`

English:
lemma stdSimplex.σ_comp_yonedaEquiv_symm
  proof: yonedaEquiv_symm_naturality_left ..

中文:
引理 stdSimplex.σ_comp_yonedaEquiv_symm
  证明: yonedaEquiv_symm_naturality_left ..

Depends on / 依赖: yonedaEquiv_symm_naturality_left
-/
lemma stdSimplex.σ_comp_yonedaEquiv_symm
    {X : SSet.{u}} {n : Nat} (x : X _⦋n⦌) (i : Fin (n + 1)) :
    stdSimplex.σ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.σ i x) :=
  yonedaEquiv_symm_naturality_left ..

/--
lemma `stdSimplex.yonedaEquiv_δ_comp` / 引理 `stdSimplex.yonedaEquiv_δ_comp`

English:
lemma stdSimplex.yonedaEquiv_δ_comp
  proof: (yonedaEquiv_naturality ..).symm

中文:
引理 stdSimplex.yonedaEquiv_δ_comp
  证明: (yonedaEquiv_naturality ..).symm

Depends on / 依赖: yonedaEquiv_naturality
-/
lemma stdSimplex.yonedaEquiv_δ_comp
    {X : SSet.{u}} {n : Nat} (g : Δ[n + 1] ⟶ X) (i : Fin (n + 2)) :
    yonedaEquiv (stdSimplex.δ i ≫ g) = X.δ i (yonedaEquiv g) :=
  (yonedaEquiv_naturality ..).symm

/--
lemma `stdSimplex.yonedaEquiv_σ_comp` / 引理 `stdSimplex.yonedaEquiv_σ_comp`

English:
lemma stdSimplex.yonedaEquiv_σ_comp
  proof: (yonedaEquiv_naturality ..).symm

中文:
引理 stdSimplex.yonedaEquiv_σ_comp
  证明: (yonedaEquiv_naturality ..).symm

Depends on / 依赖: yonedaEquiv_naturality
-/
lemma stdSimplex.yonedaEquiv_σ_comp
    {X : SSet.{u}} {n : Nat} (g : Δ[n] ⟶ X) (i : Fin (n + 1)) :
    yonedaEquiv (stdSimplex.σ i ≫ g) = X.σ i (yonedaEquiv g) :=
  (yonedaEquiv_naturality ..).symm

namespace Subcomplex

variable {X : SSet.{u}}

/--
lemma `range_eq_ofSimplex` / 引理 `range_eq_ofSimplex`

English:
lemma range_eq_ofSimplex
  given: {n : Nat} (f : Δ[n] ⟶ X)
  proof: Subfunctor.range_eq_ofSection' _

中文:
引理 range_eq_ofSimplex
  条件: {n : 自然数} (f : Δ[n] ⟶ X)
  证明: Subfunctor.range_eq_ofSection' _

Depends on / 依赖: Subfunctor, Subfunctor.range_eq_ofSection, range_eq_ofSection
-/
lemma range_eq_ofSimplex {n : Nat} (f : Δ[n] ⟶ X) :
    range f = ofSimplex (yonedaEquiv f) :=
  Subfunctor.range_eq_ofSection' _

/--
lemma `yonedaEquiv_coe` / 引理 `yonedaEquiv_coe`

English:
lemma yonedaEquiv_coe
  statement: {A : X.Subcomplex} {n : SimplexCategory}
  proof: by
  rfl

中文:
引理 yonedaEquiv_coe
  结论: {A : X.子复形} {n : 单纯形范畴}
  证明: by
  rfl
-/
lemma yonedaEquiv_coe {A : X.Subcomplex} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ A) :
    (yonedaEquiv f).val = yonedaEquiv (f ≫ A.ι) := by
  rfl

end Subcomplex

namespace stdSimplex

/--
lemma `obj₀Equiv_symm_mem_face_iff` / 引理 `obj₀Equiv_symm_mem_face_iff`

English:
lemma obj₀Equiv_symm_mem_face_iff
  proof: ⟨fun h => by simpa using! h, by aesop⟩

中文:
引理 obj₀Equiv_symm_mem_face_iff
  证明: ⟨fun h => by simpa using! h, by aesop⟩
-/
lemma obj₀Equiv_symm_mem_face_iff
    {n : Nat} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (obj₀Equiv.symm i) in (face.{u} S).obj (op (.mk 0)) ↔ i in S :=
  ⟨fun h => by simpa using! h, by aesop⟩

/--
lemma `face_le_face_iff` / 引理 `face_le_face_iff`

English:
lemma face_le_face_iff
  given: {n : Nat} (S₁ S₂ : Finset (Fin (n + 1)))
  proof: by
  refine ⟨fun h i hi => ?_, fun h d a ha => ha.trans h⟩
  simp only [← obj₀Equiv_symm_mem_face_iff.{u}] at hi ⊢
  exact h _ hi

中文:
引理 face_le_face_iff
  条件: {n : 自然数} (S₁ S₂ : 有限集 (有限集 (n + 1)))
  证明: by
  refine ⟨fun h i hi => ?_, fun h d a ha => ha.trans h⟩
  simp only [← obj₀Equiv_symm_mem_face_iff.{u}] at hi ⊢
  exact h _ hi

Depends on / 依赖: ha.trans
-/
lemma face_le_face_iff {n : Nat} (S₁ S₂ : Finset (Fin (n + 1))) :
    face.{u} S₁ <= face S₂ ↔ S₁ <= S₂ := by
  refine ⟨fun h i hi => ?_, fun h d a ha => ha.trans h⟩
  simp only [← obj₀Equiv_symm_mem_face_iff.{u}] at hi ⊢
  exact h _ hi

/--
lemma `face_eq_ofSimplex` / 引理 `face_eq_ofSimplex`

English:
lemma face_eq_ofSimplex
  given: {n : Nat} (S : Finset (Fin (n + 1))) (m : Nat) (e : Fin (m + 1) ≃o S)
  proof: by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction k using SimplexCategory.rec with | _ k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) ->o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv x).toOrderHom.monotone }
    refine ⟨Quiver.Hom.op
      (SimplexCategory.Hom.mk 

中文:
引理 face_eq_ofSimplex
  条件: {n : 自然数} (S : 有限集 (有限集 (n + 1))) (m : 自然数) (e : 有限集 (m + 1) ≃o S)
  证明: by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction k using SimplexCategory.rec with | _ k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) ->o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv x).toOrderHom.monotone }
    refine ⟨Quiver.Hom.op
      (SimplexCategory.Hom.mk 
-/
lemma face_eq_ofSimplex {n : Nat} (S : Finset (Fin (n + 1))) (m : Nat) (e : Fin (m + 1) ≃o S) :
    face.{u} S =
      Subcomplex.ofSimplex (X := Δ[n])
        (objMk ((OrderHom.Subtype.val _).comp
          e.toOrderEmbedding.toOrderHom)) := by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction k using SimplexCategory.rec with | _ k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) ->o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv x).toOrderHom.monotone }
    refine ⟨Quiver.Hom.op
      (SimplexCategory.Hom.mk ((e.symm.toOrderEmbedding.toOrderHom.comp φ))), ?_⟩
    ext j : 1
    simpa only [Subtype.ext_iff] using! e.apply_symm_apply ⟨_, hx j⟩
  · simp

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `faceRepresentableBy` / `faceRepresentableBy` 的定义

English:
definition faceRepresentableBy
  signature: {n : Nat} (S : Finset (Fin (n + 1)))
  body: { toFun f := ⟨objMk ((OrderHom.Subtype.val (· in S)).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ => by aesop⟩
      invFun := fun ⟨x, hx⟩ => SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv x).toOrderHom i, hx (by simp)⟩
          monotone' i₁ i₂ h := e.symm

中文:
定义 faceRepresentableBy
  签名: {n : 自然数} (S : 有限集 (有限集 (n + 1)))
  定义体: { toFun f := ⟨objMk ((OrderHom.Subtype.val (· in S)).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ => by aesop⟩
      invFun := fun ⟨x, hx⟩ => SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv x).toOrderHom i, hx (by simp)⟩
          monotone' i₁ i₂ h := e.symm

Depends on / 依赖: OrderHom, OrderHom.Subtype.val, OrderHom.monotone, SimplexCategory, SimplexCategory.Hom.mk, SimplexCategory.rec, Subtype, Subtype.mk_le_mk, congr_, e.symm, e.symm.monotone, e.symm_apply_apply, e.toOrderEmbedding.toOrderHom.comp, f.toOrderHom, invFun, left_inv, mk_le_mk, monotone, objEquiv, right_inv
-/
def faceRepresentableBy {n : Nat} (S : Finset (Fin (n + 1)))
    (m : Nat) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy ⦋m⦌ where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val (· in S)).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ => by aesop⟩
      invFun := fun ⟨x, hx⟩ => SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv x).toOrderHom i, hx (by simp)⟩
          monotone' i₁ i₂ h := e.symm.monotone (by
            simp only [Subtype.mk_le_mk]
            exact OrderHom.monotone _ h) }
      left_inv f := by
        ext i : 3
        apply e.symm_apply_apply
      right_inv := fun ⟨x, hx⟩ => by
        induction j using SimplexCategory.rec with | _ j
        dsimp
        ext i : 2
        exact congr_arg Subtype.val
          (e.apply_symm_apply ⟨(objEquiv x).toOrderHom i, _⟩) }
  homEquiv_comp f g := by aesop

/--
Definition of `isoOfRepresentableBy` / `isoOfRepresentableBy` 的定义

English:
definition isoOfRepresentableBy
  signature: {X : SSet.{u}} {m : Nat} (h : X.RepresentableBy ⦋m⦌)
  body: NatIso.ofComponents (fun n => Equiv.toIso (objEquiv.trans h.homEquiv))
    (fun _ => by ext; apply h.homEquiv_comp)

中文:
定义 isoOfRepresentableBy
  签名: {X : SSet.{u}} {m : 自然数} (h : X.可表示 ⦋m⦌)
  定义体: NatIso.ofComponents (fun n => Equiv.toIso (objEquiv.trans h.homEquiv))
    (fun _ => by ext; apply h.homEquiv_comp)

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, h.homEquiv, h.homEquiv_comp, homEquiv, homEquiv_comp, objEquiv, objEquiv.trans, ofComponents
-/
def isoOfRepresentableBy {X : SSet.{u}} {m : Nat} (h : X.RepresentableBy ⦋m⦌) :
    Δ[m] ≅ X :=
  NatIso.ofComponents (fun n => Equiv.toIso (objEquiv.trans h.homEquiv))
    (fun _ => by ext; apply h.homEquiv_comp)

/--
lemma `ofSimplex_yonedaEquiv_δ` / 引理 `ofSimplex_yonedaEquiv_δ`

English:
lemma ofSimplex_yonedaEquiv_δ
  given: {n : Nat} (i : Fin (n + 2))
  proof: (face_eq_ofSimplex _ _ (Fin.succAboveOrderIso i)).symm

@[simp]

中文:
引理 ofSimplex_yonedaEquiv_δ
  条件: {n : 自然数} (i : 有限集 (n + 2))
  证明: (face_eq_ofSimplex _ _ (Fin.succAboveOrderIso i)).symm

@[simp]

Depends on / 依赖: Fin.succAboveOrderIso, face_eq_ofSimplex, succAboveOrderIso
-/
lemma ofSimplex_yonedaEquiv_δ {n : Nat} (i : Fin (n + 2)) :
    Subcomplex.ofSimplex (yonedaEquiv (stdSimplex.δ i)) = face.{u} {i}ᶜ :=
  (face_eq_ofSimplex _ _ (Fin.succAboveOrderIso i)).symm

@[simp]
/--
lemma `range_δ` / 引理 `range_δ`

English:
lemma range_δ
  given: {n : Nat} (i : Fin (n + 2))
  proof: by
  rw [Subcomplex.range_eq_ofSimplex]
  exact ofSimplex_yonedaEquiv_δ i

中文:
引理 range_δ
  条件: {n : 自然数} (i : 有限集 (n + 2))
  证明: by
  rw [Subcomplex.range_eq_ofSimplex]
  exact ofSimplex_yonedaEquiv_δ i

Depends on / 依赖: Subcomplex, Subcomplex.range_eq_ofSimplex, range_eq_ofSimplex
-/
lemma range_δ {n : Nat} (i : Fin (n + 2)) :
    Subcomplex.range (stdSimplex.δ i) = face.{u} {i}ᶜ := by
  rw [Subcomplex.range_eq_ofSimplex]
  exact ofSimplex_yonedaEquiv_δ i

/-- The standard simplex identifies to the nerve to the preordered type
`ULift (Fin (n + 1))`. -/
@[pp_with_univ]
/--
Definition of `isoNerve` / `isoNerve` 的定义

English:
definition isoNerve
  signature: (n : Nat)
  body: NatIso.ofComponents (fun d => Equiv.toIso (objEquiv.trans
    { toFun f := (ULift.orderIso.symm.monotone.comp f.toOrderHom.monotone).functor
      invFun f :=
        SimplexCategory.Hom.mk
          (ULift.orderIso.toOrderEmbedding.toOrderHom.comp f.toOrderHom)
      left_inv _ := by aesop }))

@[s

中文:
定义 isoNerve
  签名: (n : 自然数)
  定义体: NatIso.ofComponents (fun d => Equiv.toIso (objEquiv.trans
    { toFun f := (ULift.orderIso.symm.monotone.comp f.toOrderHom.monotone).functor
      invFun f :=
        SimplexCategory.Hom.mk
          (ULift.orderIso.toOrderEmbedding.toOrderHom.comp f.toOrderHom)
      left_inv _ := by aesop }))

@[s

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, SimplexCategory, SimplexCategory.Hom.mk, ULift.orderIso.symm.monotone.comp, ULift.orderIso.toOrderEmbedding.toOrderHom.comp, f.toOrderHom, f.toOrderHom.monotone, functor, invFun, left_inv, monotone, objEquiv, objEquiv.trans, ofComponents, orderIso, toOrderEmbedding, toOrderHom
-/
def isoNerve (n : Nat) :
    (Δ[n] : SSet.{u}) ≅ nerve (ULift.{u} (Fin (n + 1))) :=
  NatIso.ofComponents (fun d => Equiv.toIso (objEquiv.trans
    { toFun f := (ULift.orderIso.symm.monotone.comp f.toOrderHom.monotone).functor
      invFun f :=
        SimplexCategory.Hom.mk
          (ULift.orderIso.toOrderEmbedding.toOrderHom.comp f.toOrderHom)
      left_inv _ := by aesop }))

@[simp]
/--
lemma `isoNerve_hom_app_apply` / 引理 `isoNerve_hom_app_apply`

English:
lemma isoNerve_hom_app_apply
  statement: {n d : Nat}
  proof: rfl

@[simp]

中文:
引理 isoNerve_hom_app_apply
  结论: {n d : 自然数}
  证明: rfl

@[simp]
-/
lemma isoNerve_hom_app_apply {n d : Nat}
    (s : (Δ[n] _⦋d⦌)) (i : Fin (d + 1)) :
    dsimp% ((isoNerve.{u} n).hom.app _ s).obj i = ULift.up (s i) := rfl

@[simp]
/--
lemma `isoNerve_inv_app_apply` / 引理 `isoNerve_inv_app_apply`

English:
lemma isoNerve_inv_app_apply
  statement: {n d : Nat}
  proof: rfl

中文:
引理 isoNerve_inv_app_apply
  结论: {n d : 自然数}
  证明: rfl
-/
lemma isoNerve_inv_app_apply {n d : Nat}
    (F : (nerve (ULift.{u} (Fin (n + 1)))) _⦋d⦌) (i : Fin (d + 1)) :
    dsimp% (isoNerve.{u} n).inv.app _ F i = (F.obj i).down := rfl

/--
lemma `mem_nonDegenerate_iff_strictMono` / 引理 `mem_nonDegenerate_iff_strictMono`

English:
lemma mem_nonDegenerate_iff_strictMono
  given: {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌)
  proof: by
  rw [← nonDegenerate_iff_of_mono (isoNerve n).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

中文:
引理 mem_nonDegenerate_iff_strictMono
  条件: {n d : 自然数} (s : (Δ[n] : SSet.{u}) _⦋d⦌)
  证明: by
  rw [← nonDegenerate_iff_of_mono (isoNerve n).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

Depends on / 依赖: PartialOrder, PartialOrder.mem_nerve_nonDegenerate_iff_strictMono, isoNerve, mem_nerve_nonDegenerate_iff_strictMono, nonDegenerate_iff_of_mono
-/
lemma mem_nonDegenerate_iff_strictMono {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    s in Δ[n].nonDegenerate d ↔ StrictMono s := by
  rw [← nonDegenerate_iff_of_mono (isoNerve n).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

/--
lemma `mem_nonDegenerate_iff_mono` / 引理 `mem_nonDegenerate_iff_mono`

English:
lemma mem_nonDegenerate_iff_mono
  given: {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌)
  proof: by
  rw [mem_nonDegenerate_iff_strictMono]; rw [SimplexCategory.mono_iff_injective]
  refine ⟨fun h => h.injective, fun h => ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain h' | h' := (stdSimplex.monotone_apply s i.castSucc_le_succ).lt_or_eq
  · exact h'
  · simpa [Fin.ext_iff] using h h'

中文:
引理 mem_nonDegenerate_iff_mono
  条件: {n d : 自然数} (s : (Δ[n] : SSet.{u}) _⦋d⦌)
  证明: by
  rw [mem_nonDegenerate_iff_strictMono]; rw [SimplexCategory.mono_iff_injective]
  refine ⟨fun h => h.injective, fun h => ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain h' | h' := (stdSimplex.monotone_apply s i.castSucc_le_succ).lt_or_eq
  · exact h'
  · simpa [Fin.ext_iff] using h h'

Depends on / 依赖: Fin.ext_iff, Fin.strictMono_iff_lt_succ, SimplexCategory, SimplexCategory.mono_iff_injective, castSucc_le_succ, ext_iff, h.injective, i.castSucc_le_succ, injective, lt_or_eq, mem_nonDegenerate_iff_strictMono, mono_iff_injective, monotone_apply, stdSimplex, stdSimplex.monotone_apply, strictMono_iff_lt_succ
-/
lemma mem_nonDegenerate_iff_mono {n d : Nat} (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    s in Δ[n].nonDegenerate d ↔ Mono (objEquiv s) := by
  rw [mem_nonDegenerate_iff_strictMono]; rw [SimplexCategory.mono_iff_injective]
  refine ⟨fun h => h.injective, fun h => ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain h' | h' := (stdSimplex.monotone_apply s i.castSucc_le_succ).lt_or_eq
  · exact h'
  · simpa [Fin.ext_iff] using h h'

/--
lemma `objEquiv_symm_mem_nonDegenerate_iff_mono` / 引理 `objEquiv_symm_mem_nonDegenerate_iff_mono`

English:
lemma objEquiv_symm_mem_nonDegenerate_iff_mono
  given: {n d : Nat} (f : ⦋d⦌ ⟶ ⦋n⦌)
  proof: by
  simp [mem_nonDegenerate_iff_mono]

中文:
引理 objEquiv_symm_mem_nonDegenerate_iff_mono
  条件: {n d : 自然数} (f : ⦋d⦌ ⟶ ⦋n⦌)
  证明: by
  simp [mem_nonDegenerate_iff_mono]

Depends on / 依赖: mem_nonDegenerate_iff_mono, nonDegenerate
-/
lemma objEquiv_symm_mem_nonDegenerate_iff_mono {n d : Nat} (f : ⦋d⦌ ⟶ ⦋n⦌) :
    (objEquiv.{u} (m := (op ⦋d⦌))).symm f in Δ[n].nonDegenerate d ↔ Mono f := by
  simp [mem_nonDegenerate_iff_mono]

/-- Nondegenerate `d`-dimensional simplices of the standard simplex `Δ[n]`
identify to order embeddings `Fin (d + 1) ↪o Fin (n + 1)`. -/
@[simps! apply_apply symm_apply_coe]
/--
Definition of `nonDegenerateEquiv` / `nonDegenerateEquiv` 的定义

English:
definition nonDegenerateEquiv
  signature: {n d : Nat}
  body: OrderEmbedding.ofStrictMono _ ((mem_nonDegenerate_iff_strictMono _).1 s.2)
  invFun s := ⟨objEquiv.symm (.mk s.toOrderHom), by
    simpa [mem_nonDegenerate_iff_strictMono] using! s.strictMono⟩
  left_inv _ := by aesop

中文:
定义 nonDegenerateEquiv
  签名: {n d : 自然数}
  定义体: OrderEmbedding.ofStrictMono _ ((mem_nonDegenerate_iff_strictMono _).1 s.2)
  invFun s := ⟨objEquiv.symm (.mk s.toOrderHom), by
    simpa [mem_nonDegenerate_iff_strictMono] using! s.strictMono⟩
  left_inv _ := by aesop

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, mem_nonDegenerate_iff_strictMono, ofStrictMono
-/
def nonDegenerateEquiv {n d : Nat} :
    (Δ[n] : SSet.{u}).nonDegenerate d ≃ (Fin (d + 1) ↪o Fin (n + 1)) where
  toFun s := OrderEmbedding.ofStrictMono _ ((mem_nonDegenerate_iff_strictMono _).1 s.2)
  invFun s := ⟨objEquiv.symm (.mk s.toOrderHom), by
    simpa [mem_nonDegenerate_iff_strictMono] using! s.strictMono⟩
  left_inv _ := by aesop

instance (n : Nat) : (Δ[n] : SSet.{u}).HasDimensionLE n where
  degenerate_eq_top i hi := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    have : Mono (objEquiv x) := by rwa [← mem_nonDegenerate_iff_mono]
    have := SimplexCategory.len_le_of_mono (objEquiv x)
    dsimp at this
    lia

/--
Definition of `finSuccAboveOrderIsoFinset` / `finSuccAboveOrderIsoFinset` 的定义

English:
definition finSuccAboveOrderIsoFinset
  signature: {n : Nat} (i : Fin (n + 2))
  body: (finSuccAboveEquiv (p := i)).trans
    { toFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩ }
  map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff

中文:
定义 finSuccAboveOrderIsoFinset
  签名: {n : 自然数} (i : 有限集 (n + 2))
  定义体: (finSuccAboveEquiv (p := i)).trans
    { toFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩ }
  map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff

Depends on / 依赖: finSuccAboveEquiv
-/
def finSuccAboveOrderIsoFinset {n : Nat} (i : Fin (n + 2)) :
    Fin (n + 1) ≃o ({i}ᶜ : Finset _) where
  toEquiv := (finSuccAboveEquiv (p := i)).trans
    { toFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩
      invFun := fun ⟨x, hx⟩ => ⟨x, by simpa using hx⟩ }
  map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff

/--
lemma `face_singleton_compl` / 引理 `face_singleton_compl`

English:
lemma face_singleton_compl
  given: {n : Nat} (i : Fin (n + 2))
  proof: face_eq_ofSimplex _ _ (finSuccAboveOrderIsoFinset i)

中文:
引理 face_singleton_compl
  条件: {n : 自然数} (i : 有限集 (n + 2))
  证明: face_eq_ofSimplex _ _ (finSuccAboveOrderIsoFinset i)

Depends on / 依赖: face_eq_ofSimplex, finSuccAboveOrderIsoFinset
-/
lemma face_singleton_compl {n : Nat} (i : Fin (n + 2)) :
    face.{u} {i}ᶜ =
      Subcomplex.ofSimplex (objEquiv.symm (SimplexCategory.δ i)) :=
  face_eq_ofSimplex _ _ (finSuccAboveOrderIsoFinset i)

/--
Definition of `faceSingletonComplIso` / `faceSingletonComplIso` 的定义

English:
definition faceSingletonComplIso
  signature: {n : Nat} (i : Fin (n + 2))
  body: isoOfRepresentableBy (faceRepresentableBy _ _ (finSuccAboveOrderIsoFinset i))

@[reassoc (attr := simp)]

中文:
定义 faceSingletonComplIso
  签名: {n : 自然数} (i : 有限集 (n + 2))
  定义体: isoOfRepresentableBy (faceRepresentableBy _ _ (finSuccAboveOrderIsoFinset i))

@[reassoc (attr := simp)]

Depends on / 依赖: faceRepresentableBy, finSuccAboveOrderIsoFinset, isoOfRepresentableBy
-/
def faceSingletonComplIso {n : Nat} (i : Fin (n + 2)) :
    Δ[n] ≅ (face {i}ᶜ : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (finSuccAboveOrderIsoFinset i))

@[reassoc (attr := simp)]
/--
lemma `faceSingletonComplIso_hom_ι` / 引理 `faceSingletonComplIso_hom_ι`

English:
lemma faceSingletonComplIso_hom_ι
  given: {n : Nat} (i : Fin (n + 2))
  proof: rfl

中文:
引理 faceSingletonComplIso_hom_ι
  条件: {n : 自然数} (i : 有限集 (n + 2))
  证明: rfl
-/
lemma faceSingletonComplIso_hom_ι {n : Nat} (i : Fin (n + 2)) :
    (faceSingletonComplIso.{u} i).hom ≫ (face {i}ᶜ).ι =
      stdSimplex.δ i := rfl

/--
Definition of `finOrderIsoPairCompl` / `finOrderIsoPairCompl` 的定义

English:
definition finOrderIsoPairCompl
  signature: {n : Nat} (i j : Fin (n + 2)) (h : i < j)
  body: by
    refine Equiv.ofBijective
      (fun k => ⟨j.succAbove ((i.castPred (Fin.ne_last_of_lt h)).succAbove k), ?_⟩)
        ⟨fun _ _ hk => ?_, fun ⟨l, hl⟩ => ?_⟩
    · grind [compl_insert, mem_compl, Fin.succAbove, Fin.castPred]
    · exact ((Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h)))

中文:
定义 finOrderIsoPairCompl
  签名: {n : 自然数} (i j : 有限集 (n + 2)) (h : i < j)
  定义体: by
    refine Equiv.ofBijective
      (fun k => ⟨j.succAbove ((i.castPred (Fin.ne_last_of_lt h)).succAbove k), ?_⟩)
        ⟨fun _ _ hk => ?_, fun ⟨l, hl⟩ => ?_⟩
    · grind [compl_insert, mem_compl, Fin.succAbove, Fin.castPred]
    · exact ((Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h)))

Depends on / 依赖: Equiv.ofBijective, Fin.castPred, Fin.ne_last_of_lt, Fin.range_succAbove, Fin.succAbove, Fin.succAboveOrderEmb, Set.range, Subtype, Subtype.ext_iff, castPre, castPred, compl_insert, ext_iff, i.castPre, i.castPred, injective, j.succAbove, mem_compl, ne_last_of_lt, ofBijective
-/
noncomputable def finOrderIsoPairCompl {n : Nat} (i j : Fin (n + 2)) (h : i < j) :
    Fin n ≃o ({i, j}ᶜ : Finset _) where
  toEquiv := by
    refine Equiv.ofBijective
      (fun k => ⟨j.succAbove ((i.castPred (Fin.ne_last_of_lt h)).succAbove k), ?_⟩)
        ⟨fun _ _ hk => ?_, fun ⟨l, hl⟩ => ?_⟩
    · grind [compl_insert, mem_compl, Fin.succAbove, Fin.castPred]
    · exact ((Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h))).trans
        (Fin.succAboveOrderEmb j)).injective (by rwa [Subtype.ext_iff] at hk)
    · obtain ⟨m, rfl⟩ : l in Set.range j.succAbove := by
        grind [Fin.range_succAbove, mem_compl, Fin.succAbove]
      obtain ⟨k, hk⟩ : m in Set.range (i.castPred (Fin.ne_last_of_lt h)).succAbove := by
        grind [Fin.range_succAbove, compl_insert, Fin.succAbove, Fin.castPred]
      exact ⟨k, by simp [hk]⟩
  map_rel_iff' :=
    ((Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h))).trans
      (Fin.succAboveOrderEmb j)).map_rel_iff

/--
lemma `finOrderIsoPairCompl_apply_val` / 引理 `finOrderIsoPairCompl_apply_val`

English:
lemma finOrderIsoPairCompl_apply_val
  given: {n : Nat} (i j : Fin (n + 2)) (h : i < j) (k : Fin n)
  proof: rfl

中文:
引理 finOrderIsoPairCompl_apply_val
  条件: {n : 自然数} (i j : 有限集 (n + 2)) (h : i < j) (k : 有限集 n)
  证明: rfl
-/
lemma finOrderIsoPairCompl_apply_val {n : Nat} (i j : Fin (n + 2)) (h : i < j) (k : Fin n) :
    (finOrderIsoPairCompl i j h k).val =
      j.succAbove ((i.castPred (Fin.ne_last_of_lt h)).succAbove k) := rfl

/--
Definition of `facePairComplIso` / `facePairComplIso` 的定义

English:
definition facePairComplIso
  signature: {n : Nat} (i j : Fin (n + 3)) (h : i < j)
  body: isoOfRepresentableBy (faceRepresentableBy _ _ (finOrderIsoPairCompl i j h))

@[reassoc]

中文:
定义 facePairComplIso
  签名: {n : 自然数} (i j : 有限集 (n + 3)) (h : i < j)
  定义体: isoOfRepresentableBy (faceRepresentableBy _ _ (finOrderIsoPairCompl i j h))

@[reassoc]

Depends on / 依赖: faceRepresentableBy, finOrderIsoPairCompl, isoOfRepresentableBy
-/
noncomputable def facePairComplIso {n : Nat} (i j : Fin (n + 3)) (h : i < j) :
    Δ[n] ≅ (face {i, j}ᶜ : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (finOrderIsoPairCompl i j h))

@[reassoc]
/--
lemma `facePairComplIso_hom_ι` / 引理 `facePairComplIso_hom_ι`

English:
lemma facePairComplIso_hom_ι
  given: {n : Nat} (i j : Fin (n + 3)) (h : i < j)
  proof: rfl

@[reassoc]

中文:
引理 facePairComplIso_hom_ι
  条件: {n : 自然数} (i j : 有限集 (n + 3)) (h : i < j)
  证明: rfl

@[reassoc]
-/
lemma facePairComplIso_hom_ι {n : Nat} (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ stdSimplex.δ j :=
  rfl

@[reassoc]
/--
lemma `facePairComplIso_hom_ι'` / 引理 `facePairComplIso_hom_ι'`

English:
lemma facePairComplIso_hom_ι'
  given: {n : Nat} (i j : Fin (n + 3)) (h : i < j)
  proof: by
  rw [facePairComplIso_hom_ι]
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  dsimp
  rw [Fin.pred_succ]; rw [stdSimplex.δ_comp_δ (by grind)]

@[reassoc]

中文:
引理 facePairComplIso_hom_ι'
  条件: {n : 自然数} (i j : 有限集 (n + 3)) (h : i < j)
  证明: by
  rw [facePairComplIso_hom_ι]
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  dsimp
  rw [Fin.pred_succ]; rw [stdSimplex.δ_comp_δ (by grind)]

@[reassoc]

Depends on / 依赖: Fin.ne_last_of_lt, Fin.ne_zero_of_lt, Fin.pred_succ, eq_castSucc_of_ne_last, eq_succ_of_ne_zero, i.eq_castSucc_of_ne_last, j.eq_succ_of_ne_zero, ne_last_of_lt, ne_zero_of_lt, pred_succ, stdSimplex
-/
lemma facePairComplIso_hom_ι' {n : Nat} (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ stdSimplex.δ i := by
  rw [facePairComplIso_hom_ι]
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  dsimp
  rw [Fin.pred_succ]; rw [stdSimplex.δ_comp_δ (by grind)]

@[reassoc]
/--
lemma `homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred` / 引理 `homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred`

English:
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred
  statement: {n : Nat}
  proof: by
  simp [← cancel_mono (faceSingletonComplIso i).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι']

@[reassoc]

中文:
引理 homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred
  结论: {n : 自然数}
  证明: by
  simp [← cancel_mono (faceSingletonComplIso i).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι']

@[reassoc]

Depends on / 依赖: Subcomplex, cancel_epi, cancel_mono, facePairComplIso, faceSingletonComplIso
-/
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred {n : Nat}
    (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (by simp [face_le_face_iff]) ≫
      (faceSingletonComplIso.{u} i).inv =
    (facePairComplIso i j h).inv ≫ stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) := by
  simp [← cancel_mono (faceSingletonComplIso i).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι']

@[reassoc]
/--
lemma `homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred` / 引理 `homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred`

English:
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred
  proof: by
  simp [← cancel_mono (faceSingletonComplIso j).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι]

中文:
引理 homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred
  证明: by
  simp [← cancel_mono (faceSingletonComplIso j).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι]

Depends on / 依赖: Subcomplex, cancel_epi, cancel_mono, facePairComplIso, faceSingletonComplIso
-/
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred
    {n : Nat} (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (by simp [face_le_face_iff]) ≫
      (faceSingletonComplIso.{u} j).inv =
    (facePairComplIso i j h).inv ≫ stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) := by
  simp [← cancel_mono (faceSingletonComplIso j).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom,
    facePairComplIso_hom_ι]

/--
Definition of `faceSingletonIso` / `faceSingletonIso` 的定义

English:
definition faceSingletonIso
  signature: {n : Nat} (i : Fin (n + 1))
  body: stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoSingleton i))

@[reassoc]

中文:
定义 faceSingletonIso
  签名: {n : 自然数} (i : 有限集 (n + 1))
  定义体: stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoSingleton i))

@[reassoc]

Depends on / 依赖: Fin.orderIsoSingleton, faceRepresentableBy, isoOfRepresentableBy, orderIsoSingleton, stdSimplex, stdSimplex.faceRepresentableBy, stdSimplex.isoOfRepresentableBy
-/
noncomputable def faceSingletonIso {n : Nat} (i : Fin (n + 1)) :
    Δ[0] ≅ (face {i} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoSingleton i))

@[reassoc]
/--
lemma `faceSingletonIso_zero_hom_comp_ι_eq_δ` / 引理 `faceSingletonIso_zero_hom_comp_ι_eq_δ`

English:
lemma faceSingletonIso_zero_hom_comp_ι_eq_δ
  proof: by
  decide

@[reassoc]

中文:
引理 faceSingletonIso_zero_hom_comp_ι_eq_δ
  证明: by
  decide

@[reassoc]
-/
lemma faceSingletonIso_zero_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (0 : Fin 2)).hom ≫ (face {0}).ι = stdSimplex.δ 1 := by
  decide

@[reassoc]
/--
lemma `faceSingletonIso_one_hom_comp_ι_eq_δ` / 引理 `faceSingletonIso_one_hom_comp_ι_eq_δ`

English:
lemma faceSingletonIso_one_hom_comp_ι_eq_δ
  proof: by
  decide

中文:
引理 faceSingletonIso_one_hom_comp_ι_eq_δ
  证明: by
  decide
-/
lemma faceSingletonIso_one_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (1 : Fin 2)).hom ≫ (face {1}).ι = stdSimplex.δ 0 := by
  decide

/--
Definition of `facePairIso` / `facePairIso` 的定义

English:
definition facePairIso
  signature: {n : Nat} (i j : Fin (n + 1)) (hij : i < j)
  body: stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoPair i j hij))

中文:
定义 facePairIso
  签名: {n : 自然数} (i j : 有限集 (n + 1)) (hij : i < j)
  定义体: stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoPair i j hij))

Depends on / 依赖: Fin.orderIsoPair, faceRepresentableBy, isoOfRepresentableBy, orderIsoPair, stdSimplex, stdSimplex.faceRepresentableBy, stdSimplex.isoOfRepresentableBy
-/
noncomputable def facePairIso {n : Nat} (i j : Fin (n + 1)) (hij : i < j) :
    Δ[1] ≅ (face {i, j} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoPair i j hij))

set_option backward.defeqAttrib.useBackward true in
variable (n) in
/--
lemma `bijective_image_objEquiv_toOrderHom_univ` / 引理 `bijective_image_objEquiv_toOrderHom_univ`

English:
lemma bijective_image_objEquiv_toOrderHom_univ
  given: (m : Nat)
  proof: by
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h₃
    obtain ⟨f₁, rfl⟩ := objEquiv.symm.surjective x₁
    obtain ⟨f₂, rfl⟩ := objEquiv.symm.surjective x₂
    simp only [mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply,
      SimplexCategory.mono_iff_injective, SimplexCategory.len_mk] at h₁ h₂
    s

中文:
引理 bijective_image_objEquiv_toOrderHom_univ
  条件: (m : 自然数)
  证明: by
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h₃
    obtain ⟨f₁, rfl⟩ := objEquiv.symm.surjective x₁
    obtain ⟨f₂, rfl⟩ := objEquiv.symm.surjective x₂
    simp only [mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply,
      SimplexCategory.mono_iff_injective, SimplexCategory.len_mk] at h₁ h₂
    s
-/
private lemma bijective_image_objEquiv_toOrderHom_univ (m : Nat) :
    Function.Bijective (fun (⟨x, hx⟩ : (Δ[n] : SSet.{u}).nonDegenerate m) =>
      (⟨Finset.image (objEquiv x).toOrderHom .univ, by
        dsimp
        rw [mem_nonDegenerate_iff_mono]; rw [SimplexCategory.mono_iff_injective] at hx
        rw [Finset.card_image_of_injective _ (by exact hx)]; rw [Finset.card_univ]; rw [Fintype.card_fin]⟩ : { S : Finset (Fin (n + 1)) | S.card = m + 1 })) := by
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h₃
    obtain ⟨f₁, rfl⟩ := objEquiv.symm.surjective x₁
    obtain ⟨f₂, rfl⟩ := objEquiv.symm.surjective x₂
    simp only [mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply,
      SimplexCategory.mono_iff_injective, SimplexCategory.len_mk] at h₁ h₂
    simp only [Set.mem_ofPred_eq, SimplexCategory.len_mk, Equiv.apply_symm_apply,
      Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h₃ ⊢
    apply SimplexCategory.Hom.ext
    rw [← OrderHom.range_eq_iff h₁ h₂]
    ext x
    simpa using congr_fun (congrArg Membership.mem h₃) x
  · intro ⟨S, hS⟩
    dsimp at hS
    let e := monoEquivOfFin S (k := m + 1) (by simpa using hS)
    refine ⟨⟨objMk ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom), ?_⟩, ?_⟩
    · rw [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective]
      intro a b h
      grind [e.injective, dsimp% h]
    · simp [e, ← Finset.image_image, Finset.image_univ_of_surjective e.surjective]

/--
Definition of `nonDegenerateEquiv'` / `nonDegenerateEquiv'` 的定义

English:
definition nonDegenerateEquiv'
  signature: {n d : Nat}
  body: Equiv.ofBijective _ (bijective_image_objEquiv_toOrderHom_univ n d)

中文:
定义 nonDegenerateEquiv'
  签名: {n d : 自然数}
  定义体: Equiv.ofBijective _ (bijective_image_objEquiv_toOrderHom_univ n d)
-/
@[no_expose] noncomputable def nonDegenerateEquiv' {n d : Nat} :
    (Δ[n] : SSet.{u}).nonDegenerate d ≃ { S : Finset (Fin (n + 1)) | S.card = d + 1 } :=
  Equiv.ofBijective _ (bijective_image_objEquiv_toOrderHom_univ n d)

/--
lemma `nonDegenerateEquiv'_iff` / 引理 `nonDegenerateEquiv'_iff`

English:
lemma nonDegenerateEquiv'_iff
  given: {n d : Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1))
  proof: by
  unfold nonDegenerateEquiv'
  simp

中文:
引理 nonDegenerateEquiv'_iff
  条件: {n d : 自然数} (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : 有限集 (n + 1))
  证明: by
  unfold nonDegenerateEquiv'
  simp

Depends on / 依赖: nonDegenerateEquiv
-/
lemma nonDegenerateEquiv'_iff {n d : Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) :
    j in (nonDegenerateEquiv' x).val ↔ exists (i : Fin (d + 1)), x.val i = j := by
  unfold nonDegenerateEquiv'
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `orderIsoOfNonDegenerate` / `orderIsoOfNonDegenerate` 的定义

English:
definition orderIsoOfNonDegenerate
  body: Equiv.ofBijective (fun i => ⟨x.val i, Finset.mem_image_of_mem _ (by simp)⟩) (by
    constructor
    · have := (mem_nonDegenerate_iff_mono x.val).1 x.property
      rw [SimplexCategory.mono_iff_injective] at this
      exact fun _ _ h => this (by simpa using h)
    · rintro ⟨j, hj⟩
      rw [nonDegen

中文:
定义 orderIsoOfNonDegenerate
  定义体: Equiv.ofBijective (fun i => ⟨x.val i, Finset.mem_image_of_mem _ (by simp)⟩) (by
    constructor
    · have := (mem_nonDegenerate_iff_mono x.val).1 x.property
      rw [SimplexCategory.mono_iff_injective] at this
      exact fun _ _ h => this (by simpa using h)
    · rintro ⟨j, hj⟩
      rw [nonDegen
-/
@[no_expose] noncomputable def orderIsoOfNonDegenerate
    {n d : Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate d) :
    Fin (d + 1) ≃o nonDegenerateEquiv' x where
  toEquiv := Equiv.ofBijective (fun i => ⟨x.val i, Finset.mem_image_of_mem _ (by simp)⟩) (by
    constructor
    · have := (mem_nonDegenerate_iff_mono x.val).1 x.property
      rw [SimplexCategory.mono_iff_injective] at this
      exact fun _ _ h => this (by simpa using h)
    · rintro ⟨j, hj⟩
      rw [nonDegenerateEquiv'_iff] at hj
      aesop)
  map_rel_iff' := by
    have := (mem_nonDegenerate_iff_mono x.val).1 x.property
    rw [SimplexCategory.mono_iff_injective] at this
    intro a b
    dsimp
    simp only [Subtype.mk_le_mk]
    constructor
    · rw [← not_lt, ← not_lt]
      intro h h'
      apply h
      obtain h'' | h'' := (monotone_apply x.val h'.le).lt_or_eq
      · assumption
      · simp only [this h'', lt_self_iff_false] at h'
    · intro h
      exact monotone_apply _ h

/--
lemma `face_nonDegenerateEquiv'` / 引理 `face_nonDegenerateEquiv'`

English:
lemma face_nonDegenerateEquiv'
  given: {n d : Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate d)
  proof: face_eq_ofSimplex.{u} _ _ (orderIsoOfNonDegenerate x)

中文:
引理 face_nonDegenerateEquiv'
  条件: {n d : 自然数} (x : (Δ[n] : SSet.{u}).nonDegenerate d)
  证明: face_eq_ofSimplex.{u} _ _ (orderIsoOfNonDegenerate x)

Depends on / 依赖: face_eq_ofSimplex, orderIsoOfNonDegenerate
-/
lemma face_nonDegenerateEquiv' {n d : Nat} (x : (Δ[n] : SSet.{u}).nonDegenerate d) :
    face (nonDegenerateEquiv' x) = Subcomplex.ofSimplex x.val :=
  face_eq_ofSimplex.{u} _ _ (orderIsoOfNonDegenerate x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `nonDegenerateEquiv'_symm_apply_mem` / 引理 `nonDegenerateEquiv'_symm_apply_mem`

English:
lemma nonDegenerateEquiv'_symm_apply_mem
  statement: {n d : Nat}
  proof: by
  obtain ⟨f, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  dsimp [nonDegenerateEquiv']
  simp only [Equiv.ofBijective_symm_apply_apply, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩

中文:
引理 nonDegenerateEquiv'_symm_apply_mem
  结论: {n d : 自然数}
  证明: by
  obtain ⟨f, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  dsimp [nonDegenerateEquiv']
  simp only [Equiv.ofBijective_symm_apply_apply, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩
-/
lemma nonDegenerateEquiv'_symm_apply_mem {n d : Nat}
    (S : { S : Finset (Fin (n + 1)) | S.card = d + 1 }) (i : Fin (d + 1)) :
      (nonDegenerateEquiv'.{u}.symm S).val i in S.val := by
  obtain ⟨f, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  dsimp [nonDegenerateEquiv']
  simp only [Equiv.ofBijective_symm_apply_apply, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩

/--
lemma `nonDegenerateEquiv'_symm_mem_iff_face_le` / 引理 `nonDegenerateEquiv'_symm_mem_iff_face_le`

English:
lemma nonDegenerateEquiv'_symm_mem_iff_face_le
  statement: {n d : Nat}
  proof: by
  obtain ⟨x, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  rw [face_nonDegenerateEquiv' x]; rw [Equiv.symm_apply_apply]; rw [Subcomplex.ofSimplex_le_iff]

中文:
引理 nonDegenerateEquiv'_symm_mem_iff_face_le
  结论: {n d : 自然数}
  证明: by
  obtain ⟨x, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  rw [face_nonDegenerateEquiv' x]; rw [Equiv.symm_apply_apply]; rw [Subcomplex.ofSimplex_le_iff]
-/
lemma nonDegenerateEquiv'_symm_mem_iff_face_le {n d : Nat}
    (S : { S : Finset (Fin (n + 1)) | S.card = d + 1 })
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (nonDegenerateEquiv'.symm S).val in A.obj _ ↔ face S <= A := by
  obtain ⟨x, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  rw [face_nonDegenerateEquiv' x]; rw [Equiv.symm_apply_apply]; rw [Subcomplex.ofSimplex_le_iff]

instance (n : SimplexCategory) (d : SimplexCategoryᵒᵖ) :
    Finite ((stdSimplex.{u}.obj n).obj d) := by
  rw [objEquiv.finite_iff]
  infer_instance

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).Finite := by
  induction n using SimplexCategory.rec with | _ n
  exact finite_of_hasDimensionLT _ (n + 1) inferInstance

instance {X : SSet.{u}} {n : Nat} (x : X _⦋n⦌) :
    SSet.Finite (Subcomplex.ofSimplex x) := by
  obtain ⟨f, rfl⟩ := yonedaEquiv.surjective x
  rw [← Subcomplex.range_eq_ofSimplex]
  infer_instance

/--
lemma `hasDimensionLT_face` / 引理 `hasDimensionLT_face`

English:
lemma hasDimensionLT_face
  statement: {n : Nat} (S : Finset (Fin (n + 1)))
  proof: by
  generalize hm : S.card = m
  obtain _ | m := m
  · obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
    rw [face_empty]
    infer_instance
  · rw [← hasDimensionLT_iff_of_iso
      (isoOfRepresentableBy (faceRepresentableBy S m (monoEquivOfFin S (by simpa))))]
    exact hasDimensionLT_of_le

中文:
引理 hasDimensionLT_face
  结论: {n : 自然数} (S : 有限集 (有限集 (n + 1)))
  证明: by
  generalize hm : S.card = m
  obtain _ | m := m
  · obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
    rw [face_empty]
    infer_instance
  · rw [← hasDimensionLT_iff_of_iso
      (isoOfRepresentableBy (faceRepresentableBy S m (monoEquivOfFin S (by simpa))))]
    exact hasDimensionLT_of_le

Depends on / 依赖: Finset, Finset.card_eq_zero, S.card, card_eq_zero, faceRepresentableBy, face_empty, generalize, hasDimensionLT_iff_of_iso, hasDimensionLT_of_le, infer_instance, isoOfRepresentableBy, monoEquivOfFin
-/
lemma hasDimensionLT_face {n : Nat} (S : Finset (Fin (n + 1)))
    (d : Nat) (hd : S.card <= d) :
    HasDimensionLT (face.{u} S) d := by
  generalize hm : S.card = m
  obtain _ | m := m
  · obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
    rw [face_empty]
    infer_instance
  · rw [← hasDimensionLT_iff_of_iso
      (isoOfRepresentableBy (faceRepresentableBy S m (monoEquivOfFin S (by simpa))))]
    exact hasDimensionLT_of_le _ (m + 1) _

/--
lemma `ofSimplex_objEquiv_symm_id` / 引理 `ofSimplex_objEquiv_symm_id`

English:
lemma ofSimplex_objEquiv_symm_id
  given: (n : Nat)
  proof: le_antisymm (by simp) (fun _ x _ => by
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    simp only [Subcomplex.mem_ofSimplex_obj_iff, op_unop]
    exact ⟨f, by simp [map_objEquiv_symm.{u}]⟩)

中文:
引理 ofSimplex_objEquiv_symm_id
  条件: (n : 自然数)
  证明: le_antisymm (by simp) (fun _ x _ => by
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    simp only [Subcomplex.mem_ofSimplex_obj_iff, op_unop]
    exact ⟨f, by simp [map_objEquiv_symm.{u}]⟩)

Depends on / 依赖: Subcomplex, Subcomplex.mem_ofSimplex_obj_iff, le_antisymm, map_objEquiv_symm, mem_ofSimplex_obj_iff, objEquiv, objEquiv.symm.surjective, op_unop, surjective
-/
lemma ofSimplex_objEquiv_symm_id (n : Nat) :
    Subcomplex.ofSimplex (objEquiv.{u}.symm (𝟙 ⦋n⦌)) = ⊤ :=
  le_antisymm (by simp) (fun _ x _ => by
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    simp only [Subcomplex.mem_ofSimplex_obj_iff, op_unop]
    exact ⟨f, by simp [map_objEquiv_symm.{u}]⟩)

/--
lemma `objEquiv_symm_id_mem_nonDegenerate` / 引理 `objEquiv_symm_id_mem_nonDegenerate`

English:
lemma objEquiv_symm_id_mem_nonDegenerate
  given: (n : Nat)
  proof: by
  rw [mem_nonDegenerate_iff_strictMono]
  exact fun _ _ h => h

中文:
引理 objEquiv_symm_id_mem_nonDegenerate
  条件: (n : 自然数)
  证明: by
  rw [mem_nonDegenerate_iff_strictMono]
  exact fun _ _ h => h

Depends on / 依赖: mem_nonDegenerate_iff_strictMono, nonDegenerate
-/
lemma objEquiv_symm_id_mem_nonDegenerate (n : Nat) :
    (objEquiv (m := (op ⦋n⦌))).symm (𝟙 _) in (Δ[n] : SSet.{u}).nonDegenerate n := by
  rw [mem_nonDegenerate_iff_strictMono]
  exact fun _ _ h => h

/--
lemma `nonDegenerate_top_dim` / 引理 `nonDegenerate_top_dim`

English:
lemma nonDegenerate_top_dim
  given: (n : Nat)
  proof: by
  ext x
  simp only [Set.mem_singleton_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    have : Mono f := by simpa using (mem_nonDegenerate_iff_mono _).mp h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using SimplexCategory.eq_id_of_mono f
  · rintro rfl
    

中文:
引理 nonDegenerate_top_dim
  条件: (n : 自然数)
  证明: by
  ext x
  simp only [Set.mem_singleton_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    have : Mono f := by simpa using (mem_nonDegenerate_iff_mono _).mp h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using SimplexCategory.eq_id_of_mono f
  · rintro rfl
    

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Set.mem_singleton_iff, SimplexCategory, SimplexCategory.eq_id_of_mono, apply_eq_iff_eq, eq_id_of_mono, mem_nonDegenerate_iff_mono, mem_singleton_iff, objEquiv, objEquiv.symm.surjective, objEquiv_symm_id_mem_nonDegenerate, surjective
-/
lemma nonDegenerate_top_dim (n : Nat) :
    (Δ[n] : SSet.{u}).nonDegenerate n = {(objEquiv (m := (op ⦋n⦌))).symm (𝟙 _)} := by
  ext x
  simp only [Set.mem_singleton_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    have : Mono f := by simpa using (mem_nonDegenerate_iff_mono _).mp h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using SimplexCategory.eq_id_of_mono f
  · rintro rfl
    apply objEquiv_symm_id_mem_nonDegenerate

/--
lemma `not_hasDimensionLT` / 引理 `not_hasDimensionLT`

English:
lemma not_hasDimensionLT
  given: (n : Nat) (_ : HasDimensionLT.{u} Δ[n] n := by infer_instance)
  proof: (lt_self_iff_false n).1 (Δ[n].dim_lt_of_nonDegenerate
    (nonDegenerateEquiv.2 (.refl _)) n)

中文:
引理 not_hasDimensionLT
  条件: (n : 自然数) (_ : 有DimensionLT.{u} Δ[n] n := by infer_instance)
  证明: (lt_self_iff_false n).1 (Δ[n].dim_lt_of_nonDegenerate
    (nonDegenerateEquiv.2 (.refl _)) n)

Depends on / 依赖: dim_lt_of_nonDegenerate, infer_instance, lt_self_iff_false, nonDegenerateEquiv
-/
lemma not_hasDimensionLT (n : Nat) (_ : HasDimensionLT.{u} Δ[n] n := by infer_instance) :
    False :=
  (lt_self_iff_false n).1 (Δ[n].dim_lt_of_nonDegenerate
    (nonDegenerateEquiv.2 (.refl _)) n)

/--
Definition of `opObjEquiv` / `opObjEquiv` 的定义

English:
definition opObjEquiv
  signature: {n : SimplexCategory} {d : SimplexCategoryᵒᵖ}
  body: SSet.opObjEquiv.trans (objEquiv.trans
    (SimplexCategory.revEquivalence.fullyFaithfulFunctor.homEquiv.trans objEquiv.symm))

中文:
定义 opObjEquiv
  签名: {n : 单纯形范畴} {d : SimplexCategoryᵒᵖ}
  定义体: SSet.opObjEquiv.trans (objEquiv.trans
    (SimplexCategory.revEquivalence.fullyFaithfulFunctor.homEquiv.trans objEquiv.symm))
-/
protected def opObjEquiv {n : SimplexCategory} {d : SimplexCategoryᵒᵖ} :
    (stdSimplex.{u}.obj n).op.obj d ≃ (stdSimplex.obj n).obj d :=
  SSet.opObjEquiv.trans (objEquiv.trans
    (SimplexCategory.revEquivalence.fullyFaithfulFunctor.homEquiv.trans objEquiv.symm))

/--
lemma `opObjEquiv_apply` / 引理 `opObjEquiv_apply`

English:
lemma opObjEquiv_apply
  given: {d n : Nat} (f : Δ[n].op _⦋d⦌) (i : Fin (d + 1))
  proof: rfl

中文:
引理 opObjEquiv_apply
  条件: {d n : 自然数} (f : Δ[n].op _⦋d⦌) (i : 有限集 (d + 1))
  证明: rfl
-/
protected lemma opObjEquiv_apply {d n : Nat} (f : Δ[n].op _⦋d⦌) (i : Fin (d + 1)) :
    stdSimplex.opObjEquiv.{u} f i = (opObjEquiv f i.rev).rev := rfl

/--
lemma `opObjEquiv_opObjEquiv_symm_apply` / 引理 `opObjEquiv_opObjEquiv_symm_apply`

English:
lemma opObjEquiv_opObjEquiv_symm_apply
  given: {d n : Nat} (f : (Δ[n] _⦋d⦌)) (i : Fin (d + 1))
  proof: rfl

中文:
引理 opObjEquiv_opObjEquiv_symm_apply
  条件: {d n : 自然数} (f : (Δ[n] _⦋d⦌)) (i : 有限集 (d + 1))
  证明: rfl
-/
lemma opObjEquiv_opObjEquiv_symm_apply {d n : Nat} (f : (Δ[n] _⦋d⦌)) (i : Fin (d + 1)) :
    SSet.opObjEquiv (stdSimplex.opObjEquiv.{u}.symm f) i = (f i.rev).rev :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_rev_map_op_apply` / 引理 `map_rev_map_op_apply`

English:
lemma map_rev_map_op_apply
  given: {n d d' : Nat} (f : ⦋d⦌ ⟶ ⦋d'⦌) (g : Δ[n] _⦋d'⦌) (i : Fin (d + 1))
  proof: rfl

中文:
引理 map_rev_map_op_apply
  条件: {n d d' : 自然数} (f : ⦋d⦌ ⟶ ⦋d'⦌) (g : Δ[n] _⦋d'⦌) (i : 有限集 (d + 1))
  证明: rfl
-/
lemma map_rev_map_op_apply {n d d' : Nat} (f : ⦋d⦌ ⟶ ⦋d'⦌) (g : Δ[n] _⦋d'⦌) (i : Fin (d + 1)) :
    dsimp% (show Δ[n] _⦋d⦌ from (Δ[n] : SSet.{u}).map (rev.map f).op g : Δ[n] _⦋d⦌) i =
      g (f i.rev).rev := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The opposite of `Δ[n]` is isomorphic to `Δ[n]`. -/
@[simps! hom_app_hom_apply inv_app_hom_apply]
/--
Definition of `opIso` / `opIso` 的定义

English:
definition opIso
  signature: (n : SimplexCategory)
  body: NatIso.ofComponents (fun d => stdSimplex.opObjEquiv.toIso) (fun {d d'} f => by
    ext g
    refine stdSimplex.ext _ _ (fun i => ?_)
    dsimp
    rw [stdSimplex.opObjEquiv_apply]; rw [op_map]
    erw [Equiv.apply_symm_apply]
    dsimp
    rw [map_rev_map_op_apply]
    aesop)

中文:
定义 opIso
  签名: (n : 单纯形范畴)
  定义体: NatIso.ofComponents (fun d => stdSimplex.opObjEquiv.toIso) (fun {d d'} f => by
    ext g
    refine stdSimplex.ext _ _ (fun i => ?_)
    dsimp
    rw [stdSimplex.opObjEquiv_apply]; rw [op_map]
    erw [Equiv.apply_symm_apply]
    dsimp
    rw [map_rev_map_op_apply]
    aesop)

Depends on / 依赖: Equiv.apply_symm_apply, NatIso, NatIso.ofComponents, apply_symm_apply, map_rev_map_op_apply, ofComponents, opObjEquiv, opObjEquiv_apply, op_map, stdSimplex, stdSimplex.ext, stdSimplex.opObjEquiv.toIso, stdSimplex.opObjEquiv_apply
-/
def opIso (n : SimplexCategory) :
    (stdSimplex.{u}.obj n).op ≅ stdSimplex.obj n :=
  NatIso.ofComponents (fun d => stdSimplex.opObjEquiv.toIso) (fun {d d'} f => by
    ext g
    refine stdSimplex.ext _ _ (fun i => ?_)
    dsimp
    rw [stdSimplex.opObjEquiv_apply]; rw [op_map]
    erw [Equiv.apply_symm_apply]
    dsimp
    rw [map_rev_map_op_apply]
    aesop)

end stdSimplex

section Examples

open Simplicial

/--
Definition of `S1` / `S1` 的定义

English:
definition S1
  signature: : SSet
  body: Limits.colimit
    Limits.parallelPair (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]) (stdSimplex.δ 1)

中文:
定义 S1
  签名: : SSet
  定义体: Limits.colimit
    Limits.parallelPair (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]) (stdSimplex.δ 1)

Depends on / 依赖: Limits, Limits.colimit, Limits.parallelPair, colimit, parallelPair, stdSimplex
-/
noncomputable def S1 : SSet :=
Limits.colimit
    Limits.parallelPair (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]) (stdSimplex.δ 1)

end Examples

namespace Augmented

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor which sends `⦋n⦌` to the simplicial set `Δ[n]` equipped by
the obvious augmentation towards the terminal object of the category of sets. -/
@[simps]
/--
Definition of `stdSimplex` / `stdSimplex` 的定义

English:
definition stdSimplex
  signature: : SimplexCategory ⥤ SSet.Augmented.{u} where
  body: { left := SSet.stdSimplex.obj Δ
      right := terminal _
      hom := { app := fun _ => terminal.from _ } }
  map θ :=
    { left := SSet.stdSimplex.map θ
      right := terminal.from _ }

中文:
定义 stdSimplex
  签名: : 单纯形范畴 ⥤ SSet.Augmented.{u} where
  定义体: { left := SSet.stdSimplex.obj Δ
      right := terminal _
      hom := { app := fun _ => terminal.from _ } }
  map θ :=
    { left := SSet.stdSimplex.map θ
      right := terminal.from _ }

Depends on / 依赖: SSet.stdSimplex.map, SSet.stdSimplex.obj, stdSimplex, terminal, terminal.from
-/
noncomputable def stdSimplex : SimplexCategory ⥤ SSet.Augmented.{u} where
  obj Δ :=
    { left := SSet.stdSimplex.obj Δ
      right := terminal _
      hom := { app := fun _ => terminal.from _ } }
  map θ :=
    { left := SSet.stdSimplex.map θ
      right := terminal.from _ }

end Augmented

namespace Subcomplex

variable {X : SSet.{u}} {n : Nat} (x : X _⦋n⦌)

/--
Definition of `toOfSimplex` / `toOfSimplex` 的定义

English:
definition toOfSimplex
  signature: : Δ[n] ⟶ ofSimplex x
  body: Subcomplex.lift (yonedaEquiv.symm x) (by simp [range_eq_ofSimplex])

@[reassoc (attr := simp)]

中文:
定义 toOfSimplex
  签名: : Δ[n] ⟶ ofSimplex x
  定义体: Subcomplex.lift (yonedaEquiv.symm x) (by simp [range_eq_ofSimplex])

@[reassoc (attr := simp)]

Depends on / 依赖: Subcomplex, Subcomplex.lift, range_eq_ofSimplex, yonedaEquiv, yonedaEquiv.symm
-/
def toOfSimplex : Δ[n] ⟶ ofSimplex x :=
  Subcomplex.lift (yonedaEquiv.symm x) (by simp [range_eq_ofSimplex])

@[reassoc (attr := simp)]
/--
lemma `toOfSimplex_ι` / 引理 `toOfSimplex_ι`

English:
lemma toOfSimplex_ι
  proof: rfl

@[simp]

中文:
引理 toOfSimplex_ι
  证明: rfl

@[simp]
-/
lemma toOfSimplex_ι :
    toOfSimplex x ≫ (ofSimplex x).ι = yonedaEquiv.symm x := rfl

@[simp]
/--
lemma `yonedaEquiv_toOfSimplex` / 引理 `yonedaEquiv_toOfSimplex`

English:
lemma yonedaEquiv_toOfSimplex
  proof: yonedaEquiv.symm.injective (by cat_disch)

中文:
引理 yonedaEquiv_toOfSimplex
  证明: yonedaEquiv.symm.injective (by cat_disch)

Depends on / 依赖: cat_disch, injective, yonedaEquiv, yonedaEquiv.symm.injective
-/
lemma yonedaEquiv_toOfSimplex :
    yonedaEquiv (toOfSimplex x) = ⟨x, mem_ofSimplex_obj x⟩ :=
  yonedaEquiv.symm.injective (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (toOfSimplex x)
  body: by
  rw [← range_eq_top_iff]
  ext m ⟨_, u, rfl⟩
  simp only [range_eq_ofSimplex, yonedaEquiv_toOfSimplex, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  refine ⟨u, ?_⟩
  dsimp
  ext
  rw [← yonedaEquiv.right_inv x]
  aesop

中文:
实例 :
  签名: 满态射 (toOfSimplex x)
  定义体: by
  rw [← range_eq_top_iff]
  ext m ⟨_, u, rfl⟩
  simp only [range_eq_ofSimplex, yonedaEquiv_toOfSimplex, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  refine ⟨u, ?_⟩
  dsimp
  ext
  rw [← yonedaEquiv.right_inv x]
  aesop

Depends on / 依赖: Set.mem_univ, Set.top_eq_univ, Subfunctor, Subfunctor.top_obj, iff_true, mem_univ, range_eq_ofSimplex, range_eq_top_iff, right_inv, top_eq_univ, top_obj, yonedaEquiv, yonedaEquiv.right_inv, yonedaEquiv_toOfSimplex
-/
instance : Epi (toOfSimplex x) := by
  rw [← range_eq_top_iff]
  ext m ⟨_, u, rfl⟩
  simp only [range_eq_ofSimplex, yonedaEquiv_toOfSimplex, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  refine ⟨u, ?_⟩
  dsimp
  ext
  rw [← yonedaEquiv.right_inv x]
  aesop

/--
lemma `isIso_toOfSimplex_iff` / 引理 `isIso_toOfSimplex_iff`

English:
lemma isIso_toOfSimplex_iff
  proof: by
  constructor
  · intro
    rw [← toOfSimplex_ι]
    infer_instance
  · intro h
    have := mono_of_mono_fac (toOfSimplex_ι x)
    apply isIso_of_mono_of_epi

中文:
引理 isIso_toOfSimplex_iff
  证明: by
  constructor
  · intro
    rw [← toOfSimplex_ι]
    infer_instance
  · intro h
    have := mono_of_mono_fac (toOfSimplex_ι x)
    apply isIso_of_mono_of_epi

Depends on / 依赖: infer_instance, isIso_of_mono_of_epi, mono_of_mono_fac
-/
lemma isIso_toOfSimplex_iff :
    IsIso (toOfSimplex x) ↔ Mono (yonedaEquiv.symm x) := by
  constructor
  · intro
    rw [← toOfSimplex_ι]
    infer_instance
  · intro h
    have := mono_of_mono_fac (toOfSimplex_ι x)
    apply isIso_of_mono_of_epi

end Subcomplex

end SSet
