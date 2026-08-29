/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Elementwise

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism of schemes is just a morphism of the underlying locally ringed spaces.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


universe u

noncomputable section

open TopologicalSpace CategoryTheory TopCat Opposite

namespace AlgebraicGeometry

/--
Definition of `Scheme` / `Scheme` 的定义

English:
structure Scheme
  parameters: extends LocallyRingedSpace
  extends: LocallyRingedSpace
  axioms and operations (1):
    - local_affine : forall x : toLocallyRingedSpace, exists (U : OpenNhds x) (R : CommRingCat), Nonempty (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))

中文:
结构 概形
  参数: extends LocallyRinged空间
  继承: LocallyRinged空间
  公理与运算 (1 个):
    - local_affine : 对任意 x : toLocallyRingedSpace, 存在 (U : OpenNhds x) (R : 交换环范畴), 非空 (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))
-/
structure Scheme extends LocallyRingedSpace where
  local_affine :
    forall x : toLocallyRingedSpace,
      exists (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))

namespace Scheme

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Scheme Type*
  body: X.carrier

中文:
实例 :
  签名: CoeSort 概形 类型
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort Scheme Type* where
  coe X := X.carrier

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for coercing schemes to types. -/
@[app_delab TopCat.carrier]
meta def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
guard (← getExpr).isAppOfArity ``TopCat.carrier 1
  withNaryArg 0 do
guard (← getExpr).isAppOfArity ``PresheafedSpace.carrier 3
  withNaryArg 2 do
guard (← getExpr).isAppOfArity ``SheafedSpace.toPresheafedSpace 3
  withNaryArg 2 do
guard (← getExpr).isAppOfArity ``LocallyRingedSpace.toSheafedSpace 1
  withNaryArg 0 do
guard (← getExpr).isAppOfArity ``Scheme.toLocallyRingedSpace 1
  withNaryArg 0 do
  `(↥$(← delab))

/--
Definition of `Opens` / `Opens` 的定义

English:
abbreviation Opens
  signature: (X : Scheme)
  body: TopologicalSpace.Opens X

中文:
缩写 Opens
  签名: (X : 概形)
  定义体: TopologicalSpace.Opens X

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens
-/
abbrev Opens (X : Scheme) : Type* := TopologicalSpace.Opens X

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Scheme)
  extends: toLRSHom' : X.toLocallyRingedSpace.Hom Y.toLocallyRingedSpace
  (no additional axioms)

中文:
结构 态射
  参数: (X Y : 概形)
  继承: toLRSHom' : X.toLocallyRingedSpace.态射 Y.toLocallyRingedSpace
  (无附加公理)
-/
structure Hom (X Y : Scheme)
  extends toLRSHom' : X.toLocallyRingedSpace.Hom Y.toLocallyRingedSpace where

/--
Definition of `Hom.toLRSHom` / `Hom.toLRSHom` 的定义

English:
abbreviation Hom.toLRSHom
  signature: {X Y : Scheme.{u}} (f : X.Hom Y)
  body: f.toLRSHom'

中文:
缩写 态射.toLRSHom
  签名: {X Y : 概形.{u}} (f : X.态射 Y)
  定义体: f.toLRSHom'

Depends on / 依赖: f.toLRSHom, toLRSHom
-/
abbrev Hom.toLRSHom {X Y : Scheme.{u}} (f : X.Hom Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom'

/--
Definition of `Hom.Simps.toLRSHom` / `Hom.Simps.toLRSHom` 的定义

English:
definition Hom.Simps.toLRSHom
  signature: {X Y : Scheme.{u}} (f : X.Hom Y)
  body: f.toLRSHom

initialize_simps_projections Hom (toLRSHom' -> toLRSHom)

中文:
定义 态射.Simps.toLRSHom
  签名: {X Y : 概形.{u}} (f : X.态射 Y)
  定义体: f.toLRSHom

initialize_simps_projections Hom (toLRSHom' -> toLRSHom)

Depends on / 依赖: f.toLRSHom, toLRSHom
-/
def Hom.Simps.toLRSHom {X Y : Scheme.{u}} (f : X.Hom Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom

initialize_simps_projections Hom (toLRSHom' -> toLRSHom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category Scheme
  body: Hom
  id X := Hom.mk (𝟙 X.toLocallyRingedSpace)
  comp f g := Hom.mk (f.toLRSHom ≫ g.toLRSHom)

中文:
实例 :
  签名: 范畴 概形
  定义体: Hom
  id X := Hom.mk (𝟙 X.toLocallyRingedSpace)
  comp f g := Hom.mk (f.toLRSHom ≫ g.toLRSHom)
-/
instance : Category Scheme where
  Hom := Hom
  id X := Hom.mk (𝟙 X.toLocallyRingedSpace)
  comp f g := Hom.mk (f.toLRSHom ≫ g.toLRSHom)

/-- `f ⁻¹ᵁ U` is notation for `(Opens.map f.base).obj U`, the preimage of an open set `U` under `f`.
The preferred name in lemmas is `preimage` and it should be treated as an infix. -/
scoped[AlgebraicGeometry] notation3:90 f:91 " ⁻¹ᵁ " U:90 =>
  @Functor.obj (Scheme.Opens _) _ (Scheme.Opens _) _
    (Opens.map (f : Scheme.Hom _ _).base) U

/-- `Γ(X, U)` is notation for `X.presheaf.obj (op U)`. -/
scoped[AlgebraicGeometry] notation3 "Γ(" X ", " U ")" =>
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace X)))).obj
    (op (α := Scheme.Opens _) U)

instance {X Y : Scheme.{u}} : CoeFun (X ⟶ Y) (fun _ => X -> Y) where
  coe f := f.base

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for coercing morphisms between schemes to functions. -/
@[app_delab DFunLike.coe]
meta def delabCoeFunNotation : Delab := whenPPOption getPPNotation do
guard (← getExpr).isAppOfArity ``DFunLike.coe 5
  withNaryArg 4 do
guard (← getExpr).isAppOfArity ``CategoryTheory.ConcreteCategory.hom 9
  withNaryArg 8 do
guard (← getExpr).isAppOfArity ``PresheafedSpace.Hom.base 5
  withNaryArg 4 do
guard (← getExpr).isAppOfArity ``LocallyRingedSpace.Hom.toHom 3
  withNaryArg 2 do
guard (← getExpr).isAppOfArity ``Scheme.Hom.toLRSHom' 3
  withNaryArg 2 do
  `(⇑$(← delab))

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for applying morphisms of schemes to set-theoretic points. -/
@[app_delab DFunLike.coe]
meta def delabCoeFunAppNotation : Delab := whenPPOption getPPNotation do
guard (← getExpr).isAppOfArity ``DFunLike.coe 6
  let func ← do
    withNaryArg 4 do
guard (← getExpr).isAppOfArity ``CategoryTheory.ConcreteCategory.hom 9
    withNaryArg 8 do
guard (← getExpr).isAppOfArity ``PresheafedSpace.Hom.base 5
    withNaryArg 4 do
guard (← getExpr).isAppOfArity ``LocallyRingedSpace.Hom.toHom 3
    withNaryArg 2 do
guard (← getExpr).isAppOfArity ``Scheme.Hom.toLRSHom' 3
    withNaryArg 2 do
    delab
  `($func $(← withNaryArg 5 do delab))

instance {X : Scheme.{u}} : Subsingleton Γ(X, ⊥) :=
  CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty

@[continuity, fun_prop]
/--
lemma `Hom.continuous` / 引理 `Hom.continuous`

English:
lemma Hom.continuous
  given: {X Y : Scheme} (f : X ⟶ Y)
  statement: Continuous f
  proof: f.base.hom.2

中文:
引理 态射.continuous
  条件: {X Y : 概形} (f : X ⟶ Y)
  结论: 连续 f
  证明: f.base.hom.2

Depends on / 依赖: f.base.hom
-/
lemma Hom.continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f := f.base.hom.2

/--
Definition of `sheaf` / `sheaf` 的定义

English:
abbreviation sheaf
  signature: (X : Scheme)
  body: X.toSheafedSpace.sheaf

中文:
缩写 sheaf
  签名: (X : 概形)
  定义体: X.toSheafedSpace.sheaf
-/
protected abbrev sheaf (X : Scheme) :=
  X.toSheafedSpace.sheaf

/--
We give schemes the specialization preorder by default.
-/
instance {X : Scheme.{u}} : Preorder X := specializationPreorder X

/--
lemma `le_iff_specializes` / 引理 `le_iff_specializes`

English:
lemma le_iff_specializes
  given: {X : Scheme.{u}} {a b : X}
  statement: a <= b ↔ b ⤳ a
  proof: by rfl

中文:
引理 le_iff_specializes
  条件: {X : 概形.{u}} {a b : X}
  结论: a <= b ↔ b ⤳ a
  证明: by rfl
-/
lemma le_iff_specializes {X : Scheme.{u}} {a b : X} : a <= b ↔ b ⤳ a := by rfl

open Order in
/--
lemma `height_of_isClosed` / 引理 `height_of_isClosed`

English:
lemma height_of_isClosed
  given: {X : Scheme} {x : X} (hx : IsClosed {x})
  statement: height x = 0
  proof: by
  simp only [height_eq_zero]
  intro b _
  obtain rfl | h := eq_or_ne b x
  · assumption
  · have := IsClosed.not_specializes hx rfl h
    contradiction

中文:
引理 height_of_isClosed
  条件: {X : 概形} {x : X} (hx : 是闭集 {x})
  结论: height x = 0
  证明: by
  simp only [height_eq_zero]
  intro b _
  obtain rfl | h := eq_or_ne b x
  · assumption
  · have := IsClosed.not_specializes hx rfl h
    contradiction

Depends on / 依赖: IsClosed, IsClosed.not_specializes, eq_or_ne, height_eq_zero, not_specializes
-/
lemma height_of_isClosed {X : Scheme} {x : X} (hx : IsClosed {x}) : height x = 0 := by
  simp only [height_eq_zero]
  intro b _
  obtain rfl | h := eq_or_ne b x
  · assumption
  · have := IsClosed.not_specializes hx rfl h
    contradiction

namespace Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}

/--
Definition of `app` / `app` 的定义

English:
abbreviation app
  signature: (U : Y.Opens)
  body: f.c.app (op U)

中文:
缩写 app
  签名: (U : Y.Opens)
  定义体: f.c.app (op U)

Depends on / 依赖: f.c.app
-/
abbrev app (U : Y.Opens) : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.c.app (op U)

/--
Definition of `appTop` / `appTop` 的定义

English:
abbreviation appTop
  signature: : Γ(Y, ⊤) ⟶ Γ(X, ⊤)
  body: f.app ⊤

@[reassoc]

中文:
缩写 appTop
  签名: : Γ(Y, ⊤) ⟶ Γ(X, ⊤)
  定义体: f.app ⊤

@[reassoc]

Depends on / 依赖: f.app
-/
abbrev appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤) :=
  f.app ⊤

@[reassoc]
/--
lemma `naturality` / 引理 `naturality`

English:
lemma naturality
  given: (i : op U' ⟶ op U)
  proof: f.c.naturality i

中文:
引理 naturality
  条件: (i : op U' ⟶ op U)
  证明: f.c.naturality i

Depends on / 依赖: f.c.naturality, naturality
-/
lemma naturality (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map i.unop).op :=
  f.c.naturality i

/--
Definition of `appLE` / `appLE` 的定义

English:
definition appLE
  signature: (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U)
  body: f.app U ≫ X.presheaf.map (homOfLE e).op

@[reassoc (attr := simp)]

中文:
定义 appLE
  签名: (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U)
  定义体: f.app U ≫ X.presheaf.map (homOfLE e).op

@[reassoc (attr := simp)]

Depends on / 依赖: X.presheaf.map, f.app, homOfLE, presheaf
-/
def appLE (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.app U ≫ X.presheaf.map (homOfLE e).op

@[reassoc (attr := simp)]
/--
lemma `appLE_map` / 引理 `appLE_map`

English:
lemma appLE_map
  given: (e : V <= f ⁻¹ᵁ U) (i : op V ⟶ op V')
  proof: by
  rw [Hom.appLE]; rw [Category.assoc]; rw [← Functor.map_comp]
  rfl

@[reassoc]

中文:
引理 appLE_map
  条件: (e : V <= f ⁻¹ᵁ U) (i : op V ⟶ op V')
  证明: by
  rw [Hom.appLE]; rw [Category.assoc]; rw [← Functor.map_comp]
  rfl

@[reassoc]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Hom.appLE, map_comp
-/
lemma appLE_map (e : V <= f ⁻¹ᵁ U) (i : op V ⟶ op V') :
    f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.trans e) := by
  rw [Hom.appLE]; rw [Category.assoc]; rw [← Functor.map_comp]
  rfl

@[reassoc]
/--
lemma `appLE_map'` / 引理 `appLE_map'`

English:
lemma appLE_map'
  given: (e : V <= f ⁻¹ᵁ U) (i : V = V')
  proof: appLE_map _ _ _

@[reassoc (attr := simp)]

中文:
引理 appLE_map'
  条件: (e : V <= f ⁻¹ᵁ U) (i : V = V')
  证明: appLE_map _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: appLE_map
-/
lemma appLE_map' (e : V <= f ⁻¹ᵁ U) (i : V = V') :
    f.appLE U V' (i ▸ e) ≫ X.presheaf.map (eqToHom i).op = f.appLE U V e :=
  appLE_map _ _ _

@[reassoc (attr := simp)]
/--
lemma `map_appLE` / 引理 `map_appLE`

English:
lemma map_appLE
  given: (e : V <= f ⁻¹ᵁ U) (i : op U' ⟶ op U)
  proof: by
  rw [Hom.appLE]; rw [f.naturality_assoc]; rw [← Functor.map_comp]
  rfl

@[reassoc]

中文:
引理 map_appLE
  条件: (e : V <= f ⁻¹ᵁ U) (i : op U' ⟶ op U)
  证明: by
  rw [Hom.appLE]; rw [f.naturality_assoc]; rw [← Functor.map_comp]
  rfl

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, Hom.appLE, f.naturality_assoc, map_comp, naturality_assoc
-/
lemma map_appLE (e : V <= f ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.appLE U V e =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le) := by
  rw [Hom.appLE]; rw [f.naturality_assoc]; rw [← Functor.map_comp]
  rfl

@[reassoc]
/--
lemma `map_appLE'` / 引理 `map_appLE'`

English:
lemma map_appLE'
  given: (e : V <= f ⁻¹ᵁ U) (i : U' = U)
  proof: map_appLE _ _ _

中文:
引理 map_appLE'
  条件: (e : V <= f ⁻¹ᵁ U) (i : U' = U)
  证明: map_appLE _ _ _

Depends on / 依赖: map_appLE
-/
lemma map_appLE' (e : V <= f ⁻¹ᵁ U) (i : U' = U) :
    Y.presheaf.map (eqToHom i).op ≫ f.appLE U' V (i ▸ e) = f.appLE U V e :=
  map_appLE _ _ _

/--
lemma `app_eq_appLE` / 引理 `app_eq_appLE`

English:
lemma app_eq_appLE
  given: {U : Y.Opens}
  proof: by
  simp [Hom.appLE]

中文:
引理 app_eq_appLE
  条件: {U : Y.Opens}
  证明: by
  simp [Hom.appLE]

Depends on / 依赖: Hom.appLE
-/
lemma app_eq_appLE {U : Y.Opens} :
    f.app U = f.appLE U _ le_rfl := by
  simp [Hom.appLE]

/--
lemma `appLE_eq_app` / 引理 `appLE_eq_app`

English:
lemma appLE_eq_app
  given: {U : Y.Opens}
  proof: (app_eq_appLE f).symm

中文:
引理 appLE_eq_app
  条件: {U : Y.Opens}
  证明: (app_eq_appLE f).symm

Depends on / 依赖: app_eq_appLE
-/
lemma appLE_eq_app {U : Y.Opens} :
    f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U :=
  (app_eq_appLE f).symm

/--
lemma `appLE_congr` / 引理 `appLE_congr`

English:
lemma appLE_congr
  statement: (e : V <= f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V')
  proof: by
  subst e₁; subst e₂; rfl

中文:
引理 appLE_congr
  结论: (e : V <= f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V')
  证明: by
  subst e₁; subst e₂; rfl
-/
lemma appLE_congr (e : V <= f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V')
    (P : forall {R S : CommRingCat.{u}} (_ : R ⟶ S), Prop) :
    P (f.appLE U V e) ↔ P (f.appLE U' V' (e₁ ▸ e₂ ▸ e)) := by
  subst e₁; subst e₂; rfl

/--
Definition of `stalkMap` / `stalkMap` 的定义

English:
definition stalkMap
  signature: (x : X)
  body: f.toLRSHom.stalkMap x

中文:
定义 stalkMap
  签名: (x : X)
  定义体: f.toLRSHom.stalkMap x

Depends on / 依赖: f.toLRSHom.stalkMap, stalkMap, toLRSHom
-/
def stalkMap (x : X) : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x :=
  f.toLRSHom.stalkMap x

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {f g : X ⟶ Y} (h_base : f.base = g.base)
  proof: by
  cases f; cases g; congr 1
  apply LocallyRingedSpace.Hom.ext'
  ext : 1
  · exact h_base
  · exact TopCat.Presheaf.ext (fun U => by simpa using! h_app U)

中文:
引理 ext
  结论: {f g : X ⟶ Y} (h_base : f.base = g.base)
  证明: by
  cases f; cases g; congr 1
  apply LocallyRingedSpace.Hom.ext'
  ext : 1
  · exact h_base
  · exact TopCat.Presheaf.ext (fun U => by simpa using! h_app U)
-/
protected lemma ext {f g : X ⟶ Y} (h_base : f.base = g.base)
    (h_app : forall U, f.app U ≫ X.presheaf.map
      (eqToHom congr((Opens.map $h_base.symm).obj U)).op = g.app U) : f = g := by
  cases f; cases g; congr 1
  apply LocallyRingedSpace.Hom.ext'
  ext : 1
  · exact h_base
  · exact TopCat.Presheaf.ext (fun U => by simpa using! h_app U)

/--
lemma `ext'` / 引理 `ext'`

English:
lemma ext'
  given: {f g : X ⟶ Y} (h : f.toLRSHom = g.toLRSHom)
  statement: f = g
  proof: by
  cases f; cases g; congr 1

中文:
引理 ext'
  条件: {f g : X ⟶ Y} (h : f.toLRSHom = g.toLRSHom)
  结论: f = g
  证明: by
  cases f; cases g; congr 1
-/
protected lemma ext' {f g : X ⟶ Y} (h : f.toLRSHom = g.toLRSHom) : f = g := by
  cases f; cases g; congr 1

/--
lemma `mem_preimage` / 引理 `mem_preimage`

English:
lemma mem_preimage
  given: {x : X} {U : Opens Y}
  statement: x in f ⁻¹ᵁ U ↔ f x in U
  proof: .rfl

中文:
引理 mem_preimage
  条件: {x : X} {U : Opens Y}
  结论: x in f ⁻¹ᵁ U ↔ f x in U
  证明: .rfl
-/
lemma mem_preimage {x : X} {U : Opens Y} : x in f ⁻¹ᵁ U ↔ f x in U := .rfl

/--
lemma `coe_preimage` / 引理 `coe_preimage`

English:
lemma coe_preimage
  given: {U : Opens Y}
  statement: f ⁻¹ᵁ U = f ⁻¹' U
  proof: rfl

中文:
引理 coe_preimage
  条件: {U : Opens Y}
  结论: f ⁻¹ᵁ U = f ⁻¹' U
  证明: rfl
-/
lemma coe_preimage {U : Opens Y} : f ⁻¹ᵁ U = f ⁻¹' U := rfl

/--
lemma `preimage_sup` / 引理 `preimage_sup`

English:
lemma preimage_sup
  given: {U V : Opens Y}
  statement: f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V
  proof: rfl

中文:
引理 preimage_sup
  条件: {U V : Opens Y}
  结论: f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V
  证明: rfl
-/
lemma preimage_sup {U V : Opens Y} : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := rfl
/--
lemma `preimage_inf` / 引理 `preimage_inf`

English:
lemma preimage_inf
  given: {U V : Opens Y}
  statement: f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V
  proof: rfl

中文:
引理 preimage_inf
  条件: {U V : Opens Y}
  结论: f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V
  证明: rfl
-/
lemma preimage_inf {U V : Opens Y} : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := rfl
/--
lemma `preimage_top` / 引理 `preimage_top`

English:
lemma preimage_top
  statement: f ⁻¹ᵁ ⊤ = ⊤
  proof: rfl

中文:
引理 preimage_top
  结论: f ⁻¹ᵁ ⊤ = ⊤
  证明: rfl
-/
@[simp] lemma preimage_top : f ⁻¹ᵁ ⊤ = ⊤ := rfl
/--
lemma `preimage_bot` / 引理 `preimage_bot`

English:
lemma preimage_bot
  statement: f ⁻¹ᵁ ⊥ = ⊥
  proof: rfl

中文:
引理 preimage_bot
  结论: f ⁻¹ᵁ ⊥ = ⊥
  证明: rfl
-/
@[simp] lemma preimage_bot : f ⁻¹ᵁ ⊥ = ⊥ := rfl

/--
lemma `preimage_iSup` / 引理 `preimage_iSup`

English:
lemma preimage_iSup
  given: {ι} (U : ι -> Opens Y)
  statement: f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i
  proof: Opens.ext (by simp)

中文:
引理 preimage_iSup
  条件: {ι} (U : ι -> Opens Y)
  结论: f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i
  证明: Opens.ext (by simp)

Depends on / 依赖: Opens.ext
-/
lemma preimage_iSup {ι} (U : ι -> Opens Y) : f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i :=
  Opens.ext (by simp)

/--
lemma `iSup_preimage_eq_top` / 引理 `iSup_preimage_eq_top`

English:
lemma iSup_preimage_eq_top
  given: {ι} {U : ι -> Opens Y} (hU : iSup U = ⊤)
  proof: f.preimage_iSup U ▸ hU ▸ rfl

@[gcongr]

中文:
引理 iSup_preimage_eq_top
  条件: {ι} {U : ι -> Opens Y} (hU : iSup U = ⊤)
  证明: f.preimage_iSup U ▸ hU ▸ rfl

@[gcongr]

Depends on / 依赖: f.preimage_iSup, preimage_iSup
-/
lemma iSup_preimage_eq_top {ι} {U : ι -> Opens Y} (hU : iSup U = ⊤) :
    ⨆ i, f ⁻¹ᵁ U i = ⊤ := f.preimage_iSup U ▸ hU ▸ rfl

@[gcongr]
/--
lemma `preimage_mono` / 引理 `preimage_mono`

English:
lemma preimage_mono
  given: {U U' : Y.Opens} (hUU' : U <= U')
  proof: fun _ ha => hUU' ha

中文:
引理 preimage_mono
  条件: {U U' : Y.Opens} (hUU' : U <= U')
  证明: fun _ ha => hUU' ha
-/
lemma preimage_mono {U U' : Y.Opens} (hUU' : U <= U') :
    f ⁻¹ᵁ U <= f ⁻¹ᵁ U' :=
  fun _ ha => hUU' ha

/--
lemma `id_preimage` / 引理 `id_preimage`

English:
lemma id_preimage
  given: (U : X.Opens)
  statement: (𝟙 X) ⁻¹ᵁ U = U
  proof: rfl

@[simp]

中文:
引理 id_preimage
  条件: (U : X.Opens)
  结论: (𝟙 X) ⁻¹ᵁ U = U
  证明: rfl

@[simp]
-/
lemma id_preimage (U : X.Opens) : (𝟙 X) ⁻¹ᵁ U = U := rfl

@[simp]
/--
lemma `comp_preimage` / 引理 `comp_preimage`

English:
lemma comp_preimage
  given: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  proof: rfl

中文:
引理 comp_preimage
  条件: {X Y Z : 概形.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  证明: rfl
-/
lemma comp_preimage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U := rfl

end Hom

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps!]
/--
Definition of `forgetToLocallyRingedSpace` / `forgetToLocallyRingedSpace` 的定义

English:
definition forgetToLocallyRingedSpace
  signature: : Scheme ⥤ LocallyRingedSpace where
  body: toLocallyRingedSpace
  map := Hom.toLRSHom

中文:
定义 forgetToLocallyRingedSpace
  签名: : 概形 ⥤ LocallyRinged空间 where
  定义体: toLocallyRingedSpace
  map := Hom.toLRSHom

Depends on / 依赖: toLocallyRingedSpace
-/
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace where
  obj := toLocallyRingedSpace
  map := Hom.toLRSHom

/-- The forget functor `Scheme ⥤ LocallyRingedSpace` is fully faithful. -/
@[simps preimage_toLRSHom]
/--
Definition of `fullyFaithfulForgetToLocallyRingedSpace` / `fullyFaithfulForgetToLocallyRingedSpace` 的定义

English:
definition fullyFaithfulForgetToLocallyRingedSpace
  signature: :
  body: Hom.mk

中文:
定义 fullyFaithfulForgetToLocallyRingedSpace
  签名: :
  定义体: Hom.mk

Depends on / 依赖: Hom.mk
-/
def fullyFaithfulForgetToLocallyRingedSpace :
    forgetToLocallyRingedSpace.FullyFaithful where
  preimage := Hom.mk

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forgetToLocallyRingedSpace.Full
  body: fullyFaithfulForgetToLocallyRingedSpace.full

中文:
实例 :
  签名: forgetToLocallyRingedSpace.满
  定义体: fullyFaithfulForgetToLocallyRingedSpace.full

Depends on / 依赖: fullyFaithfulForgetToLocallyRingedSpace, fullyFaithfulForgetToLocallyRingedSpace.full
-/
instance : forgetToLocallyRingedSpace.Full :=
  fullyFaithfulForgetToLocallyRingedSpace.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forgetToLocallyRingedSpace.Faithful
  body: fullyFaithfulForgetToLocallyRingedSpace.faithful

中文:
实例 :
  签名: forgetToLocallyRingedSpace.忠实
  定义体: fullyFaithfulForgetToLocallyRingedSpace.faithful

Depends on / 依赖: faithful, fullyFaithfulForgetToLocallyRingedSpace, fullyFaithfulForgetToLocallyRingedSpace.faithful
-/
instance : forgetToLocallyRingedSpace.Faithful :=
  fullyFaithfulForgetToLocallyRingedSpace.faithful

/-- The forgetful functor from `Scheme` to `TopCat`. -/
@[simps!]
/--
Definition of `forgetToTop` / `forgetToTop` 的定义

English:
definition forgetToTop
  signature: : Scheme ⥤ TopCat
  body: Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop

中文:
定义 forgetToTop
  签名: : 概形 ⥤ 顶元素范畴
  定义体: Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.forgetToTop, Scheme, Scheme.forgetToLocallyRingedSpace, forgetToLocallyRingedSpace, forgetToTop
-/
def forgetToTop : Scheme ⥤ TopCat :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop

/--
Definition of `homeoOfIso` / `homeoOfIso` 的定义

English:
definition homeoOfIso
  signature: {X Y : Scheme.{u}} (e : X ≅ Y)
  body: TopCat.homeoOfIso (forgetToTop.mapIso e)

@[simp]

中文:
定义 homeoOfIso
  签名: {X Y : 概形.{u}} (e : X ≅ Y)
  定义体: TopCat.homeoOfIso (forgetToTop.mapIso e)

@[simp]

Depends on / 依赖: TopCat, TopCat.homeoOfIso, forgetToTop, forgetToTop.mapIso, homeoOfIso, mapIso
-/
noncomputable def homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso (forgetToTop.mapIso e)

@[simp]
/--
lemma `coe_homeoOfIso` / 引理 `coe_homeoOfIso`

English:
lemma coe_homeoOfIso
  given: {X Y : Scheme.{u}} (e : X ≅ Y)
  proof: rfl

@[simp]

中文:
引理 coe_homeoOfIso
  条件: {X Y : 概形.{u}} (e : X ≅ Y)
  证明: rfl

@[simp]
-/
lemma coe_homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    ⇑(homeoOfIso e) = e.hom := rfl

@[simp]
/--
lemma `coe_homeoOfIso_symm` / 引理 `coe_homeoOfIso_symm`

English:
lemma coe_homeoOfIso_symm
  given: {X Y : Scheme.{u}} (e : X ≅ Y)
  proof: rfl

@[simp]

中文:
引理 coe_homeoOfIso_symm
  条件: {X Y : 概形.{u}} (e : X ≅ Y)
  证明: rfl

@[simp]
-/
lemma coe_homeoOfIso_symm {X Y : Scheme.{u}} (e : X ≅ Y) :
    ⇑(homeoOfIso e.symm) = e.inv := rfl

@[simp]
/--
lemma `homeoOfIso_symm` / 引理 `homeoOfIso_symm`

English:
lemma homeoOfIso_symm
  given: {X Y : Scheme} (e : X ≅ Y)
  proof: rfl

中文:
引理 homeoOfIso_symm
  条件: {X Y : 概形} (e : X ≅ Y)
  证明: rfl
-/
lemma homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) :
    (homeoOfIso e).symm = homeoOfIso e.symm := rfl

/--
lemma `homeoOfIso_apply` / 引理 `homeoOfIso_apply`

English:
lemma homeoOfIso_apply
  given: {X Y : Scheme} (e : X ≅ Y) (x : X)
  proof: rfl

alias _root_.CategoryTheory.Iso.schemeIsoToHomeo := homeoOfIso

中文:
引理 homeoOfIso_apply
  条件: {X Y : 概形} (e : X ≅ Y) (x : X)
  证明: rfl

alias _root_.CategoryTheory.Iso.schemeIsoToHomeo := homeoOfIso
-/
lemma homeoOfIso_apply {X Y : Scheme} (e : X ≅ Y) (x : X) :
    homeoOfIso e x = e.hom x := rfl

alias _root_.CategoryTheory.Iso.schemeIsoToHomeo := homeoOfIso

/--
Definition of `Hom.homeomorph` / `Hom.homeomorph` 的定义

English:
definition Hom.homeomorph
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
  body: (asIso f).schemeIsoToHomeo

@[simp]

中文:
定义 态射.homeomorph
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) [是同构 (C := 概形) f]
  定义体: (asIso f).schemeIsoToHomeo

@[simp]

Depends on / 依赖: Scheme
-/
noncomputable def Hom.homeomorph {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] :
    X ≃ₜ Y :=
  (asIso f).schemeIsoToHomeo

@[simp]
/--
lemma `Hom.homeomorph_apply` / 引理 `Hom.homeomorph_apply`

English:
lemma Hom.homeomorph_apply
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] (x)
  proof: rfl

中文:
引理 态射.homeomorph_apply
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) [是同构 (C := 概形) f] (x)
  证明: rfl

Depends on / 依赖: Scheme
-/
lemma Hom.homeomorph_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] (x) :
    f.homeomorph x = f x := rfl

/--
Instance `hasCoeToTopCat` / 实例 `hasCoeToTopCat`

English:
instance hasCoeToTopCat
  signature: : CoeOut Scheme TopCat where
  body: X.carrier

中文:
实例 hasCoeToTopCat
  签名: : CoeOut 概形 顶元素范畴 where
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance hasCoeToTopCat : CoeOut Scheme TopCat where
  coe X := X.carrier

/-- forgetful functor to `TopCat` is the same as coercion -/
unif_hint forgetToTop_obj_eq_coe (X : Scheme) where ⊢ forgetToTop.obj X ≟ (X : TopCat)

/-- The forgetful functor from `Scheme` to `Type`. -/
nonrec def forget : Scheme.{u} ⥤ Type u := Scheme.forgetToTop ⋙ forget TopCat

/--
lemma `forgetToTop_comp_forget` / 引理 `forgetToTop_comp_forget`

English:
lemma forgetToTop_comp_forget
  statement: forgetToTop ⋙ CategoryTheory.forget TopCat = forget
  proof: rfl

中文:
引理 forgetToTop_comp_forget
  结论: forgetToTop ⋙ 范畴论.forget 顶元素范畴 = forget
  证明: rfl
-/
lemma forgetToTop_comp_forget : forgetToTop ⋙ CategoryTheory.forget TopCat = forget := rfl

/-- forgetful functor to `Scheme` is the same as coercion -/
-- Schemes are often coerced as types, and it would be useful to have definitionally equal types
-- to be reducibly equal. The alternative is to make `forget` reducible but that option has
-- poor performance consequences.
unif_hint forget_obj_eq_coe (X : Scheme) where ⊢ forget.obj X ≟ (X : Type*)

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  given: (X)
  statement: Scheme.forget.obj X = X
  proof: rfl

中文:
引理 forget_obj
  条件: (X)
  结论: 概形.forget.obj X = X
  证明: rfl
-/
@[simp] lemma forget_obj (X) : Scheme.forget.obj X = X := rfl
/--
lemma `forget_map'` / 引理 `forget_map'`

English:
lemma forget_map'
  given: {X Y} (f : X ⟶ Y)
  statement: (forget.map f : _ -> _) = f
  proof: rfl

中文:
引理 forget_map'
  条件: {X Y} (f : X ⟶ Y)
  结论: (forget.map f : _ -> _) = f
  证明: rfl
-/
lemma forget_map' {X Y} (f : X ⟶ Y) : (forget.map f : _ -> _) = f := rfl
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y} (f : X ⟶ Y)
  statement: forget.map f = ↾f
  proof: rfl

中文:
引理 forget_map
  条件: {X Y} (f : X ⟶ Y)
  结论: forget.map f = ↾f
  证明: rfl
-/
@[simp] lemma forget_map {X Y} (f : X ⟶ Y) : forget.map f = ↾f := rfl

namespace Hom

@[simp]
/--
theorem `id_base` / 定理 `id_base`

English:
theorem id_base
  given: (X : Scheme)
  statement: (𝟙 X :).base = 𝟙 _
  proof: rfl

@[simp]

中文:
定理 id_base
  条件: (X : 概形)
  结论: (𝟙 X :).base = 𝟙 _
  证明: rfl

@[simp]
-/
theorem id_base (X : Scheme) : (𝟙 X :).base = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `id_app` / 定理 `id_app`

English:
theorem id_app
  given: {X : Scheme} (U : X.Opens)
  proof: rfl

@[simp]

中文:
定理 id_app
  条件: {X : 概形} (U : X.Opens)
  证明: rfl

@[simp]
-/
theorem id_app {X : Scheme} (U : X.Opens) :
    (𝟙 X :).app U = 𝟙 _ := rfl

@[simp]
/--
theorem `id_appTop` / 定理 `id_appTop`

English:
theorem id_appTop
  given: {X : Scheme}
  proof: rfl

@[reassoc]

中文:
定理 id_appTop
  条件: {X : 概形}
  证明: rfl

@[reassoc]
-/
theorem id_appTop {X : Scheme} :
    (𝟙 X :).appTop = 𝟙 _ :=
  rfl

@[reassoc]
/--
theorem `comp_toLRSHom` / 定理 `comp_toLRSHom`

English:
theorem comp_toLRSHom
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp, reassoc]

中文:
定理 comp_toLRSHom
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp, reassoc]
-/
theorem comp_toLRSHom {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toLRSHom = f.toLRSHom ≫ g.toLRSHom :=
  rfl

@[simp, reassoc]
/--
theorem `comp_base` / 定理 `comp_base`

English:
theorem comp_base
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_base
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by
  simp

@[simp, reassoc] -- reassoc lemma does not need `simp`

中文:
定理 comp_apply
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by
  simp

@[simp, reassoc] -- reassoc lemma does not need `simp`
-/
theorem comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by
  simp

@[simp, reassoc] -- reassoc lemma does not need `simp`
/--
theorem `comp_app` / 定理 `comp_app`

English:
theorem comp_app
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  proof: rfl

@[simp, reassoc] -- reassoc lemma does not need `simp`

中文:
定理 comp_app
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) (U)
  证明: rfl

@[simp, reassoc] -- reassoc lemma does not need `simp`
-/
theorem comp_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).app U = g.app U ≫ f.app _ :=
  rfl

@[simp, reassoc] -- reassoc lemma does not need `simp`
/--
theorem `comp_appTop` / 定理 `comp_appTop`

English:
theorem comp_appTop
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[reassoc]

中文:
定理 comp_appTop
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[reassoc]
-/
theorem comp_appTop {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop :=
  rfl

@[reassoc]
/--
theorem `appLE_comp_appLE` / 定理 `appLE_comp_appLE`

English:
theorem appLE_comp_appLE
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂)
  proof: by
  dsimp [Hom.appLE]
  rw [Category.assoc]; rw [f.naturality_assoc]; rw [← Functor.map_comp]
  rfl

中文:
定理 appLE_comp_appLE
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂)
  证明: by
  dsimp [Hom.appLE]
  rw [Category.assoc]; rw [f.naturality_assoc]; rw [← Functor.map_comp]
  rfl

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Hom.appLE, f.naturality_assoc, map_comp, naturality_assoc
-/
theorem appLE_comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ =
      (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le) := by
  dsimp [Hom.appLE]
  rw [Category.assoc]; rw [f.naturality_assoc]; rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc] -- reassoc lemma does not need `simp`
/--
theorem `comp_appLE` / 定理 `comp_appLE`

English:
theorem comp_appLE
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V e)
  proof: by
  rw [g.app_eq_appLE]; rw [appLE_comp_appLE]

中文:
定理 comp_appLE
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) (U V e)
  证明: by
  rw [g.app_eq_appLE]; rw [appLE_comp_appLE]

Depends on / 依赖: appLE_comp_appLE, app_eq_appLE, g.app_eq_appLE
-/
theorem comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V e) :
    (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e := by
  rw [g.app_eq_appLE]; rw [appLE_comp_appLE]

/--
theorem `congr_app` / 定理 `congr_app`

English:
theorem congr_app
  given: {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U)
  proof: by
  subst e; simp

中文:
定理 congr_app
  条件: {X Y : 概形} {f g : X ⟶ Y} (e : f = g) (U)
  证明: by
  subst e; simp
-/
theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e; rfl)).op := by
  subst e; simp

/--
theorem `app_eq` / 定理 `app_eq`

English:
theorem app_eq
  given: {X Y : Scheme} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V)
  proof: by
  aesop

中文:
定理 app_eq
  条件: {X Y : 概形} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V)
  证明: by
  aesop
-/
theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    f.app U =
      Y.presheaf.map (eqToHom e.symm).op ≫ f.app V ≫ X.presheaf.map (eqToHom (e ▸ rfl)).op := by
  aesop

/--
theorem `eqToHom_app` / 定理 `eqToHom_app`

English:
theorem eqToHom_app
  given: {X Y : Scheme} (e : X = Y) (U)
  proof: by subst e; rfl

中文:
定理 eqToHom_app
  条件: {X Y : 概形} (e : X = Y) (U)
  证明: by subst e; rfl
-/
theorem eqToHom_app {X Y : Scheme} (e : X = Y) (U) :
    (eqToHom e).app U = eqToHom (by subst e; rfl) := by subst e; rfl

/--
Instance `isIso_toLRSHom` / 实例 `isIso_toLRSHom`

English:
instance isIso_toLRSHom
  signature: {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
  body: forgetToLocallyRingedSpace.map_isIso f

中文:
实例 isIso_toLRSHom
  签名: {X Y : 概形} (f : X ⟶ Y) [是同构 f]
  定义体: forgetToLocallyRingedSpace.map_isIso f

Depends on / 依赖: forgetToLocallyRingedSpace, forgetToLocallyRingedSpace.map_isIso, map_isIso
-/
instance isIso_toLRSHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toLRSHom :=
  forgetToLocallyRingedSpace.map_isIso f

/--
Instance `isIso_toPshHom` / 实例 `isIso_toPshHom`

English:
instance isIso_toPshHom
  signature: {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
  body: inferInstanceAs (IsIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).map f.toLRSHom))

中文:
实例 isIso_toPshHom
  签名: {X Y : 概形} (f : X ⟶ Y) [是同构 f]
  定义体: inferInstanceAs (IsIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).map f.toLRSHom))

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, f.toLRSHom, forgetToPresheafedSpace, forgetToSheafedSpace, toLRSHom
-/
instance isIso_toPshHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toPshHom :=
  inferInstanceAs (IsIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).map f.toLRSHom))

/--
Instance `isIso_base` / 实例 `isIso_base`

English:
instance isIso_base
  signature: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  body: Scheme.forgetToTop.map_isIso f

中文:
实例 isIso_base
  签名: {X Y : 概形.{u}} (f : X ⟶ Y) [是同构 f]
  定义体: Scheme.forgetToTop.map_isIso f

Depends on / 依赖: Scheme, Scheme.forgetToTop.map_isIso, forgetToTop, map_isIso
-/
instance isIso_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  Scheme.forgetToTop.map_isIso f

set_option backward.isDefEq.respectTransparency false in
instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U) : IsIso (f.app U) :=
  haveI := PresheafedSpace.c_isIso_of_iso f.toPshHom
  NatIso.isIso_app_of_isIso f.c _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `inv_app` / 定理 `inv_app`

English:
theorem inv_app
  given: {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : X.Opens)
  proof: by
  rw [IsIso.eq_comp_inv]; rw [← comp_app]; rw [congr_app (IsIso.hom_inv_id f)]; rw [id_app]; rw [Category.id_comp]

中文:
定理 inv_app
  条件: {X Y : 概形} (f : X ⟶ Y) [是同构 f] (U : X.Opens)
  证明: by
  rw [IsIso.eq_comp_inv]; rw [← comp_app]; rw [congr_app (IsIso.hom_inv_id f)]; rw [id_app]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, IsIso.eq_comp_inv, IsIso.hom_inv_id, comp_app, congr_app, eq_comp_inv, hom_inv_id, id_app, id_comp
-/
theorem inv_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : X.Opens) :
    (inv f).app U =
      X.presheaf.map (eqToHom (show (f ≫ inv f) ⁻¹ᵁ U = U by rw [IsIso.hom_inv_id]; rfl)).op ≫
        inv (f.app ((inv f) ⁻¹ᵁ U)) := by
  rw [IsIso.eq_comp_inv]; rw [← comp_app]; rw [congr_app (IsIso.hom_inv_id f)]; rw [id_app]; rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `inv_appTop` / 定理 `inv_appTop`

English:
theorem inv_appTop
  given: {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
  proof: by simp

中文:
定理 inv_appTop
  条件: {X Y : 概形} (f : X ⟶ Y) [是同构 f]
  证明: by simp
-/
theorem inv_appTop {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    (inv f).appTop = inv f.appTop := by simp

/--
Definition of `copyBase` / `copyBase` 的定义

English:
definition copyBase
  signature: {X Y : Scheme} (f : X.Hom Y) (g : X -> Y) (h : f.base = g)
  body: TopCat.ofHom ⟨g, h ▸ f.base.1.2⟩
  c := f.c ≫ (TopCat.Presheaf.pushforwardEq (by subst h; rfl) _).hom
  prop x := by
    subst h
    convert! f.prop x using 4
    cat_disch

中文:
定义 copyBase
  签名: {X Y : 概形} (f : X.态射 Y) (g : X -> Y) (h : f.base = g)
  定义体: TopCat.ofHom ⟨g, h ▸ f.base.1.2⟩
  c := f.c ≫ (TopCat.Presheaf.pushforwardEq (by subst h; rfl) _).hom
  prop x := by
    subst h
    convert! f.prop x using 4
    cat_disch

Depends on / 依赖: TopCat, TopCat.ofHom, f.base
-/
def copyBase {X Y : Scheme} (f : X.Hom Y) (g : X -> Y) (h : f.base = g) : X ⟶ Y where
  base := TopCat.ofHom ⟨g, h ▸ f.base.1.2⟩
  c := f.c ≫ (TopCat.Presheaf.pushforwardEq (by subst h; rfl) _).hom
  prop x := by
    subst h
    convert! f.prop x using 4
    cat_disch

/--
lemma `copyBase_eq` / 引理 `copyBase_eq`

English:
lemma copyBase_eq
  given: {X Y : Scheme} (f : X.Hom Y) (g : X -> Y) (h : f.base = g)
  proof: by
  subst h
  obtain ⟨⟨⟨f₁, f₂⟩, f₃⟩, f₄⟩ := f
  simp only [Hom.copyBase]
  congr
  cat_disch

中文:
引理 copyBase_eq
  条件: {X Y : 概形} (f : X.态射 Y) (g : X -> Y) (h : f.base = g)
  证明: by
  subst h
  obtain ⟨⟨⟨f₁, f₂⟩, f₃⟩, f₄⟩ := f
  simp only [Hom.copyBase]
  congr
  cat_disch

Depends on / 依赖: Hom.copyBase, cat_disch, copyBase
-/
lemma copyBase_eq {X Y : Scheme} (f : X.Hom Y) (g : X -> Y) (h : f.base = g) :
    f.copyBase g h = f := by
  subst h
  obtain ⟨⟨⟨f₁, f₂⟩, f₃⟩, f₄⟩ := f
  simp only [Hom.copyBase]
  congr
  cat_disch

end Hom

end Scheme

/--
Definition of `Spec` / `Spec` 的定义

English:
definition Spec
  signature: (R : CommRingCat)
  body: ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R

中文:
定义 Spec
  签名: (R : 交换环范畴)
  定义体: ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R

Depends on / 依赖: Spec.toLocallyRingedSpace.obj, restrictTopIso, toLocallyRingedSpace
-/
def Spec (R : CommRingCat) : Scheme where
  local_affine _ := ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R

/--
theorem `Spec_toLocallyRingedSpace` / 定理 `Spec_toLocallyRingedSpace`

English:
theorem Spec_toLocallyRingedSpace
  given: (R : CommRingCat)
  proof: rfl

中文:
定理 Spec_toLocallyRingedSpace
  条件: (R : 交换环范畴)
  证明: rfl
-/
theorem Spec_toLocallyRingedSpace (R : CommRingCat) :
    (Spec R).toLocallyRingedSpace = Spec.locallyRingedSpaceObj R :=
  rfl

/--
Definition of `Spec.map` / `Spec.map` 的定义

English:
definition Spec.map
  signature: {R S : CommRingCat} (f : R ⟶ S)
  body: ⟨Spec.locallyRingedSpaceMap f⟩

@[simp]

中文:
定义 Spec.map
  签名: {R S : 交换环范畴} (f : R ⟶ S)
  定义体: ⟨Spec.locallyRingedSpaceMap f⟩

@[simp]

Depends on / 依赖: Spec.locallyRingedSpaceMap, locallyRingedSpaceMap
-/
def Spec.map {R S : CommRingCat} (f : R ⟶ S) : Spec S ⟶ Spec R :=
  ⟨Spec.locallyRingedSpaceMap f⟩

@[simp]
/--
theorem `Spec.map_id` / 定理 `Spec.map_id`

English:
theorem Spec.map_id
  given: (R : CommRingCat)
  statement: Spec.map (𝟙 R) = 𝟙 (Spec R)
  proof: Scheme.Hom.ext' Spec.locallyRingedSpaceMap_id R

中文:
定理 Spec.map_id
  条件: (R : 交换环范畴)
  结论: Spec.map (𝟙 R) = 𝟙 (Spec R)
  证明: Scheme.Hom.ext' Spec.locallyRingedSpaceMap_id R

Depends on / 依赖: Scheme, Scheme.Hom.ext, Spec.locallyRingedSpaceMap_id, locallyRingedSpaceMap_id
-/
theorem Spec.map_id (R : CommRingCat) : Spec.map (𝟙 R) = 𝟙 (Spec R) :=
Scheme.Hom.ext' Spec.locallyRingedSpaceMap_id R

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc, simp]
/--
theorem `Spec.map_comp` / 定理 `Spec.map_comp`

English:
theorem Spec.map_comp
  given: {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T)
  proof: Scheme.Hom.ext' Spec.locallyRingedSpaceMap_comp f g

中文:
定理 Spec.map_comp
  条件: {R S T : 交换环范畴} (f : R ⟶ S) (g : S ⟶ T)
  证明: Scheme.Hom.ext' Spec.locallyRingedSpaceMap_comp f g

Depends on / 依赖: Scheme, Scheme.Hom.ext, Spec.locallyRingedSpaceMap_comp, locallyRingedSpaceMap_comp
-/
theorem Spec.map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f :=
Scheme.Hom.ext' Spec.locallyRingedSpaceMap_comp f g

/-- The spectrum, as a contravariant functor from commutative rings to schemes. -/
@[simps, implicit_reducible]
/--
Definition of `Scheme.Spec` / `Scheme.Spec` 的定义

English:
definition Scheme.Spec
  signature: : CommRingCatᵒᵖ ⥤ Scheme where
  body: Spec (unop R)
  map f := Spec.map f.unop
  map_id R := by simp
  map_comp f g := by simp

中文:
定义 概形.Spec
  签名: : CommRingCatᵒᵖ ⥤ 概形 where
  定义体: Spec (unop R)
  map f := Spec.map f.unop
  map_id R := by simp
  map_comp f g := by simp
-/
protected def Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := Spec (unop R)
  map f := Spec.map f.unop
  map_id R := by simp
  map_comp f g := by simp

/--
lemma `Spec.map_eqToHom` / 引理 `Spec.map_eqToHom`

English:
lemma Spec.map_eqToHom
  given: {R S : CommRingCat} (e : R = S)
  proof: by
  subst e; exact Spec.map_id _

中文:
引理 Spec.map_eqToHom
  条件: {R S : 交换环范畴} (e : R = S)
  证明: by
  subst e; exact Spec.map_id _

Depends on / 依赖: Spec.map_id, map_id
-/
lemma Spec.map_eqToHom {R S : CommRingCat} (e : R = S) :
    Spec.map (eqToHom e) = eqToHom (e ▸ rfl) := by
  subst e; exact Spec.map_id _

instance {R S : CommRingCat} (f : R ⟶ S) [IsIso f] : IsIso (Spec.map f) :=
  inferInstanceAs (IsIso <| Scheme.Spec.map f.op)

@[simp]
/--
lemma `Spec.map_inv` / 引理 `Spec.map_inv`

English:
lemma Spec.map_inv
  given: {R S : CommRingCat} (f : R ⟶ S) [IsIso f]
  proof: by
  change Scheme.Spec.map (inv f).op = inv (Scheme.Spec.map f.op)
  rw [op_inv]; rw [← Scheme.Spec.map_inv]

中文:
引理 Spec.map_inv
  条件: {R S : 交换环范畴} (f : R ⟶ S) [是同构 f]
  证明: by
  change Scheme.Spec.map (inv f).op = inv (Scheme.Spec.map f.op)
  rw [op_inv]; rw [← Scheme.Spec.map_inv]

Depends on / 依赖: Scheme, Scheme.Spec.map, Scheme.Spec.map_inv, f.op, map_inv, op_inv
-/
lemma Spec.map_inv {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    Spec.map (inv f) = inv (Spec.map f) := by
  change Scheme.Spec.map (inv f).op = inv (Scheme.Spec.map f.op)
  rw [op_inv]; rw [← Scheme.Spec.map_inv]

/-- `Spec R` with the specialization order is order isomorphic to the dual of the prime
spectrum of `R`. -/
@[simps]
/--
Definition of `specOrderIsoPrimeSpectrum` / `specOrderIsoPrimeSpectrum` 的定义

English:
definition specOrderIsoPrimeSpectrum
  signature: (R : CommRingCat)
  body: .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := PrimeSpectrum.le_iff_specializes b a

中文:
定义 specOrderIsoPrimeSpectrum
  签名: (R : 交换环范畴)
  定义体: .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := PrimeSpectrum.le_iff_specializes b a

Depends on / 依赖: toDual
-/
def specOrderIsoPrimeSpectrum (R : CommRingCat) : Spec R ≃o (PrimeSpectrum R)ᵒᵈ where
  toFun x := .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := PrimeSpectrum.le_iff_specializes b a

/-- `PrimeSpectrum R` with the inclusion order is order isomorphic to the dual of `Spec R`. -/
@[simps]
/--
Definition of `primeSpectrumOrderIsoSpec` / `primeSpectrumOrderIsoSpec` 的定义

English:
definition primeSpectrumOrderIsoSpec
  signature: (R : Type u) [CommRing R]
  body: .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := (PrimeSpectrum.le_iff_specializes a b).symm

中文:
定义 primeSpectrumOrderIsoSpec
  签名: (R : 类型u) [交换环 R]
  定义体: .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := (PrimeSpectrum.le_iff_specializes a b).symm

Depends on / 依赖: toDual
-/
def primeSpectrumOrderIsoSpec (R : Type u) [CommRing R] : PrimeSpectrum R ≃o (Spec (.of R))ᵒᵈ where
  toFun x := .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := (PrimeSpectrum.le_iff_specializes a b).symm

section

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

-- The lemmas below are not tagged simp to respect the abstraction.
/--
lemma `Spec_carrier` / 引理 `Spec_carrier`

English:
lemma Spec_carrier
  given: (R : CommRingCat.{u})
  statement: (Spec R).carrier = PrimeSpectrum R
  proof: rfl

中文:
引理 Spec_carrier
  条件: (R : 交换环范畴.{u})
  结论: (Spec R).carrier = 素谱 R
  证明: rfl
-/
lemma Spec_carrier (R : CommRingCat.{u}) : (Spec R).carrier = PrimeSpectrum R := rfl
/--
lemma `Spec_sheaf` / 引理 `Spec_sheaf`

English:
lemma Spec_sheaf
  given: (R : CommRingCat.{u})
  statement: (Spec R).sheaf = Spec.structureSheaf R
  proof: rfl

中文:
引理 Spec_sheaf
  条件: (R : 交换环范畴.{u})
  结论: (Spec R).sheaf = Spec.structureSheaf R
  证明: rfl
-/
lemma Spec_sheaf (R : CommRingCat.{u}) : (Spec R).sheaf = Spec.structureSheaf R := rfl
/--
lemma `Spec_presheaf` / 引理 `Spec_presheaf`

English:
lemma Spec_presheaf
  given: (R : CommRingCat.{u})
  statement: (Spec R).presheaf = (Spec.structureSheaf R).1
  proof: rfl

中文:
引理 Spec_presheaf
  条件: (R : 交换环范畴.{u})
  结论: (Spec R).presheaf = (Spec.structureSheaf R).1
  证明: rfl
-/
lemma Spec_presheaf (R : CommRingCat.{u}) : (Spec R).presheaf = (Spec.structureSheaf R).1 := rfl
/--
lemma `Spec.map_base` / 引理 `Spec.map_base`

English:
lemma Spec.map_base
  statement: (Spec.map f).base = ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩
  proof: rfl

中文:
引理 Spec.map_base
  结论: (Spec.map f).base = ofHom ⟨_, 素谱.continuous_comap f.hom⟩
  证明: rfl
-/
lemma Spec.map_base : (Spec.map f).base = ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩ := rfl
/--
lemma `Spec.map_apply` / 引理 `Spec.map_apply`

English:
lemma Spec.map_apply
  given: (x : Spec S)
  statement: Spec.map f x = PrimeSpectrum.comap f.hom x
  proof: rfl

中文:
引理 Spec.map_apply
  条件: (x : Spec S)
  结论: Spec.map f x = 素谱.comap f.hom x
  证明: rfl
-/
lemma Spec.map_apply (x : Spec S) : Spec.map f x = PrimeSpectrum.comap f.hom x := rfl

/--
lemma `Spec.map_app` / 引理 `Spec.map_app`

English:
lemma Spec.map_app
  given: (U)
  proof: rfl

中文:
引理 Spec.map_app
  条件: (U)
  证明: rfl
-/
lemma Spec.map_app (U) :
    (Spec.map f).app U =
      CommRingCat.ofHom (StructureSheaf.comap f.hom U (Spec.map f ⁻¹ᵁ U) le_rfl) := rfl

/--
lemma `Spec.map_appLE` / 引理 `Spec.map_appLE`

English:
lemma Spec.map_appLE
  given: {U V} (e : U <= Spec.map f ⁻¹ᵁ V)
  proof: rfl

中文:
引理 Spec.map_appLE
  条件: {U V} (e : U <= Spec.map f ⁻¹ᵁ V)
  证明: rfl
-/
lemma Spec.map_appLE {U V} (e : U <= Spec.map f ⁻¹ᵁ V) :
    (Spec.map f).appLE V U e = CommRingCat.ofHom (StructureSheaf.comap f.hom V U e) := rfl

instance {A : CommRingCat} [Nontrivial A] : Nonempty (Spec A) :=
inferInstanceAs Nonempty (PrimeSpectrum A)

end

namespace Scheme

/--
theorem `isEmpty_of_commSq` / 定理 `isEmpty_of_commSq`

English:
theorem isEmpty_of_commSq
  statement: {W X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  proof: ⟨fun x => (Set.disjoint_iff_inter_eq_empty.mp H).le
    ⟨⟨i x, congr($(h.w) x)⟩, ⟨j x, rfl⟩⟩⟩

中文:
定理 isEmpty_of_commSq
  结论: {W X Y S : 概形.{u}} {f : X ⟶ S} {g : Y ⟶ S}
  证明: ⟨fun x => (Set.disjoint_iff_inter_eq_empty.mp H).le
    ⟨⟨i x, congr($(h.w) x)⟩, ⟨j x, rfl⟩⟩⟩

Depends on / 依赖: Set.disjoint_iff_inter_eq_empty.mp, disjoint_iff_inter_eq_empty
-/
theorem isEmpty_of_commSq {W X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : W ⟶ X} {j : W ⟶ Y} (h : CommSq i j f g)
    (H : Disjoint (Set.range f) (Set.range g)) : IsEmpty W :=
  ⟨fun x => (Set.disjoint_iff_inter_eq_empty.mp H).le
    ⟨⟨i x, congr($(h.w) x)⟩, ⟨j x, rfl⟩⟩⟩

/-- The empty scheme. -/
@[simps]
/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : Scheme where
  body: TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x

中文:
定义 empty
  签名: : 概形 where
  定义体: TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x

Depends on / 依赖: PEmpty, TopCat, TopCat.of
-/
def empty : Scheme where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection Scheme
  body: ⟨empty⟩

中文:
实例 :
  签名: EmptyCollection 概形
  定义体: ⟨empty⟩
-/
instance : EmptyCollection Scheme :=
  ⟨empty⟩

/--
Definition of `Γ` / `Γ` 的定义

English:
definition Γ
  signature: : Schemeᵒᵖ ⥤ CommRingCat
  body: Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ

中文:
定义 Γ
  签名: : Schemeᵒᵖ ⥤ 交换环范畴
  定义体: Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ

Depends on / 依赖: LocallyRingedSpace, Scheme, Scheme.forgetToLocallyRingedSpace.op, forgetToLocallyRingedSpace
-/
def Γ : Schemeᵒᵖ ⥤ CommRingCat :=
  Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ

/--
theorem `Γ_def` / 定理 `Γ_def`

English:
theorem Γ_def
  statement: Γ = Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ
  proof: rfl

@[simp]

中文:
定理 Γ_def
  结论: Γ = 概形.forgetToLocallyRingedSpace.op ⋙ LocallyRinged空间.Γ
  证明: rfl

@[simp]
-/
theorem Γ_def : Γ = Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ :=
  rfl

@[simp]
/--
theorem `Γ_obj` / 定理 `Γ_obj`

English:
theorem Γ_obj
  given: (X : Schemeᵒᵖ)
  statement: Γ.obj X = Γ(unop X, ⊤)
  proof: rfl

中文:
定理 Γ_obj
  条件: (X : Schemeᵒᵖ)
  结论: Γ.obj X = Γ(unop X, ⊤)
  证明: rfl
-/
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = Γ(unop X, ⊤) :=
  rfl

/--
theorem `Γ_obj_op` / 定理 `Γ_obj_op`

English:
theorem Γ_obj_op
  given: (X : Scheme)
  statement: Γ.obj (op X) = Γ(X, ⊤)
  proof: rfl

@[simp]

中文:
定理 Γ_obj_op
  条件: (X : 概形)
  结论: Γ.obj (op X) = Γ(X, ⊤)
  证明: rfl

@[simp]
-/
theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = Γ(X, ⊤) :=
  rfl

@[simp]
/--
theorem `Γ_map` / 定理 `Γ_map`

English:
theorem Γ_map
  given: {X Y : Schemeᵒᵖ} (f : X ⟶ Y)
  statement: Γ.map f = f.unop.appTop
  proof: rfl

中文:
定理 Γ_map
  条件: {X Y : Schemeᵒᵖ} (f : X ⟶ Y)
  结论: Γ.map f = f.unop.appTop
  证明: rfl
-/
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.appTop :=
  rfl

/--
theorem `Γ_map_op` / 定理 `Γ_map_op`

English:
theorem Γ_map_op
  given: {X Y : Scheme} (f : X ⟶ Y)
  statement: Γ.map f.op = f.appTop
  proof: rfl

中文:
定理 Γ_map_op
  条件: {X Y : 概形} (f : X ⟶ Y)
  结论: Γ.map f.op = f.appTop
  证明: rfl
-/
theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.appTop :=
  rfl

/--
Definition of `SpecΓIdentity` / `SpecΓIdentity` 的定义

English:
definition SpecΓIdentity
  signature: : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 _
  body: LocallyRingedSpace.SpecΓIdentity

中文:
定义 SpecΓIdentity
  签名: : 概形.Spec.rightOp ⋙ 概形.Γ ≅ 𝟭 _
  定义体: LocallyRingedSpace.SpecΓIdentity

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.Spec
-/
def SpecΓIdentity : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 _ :=
  LocallyRingedSpace.SpecΓIdentity

variable (R : CommRingCat.{u})

/--
Definition of `ΓSpecIso` / `ΓSpecIso` 的定义

English:
definition ΓSpecIso
  signature: : Γ(Spec R, ⊤) ≅ R
  body: SpecΓIdentity.app R

中文:
定义 ΓSpecIso
  签名: : Γ(Spec R, ⊤) ≅ R
  定义体: SpecΓIdentity.app R

Depends on / 依赖: Identity.app
-/
def ΓSpecIso : Γ(Spec R, ⊤) ≅ R := SpecΓIdentity.app R

/--
lemma `SpecΓIdentity_app` / 引理 `SpecΓIdentity_app`

English:
lemma SpecΓIdentity_app
  statement: SpecΓIdentity.app R = ΓSpecIso R
  proof: rfl

中文:
引理 SpecΓIdentity_app
  结论: SpecΓIdentity.app R = ΓSpecIso R
  证明: rfl
-/
@[simp] lemma SpecΓIdentity_app : SpecΓIdentity.app R = ΓSpecIso R := rfl
/--
lemma `SpecΓIdentity_hom_app` / 引理 `SpecΓIdentity_hom_app`

English:
lemma SpecΓIdentity_hom_app
  statement: SpecΓIdentity.hom.app R = (ΓSpecIso R).hom
  proof: rfl

中文:
引理 SpecΓIdentity_hom_app
  结论: SpecΓIdentity.hom.app R = (ΓSpecIso R).hom
  证明: rfl
-/
@[simp] lemma SpecΓIdentity_hom_app : SpecΓIdentity.hom.app R = (ΓSpecIso R).hom := rfl
/--
lemma `SpecΓIdentity_inv_app` / 引理 `SpecΓIdentity_inv_app`

English:
lemma SpecΓIdentity_inv_app
  statement: SpecΓIdentity.inv.app R = (ΓSpecIso R).inv
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 SpecΓIdentity_inv_app
  结论: SpecΓIdentity.inv.app R = (ΓSpecIso R).inv
  证明: rfl

@[reassoc (attr := simp)]
-/
@[simp] lemma SpecΓIdentity_inv_app : SpecΓIdentity.inv.app R = (ΓSpecIso R).inv := rfl

@[reassoc (attr := simp)]
/--
lemma `ΓSpecIso_naturality` / 引理 `ΓSpecIso_naturality`

English:
lemma ΓSpecIso_naturality
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: SpecΓIdentity.hom.naturality f

中文:
引理 ΓSpecIso_naturality
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  证明: SpecΓIdentity.hom.naturality f

Depends on / 依赖: Identity.hom.naturality, naturality
-/
lemma ΓSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecIso R).hom ≫ f := SpecΓIdentity.hom.naturality f

-- The RHS is not necessarily simpler than the LHS, but this direction coincides with the simp
-- direction of `NatTrans.naturality`.
@[reassoc (attr := simp)]
/--
lemma `ΓSpecIso_inv_naturality` / 引理 `ΓSpecIso_inv_naturality`

English:
lemma ΓSpecIso_inv_naturality
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: SpecΓIdentity.inv.naturality f

中文:
引理 ΓSpecIso_inv_naturality
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  证明: SpecΓIdentity.inv.naturality f

Depends on / 依赖: Identity.inv.naturality, naturality
-/
lemma ΓSpecIso_inv_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv ≫ (Spec.map f).appTop := SpecΓIdentity.inv.naturality f

set_option backward.isDefEq.respectTransparency.types false in
-- This is not marked simp to respect the abstraction
/--
lemma `ΓSpecIso_inv` / 引理 `ΓSpecIso_inv`

English:
lemma ΓSpecIso_inv
  statement: (ΓSpecIso R).inv = CommRingCat.ofHom (algebraMap _ _)
  proof: rfl

中文:
引理 ΓSpecIso_inv
  结论: (ΓSpecIso R).inv = 交换环范畴.ofHom (algebraMap _ _)
  证明: rfl
-/
lemma ΓSpecIso_inv : (ΓSpecIso R).inv = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toOpen_eq` / 引理 `toOpen_eq`

English:
lemma toOpen_eq
  given: (U)
  proof: rfl

中文:
引理 toOpen_eq
  条件: (U)
  证明: rfl
-/
lemma toOpen_eq (U) :
    CommRingCat.ofHom (algebraMap R <| (Spec.structureSheaf R).presheaf.obj (.op U)) =
    (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op := rfl

instance {K} [Field K] : Unique Spec .of K :=
inferInstanceAs Unique (PrimeSpectrum K)

@[simp]
/--
lemma `default_asIdeal` / 引理 `default_asIdeal`

English:
lemma default_asIdeal
  given: {K} [Field K]
  statement: (default : Spec (.of K)).asIdeal = ⊥
  proof: rfl

中文:
引理 default_asIdeal
  条件: {K} [域 K]
  结论: (default : Spec (.of K)).asIdeal = ⊥
  证明: rfl
-/
lemma default_asIdeal {K} [Field K] : (default : Spec (.of K)).asIdeal = ⊥ := rfl

section BasicOpen

variable (X : Scheme) {V U : X.Opens} (f g : Γ(X, U))

/--
Definition of `basicOpen` / `basicOpen` 的定义

English:
definition basicOpen
  signature: : X.Opens
  body: X.toLocallyRingedSpace.toRingedSpace.basicOpen f

中文:
定义 basicOpen
  签名: : X.Opens
  定义体: X.toLocallyRingedSpace.toRingedSpace.basicOpen f

Depends on / 依赖: X.toLocallyRingedSpace.toRingedSpace.basicOpen, basicOpen, toLocallyRingedSpace, toRingedSpace
-/
def basicOpen : X.Opens :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f

/--
theorem `mem_basicOpen` / 定理 `mem_basicOpen`

English:
theorem mem_basicOpen
  given: (x : X) (hx : x in U)
  proof: RingedSpace.mem_basicOpen _ _ _ _

中文:
定理 mem_basicOpen
  条件: (x : X) (hx : x in U)
  证明: RingedSpace.mem_basicOpen _ _ _ _

Depends on / 依赖: RingedSpace, RingedSpace.mem_basicOpen, mem_basicOpen
-/
theorem mem_basicOpen (x : X) (hx : x in U) :
    x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f) :=
  RingedSpace.mem_basicOpen _ _ _ _

/-- A variant of `mem_basicOpen` for bundled `x : U`. -/
@[simp]
/--
theorem `mem_basicOpen'` / 定理 `mem_basicOpen'`

English:
theorem mem_basicOpen'
  given: (x : U)
  statement: ↑x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x x.2 f)
  proof: RingedSpace.mem_basicOpen _ _ _ _

中文:
定理 mem_basicOpen'
  条件: (x : U)
  结论: ↑x in X.basicOpen f ↔ 是单位 (X.presheaf.germ U x x.2 f)
  证明: RingedSpace.mem_basicOpen _ _ _ _

Depends on / 依赖: RingedSpace, RingedSpace.mem_basicOpen, mem_basicOpen
-/
theorem mem_basicOpen' (x : U) : ↑x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x x.2 f) :=
  RingedSpace.mem_basicOpen _ _ _ _

/--
theorem `mem_basicOpen''` / 定理 `mem_basicOpen''`

English:
theorem mem_basicOpen''
  given: {U : X.Opens} (f : Γ(X, U)) (x : X)
  proof: Iff.rfl

中文:
定理 mem_basicOpen''
  条件: {U : X.Opens} (f : Γ(X, U)) (x : X)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_basicOpen'' {U : X.Opens} (f : Γ(X, U)) (x : X) :
    x in X.basicOpen f ↔ exists (m : x in U), IsUnit (X.presheaf.germ U x m f) :=
  Iff.rfl

/--
theorem `mem_basicOpen_top` / 定理 `mem_basicOpen_top`

English:
theorem mem_basicOpen_top
  given: (f : Γ(X, ⊤)) (x : X)
  proof: RingedSpace.mem_top_basicOpen _ f x

@[simp]

中文:
定理 mem_basicOpen_top
  条件: (f : Γ(X, ⊤)) (x : X)
  证明: RingedSpace.mem_top_basicOpen _ f x

@[simp]

Depends on / 依赖: RingedSpace, RingedSpace.mem_top_basicOpen, mem_top_basicOpen
-/
theorem mem_basicOpen_top (f : Γ(X, ⊤)) (x : X) :
    x in X.basicOpen f ↔ IsUnit (X.presheaf.germ ⊤ x trivial f) :=
  RingedSpace.mem_top_basicOpen _ f x

@[simp]
/--
theorem `basicOpen_res` / 定理 `basicOpen_res`

English:
theorem basicOpen_res
  given: (i : op U ⟶ op V)
  statement: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
  proof: RingedSpace.basicOpen_res _ i f

中文:
定理 basicOpen_res
  条件: (i : op U ⟶ op V)
  结论: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
  证明: RingedSpace.basicOpen_res _ i f

Depends on / 依赖: RingedSpace, RingedSpace.basicOpen_res, basicOpen_res
-/
theorem basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f :=
  RingedSpace.basicOpen_res _ i f

-- This should fire before `basicOpen_res`.
@[simp 1100]
/--
theorem `basicOpen_res_eq` / 定理 `basicOpen_res_eq`

English:
theorem basicOpen_res_eq
  given: (i : op U ⟶ op V) [IsIso i]
  proof: RingedSpace.basicOpen_res_eq _ i f

@[sheaf_restrict]

中文:
定理 basicOpen_res_eq
  条件: (i : op U ⟶ op V) [是同构 i]
  证明: RingedSpace.basicOpen_res_eq _ i f

@[sheaf_restrict]

Depends on / 依赖: RingedSpace, RingedSpace.basicOpen_res_eq, basicOpen_res_eq
-/
theorem basicOpen_res_eq (i : op U ⟶ op V) [IsIso i] :
    X.basicOpen (X.presheaf.map i f) = X.basicOpen f :=
  RingedSpace.basicOpen_res_eq _ i f

@[sheaf_restrict]
/--
theorem `basicOpen_le` / 定理 `basicOpen_le`

English:
theorem basicOpen_le
  statement: X.basicOpen f <= U
  proof: RingedSpace.basicOpen_le _ _

@[sheaf_restrict]

中文:
定理 basicOpen_le
  结论: X.basicOpen f <= U
  证明: RingedSpace.basicOpen_le _ _

@[sheaf_restrict]

Depends on / 依赖: RingedSpace, RingedSpace.basicOpen_le, basicOpen_le
-/
theorem basicOpen_le : X.basicOpen f <= U :=
  RingedSpace.basicOpen_le _ _

@[sheaf_restrict]
/--
lemma `basicOpen_restrict` / 引理 `basicOpen_restrict`

English:
lemma basicOpen_restrict
  given: (i : V ⟶ U) (f : Γ(X, U))
  proof: (Scheme.basicOpen_res _ _ _).trans_le inf_le_right

@[simp]

中文:
引理 basicOpen_restrict
  条件: (i : V ⟶ U) (f : Γ(X, U))
  证明: (Scheme.basicOpen_res _ _ _).trans_le inf_le_right

@[simp]

Depends on / 依赖: Scheme, Scheme.basicOpen_res, basicOpen_res, inf_le_right, trans_le
-/
lemma basicOpen_restrict (i : V ⟶ U) (f : Γ(X, U)) :
    X.basicOpen (TopCat.Presheaf.restrict f i) <= X.basicOpen f :=
  (Scheme.basicOpen_res _ _ _).trans_le inf_le_right

@[simp]
/--
theorem `preimage_basicOpen` / 定理 `preimage_basicOpen`

English:
theorem preimage_basicOpen
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U))
  proof: LocallyRingedSpace.preimage_basicOpen f.toLRSHom r

alias Hom.preimage_basicOpen := preimage_basicOpen

中文:
定理 preimage_basicOpen
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U))
  证明: LocallyRingedSpace.preimage_basicOpen f.toLRSHom r

alias Hom.preimage_basicOpen := preimage_basicOpen

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.preimage_basicOpen, f.toLRSHom, preimage_basicOpen, toLRSHom
-/
theorem preimage_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) :
    f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app U r) :=
  LocallyRingedSpace.preimage_basicOpen f.toLRSHom r

alias Hom.preimage_basicOpen := preimage_basicOpen

/--
theorem `preimage_basicOpen_top` / 定理 `preimage_basicOpen_top`

English:
theorem preimage_basicOpen_top
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤))
  proof: preimage_basicOpen ..

alias Hom.preimage_basicOpen_top := preimage_basicOpen_top

中文:
定理 preimage_basicOpen_top
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤))
  证明: preimage_basicOpen ..

alias Hom.preimage_basicOpen_top := preimage_basicOpen_top

Depends on / 依赖: preimage_basicOpen
-/
theorem preimage_basicOpen_top {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.appTop r) :=
  preimage_basicOpen ..

alias Hom.preimage_basicOpen_top := preimage_basicOpen_top

/--
lemma `basicOpen_appLE` / 引理 `basicOpen_appLE`

English:
lemma basicOpen_appLE
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e : U <= f ⁻¹ᵁ V)
  proof: by
  simp only [preimage_basicOpen, Hom.appLE, CommRingCat.comp_apply]
  rw [basicOpen_res]

@[simp]

中文:
引理 basicOpen_appLE
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e : U <= f ⁻¹ᵁ V)
  证明: by
  simp only [preimage_basicOpen, Hom.appLE, CommRingCat.comp_apply]
  rw [basicOpen_res]

@[simp]

Depends on / 依赖: CommRingCat, CommRingCat.comp_apply, Hom.appLE, basicOpen_res, comp_apply, preimage_basicOpen
-/
lemma basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e : U <= f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : X.basicOpen (f.appLE V U e s) = U ⊓ f ⁻¹ᵁ (Y.basicOpen s) := by
  simp only [preimage_basicOpen, Hom.appLE, CommRingCat.comp_apply]
  rw [basicOpen_res]

@[simp]
/--
theorem `basicOpen_zero` / 定理 `basicOpen_zero`

English:
theorem basicOpen_zero
  given: (U : X.Opens)
  statement: X.basicOpen (0 : Γ(X, U)) = ⊥
  proof: LocallyRingedSpace.basicOpen_zero _ U

@[simp]

中文:
定理 basicOpen_zero
  条件: (U : X.Opens)
  结论: X.basicOpen (0 : Γ(X, U)) = ⊥
  证明: LocallyRingedSpace.basicOpen_zero _ U

@[simp]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.basicOpen_zero, basicOpen_zero
-/
theorem basicOpen_zero (U : X.Opens) : X.basicOpen (0 : Γ(X, U)) = ⊥ :=
  LocallyRingedSpace.basicOpen_zero _ U

@[simp]
/--
theorem `basicOpen_mul` / 定理 `basicOpen_mul`

English:
theorem basicOpen_mul
  statement: X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g
  proof: RingedSpace.basicOpen_mul _ _ _

中文:
定理 basicOpen_mul
  结论: X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g
  证明: RingedSpace.basicOpen_mul _ _ _

Depends on / 依赖: RingedSpace, RingedSpace.basicOpen_mul, basicOpen_mul
-/
theorem basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  RingedSpace.basicOpen_mul _ _ _

/--
lemma `basicOpen_pow` / 引理 `basicOpen_pow`

English:
lemma basicOpen_pow
  given: {n : Nat} (h : 0 < n)
  statement: X.basicOpen (f ^ n) = X.basicOpen f
  proof: RingedSpace.basicOpen_pow _ _ _ h

中文:
引理 basicOpen_pow
  条件: {n : 自然数} (h : 0 < n)
  结论: X.basicOpen (f ^ n) = X.basicOpen f
  证明: RingedSpace.basicOpen_pow _ _ _ h

Depends on / 依赖: RingedSpace, RingedSpace.basicOpen_pow, basicOpen_pow
-/
lemma basicOpen_pow {n : Nat} (h : 0 < n) : X.basicOpen (f ^ n) = X.basicOpen f :=
  RingedSpace.basicOpen_pow _ _ _ h

/--
lemma `basicOpen_add_le` / 引理 `basicOpen_add_le`

English:
lemma basicOpen_add_le
  proof: by
  intro x hx
  have hxU : x in U := X.basicOpen_le _ hx
  simp_rw [← SetLike.mem_coe, Opens.coe_sup, Set.mem_union, SetLike.mem_coe] -- TODO : Opens.mem_sup
  simp only [Scheme.mem_basicOpen _ _ _ hxU, map_add] at hx ⊢
  exact IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx

中文:
引理 basicOpen_add_le
  证明: by
  intro x hx
  have hxU : x in U := X.basicOpen_le _ hx
  simp_rw [← SetLike.mem_coe, Opens.coe_sup, Set.mem_union, SetLike.mem_coe] -- TODO : Opens.mem_sup
  simp only [Scheme.mem_basicOpen _ _ _ hxU, map_add] at hx ⊢
  exact IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx

Depends on / 依赖: IsLocalRing, IsLocalRing.isUnit_or_isUnit_of_isUnit_add, Opens.coe_sup, Opens.mem_sup, Scheme, Scheme.mem_basicOpen, Set.mem_union, SetLike, SetLike.mem_coe, X.basicOpen_le, basicOpen_le, coe_sup, isUnit_or_isUnit_of_isUnit_add, map_add, mem_basicOpen, mem_coe, mem_sup, mem_union, simp_rw
-/
lemma basicOpen_add_le :
    X.basicOpen (f + g) <= X.basicOpen f ⊔ X.basicOpen g := by
  intro x hx
  have hxU : x in U := X.basicOpen_le _ hx
  simp_rw [← SetLike.mem_coe, Opens.coe_sup, Set.mem_union, SetLike.mem_coe] -- TODO : Opens.mem_sup
  simp only [Scheme.mem_basicOpen _ _ _ hxU, map_add] at hx ⊢
  exact IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx

/--
theorem `basicOpen_of_isUnit` / 定理 `basicOpen_of_isUnit`

English:
theorem basicOpen_of_isUnit
  given: {f : Γ(X, U)} (hf : IsUnit f)
  statement: X.basicOpen f = U
  proof: RingedSpace.basicOpen_of_isUnit _ hf

@[simp]

中文:
定理 basicOpen_of_isUnit
  条件: {f : Γ(X, U)} (hf : 是单位 f)
  结论: X.basicOpen f = U
  证明: RingedSpace.basicOpen_of_isUnit _ hf

@[simp]

Depends on / 依赖: RingedSpace, RingedSpace.basicOpen_of_isUnit, basicOpen_of_isUnit
-/
theorem basicOpen_of_isUnit {f : Γ(X, U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpace.basicOpen_of_isUnit _ hf

@[simp]
/--
theorem `basicOpen_one` / 定理 `basicOpen_one`

English:
theorem basicOpen_one
  statement: X.basicOpen (1 : Γ(X, U)) = U
  proof: X.basicOpen_of_isUnit isUnit_one

中文:
定理 basicOpen_one
  结论: X.basicOpen (1 : Γ(X, U)) = U
  证明: X.basicOpen_of_isUnit isUnit_one

Depends on / 依赖: X.basicOpen_of_isUnit, basicOpen_of_isUnit, isUnit_one
-/
theorem basicOpen_one : X.basicOpen (1 : Γ(X, U)) = U :=
  X.basicOpen_of_isUnit isUnit_one

/--
Instance `algebra_section_section_basicOpen` / 实例 `algebra_section_section_basicOpen`

English:
instance algebra_section_section_basicOpen
  signature: {X : Scheme} {U : X.Opens} (f : Γ(X, U))
  body: (X.presheaf.map (homOfLE <| X.basicOpen_le f : _ ⟶ U).op).hom.toAlgebra

@[simp]

中文:
实例 algebra_section_section_basicOpen
  签名: {X : 概形} {U : X.Opens} (f : Γ(X, U))
  定义体: (X.presheaf.map (homOfLE <| X.basicOpen_le f : _ ⟶ U).op).hom.toAlgebra

@[simp]

Depends on / 依赖: X.basicOpen_le, X.presheaf.map, basicOpen_le, hom.toAlgebra, homOfLE, presheaf, toAlgebra
-/
instance algebra_section_section_basicOpen {X : Scheme} {U : X.Opens} (f : Γ(X, U)) :
    Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
  (X.presheaf.map (homOfLE <| X.basicOpen_le f : _ ⟶ U).op).hom.toAlgebra

@[simp]
/--
lemma `_root_.AlgebraicGeometry.SpecMap_preimage_basicOpen` / 引理 `_root_.AlgebraicGeometry.SpecMap_preimage_basicOpen`

English:
lemma _root_.AlgebraicGeometry.SpecMap_preimage_basicOpen
  given: {R S : CommRingCat} (f : R ⟶ S) (r : R)
  proof: rfl

中文:
引理 _root_.AlgebraicGeometry.SpecMap_preimage_basicOpen
  条件: {R S : 交换环范畴} (f : R ⟶ S) (r : R)
  证明: rfl
-/
lemma _root_.AlgebraicGeometry.SpecMap_preimage_basicOpen {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    Spec.map f ⁻¹ᵁ PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen (f r) := rfl

end BasicOpen

section ZeroLocus

variable (X : Scheme.{u})

/--
Definition of `zeroLocus` / `zeroLocus` 的定义

English:
definition zeroLocus
  signature: {U : X.Opens} (s : Set Γ(X, U))
  body: X.toRingedSpace.zeroLocus s

中文:
定义 zeroLocus
  签名: {U : X.Opens} (s : 集合 Γ(X, U))
  定义体: X.toRingedSpace.zeroLocus s

Depends on / 依赖: X.toRingedSpace.zeroLocus, toRingedSpace, zeroLocus
-/
def zeroLocus {U : X.Opens} (s : Set Γ(X, U)) : Set X := X.toRingedSpace.zeroLocus s

/--
lemma `zeroLocus_def` / 引理 `zeroLocus_def`

English:
lemma zeroLocus_def
  given: {U : X.Opens} (s : Set Γ(X, U))
  proof: rfl

中文:
引理 zeroLocus_def
  条件: {U : X.Opens} (s : 集合 Γ(X, U))
  证明: rfl
-/
lemma zeroLocus_def {U : X.Opens} (s : Set Γ(X, U)) :
    X.zeroLocus s = ⋂ f in s, (X.basicOpen f).carrierᶜ :=
  rfl

/--
lemma `zeroLocus_isClosed` / 引理 `zeroLocus_isClosed`

English:
lemma zeroLocus_isClosed
  given: {U : X.Opens} (s : Set Γ(X, U))
  proof: X.toRingedSpace.zeroLocus_isClosed s

中文:
引理 zeroLocus_isClosed
  条件: {U : X.Opens} (s : 集合 Γ(X, U))
  证明: X.toRingedSpace.zeroLocus_isClosed s

Depends on / 依赖: X.toRingedSpace.zeroLocus_isClosed, toRingedSpace, zeroLocus_isClosed
-/
lemma zeroLocus_isClosed {U : X.Opens} (s : Set Γ(X, U)) :
    IsClosed (X.zeroLocus s) :=
  X.toRingedSpace.zeroLocus_isClosed s

/--
lemma `zeroLocus_singleton` / 引理 `zeroLocus_singleton`

English:
lemma zeroLocus_singleton
  given: {U : X.Opens} (f : Γ(X, U))
  proof: X.toRingedSpace.zeroLocus_singleton f

@[simp]

中文:
引理 zeroLocus_singleton
  条件: {U : X.Opens} (f : Γ(X, U))
  证明: X.toRingedSpace.zeroLocus_singleton f

@[simp]

Depends on / 依赖: X.toRingedSpace.zeroLocus_singleton, toRingedSpace, zeroLocus_singleton
-/
lemma zeroLocus_singleton {U : X.Opens} (f : Γ(X, U)) :
    X.zeroLocus {f} = (↑(X.basicOpen f))ᶜ :=
  X.toRingedSpace.zeroLocus_singleton f

@[simp]
/--
lemma `zeroLocus_empty_eq_univ` / 引理 `zeroLocus_empty_eq_univ`

English:
lemma zeroLocus_empty_eq_univ
  given: {U : X.Opens}
  proof: X.toRingedSpace.zeroLocus_empty_eq_univ

@[simp]

中文:
引理 zeroLocus_empty_eq_univ
  条件: {U : X.Opens}
  证明: X.toRingedSpace.zeroLocus_empty_eq_univ

@[simp]

Depends on / 依赖: X.toRingedSpace.zeroLocus_empty_eq_univ, toRingedSpace, zeroLocus_empty_eq_univ
-/
lemma zeroLocus_empty_eq_univ {U : X.Opens} :
    X.zeroLocus (∅ : Set Γ(X, U)) = Set.univ :=
  X.toRingedSpace.zeroLocus_empty_eq_univ

@[simp]
/--
lemma `mem_zeroLocus_iff` / 引理 `mem_zeroLocus_iff`

English:
lemma mem_zeroLocus_iff
  given: {U : X.Opens} (s : Set Γ(X, U)) (x : X)
  proof: X.toRingedSpace.mem_zeroLocus_iff s x

中文:
引理 mem_zeroLocus_iff
  条件: {U : X.Opens} (s : 集合 Γ(X, U)) (x : X)
  证明: X.toRingedSpace.mem_zeroLocus_iff s x

Depends on / 依赖: X.toRingedSpace.mem_zeroLocus_iff, mem_zeroLocus_iff, toRingedSpace
-/
lemma mem_zeroLocus_iff {U : X.Opens} (s : Set Γ(X, U)) (x : X) :
    x in X.zeroLocus s ↔ forall f in s, x ∉ X.basicOpen f :=
  X.toRingedSpace.mem_zeroLocus_iff s x

/--
lemma `codisjoint_zeroLocus` / 引理 `codisjoint_zeroLocus`

English:
lemma codisjoint_zeroLocus
  statement: {U : X.Opens}
  proof: by
  have (x : X) : forall f in s, x in X.basicOpen f -> x in U := fun _ _ h => X.basicOpen_le _ h
  simpa [codisjoint_iff_le_sup, Set.ext_iff, or_iff_not_imp_left]

中文:
引理 codisjoint_zeroLocus
  结论: {U : X.Opens}
  证明: by
  have (x : X) : forall f in s, x in X.basicOpen f -> x in U := fun _ _ h => X.basicOpen_le _ h
  simpa [codisjoint_iff_le_sup, Set.ext_iff, or_iff_not_imp_left]

Depends on / 依赖: Set.ext_iff, X.basicOpen, X.basicOpen_le, basicOpen, basicOpen_le, codisjoint_iff_le_sup, ext_iff, or_iff_not_imp_left
-/
lemma codisjoint_zeroLocus {U : X.Opens}
    (s : Set Γ(X, U)) : Codisjoint (X.zeroLocus s) U := by
  have (x : X) : forall f in s, x in X.basicOpen f -> x in U := fun _ _ h => X.basicOpen_le _ h
  simpa [codisjoint_iff_le_sup, Set.ext_iff, or_iff_not_imp_left]

/--
lemma `zeroLocus_span` / 引理 `zeroLocus_span`

English:
lemma zeroLocus_span
  given: {U : X.Opens} (s : Set Γ(X, U))
  proof: by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  refine ⟨fun H f hfs => H f (Ideal.subset_span hfs), fun H f => Submodule.span_induction H ?_ ?_ ?_⟩
  · simp only [Scheme.basicOpen_zero]; exact not_false
  · exact fun a b _ _ ha hb H => (X.basicOpen_add_le a b H).elim ha hb
  · s

中文:
引理 zeroLocus_span
  条件: {U : X.Opens} (s : 集合 Γ(X, U))
  证明: by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  refine ⟨fun H f hfs => H f (Ideal.subset_span hfs), fun H f => Submodule.span_induction H ?_ ?_ ?_⟩
  · simp only [Scheme.basicOpen_zero]; exact not_false
  · exact fun a b _ _ ha hb H => (X.basicOpen_add_le a b H).elim ha hb
  · s

Depends on / 依赖: Ideal.span, Ideal.subset_span, Scheme, Scheme.basicOpen_zero, Scheme.mem_zeroLocus_iff, SetLike, SetLike.mem_coe, Submodule, Submodule.span_induction, X.basicOpen_add_le, X.zeroLocus, basicOpen_add_le, basicOpen_zero, contextual, mem_coe, mem_zeroLocus_iff, not_false, span_induction, subset_span, zeroLocus
-/
lemma zeroLocus_span {U : X.Opens} (s : Set Γ(X, U)) :
    X.zeroLocus (U := U) (Ideal.span s) = X.zeroLocus s := by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  refine ⟨fun H f hfs => H f (Ideal.subset_span hfs), fun H f => Submodule.span_induction H ?_ ?_ ?_⟩
  · simp only [Scheme.basicOpen_zero]; exact not_false
  · exact fun a b _ _ ha hb H => (X.basicOpen_add_le a b H).elim ha hb
  · simp +contextual

open scoped Pointwise in
/--
lemma `zeroLocus_setMul` / 引理 `zeroLocus_setMul`

English:
lemma zeroLocus_setMul
  given: {U : X.Opens} (s t : Set Γ(X, U))
  proof: by
  simp only [← Set.image2_mul, zeroLocus_def, Set.biInter_image2]
  simp [Set.compl_inter, ← Set.union_iInter₂, ← Set.iInter₂_union]

中文:
引理 zeroLocus_setMul
  条件: {U : X.Opens} (s t : 集合 Γ(X, U))
  证明: by
  simp only [← Set.image2_mul, zeroLocus_def, Set.biInter_image2]
  simp [Set.compl_inter, ← Set.union_iInter₂, ← Set.iInter₂_union]

Depends on / 依赖: Set.biInter_image2, Set.compl_inter, Set.iInter, Set.image2_mul, Set.union_iInter, biInter_image2, compl_inter, image2_mul, zeroLocus_def
-/
lemma zeroLocus_setMul {U : X.Opens} (s t : Set Γ(X, U)) :
    X.zeroLocus (s * t) = X.zeroLocus s union X.zeroLocus t := by
  simp only [← Set.image2_mul, zeroLocus_def, Set.biInter_image2]
  simp [Set.compl_inter, ← Set.union_iInter₂, ← Set.iInter₂_union]

open scoped Pointwise in
/--
lemma `zeroLocus_mul` / 引理 `zeroLocus_mul`

English:
lemma zeroLocus_mul
  given: {U : X.Opens} (I J : Ideal Γ(X, U))
  proof: by
  rw [← X.zeroLocus_setMul]; rw [← X.zeroLocus_span (U := U) (↑I * ↑J)]; rw [← Ideal.span_mul_span]
  simp

中文:
引理 zeroLocus_mul
  条件: {U : X.Opens} (I J : 理想 Γ(X, U))
  证明: by
  rw [← X.zeroLocus_setMul]; rw [← X.zeroLocus_span (U := U) (↑I * ↑J)]; rw [← Ideal.span_mul_span]
  simp

Depends on / 依赖: Ideal.span_mul_span, X.zeroLocus, X.zeroLocus_setMul, X.zeroLocus_span, span_mul_span, zeroLocus, zeroLocus_setMul, zeroLocus_span
-/
lemma zeroLocus_mul {U : X.Opens} (I J : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) ↑(I * J) = X.zeroLocus (U := U) I union X.zeroLocus (U := U) J := by
  rw [← X.zeroLocus_setMul]; rw [← X.zeroLocus_span (U := U) (↑I * ↑J)]; rw [← Ideal.span_mul_span]
  simp

/--
lemma `zeroLocus_map` / 引理 `zeroLocus_map`

English:
lemma zeroLocus_map
  given: {U V : X.Opens} (i : U <= V) (s : Set Γ(X, V))
  proof: by
  ext x
  suffices (forall f in s, x in U -> x ∉ X.basicOpen f) ↔ x in U -> (forall f in s, x ∉ X.basicOpen f) by
    simpa [or_iff_not_imp_right]
  grind

中文:
引理 zeroLocus_map
  条件: {U V : X.Opens} (i : U <= V) (s : 集合 Γ(X, V))
  证明: by
  ext x
  suffices (forall f in s, x in U -> x ∉ X.basicOpen f) ↔ x in U -> (forall f in s, x ∉ X.basicOpen f) by
    simpa [or_iff_not_imp_right]
  grind

Depends on / 依赖: X.basicOpen, basicOpen, or_iff_not_imp_right
-/
lemma zeroLocus_map {U V : X.Opens} (i : U <= V) (s : Set Γ(X, V)) :
    X.zeroLocus ((X.presheaf.map (homOfLE i).op).hom '' s) = X.zeroLocus s union Uᶜ := by
  ext x
  suffices (forall f in s, x in U -> x ∉ X.basicOpen f) ↔ x in U -> (forall f in s, x ∉ X.basicOpen f) by
    simpa [or_iff_not_imp_right]
  grind

/--
lemma `zeroLocus_map_of_eq` / 引理 `zeroLocus_map_of_eq`

English:
lemma zeroLocus_map_of_eq
  given: {U V : X.Opens} (i : U = V) (s : Set Γ(X, V))
  proof: by
  ext; simp

中文:
引理 zeroLocus_map_of_eq
  条件: {U V : X.Opens} (i : U = V) (s : 集合 Γ(X, V))
  证明: by
  ext; simp
-/
lemma zeroLocus_map_of_eq {U V : X.Opens} (i : U = V) (s : Set Γ(X, V)) :
    X.zeroLocus ((X.presheaf.map (eqToHom i).op).hom '' s) = X.zeroLocus s := by
  ext; simp

/--
lemma `zeroLocus_mono` / 引理 `zeroLocus_mono`

English:
lemma zeroLocus_mono
  given: {U : X.Opens} {s t : Set Γ(X, U)} (h : s subseteq t)
  proof: by
  simp only [Set.subset_def, Scheme.mem_zeroLocus_iff]
  exact fun x H f hf hxf => H f (h hf) hxf

中文:
引理 zeroLocus_mono
  条件: {U : X.Opens} {s t : 集合 Γ(X, U)} (h : s subseteq t)
  证明: by
  simp only [Set.subset_def, Scheme.mem_zeroLocus_iff]
  exact fun x H f hf hxf => H f (h hf) hxf

Depends on / 依赖: Scheme, Scheme.mem_zeroLocus_iff, Set.subset_def, mem_zeroLocus_iff, subset_def
-/
lemma zeroLocus_mono {U : X.Opens} {s t : Set Γ(X, U)} (h : s subseteq t) :
    X.zeroLocus t subseteq X.zeroLocus s := by
  simp only [Set.subset_def, Scheme.mem_zeroLocus_iff]
  exact fun x H f hf hxf => H f (h hf) hxf

/--
lemma `preimage_zeroLocus` / 引理 `preimage_zeroLocus`

English:
lemma preimage_zeroLocus
  given: {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (s : Set Γ(Y, U))
  proof: by
  ext
  simp [← Scheme.preimage_basicOpen]

@[simp]

中文:
引理 preimage_zeroLocus
  条件: {X Y : 概形.{u}} (f : X ⟶ Y) {U : Y.Opens} (s : 集合 Γ(Y, U))
  证明: by
  ext
  simp [← Scheme.preimage_basicOpen]

@[simp]

Depends on / 依赖: Scheme, Scheme.preimage_basicOpen, preimage_basicOpen
-/
lemma preimage_zeroLocus {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (s : Set Γ(Y, U)) :
    f ⁻¹' Y.zeroLocus s = X.zeroLocus ((f.app U).hom '' s) := by
  ext
  simp [← Scheme.preimage_basicOpen]

@[simp]
/--
lemma `zeroLocus_univ` / 引理 `zeroLocus_univ`

English:
lemma zeroLocus_univ
  given: {U : X.Opens}
  proof: by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, Set.mem_univ, forall_const, Set.mem_compl_iff,
    SetLike.mem_coe, ← not_exists, not_iff_not]
  exact ⟨fun ⟨f, hf⟩ => X.basicOpen_le f hf, fun _ => ⟨1, by rwa [X.basicOpen_of_isUnit isUnit_one]⟩⟩

中文:
引理 zeroLocus_univ
  条件: {U : X.Opens}
  证明: by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, Set.mem_univ, forall_const, Set.mem_compl_iff,
    SetLike.mem_coe, ← not_exists, not_iff_not]
  exact ⟨fun ⟨f, hf⟩ => X.basicOpen_le f hf, fun _ => ⟨1, by rwa [X.basicOpen_of_isUnit isUnit_one]⟩⟩

Depends on / 依赖: Scheme, Scheme.mem_zeroLocus_iff, Set.mem_compl_iff, Set.mem_univ, Set.univ, SetLike, SetLike.mem_coe, X.basicOpen_le, X.basicOpen_of_isUnit, basicOpen_le, basicOpen_of_isUnit, forall_const, isUnit_one, mem_coe, mem_compl_iff, mem_univ, mem_zeroLocus_iff, not_exists, not_iff_not
-/
lemma zeroLocus_univ {U : X.Opens} :
    X.zeroLocus (U := U) Set.univ = (↑U)ᶜ := by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, Set.mem_univ, forall_const, Set.mem_compl_iff,
    SetLike.mem_coe, ← not_exists, not_iff_not]
  exact ⟨fun ⟨f, hf⟩ => X.basicOpen_le f hf, fun _ => ⟨1, by rwa [X.basicOpen_of_isUnit isUnit_one]⟩⟩

/--
lemma `zeroLocus_iUnion` / 引理 `zeroLocus_iUnion`

English:
lemma zeroLocus_iUnion
  given: {U : X.Opens} {ι : Type*} (f : ι -> Set Γ(X, U))
  proof: by
  simpa [zeroLocus, AlgebraicGeometry.RingedSpace.zeroLocus] using Set.iInter_comm _

中文:
引理 zeroLocus_iUnion
  条件: {U : X.Opens} {ι : 类型} (f : ι -> 集合 Γ(X, U))
  证明: by
  simpa [zeroLocus, AlgebraicGeometry.RingedSpace.zeroLocus] using Set.iInter_comm _

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.RingedSpace.zeroLocus, RingedSpace, Set.iInter_comm, iInter_comm, zeroLocus
-/
lemma zeroLocus_iUnion {U : X.Opens} {ι : Type*} (f : ι -> Set Γ(X, U)) :
    X.zeroLocus (⋃ i, f i) = ⋂ i, X.zeroLocus (f i) := by
  simpa [zeroLocus, AlgebraicGeometry.RingedSpace.zeroLocus] using Set.iInter_comm _

/--
lemma `zeroLocus_radical` / 引理 `zeroLocus_radical`

English:
lemma zeroLocus_radical
  given: {U : X.Opens} (I : Ideal Γ(X, U))
  proof: by
  refine (X.zeroLocus_mono I.le_radical).antisymm ?_
  simp only [Set.subset_def, mem_zeroLocus_iff, SetLike.mem_coe]
  rintro x H f ⟨n, hn⟩ hx
  rcases n.eq_zero_or_pos with rfl | hn'
  · exact H f (by simpa using I.mul_mem_left f hn) hx
  · exact H _ hn (X.basicOpen_pow f hn' ▸ hx)

中文:
引理 zeroLocus_radical
  条件: {U : X.Opens} (I : 理想 Γ(X, U))
  证明: by
  refine (X.zeroLocus_mono I.le_radical).antisymm ?_
  simp only [Set.subset_def, mem_zeroLocus_iff, SetLike.mem_coe]
  rintro x H f ⟨n, hn⟩ hx
  rcases n.eq_zero_or_pos with rfl | hn'
  · exact H f (by simpa using I.mul_mem_left f hn) hx
  · exact H _ hn (X.basicOpen_pow f hn' ▸ hx)

Depends on / 依赖: I.le_radical, I.mul_mem_left, I.radical, Set.subset_def, SetLike, SetLike.mem_coe, X.basicOpen_pow, X.zeroLocus, X.zeroLocus_mono, antisymm, basicOpen_pow, eq_zero_or_pos, le_radical, mem_coe, mem_zeroLocus_iff, mul_mem_left, n.eq_zero_or_pos, radical, subset_def, zeroLocus
-/
lemma zeroLocus_radical {U : X.Opens} (I : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) I.radical = X.zeroLocus (U := U) I := by
  refine (X.zeroLocus_mono I.le_radical).antisymm ?_
  simp only [Set.subset_def, mem_zeroLocus_iff, SetLike.mem_coe]
  rintro x H f ⟨n, hn⟩ hx
  rcases n.eq_zero_or_pos with rfl | hn'
  · exact H f (by simpa using I.mul_mem_left f hn) hx
  · exact H _ hn (X.basicOpen_pow f hn' ▸ hx)

end ZeroLocus

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `basicOpen_eq_of_affine` / 定理 `basicOpen_eq_of_affine`

English:
theorem basicOpen_eq_of_affine
  given: {R : CommRingCat} (f : R)
  proof: by
  ext x
  simp only [SetLike.mem_coe, Scheme.mem_basicOpen_top]
  suffices IsUnit (algebraMap _ ((structurePresheafInCommRingCat ↑R).stalk x) f) ↔
    f ∉ PrimeSpectrum.asIdeal x by exact this
  rw [← isUnit_map_iff (StructureSheaf.stalkIso R x).symm]; rw [AlgEquiv.commutes]
  exact IsLocalizatio

中文:
定理 basicOpen_eq_of_affine
  条件: {R : 交换环范畴} (f : R)
  证明: by
  ext x
  simp only [SetLike.mem_coe, Scheme.mem_basicOpen_top]
  suffices IsUnit (algebraMap _ ((structurePresheafInCommRingCat ↑R).stalk x) f) ↔
    f ∉ PrimeSpectrum.asIdeal x by exact this
  rw [← isUnit_map_iff (StructureSheaf.stalkIso R x).symm]; rw [AlgEquiv.commutes]
  exact IsLocalizatio

Depends on / 依赖: AlgEquiv, AlgEquiv.commutes, AtPrime, IsLocalization, IsLocalization.AtPrime.isUnit_to_map_iff, IsUnit, PrimeSpectrum, PrimeSpectrum.asIdeal, Scheme, Scheme.mem_basicOpen_top, SetLike, SetLike.mem_coe, StructureSheaf, StructureSheaf.stalkIso, algebraMap, asIdeal, commutes, isUnit_map_iff, isUnit_to_map_iff, mem_basicOpen_top
-/
theorem basicOpen_eq_of_affine {R : CommRingCat} (f : R) :
    (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpectrum.basicOpen f := by
  ext x
  simp only [SetLike.mem_coe, Scheme.mem_basicOpen_top]
  suffices IsUnit (algebraMap _ ((structurePresheafInCommRingCat ↑R).stalk x) f) ↔
    f ∉ PrimeSpectrum.asIdeal x by exact this
  rw [← isUnit_map_iff (StructureSheaf.stalkIso R x).symm]; rw [AlgEquiv.commutes]
  exact IsLocalization.AtPrime.isUnit_to_map_iff _ (PrimeSpectrum.asIdeal x) f

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `basicOpen_eq_of_affine'` / 定理 `basicOpen_eq_of_affine'`

English:
theorem basicOpen_eq_of_affine'
  given: {R : CommRingCat} (f : Γ(Spec R, ⊤))
  proof: by
  convert! basicOpen_eq_of_affine ((Scheme.ΓSpecIso R).hom f)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) f).symm

中文:
定理 basicOpen_eq_of_affine'
  条件: {R : 交换环范畴} (f : Γ(Spec R, ⊤))
  证明: by
  convert! basicOpen_eq_of_affine ((Scheme.ΓSpecIso R).hom f)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) f).symm

Depends on / 依赖: Iso.hom_inv_id_apply, Scheme, basicOpen_eq_of_affine, convert, hom_inv_id_apply
-/
theorem basicOpen_eq_of_affine' {R : CommRingCat} (f : Γ(Spec R, ⊤)) :
    (Spec R).basicOpen f = PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso R).hom f) := by
  convert! basicOpen_eq_of_affine ((Scheme.ΓSpecIso R).hom f)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) f).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Scheme.SpecMap_presheaf_map_eqToHom` / 定理 `Scheme.SpecMap_presheaf_map_eqToHom`

English:
theorem Scheme.SpecMap_presheaf_map_eqToHom
  given: {X : Scheme} {U V : X.Opens} (h : U = V) (W)
  proof: by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id]; rw [op_id]; rw [Scheme.Spec.map_id]
  cases h
  refine (Scheme.Hom.congr_app this _).trans ?_
  simp [eqToHom_map]

中文:
定理 概形.SpecMap_presheaf_map_eqToHom
  条件: {X : 概形} {U V : X.Opens} (h : U = V) (W)
  证明: by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id]; rw [op_id]; rw [Scheme.Spec.map_id]
  cases h
  refine (Scheme.Hom.congr_app this _).trans ?_
  simp [eqToHom_map]

Depends on / 依赖: Scheme, Scheme.Hom.congr_app, Scheme.Spec.map, Scheme.Spec.map_id, X.presheaf.map, X.presheaf.map_id, congr_app, eqToHom_map, map_id, op_id, presheaf
-/
theorem Scheme.SpecMap_presheaf_map_eqToHom {X : Scheme} {U V : X.Opens} (h : U = V) (W) :
    (Spec.map (X.presheaf.map (eqToHom h).op)).app W = eqToHom (by cases h; simp) := by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id]; rw [op_id]; rw [Scheme.Spec.map_id]
  cases h
  refine (Scheme.Hom.congr_app this _).trans ?_
  simp [eqToHom_map]

/--
lemma `germ_eq_zero_of_pow_mul_eq_zero` / 引理 `germ_eq_zero_of_pow_mul_eq_zero`

English:
lemma germ_eq_zero_of_pow_mul_eq_zero
  statement: {X : Scheme.{u}} {U : Opens X} (x : U) {f s : Γ(X, U)}
  proof: by
  rw [Scheme.mem_basicOpen X s x x.2] at hx
  have hu : IsUnit (X.presheaf.germ _ x x.2 (s ^ n)) := by
    rw [map_pow]
    exact IsUnit.pow n hx
  rw [← hu.mul_right_eq_zero]; rw [← map_mul]; rw [hf]; rw [map_zero]

@[reassoc (attr := simp)]

中文:
引理 germ_eq_zero_of_pow_mul_eq_zero
  结论: {X : 概形.{u}} {U : Opens X} (x : U) {f s : Γ(X, U)}
  证明: by
  rw [Scheme.mem_basicOpen X s x x.2] at hx
  have hu : IsUnit (X.presheaf.germ _ x x.2 (s ^ n)) := by
    rw [map_pow]
    exact IsUnit.pow n hx
  rw [← hu.mul_right_eq_zero]; rw [← map_mul]; rw [hf]; rw [map_zero]

@[reassoc (attr := simp)]

Depends on / 依赖: IsUnit, IsUnit.pow, Scheme, Scheme.mem_basicOpen, X.presheaf.germ, hu.mul_right_eq_zero, map_mul, map_pow, map_zero, mem_basicOpen, mul_right_eq_zero, presheaf
-/
lemma germ_eq_zero_of_pow_mul_eq_zero {X : Scheme.{u}} {U : Opens X} (x : U) {f s : Γ(X, U)}
    (hx : x.val in X.basicOpen s) {n : Nat} (hf : s ^ n * f = 0) : X.presheaf.germ U x x.2 f = 0 := by
  rw [Scheme.mem_basicOpen X s x x.2] at hx
  have hu : IsUnit (X.presheaf.germ _ x x.2 (s ^ n)) := by
    rw [map_pow]
    exact IsUnit.pow n hx
  rw [← hu.mul_right_eq_zero]; rw [← map_mul]; rw [hf]; rw [map_zero]

@[reassoc (attr := simp)]
/--
lemma `Scheme.hom_base_inv_base` / 引理 `Scheme.hom_base_inv_base`

English:
lemma Scheme.hom_base_inv_base
  given: {X Y : Scheme.{u}} (e : X ≅ Y)
  proof: LocallyRingedSpace.iso_hom_base_inv_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]

中文:
引理 概形.hom_base_inv_base
  条件: {X Y : 概形.{u}} (e : X ≅ Y)
  证明: LocallyRingedSpace.iso_hom_base_inv_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.iso_hom_base_inv_base, Scheme, Scheme.forgetToLocallyRingedSpace.mapIso, forgetToLocallyRingedSpace, iso_hom_base_inv_base, mapIso
-/
lemma Scheme.hom_base_inv_base {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.hom.base ≫ e.inv.base = 𝟙 _ :=
  LocallyRingedSpace.iso_hom_base_inv_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]
/--
lemma `Scheme.hom_inv_apply` / 引理 `Scheme.hom_inv_apply`

English:
lemma Scheme.hom_inv_apply
  given: {X Y : Scheme.{u}} (e : X ≅ Y) (x : X)
  proof: by
  change (e.hom ≫ e.inv) x = 𝟙 X.toPresheafedSpace x
  simp

@[reassoc (attr := simp)]

中文:
引理 概形.hom_inv_apply
  条件: {X Y : 概形.{u}} (e : X ≅ Y) (x : X)
  证明: by
  change (e.hom ≫ e.inv) x = 𝟙 X.toPresheafedSpace x
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: X.toPresheafedSpace, e.hom, e.inv, toPresheafedSpace
-/
lemma Scheme.hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    e.inv (e.hom x) = x := by
  change (e.hom ≫ e.inv) x = 𝟙 X.toPresheafedSpace x
  simp

@[reassoc (attr := simp)]
/--
lemma `Scheme.inv_base_hom_base` / 引理 `Scheme.inv_base_hom_base`

English:
lemma Scheme.inv_base_hom_base
  given: {X Y : Scheme.{u}} (e : X ≅ Y)
  proof: LocallyRingedSpace.iso_inv_base_hom_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]

中文:
引理 概形.inv_base_hom_base
  条件: {X Y : 概形.{u}} (e : X ≅ Y)
  证明: LocallyRingedSpace.iso_inv_base_hom_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.iso_inv_base_hom_base, Scheme, Scheme.forgetToLocallyRingedSpace.mapIso, forgetToLocallyRingedSpace, iso_inv_base_hom_base, mapIso
-/
lemma Scheme.inv_base_hom_base {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.inv.base ≫ e.hom.base = 𝟙 _ :=
  LocallyRingedSpace.iso_inv_base_hom_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]
/--
lemma `Scheme.inv_hom_apply` / 引理 `Scheme.inv_hom_apply`

English:
lemma Scheme.inv_hom_apply
  given: {X Y : Scheme.{u}} (e : X ≅ Y) (y : Y)
  proof: by
  change (e.inv ≫ e.hom) y = 𝟙 Y.toPresheafedSpace y
  simp

中文:
引理 概形.inv_hom_apply
  条件: {X Y : 概形.{u}} (e : X ≅ Y) (y : Y)
  证明: by
  change (e.inv ≫ e.hom) y = 𝟙 Y.toPresheafedSpace y
  simp

Depends on / 依赖: Y.toPresheafedSpace, e.hom, e.inv, toPresheafedSpace
-/
lemma Scheme.inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (y : Y) :
    e.hom (e.inv y) = y := by
  change (e.inv ≫ e.hom) y = 𝟙 Y.toPresheafedSpace y
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Spec_zeroLocus_eq_zeroLocus` / 定理 `Spec_zeroLocus_eq_zeroLocus`

English:
theorem Spec_zeroLocus_eq_zeroLocus
  given: {R : CommRingCat} (s : Set R)
  proof: by
  ext x
  suffices (forall a in s, x ∉ PrimeSpectrum.basicOpen a) ↔ x in PrimeSpectrum.zeroLocus s by simpa
  simp [Spec_carrier, PrimeSpectrum.mem_zeroLocus, Set.subset_def,
    PrimeSpectrum.mem_basicOpen _ x]

中文:
定理 Spec_zeroLocus_eq_zeroLocus
  条件: {R : 交换环范畴} (s : 集合 R)
  证明: by
  ext x
  suffices (forall a in s, x ∉ PrimeSpectrum.basicOpen a) ↔ x in PrimeSpectrum.zeroLocus s by simpa
  simp [Spec_carrier, PrimeSpectrum.mem_zeroLocus, Set.subset_def,
    PrimeSpectrum.mem_basicOpen _ x]

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.basicOpen, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.zeroLocus, Set.subset_def, Spec_carrier, basicOpen, mem_basicOpen, mem_zeroLocus, subset_def, zeroLocus
-/
theorem Spec_zeroLocus_eq_zeroLocus {R : CommRingCat} (s : Set R) :
    (Spec R).zeroLocus ((Scheme.ΓSpecIso R).inv '' s) = PrimeSpectrum.zeroLocus s := by
  ext x
  suffices (forall a in s, x ∉ PrimeSpectrum.basicOpen a) ↔ x in PrimeSpectrum.zeroLocus s by simpa
  simp [Spec_carrier, PrimeSpectrum.mem_zeroLocus, Set.subset_def,
    PrimeSpectrum.mem_basicOpen _ x]

/--
theorem `Spec_zeroLocus` / 定理 `Spec_zeroLocus`

English:
theorem Spec_zeroLocus
  given: {R : CommRingCat} (s : Set Γ(Spec R, ⊤))
  proof: by
  convert! Spec_zeroLocus_eq_zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s)
  rw [Set.image_preimage_eq]
  exact (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).2

中文:
定理 Spec_zeroLocus
  条件: {R : 交换环范畴} (s : 集合 Γ(Spec R, ⊤))
  证明: by
  convert! Spec_zeroLocus_eq_zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s)
  rw [Set.image_preimage_eq]
  exact (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).2

Depends on / 依赖: CommRingCat, ConcreteCategory, ConcreteCategory.bijective_of_isIso, Scheme, Set.image_preimage_eq, Spec_zeroLocus_eq_zeroLocus, bijective_of_isIso, convert, image_preimage_eq
-/
theorem Spec_zeroLocus {R : CommRingCat} (s : Set Γ(Spec R, ⊤)) :
    (Spec R).zeroLocus s = PrimeSpectrum.zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s) := by
  convert! Spec_zeroLocus_eq_zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s)
  rw [Set.image_preimage_eq]
  exact (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).2
section Stalks

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (x) : IsLocalHom (f.stalkMap x).hom :=
  f.prop x

@[simp]
/--
lemma `stalkMap_id` / 引理 `stalkMap_id`

English:
lemma stalkMap_id
  given: (X : Scheme.{u}) (x : X)
  proof: PresheafedSpace.stalkMap.id _ x

中文:
引理 stalkMap_id
  条件: (X : 概形.{u}) (x : X)
  证明: PresheafedSpace.stalkMap.id _ x

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap.id, stalkMap
-/
lemma stalkMap_id (X : Scheme.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  PresheafedSpace.stalkMap.id _ x

/--
lemma `stalkMap_comp` / 引理 `stalkMap_comp`

English:
lemma stalkMap_comp
  given: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: PresheafedSpace.stalkMap.comp f.toPshHom g.toPshHom x

@[reassoc]

中文:
引理 stalkMap_comp
  条件: {X Y Z : 概形.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: PresheafedSpace.stalkMap.comp f.toPshHom g.toPshHom x

@[reassoc]

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap.comp, f.toPshHom, g.toPshHom, stalkMap, toPshHom
-/
lemma stalkMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f x) ≫ f.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.toPshHom g.toPshHom x

@[reassoc]
/--
lemma `stalkSpecializes_stalkMap` / 引理 `stalkSpecializes_stalkMap`

English:
lemma stalkSpecializes_stalkMap
  statement: (x x' : X)
  proof: PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toPshHom h

中文:
引理 stalkSpecializes_stalkMap
  结论: (x x' : X)
  证明: PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toPshHom h

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap.stalkSpecializes_stalkMap, f.toPshHom, stalkMap, stalkSpecializes_stalkMap, toPshHom
-/
lemma stalkSpecializes_stalkMap (x x' : X)
    (h : x ⤳ x') : Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toPshHom h

/--
lemma `stalkSpecializes_stalkMap_apply` / 引理 `stalkSpecializes_stalkMap_apply`

English:
lemma stalkSpecializes_stalkMap_apply
  given: (x x' : X) (h : x ⤳ x') (y)
  proof: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

@[reassoc]

中文:
引理 stalkSpecializes_stalkMap_apply
  条件: (x x' : X) (h : x ⤳ x') (y)
  证明: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

@[reassoc]

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff.mp, DFunLike, DFunLike.congr_fun, congr_fun, hom_ext_iff, stalkSpecializes_stalkMap
-/
lemma stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) y) =
      (X.presheaf.stalkSpecializes h (f.stalkMap x' y)) :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

@[reassoc]
/--
lemma `stalkMap_congr` / 引理 `stalkMap_congr`

English:
lemma stalkMap_congr
  statement: (f g : X ⟶ Y) (hfg : f = g) (x x' : X)
  proof: LocallyRingedSpace.stalkMap_congr f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x x' hxx'

@[reassoc]

中文:
引理 stalkMap_congr
  结论: (f g : X ⟶ Y) (hfg : f = g) (x x' : X)
  证明: LocallyRingedSpace.stalkMap_congr f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x x' hxx'

@[reassoc]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_congr, f.toLRSHom, g.toLRSHom, stalkMap_congr, toLRSHom
-/
lemma stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X)
    (hxx' : x = x') : f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (.of_eq <| hfg ▸ hxx' ▸ rfl)).hom ≫ g.stalkMap x' :=
  LocallyRingedSpace.stalkMap_congr f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x x' hxx'

@[reassoc]
/--
lemma `stalkMap_congr_hom` / 引理 `stalkMap_congr_hom`

English:
lemma stalkMap_congr_hom
  given: (f g : X ⟶ Y) (hfg : f = g) (x : X)
  proof: LocallyRingedSpace.stalkMap_congr_hom f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x

@[reassoc]

中文:
引理 stalkMap_congr_hom
  条件: (f g : X ⟶ Y) (hfg : f = g) (x : X)
  证明: LocallyRingedSpace.stalkMap_congr_hom f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x

@[reassoc]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_congr_hom, f.toLRSHom, g.toLRSHom, stalkMap_congr_hom, toLRSHom
-/
lemma stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x = (Y.presheaf.stalkCongr (.of_eq <| hfg ▸ rfl)).hom ≫ g.stalkMap x :=
  LocallyRingedSpace.stalkMap_congr_hom f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x

@[reassoc]
/--
lemma `stalkMap_congr_point` / 引理 `stalkMap_congr_point`

English:
lemma stalkMap_congr_point
  given: (x x' : X) (hxx' : x = x')
  proof: LocallyRingedSpace.stalkMap_congr_point f.toLRSHom x x' hxx'

@[reassoc (attr := simp)]

中文:
引理 stalkMap_congr_point
  条件: (x x' : X) (hxx' : x = x')
  证明: LocallyRingedSpace.stalkMap_congr_point f.toLRSHom x x' hxx'

@[reassoc (attr := simp)]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_congr_point, f.toLRSHom, stalkMap_congr_point, toLRSHom
-/
lemma stalkMap_congr_point (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (.of_eq <| hxx' ▸ rfl)).hom ≫ f.stalkMap x' :=
  LocallyRingedSpace.stalkMap_congr_point f.toLRSHom x x' hxx'

@[reassoc (attr := simp)]
/--
lemma `stalkMap_hom_inv` / 引理 `stalkMap_hom_inv`

English:
lemma stalkMap_hom_inv
  given: (e : X ≅ Y) (y : Y)
  proof: LocallyRingedSpace.stalkMap_hom_inv (forgetToLocallyRingedSpace.mapIso e) y

@[simp]

中文:
引理 stalkMap_hom_inv
  条件: (e : X ≅ Y) (y : Y)
  证明: LocallyRingedSpace.stalkMap_hom_inv (forgetToLocallyRingedSpace.mapIso e) y

@[simp]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_hom_inv, forgetToLocallyRingedSpace, forgetToLocallyRingedSpace.mapIso, mapIso, stalkMap_hom_inv
-/
lemma stalkMap_hom_inv (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv y) ≫ e.inv.stalkMap y =
      (Y.presheaf.stalkCongr (.of_eq (by simp))).hom :=
  LocallyRingedSpace.stalkMap_hom_inv (forgetToLocallyRingedSpace.mapIso e) y

@[simp]
/--
lemma `stalkMap_hom_inv_apply` / 引理 `stalkMap_hom_inv_apply`

English:
lemma stalkMap_hom_inv_apply
  given: (e : X ≅ Y) (y : Y) (z)
  proof: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

@[reassoc (attr := simp)]

中文:
引理 stalkMap_hom_inv_apply
  条件: (e : X ≅ Y) (y : Y) (z)
  证明: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

@[reassoc (attr := simp)]

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff.mp, DFunLike, DFunLike.congr_fun, congr_fun, hom_ext_iff, stalkMap_hom_inv
-/
lemma stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv y) z) =
      (Y.presheaf.stalkCongr (.of_eq (by simp))).hom z :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

@[reassoc (attr := simp)]
/--
lemma `stalkMap_inv_hom` / 引理 `stalkMap_inv_hom`

English:
lemma stalkMap_inv_hom
  given: (e : X ≅ Y) (x : X)
  proof: LocallyRingedSpace.stalkMap_inv_hom (forgetToLocallyRingedSpace.mapIso e) x

@[simp]

中文:
引理 stalkMap_inv_hom
  条件: (e : X ≅ Y) (x : X)
  证明: LocallyRingedSpace.stalkMap_inv_hom (forgetToLocallyRingedSpace.mapIso e) x

@[simp]

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_inv_hom, forgetToLocallyRingedSpace, forgetToLocallyRingedSpace.mapIso, mapIso, stalkMap_inv_hom
-/
lemma stalkMap_inv_hom (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom x) ≫ e.hom.stalkMap x =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom :=
  LocallyRingedSpace.stalkMap_inv_hom (forgetToLocallyRingedSpace.mapIso e) x

@[simp]
/--
lemma `stalkMap_inv_hom_apply` / 引理 `stalkMap_inv_hom_apply`

English:
lemma stalkMap_inv_hom_apply
  given: (e : X ≅ Y) (x : X) (y)
  proof: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]

中文:
引理 stalkMap_inv_hom_apply
  条件: (e : X ≅ Y) (x : X) (y)
  证明: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff.mp, DFunLike, DFunLike.congr_fun, congr_fun, hom_ext_iff, stalkMap_inv_hom
-/
lemma stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom x) y) =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom y :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]
/--
lemma `germ_stalkMap` / 引理 `germ_stalkMap`

English:
lemma germ_stalkMap
  given: (U : Y.Opens) (x : X) (hx : f x in U)
  proof: PresheafedSpace.stalkMap_germ f.toPshHom U x hx

@[simp]

中文:
引理 germ_stalkMap
  条件: (U : Y.Opens) (x : X) (hx : f x in U)
  证明: PresheafedSpace.stalkMap_germ f.toPshHom U x hx

@[simp]

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap_germ, f.toPshHom, stalkMap_germ, toPshHom
-/
lemma germ_stalkMap (U : Y.Opens) (x : X) (hx : f x in U) :
    Y.presheaf.germ U (f x) hx ≫ f.stalkMap x =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx :=
  PresheafedSpace.stalkMap_germ f.toPshHom U x hx

@[simp]
/--
lemma `germ_stalkMap_apply` / 引理 `germ_stalkMap_apply`

English:
lemma germ_stalkMap_apply
  given: (U : Y.Opens) (x : X) (hx : f x in U) (y)
  proof: PresheafedSpace.stalkMap_germ_apply f.toPshHom U x hx y

中文:
引理 germ_stalkMap_apply
  条件: (U : Y.Opens) (x : X) (hx : f x in U) (y)
  证明: PresheafedSpace.stalkMap_germ_apply f.toPshHom U x hx y

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap_germ_apply, f.toPshHom, stalkMap_germ_apply, toPshHom
-/
lemma germ_stalkMap_apply (U : Y.Opens) (x : X) (hx : f x in U) (y) :
    f.stalkMap x (Y.presheaf.germ _ (f x) hx y) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U y) :=
  PresheafedSpace.stalkMap_germ_apply f.toPshHom U x hx y

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `arrowStalkMapIsoOfEq` / `arrowStalkMapIsoOfEq` 的定义

English:
definition arrowStalkMapIsoOfEq
  signature: {x y : X}
  body: Arrow.isoMk (Y.presheaf.stalkCongr <| (Inseparable.of_eq h).map f.continuous)
(X.presheaf.stalkCongr <| Inseparable.of_eq h) by
    simp only [Arrow.mk_left, Arrow.mk_right, TopCat.Presheaf.stalkCongr_hom,
      Arrow.mk_hom]
    rw [stalkSpecializes_stalkMap]

中文:
定义 arrowStalkMapIsoOfEq
  签名: {x y : X}
  定义体: Arrow.isoMk (Y.presheaf.stalkCongr <| (Inseparable.of_eq h).map f.continuous)
(X.presheaf.stalkCongr <| Inseparable.of_eq h) by
    simp only [Arrow.mk_left, Arrow.mk_right, TopCat.Presheaf.stalkCongr_hom,
      Arrow.mk_hom]
    rw [stalkSpecializes_stalkMap]

Depends on / 依赖: Arrow.isoMk, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right, Inseparable, Inseparable.of_eq, Presheaf, TopCat, TopCat.Presheaf.stalkCongr_hom, X.presheaf.stalkCongr, Y.presheaf.stalkCongr, continuous, f.continuous, mk_hom, mk_left, mk_right, of_eq, presheaf, stalkCongr, stalkCongr_hom
-/
noncomputable def arrowStalkMapIsoOfEq {x y : X}
    (h : x = y) : Arrow.mk (f.stalkMap x) ≅ Arrow.mk (f.stalkMap y) :=
  Arrow.isoMk (Y.presheaf.stalkCongr <| (Inseparable.of_eq h).map f.continuous)
(X.presheaf.stalkCongr <| Inseparable.of_eq h) by
    simp only [Arrow.mk_left, Arrow.mk_right, TopCat.Presheaf.stalkCongr_hom,
      Arrow.mk_hom]
    rw [stalkSpecializes_stalkMap]

end Hom

end Scheme

end Stalks

section IsLocalRing

open IsLocalRing

@[simp]
/--
lemma `Spec_closedPoint` / 引理 `Spec_closedPoint`

English:
lemma Spec_closedPoint
  statement: {R S : CommRingCat} [IsLocalRing R] [IsLocalRing S]
  proof: IsLocalRing.comap_closedPoint f.hom

中文:
引理 Spec_closedPoint
  结论: {R S : 交换环范畴} [是局部环 R] [是局部环 S]
  证明: IsLocalRing.comap_closedPoint f.hom

Depends on / 依赖: IsLocalRing, IsLocalRing.comap_closedPoint, comap_closedPoint, f.hom
-/
lemma Spec_closedPoint {R S : CommRingCat} [IsLocalRing R] [IsLocalRing S]
    {f : R ⟶ S} [IsLocalHom f.hom] : Spec.map f (closedPoint S) = closedPoint R :=
  IsLocalRing.comap_closedPoint f.hom

end IsLocalRing

end AlgebraicGeometry
