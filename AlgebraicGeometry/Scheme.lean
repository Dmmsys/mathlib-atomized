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

/-- We define `Scheme` as an `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.toLocallyRingedSpace.obj (op R)`
for some `R : CommRingCat`.
-/
/-
**AlgebraicGeometry.Scheme** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define `Scheme` as an `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that the restriction of `X` to `U` is isomorphic,
as a locally ringed space, to `Spec.toLocallyRingedSpace.obj (op R)`
for some `R : CommRingCat`.
-/
structure Scheme extends LocallyRingedSpace where
  local_affine :
    ∀ x : toLocallyRingedSpace,
      ∃ (U : OpenNhds x) (R : CommRingCat),
        Nonempty
          (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R))

namespace Scheme

/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Scheme Type* where
  coe X := X.carrier

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for coercing schemes to types. -/
@[app_delab TopCat.carrier]
meta def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``TopCat.carrier 1
  withNaryArg 0 do
  guard <| (← getExpr).isAppOfArity ``PresheafedSpace.carrier 3
  withNaryArg 2 do
  guard <| (← getExpr).isAppOfArity ``SheafedSpace.toPresheafedSpace 3
  withNaryArg 2 do
  guard <| (← getExpr).isAppOfArity ``LocallyRingedSpace.toSheafedSpace 1
  withNaryArg 0 do
  guard <| (← getExpr).isAppOfArity ``Scheme.toLocallyRingedSpace 1
  withNaryArg 0 do
  `(↥$(← delab))

/-- The type of open sets of a scheme. -/
/-
**AlgebraicGeometry.Scheme.Opens** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：Opens (X : Scheme) : Type*
参数：X : Scheme。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of open sets of a scheme.
-/
abbrev Opens (X : Scheme) : Type* := TopologicalSpace.Opens X

/-- A morphism between schemes is a morphism between the underlying locally ringed spaces. -/
/-
**AlgebraicGeometry.Scheme.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry.Sc
heme`。
形式化陈述：AlgebraicGeometry.Scheme → AlgebraicGeometry.Scheme → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between schemes is a morphism between the underlying locally ringed s
paces.
-/
structure Hom (X Y : Scheme)
  extends toLRSHom' : X.toLocallyRingedSpace.Hom Y.toLocallyRingedSpace where

/-- Cast a morphism of schemes into morphisms of local ringed spaces. -/
/-
**AlgebraicGeometry.Scheme.Hom.toLRSHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.Hom Y → (X.toLocallyRingedSpace ⟶ Y.t
oLocallyRingedSpace)
参数：X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast a morphism of schemes into morphisms of local ringed spaces.
-/
abbrev Hom.toLRSHom {X Y : Scheme.{u}} (f : X.Hom Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom'

/-- See Note [custom simps projection] -/
/-
**AlgebraicGeometry.Scheme.Hom.Simps.toLRSHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.Hom.Simps`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.Hom Y → (X.toLocallyRingedSpace ⟶ Y.t
oLocallyRingedSpace)
参数：X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Hom.Simps.toLRSHom {X Y : Scheme.{u}} (f : X.Hom Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom

initialize_simps_projections Hom (toLRSHom' → toLRSHom)

/-- Schemes are a full subcategory of locally ringed spaces.
-/
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Schemes are a full subcategory of locally ringed spaces.
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

/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} : CoeFun (X ⟶ Y) (fun _ ↦ X → Y) where
  coe f := f.base

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for coercing morphisms between schemes to functions. -/
@[app_delab DFunLike.coe]
meta def delabCoeFunNotation : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``DFunLike.coe 5
  withNaryArg 4 do
  guard <| (← getExpr).isAppOfArity ``CategoryTheory.ConcreteCategory.hom 9
  withNaryArg 8 do
  guard <| (← getExpr).isAppOfArity ``PresheafedSpace.Hom.base 5
  withNaryArg 4 do
  guard <| (← getExpr).isAppOfArity ``LocallyRingedSpace.Hom.toHom 3
  withNaryArg 2 do
  guard <| (← getExpr).isAppOfArity ``Scheme.Hom.toLRSHom' 3
  withNaryArg 2 do
  `(⇑$(← delab))

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Pretty printer for applying morphisms of schemes to set-theoretic points. -/
@[app_delab DFunLike.coe]
meta def delabCoeFunAppNotation : Delab := whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``DFunLike.coe 6
  let func ← do
    withNaryArg 4 do
    guard <| (← getExpr).isAppOfArity ``CategoryTheory.ConcreteCategory.hom 9
    withNaryArg 8 do
    guard <| (← getExpr).isAppOfArity ``PresheafedSpace.Hom.base 5
    withNaryArg 4 do
    guard <| (← getExpr).isAppOfArity ``LocallyRingedSpace.Hom.toHom 3
    withNaryArg 2 do
    guard <| (← getExpr).isAppOfArity ``Scheme.Hom.toLRSHom' 3
    withNaryArg 2 do
    delab
  `($func $(← withNaryArg 5 do delab))

/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} : Subsingleton Γ(X, ⊥) :=
  CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty

@[continuity, fun_prop]
/-
**AlgebraicGeometry.Scheme.Hom.continuous** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y), Continuous ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
lemma Hom.continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f := f.base.hom.2

/-- The structure sheaf of a scheme. -/
/-
**AlgebraicGeometry.Scheme.sheaf** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sc
heme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → TopCat.Sheaf CommRingCat ↑X.toPresheafedS
pace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure sheaf of a scheme.
-/
protected abbrev sheaf (X : Scheme) :=
  X.toSheafedSpace.sheaf

/--
We give schemes the specialization preorder by default.
-/
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We give schemes the specialization preorder by default.
-/
instance {X : Scheme.{u}} : Preorder X := specializationPreorder X
/-
**AlgebraicGeometry.Scheme.le_iff_specializes** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：le_iff_specializes {X : Scheme.{u}} {a b : X} : a <= b ↔ b ⤳ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_iff_specializes {X : Scheme.{u}} {a b : X} : a ≤ b ↔ b ⤳ a := by rfl

open Order in
/-
**AlgebraicGeometry.Scheme.height_of_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：height_of_isClosed {X : Scheme} {x : X} (hx : IsClosed {x}) : height x = 0
参数：hx : IsClosed {x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `IsClosed.not_specializes`：IsClosed.not_specializes (hs : IsClosed s) (hx
 : x in s) (hy : y ∉ s) : ¬x ⤳ y
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

/-- Given a morphism of schemes `f : X ⟶ Y`, and open `U ⊆ Y`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)`.

This is treated as a suffix in lemma names. -/
/-
**AlgebraicGeometry.Scheme.Hom.app** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：app (U : Y.Opens) : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)
参数：U : Y.Opens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of schemes `f : X ⟶ Y`, and open `U ⊆ Y`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U)`.

This is treated as a suffix in lemma names.
-/
abbrev app (U : Y.Opens) : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  f.c.app (op U)

/-- Given a morphism of schemes `f : X ⟶ Y`, this is the induced map `Γ(Y, ⊤) ⟶ Γ(X, ⊤)`.
This is treated as a suffix in lemma names. -/
/-
**AlgebraicGeometry.Scheme.Hom.appTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of schemes `f : X ⟶ Y`, this is the induced map `Γ(Y, ⊤) ⟶ Γ(X,
 ⊤)`.
This is treated as a suffix in lemma names.
-/
abbrev appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤) :=
  f.app ⊤

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.naturality** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：naturality (i : op U' ⟶ op U) : Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.
presheaf.map ((Opens.map f.base).map i.unop).op
参数：i : op U' ⟶ op U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma naturality (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map i.unop).op :=
  f.c.naturality i

/-- Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`.

This is treated as a suffix in lemma names. -/
/-
**AlgebraicGeometry.Scheme.Hom.appLE** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：appLE (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V)
参数：U : Y.Opens；V : X.Opens；e : V <= f ⁻¹ᵁ U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of schemes `f : X ⟶ Y`, and open sets `U ⊆ Y`, `V ⊆ f ⁻¹' U`,
this is the induced map `Γ(Y, U) ⟶ Γ(X, V)`.

This is treated as a suffix in lemma names.
-/
def appLE (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : Γ(Y, U) ⟶ Γ(X, V) :=
  f.app U ≫ X.presheaf.map (homOfLE e).op

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.appLE_map** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：appLE_map (e : V <= f ⁻¹ᵁ U) (i : op V ⟶ op V') : f.appLE U V e ≫ X.preshe
af.map i = f.appLE U V' (i.unop.le.trans e)
参数：e : V <= f ⁻¹ᵁ U；i : op V ⟶ op V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE.eq_1`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (e : V ≤ (TopologicalSpace.Opens.m
ap f.base).obj U),   Algebrai…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma appLE_map (e : V ≤ f ⁻¹ᵁ U) (i : op V ⟶ op V') :
    f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.trans e) := by
  rw [Hom.appLE, Category.assoc, ← Functor.map_comp]
  rfl

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.appLE_map'** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：appLE_map' (e : V <= f ⁻¹ᵁ U) (i : V = V') : f.appLE U V' (i ▸ e) ≫ X.pres
heaf.map (eqToHom i).op = f.appLE U V e
参数：e : V <= f ⁻¹ᵁ U；i : V = V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
-/
lemma appLE_map' (e : V ≤ f ⁻¹ᵁ U) (i : V = V') :
    f.appLE U V' (i ▸ e) ≫ X.presheaf.map (eqToHom i).op = f.appLE U V e :=
  appLE_map _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.map_appLE** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：map_appLE (e : V <= f ⁻¹ᵁ U) (i : op U' ⟶ op U) : Y.presheaf.map i ≫ f.app
LE U V e = f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le)
参数：e : V <= f ⁻¹ᵁ U；i : op U' ⟶ op U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE.eq_1`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (e : V ≤ (TopologicalSpace.Opens.m
ap f.base).obj U),   Algebrai…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.naturality_assoc`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) {U U' : Y.Opens} (i : Opposite.op U' ⟶ Opposite.op U) {Z :
 CommRingCat}   (h : X.presheaf.obj…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma map_appLE (e : V ≤ f ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    Y.presheaf.map i ≫ f.appLE U V e =
      f.appLE U' V (e.trans ((Opens.map f.base).map i.unop).le) := by
  rw [Hom.appLE, f.naturality_assoc, ← Functor.map_comp]
  rfl

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.map_appLE'** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：map_appLE' (e : V <= f ⁻¹ᵁ U) (i : U' = U) : Y.presheaf.map (eqToHom i).op
 ≫ f.appLE U' V (i ▸ e) = f.appLE U V e
参数：e : V <= f ⁻¹ᵁ U；i : U' = U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_appLE' (e : V ≤ f ⁻¹ᵁ U) (i : U' = U) :
    Y.presheaf.map (eqToHom i).op ≫ f.appLE U' V (i ▸ e) = f.appLE U V e :=
  map_appLE _ _ _
/-
**AlgebraicGeometry.Scheme.Hom.app_eq_appLE** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：app_eq_appLE {U : Y.Opens} : f.app U = f.appLE U _ le_rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma app_eq_appLE {U : Y.Opens} :
    f.app U = f.appLE U _ le_rfl := by
  simp [Hom.appLE]
/-
**AlgebraicGeometry.Scheme.Hom.appLE_eq_app** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：appLE_eq_app {U : Y.Opens} : f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
-/
lemma appLE_eq_app {U : Y.Opens} :
    f.appLE U (f ⁻¹ᵁ U) le_rfl = f.app U :=
  (app_eq_appLE f).symm
/-
**AlgebraicGeometry.Scheme.Hom.appLE_congr** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：appLE_congr (e : V <= f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V') (P : forall {R 
S : CommRingCat.{u}} (_ : R ⟶ S), Prop) : P (f.appLE U V e) ↔ P (f.appLE U' V' (
e₁ ▸ e₂ ▸ e))
参数：e : V <= f ⁻¹ᵁ U；e₁ : U = U'；e₂ : V = V'；P : forall {R S : CommRingCat.{u}} (
_ : R ⟶ S), Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma appLE_congr (e : V ≤ f ⁻¹ᵁ U) (e₁ : U = U') (e₂ : V = V')
    (P : ∀ {R S : CommRingCat.{u}} (_ : R ⟶ S), Prop) :
    P (f.appLE U V e) ↔ P (f.appLE U' V' (e₁ ▸ e₂ ▸ e)) := by
  subst e₁; subst e₂; rfl

/-- A morphism of schemes `f : X ⟶ Y` induces a local ring homomorphism from
`Y.presheaf.stalk (f x)` to `X.presheaf.stalk x` for any `x : X`. -/
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：stalkMap (x : X) : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` induces a local ring homomorphism from
`Y.presheaf.stalk (f x)` to `X.presheaf.stalk x` for any `x : X`.
-/
def stalkMap (x : X) : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x :=
  f.toLRSHom.stalkMap x

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f g : X ⟶ Y} (h_base : f.base = g.base
),   (∀ (U : Y.Opens),       CategoryTheory.CategoryStruct.comp (AlgebraicGeomet
ry.Scheme.Hom.app f U)           (X.presheaf.map (CategoryTheory.eqToHom ⋯).op) 
=         AlgebraicGeometry.Scheme.Hom.app g U) →     f = g
参数：h_base : f.base = g.base；∀ (U : Y.Opens),       CategoryTheory.CategoryStruct
.comp (AlgebraicGeometry.Scheme.Hom.app f U)           (X.presheaf.map (Category
Theory.eqToHom ⋯).op) =         AlgebraicGeometry.Scheme.Hom.app g U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.Hom.ext'`：∀ {X Y : AlgebraicGeometr
y.LocallyRingedSpace} {f g : X ⟶ Y}, f.toHom = g.toHom → f = g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.Hom.ext`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {X Y : AlgebraicGeometry.PresheafedSpace C}   
(α β : X.Hom Y) (w : α.base = β…
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
-/
protected lemma ext {f g : X ⟶ Y} (h_base : f.base = g.base)
    (h_app : ∀ U, f.app U ≫ X.presheaf.map
      (eqToHom congr((Opens.map $h_base.symm).obj U)).op = g.app U) : f = g := by
  cases f; cases g; congr 1
  apply LocallyRingedSpace.Hom.ext'
  ext : 1
  · exact h_base
  · exact TopCat.Presheaf.ext (fun U ↦ by simpa using! h_app U)

/-- An alternative ext lemma for scheme morphisms. -/
/-
**AlgebraicGeometry.Scheme.Hom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry
.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f g : X ⟶ Y},   AlgebraicGeometry.Sche
me.Hom.toLRSHom f = AlgebraicGeometry.Scheme.Hom.toLRSHom g → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An alternative ext lemma for scheme morphisms.
-/
protected lemma ext' {f g : X ⟶ Y} (h : f.toLRSHom = g.toLRSHom) : f = g := by
  cases f; cases g; congr 1
/-
**AlgebraicGeometry.Scheme.Hom.mem_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：mem_preimage {x : X} {U : Opens Y} : x in f ⁻¹ᵁ U ↔ f x in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_preimage {x : X} {U : Opens Y} : x ∈ f ⁻¹ᵁ U ↔ f x ∈ U := .rfl
/-
**AlgebraicGeometry.Scheme.Hom.coe_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：coe_preimage {U : Opens Y} : f ⁻¹ᵁ U = f ⁻¹' U
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_preimage {U : Opens Y} : f ⁻¹ᵁ U = f ⁻¹' U := rfl
/-
**AlgebraicGeometry.Scheme.Hom.preimage_sup** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：preimage_sup {U V : Opens Y} : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_sup {U V : Opens Y} : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := rfl
/-
**AlgebraicGeometry.Scheme.Hom.preimage_inf** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：preimage_inf {U V : Opens Y} : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_inf {U V : Opens Y} : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := rfl
/-
**AlgebraicGeometry.Scheme.Hom.preimage_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y), (TopologicalSpace.Opens.ma
p f.base).obj ⊤ = ⊤
参数：f : X ⟶ Y；TopologicalSpace.Opens.map f.base。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_top : f ⁻¹ᵁ ⊤ = ⊤ := rfl
/-
**AlgebraicGeometry.Scheme.Hom.preimage_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y), (TopologicalSpace.Opens.ma
p f.base).obj ⊥ = ⊥
参数：f : X ⟶ Y；TopologicalSpace.Opens.map f.base。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma preimage_bot : f ⁻¹ᵁ ⊥ = ⊥ := rfl
/-
**AlgebraicGeometry.Scheme.Hom.preimage_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：preimage_iSup {ι} (U : ι -> Opens Y) : f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i
参数：U : ι -> Opens Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preimage_iSup {ι} (U : ι → Opens Y) : f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i :=
  Opens.ext (by simp)
/-
**AlgebraicGeometry.Scheme.Hom.iSup_preimage_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：iSup_preimage_eq_top {ι} {U : ι -> Opens Y} (hU : iSup U = ⊤) : ⨆ i, f ⁻¹ᵁ
 U i = ⊤
参数：hU : iSup U = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_iSup`：preimage_iSup {ι} (U : ι -> 
Opens Y) : f ⁻¹ᵁ iSup U = ⨆ i, f ⁻¹ᵁ U i
-/
lemma iSup_preimage_eq_top {ι} {U : ι → Opens Y} (hU : iSup U = ⊤) :
    ⨆ i, f ⁻¹ᵁ U i = ⊤ := f.preimage_iSup U ▸ hU ▸ rfl

@[gcongr]
/-
**AlgebraicGeometry.Scheme.Hom.preimage_mono** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：preimage_mono {U U' : Y.Opens} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
参数：hUU' : U <= U'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_mono {U U' : Y.Opens} (hUU' : U ≤ U') :
    f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U' :=
  fun _ ha ↦ hUU' ha
/-
**AlgebraicGeometry.Scheme.Hom.id_preimage** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：id_preimage (U : X.Opens) : (𝟙 X) ⁻¹ᵁ U = U
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_preimage (U : X.Opens) : (𝟙 X) ⁻¹ᵁ U = U := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.comp_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：comp_preimage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g) ⁻
¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U
参数：f : X ⟶ Y；g : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_preimage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U := rfl

end Hom

/-- The forgetful functor from `Scheme` to `LocallyRingedSpace`. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Scheme` to `LocallyRingedSpace`.
-/
def forgetToLocallyRingedSpace : Scheme ⥤ LocallyRingedSpace where
  obj := toLocallyRingedSpace
  map := Hom.toLRSHom

/-- The forget functor `Scheme ⥤ LocallyRingedSpace` is fully faithful. -/
@[simps preimage_toLRSHom]
/-
**AlgebraicGeometry.Scheme.fullyFaithfulForgetToLocallyRingedSpace** 是 Mathlib 中
的一个定义，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：fullyFaithfulForgetToLocallyRingedSpace : forgetToLocallyRingedSpace.Fully
Faithful where preimage
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forget functor `Scheme ⥤ LocallyRingedSpace` is fully faithful.
-/
def fullyFaithfulForgetToLocallyRingedSpace :
    forgetToLocallyRingedSpace.FullyFaithful where
  preimage := Hom.mk
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : forgetToLocallyRingedSpace.Full :=
  fullyFaithfulForgetToLocallyRingedSpace.full
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : forgetToLocallyRingedSpace.Faithful :=
  fullyFaithfulForgetToLocallyRingedSpace.faithful

/-- The forgetful functor from `Scheme` to `TopCat`. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.forgetToTop** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：forgetToTop : Scheme ⥤ TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Scheme` to `TopCat`.
-/
def forgetToTop : Scheme ⥤ TopCat :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToTop

/-- An isomorphism of schemes induces a homeomorphism of the underlying topological spaces. -/
/-
**AlgebraicGeometry.Scheme.homeoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : X ≃ₜ Y
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of schemes induces a homeomorphism of the underlying topological 
spaces.
-/
noncomputable def homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : X ≃ₜ Y :=
  TopCat.homeoOfIso (forgetToTop.mapIso e)

@[simp]
/-
**AlgebraicGeometry.Scheme.coe_homeoOfIso** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：coe_homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) : ⇑(homeoOfIso e) = e.hom
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_homeoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    ⇑(homeoOfIso e) = e.hom := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.coe_homeoOfIso_symm** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：coe_homeoOfIso_symm {X Y : Scheme.{u}} (e : X ≅ Y) : ⇑(homeoOfIso e.symm) 
= e.inv
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_homeoOfIso_symm {X Y : Scheme.{u}} (e : X ≅ Y) :
    ⇑(homeoOfIso e.symm) = e.inv := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.homeoOfIso_symm** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) : (homeoOfIso e).symm = homeoOf
Iso e.symm
参数：e : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) :
    (homeoOfIso e).symm = homeoOfIso e.symm := rfl
/-
**AlgebraicGeometry.Scheme.homeoOfIso_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：homeoOfIso_apply {X Y : Scheme} (e : X ≅ Y) (x : X) : homeoOfIso e x = e.h
om x
参数：e : X ≅ Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homeoOfIso_apply {X Y : Scheme} (e : X ≅ Y) (x : X) :
    homeoOfIso e x = e.hom x := rfl

alias _root_.CategoryTheory.Iso.schemeIsoToHomeo := homeoOfIso

/-- An isomorphism of schemes induces a homeomorphism of the underlying topological spaces. -/
/-
**AlgebraicGeometry.Scheme.Hom.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → [CategoryTheory.IsIso f] 
→ ↥X ≃ₜ ↥Y
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of schemes induces a homeomorphism of the underlying topological 
spaces.
-/
noncomputable def Hom.homeomorph {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] :
    X ≃ₜ Y :=
  (asIso f).schemeIsoToHomeo

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.homeomorph_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : CategoryTheory.IsIs
o f] (x : ↥X),   (AlgebraicGeometry.Scheme.Hom.homeomorph f) x = f x
参数：f : X ⟶ Y；x : ↥X；AlgebraicGeometry.Scheme.Hom.homeomorph f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.homeomorph_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f] (x) :
    f.homeomorph x = f x := rfl
/-
**AlgebraicGeometry.Scheme.hasCoeToTopCat** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：hasCoeToTopCat : CoeOut Scheme TopCat where coe X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToTopCat : CoeOut Scheme TopCat where
  coe X := X.carrier

/-- forgetful functor to `TopCat` is the same as coercion -/
unif_hint forgetToTop_obj_eq_coe (X : Scheme) where ⊢ forgetToTop.obj X ≟ (X : TopCat)

/-- The forgetful functor from `Scheme` to `Type`. -/
nonrec def forget : Scheme.{u} ⥤ Type u := Scheme.forgetToTop ⋙ forget TopCat

/-
**AlgebraicGeometry.Scheme.forgetToTop_comp_forget** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：forgetToTop_comp_forget : forgetToTop ⋙ CategoryTheory.forget TopCat = for
get
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forgetToTop_comp_forget : forgetToTop ⋙ CategoryTheory.forget TopCat = forget := rfl

/-- forgetful functor to `Scheme` is the same as coercion -/
-- Schemes are often coerced as types, and it would be useful to have definitionally equal types
-- to be reducibly equal. The alternative is to make `forget` reducible but that option has
-- poor performance consequences.
unif_hint forget_obj_eq_coe (X : Scheme) where ⊢ forget.obj X ≟ (X : Type*)

/-
**AlgebraicGeometry.Scheme.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme), AlgebraicGeometry.Scheme.forget.obj X = 
↥X
参数：X : AlgebraicGeometry.Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_obj (X) : Scheme.forget.obj X = X := rfl
/-
**AlgebraicGeometry.Scheme.forget_map'** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：forget_map' {X Y} (f : X ⟶ Y) : (forget.map f : _ -> _) = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget_map' {X Y} (f : X ⟶ Y) : (forget.map f : _ → _) = f := rfl
/-
**AlgebraicGeometry.Scheme.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y), AlgebraicGeometry.Scheme.f
orget.map f = TypeCat.ofHom ⇑f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_map {X Y} (f : X ⟶ Y) : forget.map f = ↾f := rfl

namespace Hom

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.id_base** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Scheme.Hom`。
形式化陈述：id_base (X : Scheme) : (𝟙 X :).base = 𝟙 _
参数：X : Scheme。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_base (X : Scheme) : (𝟙 X :).base = 𝟙 _ :=
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.id_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.Scheme.Hom`。
形式化陈述：id_app {X : Scheme} (U : X.Opens) : (𝟙 X :).app U = 𝟙 _
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_app {X : Scheme} (U : X.Opens) :
    (𝟙 X :).app U = 𝟙 _ := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.id_appTop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：id_appTop {X : Scheme} : (𝟙 X :).appTop = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_appTop {X : Scheme} :
    (𝟙 X :).appTop = 𝟙 _ :=
  rfl

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.comp_toLRSHom** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：comp_toLRSHom {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).toLRSHom 
= f.toLRSHom ≫ g.toLRSHom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toLRSHom {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toLRSHom = f.toLRSHom ≫ g.toLRSHom :=
  rfl

@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.comp_base** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：comp_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base
 ≫ g.base
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_base {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
/-
**AlgebraicGeometry.Scheme.Hom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = 
g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by
  simp

@[simp, reassoc] -- reassoc lemma does not need `simp`
/-
**AlgebraicGeometry.Scheme.Hom.comp_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：comp_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.
app U ≫ f.app _
参数：f : X ⟶ Y；g : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
    (f ≫ g).app U = g.app U ≫ f.app _ :=
  rfl

@[simp, reassoc] -- reassoc lemma does not need `simp`
/-
**AlgebraicGeometry.Scheme.Hom.comp_appTop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：comp_appTop {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).appTop = g.
appTop ≫ f.appTop
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_appTop {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop :=
  rfl

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：appLE_comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : 
g.appLE U V e₁ ≫ f.appLE V W e₂ = (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base
).map (homOfLE e₁)).le)
参数：f : X ⟶ Y；g : Y ⟶ Z；U V W e₁ e₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.naturality_assoc`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) {U U' : Y.Opens} (i : Opposite.op U' ⟶ Opposite.op U) {Z :
 CommRingCat}   (h : X.presheaf.obj…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem appLE_comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ =
      (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le) := by
  dsimp [Hom.appLE]
  rw [Category.assoc, f.naturality_assoc, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc] -- reassoc lemma does not need `simp`
/-
**AlgebraicGeometry.Scheme.Hom.comp_appLE** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V e) : (f ≫ g).appL
E U V e = g.app U ≫ f.appLE _ V e
参数：f : X ⟶ Y；g : Y ⟶ Z；U V e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`：appLE_comp_appLE {X Y Z :
 Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : g.appLE U V e₁ ≫ f.appLE V W e₂
 = (f ≫ g).appLE U W (e₂.trans ((Op…
-/
theorem comp_appLE {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V e) :
    (f ≫ g).appLE U V e = g.app U ≫ f.appLE _ V e := by
  rw [g.app_eq_appLE, appLE_comp_appLE]
/-
**AlgebraicGeometry.Scheme.Hom.congr_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) : f.app U = g.app U
 ≫ X.presheaf.map (eqToHom (by subst e; rfl)).op
参数：e : f = g；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
    f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e; rfl)).op := by
  subst e; simp
/-
**AlgebraicGeometry.Scheme.Hom.app_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.Scheme.Hom`。
形式化陈述：app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) : f.app U = 
Y.presheaf.map (eqToHom e.symm).op ≫ f.app V ≫ X.presheaf.map (eqToHom (e ▸ rfl)
).op
参数：f : X ⟶ Y；e : U = V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem app_eq {X Y : Scheme} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    f.app U =
      Y.presheaf.map (eqToHom e.symm).op ≫ f.app V ≫ X.presheaf.map (eqToHom (e ▸ rfl)).op := by
  aesop
/-
**AlgebraicGeometry.Scheme.Hom.eqToHom_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：eqToHom_app {X Y : Scheme} (e : X = Y) (U) : (eqToHom e).app U = eqToHom (
by subst e; rfl)
参数：e : X = Y；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqToHom_app {X Y : Scheme} (e : X = Y) (U) :
    (eqToHom e).app U = eqToHom (by subst e; rfl) := by subst e; rfl
/-
**AlgebraicGeometry.Scheme.Hom.isIso_toLRSHom** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：isIso_toLRSHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toLRSHom
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_toLRSHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toLRSHom :=
  forgetToLocallyRingedSpace.map_isIso f
/-
**AlgebraicGeometry.Scheme.Hom.isIso_toPshHom** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：isIso_toPshHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toPshHom
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_toPshHom {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.toPshHom :=
  inferInstanceAs (IsIso ((LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).map f.toLRSHom))
/-
**AlgebraicGeometry.Scheme.Hom.isIso_base** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：isIso_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.base
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  Scheme.forgetToTop.map_isIso f

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U) : IsIso (f.app U) :=
  haveI := PresheafedSpace.c_isIso_of_iso f.toPshHom
  NatIso.isIso_app_of_isIso f.c _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.inv_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Scheme.Hom`。
形式化陈述：inv_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : X.Opens) : (inv f).app U
 = X.presheaf.map (eqToHom (show (f ≫ inv f) ⁻¹ᵁ U = U by rw [IsIso.hom_inv_id];
 rfl)).op ≫ inv (f.app ((inv f) ⁻¹ᵁ U))
参数：f : X ⟶ Y；U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app`：comp_app {X Y Z : Scheme} (f : X 
⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.app U ≫ f.app _
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.congr_app`：congr_app {X Y : Scheme} {f g : 
X ⟶ Y} (e : f = g) (U) : f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e
; rfl)).op
· 使用定理 `AlgebraicGeometry.Scheme.Hom.id_app`：id_app {X : Scheme} (U : X.Opens) :
 (𝟙 X :).app U = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem inv_app {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : X.Opens) :
    (inv f).app U =
      X.presheaf.map (eqToHom (show (f ≫ inv f) ⁻¹ᵁ U = U by rw [IsIso.hom_inv_id]; rfl)).op ≫
        inv (f.app ((inv f) ⁻¹ᵁ U)) := by
  rw [IsIso.eq_comp_inv, ← comp_app, congr_app (IsIso.hom_inv_id f), id_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.inv_appTop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：inv_appTop {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : (inv f).appTop = inv f.a
ppTop
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.inv_app`：inv_app {X Y : Scheme} (f : X ⟶ Y)
 [IsIso f] (U : X.Opens) : (inv f).app U = X.presheaf.map (eqToHom (show (f ≫ in
v f) ⁻¹ᵁ U = U by rw [IsIs…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_appTop {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    (inv f).appTop = inv f.appTop := by simp

/-- Copies a morphism with a different underlying map -/
/-
**AlgebraicGeometry.Scheme.Hom.copyBase** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：copyBase {X Y : Scheme} (f : X.Hom Y) (g : X -> Y) (h : f.base = g) : X ⟶ 
Y where base
参数：f : X.Hom Y；g : X -> Y；h : f.base = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copies a morphism with a different underlying map
-/
def copyBase {X Y : Scheme} (f : X.Hom Y) (g : X → Y) (h : f.base = g) : X ⟶ Y where
  base := TopCat.ofHom ⟨g, h ▸ f.base.1.2⟩
  c := f.c ≫ (TopCat.Presheaf.pushforwardEq (by subst h; rfl) _).hom
  prop x := by
    subst h
    convert! f.prop x using 4
    cat_disch
/-
**AlgebraicGeometry.Scheme.Hom.copyBase_eq** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：copyBase_eq {X Y : Scheme} (f : X.Hom Y) (g : X -> Y) (h : f.base = g) : f
.copyBase g h = f
参数：f : X.Hom Y；g : X -> Y；h : f.base = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.pushforwardEq_hom_app`：pushforwardEq_hom_app {X Y : TopC
at.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Presheaf C) (U) : (pushforwardEq h ℱ).h
om.app U = ℱ.map (eqToHom (…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma copyBase_eq {X Y : Scheme} (f : X.Hom Y) (g : X → Y) (h : f.base = g) :
    f.copyBase g h = f := by
  subst h
  obtain ⟨⟨⟨f₁, f₂⟩, f₃⟩, f₄⟩ := f
  simp only [Hom.copyBase]
  congr
  cat_disch

end Hom

end Scheme

/-- The spectrum of a commutative ring, as a scheme. -/
/-
**AlgebraicGeometry.Spec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Spec (R : CommRingCat) : Scheme where local_affine _
参数：R : CommRingCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectrum of a commutative ring, as a scheme.
-/
def Spec (R : CommRingCat) : Scheme where
  local_affine _ := ⟨⟨⊤, trivial⟩, R, ⟨(Spec.toLocallyRingedSpace.obj (op R)).restrictTopIso⟩⟩
  toLocallyRingedSpace := Spec.locallyRingedSpaceObj R
/-
**AlgebraicGeometry.Spec_toLocallyRingedSpace** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：Spec_toLocallyRingedSpace (R : CommRingCat) : (Spec R).toLocallyRingedSpac
e = Spec.locallyRingedSpaceObj R
参数：R : CommRingCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Spec_toLocallyRingedSpace (R : CommRingCat) :
    (Spec R).toLocallyRingedSpace = Spec.locallyRingedSpaceObj R :=
  rfl

/-- The induced map of a ring homomorphism on the ring spectra, as a morphism of schemes. -/
/-
**AlgebraicGeometry.Spec.map** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Spec`。
形式化陈述：{R S : CommRingCat} → (R ⟶ S) → (AlgebraicGeometry.Spec S ⟶ AlgebraicGeome
try.Spec R)
参数：R ⟶ S；AlgebraicGeometry.Spec S ⟶ AlgebraicGeometry.Spec R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map of a ring homomorphism on the ring spectra, as a morphism of sch
emes.
-/
def Spec.map {R S : CommRingCat} (f : R ⟶ S) : Spec S ⟶ Spec R :=
  ⟨Spec.locallyRingedSpaceMap f⟩

@[simp]
/-
**AlgebraicGeometry.Spec.map_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Spe
c`。
形式化陈述：∀ (R : CommRingCat),   AlgebraicGeometry.Spec.map (CategoryTheory.Category
Struct.id R) =     CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec R)
参数：R : CommRingCat；CategoryTheory.CategoryStruct.id R；AlgebraicGeometry.Spec R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ext'`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 g : X ⟶ Y},   AlgebraicGeometry.Scheme.Hom.toLRSHom f = AlgebraicGeometry.Schem
e.Hom.toLRSHom g → f = …
· 使用定理 `AlgebraicGeometry.Spec.locallyRingedSpaceMap_id`：∀ (R : CommRingCat),   
AlgebraicGeometry.Spec.locallyRingedSpaceMap (CategoryTheory.CategoryStruct.id R
) =     CategoryTheory.CategoryStruct…
-/
theorem Spec.map_id (R : CommRingCat) : Spec.map (𝟙 R) = 𝟙 (Spec R) :=
  Scheme.Hom.ext' <| Spec.locallyRingedSpaceMap_id R

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc, simp]
/-
**AlgebraicGeometry.Spec.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
pec`。
形式化陈述：∀ {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T),   AlgebraicGeometry.Spec.
map (CategoryTheory.CategoryStruct.comp f g) =     CategoryTheory.CategoryStruct
.comp (AlgebraicGeometry.Spec.map g) (AlgebraicGeometry.Spec.map f)
参数：f : R ⟶ S；g : S ⟶ T；CategoryTheory.CategoryStruct.comp f g；AlgebraicGeometry.
Spec.map g；AlgebraicGeometry.Spec.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ext'`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 g : X ⟶ Y},   AlgebraicGeometry.Scheme.Hom.toLRSHom f = AlgebraicGeometry.Schem
e.Hom.toLRSHom g → f = …
· 使用定理 `AlgebraicGeometry.Spec.locallyRingedSpaceMap_comp`：∀ {R S T : CommRingCa
t} (f : R ⟶ S) (g : S ⟶ T),   AlgebraicGeometry.Spec.locallyRingedSpaceMap (Cate
goryTheory.CategoryStruct.comp f g) =  …
-/
theorem Spec.map_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f :=
  Scheme.Hom.ext' <| Spec.locallyRingedSpaceMap_comp f g

/-- The spectrum, as a contravariant functor from commutative rings to schemes. -/
@[simps, implicit_reducible]
/-
**AlgebraicGeometry.Scheme.Spec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sch
eme`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ AlgebraicGeometry.Scheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The spectrum, as a contravariant functor from commutative rings to schemes.
-/
protected def Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme where
  obj R := Spec (unop R)
  map f := Spec.map f.unop
  map_id R := by simp
  map_comp f g := by simp
/-
**AlgebraicGeometry.Spec.map_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.Spec`。
形式化陈述：∀ {R S : CommRingCat} (e : R = S), AlgebraicGeometry.Spec.map (CategoryThe
ory.eqToHom e) = CategoryTheory.eqToHom ⋯
参数：e : R = S；CategoryTheory.eqToHom e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
-/
lemma Spec.map_eqToHom {R S : CommRingCat} (e : R = S) :
    Spec.map (eqToHom e) = eqToHom (e ▸ rfl) := by
  subst e; exact Spec.map_id _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : CommRingCat} (f : R ⟶ S) [IsIso f] : IsIso (Spec.map f) :=
  inferInstanceAs (IsIso <| Scheme.Spec.map f.op)

@[simp]
/-
**AlgebraicGeometry.Spec.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Sp
ec`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S) [inst : CategoryTheory.IsIso f],   Algeb
raicGeometry.Spec.map (CategoryTheory.inv f) = CategoryTheory.inv (AlgebraicGeom
etry.Spec.map f)
参数：f : R ⟶ S；CategoryTheory.inv f；AlgebraicGeometry.Spec.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat`：∀ {R S : CommRingCat}
 (f : R ⟶ S) [CategoryTheory.IsIso f], CategoryTheory.IsIso (AlgebraicGeometry.S
pec.map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.op_inv`：op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).
op = inv f.op
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
-/
lemma Spec.map_inv {R S : CommRingCat} (f : R ⟶ S) [IsIso f] :
    Spec.map (inv f) = inv (Spec.map f) := by
  change Scheme.Spec.map (inv f).op = inv (Scheme.Spec.map f.op)
  rw [op_inv, ← Scheme.Spec.map_inv]

/-- `Spec R` with the specialization order is order isomorphic to the dual of the prime
spectrum of `R`. -/
@[simps]
/-
**AlgebraicGeometry.specOrderIsoPrimeSpectrum** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry`。
形式化陈述：specOrderIsoPrimeSpectrum (R : CommRingCat) : Spec R ≃o (PrimeSpectrum R)ᵒ
ᵈ where toFun x
参数：R : CommRingCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Spec R` with the specialization order is order isomorphic to the dual of the pr
ime
spectrum of `R`.
-/
def specOrderIsoPrimeSpectrum (R : CommRingCat) : Spec R ≃o (PrimeSpectrum R)ᵒᵈ where
  toFun x := .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := PrimeSpectrum.le_iff_specializes b a

/-- `PrimeSpectrum R` with the inclusion order is order isomorphic to the dual of `Spec R`. -/
@[simps]
/-
**AlgebraicGeometry.primeSpectrumOrderIsoSpec** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry`。
形式化陈述：primeSpectrumOrderIsoSpec (R : Type u) [CommRing R] : PrimeSpectrum R ≃o (
Spec (.of R))ᵒᵈ where toFun x
参数：R : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PrimeSpectrum R` with the inclusion order is order isomorphic to the dual of `S
pec R`.
-/
def primeSpectrumOrderIsoSpec (R : Type u) [CommRing R] : PrimeSpectrum R ≃o (Spec (.of R))ᵒᵈ where
  toFun x := .toDual x
  invFun x := OrderDual.ofDual x
  map_rel_iff' {a b} := (PrimeSpectrum.le_iff_specializes a b).symm

section

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

-- The lemmas below are not tagged simp to respect the abstraction.
/-
**AlgebraicGeometry.Spec_carrier** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Spec_carrier (R : CommRingCat.{u}) : (Spec R).carrier = PrimeSpectrum R
参数：R : CommRingCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec_carrier (R : CommRingCat.{u}) : (Spec R).carrier = PrimeSpectrum R := rfl
/-
**AlgebraicGeometry.Spec_sheaf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Spec_sheaf (R : CommRingCat.{u}) : (Spec R).sheaf = Spec.structureSheaf R
参数：R : CommRingCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec_sheaf (R : CommRingCat.{u}) : (Spec R).sheaf = Spec.structureSheaf R := rfl
/-
**AlgebraicGeometry.Spec_presheaf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Spec_presheaf (R : CommRingCat.{u}) : (Spec R).presheaf = (Spec.structureS
heaf R).1
参数：R : CommRingCat.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec_presheaf (R : CommRingCat.{u}) : (Spec R).presheaf = (Spec.structureSheaf R).1 := rfl
/-
**AlgebraicGeometry.Spec.map_base** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
pec`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S),   (AlgebraicGeometry.Spec.map f).base =
     TopCat.ofHom { toFun := PrimeSpectrum.comap (CommRingCat.Hom.hom f), contin
uous_toFun := ⋯ }
参数：f : R ⟶ S；AlgebraicGeometry.Spec.map f；CommRingCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.map_base : (Spec.map f).base = ofHom ⟨_, PrimeSpectrum.continuous_comap f.hom⟩ := rfl
/-
**AlgebraicGeometry.Spec.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Spec`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S) (x : ↥(AlgebraicGeometry.Spec S)),   (Al
gebraicGeometry.Spec.map f) x = PrimeSpectrum.comap (CommRingCat.Hom.hom f) x
参数：f : R ⟶ S；x : ↥(AlgebraicGeometry.Spec S)；AlgebraicGeometry.Spec.map f；CommRi
ngCat.Hom.hom f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.map_apply (x : Spec S) : Spec.map f x = PrimeSpectrum.comap f.hom x := rfl
/-
**AlgebraicGeometry.Spec.map_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Sp
ec`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S) (U : (AlgebraicGeometry.Spec R).Opens), 
  AlgebraicGeometry.Scheme.Hom.app (AlgebraicGeometry.Spec.map f) U =     CommRi
ngCat.ofHom       (AlgebraicGeometry.StructureSheaf.comap (CommRingCat.Hom.hom f
) U         ((TopologicalSpace.Opens.map (AlgebraicGeometry.Spec.map f).base).ob
j U) ⋯)
参数：f : R ⟶ S；U : (AlgebraicGeometry.Spec R).Opens；AlgebraicGeometry.Spec.map f；A
lgebraicGeometry.StructureSheaf.comap (CommRingCat.Hom.hom f) U         ((Topolo
gicalSpace.Opens.map (AlgebraicGeometry.Spec.map f).base).obj U) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.map_app (U) :
    (Spec.map f).app U =
      CommRingCat.ofHom (StructureSheaf.comap f.hom U (Spec.map f ⁻¹ᵁ U) le_rfl) := rfl
/-
**AlgebraicGeometry.Spec.map_appLE** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.
Spec`。
形式化陈述：∀ {R S : CommRingCat} (f : R ⟶ S) {U : (AlgebraicGeometry.Spec S).Opens} {
V : (AlgebraicGeometry.Spec R).Opens}   (e : U ≤ (TopologicalSpace.Opens.map (Al
gebraicGeometry.Spec.map f).base).obj V),   AlgebraicGeometry.Scheme.Hom.appLE (
AlgebraicGeometry.Spec.map f) V U e =     CommRingCat.ofHom (AlgebraicGeometry.S
tructureSheaf.comap (CommRingCat.Hom.hom f) V U e)
参数：f : R ⟶ S；AlgebraicGeometry.Spec S；AlgebraicGeometry.Spec R；e : U ≤ (Topologi
calSpace.Opens.map (AlgebraicGeometry.Spec.map f).base).obj V；AlgebraicGeometry.
Spec.map f；AlgebraicGeometry.StructureSheaf.comap (CommRingCat.Hom.hom f) V U e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Spec.map_appLE {U V} (e : U ≤ Spec.map f ⁻¹ᵁ V) :
    (Spec.map f).appLE V U e = CommRingCat.ofHom (StructureSheaf.comap f.hom V U e) := rfl
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : CommRingCat} [Nontrivial A] : Nonempty (Spec A) :=
  inferInstanceAs <| Nonempty (PrimeSpectrum A)

end

namespace Scheme

/-
**AlgebraicGeometry.Scheme.isEmpty_of_commSq** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：isEmpty_of_commSq {W X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : W ⟶ 
X} {j : W ⟶ Y} (h : CommSq i j f g) (H : Disjoint (Set.range f) (Set.range g)) :
 IsEmpty W
参数：h : CommSq i j f g；H : Disjoint (Set.range f) (Set.range g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isEmpty_of_commSq {W X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : W ⟶ X} {j : W ⟶ Y} (h : CommSq i j f g)
    (H : Disjoint (Set.range f) (Set.range g)) : IsEmpty W :=
  ⟨fun x ↦ (Set.disjoint_iff_inter_eq_empty.mp H).le
    ⟨⟨i x, congr($(h.w) x)⟩, ⟨j x, rfl⟩⟩⟩

/-- The empty scheme. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.empty** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sc
heme`。
形式化陈述：empty : Scheme where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty scheme.
-/
def empty : Scheme where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x
  local_affine x := PEmpty.elim x
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmptyCollection Scheme :=
  ⟨empty⟩

/-- The global sections as a functor. For the global section themselves, use `Γ(X, ⊤)` instead. -/
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global sections as a functor. For the global section themselves, use `Γ(X, ⊤
)` instead.
-/
def Γ : Schemeᵒᵖ ⥤ CommRingCat :=
  Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_def : Γ = Scheme.forgetToLocallyRingedSpace.op ⋙ LocallyRingedSpace.Γ :=
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_obj (X : Schemeᵒᵖ) : Γ.obj X = Γ(unop X, ⊤) :=
  rfl
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_obj_op (X : Scheme) : Γ.obj (op X) = Γ(X, ⊤) :=
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_map {X Y : Schemeᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.appTop :=
  rfl
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_map_op {X Y : Scheme} (f : X ⟶ Y) : Γ.map f.op = f.appTop :=
  rfl

/--
The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` as a natural isomorphism.
This is almost never needed in practical use cases. Use `ΓSpecIso` instead.
-/
/-
**AlgebraicGeometry.Scheme.Spec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sch
eme`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ AlgebraicGeometry.Scheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit (`SpecΓIdentity.inv.op`) of the adjunction `Γ ⊣ Spec` as a natural is
omorphism.
This is almost never needed in practical use cases. Use `ΓSpecIso` instead.
-/
def SpecΓIdentity : Scheme.Spec.rightOp ⋙ Scheme.Γ ≅ 𝟭 _ :=
  LocallyRingedSpace.SpecΓIdentity

variable (R : CommRingCat.{u})

/-- The global sections of `Spec R` is isomorphic to `R`. -/
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global sections of `Spec R` is isomorphic to `R`.
-/
def ΓSpecIso : Γ(Spec R, ⊤) ≅ R := SpecΓIdentity.app R
/-
**AlgebraicGeometry.Scheme.Spec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sch
eme`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ AlgebraicGeometry.Scheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma SpecΓIdentity_app : SpecΓIdentity.app R = ΓSpecIso R := rfl
/-
**AlgebraicGeometry.Scheme.Spec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sch
eme`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ AlgebraicGeometry.Scheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma SpecΓIdentity_hom_app : SpecΓIdentity.hom.app R = (ΓSpecIso R).hom := rfl
/-
**AlgebraicGeometry.Scheme.Spec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sch
eme`。
形式化陈述：CategoryTheory.Functor CommRingCatᵒᵖ AlgebraicGeometry.Scheme
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma SpecΓIdentity_inv_app : SpecΓIdentity.inv.app R = (ΓSpecIso R).inv := rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ΓSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecIso R).hom ≫ f := SpecΓIdentity.hom.naturality f

-- The RHS is not necessarily simpler than the LHS, but this direction coincides with the simp
-- direction of `NatTrans.naturality`.
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ΓSpecIso_inv_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ (ΓSpecIso S).inv = (ΓSpecIso R).inv ≫ (Spec.map f).appTop := SpecΓIdentity.inv.naturality f

set_option backward.isDefEq.respectTransparency.types false in
-- This is not marked simp to respect the abstraction
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ΓSpecIso_inv : (ΓSpecIso R).inv = CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.toOpen_eq** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometr
y.Scheme`。
形式化陈述：toOpen_eq (U) : CommRingCat.ofHom (algebraMap R <| (Spec.structureSheaf R)
.presheaf.obj (.op U)) = (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_to
p).op
参数：U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toOpen_eq (U) :
    CommRingCat.ofHom (algebraMap R <| (Spec.structureSheaf R).presheaf.obj (.op U)) =
    (ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op := rfl
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K} [Field K] : Unique <| Spec <| .of K :=
  inferInstanceAs <| Unique (PrimeSpectrum K)

@[simp]
/-
**AlgebraicGeometry.Scheme.default_asIdeal** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：default_asIdeal {K} [Field K] : (default : Spec (.of K)).asIdeal = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma default_asIdeal {K} [Field K] : (default : Spec (.of K)).asIdeal = ⊥ := rfl

section BasicOpen

variable (X : Scheme) {V U : X.Opens} (f g : Γ(X, U))

/-- The subset of the underlying space where the given section does not vanish. -/
/-
**AlgebraicGeometry.Scheme.basicOpen** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme`。
形式化陈述：basicOpen : X.Opens
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subset of the underlying space where the given section does not vanish.
-/
def basicOpen : X.Opens :=
  X.toLocallyRingedSpace.toRingedSpace.basicOpen f
/-
**AlgebraicGeometry.Scheme.mem_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：mem_basicOpen (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit (X.presh
eaf.germ U x hx f)
参数：x : X；hx : x in U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
-/
theorem mem_basicOpen (x : X) (hx : x ∈ U) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f) :=
  RingedSpace.mem_basicOpen _ _ _ _

/-- A variant of `mem_basicOpen` for bundled `x : U`. -/
@[simp]
/-
**AlgebraicGeometry.Scheme.mem_basicOpen'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：mem_basicOpen' (x : U) : ↑x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x
 x.2 f)
参数：x : U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
A variant of `mem_basicOpen` for bundled `x : U`.
-/
theorem mem_basicOpen' (x : U) : ↑x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x x.2 f) :=
  RingedSpace.mem_basicOpen _ _ _ _

/-- A variant of `mem_basicOpen` without the `x ∈ U` assumption. -/
/-
**AlgebraicGeometry.Scheme.mem_basicOpen''** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：mem_basicOpen'' {U : X.Opens} (f : Γ(X, U)) (x : X) : x in X.basicOpen f ↔
 exists (m : x in U), IsUnit (X.presheaf.germ U x m f)
参数：f : Γ(X, U)；x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A variant of `mem_basicOpen` without the `x ∈ U` assumption.
-/
theorem mem_basicOpen'' {U : X.Opens} (f : Γ(X, U)) (x : X) :
    x ∈ X.basicOpen f ↔ ∃ (m : x ∈ U), IsUnit (X.presheaf.germ U x m f) :=
  Iff.rfl
/-
**AlgebraicGeometry.Scheme.mem_basicOpen_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：mem_basicOpen_top (f : Γ(X, ⊤)) (x : X) : x in X.basicOpen f ↔ IsUnit (X.p
resheaf.germ ⊤ x trivial f)
参数：f : Γ(X, ⊤)；x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_top_basicOpen`：mem_top_basicOpen (f : 
X.presheaf.obj (op ⊤)) (x : X) : x in X.basicOpen f ↔ IsUnit (X.presheaf.Γgerm x
 f)
-/
theorem mem_basicOpen_top (f : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ ⊤ x trivial f) :=
  RingedSpace.mem_top_basicOpen _ f x

@[simp]
/-
**AlgebraicGeometry.Scheme.basicOpen_res** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.presheaf.map i f) = V ⊓ X
.basicOpen f
参数：i : op U ⟶ op V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_res`：basicOpen_res {U V : (Opens
 X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) : @basicOpen X (unop V) (X.presheaf.ma
p i f) = unop V ⊓ @basicOpen X (u…
-/
theorem basicOpen_res (i : op U ⟶ op V) : X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f :=
  RingedSpace.basicOpen_res _ i f

-- This should fire before `basicOpen_res`.
@[simp 1100]
/-
**AlgebraicGeometry.Scheme.basicOpen_res_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：basicOpen_res_eq (i : op U ⟶ op V) [IsIso i] : X.basicOpen (X.presheaf.map
 i f) = X.basicOpen f
参数：i : op U ⟶ op V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_res_eq`：basicOpen_res_eq {U V : 
(Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.presheaf.obj U) : @basicOpen X (unop V
) (X.presheaf.map i f) = @RingedSpac…
-/
theorem basicOpen_res_eq (i : op U ⟶ op V) [IsIso i] :
    X.basicOpen (X.presheaf.map i f) = X.basicOpen f :=
  RingedSpace.basicOpen_res_eq _ i f

@[sheaf_restrict]
/-
**AlgebraicGeometry.Scheme.basicOpen_le** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：basicOpen_le : X.basicOpen f <= U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_le`：basicOpen_le {U : Opens X} (
f : X.presheaf.obj (op U)) : X.basicOpen f <= U
-/
theorem basicOpen_le : X.basicOpen f ≤ U :=
  RingedSpace.basicOpen_le _ _

@[sheaf_restrict]
/-
**AlgebraicGeometry.Scheme.basicOpen_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：basicOpen_restrict (i : V ⟶ U) (f : Γ(X, U)) : X.basicOpen (TopCat.Preshea
f.restrict f i) <= X.basicOpen f
参数：i : V ⟶ U；f : Γ(X, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma basicOpen_restrict (i : V ⟶ U) (f : Γ(X, U)) :
    X.basicOpen (TopCat.Presheaf.restrict f i) ≤ X.basicOpen f :=
  (Scheme.basicOpen_res _ _ _).trans_le inf_le_right

@[simp]
/-
**AlgebraicGeometry.Scheme.preimage_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：preimage_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, 
U)) : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app U r)
参数：f : X ⟶ Y；r : Γ(Y, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.preimage_basicOpen`：preimage_basicO
pen {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y} (s : Y.presheaf.obj
 (op U)) : (Opens.map f.base).obj (Y.toRinged…
-/
theorem preimage_basicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) :
    f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app U r) :=
  LocallyRingedSpace.preimage_basicOpen f.toLRSHom r

alias Hom.preimage_basicOpen := preimage_basicOpen
/-
**AlgebraicGeometry.Scheme.preimage_basicOpen_top** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：preimage_basicOpen_top {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) : f ⁻¹
ᵁ Y.basicOpen r = X.basicOpen (f.appTop r)
参数：f : X ⟶ Y；r : Γ(Y, ⊤)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
-/
theorem preimage_basicOpen_top {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.appTop r) :=
  preimage_basicOpen ..

alias Hom.preimage_basicOpen_top := preimage_basicOpen_top
/-
**AlgebraicGeometry.Scheme.basicOpen_appLE** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
 (e : U <= f ⁻¹ᵁ V) (s : Γ(Y, V)) : X.basicOpen (f.appLE V U e s) = U ⊓ f ⁻¹ᵁ (Y
.basicOpen s)
参数：f : X ⟶ Y；U : X.Opens；V : Y.Opens；e : U <= f ⁻¹ᵁ V；s : Γ(Y, V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
-/
lemma basicOpen_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e : U ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : X.basicOpen (f.appLE V U e s) = U ⊓ f ⁻¹ᵁ (Y.basicOpen s) := by
  simp only [preimage_basicOpen, Hom.appLE, CommRingCat.comp_apply]
  rw [basicOpen_res]

@[simp]
/-
**AlgebraicGeometry.Scheme.basicOpen_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：basicOpen_zero (U : X.Opens) : X.basicOpen (0 : Γ(X, U)) = ⊥
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.basicOpen_zero`：basicOpen_zero (X :
 LocallyRingedSpace.{u}) (U : Opens X.carrier) : X.toRingedSpace.basicOpen (0 : 
X.presheaf.obj <| op U) = ⊥
-/
theorem basicOpen_zero (U : X.Opens) : X.basicOpen (0 : Γ(X, U)) = ⊥ :=
  LocallyRingedSpace.basicOpen_zero _ U

@[simp]
/-
**AlgebraicGeometry.Scheme.basicOpen_mul** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_mul`：basicOpen_mul {U : Opens X}
 (f g : X.presheaf.obj (op U)) : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOp
en g
-/
theorem basicOpen_mul : X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g :=
  RingedSpace.basicOpen_mul _ _ _
/-
**AlgebraicGeometry.Scheme.basicOpen_pow** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：basicOpen_pow {n : Nat} (h : 0 < n) : X.basicOpen (f ^ n) = X.basicOpen f
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.RingedSpace.basicOpen_pow`：basicOpen_pow {U : Opens X}
 (f : X.presheaf.obj (op U)) (n : Nat) (h : 0 < n) : X.basicOpen (f ^ n) = X.bas
icOpen f
-/
lemma basicOpen_pow {n : ℕ} (h : 0 < n) : X.basicOpen (f ^ n) = X.basicOpen f :=
  RingedSpace.basicOpen_pow _ _ _ h
/-
**AlgebraicGeometry.Scheme.basicOpen_add_le** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：basicOpen_add_le : X.basicOpen (f + g) <= X.basicOpen f ⊔ X.basicOpen g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.mem_basicOpen`：mem_basicOpen (x : X) (hx : x in
 U) : x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f)
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`：isUnit_or_isUnit_of_isUnit_a
dd {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
lemma basicOpen_add_le :
    X.basicOpen (f + g) ≤ X.basicOpen f ⊔ X.basicOpen g := by
  intro x hx
  have hxU : x ∈ U := X.basicOpen_le _ hx
  simp_rw [← SetLike.mem_coe, Opens.coe_sup, Set.mem_union, SetLike.mem_coe] -- TODO : Opens.mem_sup
  simp only [Scheme.mem_basicOpen _ _ _ hxU, map_add] at hx ⊢
  exact IsLocalRing.isUnit_or_isUnit_of_isUnit_add hx
/-
**AlgebraicGeometry.Scheme.basicOpen_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：basicOpen_of_isUnit {f : Γ(X, U)} (hf : IsUnit f) : X.basicOpen f = U
参数：X, U；hf : IsUnit f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_of_isUnit`：basicOpen_of_isUnit {
U : Opens X} {f : X.presheaf.obj (op U)} (hf : IsUnit f) : X.basicOpen f = U
-/
theorem basicOpen_of_isUnit {f : Γ(X, U)} (hf : IsUnit f) : X.basicOpen f = U :=
  RingedSpace.basicOpen_of_isUnit _ hf

@[simp]
/-
**AlgebraicGeometry.Scheme.basicOpen_one** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：basicOpen_one : X.basicOpen (1 : Γ(X, U)) = U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_of_isUnit`：basicOpen_of_isUnit {f : Γ
(X, U)} (hf : IsUnit f) : X.basicOpen f = U
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem basicOpen_one : X.basicOpen (1 : Γ(X, U)) = U :=
  X.basicOpen_of_isUnit isUnit_one
/-
**AlgebraicGeometry.Scheme.algebra_section_section_basicOpen** 是 Mathlib 中的一个实例，
位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：algebra_section_section_basicOpen {X : Scheme} {U : X.Opens} (f : Γ(X, U))
 : Algebra Γ(X, U) Γ(X, X.basicOpen f)
参数：f : Γ(X, U)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
-/
instance algebra_section_section_basicOpen {X : Scheme} {U : X.Opens} (f : Γ(X, U)) :
    Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
  (X.presheaf.map (homOfLE <| X.basicOpen_le f : _ ⟶ U).op).hom.toAlgebra

@[simp]
/-
**AlgebraicGeometry.Scheme._root_.AlgebraicGeometry.SpecMap_preimage_basicOpen**
 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.SpecMap_preimage_basicOpen {R S : CommRingCat} (f : R ⟶ S) (r : R) :
    Spec.map f ⁻¹ᵁ PrimeSpectrum.basicOpen r = PrimeSpectrum.basicOpen (f r) := rfl

end BasicOpen

section ZeroLocus

variable (X : Scheme.{u})

/--
The zero locus of a set of sections `s` over an open set `U` is the closed set consisting of
the complement of `U` and of all points of `U`, where all elements of `f` vanish.
-/
/-
**AlgebraicGeometry.Scheme.zeroLocus** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme`。
形式化陈述：zeroLocus {U : X.Opens} (s : Set Γ(X, U)) : Set X
参数：s : Set Γ(X, U)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero locus of a set of sections `s` over an open set `U` is the closed set c
onsisting of
the complement of `U` and of all points of `U`, where all elements of `f` vanish
.
-/
def zeroLocus {U : X.Opens} (s : Set Γ(X, U)) : Set X := X.toRingedSpace.zeroLocus s
/-
**AlgebraicGeometry.Scheme.zeroLocus_def** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：zeroLocus_def {U : X.Opens} (s : Set Γ(X, U)) : X.zeroLocus s = ⋂ f in s, 
(X.basicOpen f).carrierᶜ
参数：s : Set Γ(X, U)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zeroLocus_def {U : X.Opens} (s : Set Γ(X, U)) :
    X.zeroLocus s = ⋂ f ∈ s, (X.basicOpen f).carrierᶜ :=
  rfl
/-
**AlgebraicGeometry.Scheme.zeroLocus_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：zeroLocus_isClosed {U : X.Opens} (s : Set Γ(X, U)) : IsClosed (X.zeroLocus
 s)
参数：s : Set Γ(X, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.RingedSpace.zeroLocus_isClosed`：zeroLocus_isClosed {U 
: Opens X} (s : Set (X.presheaf.obj (op U))) : IsClosed (X.zeroLocus s)
-/
lemma zeroLocus_isClosed {U : X.Opens} (s : Set Γ(X, U)) :
    IsClosed (X.zeroLocus s) :=
  X.toRingedSpace.zeroLocus_isClosed s
/-
**AlgebraicGeometry.Scheme.zeroLocus_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：zeroLocus_singleton {U : X.Opens} (f : Γ(X, U)) : X.zeroLocus {f} = (↑(X.b
asicOpen f))ᶜ
参数：f : Γ(X, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.RingedSpace.zeroLocus_singleton`：zeroLocus_singleton {
U : Opens X} (f : X.presheaf.obj (op U)) : X.zeroLocus {f} = (X.basicOpen f).car
rierᶜ
-/
lemma zeroLocus_singleton {U : X.Opens} (f : Γ(X, U)) :
    X.zeroLocus {f} = (↑(X.basicOpen f))ᶜ :=
  X.toRingedSpace.zeroLocus_singleton f

@[simp]
/-
**AlgebraicGeometry.Scheme.zeroLocus_empty_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：zeroLocus_empty_eq_univ {U : X.Opens} : X.zeroLocus (∅ : Set Γ(X, U)) = Se
t.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.RingedSpace.zeroLocus_empty_eq_univ`：zeroLocus_empty_e
q_univ {U : Opens X} : X.zeroLocus (∅ : Set (X.presheaf.obj (op U))) = Set.univ
-/
lemma zeroLocus_empty_eq_univ {U : X.Opens} :
    X.zeroLocus (∅ : Set Γ(X, U)) = Set.univ :=
  X.toRingedSpace.zeroLocus_empty_eq_univ

@[simp]
/-
**AlgebraicGeometry.Scheme.mem_zeroLocus_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：mem_zeroLocus_iff {U : X.Opens} (s : Set Γ(X, U)) (x : X) : x in X.zeroLoc
us s ↔ forall f in s, x ∉ X.basicOpen f
参数：s : Set Γ(X, U)；x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.RingedSpace.mem_zeroLocus_iff`：mem_zeroLocus_iff {U : 
Opens X} (s : Set (X.presheaf.obj (op U))) (x : X) : x in X.zeroLocus s ↔ forall
 f in s, x ∉ X.basicOpen f
-/
lemma mem_zeroLocus_iff {U : X.Opens} (s : Set Γ(X, U)) (x : X) :
    x ∈ X.zeroLocus s ↔ ∀ f ∈ s, x ∉ X.basicOpen f :=
  X.toRingedSpace.mem_zeroLocus_iff s x
/-
**AlgebraicGeometry.Scheme.codisjoint_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：codisjoint_zeroLocus {U : X.Opens} (s : Set Γ(X, U)) : Codisjoint (X.zeroL
ocus s) U
参数：s : Set Γ(X, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
lemma codisjoint_zeroLocus {U : X.Opens}
    (s : Set Γ(X, U)) : Codisjoint (X.zeroLocus s) U := by
  have (x : X) : ∀ f ∈ s, x ∈ X.basicOpen f → x ∈ U := fun _ _ h ↦ X.basicOpen_le _ h
  simpa [codisjoint_iff_le_sup, Set.ext_iff, or_iff_not_imp_left]
/-
**AlgebraicGeometry.Scheme.zeroLocus_span** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：zeroLocus_span {U : X.Opens} (s : Set Γ(X, U)) : X.zeroLocus (U
参数：s : Set Γ(X, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_zero`：basicOpen_zero (U : X.Opens) : 
X.basicOpen (0 : Γ(X, U)) = ⊥
· 使用定理 `not_false`：¬False
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `AlgebraicGeometry.Scheme.basicOpen_add_le`：basicOpen_add_le : X.basicOpe
n (f + g) <= X.basicOpen f ⊔ X.basicOpen g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_mul`：basicOpen_mul : X.basicOpen (f *
 g) = X.basicOpen f ⊓ X.basicOpen g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma zeroLocus_span {U : X.Opens} (s : Set Γ(X, U)) :
    X.zeroLocus (U := U) (Ideal.span s) = X.zeroLocus s := by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  refine ⟨fun H f hfs ↦ H f (Ideal.subset_span hfs), fun H f ↦ Submodule.span_induction H ?_ ?_ ?_⟩
  · simp only [Scheme.basicOpen_zero]; exact not_false
  · exact fun a b _ _ ha hb H ↦ (X.basicOpen_add_le a b H).elim ha hb
  · simp +contextual

open scoped Pointwise in
/-
**AlgebraicGeometry.Scheme.zeroLocus_setMul** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：zeroLocus_setMul {U : X.Opens} (s t : Set Γ(X, U)) : X.zeroLocus (s * t) =
 X.zeroLocus s union X.zeroLocus t
参数：s t : Set Γ(X, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.biInter_image2`：biInter_image2 (s : Set α) (t : Set β) (f : α -> β -
> γ) (g : γ -> Set δ) : ⋂ c in image2 f s t, g c = ⋂ a in s, ⋂ b in t, g (f a b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_mul`：basicOpen_mul : X.basicOpen (f *
 g) = X.basicOpen f ⊓ X.basicOpen g
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeroLocus_setMul {U : X.Opens} (s t : Set Γ(X, U)) :
    X.zeroLocus (s * t) = X.zeroLocus s ∪ X.zeroLocus t := by
  simp only [← Set.image2_mul, zeroLocus_def, Set.biInter_image2]
  simp [Set.compl_inter, ← Set.union_iInter₂, ← Set.iInter₂_union]

open scoped Pointwise in
/-
**AlgebraicGeometry.Scheme.zeroLocus_mul** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：zeroLocus_mul {U : X.Opens} (I J : Ideal Γ(X, U)) : X.zeroLocus (U
参数：I J : Ideal Γ(X, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.zeroLocus_setMul`：zeroLocus_setMul {U : X.Opens
} (s t : Set Γ(X, U)) : X.zeroLocus (s * t) = X.zeroLocus s union X.zeroLocus t
· 使用引理 `AlgebraicGeometry.Scheme.zeroLocus_span`：zeroLocus_span {U : X.Opens} (s
 : Set Γ(X, U)) : X.zeroLocus (U
· 使用定理 `Ideal.span_mul_span`：span_mul_span (S T : Set R) [(span S).IsTwoSided] :
 span S * span T = span (S * T)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeroLocus_mul {U : X.Opens} (I J : Ideal Γ(X, U)) :
    X.zeroLocus (U := U) ↑(I * J) = X.zeroLocus (U := U) I ∪ X.zeroLocus (U := U) J := by
  rw [← X.zeroLocus_setMul, ← X.zeroLocus_span (U := U) (↑I * ↑J), ← Ideal.span_mul_span]
  simp
/-
**AlgebraicGeometry.Scheme.zeroLocus_map** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：zeroLocus_map {U V : X.Opens} (i : U <= V) (s : Set Γ(X, V)) : X.zeroLocus
 ((X.presheaf.map (homOfLE i).op).hom '' s) = X.zeroLocus s union Uᶜ
参数：i : U <= V；s : Set Γ(X, V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
-/
lemma zeroLocus_map {U V : X.Opens} (i : U ≤ V) (s : Set Γ(X, V)) :
    X.zeroLocus ((X.presheaf.map (homOfLE i).op).hom '' s) = X.zeroLocus s ∪ Uᶜ := by
  ext x
  suffices (∀ f ∈ s, x ∈ U → x ∉ X.basicOpen f) ↔ x ∈ U → (∀ f ∈ s, x ∉ X.basicOpen f) by
    simpa [or_iff_not_imp_right]
  grind
/-
**AlgebraicGeometry.Scheme.zeroLocus_map_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：zeroLocus_map_of_eq {U V : X.Opens} (i : U = V) (s : Set Γ(X, V)) : X.zero
Locus ((X.presheaf.map (eqToHom i).op).hom '' s) = X.zeroLocus s
参数：i : U = V；s : Set Γ(X, V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res_eq`：basicOpen_res_eq (i : op U ⟶ 
op V) [IsIso i] : X.basicOpen (X.presheaf.map i f) = X.basicOpen f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma zeroLocus_map_of_eq {U V : X.Opens} (i : U = V) (s : Set Γ(X, V)) :
    X.zeroLocus ((X.presheaf.map (eqToHom i).op).hom '' s) = X.zeroLocus s := by
  ext; simp
/-
**AlgebraicGeometry.Scheme.zeroLocus_mono** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：zeroLocus_mono {U : X.Opens} {s t : Set Γ(X, U)} (h : s subseteq t) : X.ze
roLocus t subseteq X.zeroLocus s
参数：X, U；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma zeroLocus_mono {U : X.Opens} {s t : Set Γ(X, U)} (h : s ⊆ t) :
    X.zeroLocus t ⊆ X.zeroLocus s := by
  simp only [Set.subset_def, Scheme.mem_zeroLocus_iff]
  exact fun x H f hf hxf ↦ H f (h hf) hxf
/-
**AlgebraicGeometry.Scheme.preimage_zeroLocus** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：preimage_zeroLocus {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (s : Set Γ
(Y, U)) : f ⁻¹' Y.zeroLocus s = X.zeroLocus ((f.app U).hom '' s)
参数：f : X ⟶ Y；s : Set Γ(Y, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma preimage_zeroLocus {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (s : Set Γ(Y, U)) :
    f ⁻¹' Y.zeroLocus s = X.zeroLocus ((f.app U).hom '' s) := by
  ext
  simp [← Scheme.preimage_basicOpen]

@[simp]
/-
**AlgebraicGeometry.Scheme.zeroLocus_univ** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：zeroLocus_univ {U : X.Opens} : X.zeroLocus (U
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_of_isUnit`：basicOpen_of_isUnit {f : Γ
(X, U)} (hf : IsUnit f) : X.basicOpen f = U
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
lemma zeroLocus_univ {U : X.Opens} :
    X.zeroLocus (U := U) Set.univ = (↑U)ᶜ := by
  ext x
  simp only [Scheme.mem_zeroLocus_iff, Set.mem_univ, forall_const, Set.mem_compl_iff,
    SetLike.mem_coe, ← not_exists, not_iff_not]
  exact ⟨fun ⟨f, hf⟩ ↦ X.basicOpen_le f hf, fun _ ↦ ⟨1, by rwa [X.basicOpen_of_isUnit isUnit_one]⟩⟩
/-
**AlgebraicGeometry.Scheme.zeroLocus_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：zeroLocus_iUnion {U : X.Opens} {ι : Type*} (f : ι -> Set Γ(X, U)) : X.zero
Locus (⋃ i, f i) = ⋂ i, X.zeroLocus (f i)
参数：f : ι -> Set Γ(X, U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_comm`：iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i'
 = ⋂ (i') (i), s i i'
-/
lemma zeroLocus_iUnion {U : X.Opens} {ι : Type*} (f : ι → Set Γ(X, U)) :
    X.zeroLocus (⋃ i, f i) = ⋂ i, X.zeroLocus (f i) := by
  simpa [zeroLocus, AlgebraicGeometry.RingedSpace.zeroLocus] using Set.iInter_comm _
/-
**AlgebraicGeometry.Scheme.zeroLocus_radical** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：zeroLocus_radical {U : X.Opens} (I : Ideal Γ(X, U)) : X.zeroLocus (U
参数：I : Ideal Γ(X, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `AlgebraicGeometry.Scheme.zeroLocus_mono`：zeroLocus_mono {U : X.Opens} {s
 t : Set Γ(X, U)} (h : s subseteq t) : X.zeroLocus t subseteq X.zeroLocus s
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.basicOpen_pow`：basicOpen_pow {n : Nat} (h : 0 <
 n) : X.basicOpen (f ^ n) = X.basicOpen f
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
/-
**AlgebraicGeometry.basicOpen_eq_of_affine** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry`。
形式化陈述：basicOpen_eq_of_affine {R : CommRingCat} (f : R) : (Spec R).basicOpen ((Sc
heme.ΓSpecIso R).inv f) = PrimeSpectrum.basicOpen f
参数：f : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `trivial`：True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `IsLocalization.AtPrime.isUnit_to_map_iff`：isUnit_to_map_iff (x : R) : Is
Unit ((algebraMap R S) x) ↔ x in I.primeCompl
-/
theorem basicOpen_eq_of_affine {R : CommRingCat} (f : R) :
    (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpectrum.basicOpen f := by
  ext x
  simp only [SetLike.mem_coe, Scheme.mem_basicOpen_top]
  suffices IsUnit (algebraMap _ ((structurePresheafInCommRingCat ↑R).stalk x) f) ↔
    f ∉ PrimeSpectrum.asIdeal x by exact this
  rw [← isUnit_map_iff (StructureSheaf.stalkIso R x).symm, AlgEquiv.commutes]
  exact IsLocalization.AtPrime.isUnit_to_map_iff _ (PrimeSpectrum.asIdeal x) f

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.basicOpen_eq_of_affine'** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：basicOpen_eq_of_affine' {R : CommRingCat} (f : Γ(Spec R, ⊤)) : (Spec R).ba
sicOpen f = PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso R).hom f)
参数：f : Γ(Spec R, ⊤)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `AlgebraicGeometry.basicOpen_eq_of_affine`：basicOpen_eq_of_affine {R : Co
mmRingCat} (f : R) : (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv f) = PrimeSpect
rum.basicOpen f
-/
theorem basicOpen_eq_of_affine' {R : CommRingCat} (f : Γ(Spec R, ⊤)) :
    (Spec R).basicOpen f = PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso R).hom f) := by
  convert! basicOpen_eq_of_affine ((Scheme.ΓSpecIso R).hom f)
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso R) f).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.SpecMap_presheaf_map_eqToHom** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (h : U = V)   (W : (Algeb
raicGeometry.Spec (X.presheaf.obj (Opposite.op V))).Opens),   AlgebraicGeometry.
Scheme.Hom.app (AlgebraicGeometry.Spec.map (X.presheaf.map (CategoryTheory.eqToH
om h).op)) W =     CategoryTheory.eqToHom ⋯
参数：h : U = V；W : (AlgebraicGeometry.Spec (X.presheaf.obj (Opposite.op V))).Opens
；AlgebraicGeometry.Spec.map (X.presheaf.map (CategoryTheory.eqToHom h).op)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.congr_app`：congr_app {X Y : Scheme} {f g : 
X ⟶ Y} (e : f = g) (U) : f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e
; rfl)).op
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `TopologicalSpace.Opens.map_id_obj`：map_id_obj (U : Opens X) : (map (𝟙 X)
).obj U = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_naturality`：eqToHom_naturality {f g : β -> C} (z 
: forall b, f b ⟶ g b) {j j' : β} (w : j = j') : z j ≫ eqToHom (by simp [w]) = e
qToHom (by simp [w]) ≫ …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem Scheme.SpecMap_presheaf_map_eqToHom {X : Scheme} {U V : X.Opens} (h : U = V) (W) :
    (Spec.map (X.presheaf.map (eqToHom h).op)).app W = eqToHom (by cases h; simp) := by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]
  cases h
  refine (Scheme.Hom.congr_app this _).trans ?_
  simp [eqToHom_map]
/-
**AlgebraicGeometry.germ_eq_zero_of_pow_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：germ_eq_zero_of_pow_mul_eq_zero {X : Scheme.{u}} {U : Opens X} (x : U) {f 
s : Γ(X, U)} (hx : x.val in X.basicOpen s) {n : Nat} (hf : s ^ n * f = 0) : X.pr
esheaf.germ U x x.2 f = 0
参数：x : U；X, U；hx : x.val in X.basicOpen s；hf : s ^ n * f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `AlgebraicGeometry.Scheme.mem_basicOpen`：mem_basicOpen (x : X) (hx : x in
 U) : x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_right_eq_zero`：mul_right_eq_zero {a b : M₀} (ha : IsUnit a) :
 a * b = 0 ↔ b = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
lemma germ_eq_zero_of_pow_mul_eq_zero {X : Scheme.{u}} {U : Opens X} (x : U) {f s : Γ(X, U)}
    (hx : x.val ∈ X.basicOpen s) {n : ℕ} (hf : s ^ n * f = 0) : X.presheaf.germ U x x.2 f = 0 := by
  rw [Scheme.mem_basicOpen X s x x.2] at hx
  have hu : IsUnit (X.presheaf.germ _ x x.2 (s ^ n)) := by
    rw [map_pow]
    exact IsUnit.pow n hx
  rw [← hu.mul_right_eq_zero, ← map_mul, hf, map_zero]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.hom_base_inv_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (e : X ≅ Y),   CategoryTheory.CategoryS
truct.comp e.hom.base e.inv.base = CategoryTheory.CategoryStruct.id ↑X.toPreshea
fedSpace
参数：e : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.iso_hom_base_inv_base`：iso_hom_base
_inv_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) : e.hom.base ≫ e.inv.base =
 𝟙 _
-/
lemma Scheme.hom_base_inv_base {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.hom.base ≫ e.inv.base = 𝟙 _ :=
  LocallyRingedSpace.iso_hom_base_inv_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]
/-
**AlgebraicGeometry.Scheme.hom_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (e : X ≅ Y) (x : ↥X), e.inv (e.hom x) =
 x
参数：e : X ≅ Y；x : ↥X；e.hom x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    e.inv (e.hom x) = x := by
  change (e.hom ≫ e.inv) x = 𝟙 X.toPresheafedSpace x
  simp

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.inv_base_hom_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (e : X ≅ Y),   CategoryTheory.CategoryS
truct.comp e.inv.base e.hom.base = CategoryTheory.CategoryStruct.id ↑Y.toPreshea
fedSpace
参数：e : X ≅ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.iso_inv_base_hom_base`：iso_inv_base
_hom_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) : e.inv.base ≫ e.hom.base =
 𝟙 _
-/
lemma Scheme.inv_base_hom_base {X Y : Scheme.{u}} (e : X ≅ Y) :
    e.inv.base ≫ e.hom.base = 𝟙 _ :=
  LocallyRingedSpace.iso_inv_base_hom_base (Scheme.forgetToLocallyRingedSpace.mapIso e)

@[simp]
/-
**AlgebraicGeometry.Scheme.inv_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (e : X ≅ Y) (y : ↥Y), e.hom (e.inv y) =
 y
参数：e : X ≅ Y；y : ↥Y；e.inv y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (y : Y) :
    e.hom (e.inv y) = y := by
  change (e.inv ≫ e.hom) y = 𝟙 Y.toPresheafedSpace y
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Spec_zeroLocus_eq_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：Spec_zeroLocus_eq_zeroLocus {R : CommRingCat} (s : Set R) : (Spec R).zeroL
ocus ((Scheme.ΓSpecIso R).inv '' s) = PrimeSpectrum.zeroLocus s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PrimeSpectrum.mem_basicOpen`：mem_basicOpen (f : R) (x : PrimeSpectrum R)
 : x in basicOpen f ↔ f ∉ x.asIdeal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `AlgebraicGeometry.basicOpen_eq_of_affine'`：basicOpen_eq_of_affine' {R : 
CommRingCat} (f : Γ(Spec R, ⊤)) : (Spec R).basicOpen f = PrimeSpectrum.basicOpen
 ((Scheme.ΓSpecIso R).hom f)
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
-/
theorem Spec_zeroLocus_eq_zeroLocus {R : CommRingCat} (s : Set R) :
    (Spec R).zeroLocus ((Scheme.ΓSpecIso R).inv '' s) = PrimeSpectrum.zeroLocus s := by
  ext x
  suffices (∀ a ∈ s, x ∉ PrimeSpectrum.basicOpen a) ↔ x ∈ PrimeSpectrum.zeroLocus s by simpa
  simp [Spec_carrier, PrimeSpectrum.mem_zeroLocus, Set.subset_def,
    PrimeSpectrum.mem_basicOpen _ x]
/-
**AlgebraicGeometry.Spec_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：Spec_zeroLocus {R : CommRingCat} (s : Set Γ(Spec R, ⊤)) : (Spec R).zeroLoc
us s = PrimeSpectrum.zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s)
参数：s : Set Γ(Spec R, ⊤)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.ConcreteCategory.bijective_of_isIso`：bijective_of_isIso {
X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `AlgebraicGeometry.Spec_zeroLocus_eq_zeroLocus`：Spec_zeroLocus_eq_zeroLoc
us {R : CommRingCat} (s : Set R) : (Spec R).zeroLocus ((Scheme.ΓSpecIso R).inv '
' s) = PrimeSpectrum.zeroLocus s
-/
theorem Spec_zeroLocus {R : CommRingCat} (s : Set Γ(Spec R, ⊤)) :
    (Spec R).zeroLocus s = PrimeSpectrum.zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s) := by
  convert! Spec_zeroLocus_eq_zeroLocus ((Scheme.ΓSpecIso R).inv ⁻¹' s)
  rw [Set.image_preimage_eq]
  exact (ConcreteCategory.bijective_of_isIso (C := CommRingCat) _).2
section Stalks

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-
**AlgebraicGeometry.Scheme.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Sch
eme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x) : IsLocalHom (f.stalkMap x).hom :=
  f.prop x

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：stalkMap_id (X : Scheme.{u}) (x : X) : (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.pre
sheaf.stalk x)
参数：X : Scheme.{u}；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.id`：id (X : PresheafedSpace.{
_, _, v} C) (x : X) : (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x)
-/
lemma stalkMap_id (X : Scheme.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  PresheafedSpace.stalkMap.id _ x
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：stalkMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ 
g : X ⟶ Z).stalkMap x = g.stalkMap (f x) ≫ f.stalkMap x
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.comp`：comp {X Y Z : Presheafe
dSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) : (α ≫ β).stalkMap x = (β.st
alkMap (α.base x) : Z.presheaf.stalk …
-/
lemma stalkMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f x) ≫ f.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.toPshHom g.toPshHom x

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：stalkSpecializes_stalkMap (x x' : X) (h : x ⤳ x') : Y.presheaf.stalkSpecia
lizes (f.base.hom.map_specializes h) ≫ f.stalkMap x = f.stalkMap x' ≫ X.presheaf
.stalkSpecializes h
参数：x x' : X；h : x ⤳ x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.stalkSpecializes_stalkMap`：st
alkSpecializes_stalkMap {X Y : PresheafedSpace.{_, _, v} C} (f : X ⟶ Y) {x y : X
} (h : x ⤳ y) : Y.presheaf.stalkSpecializes (f.base.hom.ma…
-/
lemma stalkSpecializes_stalkMap (x x' : X)
    (h : x ⤳ x') : Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toPshHom h
/-
**AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap_apply** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) : f.stalkMap x
 (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) y) = (X.presheaf.st
alkSpecializes h (f.stalkMap x' y))
参数：x x' : X；h : x ⤳ x'；y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `ContinuousMap.map_specializes`：map_specializes (f : C(α, β)) {x y : α} (
h : x ⤳ y) : f x ⤳ f y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap`：stalkSpecializes
_stalkMap (x x' : X) (h : x ⤳ x') : Y.presheaf.stalkSpecializes (f.base.hom.map_
specializes h) ≫ f.stalkMap x = f.stalkMap x…
-/
lemma stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) y) =
      (X.presheaf.stalkSpecializes h (f.stalkMap x' y)) :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_congr** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') : f.
stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hxx')).hom = (Y.presheaf.stalkCongr 
(.of_eq <| hfg ▸ hxx' ▸ rfl)).hom ≫ g.stalkMap x'
参数：f g : X ⟶ Y；hfg : f = g；x x' : X；hxx' : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr`：stalkMap_congr (f g
 : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') : f.stalkMap x ≫ X.presheaf.s
talkSpecializes (specializes_of_eq hxx'.s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X)
    (hxx' : x = x') : f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (.of_eq <| hfg ▸ hxx' ▸ rfl)).hom ≫ g.stalkMap x' :=
  LocallyRingedSpace.stalkMap_congr f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x x' hxx'

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_congr_hom** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.Hom`。
形式化陈述：stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) : f.stalkMap x = (Y
.presheaf.stalkCongr (.of_eq <| hfg ▸ rfl)).hom ≫ g.stalkMap x
参数：f g : X ⟶ Y；hfg : f = g；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_hom`：stalkMap_congr_
hom (f g : X ⟶ Y) (hfg : f = g) (x : X) : f.stalkMap x = Y.presheaf.stalkSpecial
izes (specializes_of_eq <| hfg ▸ rfl) ≫ g.sta…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x = (Y.presheaf.stalkCongr (.of_eq <| hfg ▸ rfl)).hom ≫ g.stalkMap x :=
  LocallyRingedSpace.stalkMap_congr_hom f.toLRSHom g.toLRSHom congr(($hfg).toLRSHom) x

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_congr_point** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：stalkMap_congr_point (x x' : X) (hxx' : x = x') : f.stalkMap x ≫ (X.preshe
af.stalkCongr (.of_eq hxx')).hom = (Y.presheaf.stalkCongr (.of_eq <| hxx' ▸ rfl)
).hom ≫ f.stalkMap x'
参数：x x' : X；hxx' : x = x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_congr_point`：stalkMap_cong
r_point {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X) (hxx' : x = x') : 
f.stalkMap x ≫ X.presheaf.stalkSpecializes (spe…
-/
lemma stalkMap_congr_point (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (.of_eq <| hxx' ▸ rfl)).hom ≫ f.stalkMap x' :=
  LocallyRingedSpace.stalkMap_congr_point f.toLRSHom x x' hxx'

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_hom_inv** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：stalkMap_hom_inv (e : X ≅ Y) (y : Y) : e.hom.stalkMap (e.inv y) ≫ e.inv.st
alkMap y = (Y.presheaf.stalkCongr (.of_eq (by simp))).hom
参数：e : X ≅ Y；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_hom_inv`：stalkMap_hom_inv 
(e : X ≅ Y) (y : Y) : e.hom.stalkMap (e.inv.base y) ≫ e.inv.stalkMap y = Y.presh
eaf.stalkSpecializes (specializes_of_eq <| …
-/
lemma stalkMap_hom_inv (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv y) ≫ e.inv.stalkMap y =
      (Y.presheaf.stalkCongr (.of_eq (by simp))).hom :=
  LocallyRingedSpace.stalkMap_hom_inv (forgetToLocallyRingedSpace.mapIso e) y

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_hom_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) : e.inv.stalkMap y (e.hom.s
talkMap (e.inv y) z) = (Y.presheaf.stalkCongr (.of_eq (by simp))).hom z
参数：e : X ≅ Y；y : Y；z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_hom_inv`：stalkMap_hom_inv (e : X ≅
 Y) (y : Y) : e.hom.stalkMap (e.inv y) ≫ e.inv.stalkMap y = (Y.presheaf.stalkCon
gr (.of_eq (by simp))).hom
-/
lemma stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv y) z) =
      (Y.presheaf.stalkCongr (.of_eq (by simp))).hom z :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_inv_hom** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：stalkMap_inv_hom (e : X ≅ Y) (x : X) : e.inv.stalkMap (e.hom x) ≫ e.hom.st
alkMap x = (X.presheaf.stalkCongr (.of_eq (by simp))).hom
参数：e : X ≅ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_inv_hom`：stalkMap_inv_hom 
(e : X ≅ Y) (x : X) : e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x = X.presh
eaf.stalkSpecializes (specializes_of_eq <| …
-/
lemma stalkMap_inv_hom (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom x) ≫ e.hom.stalkMap x =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom :=
  LocallyRingedSpace.stalkMap_inv_hom (forgetToLocallyRingedSpace.mapIso e) x

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.stalkMap_inv_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) : e.hom.stalkMap x (e.inv.s
talkMap (e.hom x) y) = (X.presheaf.stalkCongr (.of_eq (by simp))).hom y
参数：e : X ≅ Y；x : X；y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRingCat.hom_ext_iff`：∀ {R S : CommRingCat} {f g : R ⟶ S}, f = g ↔ Co
mmRingCat.Hom.hom f = CommRingCat.Hom.hom g
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_inv_hom`：stalkMap_inv_hom (e : X ≅
 Y) (x : X) : e.inv.stalkMap (e.hom x) ≫ e.hom.stalkMap x = (X.presheaf.stalkCon
gr (.of_eq (by simp))).hom
-/
lemma stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom x) y) =
      (X.presheaf.stalkCongr (.of_eq (by simp))).hom y :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.germ_stalkMap** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：germ_stalkMap (U : Y.Opens) (x : X) (hx : f x in U) : Y.presheaf.germ U (f
 x) hx ≫ f.stalkMap x = f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx
参数：U : Y.Opens；x : X；hx : f x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ`：stalkMap_germ {X Y : Pr
esheafedSpace.{_, _, v} C} (α : X ⟶ Y) (U : Opens Y) (x : X) (hx : α x in U) : Y
.presheaf.germ U (α x) hx ≫ α.stalkMa…
-/
lemma germ_stalkMap (U : Y.Opens) (x : X) (hx : f x ∈ U) :
    Y.presheaf.germ U (f x) hx ≫ f.stalkMap x =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx :=
  PresheafedSpace.stalkMap_germ f.toPshHom U x hx

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Hom`。
形式化陈述：germ_stalkMap_apply (U : Y.Opens) (x : X) (hx : f x in U) (y) : f.stalkMap
 x (Y.presheaf.germ _ (f x) hx y) = X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U y)
参数：U : Y.Opens；x : X；hx : f x in U；y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColim
its C]   {X Y : AlgebraicGeometry.Presheafe…
-/
lemma germ_stalkMap_apply (U : Y.Opens) (x : X) (hx : f x ∈ U) (y) :
    f.stalkMap x (Y.presheaf.germ _ (f x) hx y) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U y) :=
  PresheafedSpace.stalkMap_germ_apply f.toPshHom U x hx y

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `x = y`, the stalk maps are isomorphic. -/
/-
**AlgebraicGeometry.Scheme.Hom.arrowStalkMapIsoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：arrowStalkMapIsoOfEq {x y : X} (h : x = y) : Arrow.mk (f.stalkMap x) ≅ Arr
ow.mk (f.stalkMap y)
参数：h : x = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x = y`, the stalk maps are isomorphic.
-/
noncomputable def arrowStalkMapIsoOfEq {x y : X}
    (h : x = y) : Arrow.mk (f.stalkMap x) ≅ Arrow.mk (f.stalkMap y) :=
  Arrow.isoMk (Y.presheaf.stalkCongr <| (Inseparable.of_eq h).map f.continuous)
      (X.presheaf.stalkCongr <| Inseparable.of_eq h) <| by
    simp only [Arrow.mk_left, Arrow.mk_right, TopCat.Presheaf.stalkCongr_hom,
      Arrow.mk_hom]
    rw [stalkSpecializes_stalkMap]

end Hom

end Scheme

end Stalks

section IsLocalRing

open IsLocalRing

@[simp]
/-
**AlgebraicGeometry.Spec_closedPoint** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：∀ {R S : CommRingCat} [inst : IsLocalRing ↑R] [inst_1 : IsLocalRing ↑S] {f
 : R ⟶ S}   [IsLocalHom (CommRingCat.Hom.hom f)],   (AlgebraicGeometry.Spec.map 
f) (IsLocalRing.closedPoint ↑S) = IsLocalRing.closedPoint ↑R
参数：CommRingCat.Hom.hom f；AlgebraicGeometry.Spec.map f；IsLocalRing.closedPoint ↑S
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.comap_closedPoint`：comap_closedPoint {S : Type v} [CommSemir
ing S] [IsLocalRing S] (f : R ->+* S) [IsLocalHom f] : PrimeSpectrum.comap f (cl
osedPoint S) = clos…
-/
lemma Spec_closedPoint {R S : CommRingCat} [IsLocalRing R] [IsLocalRing S]
    {f : R ⟶ S} [IsLocalHom f.hom] : Spec.map f (closedPoint S) = closedPoint R :=
  IsLocalRing.comap_closedPoint f.hom

end IsLocalRing

end AlgebraicGeometry

