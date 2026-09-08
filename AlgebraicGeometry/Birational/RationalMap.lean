/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
/-!

# Rational maps between schemes

## Main definitions

* `AlgebraicGeometry.Scheme.PartialMap`: A partial map from `X` to `Y` (`X.PartialMap Y`) is
  a morphism into `Y` defined on a dense open subscheme of `X`.
* `AlgebraicGeometry.Scheme.PartialMap.equiv`:
  Two partial maps are equivalent if they are equal on a dense open subscheme.
* `AlgebraicGeometry.Scheme.RationalMap`:
  A rational map from `X` to `Y` (`X ⤏ Y`) is an equivalence class of partial maps.
* `AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver`:
  Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
  `S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
* `AlgebraicGeometry.Scheme.RationalMap.toPartialMap`:
  If `X` is reduced and `Y` is separated, then any `f : X ⤏ Y` can be realized as a partial
  map on `f.domain`, the domain of definition of `f`.
-/

@[expose] public section

universe u

open CategoryTheory hiding Quotient

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

namespace Scheme

/--
A partial map from `X` to `Y` (`X.PartialMap Y`) is a morphism into `Y`
defined on a dense open subscheme of `X`.
-/
/-
**AlgebraicGeometry.Scheme.PartialMap** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：AlgebraicGeometry.Scheme → AlgebraicGeometry.Scheme → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial map from `X` to `Y` (`X.PartialMap Y`) is a morphism into `Y`
defined on a dense open subscheme of `X`.
-/
structure PartialMap (X Y : Scheme.{u}) where
  /-- The domain of definition of a partial map. -/
  domain : X.Opens
  dense_domain : Dense (domain : Set X)
  /-- The underlying morphism of a partial map. -/
  hom : ↑domain ⟶ Y

variable (S) in
/-- A partial map is an `S`-map if the underlying morphism is. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.IsOver** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.PartialMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (S : AlgebraicGeometry.Scheme) → [X.Ove
r S] → [Y.Over S] → X.PartialMap Y → Prop
参数：S : AlgebraicGeometry.Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial map is an `S`-map if the underlying morphism is.
-/
abbrev PartialMap.IsOver [X.Over S] [Y.Over S] (f : X.PartialMap Y) :=
  f.hom.IsOver S

namespace PartialMap

/-
**AlgebraicGeometry.Scheme.PartialMap.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.PartialMap`。
形式化陈述：ext_iff (f g : X.PartialMap Y) : f = g ↔ exists e : f.domain = g.domain, f
.hom = (X.isoOfEq e).hom ≫ g.hom
参数：f g : X.PartialMap Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma ext_iff (f g : X.PartialMap Y) :
    f = g ↔ ∃ e : f.domain = g.domain, f.hom = (X.isoOfEq e).hom ≫ g.hom := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U, hU, f⟩ := f
    obtain ⟨V, hV, g⟩ := g
    rintro ⟨rfl : U = V, e⟩
    congr 1
    simpa using e

@[ext]
/-
**AlgebraicGeometry.Scheme.PartialMap.ext** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.PartialMap`。
形式化陈述：ext (f g : X.PartialMap Y) (e : f.domain = g.domain) (H : f.hom = (X.isoOf
Eq e).hom ≫ g.hom) : f = g
参数：f g : X.PartialMap Y；e : f.domain = g.domain；H : f.hom = (X.isoOfEq e).hom ≫ 
g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext_iff`：ext_iff (f g : X.PartialMap
 Y) : f = g ↔ exists e : f.domain = g.domain, f.hom = (X.isoOfEq e).hom ≫ g.hom
-/
lemma ext (f g : X.PartialMap Y) (e : f.domain = g.domain)
    (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g := by
  rw [ext_iff]
  exact ⟨e, H⟩

/-- The restriction of a partial map to a smaller domain. -/
@[simps hom domain]
noncomputable
/-
**AlgebraicGeometry.Scheme.PartialMap.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme.PartialMap`。
形式化陈述：restrict (f : X.PartialMap Y) (U : X.Opens) (hU : Dense (U : Set X)) (hU' 
: U <= f.domain) : X.PartialMap Y where domain
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def restrict (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) : X.PartialMap Y where
  domain := U
  dense_domain := hU
  hom := X.homOfLE hU' ≫ f.hom

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.restrict_id** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.PartialMap`。
形式化陈述：restrict_id (f : X.PartialMap Y) : f.restrict f.domain f.dense_domain le_r
fl = f
参数：f : X.PartialMap Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.homOfLE ⋯ = CategoryTheory.CategoryStruct.id ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
-/
lemma restrict_id (f : X.PartialMap Y) : f.restrict f.domain f.dense_domain le_rfl = f := by
  ext1 <;> simp [restrict_domain]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.PartialMap.restrict_id_hom** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：restrict_id_hom (f : X.PartialMap Y) : (f.restrict f.domain f.dense_domain
 le_rfl).hom = f.hom
参数：f : X.PartialMap Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.restrict_hom`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X.PartialMap Y) (U : X.Opens) (hU : Dense ↑U) (hU' : U ≤ f.dom
ain),   (f.restrict U hU hU').hom = Ca…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.homOfLE ⋯ = CategoryTheory.CategoryStruct.id ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_id_hom (f : X.PartialMap Y) :
    (f.restrict f.domain f.dense_domain le_rfl).hom = f.hom := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.restrict_restrict** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：restrict_restrict (f : X.PartialMap Y) (U : X.Opens) (hU : Dense (U : Set 
X)) (hU' : U <= f.domain) (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V <= U) 
: (f.restrict U hU hU').restrict V hV hV' = f.restrict V hV (hV'.trans hU')
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain；V :
 X.Opens；hV : Dense (V : Set X)；hV' : V <= U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_homOfLE_assoc`：∀ (X : AlgebraicGeometry
.Scheme) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) {Z : AlgebraicGeometry.Sche
me}   (h : ↑W ⟶ Z),   CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma restrict_restrict (f : X.PartialMap Y)
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain)
    (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V ≤ U) :
    (f.restrict U hU hU').restrict V hV hV' = f.restrict V hV (hV'.trans hU') := by
  ext1 <;> simp [restrict_domain]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.restrict_restrict_hom** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：restrict_restrict_hom (f : X.PartialMap Y) (U : X.Opens) (hU : Dense (U : 
Set X)) (hU' : U <= f.domain) (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V <=
 U) : ((f.restrict U hU hU').restrict V hV hV').hom = (f.restrict V hV (hV'.tran
s hU')).hom
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain；V :
 X.Opens；hV : Dense (V : Set X)；hV' : V <= U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_homOfLE_assoc`：∀ (X : AlgebraicGeometry
.Scheme) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) {Z : AlgebraicGeometry.Sche
me}   (h : ↑W ⟶ Z),   CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_restrict_hom (f : X.PartialMap Y)
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain)
    (V : X.Opens) (hV : Dense (V : Set X)) (hV' : V ≤ U) :
    ((f.restrict U hU hU').restrict V hV hV').hom = (f.restrict V hV (hV'.trans hU')).hom := by
  simp

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.Scheme.PartialMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Over S] [Y.Over S] (f : X.PartialMap Y) [f.IsOver S]
    (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').IsOver S where

/-- The composition of a partial map and a morphism on the right. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.PartialMap.compHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.PartialMap`。
形式化陈述：compHom (f : X.PartialMap Y) (g : Y ⟶ Z) : X.PartialMap Z where domain
参数：f : X.PartialMap Y；g : Y ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain

--- 原说明 ---
The composition of a partial map and a morphism on the right.
-/
def compHom (f : X.PartialMap Y) (g : Y ⟶ Z) : X.PartialMap Z where
  domain := f.domain
  dense_domain := f.dense_domain
  hom := f.hom ≫ g

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.compHom_id** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.PartialMap`。
形式化陈述：compHom_id (f : X.PartialMap Y) : f.compHom (𝟙 Y) = f
参数：f : X.PartialMap Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compHom_id (f : X.PartialMap Y) : f.compHom (𝟙 Y) = f := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.Scheme.PartialMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Over S] [Y.Over S] [Z.Over S] (f : X.PartialMap Y) (g : Y ⟶ Z)
    [f.IsOver S] [g.IsOver S] : (f.compHom g).IsOver S where

/-- A scheme morphism as a partial map. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.PartialMap._root_.AlgebraicGeometry.Scheme.Hom.toPart
ialMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme morphism as a partial map.
-/
def _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap (f : X ⟶ Y) :
    X.PartialMap Y := ⟨⊤, dense_univ, X.topIso.hom ≫ f⟩

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.Scheme.PartialMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) [IsDominant f] : IsDominant f.toPartialMap.hom := by
  dsimp
  have := Opens.isDominant_ι (X := X) (U := ⊤) dense_univ
  infer_instance
/-
**AlgebraicGeometry.Scheme.PartialMap._root_.AlgebraicGeometry.Scheme.Hom.toPart
ialMap_compHom** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AlgebraicGeometry.Scheme.Hom.toPartialMap_compHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toPartialMap.compHom g = (f ≫ g).toPartialMap := rfl

variable (X) in
/-- The identity partial map. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.id** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme.PartialMap`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → X.PartialMap X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity partial map.
-/
protected abbrev id : X.PartialMap X := (𝟙 X : X ⟶ X).toPartialMap

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.id_compHom** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.PartialMap`。
形式化陈述：id_compHom (f : X ⟶ Y) : (PartialMap.id X).compHom f = f.toPartialMap
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.compHom_hom`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X.PartialMap Y) (g : Y ⟶ Z),   (f.compHom g).hom = CategoryTh
eory.CategoryStruct.comp f.hom g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toPartialMap_hom`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y),   (AlgebraicGeometry.Scheme.Hom.toPartialMap f).hom = Cat
egoryTheory.CategoryStruct.comp X.t…
· 使用定理 `AlgebraicGeometry.Scheme.topIso_hom`：∀ (X : AlgebraicGeometry.Scheme), X
.topIso.hom = ⊤.ι
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_compHom (f : X ⟶ Y) : (PartialMap.id X).compHom f = f.toPartialMap := by
  apply PartialMap.ext _ _ rfl
  simp

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.Scheme.PartialMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S] : f.toPartialMap.IsOver S where

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.isOver_iff** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.PartialMap`。
形式化陈述：isOver_iff [X.Over S] [Y.Over S] {f : X.PartialMap Y} : f.IsOver S ↔ (f.co
mpHom (Y ↘ S)).hom = f.domain.ι ≫ X ↘ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `CategoryTheory.instHomIsOverOfIsOverTower`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) (S S' : C)   [inst_1 : Categor
yTheory.CanonicallyOverClass X …
· 使用定理 `CategoryTheory.instIsOverTower_2`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (S : C)   [inst_1 : CategoryTheory.CanonicallyOverC
lass X Y] [inst_2 : Ca…
· 使用定理 `CategoryTheory.instIsOverTower`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.IsOverTow…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOverι`：∀ {X : AlgebraicGeometry.Sch
eme} (U : X.Opens), AlgebraicGeometry.Scheme.Hom.IsOver U.ι X
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isOver_iff [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔ (f.compHom (Y ↘ S)).hom = f.domain.ι ≫ X ↘ S := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.isOver_iff_eq_restrict** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：isOver_iff_eq_restrict [X.Over S] [Y.Over S] {f : X.PartialMap Y} : f.IsOv
er S ↔ f.compHom (Y ↘ S) = (X ↘ S).toPartialMap.restrict _ f.dense_domain (by si
mp)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `CategoryTheory.instHomIsOverOfIsOverTower`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) (S S' : C)   [inst_1 : Categor
yTheory.CanonicallyOverClass X …
· 使用定理 `CategoryTheory.instIsOverTower_2`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (S : C)   [inst_1 : CategoryTheory.CanonicallyOverC
lass X Y] [inst_2 : Ca…
· 使用定理 `CategoryTheory.instIsOverTower`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.IsOverTow…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOverι`：∀ {X : AlgebraicGeometry.Sch
eme} (U : X.Opens), AlgebraicGeometry.Scheme.Hom.IsOver U.ι X
· 使用定理 `CategoryTheory.instHomIsOverOfIsOverTower_1`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) (S S' : C)   [inst_1 : Categ
oryTheory.OverClass X S] [inst_2 …
· 使用定理 `AlgebraicGeometry.instIsOverHomOfLE`：∀ {X : AlgebraicGeometry.Scheme} {U
 V : X.Opens} (h : U ≤ V), AlgebraicGeometry.Scheme.Hom.IsOver (X.homOfLE h) X
· 使用定理 `CategoryTheory.instHomIsOverId`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.HomIsOver…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isOver_iff_eq_restrict [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔ f.compHom (Y ↘ S) = (X ↘ S).toPartialMap.restrict _ f.dense_domain (by simp) := by
  simp [PartialMap.ext_iff]

/-- If `x` is in the domain of a partial map `f`, then `f` restricts to a map from `Spec 𝒪_x`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：fromSpecStalkOfMem (f : X.PartialMap Y) {x} (hx : x in f.domain) : Spec (X
.presheaf.stalk x) ⟶ Y
参数：f : X.PartialMap Y；hx : x in f.domain。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fromSpecStalkOfMem (f : X.PartialMap Y) {x} (hx : x ∈ f.domain) :
    Spec (X.presheaf.stalk x) ⟶ Y :=
  f.domain.fromSpecStalkOfMem x hx ≫ f.hom

/-- A partial map restricts to a map from `Spec K(X)`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.PartialMap.fromFunctionField** 是 Mathlib 中的一个缩写定义，位于命
名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：fromFunctionField [IrreducibleSpace X] (f : X.PartialMap Y) : Spec X.funct
ionField ⟶ Y
参数：f : X.PartialMap Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
-/
abbrev fromFunctionField [IrreducibleSpace X] (f : X.PartialMap Y) :
    Spec X.functionField ⟶ Y :=
  f.fromSpecStalkOfMem
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_restrict** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：fromSpecStalkOfMem_restrict (f : X.PartialMap Y) {U : X.Opens} (hU : Dense
 (U : Set X)) (hU' : U <= f.domain) {x} (hx : x in U) : (f.restrict U hU hU').fr
omSpecStalkOfMem hx = f.fromSpecStalkOfMem (hU' hx)
参数：f : X.PartialMap Y；hU : Dense (U : Set X)；hU' : U <= f.domain；hx : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_base`：∀ {X : AlgebraicGeometry.Scheme} 
{U V : X.Opens} (e : U ≤ V),   (X.homOfLE e).base = (TopologicalSpace.Opens.toTo
pCat ↑X.toPresheafedSpace).…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk_assoc`：∀ {X Y : 
AlgebraicGeometry.Scheme} (f : X ⟶ Y) {x : ↥X} {Z : AlgebraicGeometry.Scheme} (h
 : Y ⟶ Z),   CategoryTheory.CategoryStruct.comp (Al…
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk`：SpecMap
_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) : Spec.map (X.presheaf.sta
lkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStal…
· 使用定理 `TopCat.Presheaf.stalkCongr_inv`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_congr_hom`：stalkMap_congr_hom (f g
 : X ⟶ Y) (hfg : f = g) (x : X) : f.stalkMap x = (Y.presheaf.stalkCongr (.of_eq 
<| hfg ▸ rfl)).hom ≫ g.stalkMap x
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `ContinuousMap.map_specializes`：map_specializes (f : C(α, β)) {x y : α} (
h : x ⤳ y) : f x ⤳ f y
· 使用定理 `AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap_assoc`：∀ {X Y : A
lgebraicGeometry.Scheme} (f : X ⟶ Y) (x x' : ↥X) (h : x ⤳ x') {Z : CommRingCat} 
  (h_1 : X.presheaf.stalk x ⟶ Z),   CategoryTheory…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
-/
lemma fromSpecStalkOfMem_restrict (f : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) {x} (hx : x ∈ U) :
    (f.restrict U hU hU').fromSpecStalkOfMem hx = f.fromSpecStalkOfMem (hU' hx) := by
  dsimp only [fromSpecStalkOfMem, restrict, Scheme.Opens.fromSpecStalkOfMem]
  have e : ⟨x, hU' hx⟩ = X.homOfLE hU' ⟨x, hx⟩ := by
    rw [Scheme.homOfLE_base]
    rfl
  rw [Category.assoc, ← SpecMap_stalkMap_fromSpecStalk_assoc,
    ← SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq e).specializes,
    ← TopCat.Presheaf.stalkCongr_inv _ (Inseparable.of_eq e)]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 3
  rw [Iso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, IsIso.eq_inv_comp,
    Hom.stalkMap_congr_hom _ _ (X.homOfLE_ι hU').symm]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [← Hom.stalkSpecializes_stalkMap_assoc, Hom.stalkMap_comp]
/-
**AlgebraicGeometry.Scheme.PartialMap.fromFunctionField_restrict** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：fromFunctionField_restrict (f : X.PartialMap Y) [IrreducibleSpace X] {U : 
X.Opens} (hU : Dense (U : Set X)) (hU' : U <= f.domain) : (f.restrict U hU hU').
fromFunctionField = f.fromFunctionField
参数：f : X.PartialMap Y；hU : Dense (U : Set X)；hU' : U <= f.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_restrict`：fromSpe
cStalkOfMem_restrict (f : X.PartialMap Y) {U : X.Opens} (hU : Dense (U : Set X))
 (hU' : U <= f.domain) {x} (hx : x in U) : (f.restric…
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
-/
lemma fromFunctionField_restrict (f : X.PartialMap Y) [IrreducibleSpace X]
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField :=
  fromSpecStalkOfMem_restrict f _ _ _

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and
`X` is irreducible germ-injective at `x` (e.g. when `X` is integral),
any `S`-morphism `Spec 𝒪ₓ ⟶ Y` spreads out to a partial map from `X` to `Y`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.PartialMap.ofFromSpecStalk** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY] {x : X} [X.I
sGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.fromSpec
Stalk x ≫ sX) : X.PartialMap Y where hom
参数：φ : Spec (X.presheaf.stalk x) ⟶ Y；h : φ ≫ sY = X.fromSpecStalk x ≫ sX。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.spread_out_of_isGermInjective'`：spread_out_of_isGermIn
jective' [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.p
resheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.…
-/
def ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
    (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) : X.PartialMap Y where
  hom := (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose
  domain := (spread_out_of_isGermInjective' sX sY φ h).choose
  dense_domain := (spread_out_of_isGermInjective' sX sY φ h).choose.2.dense
    ⟨_, (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose⟩
/-
**AlgebraicGeometry.Scheme.PartialMap.ofFromSpecStalk_comp** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：ofFromSpecStalk_comp [IrreducibleSpace X] [LocallyOfFiniteType sY] {x : X}
 [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.fro
mSpecStalk x ≫ sX) : (ofFromSpecStalk sX sY φ h).hom ≫ sY = (ofFromSpecStalk sX 
sY φ h).domain.ι ≫ sX
参数：φ : Spec (X.presheaf.stalk x) ⟶ Y；h : φ ≫ sY = X.fromSpecStalk x ≫ sX。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `AlgebraicGeometry.spread_out_of_isGermInjective'`：spread_out_of_isGermIn
jective' [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.p
resheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma ofFromSpecStalk_comp [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    (ofFromSpecStalk sX sY φ h).hom ≫ sY = (ofFromSpecStalk sX sY φ h).domain.ι ≫ sX :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.2
/-
**AlgebraicGeometry.Scheme.PartialMap.mem_domain_ofFromSpecStalk** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：mem_domain_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY] {
x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : φ ≫ sY =
 X.fromSpecStalk x ≫ sX) : x in (ofFromSpecStalk sX sY φ h).domain
参数：φ : Spec (X.presheaf.stalk x) ⟶ Y；h : φ ≫ sY = X.fromSpecStalk x ≫ sX。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.spread_out_of_isGermInjective'`：spread_out_of_isGermIn
jective' [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.p
resheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma mem_domain_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) : x ∈ (ofFromSpecStalk sX sY φ h).domain :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose
/-
**AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk** 是 Mat
hlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：fromSpecStalkOfMem_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteTy
pe sY] {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y) (h : 
φ ≫ sY = X.fromSpecStalk x ≫ sX) : (ofFromSpecStalk sX sY φ h).fromSpecStalkOfMe
m (mem_domain_ofFromSpecStalk sX sY φ h) = φ
参数：φ : Spec (X.presheaf.stalk x) ⟶ Y；h : φ ≫ sY = X.fromSpecStalk x ≫ sX。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.spread_out_of_isGermInjective'`：spread_out_of_isGermIn
jective' [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.p
resheaf.stalk x) ⟶ Y) (h : φ ≫ sY = X.…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma fromSpecStalkOfMem_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY]
    {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    (ofFromSpecStalk sX sY φ h).fromSpecStalkOfMem (mem_domain_ofFromSpecStalk sX sY φ h) = φ :=
  (spread_out_of_isGermInjective' sX sY φ h).choose_spec.choose_spec.choose_spec.1.symm

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_compHom** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：fromSpecStalkOfMem_compHom (f : X.PartialMap Y) (g : Y ⟶ Z) (x) (hx) : (f.
compHom g).fromSpecStalkOfMem (x
参数：f : X.PartialMap Y；g : Y ⟶ Z；x；hx。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSpecStalkOfMem_compHom (f : X.PartialMap Y) (g : Y ⟶ Z) (x) (hx) :
    (f.compHom g).fromSpecStalkOfMem (x := x) hx = f.fromSpecStalkOfMem hx ≫ g := by
  simp [fromSpecStalkOfMem]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：fromSpecStalkOfMem_toPartialMap (f : X ⟶ Y) (x) : f.toPartialMap.fromSpecS
talkOfMem (x
参数：f : X ⟶ Y；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `trivial`：True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_ι_assoc`：∀ {X : Algebr
aicGeometry.Scheme} (U : X.Opens) (x : ↥X) (hxU : x ∈ U) {Z : AlgebraicGeometry.
Scheme} (h : X ⟶ Z),   CategoryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSpecStalkOfMem_toPartialMap (f : X ⟶ Y) (x) :
    f.toPartialMap.fromSpecStalkOfMem (x := x) trivial = X.fromSpecStalk x ≫ f := by
  simp [fromSpecStalkOfMem]

/-- Two partial maps are equivalent if they are equal on a dense open subscheme. -/
protected noncomputable
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.PartialMap`。
形式化陈述：equiv (f g : X.PartialMap Y) : Prop
参数：f g : X.PartialMap Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equiv (f g : X.PartialMap Y) : Prop :=
  ∃ (W : X.Opens) (hW : Dense (W : Set X)) (hWl : W ≤ f.domain) (hWr : W ≤ g.domain),
    (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv_of_restrict_eq** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：equiv_of_restrict_eq (f g : X.PartialMap Y) {W₁ W₂ : X.Opens} {hW₁ : Dense
 (W₁ : Set X)} {hW₂ : Dense (W₂ : Set X)} {hW₁' : W₁ <= f.domain} {hW₂' : W₂ <= 
g.domain} (H : f.restrict W₁ hW₁ hW₁' = g.restrict W₂ hW₂ hW₂') : f.equiv g
参数：f g : X.PartialMap Y；W₁ : Set X；W₂ : Set X；H : f.restrict W₁ hW₁ hW₁' = g.res
trict W₂ hW₂ hW₂'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma equiv_of_restrict_eq (f g : X.PartialMap Y) {W₁ W₂ : X.Opens} {hW₁ : Dense (W₁ : Set X)}
    {hW₂ : Dense (W₂ : Set X)} {hW₁' : W₁ ≤ f.domain} {hW₂' : W₂ ≤ g.domain}
    (H : f.restrict W₁ hW₁ hW₁' = g.restrict W₂ hW₂ hW₂') : f.equiv g := by
  have e : W₁ = W₂ := congr($(H).domain)
  subst e
  exact ⟨W₁, hW₁, hW₁', hW₂', congr($(H).hom)⟩

set_option backward.isDefEq.respectTransparency false in
@[refl]
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.PartialMap.equiv`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y), f.equiv f
参数：f : X.PartialMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.restrict_hom`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X.PartialMap Y) (U : X.Opens) (hU : Dense ↑U) (hU' : U ≤ f.dom
ain),   (f.restrict U hU hU').hom = Ca…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.homOfLE ⋯ = CategoryTheory.CategoryStruct.id ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma equiv.refl (f : X.PartialMap Y) : f.equiv f :=
  ⟨f.domain, f.dense_domain, by simp⟩

@[symm]
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.PartialMap.equiv`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f g : X.PartialMap Y}, f.equiv g → g.e
quiv f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma equiv.symm {f g : X.PartialMap Y} : f.equiv g → g.equiv f := by
  intro ⟨W, hW, hWl, hWr, e⟩
  exact ⟨W, hW, hWr, hWl, e.symm⟩

set_option backward.defeqAttrib.useBackward true in
@[trans]
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.PartialMap.equiv`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f g h : X.PartialMap Y}, f.equiv g → g
.equiv h → f.equiv h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_of_isOpen_left`：Dense.inter_of_isOpen_left (hs : Dense s) (h
t : Dense t) (hso : IsOpen s) : Dense (s inter t)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_homOfLE`：∀ (X : AlgebraicGeometry.Schem
e) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W),   CategoryTheory.CategoryStruct.
comp (X.homOfLE e₁) (X.homOfLE…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_homOfLE_assoc`：∀ (X : AlgebraicGeometry
.Scheme) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) {Z : AlgebraicGeometry.Sche
me}   (h : ↑W ⟶ Z),   CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv.trans {f g h : X.PartialMap Y} : f.equiv g → g.equiv h → f.equiv h := by
  intro ⟨W₁, hW₁, hW₁l, hW₁r, e₁⟩ ⟨W₂, hW₂, hW₂l, hW₂r, e₂⟩
  refine ⟨W₁ ⊓ W₂, hW₁.inter_of_isOpen_left hW₂ W₁.2, inf_le_left.trans hW₁l,
    inf_le_right.trans hW₂r, ?_⟩
  dsimp at e₁ e₂
  simp only [restrict_domain, restrict_hom, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_left hW₁l,
    Category.assoc, e₁, ← X.homOfLE_homOfLE (U := W₁ ⊓ W₂) inf_le_right hW₂r, ← e₂]
  simp only [homOfLE_homOfLE_assoc]
/-
**AlgebraicGeometry.Scheme.PartialMap.equivalence_rel** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：equivalence_rel : Equivalence (@Scheme.PartialMap.equiv X Y) where refl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.equiv.refl`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X.PartialMap Y), f.equiv f
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.equiv.symm`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f g : X.PartialMap Y}, f.equiv g → g.equiv f
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.equiv.trans`：∀ {X Y : AlgebraicGeome
try.Scheme} {f g h : X.PartialMap Y}, f.equiv g → g.equiv h → f.equiv h
-/
lemma equivalence_rel : Equivalence (@Scheme.PartialMap.equiv X Y) where
  refl := equiv.refl
  symm := equiv.symm
  trans := equiv.trans
/-
**AlgebraicGeometry.Scheme.PartialMap.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.Scheme.PartialMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Setoid (X.PartialMap Y) := ⟨@PartialMap.equiv X Y, equivalence_rel⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.restrict_equiv** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：restrict_equiv (f : X.PartialMap Y) (U : X.Opens) (hU : Dense (U : Set X))
 (hU' : U <= f.domain) : (f.restrict U hU hU').equiv f
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.homOfLE ⋯ = CategoryTheory.CategoryStruct.id ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_equiv (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) : (f.restrict U hU hU').equiv f :=
  ⟨U, hU, le_rfl, hU', by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：equiv_of_fromSpecStalkOfMem_eq [IrreducibleSpace X] {x : X} [X.IsGermInjec
tiveAt x] (f g : X.PartialMap Y) (hxf : x in f.domain) (hxg : x in g.domain) (H 
: f.fromSpecStalkOfMem hxf = g.fromSpecStalkOfMem hxg) : f.equiv g
参数：f g : X.PartialMap Y；hxf : x in f.domain；hxg : x in g.domain；H : f.fromSpecSt
alkOfMem hxf = g.fromSpecStalkOfMem hxg。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_of_isOpen_left`：Dense.inter_of_isOpen_left (hs : Dense s) (h
t : Dense t) (hso : IsOpen s) : Dense (s inter t)
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.isGermInjectiveAt_iff_of_isOpenImmersion`：isGermInject
iveAt_iff_of_isOpenImmersion {x : X} [IsOpenImmersion f] : Y.IsGermInjectiveAt (
f x) ↔ X.IsGermInjectiveAt x
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `AlgebraicGeometry.spread_out_unique_of_isGermInjective'`：spread_out_uniq
ue_of_isGermInjective' {x : X} [X.IsGermInjectiveAt x] (f g : X ⟶ Y) (e : X.from
SpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : ex…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat`：∀ {R S : CommRingCat}
 (f : R ⟶ S) [CategoryTheory.IsIso f], CategoryTheory.IsIso (AlgebraicGeometry.S
pec.map f)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Spec.map_inv`：∀ {R S : CommRingCat} (f : R ⟶ S) [inst 
: CategoryTheory.IsIso f],   AlgebraicGeometry.Spec.map (CategoryTheory.inv f) =
 CategoryTheory.inv …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_restrict`：fromSpe
cStalkOfMem_restrict (f : X.PartialMap Y) {U : X.Opens} (hU : Dense (U : Set X))
 (hU' : U <= f.domain) {x} (hx : x in U) : (f.restric…
· 使用定理 `IsOpen.dense`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X} [
PreirreducibleSpace X], IsOpen s → s.Nonempty → Dense s
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
（共 34 条，此处仅展示前 30 条）
-/
lemma equiv_of_fromSpecStalkOfMem_eq [IrreducibleSpace X]
    {x : X} [X.IsGermInjectiveAt x] (f g : X.PartialMap Y)
    (hxf : x ∈ f.domain) (hxg : x ∈ g.domain)
    (H : f.fromSpecStalkOfMem hxf = g.fromSpecStalkOfMem hxg) : f.equiv g := by
  have hdense : Dense ((f.domain ⊓ g.domain) : Set X) :=
    f.dense_domain.inter_of_isOpen_left g.dense_domain f.domain.2
  have := (isGermInjectiveAt_iff_of_isOpenImmersion (f := (f.domain ⊓ g.domain).ι)
    (x := ⟨x, hxf, hxg⟩)).mp ‹_›
  have := spread_out_unique_of_isGermInjective' (X := (f.domain ⊓ g.domain).toScheme)
    (X.homOfLE inf_le_left ≫ f.hom) (X.homOfLE inf_le_right ≫ g.hom) (x := ⟨x, hxf, hxg⟩) ?_
  · obtain ⟨U, hxU, e⟩ := this
    refine ⟨(f.domain ⊓ g.domain).ι ''ᵁ U, ((f.domain ⊓ g.domain).ι ''ᵁ U).2.dense
      ⟨_, ⟨_, hxU, rfl⟩⟩,
      ((Set.image_subset_range _ _).trans_eq (Subtype.range_val)).trans inf_le_left,
      ((Set.image_subset_range _ _).trans_eq (Subtype.range_val)).trans inf_le_right, ?_⟩
    rw [← cancel_epi (Scheme.Hom.isoImage _ _).hom]
    simp only [restrict_hom, ← Category.assoc] at e ⊢
    convert! e using 2 <;> rw [← cancel_mono (Scheme.Opens.ι _)] <;> simp
  · rw [← f.fromSpecStalkOfMem_restrict hdense inf_le_left ⟨hxf, hxg⟩,
      ← g.fromSpecStalkOfMem_restrict hdense inf_le_right ⟨hxf, hxg⟩] at H
    simpa only [fromSpecStalkOfMem, restrict_domain, Opens.fromSpecStalkOfMem, Spec.map_inv,
      restrict_hom, Category.assoc, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc] using H

set_option backward.isDefEq.respectTransparency false in
/-- Two partial maps from reduced schemes to separated schemes are equivalent if and only if
they are equal on **any** open dense subset. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：equiv_iff_of_isSeparated_of_le [X.Over S] [Y.Over S] [IsReduced X] [IsSepa
rated (Y ↘ S)] {f g : X.PartialMap Y} [f.IsOver S] [g.IsOver S] {W : X.Opens} (h
W : Dense (X
参数：Y ↘ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `AlgebraicGeometry.Opens.isDominant_homOfLE`：∀ {X : AlgebraicGeometry.Sch
eme} {U V : X.Opens},   Dense ↑U → ∀ (hU' : U ≤ V), AlgebraicGeometry.IsDominant
 (X.homOfLE hU')
· 使用定理 `Dense.inter_of_isOpen_left`：Dense.inter_of_isOpen_left (hs : Dense s) (h
t : Dense t) (hso : IsOpen s) : Dense (s inter t)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `AlgebraicGeometry.ext_of_isDominant_of_isSeparated'`：ext_of_isDominant_o
f_isSeparated' [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)] {f g : 
X ⟶ Y} [f.IsOver S] [g.IsOver S] {W} (ι :…
· 使用定理 `AlgebraicGeometry.instIsReducedToScheme`：∀ {X : AlgebraicGeometry.Scheme
} {U : X.Opens} [AlgebraicGeometry.IsReduced X], AlgebraicGeometry.IsReduced ↑U
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.instIsOverRestrict`：∀ {X Y S : Algeb
raicGeometry.Scheme} [inst : X.Over S] [inst_1 : Y.Over S] (f : X.PartialMap Y) 
  [AlgebraicGeometry.Scheme.PartialMap.IsOve…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.restrict_hom`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X.PartialMap Y) (U : X.Opens) (hU : Dense ↑U) (hU' : U ≤ f.dom
ain),   (f.restrict U hU hU').hom = Ca…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_homOfLE_assoc`：∀ (X : AlgebraicGeometry
.Scheme) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) {Z : AlgebraicGeometry.Sche
me}   (h : ↑W ⟶ Z),   CategoryTheory…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
Two partial maps from reduced schemes to separated schemes are equivalent if and
 only if
they are equal on **any** open dense subset.
-/
lemma equiv_iff_of_isSeparated_of_le [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y} [f.IsOver S] [g.IsOver S]
    {W : X.Opens} (hW : Dense (X := X) W) (hWl : W ≤ f.domain) (hWr : W ≤ g.domain) : f.equiv g ↔
      (f.restrict W hW hWl).hom = (g.restrict W hW hWr).hom := by
  refine ⟨fun ⟨V, hV, hVl, hVr, e⟩ ↦ ?_, fun e ↦ ⟨_, _, _, _, e⟩⟩
  have : IsDominant (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) :=
    Opens.isDominant_homOfLE (hW.inter_of_isOpen_left hV W.2) _
  apply ext_of_isDominant_of_isSeparated' S (X.homOfLE (inf_le_left : W ⊓ V ≤ W))
  simpa using congr(X.homOfLE (inf_le_right : W ⊓ V ≤ V) ≫ $e)

/-- Two partial maps from reduced schemes to separated schemes are equivalent if and only if
they are equal on the intersection of the domains. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：equiv_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated 
(Y ↘ S)] {f g : X.PartialMap Y} [f.IsOver S] [g.IsOver S] : f.equiv g ↔ (f.restr
ict _ (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_left).hom = (g.restrict _
 (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_right).hom
参数：Y ↘ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le`：equi
v_iff_of_isSeparated_of_le [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘
 S)] {f g : X.PartialMap Y} [f.IsOver S] [g.IsOver S] {W…
· 使用定理 `Dense.inter_of_isOpen_left`：Dense.inter_of_isOpen_left (hs : Dense s) (h
t : Dense t) (hso : IsOpen s) : Dense (s inter t)
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
Two partial maps from reduced schemes to separated schemes are equivalent if and
 only if
they are equal on the intersection of the domains.
-/
lemma equiv_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y}
    [f.IsOver S] [g.IsOver S] : f.equiv g ↔
      (f.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_left).hom =
      (g.restrict _ (f.2.inter_of_isOpen_left g.2 f.domain.2) inf_le_right).hom :=
  equiv_iff_of_isSeparated_of_le (S := S) _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Two partial maps from reduced schemes to separated schemes with the same domain are equivalent
if and only if they are equal. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：equiv_iff_of_domain_eq_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X] 
[IsSeparated (Y ↘ S)] {f g : X.PartialMap Y} (hfg : f.domain = g.domain) [f.IsOv
er S] [g.IsOver S] : f.equiv g ↔ f = g
参数：Y ↘ S；hfg : f.domain = g.domain。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated_of_le`：equi
v_iff_of_isSeparated_of_le [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘
 S)] {f g : X.PartialMap Y} [f.IsOver S] [g.IsOver S] {W…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.homOfLE ⋯ = CategoryTheory.CategoryStruct.id ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.mk.injEq`：∀ {X Y : AlgebraicGeometry
.Scheme} (domain : X.Opens) (dense_domain : Dense ↑domain) (hom : ↑domain ⟶ Y)  
 (domain_1 : X.Opens) (dense_domai…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two partial maps from reduced schemes to separated schemes with the same domain 
are equivalent
if and only if they are equal.
-/
lemma equiv_iff_of_domain_eq_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f g : X.PartialMap Y} (hfg : f.domain = g.domain)
    [f.IsOver S] [g.IsOver S] : f.equiv g ↔ f = g := by
  rw [equiv_iff_of_isSeparated_of_le (S := S) f.dense_domain le_rfl hfg.le]
  obtain ⟨Uf, _, f⟩ := f
  obtain ⟨Ug, _, g⟩ := g
  obtain rfl : Uf = Ug := hfg
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A partial map from a reduced scheme to a separated scheme is equivalent to a morphism
if and only if it is equal to the restriction of the morphism. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：equiv_toPartialMap_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X] 
[IsSeparated (Y ↘ S)] {f : X.PartialMap Y} {g : X ⟶ Y} [f.IsOver S] [g.IsOver S]
 : f.equiv g.toPartialMap ↔ f.hom = f.domain.ι ≫ g
参数：Y ↘ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.inter_of_isOpen_left`：Dense.inter_of_isOpen_left (hs : Dense s) (h
t : Dense t) (hso : IsOpen s) : Dense (s inter t)
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_isSeparated`：equiv_iff_
of_isSeparated [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)] {f g : 
X.PartialMap Y} [f.IsOver S] [g.IsOver S] : f.equi…
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.instIsOverToPartialMapOfIsOver`：∀ {X
 Y S : AlgebraicGeometry.Scheme} [inst : X.Over S] [inst_1 : Y.Over S] (f : X ⟶ 
Y)   [AlgebraicGeometry.Scheme.Hom.IsOver f S],   Algebr…
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι_assoc`：∀ (X : AlgebraicGeometry.Schem
e) {U V : X.Opens} (e : U ≤ V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),   Cat
egoryTheory.CategoryStruct.com…
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι_assoc`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U = V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),  
 CategoryTheory.CategoryStruct.com…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A partial map from a reduced scheme to a separated scheme is equivalent to a mor
phism
if and only if it is equal to the restriction of the morphism.
-/
lemma equiv_toPartialMap_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] {f : X.PartialMap Y} {g : X ⟶ Y}
    [f.IsOver S] [g.IsOver S] : f.equiv g.toPartialMap ↔
      f.hom = f.domain.ι ≫ g := by
  rw [equiv_iff_of_isSeparated (S := S), ← cancel_epi (X.isoOfEq (inf_top_eq f.domain)).hom]
  simp
  rfl

end PartialMap

/-- A rational map from `X` to `Y` (`X ⤏ Y`) is an equivalence class of partial maps,
where two partial maps are equivalent if they are equal on a dense open subscheme. -/
/-
**AlgebraicGeometry.Scheme.RationalMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：RationalMap (X Y : Scheme.{u}) : Type u
参数：X Y : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rational map from `X` to `Y` (`X ⤏ Y`) is an equivalence class of partial maps
,
where two partial maps are equivalent if they are equal on a dense open subschem
e.
-/
def RationalMap (X Y : Scheme.{u}) : Type u :=
  @Quotient (X.PartialMap Y) inferInstance

/-- The notation for rational maps. -/
scoped[AlgebraicGeometry] infix:10 " ⤏ " => Scheme.RationalMap

/-- A partial map as a rational map. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.toRationalMap** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.PartialMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.PartialMap Y → X.RationalMap Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial map as a rational map.
-/
def PartialMap.toRationalMap (f : X.PartialMap Y) : X ⤏ Y := Quotient.mk _ f

/-- A scheme morphism as a rational map. -/
/-
**AlgebraicGeometry.Scheme.Hom.toRationalMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.Hom Y → X.RationalMap Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme morphism as a rational map.
-/
abbrev Hom.toRationalMap (f : X.Hom Y) : X ⤏ Y := f.toPartialMap.toRationalMap

variable (X) in
/-- The identity rational map. -/
/-
**AlgebraicGeometry.Scheme.RationalMap.id** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.RationalMap`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → X.RationalMap X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity rational map.
-/
abbrev RationalMap.id : X ⤏ X := (PartialMap.id X).toRationalMap

variable (S) in
/-- A rational map is an `S`-map if some partial map in the equivalence class is an `S`-map. -/
/-
**AlgebraicGeometry.Scheme.RationalMap.IsOver** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algeb
raicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (S : AlgebraicGeometry.Scheme) → [X.Ove
r S] → [Y.Over S] → X.RationalMap Y → Prop
参数：S : AlgebraicGeometry.Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rational map is an `S`-map if some partial map in the equivalence class is an 
`S`-map.
-/
class RationalMap.IsOver [X.Over S] [Y.Over S] (f : X ⤏ Y) : Prop where
  exists_partialMap_over : ∃ g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f
/-
**AlgebraicGeometry.Scheme.PartialMap.toRationalMap_surjective** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme}, Function.Surjective AlgebraicGeometry.
Scheme.PartialMap.toRationalMap
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
-/
lemma PartialMap.toRationalMap_surjective : Function.Surjective (@toRationalMap X Y) :=
  Quotient.exists_rep
/-
**AlgebraicGeometry.Scheme.RationalMap.exists_rep** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), ∃ g, g.toRationa
lMap = f
参数：f : X.RationalMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
-/
lemma RationalMap.exists_rep (f : X ⤏ Y) : ∃ g : X.PartialMap Y, g.toRationalMap = f :=
  Quotient.exists_rep f
/-
**AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap
 = g.toRationalMap ↔ f.equiv g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
lemma PartialMap.toRationalMap_eq_iff {f g : X.PartialMap Y} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g :=
  Quotient.eq

/-- An arbitrarily chosen partial map representing `f`. Use `RationalMap.toPartialMap` instead
if `X` is reduced and `Y` is separated. -/
/-
**AlgebraicGeometry.Scheme.RationalMap.representative** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.RationalMap Y → X.PartialMap Y
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.exists_rep`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X.RationalMap Y), ∃ g, g.toRationalMap = f

--- 原说明 ---
An arbitrarily chosen partial map representing `f`. Use `RationalMap.toPartialMa
p` instead
if `X` is reduced and `Y` is separated.
-/
noncomputable def RationalMap.representative (f : X ⤏ Y) : X.PartialMap Y :=
  f.exists_rep.choose

@[simp]
/-
**AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), f.representative
.toRationalMap = f
参数：f : X.RationalMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.exists_rep`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X.RationalMap Y), ∃ g, g.toRationalMap = f
-/
lemma RationalMap.toRationalMap_representative (f : X ⤏ Y) :
    f.representative.toRationalMap = f :=
  f.exists_rep.choose_spec
/-
**AlgebraicGeometry.Scheme.PartialMap.representative_toRationalMap_equiv** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y), f.toRationalMap.r
epresentative.equiv f
参数：f : X.PartialMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap = g.toRationalMap ↔
 f.equiv g
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), f.representative.toRational
Map = f
-/
lemma PartialMap.representative_toRationalMap_equiv (f : X.PartialMap Y) :
    f.toRationalMap.representative.equiv f := by
  rw [← PartialMap.toRationalMap_eq_iff, f.toRationalMap.toRationalMap_representative]

@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.restrict_toRationalMap** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y) (U : X.Opens) (hU 
: Dense ↑U) (hU' : U ≤ f.domain),   (f.restrict U hU hU').toRationalMap = f.toRa
tionalMap
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense ↑U；hU' : U ≤ f.domain；f.restrict U 
hU hU'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap = g.toRationalMap ↔
 f.equiv g
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.restrict_equiv`：restrict_equiv (f : 
X.PartialMap Y) (U : X.Opens) (hU : Dense (U : Set X)) (hU' : U <= f.domain) : (
f.restrict U hU hU').equiv f
-/
lemma PartialMap.restrict_toRationalMap (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').toRationalMap = f.toRationalMap :=
  toRationalMap_eq_iff.mpr (f.restrict_equiv U hU hU')
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Over S] [Y.Over S] (f : X.PartialMap Y) [f.IsOver S] : f.toRationalMap.IsOver S :=
  ⟨f, ‹_›, rfl⟩

variable (S) in
/-
**AlgebraicGeometry.Scheme.RationalMap.exists_partialMap_over** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (S : AlgebraicGeometry.Scheme) [inst : 
X.Over S] [inst_1 : Y.Over S]   (f : X.RationalMap Y) [AlgebraicGeometry.Scheme.
RationalMap.IsOver S f],   ∃ g, AlgebraicGeometry.Scheme.PartialMap.IsOver S g ∧
 g.toRationalMap = f
参数：S : AlgebraicGeometry.Scheme；f : X.RationalMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.IsOver.exists_partialMap_over`：∀ {X
 Y S : AlgebraicGeometry.Scheme} {inst : X.Over S} {inst_1 : Y.Over S} {f : X.Ra
tionalMap Y}   [self : AlgebraicGeometry.Scheme.Rational…
-/
lemma RationalMap.exists_partialMap_over [X.Over S] [Y.Over S] (f : X ⤏ Y) [f.IsOver S] :
    ∃ g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f :=
  IsOver.exists_partialMap_over

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The composition of a rational map and a morphism on the right. -/
/-
**AlgebraicGeometry.Scheme.RationalMap.compHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y Z : AlgebraicGeometry.Scheme} → X.RationalMap Y → (Y ⟶ Z) → X.Rationa
lMap Z
参数：Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of a rational map and a morphism on the right.
-/
def RationalMap.compHom (f : X ⤏ Y) (g : Y ⟶ Z) : X ⤏ Z := by
  refine Quotient.map (PartialMap.compHom · g) ?_ f
  intro f₁ f₂ ⟨W, hW, hWl, hWr, e⟩
  refine ⟨W, hW, hWl, hWr, ?_⟩
  simp only [PartialMap.restrict_domain, PartialMap.restrict_hom, PartialMap.compHom_domain,
    PartialMap.compHom_hom] at e ⊢
  rw [reassoc_of% e]

@[simp]
/-
**AlgebraicGeometry.Scheme.RationalMap.compHom_toRationalMap** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X.PartialMap Y) (g : Y ⟶ Z),   (
f.compHom g).toRationalMap = f.toRationalMap.compHom g
参数：f : X.PartialMap Y；g : Y ⟶ Z；f.compHom g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RationalMap.compHom_toRationalMap (f : X.PartialMap Y) (g : Y ⟶ Z) :
    (f.compHom g).toRationalMap = f.toRationalMap.compHom g := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.RationalMap.id_compHom** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),   (AlgebraicGeometry.Schem
e.RationalMap.id X).compHom f = AlgebraicGeometry.Scheme.Hom.toRationalMap f
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.RationalMap.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.id.eq_1`：∀ (X : AlgebraicGeometry.S
cheme),   AlgebraicGeometry.Scheme.RationalMap.id X = (AlgebraicGeometry.Scheme.
PartialMap.id X).toRationalMap
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.compHom_toRationalMap`：∀ {X Y Z : A
lgebraicGeometry.Scheme} (f : X.PartialMap Y) (g : Y ⟶ Z),   (f.compHom g).toRat
ionalMap = f.toRationalMap.compHom g
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.id_compHom`：id_compHom (f : X ⟶ Y) :
 (PartialMap.id X).compHom f = f.toPartialMap
-/
lemma RationalMap.id_compHom (f : X ⟶ Y) :
    (RationalMap.id X).compHom f = f.toRationalMap := by
  rw [RationalMap.id, ← compHom_toRationalMap, PartialMap.id_compHom]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Over S] [Y.Over S] [Z.Over S] (f : X ⤏ Y) (g : Y ⟶ Z)
    [f.IsOver S] [g.IsOver S] : (f.compHom g).IsOver S where
  exists_partialMap_over := by
    obtain ⟨f, hf, rfl⟩ := f.exists_partialMap_over S
    exact ⟨f.compHom g, inferInstance, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/-
**AlgebraicGeometry.Scheme.PartialMap.exists_restrict_isOver** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (S : AlgebraicGeometry.Scheme) [inst : 
X.Over S] [inst_1 : Y.Over S]   (f : X.PartialMap Y) [AlgebraicGeometry.Scheme.R
ationalMap.IsOver S f.toRationalMap],   ∃ U, ∃ (hU : Dense ↑U) (hU' : U ≤ f.doma
in), AlgebraicGeometry.Scheme.PartialMap.IsOver S (f.restrict U hU hU')
参数：S : AlgebraicGeometry.Scheme；f : X.PartialMap Y；hU : Dense ↑U；hU' : U ≤ f.dom
ain；f.restrict U hU hU'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.IsOver.exists_partialMap_over`：∀ {X
 Y S : AlgebraicGeometry.Scheme} {inst : X.Over S} {inst_1 : Y.Over S} {f : X.Ra
tionalMap Y}   [self : AlgebraicGeometry.Scheme.Rational…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap = g.toRationalMap ↔
 f.equiv g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.IsOver.eq_1`：∀ {X Y : AlgebraicGeome
try.Scheme} (S : AlgebraicGeometry.Scheme) [inst : X.Over S] [inst_1 : Y.Over S]
   (f : X.PartialMap Y), AlgebraicGeo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.instIsOverRestrict`：∀ {X Y S : Algeb
raicGeometry.Scheme} [inst : X.Over S] [inst_1 : Y.Over S] (f : X.PartialMap Y) 
  [AlgebraicGeometry.Scheme.PartialMap.IsOve…
-/
lemma PartialMap.exists_restrict_isOver [X.Over S] [Y.Over S] (f : X.PartialMap Y)
    [f.toRationalMap.IsOver S] : ∃ U hU hU', (f.restrict U hU hU').IsOver S := by
  obtain ⟨f', hf₁, hf₂⟩ := RationalMap.IsOver.exists_partialMap_over (S := S) (f := f.toRationalMap)
  obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp hf₂
  exact ⟨U, hU, hUr, by rw [IsOver, ← e]; infer_instance⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.RationalMap.isOver_iff** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} [inst : X.Over S] [inst_1 : Y.Over S]
 {f : X.RationalMap Y},   AlgebraicGeometry.Scheme.RationalMap.IsOver S f ↔     
f.compHom (Y ↘ S) = AlgebraicGeometry.Scheme.Hom.toRationalMap (X ↘ S)
参数：Y ↘ S；X ↘ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.exists_partialMap_over`：∀ {X Y : Al
gebraicGeometry.Scheme} (S : AlgebraicGeometry.Scheme) [inst : X.Over S] [inst_1
 : Y.Over S]   (f : X.RationalMap Y) [AlgebraicGe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toRationalMap.eq_1`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X.Hom Y), f.toRationalMap = f.toPartialMap.toRationalMap
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.compHom_toRationalMap`：∀ {X Y Z : A
lgebraicGeometry.Scheme} (f : X.PartialMap Y) (g : Y ⟶ Z),   (f.compHom g).toRat
ionalMap = f.toRationalMap.compHom g
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.isOver_iff_eq_restrict`：isOver_iff_e
q_restrict [X.Over S] [Y.Over S] {f : X.PartialMap Y} : f.IsOver S ↔ f.compHom (
Y ↘ S) = (X ↘ S).toPartialMap.restrict _ f.dense…
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.restrict_toRationalMap`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X.PartialMap Y) (U : X.Opens) (hU : Dense ↑U) (hU' :
 U ≤ f.domain),   (f.restrict U hU hU').toRation…
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_surjective`：∀ {X Y : A
lgebraicGeometry.Scheme}, Function.Surjective AlgebraicGeometry.Scheme.PartialMa
p.toRationalMap
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap = g.toRationalMap ↔
 f.equiv g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `CategoryTheory.instHomIsOverOfIsOverTower`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) (S S' : C)   [inst_1 : Categor
yTheory.CanonicallyOverClass X …
· 使用定理 `CategoryTheory.instIsOverTower_2`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (S : C)   [inst_1 : CategoryTheory.CanonicallyOverC
lass X Y] [inst_2 : Ca…
· 使用定理 `CategoryTheory.instIsOverTower`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.IsOverTow…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOverι`：∀ {X : AlgebraicGeometry.Sch
eme} (U : X.Opens), AlgebraicGeometry.Scheme.Hom.IsOver U.ι X
· 使用定理 `CategoryTheory.instHomIsOverOfIsOverTower_1`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) (S S' : C)   [inst_1 : Categ
oryTheory.OverClass X S] [inst_2 …
· 使用定理 `AlgebraicGeometry.instIsOverHomOfLE`：∀ {X : AlgebraicGeometry.Scheme} {U
 V : X.Opens} (h : U ≤ V), AlgebraicGeometry.Scheme.Hom.IsOver (X.homOfLE h) X
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma RationalMap.isOver_iff [X.Over S] [Y.Over S] {f : X ⤏ Y} :
    f.IsOver S ↔ f.compHom (Y ↘ S) = (X ↘ S).toRationalMap := by
  constructor
  · intro h
    obtain ⟨g, hg, e⟩ := f.exists_partialMap_over S
    rw [← e, Hom.toRationalMap, ← compHom_toRationalMap, PartialMap.isOver_iff_eq_restrict.mp hg,
      PartialMap.restrict_toRationalMap]
  · intro e
    obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
    obtain ⟨U, hU, hUl, hUr, e⟩ := PartialMap.toRationalMap_eq_iff.mp e
    exact ⟨⟨f.restrict U hU hUl, by simpa using! e, by simp⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} [inst : X.Over S] [inst_1 : Y.Over S]
 [AlgebraicGeometry.IsReduced X]   [S.IsSeparated] {f : X.PartialMap Y},   Algeb
raicGeometry.Scheme.RationalMap.IsOver S f.toRationalMap ↔ AlgebraicGeometry.Sch
eme.PartialMap.IsOver S f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.exists_restrict_isOver`：∀ {X Y : Alg
ebraicGeometry.Scheme} (S : AlgebraicGeometry.Scheme) [inst : X.Over S] [inst_1 
: Y.Over S]   (f : X.PartialMap Y) [AlgebraicGeo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.isOver_iff`：isOver_iff [X.Over S] [Y
.Over S] {f : X.PartialMap Y} : f.IsOver S ↔ (f.compHom (Y ↘ S)).hom = f.domain.
ι ≫ X ↘ S
· 使用定理 `AlgebraicGeometry.Opens.isDominant_homOfLE`：∀ {X : AlgebraicGeometry.Sch
eme} {U V : X.Opens},   Dense ↑U → ∀ (hU' : U ≤ V), AlgebraicGeometry.IsDominant
 (X.homOfLE hU')
· 使用引理 `AlgebraicGeometry.ext_of_isDominant`：ext_of_isDominant [IsReduced X] {f 
g : X ⟶ Y} [Y.IsSeparated] (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f =
 g
· 使用定理 `AlgebraicGeometry.instIsReducedToScheme`：∀ {X : AlgebraicGeometry.Scheme
} {U : X.Opens} [AlgebraicGeometry.IsReduced X], AlgebraicGeometry.IsReduced ↑U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `CategoryTheory.instHomIsOverOfIsOverTower`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) (S S' : C)   [inst_1 : Categor
yTheory.CanonicallyOverClass X …
· 使用定理 `CategoryTheory.instIsOverTower_2`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (S : C)   [inst_1 : CategoryTheory.CanonicallyOverC
lass X Y] [inst_2 : Ca…
· 使用定理 `CategoryTheory.instIsOverTower`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X : C} (S : C) [inst_1 : CategoryTheory.OverClass X S],   Cate
goryTheory.IsOverTow…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOverι`：∀ {X : AlgebraicGeometry.Sch
eme} (U : X.Opens), AlgebraicGeometry.Scheme.Hom.IsOver U.ι X
· 使用定理 `CategoryTheory.instHomIsOverOfIsOverTower_1`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) (S S' : C)   [inst_1 : Categ
oryTheory.OverClass X S] [inst_2 …
· 使用定理 `AlgebraicGeometry.instIsOverHomOfLE`：∀ {X : AlgebraicGeometry.Scheme} {U
 V : X.Opens} (h : U ≤ V), AlgebraicGeometry.Scheme.Hom.IsOver (X.homOfLE h) X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.HomIsOver.comp_over`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} {S : C}   {inst_1 : CategoryTheory.Ov
erClass X S} {inst_2 : C…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOverToRationalMapOfIsOver`：∀ {X Y S : Alg
ebraicGeometry.Scheme} [inst : X.Over S] [inst_1 : Y.Over S] (f : X.PartialMap Y
)   [AlgebraicGeometry.Scheme.PartialMap.IsOve…
-/
lemma PartialMap.isOver_toRationalMap_iff_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X]
    [S.IsSeparated] {f : X.PartialMap Y} :
    f.toRationalMap.IsOver S ↔ f.IsOver S := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  obtain ⟨U, hU, hU', H⟩ := f.exists_restrict_isOver (S := S)
  rw [isOver_iff]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU _
  exact ext_of_isDominant (ι := X.homOfLE hU') (by simpa using H.1)

section functionField

set_option backward.defeqAttrib.useBackward true in
/-- A rational map restricts to a map from `Spec K(X)`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.RationalMap.fromFunctionField** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   [inst : IrreducibleSpace ↥X] → X.Rati
onalMap Y → (AlgebraicGeometry.Spec X.functionField ⟶ Y)
参数：AlgebraicGeometry.Spec X.functionField ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def RationalMap.fromFunctionField [IrreducibleSpace X] (f : X ⤏ Y) :
    Spec X.functionField ⟶ Y := by
  refine Quotient.lift PartialMap.fromFunctionField ?_ f
  intro f g ⟨W, hW, hWl, hWr, e⟩
  have : f.restrict W hW hWl = g.restrict W hW hWr := by
    ext1
    · rfl
    rw [e]; simp
  rw [← f.fromFunctionField_restrict hW hWl, this, g.fromFunctionField_restrict]

@[simp]
/-
**AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_toRationalMap** 是 Mathl
ib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : IrreducibleSpace ↥X] (f : X.Par
tialMap Y),   f.toRationalMap.fromFunctionField = f.fromFunctionField
参数：f : X.PartialMap Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RationalMap.fromFunctionField_toRationalMap [IrreducibleSpace X] (f : X.PartialMap Y) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField := rfl

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
any `S`-morphism `Spec K(X) ⟶ Y` spreads out to a rational map from `X` to `Y`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.RationalMap.ofFunctionField** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y S : AlgebraicGeometry.Scheme} →   (sX : X ⟶ S) →     (sY : Y ⟶ S) →  
     [inst : AlgebraicGeometry.IsIntegral X] →         [AlgebraicGeometry.Locall
yOfFiniteType sY] →           (f : AlgebraicGeometry.Spec X.functionField ⟶ Y) →
             CategoryTheory.CategoryStruct.comp f sY =                 CategoryT
heory.CategoryStruct.comp (X.fromSpecStalk (genericPoint ↥X)) sX →              
 X.RationalMap Y
参数：sX : X ⟶ S；sY : Y ⟶ S；f : AlgebraicGeometry.Spec X.functionField ⟶ Y；X.fromSp
ecStalk (genericPoint ↥X)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
-/
def RationalMap.ofFunctionField [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y) (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) : X ⤏ Y :=
  (PartialMap.ofFromSpecStalk sX sY f h).toRationalMap
/-
**AlgebraicGeometry.Scheme.RationalMap.fromFunctionField_ofFunctionField** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} (sX : X ⟶ S) (sY : Y ⟶ S) [inst : Alg
ebraicGeometry.IsIntegral X]   [inst_1 : AlgebraicGeometry.LocallyOfFiniteType s
Y] (f : AlgebraicGeometry.Spec X.functionField ⟶ Y)   (h :     CategoryTheory.Ca
tegoryStruct.comp f sY =       CategoryTheory.CategoryStruct.comp (X.fromSpecSta
lk (genericPoint ↥X)) sX),   (AlgebraicGeometry.Scheme.RationalMap.ofFunctionFie
ld sX sY f h).fromFunctionField = f
参数：sX : X ⟶ S；sY : Y ⟶ S；f : AlgebraicGeometry.Spec X.functionField ⟶ Y；h :     
CategoryTheory.CategoryStruct.comp f sY =       CategoryTheory.CategoryStruct.co
mp (X.fromSpecStalk (genericPoint ↥X)) sX；AlgebraicGeometry.Scheme.RationalMap.o
fFunctionField sX sY f h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk`：
fromSpecStalkOfMem_ofFromSpecStalk [IrreducibleSpace X] [LocallyOfFiniteType sY]
 {x : X} [X.IsGermInjectiveAt x] (φ : Spec (X.presheaf.stalk…
-/
lemma RationalMap.fromFunctionField_ofFunctionField [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y) (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    (ofFunctionField sX sY f h).fromFunctionField = f :=
  PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY _ _
/-
**AlgebraicGeometry.Scheme.RationalMap.eq_of_fromFunctionField_eq** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsIntegral X]
 (f g : X.RationalMap Y),   f.fromFunctionField = g.fromFunctionField → f = g
参数：f g : X.RationalMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.exists_rep`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X.RationalMap Y), ∃ g, g.toRationalMap = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap = g.toRationalMap ↔
 f.equiv g
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq`：equi
v_of_fromSpecStalkOfMem_eq [IrreducibleSpace X] {x : X} [X.IsGermInjectiveAt x] 
(f g : X.PartialMap Y) (hxf : x in f.domain) (hxg : x in…
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `AlgebraicGeometry.instIsGermInjectiveOfIsIntegral`：∀ {X : AlgebraicGeome
try.Scheme} [AlgebraicGeometry.IsIntegral X], X.IsGermInjective
-/
lemma RationalMap.eq_of_fromFunctionField_eq [IsIntegral X] (f g : X.RationalMap Y)
    (H : f.fromFunctionField = g.fromFunctionField) : f = g := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  obtain ⟨g, rfl⟩ := g.exists_rep
  refine PartialMap.toRationalMap_eq_iff.mpr ?_
  exact PartialMap.equiv_of_fromSpecStalkOfMem_eq _ _ _ _ H

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
`S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.RationalMap.equivFunctionField** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y S : AlgebraicGeometry.Scheme} →   (sX : X ⟶ S) →     (sY : Y ⟶ S) →  
     [inst : AlgebraicGeometry.IsIntegral X] →         [AlgebraicGeometry.Locall
yOfFiniteType sY] →           { f //               CategoryTheory.CategoryStruct
.comp f sY =                 CategoryTheory.CategoryStruct.comp (X.fromSpecStalk
 (genericPoint ↥X)) sX } ≃             { f // f.compHom sY = AlgebraicGeometry.S
cheme.Hom.toRationalMap sX }
参数：sX : X ⟶ S；sY : Y ⟶ S；X.fromSpecStalk (genericPoint ↥X)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
-/
def RationalMap.equivFunctionField [IsIntegral X] [LocallyOfFiniteType sY] :
    { f : Spec X.functionField ⟶ Y // f ≫ sY = X.fromSpecStalk _ ≫ sX } ≃
      { f : X ⤏ Y // f.compHom sY = sX.toRationalMap } where
  toFun f := ⟨.ofFunctionField sX sY f f.2, PartialMap.toRationalMap_eq_iff.mpr
      ⟨_, PartialMap.dense_domain _, le_rfl, le_top, by simp [PartialMap.ofFromSpecStalk_comp]⟩⟩
  invFun f := ⟨f.1.fromFunctionField, by
    obtain ⟨f, hf⟩ := f
    obtain ⟨f, rfl⟩ := f.exists_rep
    simpa [fromFunctionField_toRationalMap] using! congr(RationalMap.fromFunctionField $hf)⟩
  left_inv f := Subtype.ext (RationalMap.fromFunctionField_ofFunctionField _ _ _ _)
  right_inv f := Subtype.ext (RationalMap.eq_of_fromFunctionField_eq
      (ofFunctionField sX sY f.1.fromFunctionField _) f
      (RationalMap.fromFunctionField_ofFunctionField _ _ _ _))

/--
Given `S`-schemes `X` and `Y` such that `Y` is locally of finite type and `X` is integral,
`S`-morphisms `Spec K(X) ⟶ Y` correspond bijectively to `S`-rational maps from `X` to `Y`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldOver** 是 Mathlib 中的一个定义
，位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y S : AlgebraicGeometry.Scheme} →   [inst : X.Over S] →     [inst_1 : Y
.Over S] →       [inst_2 : AlgebraicGeometry.IsIntegral X] →         [AlgebraicG
eometry.LocallyOfFiniteType (Y ↘ S)] →           { f // AlgebraicGeometry.Scheme
.Hom.IsOver f S } ≃ { f // AlgebraicGeometry.Scheme.RationalMap.IsOver S f }
参数：Y ↘ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
-/
def RationalMap.equivFunctionFieldOver [X.Over S] [Y.Over S] [IsIntegral X]
    [LocallyOfFiniteType (Y ↘ S)] :
    { f : Spec X.functionField ⟶ Y // f.IsOver S } ≃ { f : X ⤏ Y // f.IsOver S } :=
  ((Equiv.subtypeEquivProp (by simp only [Hom.isOver_iff]; rfl)).trans
    (RationalMap.equivFunctionField (X ↘ S) (Y ↘ S))).trans
      (Equiv.subtypeEquivProp (by ext f; rw [RationalMap.isOver_iff]))

end functionField

section domain

/-- The domain of definition of a rational map. -/
/-
**AlgebraicGeometry.Scheme.RationalMap.domain** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.RationalMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.RationalMap Y → X.Opens
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The domain of definition of a rational map.
-/
def RationalMap.domain (f : X ⤏ Y) : X.Opens :=
  sSup { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }
/-
**AlgebraicGeometry.Scheme.PartialMap.le_domain_toRationalMap** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y), f.domain ≤ f.toRa
tionalMap.domain
参数：f : X.PartialMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
lemma PartialMap.le_domain_toRationalMap (f : X.PartialMap Y) :
    f.domain ≤ f.toRationalMap.domain :=
  le_sSup ⟨f, rfl, rfl⟩
/-
**AlgebraicGeometry.Scheme.RationalMap.mem_domain** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X.RationalMap Y} {x : ↥X},   x ∈ f
.domain ↔ ∃ g, x ∈ g.domain ∧ g.toRationalMap = f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `TopologicalSpace.Opens.mem_sSup`：mem_sSup {Us : Set (Opens α)} {x : α} :
 x in sSup Us ↔ exists u in Us, x in u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma RationalMap.mem_domain {f : X ⤏ Y} {x} :
    x ∈ f.domain ↔ ∃ g : X.PartialMap Y, x ∈ g.domain ∧ g.toRationalMap = f :=
  TopologicalSpace.Opens.mem_sSup.trans (by simp [@and_comm (x ∈ _)])
/-
**AlgebraicGeometry.Scheme.RationalMap.dense_domain** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), Dense ↑f.domain
参数：f : X.RationalMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.le_domain_toRationalMap`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X.PartialMap Y), f.domain ≤ f.toRationalMap.domain
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
-/
lemma RationalMap.dense_domain (f : X ⤏ Y) : Dense (X := X) f.domain :=
  f.inductionOn (fun g ↦ g.dense_domain.mono g.le_domain_toRationalMap)

set_option backward.isDefEq.respectTransparency false in
/-- The open cover of the domain of `f : X ⤏ Y`,
consisting of all the domains of the partial maps in the equivalence class. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.RationalMap.openCoverDomain** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X.RationalMap Y) → (↑f.domain).Ope
nCover
参数：f : X.RationalMap Y；↑f.domain。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def RationalMap.openCoverDomain (f : X ⤏ Y) : f.domain.toScheme.OpenCover where
  I₀ := { PartialMap.domain g | (g) (_ : g.toRationalMap = f) }
  X U := U.1.toScheme
  f U := X.homOfLE (le_sSup U.2)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    use ⟨_, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.1⟩
    exact ⟨⟨x.1, (TopologicalSpace.Opens.mem_sSup.mp x.2).choose_spec.2⟩, Subtype.ext (by simp)⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `f : X ⤏ Y` is a rational map from a reduced scheme to a separated scheme,
then `f` can be represented as a partial map on its domain of definition. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.RationalMap.toPartialMap** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.RationalMap`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → [AlgebraicGeometry.IsReduced X] → [Y.Is
Separated] → X.RationalMap Y → X.PartialMap Y
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.dense_domain`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X.RationalMap Y), Dense ↑f.domain
-/
def RationalMap.toPartialMap [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) : X.PartialMap Y := by
  refine ⟨f.domain, f.dense_domain, f.openCoverDomain.glueMorphisms
    (fun x ↦ (X.isoOfEq x.2.choose_spec.2).inv ≫ x.2.choose.hom) ?_⟩
  intro x y
  let g (x : f.openCoverDomain.I₀) := x.2.choose
  have hg₁ (x) : (g x).toRationalMap = f := x.2.choose_spec.1
  have hg₂ (x) : (g x).domain = x.1 := x.2.choose_spec.2
  refine (cancel_epi (isPullback_opens_inf_le (le_sSup x.2) (le_sSup y.2)).isoPullback.hom).mp ?_
  simp only [openCoverDomain, IsPullback.isoPullback_hom_fst_assoc,
    IsPullback.isoPullback_hom_snd_assoc]
  change _ ≫ _ ≫ (g x).hom = _ ≫ _ ≫ (g y).hom
  simp_rw [← cancel_epi (X.isoOfEq congr($(hg₂ x) ⊓ $(hg₂ y))).hom, ← Category.assoc]
  convert! (PartialMap.equiv_iff_of_isSeparated (S := ⊤_ _) (f := g x) (g := g y)).mp ?_ using 1
  · dsimp; congr 1; simp [g, ← cancel_mono (Opens.ι _)]
  · dsimp; congr 1; simp [g, ← cancel_mono (Opens.ι _)]
  · rw [← PartialMap.toRationalMap_eq_iff, hg₁, hg₁]

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.toPartialMap_toRationalMap_restrict** 是 Ma
thlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsReduced X] 
[inst_1 : Y.IsSeparated] (f : X.PartialMap Y),   (f.toRationalMap.toPartialMap.r
estrict f.domain ⋯ ⋯).hom = f.hom
参数：f : X.PartialMap Y；f.toRationalMap.toPartialMap.restrict f.domain ⋯ ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.le_domain_toRationalMap`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X.PartialMap Y), f.domain ≤ f.toRationalMap.domain
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparate
d`：equiv_iff_of_domain_eq_of_isSeparated [X.Over S] [Y.Over S] [IsReduced X] [Is
Separated (Y ↘ S)] {f g : X.PartialMap Y} (hfg : f.domain = g.d…
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.instIsSeparatedOfIsSeparated`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [X.IsSeparated], AlgebraicGeometry.IsSeparated f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AlgebraicGeometry.instIsOverTerminalScheme`：∀ {X Y : AlgebraicGeometry.S
cheme} [inst : X.Over (⊤_ AlgebraicGeometry.Scheme)]   [inst_1 : Y.Over (⊤_ Alge
braicGeometry.Scheme)] (f : X ⟶ …
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap = g.toRationalMap ↔
 f.equiv g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext_iff`：ext_iff (f g : X.PartialMap
 Y) : f = g ↔ exists e : f.domain = g.domain, f.hom = (X.isoOfEq e).hom ≫ g.hom
-/
lemma PartialMap.toPartialMap_toRationalMap_restrict [IsReduced X] [Y.IsSeparated]
    (f : X.PartialMap Y) : (f.toRationalMap.toPartialMap.restrict _ f.dense_domain
      f.le_domain_toRationalMap).hom = f.hom := by
  dsimp [RationalMap.toPartialMap]
  refine (f.toRationalMap.openCoverDomain.ι_glueMorphisms _ _ ⟨_, f, rfl, rfl⟩).trans ?_
  generalize_proofs _ _ H _
  have : H.choose = f := (equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ _) H.choose_spec.2).mp
    (toRationalMap_eq_iff.mp H.choose_spec.1)
  exact ((ext_iff _ _).mp this.symm).choose_spec.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.RationalMap.toRationalMap_toPartialMap** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsReduced X] 
[inst_1 : Y.IsSeparated]   (f : X.RationalMap Y), f.toPartialMap.toRationalMap =
 f
参数：f : X.RationalMap Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_surjective`：∀ {X Y : A
lgebraicGeometry.Scheme}, Function.Surjective AlgebraicGeometry.Scheme.PartialMa
p.toRationalMap
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.le_domain_toRationalMap`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X.PartialMap Y), f.domain ≤ f.toRationalMap.domain
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.restrict_toRationalMap`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X.PartialMap Y) (U : X.Opens) (hU : Dense ↑U) (hU' :
 U ≤ f.domain),   (f.restrict U hU hU').toRation…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toPartialMap_toRationalMap_restrict`
：∀ {X Y : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsReduced X] [inst
_1 : Y.IsSeparated] (f : X.PartialMap Y),   (f.toRationalMap.…
-/
lemma RationalMap.toRationalMap_toPartialMap [IsReduced X] [Y.IsSeparated]
    (f : X ⤏ Y) : f.toPartialMap.toRationalMap = f := by
  obtain ⟨f, rfl⟩ := PartialMap.toRationalMap_surjective f
  trans (f.toRationalMap.toPartialMap.restrict _
    f.dense_domain f.le_domain_toRationalMap).toRationalMap
  · simp
  · congr 1
    exact PartialMap.ext _ f rfl (by simpa using f.toPartialMap_toRationalMap_restrict)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsReduced X] [Y.IsSeparated] [S.IsSeparated] [X.Over S] [Y.Over S]
    (f : X ⤏ Y) [f.IsOver S] : f.toPartialMap.IsOver S := by
  rw [← PartialMap.isOver_toRationalMap_iff_of_isSeparated, f.toRationalMap_toPartialMap]
  infer_instance

end domain

end Scheme

end AlgebraicGeometry

