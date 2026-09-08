/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Basic

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/

@[expose] public section


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u} [Category.{v} C]

/-- The objects for the Kleisli category of the monad `T : Monad C`, which are the same
thing as objects of the base category `C`.
-/
/-
**CategoryTheory.Kleisli** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Monad C → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The objects for the Kleisli category of the monad `T : Monad C`, which are the s
ame
thing as objects of the base category `C`.
-/
structure Kleisli (T : Monad C) where mk (T) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Kleisli

variable {T : Monad C}

/-
**CategoryTheory.Kleisli.mk_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Kleisli
`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {T : CategoryTheo
ry.Monad C} (c : CategoryTheory.Kleisli T),   { of := c.of } = c
参数：c : CategoryTheory.Kleisli T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_of (c : Kleisli T) : Kleisli.mk T c.of = c := rfl
/-
**CategoryTheory.Kleisli.of_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Kleisli
`。
形式化陈述：of_mk (c : C) : (Kleisli.mk T c).of = c
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_mk (c : C) : (Kleisli.mk T c).of = c := rfl

/-- For (T : Monad C), morphisms `c ⟶ c'` in the Kleisli category of `T` are
morphisms ` c ⟶ T.obj c'` in `C`. -/
/-
**CategoryTheory.Kleisli.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Kleisli
`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {T : Cate
goryTheory.Monad C} → CategoryTheory.Kleisli T → CategoryTheory.Kleisli T → Type
 v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For (T : Monad C), morphisms `c ⟶ c'` in the Kleisli category of `T` are
morphisms ` c ⟶ T.obj c'` in `C`.
-/
structure Hom (c c' : Kleisli T) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : c.of ⟶ T.obj c'.of
/-
**CategoryTheory.Kleisli.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Kleisli`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) := ⟨.mk T default⟩

variable (T)

attribute [local ext] Hom in
/-- The Kleisli category on a monad `T`.
cf Definition 5.2.9 in [Riehl][riehl2017]. -/
@[simps!]
/-
**CategoryTheory.Kleisli.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Klei
sli`。
形式化陈述：category : Category (Kleisli T) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Kleisli category on a monad `T`.
cf Definition 5.2.9 in [Riehl][riehl2017].
-/
instance category : Category (Kleisli T) where
  Hom X Y := Hom X Y
  id X := .mk <| T.η.app X.of
  comp {_} {_} {Z} f g := .mk <| f.of ≫ T.map g.of ≫ T.μ.app Z.of
  id_comp {X} {Y} f := by
    ext
    dsimp
    rw [← T.η.naturality_assoc f.of, T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp [Monad.assoc, T.mu_naturality_assoc]

variable {T} in
attribute [local ext] Hom in
@[ext]
/-
**CategoryTheory.Kleisli.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Kleis
li`。
形式化陈述：hom_ext {x y : Kleisli T} {f g : x ⟶ y} (h : f.of = g.of) : f = g
参数：h : f.of = g.of。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Kleisli.Hom.ext`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {T : CategoryTheory.Monad C} {c c' : CategoryTheory.Kleisli T} 
  {x y : c.Hom c'}, …
-/
lemma hom_ext {x y : Kleisli T} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
/-
**CategoryTheory.Kleisli.Adjunction.toKleisli** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Kleisli.Adjunction`。
形式化陈述：toKleisli : C ⥤ Kleisli T where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`.
-/
def toKleisli : C ⥤ Kleisli T where
  obj X := .mk T X
  map {X} {Y} f := .mk <| f ≫ T.η.app Y
  map_comp {X} {Y} {Z} f g := by
    unfold_projs
    simp [← T.η.naturality g]

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
/-
**CategoryTheory.Kleisli.Adjunction.fromKleisli** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Kleisli.Adjunction`。
形式化陈述：fromKleisli : Kleisli T ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`.
-/
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X.of
  map {_} {Y} f := T.map f.of ≫ T.μ.app Y.of
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    simp [← T.μ.naturality_assoc g.of, T.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
/-
**CategoryTheory.Kleisli.Adjunction.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Kleisli.Adjunction`。
形式化陈述：adj : toKleisli T ⊣ fromKleisli T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
cf Lemma 5.2.11 of [Riehl][riehl2017].
-/
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := f.of, invFun f := .mk f }
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        ext
        simp [← T.η.naturality_assoc g] }

set_option backward.defeqAttrib.useBackward true in
/-- The composition of the adjunction gives the original functor. -/
/-
**CategoryTheory.Kleisli.Adjunction.toKleisliCompFromKleisliIsoSelf** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Kleisli.Adjunction`。
形式化陈述：toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of the adjunction gives the original functor.
-/
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Kleisli

/-- The objects for the co-Kleisli category of the comonad `U : Comonad C`, which are the same
thing as objects of the base category `C`.
-/
/-
**CategoryTheory.Cokleisli** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Comonad C → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The objects for the co-Kleisli category of the comonad `U : Comonad C`, which ar
e the same
thing as objects of the base category `C`.
-/
structure Cokleisli (U : Comonad C) where mk (U) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Cokleisli

variable (U : Comonad C)

/-
**CategoryTheory.Cokleisli.mk_of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cokle
isli`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (U : CategoryTheo
ry.Comonad C)   (c : CategoryTheory.Cokleisli U), { of := c.of } = c
参数：U : CategoryTheory.Comonad C；c : CategoryTheory.Cokleisli U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_of (c : Cokleisli U) : Cokleisli.mk U c.of = c := rfl
/-
**CategoryTheory.Cokleisli.of_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cokle
isli`。
形式化陈述：of_mk (c : C) : (Cokleisli.mk U c).of = c
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_mk (c : C) : (Cokleisli.mk U c).of = c := rfl

variable {U} in
/-- For (U : Comonad C), morphisms `c ⟶ c'` in the Cokleisli category of `U` are
morphisms ` U.obj c ⟶ c'` in `C`. -/
/-
**CategoryTheory.Cokleisli.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Cokle
isli`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {U : Cate
goryTheory.Comonad C} → CategoryTheory.Cokleisli U → CategoryTheory.Cokleisli U 
→ Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For (U : Comonad C), morphisms `c ⟶ c'` in the Cokleisli category of `U` are
morphisms ` U.obj c ⟶ c'` in `C`.
-/
structure Hom (c c' : Cokleisli U) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : U.obj c.of ⟶ c'.of
/-
**CategoryTheory.Cokleisli.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cokleisli`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) := ⟨.mk U default⟩

/-- The co-Kleisli category on a comonad `U`. -/
@[simps!]
/-
**CategoryTheory.Cokleisli.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
kleisli`。
形式化陈述：category : Category (Cokleisli U) where Hom X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The co-Kleisli category on a comonad `U`.
-/
instance category : Category (Cokleisli U) where
  Hom X Y := Hom X Y
  id X := .mk <| U.ε.app X.of
  comp f g := .mk <| U.δ.app _ ≫ (U : C ⥤ C).map f.of ≫ g.of

variable {T} in
attribute [local ext] Hom in
@[ext]
/-
**CategoryTheory.Cokleisli.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cok
leisli`。
形式化陈述：hom_ext {x y : Cokleisli U} {f g : x ⟶ y} (h : f.of = g.of) : f = g
参数：h : f.of = g.of。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Cokleisli.Hom.ext`：∀ {C : Type u} {inst : CategoryTheory.
Category.{v, u} C} {U : CategoryTheory.Comonad C}   {c c' : CategoryTheory.Cokle
isli U} {x y : c.Hom c…
-/
lemma hom_ext {x y : Cokleisli U} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
/-
**CategoryTheory.Cokleisli.Adjunction.toCokleisli** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Cokleisli.Adjunction`。
形式化陈述：toCokleisli : C ⥤ Cokleisli U where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`.
-/
def toCokleisli : C ⥤ Cokleisli U where
  obj X := .mk U X
  map {X} {_} f := .mk (U.ε.app X ≫ f)

/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
/-
**CategoryTheory.Cokleisli.Adjunction.fromCokleisli** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Cokleisli.Adjunction`。
形式化陈述：fromCokleisli : Cokleisli U ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`.
-/
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X.of
  map {X} {_} f := U.δ.app X.of ≫ U.map f.of
  map_id _ := U.right_counit _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The co-Kleisli adjunction which gives rise to the comonad `(U, ε_ U, δ_ U)`. -/
/-
**CategoryTheory.Cokleisli.Adjunction.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Cokleisli.Adjunction`。
形式化陈述：adj : fromCokleisli U ⊣ toCokleisli U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The co-Kleisli adjunction which gives rise to the comonad `(U, ε_ U, δ_ U)`.
-/
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := .mk f, invFun f := f.of }
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by cat_disch }

set_option backward.defeqAttrib.useBackward true in
/-- The composition of the adjunction gives the original functor. -/
/-
**CategoryTheory.Cokleisli.Adjunction.toCokleisliCompFromCokleisliIsoSelf** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Cokleisli.Adjunction`。
形式化陈述：toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of the adjunction gives the original functor.
-/
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Cokleisli

end CategoryTheory

