/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Preadditive.Comma

/-!
# Homotopies in the arrow category

We define left and right homotopies between morphisms of `Arrow V`, where `V` is
a preadditive category.

TODO: Define the preadditive categories `LeftFreyd V` (resp. `RightFreyd V`) obtained by
taking the quotient of `Arrow V` by the left (resp. right) homotopy relation. If `V`
has binary biproducts, this will have all kernels (resp. cokernels) and will be the
category obtained by freely adjoining kernels (resp. cokernels) to `V`.

-/

@[expose] public section

noncomputable section

open CategoryTheory Category

variable {V : Type*} [Category* V] [Preadditive V]

namespace CategoryTheory.Arrow

variable {u v w : Arrow V} (f g : u ⟶ v)

/-- A left homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
/-
**CategoryTheory.Arrow.LeftHomotopy** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Ar
row`。
形式化陈述：LeftHomotopy where /-- A "diagonal" morphism from the right object of `u` 
to the left object of `v`. -/ hom : u.right ⟶ v.left /-- The difference of the l
eft morphisms factors through `hom`. -/ comm : f.left - g.left = u.hom ≫ hom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left homotopy on morphisms in the category of arrows of a preadditive category
.
-/
structure LeftHomotopy where
/-- A "diagonal" morphism from the right object of `u` to the left object of `v`. -/
  hom : u.right ⟶ v.left
/-- The difference of the left morphisms factors through `hom`. -/
  comm : f.left - g.left = u.hom ≫ hom := by cat_disch

/-- A right homotopy on morphisms in the category of arrows of a preadditive category. -/
@[ext]
/-
**CategoryTheory.Arrow.RightHomotopy** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.A
rrow`。
形式化陈述：RightHomotopy where /-- A "diagonal" morphism from the right object of `u`
 to the left object of `v`. -/ hom : u.right ⟶ v.left /-- The difference of the 
right morphisms factors through `hom`. -/ comm : f.right - g.right = hom ≫ v.hom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right homotopy on morphisms in the category of arrows of a preadditive categor
y.
-/
structure RightHomotopy where
  /-- A "diagonal" morphism from the right object of `u` to the left object of `v`. -/
  hom : u.right ⟶ v.left
  /-- The difference of the right morphisms factors through `hom`. -/
  comm : f.right - g.right = hom ≫ v.hom := by cat_disch

variable {f g}

namespace LeftHomotopy

/-- `f` is left homotopic to `g` iff `f - g` is left homotopic to `0`. -/
/-
**CategoryTheory.Arrow.LeftHomotopy.equivSubZero** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Arrow.LeftHomotopy`。
形式化陈述：equivSubZero : LeftHomotopy f g ≃ LeftHomotopy (f - g) 0 where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is left homotopic to `g` iff `f - g` is left homotopic to `0`.
-/
def equivSubZero : LeftHomotopy f g ≃ LeftHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal maps of arrows are left homotopic. -/
@[simps]
/-
**CategoryTheory.Arrow.LeftHomotopy.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Arrow.LeftHomotopy`。
形式化陈述：ofEq (h : f = g) : LeftHomotopy f g where hom
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equal maps of arrows are left homotopic.
-/
def ofEq (h : f = g) : LeftHomotopy f g where
  hom := 0

/-- Every map of arrows is left homotopic to itself. -/
@[simps!, refl]
/-
**CategoryTheory.Arrow.LeftHomotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Arrow.LeftHomotopy`。
形式化陈述：refl (f : u ⟶ v) : LeftHomotopy f f
参数：f : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every map of arrows is left homotopic to itself.
-/
def refl (f : u ⟶ v) : LeftHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is left homotopic to `g` iff `g` is left homotopic to `f`. -/
@[simps!, symm]
/-
**CategoryTheory.Arrow.LeftHomotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Arrow.LeftHomotopy`。
形式化陈述：symm {f g : u ⟶ v} (h : LeftHomotopy f g) : LeftHomotopy g f where hom
参数：h : LeftHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is left homotopic to `g` iff `g` is left homotopic to `f`.
-/
def symm {f g : u ⟶ v} (h : LeftHomotopy f g) : LeftHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- Left homotopy is a transitive relation. -/
@[simps!, trans]
/-
**CategoryTheory.Arrow.LeftHomotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Arrow.LeftHomotopy`。
形式化陈述：trans {e f g : u ⟶ v} (h : LeftHomotopy e f) (k : LeftHomotopy f g) : Left
Homotopy e g where hom
参数：h : LeftHomotopy e f；k : LeftHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopy is a transitive relation.
-/
def trans {e f g : u ⟶ v} (h : LeftHomotopy e f) (k : LeftHomotopy f g) : LeftHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- The sum of two left homotopies is a left homotopy between the sum of the respective
morphisms. -/
@[simps!]
/-
**CategoryTheory.Arrow.LeftHomotopy.add** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Arrow.LeftHomotopy`。
形式化陈述：add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ 
g₂) : LeftHomotopy (f₁ + f₂) (g₁ + g₂) where hom
参数：h₁ : LeftHomotopy f₁ g₁；h₂ : LeftHomotopy f₂ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two left homotopies is a left homotopy between the sum of the respect
ive
morphisms.
-/
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) :
    LeftHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- Left homotopy is closed under composition (on the right). -/
@[simps]
/-
**CategoryTheory.Arrow.LeftHomotopy.compRight** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Arrow.LeftHomotopy`。
形式化陈述：compRight {e f : u ⟶ v} (h : LeftHomotopy e f) (g : v ⟶ w) : LeftHomotopy 
(e ≫ g) (f ≫ g) where hom
参数：h : LeftHomotopy e f；g : v ⟶ w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopy is closed under composition (on the right).
-/
def compRight {e f : u ⟶ v} (h : LeftHomotopy e f) (g : v ⟶ w) :
    LeftHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- Left homotopy is closed under composition (on the left). -/
@[simps]
/-
**CategoryTheory.Arrow.LeftHomotopy.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Arrow.LeftHomotopy`。
形式化陈述：compLeft {f g : v ⟶ w} (h : LeftHomotopy f g) (e : u ⟶ v) : LeftHomotopy (
e ≫ f) (e ≫ g) where hom
参数：h : LeftHomotopy f g；e : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopy is closed under composition (on the left).
-/
def compLeft {f g : v ⟶ w} (h : LeftHomotopy f g) (e : u ⟶ v) :
    LeftHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← reassoc_of% e.w, ← h.comm]

/-- Left homotopy is closed under composition. -/
@[simps!]
/-
**CategoryTheory.Arrow.LeftHomotopy.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Arrow.LeftHomotopy`。
形式化陈述：comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w} (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftH
omotopy f₂ g₂) : LeftHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂)
参数：h₁ : LeftHomotopy f₁ g₁；h₂ : LeftHomotopy f₂ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left homotopy is closed under composition.
-/
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : LeftHomotopy f₁ g₁) (h₂ : LeftHomotopy f₂ g₂) : LeftHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- A variant of `LeftHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
/-
**CategoryTheory.Arrow.LeftHomotopy.compRightId** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Arrow.LeftHomotopy`。
形式化陈述：compRightId {f : u ⟶ u} (h : LeftHomotopy f (𝟙 u)) (g : u ⟶ v) : LeftHomot
opy (f ≫ g) g
参数：h : LeftHomotopy f (𝟙 u)；g : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `LeftHomotopy.compRight` useful for dealing with homotopy equivalen
ces.
-/
def compRightId {f : u ⟶ u} (h : LeftHomotopy f (𝟙 u)) (g : u ⟶ v) : LeftHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- A variant of `LeftHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
/-
**CategoryTheory.Arrow.LeftHomotopy.compLeftId** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Arrow.LeftHomotopy`。
形式化陈述：compLeftId {f : v ⟶ v} (h : LeftHomotopy f (𝟙 v)) (g : u ⟶ v) : LeftHomoto
py (g ≫ f) g
参数：h : LeftHomotopy f (𝟙 v)；g : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `LeftHomotopy.compLeft` useful for dealing with homotopy equivalenc
es.
-/
def compLeftId {f : v ⟶ v} (h : LeftHomotopy f (𝟙 v)) (g : u ⟶ v) : LeftHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end LeftHomotopy

namespace RightHomotopy

/-- `f` is right homotopic to `g` iff `f - g` is righthomotopic to `0`. -/
/-
**CategoryTheory.Arrow.RightHomotopy.equivSubZero** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Arrow.RightHomotopy`。
形式化陈述：equivSubZero : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is right homotopic to `g` iff `f - g` is righthomotopic to `0`.
-/
def equivSubZero : RightHomotopy f g ≃ RightHomotopy (f - g) 0 where
  toFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  invFun h :=
    { hom := h.hom
      comm := by simp [← h.comm]}
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equal maps of arrows are right homotopic. -/
@[simps]
/-
**CategoryTheory.Arrow.RightHomotopy.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Arrow.RightHomotopy`。
形式化陈述：ofEq (h : f = g) : RightHomotopy f g where hom
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equal maps of arrows are right homotopic.
-/
def ofEq (h : f = g) : RightHomotopy f g where
  hom := 0

/-- Every map of arrows is right homotopic to itself. -/
@[simps!, refl]
/-
**CategoryTheory.Arrow.RightHomotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Arrow.RightHomotopy`。
形式化陈述：refl (f : u ⟶ v) : RightHomotopy f f
参数：f : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every map of arrows is right homotopic to itself.
-/
def refl (f : u ⟶ v) : RightHomotopy f f :=
  ofEq (rfl : f = f)

/-- `f` is right homotopic to `g` iff `g` is right homotopic to `f`. -/
@[simps!, symm]
/-
**CategoryTheory.Arrow.RightHomotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Arrow.RightHomotopy`。
形式化陈述：symm {f g : u ⟶ v} (h : RightHomotopy f g) : RightHomotopy g f where hom
参数：h : RightHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f` is right homotopic to `g` iff `g` is right homotopic to `f`.
-/
def symm {f g : u ⟶ v} (h : RightHomotopy f g) : RightHomotopy g f where
  hom := -h.hom
  comm := by simp [← h.comm]

/-- Right homotopy is a transitive relation. -/
@[simps!, trans]
/-
**CategoryTheory.Arrow.RightHomotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Arrow.RightHomotopy`。
形式化陈述：trans {e f g : u ⟶ v} (h : RightHomotopy e f) (k : RightHomotopy f g) : Ri
ghtHomotopy e g where hom
参数：h : RightHomotopy e f；k : RightHomotopy f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopy is a transitive relation.
-/
def trans {e f g : u ⟶ v} (h : RightHomotopy e f) (k : RightHomotopy f g) : RightHomotopy e g where
  hom := h.hom + k.hom
  comm := by simp [← h.comm, ← k.comm]

/-- The sum of two right homotopies is a right homotopy between the sum of the respective
morphisms. -/
@[simps!]
/-
**CategoryTheory.Arrow.RightHomotopy.add** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Arrow.RightHomotopy`。
形式化陈述：add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f
₂ g₂) : RightHomotopy (f₁ + f₂) (g₁ + g₂) where hom
参数：h₁ : RightHomotopy f₁ g₁；h₂ : RightHomotopy f₂ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two right homotopies is a right homotopy between the sum of the respe
ctive
morphisms.
-/
def add {f₁ g₁ f₂ g₂ : u ⟶ v} (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) :
    RightHomotopy (f₁ + f₂) (g₁ + g₂) where
  hom := h₁.hom + h₂.hom
  comm := by simp [← h₁.comm, ← h₂.comm, add_sub_add_comm]

/-- Right homotopy is closed under composition (on the right). -/
@[simps]
/-
**CategoryTheory.Arrow.RightHomotopy.compRight** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Arrow.RightHomotopy`。
形式化陈述：compRight {e f : u ⟶ v} (h : RightHomotopy e f) (g : v ⟶ w) : RightHomotop
y (e ≫ g) (f ≫ g) where hom
参数：h : RightHomotopy e f；g : v ⟶ w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopy is closed under composition (on the right).
-/
def compRight {e f : u ⟶ v} (h : RightHomotopy e f) (g : v ⟶ w) :
    RightHomotopy (e ≫ g) (f ≫ g) where
  hom := h.hom ≫ g.left
  comm := by simp [← reassoc_of% h.comm]

/-- Right homotopy is closed under composition (on the left). -/
@[simps]
/-
**CategoryTheory.Arrow.RightHomotopy.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Arrow.RightHomotopy`。
形式化陈述：compLeft {f g : v ⟶ w} (h : RightHomotopy f g) (e : u ⟶ v) : RightHomotopy
 (e ≫ f) (e ≫ g) where hom
参数：h : RightHomotopy f g；e : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopy is closed under composition (on the left).
-/
def compLeft {f g : v ⟶ w} (h : RightHomotopy f g) (e : u ⟶ v) :
    RightHomotopy (e ≫ f) (e ≫ g) where
  hom := e.right ≫ h.hom
  comm := by simp [← h.comm]

/-- Right homotopy is closed under composition. -/
@[simps!]
/-
**CategoryTheory.Arrow.RightHomotopy.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Arrow.RightHomotopy`。
形式化陈述：comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w} (h₁ : RightHomotopy f₁ g₁) (h₂ : Righ
tHomotopy f₂ g₂) : RightHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂)
参数：h₁ : RightHomotopy f₁ g₁；h₂ : RightHomotopy f₂ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right homotopy is closed under composition.
-/
def comp {f₁ g₁ : u ⟶ v} {f₂ g₂ : v ⟶ w}
    (h₁ : RightHomotopy f₁ g₁) (h₂ : RightHomotopy f₂ g₂) : RightHomotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
  (h₁.compRight _).trans (h₂.compLeft _)

/-- A variant of `RightHomotopy.compRight` useful for dealing with homotopy equivalences. -/
@[simps!]
/-
**CategoryTheory.Arrow.RightHomotopy.compRightId** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Arrow.RightHomotopy`。
形式化陈述：compRightId {f : u ⟶ u} (h : RightHomotopy f (𝟙 u)) (g : u ⟶ v) : RightHom
otopy (f ≫ g) g
参数：h : RightHomotopy f (𝟙 u)；g : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `RightHomotopy.compRight` useful for dealing with homotopy equivale
nces.
-/
def compRightId {f : u ⟶ u} (h : RightHomotopy f (𝟙 u)) (g : u ⟶ v) : RightHomotopy (f ≫ g) g :=
  (h.compRight g).trans (ofEq <| id_comp _)

/-- A variant of `RightHomotopy.compLeft` useful for dealing with homotopy equivalences. -/
@[simps!]
/-
**CategoryTheory.Arrow.RightHomotopy.compLeftId** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Arrow.RightHomotopy`。
形式化陈述：compLeftId {f : v ⟶ v} (h : RightHomotopy f (𝟙 v)) (g : u ⟶ v) : RightHomo
topy (g ≫ f) g
参数：h : RightHomotopy f (𝟙 v)；g : u ⟶ v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `RightHomotopy.compLeft` useful for dealing with homotopy equivalen
ces.
-/
def compLeftId {f : v ⟶ v} (h : RightHomotopy f (𝟙 v)) (g : u ⟶ v) : RightHomotopy (g ≫ f) g :=
  (h.compLeft g).trans (ofEq <| comp_id _)

end RightHomotopy

variable (V)

/-- The left homotopy relation on morphisms of `Arrow V`. -/
/-
**CategoryTheory.Arrow.leftHomotopic** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
rrow`。
形式化陈述：leftHomotopic : HomRel (Arrow V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homotopy relation on morphisms of `Arrow V`.
-/
def leftHomotopic : HomRel (Arrow V) := fun _ _ f g => Nonempty (LeftHomotopy f g)
/-
**CategoryTheory.Arrow.leftHomotopy_congruence** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Arrow`。
形式化陈述：leftHomotopy_congruence : Congruence (leftHomotopic V) where equivalence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance leftHomotopy_congruence : Congruence (leftHomotopic V) where
  equivalence :=
    { refl := fun C => ⟨LeftHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

/-- The left homotopy relation on morphisms of `Arrow V`. -/
/-
**CategoryTheory.Arrow.rightHomotopic** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Arrow`。
形式化陈述：rightHomotopic : HomRel (Arrow V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homotopy relation on morphisms of `Arrow V`.
-/
def rightHomotopic : HomRel (Arrow V) := fun _ _ f g => Nonempty (RightHomotopy f g)
/-
**CategoryTheory.Arrow.rightHomotopy_congruence** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Arrow`。
形式化陈述：rightHomotopy_congruence : Congruence (rightHomotopic V) where equivalence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance rightHomotopy_congruence : Congruence (rightHomotopic V) where
  equivalence :=
    { refl := fun C => ⟨RightHomotopy.refl C⟩
      symm := fun ⟨w⟩ => ⟨w.symm⟩
      trans := fun ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ }
  comp_left := fun _ _ _ ⟨i⟩ => ⟨i.compLeft _⟩
  comp_right := fun _ ⟨i⟩ => ⟨i.compRight _⟩

end CategoryTheory.Arrow

