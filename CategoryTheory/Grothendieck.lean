/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj b`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).toFunctor.obj f ⟶ f'`

`Grothendieck.functor` makes the Grothendieck construction into a functor from the functor category
`C ⥤ Cat` to the over category `Over C` in the category of categories.

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consist again of `β : b ⟶ b'` and `φ : f ⟶ (G.map (op β)).obj f'`.

## Notable constructions

- `Grothendieck F` is the Grothendieck construction.
- Elements of `Grothendieck F` whose base is `c : C` can be transported along `f : c ⟶ d` using
  `transport`.
- A natural transformation `α : F ⟶ G` induces `map α : Grothendieck F ⥤ Grothendieck G`.
- The Grothendieck construction and `map` together form a functor (`functor`) from the functor
  category `E ⥤ Cat` to the over category `Over E`.
- A functor `G : D ⥤ C` induces `pre F G : Grothendieck (G ⋙ F) ⥤ Grothendieck F`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of a functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/

@[expose] public section


universe w u v u₁ v₁ u₂ v₂

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]
variable (F : C ⥤ Cat.{v₂, u₂})

/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
/-
**CategoryTheory.Grothendieck** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor C CategoryTheory.Cat → Type (max u u₂)
参数：max u u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck construction (often written as `∫ F` in mathematics) for a func
tor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

namespace Grothendieck

variable {F}

/-- A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (Functor.ofCatHom (F.map base)).obj X.fiber ⟶ Y.fiber`.
-/
/-
**CategoryTheory.Grothendieck.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Gr
othendieck`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor C CategoryTheory.Cat} →       CategoryTheory.Grothendieck F →
 CategoryTheory.Grothendieck F → Type (max v v₂)
参数：max v v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (Functor.ofCatHom (F.map base)).obj X.fi
ber ⟶ Y.fiber`.
-/
structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).toFunctor.obj X.fiber ⟶ Y.fiber

@[ext (iff := false)]
/-
**CategoryTheory.Grothendieck.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Grot
hendieck`。
形式化陈述：ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base) (w_f
iber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g
参数：f g : Hom X Y；w_base : f.base = g.base；w_fiber : eqToHom (by rw [w_base]) ≫ f
.fiber = g.fiber。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

/-- The identity morphism in the Grothendieck category.
-/
/-
**CategoryTheory.Grothendieck.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Groth
endieck`。
形式化陈述：id (X : Grothendieck F) : Hom X X where base
参数：X : Grothendieck F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism in the Grothendieck category.
-/
def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by simp)
/-
**CategoryTheory.Grothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grothen
dieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the Grothendieck category.
-/
/-
**CategoryTheory.Grothendieck.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Gro
thendieck`。
形式化陈述：comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where 
base
参数：f : Hom X Y；g : Hom Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms in the Grothendieck category.
-/
def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber

attribute [local simp] eqToHom_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Grothendieck.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Grothen
dieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp f g := Grothendieck.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 ((Cat.Hom.toNatIso <| eqToIso (F.map_id Y.base)) ≪≫
        (eqToIso Cat.Hom.id_toFunctor)) f.fiber]
      simp
  id_comp f := by ext <;> simp [comp, id]
  assoc f g h := by
    ext
    · simp [comp]
    · simp [comp, ← NatIso.naturality_2 (Cat.Hom.toNatIso (eqToIso (F.map_comp g.base h.base)) ≪≫
        (eqToIso (Cat.Hom.comp_toFunctor _ _))) f.fiber]

@[simp]
/-
**CategoryTheory.Grothendieck.id_base** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Grothendieck`。
形式化陈述：id_base (X : Grothendieck F) : Hom.base (𝟙 X) = 𝟙 X.base
参数：X : Grothendieck F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_base (X : Grothendieck F) :
    Hom.base (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
/-
**CategoryTheory.Grothendieck.id_fiber** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Grothendieck`。
形式化陈述：id_fiber (X : Grothendieck F) : Hom.fiber (𝟙 X) = eqToHom (by simp)
参数：X : Grothendieck F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_fiber (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by simp) :=
  rfl

@[simp]
/-
**CategoryTheory.Grothendieck.comp_base** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Grothendieck`。
形式化陈述：comp_base {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base 
= f.base ≫ g.base
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_base {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
/-
**CategoryTheory.Grothendieck.comp_fiber** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Grothendieck`。
形式化陈述：comp_fiber {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.fiber (f
 ≫ g) = eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_fiber {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) =
      eqToHom (by simp) ≫ ((F.map g.base).toFunctor).map f.fiber ≫ g.fiber :=
  rfl
/-
**CategoryTheory.Grothendieck.congr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Gr
othendieck`。
形式化陈述：congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) : f.fiber = eqToHom
 (by subst h; rfl) ≫ g.fiber
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  simp

@[simp]
/-
**CategoryTheory.Grothendieck.base_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Grothendieck`。
形式化陈述：base_eqToHom {X Y : Grothendieck F} (h : X = Y) : (eqToHom h).base = eqToH
om (congrArg Grothendieck.base h)
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem base_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Grothendieck.base h) := by subst h; rfl

@[simp]
/-
**CategoryTheory.Grothendieck.fiber_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Grothendieck`。
形式化陈述：fiber_eqToHom {X Y : Grothendieck F} (h : X = Y) : (eqToHom h).fiber = eqT
oHom (by subst h; simp)
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fiber_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; simp) := by subst h; rfl
/-
**CategoryTheory.Grothendieck.eqToHom_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Grothendieck`。
形式化陈述：eqToHom_eq {X Y : Grothendieck F} (hF : X = Y) : eqToHom hF = { base
参数：hF : X = Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_eq {X Y : Grothendieck F} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) } := by
  subst hF
  rfl

section Transport

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element of `Grothendieck F` to a `d`-based element.
-/
@[simps]
/-
**CategoryTheory.Grothendieck.transport** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Grothendieck`。
形式化陈述：transport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : Grothendieck F
参数：x : Grothendieck F；t : x.base ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transp
ort` maps each
`c`-based element of `Grothendieck F` to a `d`-based element.
-/
def transport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : Grothendieck F :=
  ⟨c, (F.map t).toFunctor.obj x.fiber⟩

/--
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transport` maps each
`c`-based element `x` of `Grothendieck F` to a `d`-based element `x.transport t`.

`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identity on fibers.
-/
@[simps]
/-
**CategoryTheory.Grothendieck.toTransport** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Grothendieck`。
形式化陈述：toTransport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : x ⟶ x.transpor
t t
参数：x : Grothendieck F；t : x.base ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Cat` is a functor and `t : c ⟶ d` is a morphism in `C`, then `transp
ort` maps each
`c`-based element `x` of `Grothendieck F` to a `d`-based element `x.transport t`
.

`toTransport` is the morphism `x ⟶ x.transport t` induced by `t` and the identit
y on fibers.
-/
def toTransport (x : Grothendieck F) {c : C} (t : x.base ⟶ c) : x ⟶ x.transport t :=
  ⟨t, 𝟙 _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Construct an isomorphism in a Grothendieck construction from isomorphisms in its base and fiber.
-/
@[simps]
/-
**CategoryTheory.Grothendieck.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Gr
othendieck`。
形式化陈述：isoMk {X Y : Grothendieck F} (e₁ : X.base ≅ Y.base) (e₂ : (F.map e₁.hom).t
oFunctor.obj X.fiber ≅ Y.fiber) : X ≅ Y where hom
参数：e₁ : X.base ≅ Y.base；e₂ : (F.map e₁.hom).toFunctor.obj X.fiber ≅ Y.fiber。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in a Grothendieck construction from isomorphisms in its
 base and fiber.
-/
def isoMk {X Y : Grothendieck F} (e₁ : X.base ≅ Y.base)
    (e₂ : (F.map e₁.hom).toFunctor.obj X.fiber ≅ Y.fiber) :
    X ≅ Y where
  hom := ⟨e₁.hom, e₂.hom⟩
  inv := ⟨e₁.inv, (F.map e₁.inv).toFunctor.map e₂.inv ≫ eqToHom (by
    rw [← Cat.Hom.comp_obj, ← F.map_comp,e₁.hom_inv_id,F.map_id,Cat.Hom.id_obj])⟩
  hom_inv_id := Grothendieck.ext _ _ (by simp) (by simp)
  inv_hom_id := Grothendieck.ext _ _ (by simp) (by
    have := Functor.congr_hom congr($((F.mapIso e₁).inv_hom_id).toFunctor) e₂.inv
    simp_all)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
If `F : C ⥤ Cat` and `x : Grothendieck F`, then every `C`-isomorphism `α : x.base ≅ c` induces
an isomorphism between `x` and its transport along `α`
-/
@[simps!]
/-
**CategoryTheory.Grothendieck.transportIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Grothendieck`。
形式化陈述：transportIso (x : Grothendieck F) {c : C} (α : x.base ≅ c) : x.transport α
.hom ≅ x
参数：x : Grothendieck F；α : x.base ≅ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ Cat` and `x : Grothendieck F`, then every `C`-isomorphism `α : x.bas
e ≅ c` induces
an isomorphism between `x` and its transport along `α`
-/
def transportIso (x : Grothendieck F) {c : C} (α : x.base ≅ c) :
    x.transport α.hom ≅ x := (isoMk α (Iso.refl _)).symm

end Transport
section

variable (F)

/-- The forgetful functor from `Grothendieck F` to the source category. -/
@[simps!]
/-
**CategoryTheory.Grothendieck.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
rothendieck`。
形式化陈述：forget : Grothendieck F ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Grothendieck F` to the source category.
-/
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map f := f.1

end

section

variable {G : C ⥤ Cat}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The Grothendieck construction is functorial: a natural transformation `α : F ⟶ G` induces
a functor `Grothendieck.map : Grothendieck F ⥤ Grothendieck G`.
-/
@[simps!]
/-
**CategoryTheory.Grothendieck.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grot
hendieck`。
形式化陈述：map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where obj X
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck construction is functorial: a natural transformation `α : F ⟶ G
` induces
a functor `Grothendieck.map : Grothendieck F ⥤ Grothendieck G`.
-/
def map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where
  obj X :=
  { base := X.base
    fiber := (α.app X.base).toFunctor.obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber }
  -- map_id X := by simp only [id_base, id_fiber, eqToHom_map, eqToHom_trans]; rfl
  map_comp {X Y Z} f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_fiber, map_comp, ← Cat.Hom.comp_map,
      Functor.congr_hom congr($(α.naturality g.base).toFunctor) f.fiber]
    simp


set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Grothendieck.map_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Grothendieck`。
形式化陈述：map_obj {α : F ⟶ G} (X : Grothendieck F) : (Grothendieck.map α).obj X = ⟨X
.base, (α.app X.base).toFunctor.obj X.fiber⟩
参数：X : Grothendieck F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_obj {α : F ⟶ G} (X : Grothendieck F) :
    (Grothendieck.map α).obj X = ⟨X.base, (α.app X.base).toFunctor.obj X.fiber⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Grothendieck.map_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Grothendieck`。
形式化陈述：map_map {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y} : (Grothendieck.map
 α).map f = ⟨f.base, (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber
 ≫ (α.app Y.base).toFunctor.map f.fiber⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Grothendieck.ext`：ext {X Y : Grothendieck F} (f g : Hom X
 Y) (w_base : f.base = g.base) (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g
.fiber) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Grothendieck.map_map_base`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {F G : CategoryTheory.Functor C CategoryTheory.Cat} (
α : F ⟶ G)   {X Y : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Grothendieck.map_map_fiber`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {F G : CategoryTheory.Functor C CategoryTheory.Cat} 
(α : F ⟶ G)   {X Y : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans`：∀ {C D : CategoryTheory.Cat}
 {F G : C ⟶ D} (h : F = G), (CategoryTheory.eqToHom h).toNatTrans = CategoryTheo
ry.eqToHom ⋯
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
-/
theorem map_map {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y} :
    (Grothendieck.map α).map f =
    ⟨f.base, (eqToHom (α.naturality f.base).symm).toNatTrans.app X.fiber ≫
      (α.app Y.base).toFunctor.map f.fiber⟩ := by
    apply Grothendieck.ext _ _ (by simp) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `Grothendieck.map α : Grothendieck F ⥤ Grothendieck G` lies over `C`. -/
/-
**CategoryTheory.Grothendieck.functor_comp_forget** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Grothendieck`。
形式化陈述：functor_comp_forget {α : F ⟶ G} : Grothendieck.map α ⋙ Grothendieck.forget
 G = Grothendieck.forget F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Grothendieck.map α : Grothendieck F ⥤ Grothendieck G` lies over `C`
.
-/
theorem functor_comp_forget {α : F ⟶ G} :
    Grothendieck.map α ⋙ Grothendieck.forget G = Grothendieck.forget F := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Grothendieck.map_id_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Grothendieck`。
形式化陈述：map_id_eq : map (𝟙 F) = Functor.id (Grothendieck <| F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Grothendieck.map_map`：map_map {α : F ⟶ G} {X Y : Grothend
ieck F} {f : X ⟶ Y} : (Grothendieck.map α).map f = ⟨f.base, (eqToHom (α.naturali
ty f.base).symm).toNatTra…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem map_id_eq : map (𝟙 F) = Functor.id (Grothendieck <| F) := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `mapIdIso` to `map_id_eq` whenever we can. -/
/-
**CategoryTheory.Grothendieck.mapIdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Grothendieck`。
形式化陈述：mapIdIso : (map (𝟙 F)).toCatHom ≅ 𝟙 (Cat.of <| Grothendieck <| F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Making the equality of functors into an isomorphism. Note: we should avoid equal
ity of functors
if possible, and we should prefer `mapIdIso` to `map_id_eq` whenever we can.
-/
def mapIdIso : (map (𝟙 F)).toCatHom ≅ 𝟙 (Cat.of <| Grothendieck <| F) :=
  eqToIso congr(($map_id_eq).toCatHom)

variable {H : C ⥤ Cat}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Grothendieck.map_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Grothendieck`。
形式化陈述：map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Grothendieck.map_map`：map_map {α : F ⟶ G} {X Y : Grothend
ieck F} {f : X ⟶ Y} : (Grothendieck.map α).map f = ⟨f.base, (eqToHom (α.naturali
ty f.base).symm).toNatTra…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Cat.Hom₂.eqToHom_toNatTrans`：∀ {C D : CategoryTheory.Cat}
 {F G : C ⟶ D} (h : F = G), (CategoryTheory.eqToHom h).toNatTrans = CategoryTheo
ry.eqToHom ⋯
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_eq (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, map_obj_fiber, NatTrans.comp_app, Cat.Hom.comp_toFunctor,
      comp_obj, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Functor.comp_map, eqToHom_refl, map_comp,
      eqToHom_map, eqToHom_trans_assoc, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- Making the equality of functors into an isomorphism. Note: we should avoid equality of functors
if possible, and we should prefer `map_comp_iso` to `map_comp_eq` whenever we can. -/
/-
**CategoryTheory.Grothendieck.mapCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Grothendieck`。
形式化陈述：mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β
参数：α : F ⟶ G；β : G ⟶ H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Grothendieck.map_comp_eq`：map_comp_eq (α : F ⟶ G) (β : G 
⟶ H) : map (α ≫ β) = map α ⋙ map β

--- 原说明 ---
Making the equality of functors into an isomorphism. Note: we should avoid equal
ity of functors
if possible, and we should prefer `map_comp_iso` to `map_comp_eq` whenever we ca
n.
-/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
/-
**CategoryTheory.Grothendieck.compAsSmallFunctorEquivalenceInverse** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：compAsSmallFunctorEquivalenceInverse : Grothendieck F ⥤ Grothendieck (F ⋙ 
Cat.asSmallFunctor.{w}) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor to build the equivalence `compAsSmallFunctorEquivalence`.
-/
def compAsSmallFunctorEquivalenceInverse :
    Grothendieck F ⥤ Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) where
  obj X := ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor to build the equivalence `compAsSmallFunctorEquivalence`. -/
@[simps]
/-
**CategoryTheory.Grothendieck.compAsSmallFunctorEquivalenceFunctor** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：compAsSmallFunctorEquivalenceFunctor : Grothendieck (F ⋙ Cat.asSmallFuncto
r.{w}) ⥤ Grothendieck F where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to build the equivalence `compAsSmallFunctorEquivalence`.
-/
def compAsSmallFunctorEquivalenceFunctor :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ⥤ Grothendieck F where
  obj X := ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id _ := by apply Grothendieck.ext <;> simp
  map_comp _ _ := by apply Grothendieck.ext <;> simp [down_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Taking the Grothendieck construction on `F ⋙ asSmallFunctor`, where
`asSmallFunctor : Cat ⥤ Cat` is the functor which turns each category into a small category of a
(potentially) larger universe, is equivalent to the Grothendieck construction on `F` itself. -/
@[simps]
/-
**CategoryTheory.Grothendieck.compAsSmallFunctorEquivalence** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：compAsSmallFunctorEquivalence : Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) 
≌ Grothendieck F where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the Grothendieck construction on `F ⋙ asSmallFunctor`, where
`asSmallFunctor : Cat ⥤ Cat` is the functor which turns each category into a sma
ll category of a
(potentially) larger universe, is equivalent to the Grothendieck construction on
 `F` itself.
-/
def compAsSmallFunctorEquivalence :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ≌ Grothendieck F where
  functor := compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := Iso.refl _
  unitIso := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F} in
/-- Mapping a Grothendieck construction along the whiskering of any natural transformation
`α : F ⟶ G` with the functor `asSmallFunctor : Cat ⥤ Cat` is naturally isomorphic to conjugating
`map α` with the equivalence between `Grothendieck (F ⋙ asSmallFunctor)` and `Grothendieck F`. -/
/-
**CategoryTheory.Grothendieck.mapWhiskerRightAsSmallFunctor** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：mapWhiskerRightAsSmallFunctor (α : F ⟶ G) : map (whiskerRight α Cat.asSmal
lFunctor.{w}) ≅ (compAsSmallFunctorEquivalence F).functor ⋙ map α ⋙ (compAsSmall
FunctorEquivalence G).inverse
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping a Grothendieck construction along the whiskering of any natural transfor
mation
`α : F ⟶ G` with the functor `asSmallFunctor : Cat ⥤ Cat` is naturally isomorphi
c to conjugating
`map α` with the equivalence between `Grothendieck (F ⋙ asSmallFunctor)` and `Gr
othendieck F`.
-/
def mapWhiskerRightAsSmallFunctor (α : F ⟶ G) :
    map (whiskerRight α Cat.asSmallFunctor.{w}) ≅
    (compAsSmallFunctorEquivalence F).functor ⋙ map α ⋙
      (compAsSmallFunctorEquivalence G).inverse :=
  NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun f => by
      fapply Grothendieck.ext
      · simp [compAsSmallFunctorEquivalenceInverse]
      · simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse,
        comp_obj, compAsSmallFunctorEquivalenceInverse_obj_base, map_obj_base,
        compAsSmallFunctorEquivalenceFunctor_obj_base, Cat.asSmallFunctor_obj, Cat.of_α,
        Iso.refl_hom, Functor.comp_map, comp_base, id_base,
        compAsSmallFunctorEquivalenceInverse_map_base, map_map_base,
        compAsSmallFunctorEquivalenceFunctor_map_base, Cat.asSmallFunctor_map, toCatHom_toFunctor,
        map_obj_fiber, whiskerRight_app, AsSmall.down_obj, AsSmall.up_obj_down,
        compAsSmallFunctorEquivalenceInverse_obj_fiber,
        compAsSmallFunctorEquivalenceFunctor_obj_fiber, comp_fiber, map_map_fiber, AsSmall.down_map,
        down_comp, eqToHom_down, AsSmall.up_map_down, map_comp, eqToHom_map, id_fiber,
        Category.assoc, eqToHom_trans_assoc, compAsSmallFunctorEquivalenceInverse_map_fiber,
        compAsSmallFunctorEquivalenceFunctor_map_fiber, eqToHom_comp_iff, comp_eqToHom_iff]
        simp only [conj_eqToHom_iff_heq']
        rw [G.map_id]
        simp)

end

set_option backward.isDefEq.respectTransparency.types false in
/-- The Grothendieck construction as a functor from the functor category `E ⥤ Cat` to the
over category `Over E`. -/
/-
**CategoryTheory.Grothendieck.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Grothendieck`。
形式化陈述：functor {E : Cat.{v, u}} : (E ⥤ Cat.{v, u}) ⥤ Over (T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck construction as a functor from the functor category `E ⥤ Cat` t
o the
over category `Over E`.
-/
def functor {E : Cat.{v, u}} : (E ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E where
  obj F := Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F).toCatHom
  map {_ _} α := Over.homMk (X := E) (Grothendieck.map α).toCatHom
    congr($(Grothendieck.functor_comp_forget).toCatHom)
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp [Grothendieck.map_comp_eq α β]
    rfl

variable (G : C ⥤ Type w)

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
/-
**CategoryTheory.Grothendieck.grothendieckTypeToCatFunctor** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements w
here obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration.
-/
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩

/-- Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration. -/
@[simps!]
/-
**CategoryTheory.Grothendieck.grothendieckTypeToCatInverse** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Grothendieck`。
形式化陈述：grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) w
here obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `grothendieckTypeToCat`, to speed up elaboration.
-/
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
@[simps!]
/-
**CategoryTheory.Grothendieck.grothendieckTypeToCat** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Grothendieck`。
形式化陈述：grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where fu
nctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    simp
    rfl

section Pre

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction induces a functor
`Grothendieck (G ⋙ F) ⥤ Grothendieck F`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Grothendieck.pre** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grot
hendieck`。
形式化陈述：pre (G : D ⥤ C) : Grothendieck (G ⋙ F) ⥤ Grothendieck F where obj X
参数：G : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction indu
ces a functor
`Grothendieck (G ⋙ F) ⥤ Grothendieck F`.
-/
def pre (G : D ⥤ C) : Grothendieck (G ⋙ F) ⥤ Grothendieck F where
  obj X := ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

@[simp]
/-
**CategoryTheory.Grothendieck.pre_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.G
rothendieck`。
形式化陈述：pre_id : pre F (𝟭 C) = 𝟭 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pre_id : pre F (𝟭 C) = 𝟭 _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
A natural isomorphism between functors `G ≅ H` induces a natural isomorphism between the canonical
morphism `pre F G` and `pre F H`, up to composition with
`Grothendieck (G ⋙ F) ⥤ Grothendieck (H ⋙ F)`.
-/
/-
**CategoryTheory.Grothendieck.preNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Grothendieck`。
形式化陈述：preNatIso {G H : D ⥤ C} (α : G ≅ H) : pre F G ≅ map (whiskerRight α.hom F)
 ⋙ (pre F H)
参数：α : G ≅ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between functors `G ≅ H` induces a natural isomorphism bet
ween the canonical
morphism `pre F G` and `pre F H`, up to composition with
`Grothendieck (G ⋙ F) ⥤ Grothendieck (H ⋙ F)`.
-/
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F G ≅ map (whiskerRight α.hom F) ⋙ (pre F H) :=
  NatIso.ofComponents
    (fun X => (transportIso ⟨G.obj X.base, X.fiber⟩ (α.app X.base)).symm)
    (fun f => by fapply Grothendieck.ext <;> simp)

set_option backward.isDefEq.respectTransparency.types false in
/--
Given an equivalence of categories `G`, `preInv _ G` is the (weak) inverse of the `pre _ G.functor`.
-/
/-
**CategoryTheory.Grothendieck.preInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
rothendieck`。
形式化陈述：preInv (G : D ≌ C) : Grothendieck F ⥤ Grothendieck (G.functor ⋙ F)
参数：G : D ≌ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an equivalence of categories `G`, `preInv _ G` is the (weak) inverse of th
e `pre _ G.functor`.
-/
def preInv (G : D ≌ C) : Grothendieck F ⥤ Grothendieck (G.functor ⋙ F) :=
  map (whiskerRight G.counitInv F) ⋙ Grothendieck.pre (G.functor ⋙ F) G.inverse

set_option backward.isDefEq.respectTransparency.types false in
variable {F} in
/-
**CategoryTheory.Grothendieck.pre_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Grothendieck`。
形式化陈述：pre_comp_map (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) : pre F G ⋙ map α = map
 (whiskerLeft G α) ⋙ pre H G
参数：G : D ⥤ C；α : F ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pre_comp_map (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) :
    pre F G ⋙ map α = map (whiskerLeft G α) ⋙ pre H G := rfl

set_option backward.isDefEq.respectTransparency.types false in
variable {F} in
/-
**CategoryTheory.Grothendieck.pre_comp_map_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Grothendieck`。
形式化陈述：pre_comp_map_assoc (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : Type*} [Cate
gory* E] (K : Grothendieck H ⥤ E) : pre F G ⋙ map α ⋙ K = map (whiskerLeft G α) 
⋙ pre H G ⋙ K
参数：G : D ⥤ C；α : F ⟶ H；K : Grothendieck H ⥤ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pre_comp_map_assoc (G : D ⥤ C) {H : C ⥤ Cat} (α : F ⟶ H) {E : Type*} [Category* E]
    (K : Grothendieck H ⥤ E) : pre F G ⋙ map α ⋙ K = map (whiskerLeft G α) ⋙ pre H G ⋙ K := rfl

variable {E : Type*} [Category* E] in
@[simp]
/-
**CategoryTheory.Grothendieck.pre_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Grothendieck`。
形式化陈述：pre_comp (G : D ⥤ C) (H : E ⥤ D) : pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G
参数：G : D ⥤ C；H : E ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pre_comp (G : D ⥤ C) (H : E ⥤ D) : pre F (H ⋙ G) = pre (G ⋙ F) H ⋙ pre F G := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Let `G` be an equivalence of categories. The functor induced via `pre` by `G.functor ⋙ G.inverse`
is naturally isomorphic to the functor induced via `map` by a whiskered version of `G`'s inverse
unit.
-/
/-
**CategoryTheory.Grothendieck.preUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Grothendieck`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u₁} →       [inst_1 : CategoryTheory.Category.{v₁, u₁} D] →         (F : Catego
ryTheory.Functor C CategoryTheory.Cat) →           (G : D ≌ C) →             Cat
egoryTheory.Grothendieck.map (CategoryTheory.Functor.whiskerRight G.unitInv (G.f
unctor.comp F)) ≅               CategoryTheory.Grothendieck.pre (G.functor.comp 
F) (G.functor.comp G.inverse)
参数：F : CategoryTheory.Functor C CategoryTheory.Cat；G : D ≌ C；CategoryTheory.Func
tor.whiskerRight G.unitInv (G.functor.comp F)；G.functor.comp F；G.functor.comp G.
inverse。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `G` be an equivalence of categories. The functor induced via `pre` by `G.fun
ctor ⋙ G.inverse`
is naturally isomorphic to the functor induced via `map` by a whiskered version 
of `G`'s inverse
unit.
-/
protected def preUnitIso (G : D ≌ C) :
    map (whiskerRight G.unitInv _) ≅ pre (G.functor ⋙ F) (G.functor ⋙ G.inverse) :=
  preNatIso _ G.unitIso.symm |>.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Given a functor `F : C ⥤ Cat` and an equivalence of categories `G : D ≌ C`, the functor
`pre F G.functor` is an equivalence between `Grothendieck (G.functor ⋙ F)` and `Grothendieck F`.
-/
/-
**CategoryTheory.Grothendieck.preEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Grothendieck`。
形式化陈述：preEquivalence (G : D ≌ C) : Grothendieck (G.functor ⋙ F) ≌ Grothendieck F
 where functor
参数：G : D ≌ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ Cat` and an equivalence of categories `G : D ≌ C`, the 
functor
`pre F G.functor` is an equivalence between `Grothendieck (G.functor ⋙ F)` and `
Grothendieck F`.
-/
def preEquivalence (G : D ≌ C) : Grothendieck (G.functor ⋙ F) ≌ Grothendieck F where
  functor := pre F G.functor
  inverse := preInv F G
  unitIso := by
    refine (eqToIso ?_)
      ≪≫ (Grothendieck.preUnitIso F G |> isoWhiskerLeft (map _))
      ≪≫ (pre_comp_map_assoc G.functor _ _ |> Eq.symm |> eqToIso)
    calc
      _ = map (𝟙 _) := map_id_eq.symm
      _ = map _ := ?_
      _ = map _ ⋙ map _ := map_comp_eq _ _
    congr; ext X
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, Functor.id_obj,
      Functor.map_id, NatTrans.comp_app, NatTrans.id_app, whiskerLeft_app, whiskerRight_app,
      Equivalence.counitInv_functor_comp]
  counitIso := preNatIso F G.counitIso.symm |>.symm
  functor_unitIso_comp := by
    intro X
    simp only [preInv, Grothendieck.preUnitIso, pre_id,
      Iso.trans_hom, eqToIso.hom, eqToHom_app, eqToHom_refl, isoWhiskerLeft_hom, NatTrans.comp_app]
    fapply Grothendieck.ext <;> simp [preNatIso, transportIso]

set_option backward.isDefEq.respectTransparency.types false in
variable {F} in
/--
Let `F, F' : C ⥤ Cat` be functor, `G : D ≌ C` an equivalence and `α : F ⟶ F'` a natural
transformation.

Left-whiskering `α` by `G` and then taking the Grothendieck construction is, up to isomorphism,
the same as taking the Grothendieck construction of `α` and using the equivalences `pre F G`
and `pre F' G` to match the expected type:

```
Grothendieck (G.functor ⋙ F) ≌ Grothendieck F ⥤ Grothendieck F' ≌ Grothendieck (G.functor ⋙ F')
```
-/
/-
**CategoryTheory.Grothendieck.mapWhiskerLeftIsoConjPreMap** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Grothendieck`。
形式化陈述：mapWhiskerLeftIsoConjPreMap {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F') : map 
(whiskerLeft G.functor α) ≅ (preEquivalence F G).functor ⋙ map α ⋙ (preEquivalen
ce F' G).inverse
参数：G : D ≌ C；α : F ⟶ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F, F' : C ⥤ Cat` be functor, `G : D ≌ C` an equivalence and `α : F ⟶ F'` a 
natural
transformation.

Left-whiskering `α` by `G` and then taking the Grothendieck construction is, up 
to isomorphism,
the same as taking the Grothendieck construction of `α` and using the equivalenc
es `pre F G`
and `pre F' G` to match the expected type:

```
Grothendieck (G.functor ⋙ F) ≌ Grothendieck F ⥤ Grothendieck F' ≌ Grothendieck (
G.functor ⋙ F')
```
-/
def mapWhiskerLeftIsoConjPreMap {F' : C ⥤ Cat} (G : D ≌ C) (α : F ⟶ F') :
    map (whiskerLeft G.functor α) ≅
      (preEquivalence F G).functor ⋙ map α ⋙ (preEquivalence F' G).inverse :=
  (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ (preEquivalence F' G).unitIso

end Pre

section FunctorFrom

variable {E : Type*} [Category* E]

set_option backward.isDefEq.respectTransparency.types false in
variable (F) in
/-- The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its Grothendieck
construction. -/
@[simps obj map]
/-
**CategoryTheory.Grothendieck.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grothen
dieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a fiber `F.obj c` of a functor `F : C ⥤ Cat` into its Grothendi
eck
construction.
-/
def ι (c : C) : F.obj c ⥤ Grothendieck F where
  obj d := ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
    simp only [eqToHom_comp_iff, Category.assoc, eqToHom_trans_assoc]
    apply Functor.congr_hom congr($(F.map_id _).toFunctor).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Grothendieck.faithful_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Grothendieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance faithful_ι (c : C) : (ι F c).Faithful where
  map_injective f := by
    injection f with _ f
    rwa [cancel_epi] at f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every morphism `f : X ⟶ Y` in the base category induces a natural transformation from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`. -/
@[simps]
/-
**CategoryTheory.Grothendieck.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grothen
dieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every morphism `f : X ⟶ Y` in the base category induces a natural transformation
 from the fiber
inclusion `ι F X` to the composition `F.map f ⋙ ι F Y`.
-/
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ (F.map f).toFunctor ⋙ ι F Y where
  app d := ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'),
  fib c ⟶ (F.map f).toFunctor ⋙ fib c')
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))
variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f).toFunctor (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct a functor from `Grothendieck F` to another category `E` by providing a family of
functors on the fibers of `Grothendieck F`, a family of natural transformations on morphisms in the
base of `Grothendieck F` and coherence data for this family of natural transformations. -/
@[simps]
/-
**CategoryTheory.Grothendieck.functorFrom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Grothendieck`。
形式化陈述：functorFrom : Grothendieck F ⥤ E where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a functor from `Grothendieck F` to another category `E` by providing a
 family of
functors on the fibers of `Grothendieck F`, a family of natural transformations 
on morphisms in the
base of `Grothendieck F` and coherence data for this family of natural transform
ations.
-/
def functorFrom : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

set_option backward.defeqAttrib.useBackward true in
/-- `Grothendieck.ι F c` composed with `Grothendieck.functorFrom` is isomorphic a functor on a fiber
on `F` supplied as the first argument to `Grothendieck.functorFrom`. -/
/-
**CategoryTheory.Grothendieck.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grothen
dieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Grothendieck.ι F c` composed with `Grothendieck.functorFrom` is isomorphic a fu
nctor on a fiber
on `F` supplied as the first argument to `Grothendieck.functorFrom`.
-/
def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

end FunctorFrom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The fiber inclusion `ι F c` composed with `map α` is isomorphic to `α.app c ⋙ ι F' c`. -/
@[simps!]
/-
**CategoryTheory.Grothendieck.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grothen
dieck`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber inclusion `ι F c` composed with `map α` is isomorphic to `α.app c ⋙ ι 
F' c`.
-/
def ιCompMap {F' : C ⥤ Cat} (α : F ⟶ F') (c : C) : ι F c ⋙ map α ≅ (α.app c).toFunctor ⋙ ι F' c :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun f => by simp [map])

end Grothendieck

end CategoryTheory

