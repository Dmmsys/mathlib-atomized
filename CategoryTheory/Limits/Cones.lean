/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Cones and cocones

We define `Cone F`, a cone over a functor `F`,
and `F.cones : Cᵒᵖ ⥤ Type`, the functor associating to `X` the cones over `F` with cone point `X`.

A cone `c` is defined by specifying its cone point `c.pt` and a natural transformation `c.π`
from the constant `c.pt`-valued functor to `F`.

We provide `c.w f : c.π.app j ≫ F.map f = c.π.app j'` for any `f : j ⟶ j'`
as a wrapper for `c.π.naturality f` avoiding unneeded identity morphisms.

We define `c.extend f`, where `c : cone F` and `f : Y ⟶ c.pt` for some other `Y`,
which replaces the cone point by `Y` and inserts `f` into each of the components of the cone.
Similarly we have `c.whisker F` producing a `Cone (E ⋙ F)`

We define morphisms of cones, and the category of cones.

We define `Cone.postcompose α : cone F ⥤ cone G` for `α` a natural transformation `F ⟶ G`.

And, of course, we dualise all this to cocones as well.

For more results about the category of cones, see `cone_category.lean`.
-/

@[expose] public section

-- morphism levels before object levels. See note [category theory universes].
universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

open CategoryTheory

variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory

namespace Functor

variable (F : J ⥤ C)

/-- If `F : J ⥤ C` then `F.cones` is the functor assigning to an object `X : C` the
type of natural transformations from the constant functor with value `X` to `F`.
An object representing this functor is a limit of `F`.
-/
@[implicit_reducible, simps! obj map]
/-
**CategoryTheory.Functor.cones** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：cones : Cᵒᵖ ⥤ Type (max u₁ v₃)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ C` then `F.cones` is the functor assigning to an object `X : C` the
type of natural transformations from the constant functor with value `X` to `F`.
An object representing this functor is a limit of `F`.
-/
def cones : Cᵒᵖ ⥤ Type (max u₁ v₃) :=
  (const J).op ⋙ yoneda.obj F

/-- If `F : J ⥤ C` then `F.cocones` is the functor assigning to an object `(X : C)`
the type of natural transformations from `F` to the constant functor with value `X`.
An object corepresenting this functor is a colimit of `F`.
-/
@[implicit_reducible, simps! obj map]
/-
**CategoryTheory.Functor.cocones** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：cocones : C ⥤ Type (max u₁ v₃)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ C` then `F.cocones` is the functor assigning to an object `(X : C)`
the type of natural transformations from `F` to the constant functor with value 
`X`.
An object corepresenting this functor is a colimit of `F`.
-/
def cocones : C ⥤ Type (max u₁ v₃) :=
  const J ⋙ coyoneda.obj (op F)

end Functor

section

variable (J C)

/-- Functorially associated to each functor `J ⥤ C`, we have the `C`-presheaf consisting of
cones with a given cone point.
-/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.cones** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：cones : (J ⥤ C) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₃) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorially associated to each functor `J ⥤ C`, we have the `C`-presheaf consis
ting of
cones with a given cone point.
-/
def cones : (J ⥤ C) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₃) where
  obj := Functor.cones
  map f := whiskerLeft (const J).op (yoneda.map f)

/-- Contravariantly associated to each functor `J ⥤ C`, we have the `C`-copresheaf consisting of
cocones with a given cocone point.
-/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.cocones** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：cocones : (J ⥤ C)ᵒᵖ ⥤ C ⥤ Type (max u₁ v₃) where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Contravariantly associated to each functor `J ⥤ C`, we have the `C`-copresheaf c
onsisting of
cocones with a given cocone point.
-/
def cocones : (J ⥤ C)ᵒᵖ ⥤ C ⥤ Type (max u₁ v₃) where
  obj F := Functor.cocones (unop F)
  map f := whiskerLeft (const J) (coyoneda.map f)

end

namespace Limits

section

/-- A `c : Cone F` is:
* an object `c.pt` and
* a natural transformation `c.π : c.pt ⟶ F` from the constant `c.pt` functor to `F`.

Example: if `J` is a category coming from a poset then the data required to make
a term of type `Cone F` is morphisms `πⱼ : c.pt ⟶ F j` for all `j : J` and,
for all `i ≤ j` in `J`, morphisms `πᵢⱼ : F i ⟶ F j` such that `πᵢ ≫ πᵢⱼ = πⱼ`.

`Cone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cones.obj X`.
-/
/-
**CategoryTheory.Limits.Cone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] → CategoryTheory.F
unctor J C → Type (max (max u₁ u₃) v₃)
参数：max (max u₁ u₃) v₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `c : Cone F` is:
* an object `c.pt` and
* a natural transformation `c.π : c.pt ⟶ F` from the constant `c.pt` functor to 
`F`.

Example: if `J` is a category coming from a poset then the data required to make
a term of type `Cone F` is morphisms `πⱼ : c.pt ⟶ F j` for all `j : J` and,
for all `i ≤ j` in `J`, morphisms `πᵢⱼ : F i ⟶ F j` such that `πᵢ ≫ πᵢⱼ = πⱼ`.

`Cone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cones.obj X`.
-/
structure Cone (F : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from the constant functor at `X` to `F` -/
  π : (const J).obj pt ⟶ F

/-- A `c : Cocone F` is
* an object `c.pt` and
* a natural transformation `c.ι : F ⟶ c.pt` from `F` to the constant `c.pt` functor.

For example, if the source `J` of `F` is a partially ordered set, then to give
`c : Cocone F` is to give a collection of morphisms `ιⱼ : F j ⟶ c.pt` and, for
all `j ≤ k` in `J`, morphisms `ιⱼₖ : F j ⟶ F k` such that `Fⱼₖ ≫ Fₖ = Fⱼ` for all `j ≤ k`.

`Cocone F` is equivalent, via `Cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
@[to_dual existing]
/-
**CategoryTheory.Limits.Cocone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] → CategoryTheory.F
unctor J C → Type (max (max u₁ u₃) v₃)
参数：max (max u₁ u₃) v₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `c : Cocone F` is
* an object `c.pt` and
* a natural transformation `c.ι : F ⟶ c.pt` from `F` to the constant `c.pt` func
tor.

For example, if the source `J` of `F` is a partially ordered set, then to give
`c : Cocone F` is to give a collection of morphisms `ιⱼ : F j ⟶ c.pt` and, for
all `j ≤ k` in `J`, morphisms `ιⱼₖ : F j ⟶ F k` such that `Fⱼₖ ≫ Fₖ = Fⱼ` for al
l `j ≤ k`.

`Cocone F` is equivalent, via `Cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
structure Cocone (F : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from `F` to the constant functor at `pt` -/
  ι : F ⟶ (const J).obj pt

@[to_dual]
/-
**CategoryTheory.Limits.inhabitedCone** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：inhabitedCone (F : Discrete PUnit ⥤ C) : Inhabited (Cone F)
参数：F : Discrete PUnit ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedCone (F : Discrete PUnit ⥤ C) : Inhabited (Cone F) :=
  ⟨{  pt := F.obj ⟨⟨⟩⟩
      π := { app := fun ⟨⟨⟩⟩ => 𝟙 _
             naturality := by
              intro X Y f
              match X, Y, f with
              | .mk A, .mk B, .up g =>
                simp
           }
  }⟩

@[to_dual (attr := reassoc), elementwise]
/-
**CategoryTheory.Limits.Cone.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits.
Cone`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 (c : CategoryTheory.Limits.Cone F) {j j' : J} (f : j ⟶ j'),   CategoryTheory.Ca
tegoryStruct.comp (c.π.app j) (F.map f) = c.π.app j'
参数：c : CategoryTheory.Limits.Cone F；f : j ⟶ j'；c.π.app j；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem Cone.w {F : J ⥤ C} (c : Cone F) {j j' : J} (f : j ⟶ j') :
    dsimp% c.π.app j ≫ F.map f = c.π.app j' := by
  simpa using (c.π.naturality f).symm

attribute [simp] Cone.w Cone.w_assoc -- `Cocone.w` and `Cocone.w_assoc` are redundant

#adaptation_note
/--
This lemma can be derived by `simp`, so `[elementwise]` does errors out.
For symmetry reasons, it seems good to have the dual of `Cone.w_apply`, though,
so we provide it by hand now.
-/
/-
**CategoryTheory.Limits.Cocone.w_apply.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma can be derived by `simp`, so `[elementwise]` does errors out.
For symmetry reasons, it seems good to have the dual of `Cone.w_apply`, though,
so we provide it by hand now.
-/
theorem Cocone.w_apply.{uF, w} {F : J ⥤ C} (c : Cocone F) {j j' : J} (f : j' ⟶ j)
    {F' : C → C → Type uF} {carrier : C → Type w}
    {instFunLike : (X Y : C) → FunLike (F' X Y) (carrier X) (carrier Y)}
    [inst : ConcreteCategory C F'] (x : carrier (F.obj j')) :
    (ConcreteCategory.hom (c.ι.app j)) ((ConcreteCategory.hom (F.map f)) x) =
      (ConcreteCategory.hom (c.ι.app j')) x := by
  simp

end

variable {F : J ⥤ C}

namespace Cone

/-- The isomorphism between a cone on `F` and an element of the functor `F.cones`. -/
@[simps!]
/-
**CategoryTheory.Limits.Cone.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Cone`。
形式化陈述：equiv (F : J ⥤ C) : dsimp% Cone F ≅ Σ X, F.cones.obj X where hom
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between a cone on `F` and an element of the functor `F.cones`.
-/
def equiv (F : J ⥤ C) : dsimp% Cone F ≅ Σ X, F.cones.obj X where
  hom := ↾fun c ↦ ⟨op c.pt, c.π⟩
  inv := ↾fun c ↦
    { pt := c.1.unop
      π := c.2 }
  hom_inv_id := by
    ext X
    cases X
    rfl
  inv_hom_id := by
    ext X
    cases X
    all_goals rfl

/-- A map to the vertex of a cone naturally induces a cone by composition. -/
@[simps]
/-
**CategoryTheory.Limits.Cone.extensions** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Cone`。
形式化陈述：extensions (c : Cone F) : uliftYoneda.obj c.pt ⟶ F.cones where app _
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map to the vertex of a cone naturally induces a cone by composition.
-/
def extensions (c : Cone F) : uliftYoneda.obj c.pt ⟶ F.cones where
  app _ := ↾fun f ↦ (const J).map f.down ≫ c.π

/-- A map to the vertex of a cone induces a cone by composition. -/
@[to_dual (attr := implicit_reducible, simps)
/-- A map from the vertex of a cocone induces a cocone by composition. -/]
/-
**CategoryTheory.Limits.Cone.extend** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Cone`。
形式化陈述：extend (c : Cone F) {X : C} (f : X ⟶ c.pt) : Cone F where pt
参数：c : Cone F；f : X ⟶ c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def extend (c : Cone F) {X : C} (f : X ⟶ c.pt) : Cone F where
  pt := X
  π := (const J).map f ≫ c.π

/-- Whisker a cone by precomposition of a functor. -/
@[to_dual (attr := implicit_reducible, simps)
/-- Whisker a cocone by precomposition of a functor. See `whiskering` for a functorial
version.
-/]
/-
**CategoryTheory.Limits.Cone.whisker** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Cone`。
形式化陈述：whisker (E : K ⥤ J) (c : Cone F) : Cone (E ⋙ F) where pt
参数：E : K ⥤ J；c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def whisker (E : K ⥤ J) (c : Cone F) : Cone (E ⋙ F) where
  pt := c.pt
  π := whiskerLeft E c.π

end Cone

namespace Cocone

/-- The isomorphism between a cocone on `F` and an element of the functor `F.cocones`. -/
/-
**CategoryTheory.Limits.Cocone.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Cocone`。
形式化陈述：equiv (F : J ⥤ C) : Cocone F ≅ Σ X, F.cocones.obj X where hom
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between a cocone on `F` and an element of the functor `F.cocones
`.
-/
def equiv (F : J ⥤ C) : Cocone F ≅ Σ X, F.cocones.obj X where
  hom := ↾fun c ↦ ⟨c.pt, c.ι⟩
  inv := ↾fun c ↦
    { pt := c.1
      ι := c.2 }
  hom_inv_id := by
    ext X
    cases X
    rfl
  inv_hom_id := by
    ext X
    cases X
    all_goals rfl

/-- A map from the vertex of a cocone naturally induces a cocone by composition. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.extensions** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.Cocone`。
形式化陈述：extensions (c : Cocone F) : coyoneda.obj (op c.pt) ⋙ uliftFunctor.{u₁} ⟶ F
.cocones where app _
参数：c : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map from the vertex of a cocone naturally induces a cocone by composition.
-/
def extensions (c : Cocone F) : coyoneda.obj (op c.pt) ⋙ uliftFunctor.{u₁} ⟶ F.cocones where
  app _ := ↾fun f ↦ c.ι ≫ (const J).map f.down

end Cocone

/-- A cone morphism between two cones for the same diagram is a morphism of the cone points which
commutes with the cone legs. -/
/-
**CategoryTheory.Limits.ConeMorphism** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：ConeMorphism (A B : Cone F) where /-- A morphism between the two vertex ob
jects of the cones -/ hom : A.pt ⟶ B.pt /-- The triangle consisting of the two n
atural transformations and `hom` commutes -/ w (j : J) : hom ≫ B.π.app j = A.π.a
pp j
参数：A B : Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cone morphism between two cones for the same diagram is a morphism of the cone
 points which
commutes with the cone legs.
-/
structure ConeMorphism (A B : Cone F) where
  /-- A morphism between the two vertex objects of the cones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  w (j : J) : hom ≫ B.π.app j = A.π.app j := by cat_disch

/-- A cocone morphism between two cocones for the same diagram is a morphism of the cocone points
which commutes with the cocone legs. -/
@[to_dual (reorder := A B)]
/-
**CategoryTheory.Limits.CoconeMorphism** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：CoconeMorphism (A B : Cocone F) where /-- A morphism between the (co)verte
x objects in `C` -/ hom : A.pt ⟶ B.pt /-- The triangle made from the two natural
 transformations and `hom` commutes -/ w (j : J) : dsimp% A.ι.app j ≫ hom = B.ι.
app j
参数：A B : Cocone F；co。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone morphism between two cocones for the same diagram is a morphism of the 
cocone points
which commutes with the cocone legs.
-/
structure CoconeMorphism (A B : Cocone F) where
  /-- A morphism between the (co)vertex objects in `C` -/
  hom : A.pt ⟶ B.pt
  /-- The triangle made from the two natural transformations and `hom` commutes -/
  w (j : J) : dsimp% A.ι.app j ≫ hom = B.ι.app j := by cat_disch

attribute [reassoc (attr := simp)] ConeMorphism.w CoconeMorphism.w
attribute [to_dual existing] ConeMorphism.casesOn

@[to_dual]
/-
**CategoryTheory.Limits.inhabitedConeMorphism** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：inhabitedConeMorphism (A : Cone F) : Inhabited (ConeMorphism A A)
参数：A : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedConeMorphism (A : Cone F) : Inhabited (ConeMorphism A A) :=
  ⟨{ hom := 𝟙 _ }⟩

/-- The category of cones on a given diagram. -/
@[to_dual (attr := simps) /-- The category of cocones on a given diagram. -/]
/-
**CategoryTheory.Limits.Cone.category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} →           CategoryTheory.Category.{v₃, max (max u₃ u₁
) v₃} (CategoryTheory.Limits.Cone F)
参数：max u₃ u₁；CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of cones on a given diagram.
-/
instance Cone.category : Category (Cone F) where
  Hom A B := ConeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

@[to_dual (attr := ext)
/- We do not want `simps` automatically generate the lemma for simplifying the
hom field of a category. So we need to write the `ext` lemma in terms of the
categorical morphism, rather than the underlying structure. -/]
/-
**CategoryTheory.Limits.ConeMorphism.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.ConeMorphism`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 {c c' : CategoryTheory.Limits.Cone F} (f g : c ⟶ c'), f.hom = g.hom → f = g
参数：f g : c ⟶ c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ConeMorphism.ext {c c' : Cone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.Limits.ConeMorphism.hom_inv_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.ConeMorphism`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 {c d : CategoryTheory.Limits.Cone F} (f : c ≅ d),   CategoryTheory.CategoryStru
ct.comp f.hom.hom f.inv.hom = CategoryTheory.CategoryStruct.id c.pt
参数：f : c ≅ d。
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
lemma ConeMorphism.hom_inv_id {c d : Cone F} (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.Limits.ConeMorphism.inv_hom_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.ConeMorphism`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheory.Functor J C}
 {c d : CategoryTheory.Limits.Cone F} (f : c ≅ d),   CategoryTheory.CategoryStru
ct.comp f.inv.hom f.hom.hom = CategoryTheory.CategoryStruct.id d.pt
参数：f : c ≅ d。
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
lemma ConeMorphism.inv_hom_id {c d : Cone F} (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

@[to_dual]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {c d : Cone F} (f : c ≅ d) : IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

@[to_dual]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {c d : Cone F} (f : c ≅ d) : IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.Limits.ConeMorphism.map_w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.ConeMorphism`。
形式化陈述：∀ {J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} 
[inst_1 : CategoryTheory.Category.{v₃, u₃} C]   {D : Type u₄} [inst_2 : Category
Theory.Category.{v₄, u₄} D] {F : CategoryTheory.Functor J C}   {c c' : CategoryT
heory.Limits.Cone F} (f : c ⟶ c') (G : CategoryTheory.Functor C D) (j : J),   Ca
tegoryTheory.CategoryStruct.comp (G.map f.hom) (G.map (c'.π.app j)) = G.map (c.π
.app j)
参数：f : c ⟶ c'；G : CategoryTheory.Functor C D；j : J；G.map f.hom；G.map (c'.π.app j
)；c.π.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ConeMorphism.w`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ConeMorphism.map_w {c c' : Cone F} (f : c ⟶ c') (G : C ⥤ D) (j : J) :
    G.map f.hom ≫ G.map (c'.π.app j) = G.map (c.π.app j) := by
  simp [← map_comp]

namespace Cone

set_option linter.translate.warnInvalid false in
/-- To give an isomorphism between cones, it suffices to give an
isomorphism between their vertices which commutes with the cone maps. -/
@[to_dual (attr := simps) extInv
/-- To give an isomorphism between cocones, it suffices to give an
isomorphism between their vertices which commutes with the cone maps. -/]
/-
**CategoryTheory.Limits.Cone.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.Cone`。
形式化陈述：ext {c c' : Cone F} (φ : c.pt ≅ c'.pt) (w : forall j, c.π.app j = φ.hom ≫ 
c'.π.app j
参数：φ : c.pt ≅ c'.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ext {c c' : Cone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      w := fun j => φ.inv_comp_eq.mpr (w j) }

attribute [to_dual existing extInv_inv_hom] ext_hom_hom
attribute [to_dual existing extInv_hom_hom] ext_inv_hom

set_option linter.translate.warnInvalid false in
/-- To give an isomorphism between cones, it suffices to give an
isomorphism between their vertices which commutes with the cone maps. -/
@[to_dual (attr := simps!) ext
/-- To give an isomorphism between cocones, it suffices to give an
isomorphism between their vertices which commutes with the cocone maps. -/]
/-
**CategoryTheory.Limits.Cone.extInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Cone`。
形式化陈述：extInv {c c' : Cone F} (φ : c.pt ≅ c'.pt) (w : forall j, φ.inv ≫ c.π.app j
 = c'.π.app j
参数：φ : c.pt ≅ c'.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def extInv {c c' : Cone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, φ.inv ≫ c.π.app j = c'.π.app j := by cat_disch) : c ≅ c' :=
  ext φ fun j ↦ (Iso.inv_comp_eq φ).mp (w j)

attribute [to_dual existing ext_hom_hom] extInv_inv_hom
attribute [to_dual existing ext_inv_hom] extInv_hom_hom

attribute [aesop apply safe (rule_sets := [CategoryTheory])] Limits.Cone.ext Limits.Cocone.ext

set_option linter.translate.warnInvalid false in
/-- Eta rule for cones. -/
@[to_dual (attr := simps!) /-- Eta rule for cocones. -/]
/-
**CategoryTheory.Limits.Cone.eta** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.Cone`。
形式化陈述：eta (c : Cone F) : c ≅ ⟨c.pt, c.π⟩
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Eta rule for cones.
-/
def eta (c : Cone F) : c ≅ ⟨c.pt, c.π⟩ :=
  ext (Iso.refl _)

attribute [to_dual existing eta_hom_hom] eta_inv_hom
attribute [to_dual existing eta_inv_hom] eta_hom_hom

/-- Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
@[to_dual
/-- Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/]
/-
**CategoryTheory.Limits.Cone.cone_iso_of_hom_iso** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Cone`。
形式化陈述：cone_iso_of_hom_iso {K : J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.ho
m] : IsIso f
参数：f : c ⟶ d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.ConeMorphism.w`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ConeMorphism.ext`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
theorem cone_iso_of_hom_iso {K : J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.hom] : IsIso f :=
  ⟨⟨{   hom := inv f.hom
        w := fun j => (asIso f.hom).inv_comp_eq.2 (f.w j).symm }, by cat_disch⟩⟩

/-- There is a morphism from an extended cone to the original cone. -/
@[to_dual (attr := simps) /-- There is a morphism from a cocone to its extension. -/]
/-
**CategoryTheory.Limits.Cone.extendHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Cone`。
形式化陈述：extendHom (s : Cone F) {X : C} (f : X ⟶ s.pt) : s.extend f ⟶ s where hom
参数：s : Cone F；f : X ⟶ s.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a morphism from an extended cone to the original cone.
-/
def extendHom (s : Cone F) {X : C} (f : X ⟶ s.pt) : s.extend f ⟶ s where
  hom := f

set_option linter.translate.warnInvalid false in
/-- Extending a cone by the identity does nothing. -/
@[to_dual (attr := simps!) /-- Extending a cocone by the identity does nothing. -/]
/-
**CategoryTheory.Limits.Cone.extendId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Cone`。
形式化陈述：extendId (s : Cone F) : s.extend (𝟙 s.pt) ≅ s
参数：s : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extending a cone by the identity does nothing.
-/
def extendId (s : Cone F) : s.extend (𝟙 s.pt) ≅ s :=
  ext (Iso.refl _)

attribute [to_dual existing extendId_inv_hom] extendId_hom_hom
attribute [to_dual existing extendId_hom_hom] extendId_inv_hom

set_option linter.translate.warnInvalid false in
/-- Extending a cone by a composition is the same as extending the cone twice. -/
@[to_dual (attr := simps!) (reorder := f g)
/-- Extending a cocone by a composition is the same as extending the cone twice. -/]
/-
**CategoryTheory.Limits.Cone.extendComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Cone`。
形式化陈述：extendComp (s : Cone F) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ s.pt) : s.extend (f
 ≫ g) ≅ (s.extend g).extend f
参数：s : Cone F；f : X ⟶ Y；g : Y ⟶ s.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def extendComp (s : Cone F) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ s.pt) :
    s.extend (f ≫ g) ≅ (s.extend g).extend f :=
  ext (Iso.refl _)

attribute [to_dual existing extendComp_inv_hom] extendComp_hom_hom
attribute [to_dual existing extendComp_hom_hom] extendComp_inv_hom

set_option linter.translate.warnInvalid false in
/-- A cone extended by an isomorphism is isomorphic to the original cone. -/
@[to_dual (attr := simps)
/-- A cocone extended by an isomorphism is isomorphic to the original cone. -/]
/-
**CategoryTheory.Limits.Cone.extendIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Cone`。
形式化陈述：extendIso (s : Cone F) {X : C} (f : s.pt ≅ X) : s ≅ s.extend f.inv where h
om
参数：s : Cone F；f : s.pt ≅ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def extendIso (s : Cone F) {X : C} (f : s.pt ≅ X) : s ≅ s.extend f.inv where
  hom := { hom := f.hom }
  inv := { hom := f.inv }

attribute [to_dual existing extendIso_inv_hom] extendIso_hom_hom
attribute [to_dual existing extendIso_hom_hom] extendIso_inv_hom

@[to_dual]
/-
**CategoryTheory.Limits.Cone.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits.C
one`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : Cone F} {X : C} (f : X ⟶ s.pt) [IsIso f] : IsIso (s.extendHom f) :=
  ⟨(extendIso s (asIso' f)).hom, by cat_disch⟩

/--
Functorially postcompose a cone for `F` by a natural transformation `F ⟶ G` to give a cone for `G`.
-/
@[to_dual (attr := implicit_reducible, simps)
/-- Functorially precompose a cocone for `F` by a natural transformation `G ⟶ F` to give a cocone
for `G`. -/]
/-
**CategoryTheory.Limits.Cone.postcompose** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Cone`。
形式化陈述：postcompose {G : J ⥤ C} (α : F ⟶ G) : Cone F ⥤ Cone G where obj c
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def postcompose {G : J ⥤ C} (α : F ⟶ G) : Cone F ⥤ Cone G where
  obj c :=
    { pt := c.pt
      π := c.π ≫ α }
  map f := { hom := f.hom }

set_option linter.translate.warnInvalid false in
/-- Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
@[to_dual (attr := simps!) (reorder := α β)
/-- Precomposing a cocone by the composite natural transformation `α ≫ β` is the same as
precomposing by `β` and then by `α`. -/]
/-
**CategoryTheory.Limits.Cone.postcomposeComp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Cone`。
形式化陈述：postcomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) : postcompose (α ≫ β
) ≅ postcompose α ⋙ postcompose β
参数：α : F ⟶ G；β : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def postcomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
  NatIso.ofComponents fun s => ext (Iso.refl _)

attribute [to_dual existing precomposeComp_inv_app_hom] postcomposeComp_hom_app_hom
attribute [to_dual existing precomposeComp_hom_app_hom] postcomposeComp_inv_app_hom

set_option linter.translate.warnInvalid false in
/-- Postcomposing by the identity does not change the cone up to isomorphism. -/
@[to_dual (attr := simps!)
/-- Precomposing by the identity does not change the cocone up to isomorphism. -/]
/-
**CategoryTheory.Limits.Cone.postcomposeId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cone`。
形式化陈述：postcomposeId : postcompose (𝟙 F) ≅ 𝟭 (Cone F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def postcomposeId : postcompose (𝟙 F) ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun s => ext (Iso.refl _)

attribute [to_dual existing precomposeId_inv_app_hom] postcomposeId_hom_app_hom
attribute [to_dual existing precomposeId_hom_app_hom] postcomposeId_inv_app_hom

/-- If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cones.
-/
@[to_dual (attr := implicit_reducible, simps)
/-- If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cocones.
-/]
/-
**CategoryTheory.Limits.Cone.postcomposeEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Cone`。
形式化陈述：postcomposeEquivalence {G : J ⥤ C} (α : F ≅ G) : Cone F ≌ Cone G where fun
ctor
参数：α : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def postcomposeEquivalence {G : J ⥤ C} (α : F ≅ G) : Cone F ≌ Cone G where
  functor := postcompose α.hom
  inverse := postcompose α.inv
  unitIso := NatIso.ofComponents fun s => ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s => ext (Iso.refl _)

/-- Whiskering on the left by `E : K ⥤ J` gives a functor from `Cone F` to `Cone (E ⋙ F)`.
-/
@[to_dual (attr := implicit_reducible, simps)
/-- Whiskering on the left by `E : K ⥤ J` gives a functor from `Cocone F` to `Cocone (E ⋙ F)`.
-/]
/-
**CategoryTheory.Limits.Cone.whiskering** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Cone`。
形式化陈述：whiskering (E : K ⥤ J) : Cone F ⥤ Cone (E ⋙ F) where obj c
参数：E : K ⥤ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def whiskering (E : K ⥤ J) : Cone F ⥤ Cone (E ⋙ F) where
  obj c := c.whisker E
  map f := { hom := f.hom }

/-- Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[to_dual (attr := simps)
/-- Whiskering by an equivalence gives an equivalence between categories of cones.
-/]
/-
**CategoryTheory.Limits.Cone.whiskeringEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Cone`。
形式化陈述：whiskeringEquivalence (e : K ≌ J) : Cone F ≌ Cone (e.functor ⋙ F) where fu
nctor
参数：e : K ≌ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def whiskeringEquivalence (e : K ≌ J) : Cone F ≌ Cone (e.functor ⋙ F) where
  functor := whiskering e.functor
  inverse := whiskering e.inverse ⋙ postcompose (e.invFunIdAssoc F).hom
  unitIso := NatIso.ofComponents fun s => ext (Iso.refl _)
  counitIso :=
    NatIso.ofComponents
      fun s =>
        ext (Iso.refl _)
          (by
            intro k
            simpa [e.counit_app_functor] using s.w (e.unitInv.app k))

/-- The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
@[to_dual (attr := simps! functor inverse unitIso counitIso)
/-- The categories of cocones over `F` and `G` are equivalent if `F` and `G` are naturally
isomorphic (possibly after changing the indexing category by an equivalence).
-/]
/-
**CategoryTheory.Limits.Cone.equivalenceOfReindexing** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Cone`。
形式化陈述：equivalenceOfReindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : 
Cone F ≌ Cone G
参数：e : K ≌ J；α : e.functor ⋙ F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivalenceOfReindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : Cone F ≌ Cone G :=
  (whiskeringEquivalence e).trans (postcomposeEquivalence α)

section

variable (F)

/-- Forget the cone structure and obtain just the cone point. -/
@[to_dual (attr := simps) /-- Forget the cocone structure and obtain just the cocone point. -/]
/-
**CategoryTheory.Limits.Cone.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Cone`。
形式化陈述：forget : Cone F ⥤ C where obj t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forget the cone structure and obtain just the cone point.
-/
def forget : Cone F ⥤ C where
  obj t := t.pt
  map f := f.hom

variable (G : C ⥤ D)

/-- A functor `G : C ⥤ D` sends cones over `F` to cones over `F ⋙ G` functorially. -/
@[to_dual (attr := implicit_reducible, simps)
/-- A functor `G : C ⥤ D` sends cocones over `F` to cocones over `F ⋙ G` functorially. -/]
/-
**CategoryTheory.Limits.Cone.functoriality** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cone`。
形式化陈述：functoriality : Cone F ⥤ Cone (F ⋙ G) where obj A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ConeMorphism.map_w`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v
₃, u₃} C]   {D : Type u₄} [ins…
-/
def functoriality : Cone F ⥤ Cone (F ⋙ G) where
  obj A :=
    { pt := G.obj A.pt
      π :=
        { app := fun j => G.map (A.π.app j)
          naturality := by simp [← G.map_comp] } }
  map f :=
    { hom := G.map f.hom
      w := ConeMorphism.map_w f G }

/-- Functoriality is functorial. -/
@[to_dual /-- Functoriality is functorial. -/]
/-
**CategoryTheory.Limits.Cone.functorialityCompFunctoriality** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.Cone`。
形式化陈述：functorialityCompFunctoriality (H : D ⥤ E) : functoriality F G ⋙ functoria
lity (F ⋙ G) H ≅ functoriality F (G ⋙ H)
参数：H : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality is functorial.
-/
def functorialityCompFunctoriality (H : D ⥤ E) :
    functoriality F G ⋙ functoriality (F ⋙ G) H ≅ functoriality F (G ⋙ H) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

@[to_dual]
/-
**CategoryTheory.Limits.Cone.functoriality_full** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Limits.Cone`。
形式化陈述：functoriality_full [G.Full] [G.Faithful] : (functoriality F G).Full where 
map_surjective t
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Limits.ConeMorphism.w`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ConeMorphism.ext`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance functoriality_full [G.Full] [G.Faithful] : (functoriality F G).Full where
  map_surjective t :=
    ⟨{ hom := G.preimage t.hom
       w := fun j => G.map_injective (by simpa using t.w j) }, by cat_disch⟩

@[to_dual]
/-
**CategoryTheory.Limits.Cone.functoriality_faithful** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits.Cone`。
形式化陈述：functoriality_faithful [G.Faithful] : (functoriality F G).Faithful where m
ap_injective {_X} {_Y} f g h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ConeMorphism.ext`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃,
 u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance functoriality_faithful [G.Faithful] : (functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    ConeMorphism.ext f g <| G.map_injective <| congr_arg ConeMorphism.hom h

set_option backward.isDefEq.respectTransparency.types false in
/-- If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cones over `F` and cones over `F ⋙ e.functor`.
-/
@[to_dual (attr := simps)
/-- If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cocones over `F` and cocones over `F ⋙ e.functor`.
-/]
/-
**CategoryTheory.Limits.Cone.functorialityEquivalence** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.Cone`。
形式化陈述：functorialityEquivalence (e : C ≌ D) : Cone F ≌ Cone (F ⋙ e.functor)
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def functorialityEquivalence (e : C ≌ D) : Cone F ≌ Cone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  { functor := functoriality F e.functor
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (postcomposeEquivalence f).functor
    unitIso := NatIso.ofComponents fun c => ext (e.unitIso.app _)
    counitIso := NatIso.ofComponents fun c => ext (e.counitIso.app _) }

/-- If `F` reflects isomorphisms, then `functoriality F` reflects isomorphisms
as well.
-/
@[to_dual
/-- If `F` reflects isomorphisms, then `Cocones.functoriality F` reflects isomorphisms
as well.
-/]
/-
**CategoryTheory.Limits.Cone.reflects_cone_isomorphism** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits.Cone`。
形式化陈述：reflects_cone_isomorphism (F : C ⥤ D) [F.ReflectsIsomorphisms] (K : J ⥤ C)
 : (functoriality K F).ReflectsIsomorphisms
参数：F : C ⥤ D；K : J ⥤ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ReflectsIsomorphisms.reflects`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} (F : Categor…
· 使用定理 `CategoryTheory.Limits.Cone.cone_iso_of_hom_iso`：cone_iso_of_hom_iso {K :
 J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.hom] : IsIso f
-/
instance reflects_cone_isomorphism (F : C ⥤ D) [F.ReflectsIsomorphisms] (K : J ⥤ C) :
    (functoriality K F).ReflectsIsomorphisms := by
  constructor
  intro A B f _
  have : IsIso (F.map f.hom) :=
    (forget (K ⋙ F)).map_isIso ((functoriality K F).map f)
  have := ReflectsIsomorphisms.reflects F f.hom
  apply cone_iso_of_hom_iso

end

end Cone

namespace Cones

@[deprecated (since := "2026-03-06")] alias ext := Cone.ext
@[deprecated (since := "2026-03-06")] alias eta := Cone.eta
@[deprecated (since := "2026-03-06")] alias cone_iso_of_hom_iso := Cone.cone_iso_of_hom_iso
@[deprecated (since := "2026-03-06")] alias extend := Cone.extendHom
@[deprecated (since := "2026-03-06")] alias extendId := Cone.extendId
@[deprecated (since := "2026-03-06")] alias extendComp := Cone.extendComp
@[deprecated (since := "2026-03-06")] alias extendIso := Cone.extendIso
@[deprecated (since := "2026-03-06")] alias postcompose := Cone.postcompose
@[deprecated (since := "2026-03-06")] alias postcomposeComp := Cone.postcomposeComp
@[deprecated (since := "2026-03-06")] alias postcomposeId := Cone.postcomposeId
@[deprecated (since := "2026-03-06")] alias postcomposeEquivalence := Cone.postcomposeEquivalence
@[deprecated (since := "2026-03-06")] alias whiskering := Cone.whiskering
@[deprecated (since := "2026-03-06")] alias whiskeringEquivalence := Cone.whiskeringEquivalence
@[deprecated (since := "2026-03-06")] alias equivalenceOfReindexing := Cone.equivalenceOfReindexing
@[deprecated (since := "2026-03-06")] alias forget := Cone.forget
@[deprecated (since := "2026-03-06")] alias functoriality := Cone.functoriality
@[deprecated (since := "2026-03-06")]
alias functorialityCompFunctoriality := Cone.functorialityCompFunctoriality
@[deprecated (since := "2026-03-06")] alias functoriality_full := Cone.functoriality_full
@[deprecated (since := "2026-03-06")] alias functoriality_faithful := Cone.functoriality_faithful
@[deprecated (since := "2026-03-06")]
alias functorialityEquivalence := Cone.functorialityEquivalence
@[deprecated (since := "2026-03-06")]
alias reflects_cone_isomorphism := Cone.reflects_cone_isomorphism

end Cones

namespace Cocones

@[deprecated (since := "2026-03-06")] alias ext := Cocone.ext
@[deprecated (since := "2026-03-06")] alias eta := Cocone.eta
@[deprecated (since := "2026-03-06")] alias cone_iso_of_hom_iso := Cocone.cocone_iso_of_hom_iso
@[deprecated (since := "2026-03-06")] alias extend := Cocone.extendHom
@[deprecated (since := "2026-03-06")] alias extendId := Cocone.extendId
@[deprecated (since := "2026-03-06")] alias extendComp := Cocone.extendComp
@[deprecated (since := "2026-03-06")] alias extendIso := Cocone.extendIso
@[deprecated (since := "2026-03-06")] alias postcompose := Cocone.precompose
@[deprecated (since := "2026-03-06")] alias postcomposeComp := Cocone.precomposeComp
@[deprecated (since := "2026-03-06")] alias postcomposeId := Cocone.precomposeId
@[deprecated (since := "2026-03-06")] alias postcomposeEquivalence := Cocone.precomposeEquivalence
@[deprecated (since := "2026-03-06")] alias whiskering := Cocone.whiskering
@[deprecated (since := "2026-03-06")] alias whiskeringEquivalence := Cocone.whiskeringEquivalence
@[deprecated (since := "2026-03-06")]
alias equivalenceOfReindexing := Cocone.equivalenceOfReindexing
@[deprecated (since := "2026-03-06")] alias forget := Cocone.forget
@[deprecated (since := "2026-03-06")] alias functoriality := Cocone.functoriality
@[deprecated (since := "2026-03-06")]
alias functorialityCompFunctoriality := Cocone.functorialityCompFunctoriality
@[deprecated (since := "2026-03-06")] alias functoriality_full := Cocone.functoriality_full
@[deprecated (since := "2026-03-06")] alias functoriality_faithful := Cocone.functoriality_faithful
@[deprecated (since := "2026-03-06")]
alias functorialityEquivalence := Cocone.functorialityEquivalence
@[deprecated (since := "2026-03-06")]
alias reflects_cone_isomorphism := Cocone.reflects_cocone_isomorphism

end Cocones

end Limits

namespace Functor

variable (H : C ⥤ D) {F : J ⥤ C} {G : J ⥤ C}

open CategoryTheory.Limits

/-- The image of a cone in C under a functor G : C ⥤ D is a cone in D. -/
@[to_dual (attr := implicit_reducible, simps!)
/-- The image of a cocone in C under a functor G : C ⥤ D is a cocone in D. -/]
/-
**CategoryTheory.Functor.mapCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：mapCone (c : Cone F) : Cone (F ⋙ H)
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapCone (c : Cone F) : Cone (F ⋙ H) :=
  (Cone.functoriality F H).obj c

set_option linter.translate.warnInvalid false in
/-- The construction `mapCone` respects functor composition. -/
@[to_dual (attr := simps!)
/-- The construction `mapCocone` respects functor composition. -/]
/-
**CategoryTheory.Functor.mapConeMapCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：mapConeMapCone {F : J ⥤ C} {H : C ⥤ D} {H' : D ⥤ E} (c : Cone F) : H'.mapC
one (H.mapCone c) ≅ (H ⋙ H').mapCone c
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mapConeMapCone {F : J ⥤ C} {H : C ⥤ D} {H' : D ⥤ E} (c : Cone F) :
    H'.mapCone (H.mapCone c) ≅ (H ⋙ H').mapCone c := Cone.ext (Iso.refl _)

attribute [to_dual existing mapCoconeMapCocone_inv_hom] mapConeMapCone_hom_hom
attribute [to_dual existing mapCoconeMapCocone_hom_hom] mapConeMapCone_inv_hom

/-- Given a cone morphism `c ⟶ c'`, construct a cone morphism on the mapped cones functorially. -/
@[to_dual
/-- Given a cocone morphism `c ⟶ c'`, construct a cocone morphism on the mapped cocones
functorially. -/]
/-
**CategoryTheory.Functor.mapConeMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：mapConeMorphism {c c' : Cone F} (f : c ⟶ c') : H.mapCone c ⟶ H.mapCone c'
参数：f : c ⟶ c'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapConeMorphism {c c' : Cone F} (f : c ⟶ c') : H.mapCone c ⟶ H.mapCone c' :=
  (Cone.functoriality F H).map f

/-- If `H` is an equivalence, we invert `H.mapCone` and get a cone for `F` from a cone
for `F ⋙ H`. -/
@[to_dual
/-- If `H` is an equivalence, we invert `H.mapCone` and get a cone for `F` from a cone
for `F ⋙ H`. -/]
/-
**CategoryTheory.Functor.mapConeInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：mapConeInv [IsEquivalence H] (c : Cone (F ⋙ H)) : Cone F
参数：c : Cone (F ⋙ H)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mapConeInv [IsEquivalence H] (c : Cone (F ⋙ H)) : Cone F :=
  (Limits.Cone.functorialityEquivalence F (asEquivalence H)).inverse.obj c

/-- `mapCone` is the left inverse to `mapConeInv`. -/
@[to_dual /-- `mapCocone` is the left inverse to `mapCoconeInv`. -/]
/-
**CategoryTheory.Functor.mapConeMapConeInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapConeMapConeInv {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cone (F ⋙
 H)) : mapCone H (mapConeInv H c) ≅ c
参数：H : D ⥤ C；c : Cone (F ⋙ H)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapCone` is the left inverse to `mapConeInv`.
-/
noncomputable def mapConeMapConeInv {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H]
    (c : Cone (F ⋙ H)) :
    mapCone H (mapConeInv H c) ≅ c :=
  (Limits.Cone.functorialityEquivalence F (asEquivalence H)).counitIso.app c

/-- `mapCone` is the right inverse to `mapConeInv`. -/
@[to_dual /-- `mapCocone` is the right inverse to `mapCoconeInv`. -/]
/-
**CategoryTheory.Functor.mapConeInvMapCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapConeInvMapCone {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cone F) :
 mapConeInv H (mapCone H c) ≅ c
参数：H : D ⥤ C；c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapCone` is the right inverse to `mapConeInv`.
-/
noncomputable def mapConeInvMapCone {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cone F) :
    mapConeInv H (mapCone H c) ≅ c :=
  (Limits.Cone.functorialityEquivalence F (asEquivalence H)).unitIso.symm.app c

set_option linter.translate.warnInvalid false in
/-- `functoriality F _ ⋙ postcompose (whisker_left F _)` simplifies to `functoriality F _`. -/
@[to_dual (attr := simps!)
/-- `functoriality F _ ⋙ precompose (whiskerLeft F _)` simplifies to `functoriality F _`. -/]
/-
**CategoryTheory.Functor.functorialityCompPostcompose** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：functorialityCompPostcompose {H H' : C ⥤ D} (α : H ≅ H') : Cone.functorial
ity F H ⋙ Cone.postcompose (whiskerLeft F α.hom) ≅ Cone.functoriality F H'
参数：α : H ≅ H'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def functorialityCompPostcompose {H H' : C ⥤ D} (α : H ≅ H') :
    Cone.functoriality F H ⋙ Cone.postcompose (whiskerLeft F α.hom) ≅ Cone.functoriality F H' :=
  NatIso.ofComponents fun c => Cone.ext (α.app _)

attribute [to_dual existing functorialityCompPrecompose_inv_app_hom]
  functorialityCompPostcompose_hom_app_hom
attribute [to_dual existing functorialityCompPrecompose_hom_app_hom]
  functorialityCompPostcompose_inv_app_hom

set_option linter.translate.warnInvalid false in
/-- For `F : J ⥤ C`, given a cone `c : Cone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the postcomposition of the cone `H.mapCone` using the isomorphism `α` is
isomorphic to the cone `H'.mapCone`.
-/
@[to_dual (attr := simps!)
/--
For `F : J ⥤ C`, given a cocone `c : Cocone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the precomposition of the cocone `H.mapCocone` using the isomorphism `α` is
isomorphic to the cocone `H'.mapCocone`.
-/]
/-
**CategoryTheory.Functor.postcomposeWhiskerLeftMapCone** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：postcomposeWhiskerLeftMapCone {H H' : C ⥤ D} (α : H ≅ H') (c : Cone F) : (
Cone.postcompose (whiskerLeft F α.hom :)).obj (mapCone H c) ≅ mapCone H' c
参数：α : H ≅ H'；c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def postcomposeWhiskerLeftMapCone {H H' : C ⥤ D} (α : H ≅ H') (c : Cone F) :
    (Cone.postcompose (whiskerLeft F α.hom :)).obj (mapCone H c) ≅ mapCone H' c :=
  (functorialityCompPostcompose α).app c

attribute [to_dual existing precomposeWhiskerLeftMapCocone_inv_hom]
  postcomposeWhiskerLeftMapCone_hom_hom
attribute [to_dual existing precomposeWhiskerLeftMapCocone_hom_hom]
  postcomposeWhiskerLeftMapCone_inv_hom

set_option linter.translate.warnInvalid false in
/--
`mapCone` commutes with `postcompose`. In particular, for `F : J ⥤ C`, given a cone `c : Cone F`, a
natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious ways of producing
a cone over `G ⋙ H`, and they are both isomorphic.
-/
@[to_dual (attr := simps!)
/-- `map_cocone` commutes with `precompose`. In particular, for `F : J ⥤ C`, given a cocone
`c : Cocone F`, a natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious
ways of producing a cocone over `G ⋙ H`, and they are both isomorphic.
-/]
/-
**CategoryTheory.Functor.mapConePostcompose** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：mapConePostcompose {α : F ⟶ G} {c} : mapCone H ((Cone.postcompose α).obj c
) ≅ (Cone.postcompose (whiskerRight α H :)).obj (mapCone H c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapConePostcompose {α : F ⟶ G} {c} :
    mapCone H ((Cone.postcompose α).obj c) ≅
      (Cone.postcompose (whiskerRight α H :)).obj (mapCone H c) :=
  Cone.ext (Iso.refl _)

attribute [to_dual existing mapCoconePrecompose_inv_hom] mapConePostcompose_hom_hom
attribute [to_dual existing mapCoconePrecompose_hom_hom] mapConePostcompose_inv_hom

set_option linter.translate.warnInvalid false in
/-- `mapCone` commutes with `postcomposeEquivalence` -/
@[to_dual (attr := simps!) /-- `mapCocone` commutes with `precomposeEquivalence` -/]
/-
**CategoryTheory.Functor.mapConePostcomposeEquivalenceFunctor** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mapConePostcomposeEquivalenceFunctor {α : F ≅ G} {c} : mapCone H ((Cone.po
stcomposeEquivalence α).functor.obj c) ≅ (Cone.postcomposeEquivalence (isoWhiske
rRight α H :)).functor.obj (mapCone H c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapCone` commutes with `postcomposeEquivalence`
-/
def mapConePostcomposeEquivalenceFunctor {α : F ≅ G} {c} :
    mapCone H ((Cone.postcomposeEquivalence α).functor.obj c) ≅
      (Cone.postcomposeEquivalence (isoWhiskerRight α H :)).functor.obj (mapCone H c) :=
  Cone.ext (Iso.refl _)

attribute [to_dual existing mapCoconePrecomposeEquivalenceFunctor_inv_hom]
  mapConePostcomposeEquivalenceFunctor_hom_hom
attribute [to_dual existing mapCoconePrecomposeEquivalenceFunctor_hom_hom]
  mapConePostcomposeEquivalenceFunctor_inv_hom

set_option linter.translate.warnInvalid false in
/-- `mapCone` commutes with `whisker` -/
@[to_dual (attr := simps!) /-- `mapCocone` commutes with `whisker` -/]
/-
**CategoryTheory.Functor.mapConeWhisker** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：mapConeWhisker {E : K ⥤ J} {c : Cone F} : mapCone H (c.whisker E) ≅ (mapCo
ne H c).whisker E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapCone` commutes with `whisker`
-/
def mapConeWhisker {E : K ⥤ J} {c : Cone F} : mapCone H (c.whisker E) ≅ (mapCone H c).whisker E :=
  Cone.ext (Iso.refl _)

attribute [to_dual existing mapCoconeWhisker_inv_hom] mapConeWhisker_hom_hom
attribute [to_dual existing mapCoconeWhisker_hom_hom] mapConeWhisker_inv_hom

end Functor

namespace Limits

section

variable {F : J ⥤ C}

/-- Change a `Cone F` into a `Cocone F.op`. -/
@[to_dual (attr := implicit_reducible, simps) /-- Change a `Cocone F` into a `Cone F.op`. -/]
/-
**CategoryTheory.Limits.Cone.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} → CategoryTheory.Limits.Cone F → CategoryTheory.Limits.
Cocone F.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change a `Cone F` into a `Cocone F.op`.
-/
def Cone.op (c : Cone F) : Cocone F.op where
  pt := Opposite.op c.pt
  ι := NatTrans.op c.π

/-- Change a `Cone F.op` into a `Cocone F`. -/
@[to_dual (attr := implicit_reducible, simps) /-- Change a `Cocone F.op` into a `Cone F`. -/]
/-
**CategoryTheory.Limits.Cone.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Cone`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {F : Cat
egoryTheory.Functor J C} → CategoryTheory.Limits.Cone F.op → CategoryTheory.Limi
ts.Cocone F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change a `Cone F.op` into a `Cocone F`.
-/
def Cone.unop (c : Cone F.op) : Cocone F where
  pt := Opposite.unop c.pt
  ι := NatTrans.removeOp c.π

variable (F)

/-- The category of cocones on `F` is equivalent to the opposite category of
the category of cones on the opposite of `F`.
-/
@[to_dual (attr := simp)
/-- The category of cones on `F` is equivalent to the opposite category of
the category of cocones on the opposite of `F`.
-/]
/-
**CategoryTheory.Limits.coconeEquivalenceOpConeOp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：coconeEquivalenceOpConeOp : Cocone F ≌ (Cone F.op)ᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeEquivalenceOpConeOp : Cocone F ≌ (Cone F.op)ᵒᵖ where
  functor :=
    { obj := fun c => op (Cocone.op c)
      map := fun {X} {Y} f =>
        Quiver.Hom.op
          { hom := f.hom.op
            w := fun j => by
              apply Quiver.Hom.unop_inj
              dsimp
              apply CoconeMorphism.w } }
  inverse :=
    { obj := fun c => Cone.unop (unop c)
      map := fun {X} {Y} f =>
        { hom := f.unop.hom.unop
          w := fun j => by
            apply Quiver.Hom.op_inj
            dsimp
            apply ConeMorphism.w } }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Cones on `F : J ⥤ C` are equivalent to cocones on `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : J ⥤ C` are equivalent to cones on `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/]
/-
**CategoryTheory.Limits.coneOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：coneOpEquiv {F : J ⥤ C} : (Cone F)ᵒᵖ ≌ Cocone F.op where functor.obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coneOpEquiv {F : J ⥤ C} : (Cone F)ᵒᵖ ≌ Cocone F.op where
  functor.obj c := c.unop.op
  functor.map f := { hom := f.unop.hom.op, w j := congr($(f.unop.w j.unop).op) }
  inverse.obj c := .op <| c.unop
  inverse.map f := ⟨{ hom := f.hom.unop, w j := congr($(f.w (.op j)).unop) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

section

variable {F : J ⥤ Cᵒᵖ}

/-- Change a cocone on `F.leftOp : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
@[to_dual (attr := implicit_reducible, simps!)
/-- Change a cone on `F.leftOp : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/]
/-
**CategoryTheory.Limits.coneOfCoconeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：coneOfCoconeLeftOp (c : Cocone F.leftOp) : Cone F where pt
参数：c : Cocone F.leftOp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coneOfCoconeLeftOp (c : Cocone F.leftOp) : Cone F where
  pt := op c.pt
  π := NatTrans.removeLeftOp c.ι

/-- Change a cone on `F : J ⥤ Cᵒᵖ` to a cocone on `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := implicit_reducible, simps!)
/-- Change a cocone on `F : J ⥤ Cᵒᵖ` to a cone on `F.leftOp : Jᵒᵖ ⥤ C`. -/]
/-
**CategoryTheory.Limits.coconeLeftOpOfCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：coconeLeftOpOfCone (c : Cone F) : Cocone F.leftOp where pt
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeLeftOpOfCone (c : Cone F) : Cocone F.leftOp where
  pt := unop c.pt
  ι := NatTrans.leftOp c.π

/-- Cones on `F : J ⥤ Cᵒᵖ` are equivalent to cocones on `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : J ⥤ Cᵒᵖ` are equivalent to cones on `F.leftOp : Jᵒᵖ ⥤ C`. -/]
/-
**CategoryTheory.Limits.coconeLeftOpOfConeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：coconeLeftOpOfConeEquiv {F : J ⥤ Cᵒᵖ} : (Cone F)ᵒᵖ ≌ Cocone F.leftOp where
 functor.obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeLeftOpOfConeEquiv {F : J ⥤ Cᵒᵖ} : (Cone F)ᵒᵖ ≌ Cocone F.leftOp where
  functor.obj c := coconeLeftOpOfCone c.unop
  functor.map f := { hom := f.unop.hom.unop, w j := congr($(f.unop.w j.unop).unop) }
  inverse.obj c := .op <| coneOfCoconeLeftOp c
  inverse.map f := ⟨{ hom := f.hom.op, w j := congr($(f.w (.op j)).op) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

section

variable {F : Jᵒᵖ ⥤ C}

/-- Change a cocone on `F.rightOp : J ⥤ Cᵒᵖ` to a cone on `F : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := implicit_reducible, simps)
/-- Change a cone on `F.rightOp : J ⥤ Cᵒᵖ` to a cocone on `F : Jᵒᵖ ⥤ C`. -/]
/-
**CategoryTheory.Limits.coneOfCoconeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：coneOfCoconeRightOp (c : Cocone F.rightOp) : Cone F where pt
参数：c : Cocone F.rightOp。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coneOfCoconeRightOp (c : Cocone F.rightOp) : Cone F where
  pt := unop c.pt
  π := NatTrans.removeRightOp c.ι

/-- Change a cone on `F : Jᵒᵖ ⥤ C` to a cocone on `F.rightOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := implicit_reducible, simps)
/-- Change a cocone on `F : Jᵒᵖ ⥤ C` to a cone on `F.rightOp : J ⥤ Cᵒᵖ`. -/]
/-
**CategoryTheory.Limits.coconeRightOpOfCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：coconeRightOpOfCone (c : Cone F) : Cocone F.rightOp where pt
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeRightOpOfCone (c : Cone F) : Cocone F.rightOp where
  pt := op c.pt
  ι := NatTrans.rightOp c.π

/-- Cones on `F : Jᵒᵖ ⥤ C` are equivalent to cocones on `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : Jᵒᵖ ⥤ C` are equivalent to cones on `F.rightOp : J ⥤ Cᵒᵖ`. -/]
/-
**CategoryTheory.Limits.coconeRightOpOfConeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：coconeRightOpOfConeEquiv {F : Jᵒᵖ ⥤ C} : (Cone F)ᵒᵖ ≌ Cocone F.rightOp whe
re functor.obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeRightOpOfConeEquiv {F : Jᵒᵖ ⥤ C} : (Cone F)ᵒᵖ ≌ Cocone F.rightOp where
  functor.obj c := coconeRightOpOfCone c.unop
  functor.map f := { hom := f.unop.hom.op, w j := congr($(f.unop.w (.op j)).op) }
  inverse.obj c := .op <| coneOfCoconeRightOp c
  inverse.map f := ⟨{ hom := f.hom.unop, w j := congr($(f.w j.unop).unop) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

section

variable {F : Jᵒᵖ ⥤ Cᵒᵖ}

/-- Change a cocone on `F.unop : J ⥤ C` into a cone on `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[to_dual (attr := implicit_reducible, simps)
/-- Change a cone on `F.unop : J ⥤ C` into a cocone on `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/]
/-
**CategoryTheory.Limits.coneOfCoconeUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：coneOfCoconeUnop (c : Cocone F.unop) : Cone F where pt
参数：c : Cocone F.unop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coneOfCoconeUnop (c : Cocone F.unop) : Cone F where
  pt := op c.pt
  π := NatTrans.removeUnop c.ι

/-- Change a cone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cocone on `F.unop : J ⥤ C`. -/
@[to_dual (attr := implicit_reducible, simps)
/-- Change a cocone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cone on `F.unop : J ⥤ C`. -/]
/-
**CategoryTheory.Limits.coconeUnopOfCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：coconeUnopOfCone (c : Cone F) : Cocone F.unop where pt
参数：c : Cone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeUnopOfCone (c : Cone F) : Cocone F.unop where
  pt := unop c.pt
  ι := NatTrans.unop c.π

/-- Cones on `F : Jᵒᵖ ⥤ Cᵒᵖ` are equivalent to cocones on `F.unop : J ⥤ C`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : Jᵒᵖ ⥤ Cᵒᵖ` are equivalent to cones on `F.unop : J ⥤ C`. -/]
/-
**CategoryTheory.Limits.coconeUnopOfConeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：coconeUnopOfConeEquiv {F : Jᵒᵖ ⥤ Cᵒᵖ} : (Cone F)ᵒᵖ ≌ Cocone F.unop where f
unctor.obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coconeUnopOfConeEquiv {F : Jᵒᵖ ⥤ Cᵒᵖ} : (Cone F)ᵒᵖ ≌ Cocone F.unop where
  functor.obj c := coconeUnopOfCone c.unop
  functor.map f := { hom := f.unop.hom.unop, w j := congr($(f.unop.w (.op j)).unop) }
  inverse.obj c := .op <| coneOfCoconeUnop c
  inverse.map f := ⟨{ hom := f.hom.op, w j := congr($(f.w j.unop).op) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {F : J ⥤ C} (G : C ⥤ D)

set_option linter.translate.warnInvalid false in
/-- The opposite cocone of the image of a cone is the image of the opposite cocone. -/
@[to_dual (attr := simps!)
/-- The opposite cone of the image of a cocone is the image of the opposite cone. -/]
/-
**CategoryTheory.Functor.mapConeOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：{J : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} J] →     {C : T
ype u₃} →       [inst_1 : CategoryTheory.Category.{v₃, u₃} C] →         {D : Typ
e u₄} →           [inst_2 : CategoryTheory.Category.{v₄, u₄} D] →             {F
 : CategoryTheory.Functor J C} →               (G : CategoryTheory.Functor C D) 
→                 (t : CategoryTheory.Limits.Cone F) → (G.mapCone t).op ≅ G.op.m
apCocone t.op
参数：G : CategoryTheory.Functor C D；t : CategoryTheory.Limits.Cone F；G.mapCone t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapConeOp (t : Cone F) : (mapCone G t).op ≅ mapCocone G.op t.op :=
  Cocone.ext (Iso.refl _)

attribute [to_dual existing mapCoconeOp_inv_hom] mapConeOp_hom_hom
attribute [to_dual existing mapCoconeOp_hom_hom] mapConeOp_inv_hom

end CategoryTheory.Functor

