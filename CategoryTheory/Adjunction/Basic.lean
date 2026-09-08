/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Adjunctions between functors

`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We provide various useful constructors:
* `mkOfHomEquiv`
* `mk'`: construct an adjunction from the data of a hom set equivalence, unit and counit natural
  transformations together with proofs of the equalities `homEquiv_unit` and `homEquiv_counit`
  relating them to each other.
* `leftAdjointOfEquiv` / `rightAdjointOfEquiv`
  construct a left/right adjoint of a given functor given the action on objects and
  the relevant equivalence of morphism spaces.
* `adjunctionOfEquivLeft` / `adjunctionOfEquivRight` witness that these constructions
  give adjunctions.

There are also typeclasses `IsLeftAdjoint` / `IsRightAdjoint`, which assert the
existence of an adjoint functor. Given `[F.IsLeftAdjoint]`, a chosen right
adjoint can be obtained as `F.rightAdjoint`.

`Adjunction.comp` composes adjunctions.

`toEquivalence` upgrades an adjunction to an equivalence,
given witnesses that the unit and counit are pointwise isomorphisms.
Conversely `Equivalence.toAdjunction` recovers the underlying adjunction from an equivalence.

## Overview of the directory `CategoryTheory.Adjunction`

* Adjoint lifting theorems are in the directory `Lifting`.
* The file `AdjointFunctorTheorems` proves the adjoint functor theorems.
* The file `Additive` develops adjunctions between additive functors.
* The file `Comma` shows that for a functor `G : D ⥤ C` the data of an initial object in each
  `StructuredArrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.
* The file `CompositionIso` derives compatibilities for compositions of left adjoints from the
  corresponding data on right adjoints.
* The file `Evaluation` shows that products and coproducts are adjoint to evaluation of functors.
* The file `FullyFaithful` characterizes when adjoints are full or faithful in terms of the unit
  and counit.
* The file `Limits` proves that left adjoints preserve colimits and right adjoints preserve limits.
* The file `Mates` establishes the bijection between the 2-cells
  ```
          L₁                  R₁
        C --→ D             C ←-- D
      G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
        E --→ F             E ←-- F
          L₂                  R₂
  ```
  where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. Specializing to a pair of adjoints `L₁ L₂ : C ⥤ D`,
  `R₁ R₂ : D ⥤ C`, it provides equivalences `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)` and `(L₂ ≅ L₁) ≃ (R₁ ≅ R₂)`.
* The file `Opposites` contains constructions to relate adjunctions of functors to adjunctions of
  their opposites.
* The file `Parametrized` defines adjunctions with a parameter.
* The file `PartialAdjoint` studies the domain of definition of partial adjoints (left/right).
* The file `Reflective` defines reflective functors, i.e. fully faithful right adjoints. Note that
  many facts about reflective functors are proved in the earlier file `FullyFaithful`.
* The file `Restrict` defines the restriction of an adjunction along fully faithful functors.
* The file `Triple` proves that in an adjoint triple, the left adjoint is fully faithful if and
  only if the right adjoint is.
* The file `Quadruple` bundles adjoint quadruples and compares induced natural transformations.
* The file `Unique` proves uniqueness of adjoints.
* The file `Whiskering` proves that functors `F : D ⥤ E` and `G : E ⥤ D` with an adjunction
  `F ⊣ G`, induce adjunctions between the functor categories `C ⥤ D` and `C ⥤ E`,
  and the functor categories `E ⥤ C` and `D ⥤ C`.

## Other files related to adjunctions

* The file `Mathlib/CategoryTheory/Monad/Adjunction.lean` develops the basic relationship between
  adjunctions and (co)monads. There it is also shown that given an adjunction `L ⊣ R` and an
  isomorphism `L ⋙ R ≅ 𝟭 C`, the unit is an isomorphism, and similarly for the counit.
-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option linter.translate.warnInvalid false in
/-- `F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

We use the unit-counit definition of an adjunction. There is a constructor `Adjunction.mk'`
which constructs an adjunction from the data of a hom set equivalence, a unit, and a counit,
together with proofs of the equalities `homEquiv_unit` and `homEquiv_counit` relating them to each
other.

There is also a constructor `Adjunction.mkOfHomEquiv` which constructs an adjunction from a natural
hom set equivalence.

To construct adjoints to a given functor, there are constructors `leftAdjointOfEquiv` and
`adjunctionOfEquivLeft` (as well as their duals). -/
@[stacks 0037, to_dual self (reorder := C D, 2 4, F G)]
/-
**CategoryTheory.Adjunction** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Adjunction (F : C ⥤ D) (G : D ⥤ C) where /-- The unit of an adjunction -/ 
unit : 𝟭 C ⟶ F.comp G /-- The counit of an adjunction -/ counit : G.comp F ⟶ 𝟭 D
 /-- Equality of the composition of the unit and counit with the identity `F ⟶ F
GF ⟶ F = 𝟙` -/ left_triangle_components (X : C) : dsimp% F.map (unit.app X) ≫ co
unit.app (F.obj X) = 𝟙 (F.obj X)
参数：F : C ⥤ D；G : D ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoin
t.

We use the unit-counit definition of an adjunction. There is a constructor `Adju
nction.mk'`
which constructs an adjunction from the data of a hom set equivalence, a unit, a
nd a counit,
together with proofs of the equalities `homEquiv_unit` and `homEquiv_counit` rel
ating them to each
other.

There is also a constructor `Adjunction.mkOfHomEquiv` which constructs an adjunc
tion from a natural
hom set equivalence.

To construct adjoints to a given functor, there are constructors `leftAdjointOfE
quiv` and
`adjunctionOfEquivLeft` (as well as their duals).
-/
structure Adjunction (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit and counit with the identity `F ⟶ FGF ⟶ F = 𝟙` -/
  left_triangle_components (X : C) :
    dsimp% F.map (unit.app X) ≫ counit.app (F.obj X) = 𝟙 (F.obj X) := by cat_disch
  /-- Equality of the composition of the unit and counit with the identity `G ⟶ GFG ⟶ G = 𝟙` -/
  right_triangle_components (Y : D) :
    dsimp% unit.app (G.obj Y) ≫ G.map (counit.app Y) = 𝟙 (G.obj Y) := by cat_disch

to_dual_name_hint Left Right

attribute [to_dual existing] Adjunction.unit Adjunction.left_triangle_components
attribute [to_dual self (reorder := C D, 2 4, F G,
  unit counit, left_triangle_components right_triangle_components)] Adjunction.mk
attribute [to_dual self (reorder := C D, 2 4, F G,
  mk (unit counit, left_triangle_components right_triangle_components))] Adjunction.casesOn

/-- The notation `F ⊣ G` stands for `Adjunction F G` representing that `F` is left adjoint to `G` -/
infixl:15 " ⊣ " => Adjunction

namespace Functor

/-- A class asserting the existence of a right adjoint. -/
/-
**CategoryTheory.Functor.IsLeftAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class asserting the existence of a right adjoint.
-/
class IsLeftAdjoint (left : C ⥤ D) : Prop where
  exists_rightAdjoint : ∃ (right : D ⥤ C), Nonempty (left ⊣ right)

/-- A class asserting the existence of a left adjoint. -/
@[to_dual]
/-
**CategoryTheory.Functor.IsRightAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 D C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class asserting the existence of a left adjoint.
-/
class IsRightAdjoint (right : D ⥤ C) : Prop where
  exists_leftAdjoint : ∃ (left : C ⥤ D), Nonempty (left ⊣ right)

/-- A chosen left adjoint to a functor that is a right adjoint. -/
@[to_dual /-- A chosen right adjoint to a functor that is a left adjoint. -/]
/-
**CategoryTheory.Functor.leftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D
参数：R : D ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsRightAdjoint.exists_leftAdjoint`：∀ {C : Type u₁
} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} D}   {right : CategoryT…

--- 原说明 ---
A chosen left adjoint to a functor that is a right adjoint.
-/
noncomputable def leftAdjoint (R : D ⥤ C) [IsRightAdjoint R] : C ⥤ D :=
  (IsRightAdjoint.exists_leftAdjoint (right := R)).choose

end Functor

/-- The adjunction associated to a functor known to be a left adjoint. -/
@[to_dual /-- The adjunction associated to a functor known to be a right adjoint. -/]
/-
**CategoryTheory.Adjunction.ofIsLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (left : 
CategoryTheory.Functor C D) → [inst_2 : left.IsLeftAdjoint] → left ⊣ left.rightA
djoint
参数：left : CategoryTheory.Functor C D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLeftAdjoint.exists_rightAdjoint`：∀ {C : Type u₁
} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTh
eory.Category.{v₂, u₂} D}   {left : CategoryTh…

--- 原说明 ---
The adjunction associated to a functor known to be a left adjoint.
-/
noncomputable def Adjunction.ofIsLeftAdjoint (left : C ⥤ D) [left.IsLeftAdjoint] :
    left ⊣ left.rightAdjoint :=
  IsLeftAdjoint.exists_rightAdjoint.choose_spec.some

namespace Adjunction

attribute [reassoc (attr := simp)] left_triangle_components right_triangle_components

/-- The hom set equivalence associated to an adjunction. -/
/-
**CategoryTheory.Adjunction.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
djunction`。
形式化陈述：homEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D) : (F.obj X 
⟶ Y) ≃ (X ⟶ G.obj Y) where toFun
参数：adj : F ⊣ G；X : C；Y : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The hom set equivalence associated to an adjunction.
-/
def homEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) where
  toFun := fun f => adj.unit.app X ≫ G.map f
  invFun := fun g => F.map g ≫ adj.counit.app Y
  left_inv := fun f => by
    dsimp
    rw [F.map_comp, assoc, ← Functor.comp_map, adj.counit.naturality, ← assoc]
    simp
  right_inv := fun g => by
    simp only [Functor.comp_obj, Functor.map_comp]
    rw [← assoc, ← Functor.comp_map, ← adj.unit.naturality]
    simp

/-- `homEquiv'` is the dual of `homEquiv`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing homEquiv]
/-
**CategoryTheory.Adjunction.homEquiv'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Adjunction`。
形式化陈述：homEquiv' {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) (X : C) (Y : D) : (Y ⟶ F.o
bj X) ≃ (G.obj Y ⟶ X)
参数：adj : G ⊣ F；X : C；Y : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`homEquiv'` is the dual of `homEquiv`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev homEquiv' {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) (X : C) (Y : D) :
    (Y ⟶ F.obj X) ≃ (G.obj Y ⟶ X) := (homEquiv adj Y X).symm

attribute [simps (attr := to_dual none) -isSimp] homEquiv

@[to_dual none] alias homEquiv_unit := homEquiv_apply
@[to_dual none] alias homEquiv_counit := homEquiv_symm_apply

-- These lemmas are not global simp lemmas because certain adjunctions
-- are constructed using `Adjunction.mkOfHomEquiv`, and we certainly
-- do not want `dsimp` to apply `homEquiv_unit` or `homEquiv_counit`
-- in that case. However, when proving general API results about adjunctions,
-- it may be advisable to add a local simp attribute to these lemmas.
attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

set_option linter.existingAttributeWarning false in
@[ext, to_dual ext_counit]
/-
**CategoryTheory.Adjunction.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunc
tion`。
形式化陈述：ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F ⊣ G} (h : adj.unit = adj'.unit) 
: adj = adj'
参数：h : adj.unit = adj'.unit。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F ⊣ G}
    (h : adj.unit = adj'.unit) : adj = adj' := by
  suffices h' : adj.counit = adj'.counit by cases adj; cases adj'; aesop
  ext X
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.right_triangle_components, h, Adjunction.right_triangle_components]

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

@[to_dual]
/-
**CategoryTheory.Adjunction.isLeftAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：isLeftAdjoint (adj : F ⊣ G) : F.IsLeftAdjoint
参数：adj : F ⊣ G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLeftAdjoint (adj : F ⊣ G) : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

@[to_dual]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : D ⥤ C) [R.IsRightAdjoint] : R.leftAdjoint.IsLeftAdjoint :=
  (ofIsRightAdjoint R).isLeftAdjoint

variable {X' X : C} {Y Y' : D}

set_option backward.defeqAttrib.useBackward true in
@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Adjunction`。
形式化陈述：homEquiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.unit.app X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_id (X : C) : adj.homEquiv X _ (𝟙 _) = adj.unit.app X := by simp

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_symm_id** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Adjunction`。
形式化陈述：homEquiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app 
X
参数：X : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_symm_id (X : D) : (adj.homEquiv _ X).symm (𝟙 _) = adj.counit.app X := by simp

@[simp, to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_symm_unit** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Adjunction`。
形式化陈述：homEquiv_symm_unit (X : C) : dsimp% (adj.homEquiv _ _).symm (adj.unit.app 
X) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_symm_unit (X : C) : dsimp% (adj.homEquiv _ _).symm (adj.unit.app X) = 𝟙 _ := by
  simp

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_left_symm** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) : (adj.homEqu
iv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g
参数：f : X' ⟶ X；g : X ⟶ G.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
    (adj.homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.homEquiv X Y).symm g := by
  simp

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_left** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X'
 Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g
参数：f : X' ⟶ X；g : F.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`：homEquiv_natura
lity_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) : (adj.homEquiv X' Y).symm (f ≫ g)
 = F.map f ≫ (adj.homEquiv X Y).symm g
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]
  simp only [Equiv.symm_apply_apply, homEquiv_naturality_left_symm]

set_option backward.defeqAttrib.useBackward true in
@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_right** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X
 Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g
参数：f : F.obj X ⟶ Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y') (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g := by
  simp

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_right_symm** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') : (adj.homEq
uiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g
参数：f : X ⟶ G.obj Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right`：homEquiv_naturality
_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X Y') (f ≫ g) = (adj.homEq
uiv X Y) f ≫ G.map g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]
  simp only [homEquiv_naturality_right, Equiv.apply_symm_apply]

@[to_dual none, reassoc]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_left_square** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y') (h : F.obj
 X' ⟶ Y) (k : Y ⟶ Y') (w : F.map f ≫ g = h ≫ k) : f ≫ (adj.homEquiv X Y') g = (a
dj.homEquiv X' Y) h ≫ G.map k
参数：f : X' ⟶ X；g : F.obj X ⟶ Y'；h : F.obj X' ⟶ Y；k : Y ⟶ Y'；w : F.map f ≫ g = h ≫
 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right`：homEquiv_naturality
_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X Y') (f ≫ g) = (adj.homEq
uiv X Y) f ≫ G.map g
-/
theorem homEquiv_naturality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') (w : F.map f ≫ g = h ≫ k) :
    f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k := by
  rw [← homEquiv_naturality_left, ← homEquiv_naturality_right, w]

@[to_dual none, reassoc]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_right_square** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y') (h : X' ⟶
 G.obj Y) (k : Y ⟶ Y') (w : f ≫ g = h ≫ G.map k) : F.map f ≫ (adj.homEquiv X Y')
.symm g = (adj.homEquiv X' Y).symm h ≫ k
参数：f : X' ⟶ X；g : X ⟶ G.obj Y'；h : X' ⟶ G.obj Y；k : Y ⟶ Y'；w : f ≫ g = h ≫ G.map
 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`：homEquiv_natura
lity_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) : (adj.homEquiv X' Y).symm (f ≫ g)
 = F.map f ≫ (adj.homEquiv X Y).symm g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right_symm`：homEquiv_natur
ality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') : (adj.homEquiv X Y').symm (f ≫ 
G.map g) = (adj.homEquiv X Y).symm f ≫ g
-/
theorem homEquiv_naturality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') (w : f ≫ g = h ≫ G.map k) :
    F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k := by
  rw [← homEquiv_naturality_left_symm, ← homEquiv_naturality_right_symm, w]

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_left_square_iff** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_left_square_iff (f : X' ⟶ X) (g : F.obj X ⟶ Y') (h : F
.obj X' ⟶ Y) (k : Y ⟶ Y') : (f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫
 G.map k) ↔ (F.map f ≫ g = h ≫ k)
参数：f : X' ⟶ X；g : F.obj X ⟶ Y'；h : F.obj X' ⟶ Y；k : Y ⟶ Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right_square`：homEquiv_nat
urality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y') (h : X' ⟶ G.obj Y) (k : Y ⟶
 Y') (w : f ≫ g = h ≫ G.map k) : F.map f ≫ (adj.…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_square`：homEquiv_natu
rality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y') (h : F.obj X' ⟶ Y) (k : Y ⟶ Y
') (w : F.map f ≫ g = h ≫ k) : f ≫ (adj.homEqui…
-/
theorem homEquiv_naturality_left_square_iff (f : X' ⟶ X) (g : F.obj X ⟶ Y')
    (h : F.obj X' ⟶ Y) (k : Y ⟶ Y') :
    (f ≫ (adj.homEquiv X Y') g = (adj.homEquiv X' Y) h ≫ G.map k) ↔
      (F.map f ≫ g = h ≫ k) :=
  ⟨fun w ↦ by simpa only [Equiv.symm_apply_apply]
      using homEquiv_naturality_right_square adj _ _ _ _ w,
    homEquiv_naturality_left_square adj f g h k⟩

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_naturality_right_square_iff** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_naturality_right_square_iff (f : X' ⟶ X) (g : X ⟶ G.obj Y') (h : 
X' ⟶ G.obj Y) (k : Y ⟶ Y') : (F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEqu
iv X' Y).symm h ≫ k) ↔ (f ≫ g = h ≫ G.map k)
参数：f : X' ⟶ X；g : X ⟶ G.obj Y'；h : X' ⟶ G.obj Y；k : Y ⟶ Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_square`：homEquiv_natu
rality_left_square (f : X' ⟶ X) (g : F.obj X ⟶ Y') (h : F.obj X' ⟶ Y) (k : Y ⟶ Y
') (w : F.map f ≫ g = h ≫ k) : f ≫ (adj.homEqui…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right_square`：homEquiv_nat
urality_right_square (f : X' ⟶ X) (g : X ⟶ G.obj Y') (h : X' ⟶ G.obj Y) (k : Y ⟶
 Y') (w : f ≫ g = h ≫ G.map k) : F.map f ≫ (adj.…
-/
theorem homEquiv_naturality_right_square_iff (f : X' ⟶ X) (g : X ⟶ G.obj Y')
    (h : X' ⟶ G.obj Y) (k : Y ⟶ Y') :
    (F.map f ≫ (adj.homEquiv X Y').symm g = (adj.homEquiv X' Y).symm h ≫ k) ↔
      (f ≫ g = h ≫ G.map k) :=
  ⟨fun w ↦ by simpa only [Equiv.apply_symm_apply]
      using homEquiv_naturality_left_square adj _ _ _ _ w,
    homEquiv_naturality_right_square adj f g h k⟩

@[simp, to_dual none]
/-
**CategoryTheory.Adjunction.left_triangle** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：left_triangle : whiskerRight adj.unit F ≫ (Functor.associator ..).hom ≫ wh
iskerLeft F adj.counit = F.leftUnitor.hom ≫ F.rightUnitor.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem left_triangle :
    whiskerRight adj.unit F ≫ (Functor.associator ..).hom ≫ whiskerLeft F adj.counit =
    F.leftUnitor.hom ≫ F.rightUnitor.inv := by
  ext; simp

@[simp, to_dual none]
/-
**CategoryTheory.Adjunction.right_triangle** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：right_triangle : whiskerLeft G adj.unit ≫ (Functor.associator ..).inv ≫ wh
iskerRight adj.counit G = G.rightUnitor.hom ≫ G.leftUnitor.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem right_triangle :
    whiskerLeft G adj.unit ≫ (Functor.associator ..).inv ≫ whiskerRight adj.counit G =
    G.rightUnitor.hom ≫ G.leftUnitor.inv := by
  ext; simp

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.Adjunction.unit_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：unit_naturality {X Y : C} (f : X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.m
ap f) = f ≫ adj.unit.app Y
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem unit_naturality {X Y : C} (f : X ⟶ Y) :
    dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y :=
  (adj.unit.naturality f).symm

@[to_dual none]
/-
**CategoryTheory.Adjunction.unit_comp_map_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：unit_comp_map_eq_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
 dsimp% adj.unit.app A ≫ G.map f = g ↔ f = F.map g ≫ adj.counit.app B
参数：f : F.obj A ⟶ B；g : A ⟶ G.obj B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma unit_comp_map_eq_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    dsimp% adj.unit.app A ≫ G.map f = g ↔ f = F.map g ≫ adj.counit.app B :=
  ⟨fun h => by simp [← h], fun h => by simp [h]⟩

@[to_dual none]
/-
**CategoryTheory.Adjunction.eq_unit_comp_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：eq_unit_comp_map_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
 dsimp% g = adj.unit.app A ≫ G.map f ↔ F.map g ≫ adj.counit.app B = f
参数：f : F.obj A ⟶ B；g : A ⟶ G.obj B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma eq_unit_comp_map_iff {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    dsimp% g = adj.unit.app A ≫ G.map f ↔ F.map g ≫ adj.counit.app B = f :=
  ⟨fun h => by simp [h], fun h => by simp [← h]⟩

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Adjunction`。
形式化陈述：homEquiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : ad
j.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g
参数：f : F.obj A ⟶ B；g : A ⟶ G.obj B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.unit_comp_map_eq_iff`：unit_comp_map_eq_iff {A 
: C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : dsimp% adj.unit.app A ≫ G.map
 f = g ↔ f = F.map g ≫ adj.counit.ap…
-/
theorem homEquiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    adj.homEquiv A B f = g ↔ f = (adj.homEquiv A B).symm g :=
  unit_comp_map_eq_iff adj f g

@[to_dual none]
/-
**CategoryTheory.Adjunction.eq_homEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Adjunction`。
形式化陈述：eq_homEquiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : g 
= adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f
参数：f : F.obj A ⟶ B；g : A ⟶ G.obj B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.eq_unit_comp_map_iff`：eq_unit_comp_map_iff {A 
: C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) : dsimp% g = adj.unit.app A ≫ G
.map f ↔ F.map g ≫ adj.counit.app B …
-/
theorem eq_homEquiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
    g = adj.homEquiv A B f ↔ (adj.homEquiv A B).symm g = f :=
  eq_unit_comp_map_iff adj f g

/-- If `adj : F ⊣ G`, and `X : C`, then `F.obj X` corepresents `Y ↦ (X ⟶ G.obj Y)`. -/
@[simps]
/-
**CategoryTheory.Adjunction.corepresentableBy** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Adjunction`。
形式化陈述：corepresentableBy (X : C) : (G ⋙ coyoneda.obj (Opposite.op X)).Corepresent
ableBy (F.obj X) where homEquiv
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `adj : F ⊣ G`, and `X : C`, then `F.obj X` corepresents `Y ↦ (X ⟶ G.obj Y)`.
-/
def corepresentableBy (X : C) :
    (G ⋙ coyoneda.obj (Opposite.op X)).CorepresentableBy (F.obj X) where
  homEquiv := adj.homEquiv _ _
  homEquiv_comp := by simp

/-- If `adj : F ⊣ G`, and `Y : D`, then `G.obj Y` represents `X ↦ (F.obj X ⟶ Y)`. -/
@[simps]
/-
**CategoryTheory.Adjunction.representableBy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：representableBy (Y : D) : (F.op ⋙ yoneda.obj Y).RepresentableBy (G.obj Y) 
where homEquiv
参数：Y : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `adj : F ⊣ G`, and `Y : D`, then `G.obj Y` represents `X ↦ (F.obj X ⟶ Y)`.
-/
def representableBy (Y : D) :
    (F.op ⋙ yoneda.obj Y).RepresentableBy (G.obj Y) where
  homEquiv := (adj.homEquiv _ _).symm
  homEquiv_comp := by simp

end

/--
This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mk'`. This structure won't typically be used anywhere else.
-/
/-
**CategoryTheory.Adjunction.CoreHomEquivUnitCounit** 是 Mathlib 中的一个结构，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：CoreHomEquivUnitCounit (F : C ⥤ D) (G : D ⥤ C) where /-- The equivalence b
etween `Hom (F X) Y` and `Hom X (G Y)` coming from an adjunction -/ homEquiv : f
orall X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) /-- The unit of an adjunction -/ unit :
 𝟭 C ⟶ F ⋙ G /-- The counit of an adjunction -/ counit : G ⋙ F ⟶ 𝟭 D /-- The rel
ationship between the unit and hom set equivalence of an adjunction -/ homEquiv_
unit : forall {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f
参数：F : C ⥤ D；G : D ⥤ C；F X；G Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mk'`. This structure won't typically be used anywhere else.
-/
structure CoreHomEquivUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` coming from an adjunction -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The unit of an adjunction -/
  unit : 𝟭 C ⟶ F ⋙ G
  /-- The counit of an adjunction -/
  counit : G ⋙ F ⟶ 𝟭 D
  /-- The relationship between the unit and hom set equivalence of an adjunction -/
  homEquiv_unit : ∀ {X Y f}, (homEquiv X Y) f = unit.app X ≫ G.map f := by cat_disch
  /-- The relationship between the counit and hom set equivalence of an adjunction -/
  homEquiv_counit : ∀ {X Y g}, (homEquiv X Y).symm g = F.map g ≫ counit.app Y := by cat_disch

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfHomEquiv`.
This structure won't typically be used anywhere else.
-/
/-
**CategoryTheory.Adjunction.CoreHomEquiv** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where /-- The equivalence between `Ho
m (F X) Y` and `Hom X (G Y)` -/ homEquiv : forall X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.ob
j Y) /-- The property that describes how `homEquiv.symm` transforms compositions
 `X' ⟶ X ⟶ G Y` -/ homEquiv_naturality_left_symm : forall {X' X Y} (f : X' ⟶ X) 
(g : X ⟶ G.obj Y), (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm 
g
参数：F : C ⥤ D；G : D ⥤ C；F X；G Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfHomEquiv`.
This structure won't typically be used anywhere else.
-/
structure CoreHomEquiv (F : C ⥤ D) (G : D ⥤ C) where
  /-- The equivalence between `Hom (F X) Y` and `Hom X (G Y)` -/
  homEquiv : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y)
  /-- The property that describes how `homEquiv.symm` transforms compositions `X' ⟶ X ⟶ G Y` -/
  homEquiv_naturality_left_symm :
    ∀ {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
      (homEquiv X' Y).symm (f ≫ g) = F.map f ≫ (homEquiv X Y).symm g := by
    cat_disch
  /-- The property that describes how `homEquiv` transforms compositions `F X ⟶ Y ⟶ Y'` -/
  homEquiv_naturality_right :
    ∀ {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
      (homEquiv X Y') (f ≫ g) = (homEquiv X Y) f ≫ G.map g := by
    cat_disch

namespace CoreHomEquiv

attribute [simp] homEquiv_naturality_left_symm homEquiv_naturality_right

variable {F : C ⥤ D} {G : D ⥤ C} (adj : CoreHomEquiv F G) {X' X : C} {Y Y' : D}

/-
**CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_left** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Adjunction.CoreHomEquiv`。
形式化陈述：homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X'
 Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g
参数：f : X' ⟶ X；g : F.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_left_symm`：∀ 
{C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 
: CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
    (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (adj.homEquiv X Y) g := by
  rw [← Equiv.eq_symm_apply]; simp
/-
**CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_right_symm** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Adjunction.CoreHomEquiv`。
形式化陈述：homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') : (adj.homEq
uiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g
参数：f : X ⟶ G.obj Y；g : Y ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_right`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homEquiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
    (adj.homEquiv X Y').symm (f ≫ G.map g) = (adj.homEquiv X Y).symm f ≫ g := by
  rw [Equiv.symm_apply_eq]; simp

end CoreHomEquiv

/-- This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfUnitCounit`.
This structure won't typically be used anywhere else.
-/
/-
**CategoryTheory.Adjunction.CoreUnitCounit** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where /-- The unit of an adjunction
 between `F` and `G` -/ unit : 𝟭 C ⟶ F.comp G /-- The counit of an adjunction be
tween `F` and `G` -/ counit : G.comp F ⟶ 𝟭 D /-- Equality of the composition of 
the unit, associator, and counit with the identity `F ⟶ (F G) F ⟶ F (G F) ⟶ F = 
NatTrans.id F` -/ left_triangle : whiskerRight unit F ≫ (associator F G F).hom ≫
 whiskerLeft F counit = NatTrans.id (𝟭 C ⋙ F)
参数：F : C ⥤ D；G : D ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an auxiliary data structure useful for constructing adjunctions.
See `Adjunction.mkOfUnitCounit`.
This structure won't typically be used anywhere else.
-/
structure CoreUnitCounit (F : C ⥤ D) (G : D ⥤ C) where
  /-- The unit of an adjunction between `F` and `G` -/
  unit : 𝟭 C ⟶ F.comp G
  /-- The counit of an adjunction between `F` and `G` -/
  counit : G.comp F ⟶ 𝟭 D
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `F ⟶ (F G) F ⟶ F (G F) ⟶ F = NatTrans.id F` -/
  left_triangle :
    whiskerRight unit F ≫ (associator F G F).hom ≫ whiskerLeft F counit =
      NatTrans.id (𝟭 C ⋙ F) := by
    cat_disch
  /-- Equality of the composition of the unit, associator, and counit with the identity
  `G ⟶ G (F G) ⟶ (F G) F ⟶ G = NatTrans.id G` -/
  right_triangle :
    whiskerLeft G unit ≫ (associator G F G).inv ≫ whiskerRight counit G =
      NatTrans.id (G ⋙ 𝟭 C) := by
    cat_disch

namespace CoreUnitCounit

attribute [simp] left_triangle right_triangle

end CoreUnitCounit

variable {F : C ⥤ D} {G : D ⥤ C}

attribute [local simp] CoreHomEquivUnitCounit.homEquiv_unit CoreHomEquivUnitCounit.homEquiv_counit

/--
Construct an adjunction from the data of a `CoreHomEquivUnitCounit`, i.e. a hom set
equivalence, unit and counit natural transformations together with proofs of the equalities
`homEquiv_unit` and `homEquiv_counit` relating them to each other.
-/
@[simps]
/-
**CategoryTheory.Adjunction.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adjunc
tion`。
形式化陈述：mk' (adj : CoreHomEquivUnitCounit F G) : F ⊣ G where unit
参数：adj : CoreHomEquivUnitCounit F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an adjunction from the data of a `CoreHomEquivUnitCounit`, i.e. a hom 
set
equivalence, unit and counit natural transformations together with proofs of the
 equalities
`homEquiv_unit` and `homEquiv_counit` relating them to each other.
-/
def mk' (adj : CoreHomEquivUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    rw [← adj.homEquiv_counit, (adj.homEquiv _ _).symm_apply_eq, adj.homEquiv_unit]
    simp
  right_triangle_components Y := by
    rw [← adj.homEquiv_unit, ← (adj.homEquiv _ _).eq_symm_apply, adj.homEquiv_counit]
    simp
/-
**CategoryTheory.Adjunction.mk'_homEquiv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 {G : CategoryTheory.Functor D C}   (adj : CategoryTheory.Adjunction.CoreHomEqui
vUnitCounit F G),   (CategoryTheory.Adjunction.mk' adj).homEquiv = adj.homEquiv
参数：adj : CategoryTheory.Adjunction.CoreHomEquivUnitCounit F G；CategoryTheory.Adj
unction.mk' adj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.CoreHomEquivUnitCounit.homEquiv_unit`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.mk'_unit`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F : CategoryTheor…
-/
lemma mk'_homEquiv (adj : CoreHomEquivUnitCounit F G) : (mk' adj).homEquiv = adj.homEquiv := by
  ext
  rw [homEquiv_unit, adj.homEquiv_unit, mk'_unit]

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps!]
/-
**CategoryTheory.Adjunction.mkOfHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G
参数：adj : CoreHomEquiv F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an adjunction between `F` and `G` out of a natural bijection between e
ach
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`.
-/
def mkOfHomEquiv (adj : CoreHomEquiv F G) : F ⊣ G :=
  mk' {
    unit :=
      { app := fun X => (adj.homEquiv X (F.obj X)) (𝟙 (F.obj X))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right] }
    counit :=
      { app := fun Y => (adj.homEquiv _ _).invFun (𝟙 (G.obj Y))
        naturality := by
          intros
          simp [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm] }
    homEquiv := adj.homEquiv
    homEquiv_unit := fun {X Y f} => by simp [← adj.homEquiv_naturality_right]
    homEquiv_counit := fun {X Y f} => by simp [← adj.homEquiv_naturality_left_symm] }

@[simp]
/-
**CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：mkOfHomEquiv_homEquiv (adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEqu
iv = adj.homEquiv
参数：adj : CoreHomEquiv F G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.mk'_unit`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.CoreHomEquiv.homEquiv_naturality_right`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mkOfHomEquiv_homEquiv (adj : CoreHomEquiv F G) :
    (mkOfHomEquiv adj).homEquiv = adj.homEquiv := by
  ext X Y g
  simp [mkOfHomEquiv, ← adj.homEquiv_naturality_right (𝟙 _) g]

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simps!]
/-
**CategoryTheory.Adjunction.mkOfUnitCounit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G where unit
参数：adj : CoreUnitCounit F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an adjunction between functors `F` and `G` given a unit and counit for
 the adjunction
satisfying the triangle identities.
-/
def mkOfUnitCounit (adj : CoreUnitCounit F G) : F ⊣ G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := adj.left_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.left_triangle] using this X
  right_triangle_components Y := by
    have := adj.right_triangle
    rw [NatTrans.ext_iff, funext_iff] at this
    simpa [-CoreUnitCounit.right_triangle] using this Y

/-- The adjunction between the identity functor on a category and itself. -/
@[simps]
/-
**CategoryTheory.Adjunction.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adjunct
ion`。
形式化陈述：id : 𝟭 C ⊣ 𝟭 C where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the identity functor on a category and itself.
-/
def id : 𝟭 C ⊣ 𝟭 C where
  unit := 𝟙 _
  counit := 𝟙 _

-- Satisfy the inhabited linter.
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Adjunction (𝟭 C) (𝟭 C)) :=
  ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[to_dual (attr := simps)
/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/]
/-
**CategoryTheory.Adjunction.equivHomsetLeftOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} : (F
.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where toFun f
参数：iso : F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivHomsetLeftOfNatIso {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} :
    (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) where
  toFun f := iso.inv.app _ ≫ f
  invFun g := iso.hom.app _ ≫ g
  left_inv f := by simp
  right_inv g := by simp

set_option linter.translate.warnInvalid false in
/-- Transport an adjunction along a natural isomorphism on the left. -/
@[to_dual (attr := simps)
/-- Transport an adjunction along a natural isomorphism on the right. -/]
/-
**CategoryTheory.Adjunction.ofNatIsoLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H
 where unit
参数：adj : F ⊣ H；iso : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofNatIsoLeft {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H where
  unit := adj.unit ≫ Functor.whiskerRight iso.hom _
  counit := Functor.whiskerLeft _ iso.inv ≫ adj.counit
  left_triangle_components X := by
    simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.map_comp, Functor.whiskerLeft_app, Category.assoc, NatTrans.naturality_assoc]
    simp [← Functor.comp_map]
  right_triangle_components := by simp [← Functor.map_comp]

attribute [to_dual existing] ofNatIsoLeft_unit ofNatIsoLeft_counit

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_apply** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_ofNatIsoLeft_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso :
 F ≅ G) {X : C} {Y : D} (f : G.obj X ⟶ Y) : (ofNatIsoLeft adj iso).homEquiv X Y 
f = adj.homEquiv _ _ (iso.hom.app _ ≫ f)
参数：adj : F ⊣ H；iso : F ≅ G；f : G.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.ofNatIsoLeft_unit`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_ofNatIsoLeft_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
    {X : C} {Y : D} (f : G.obj X ⟶ Y) :
    (ofNatIsoLeft adj iso).homEquiv X Y f = adj.homEquiv _ _ (iso.hom.app _ ≫ f) := by
  simp

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_symm_apply** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_ofNatIsoLeft_symm_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (
iso : F ≅ G) {X : C} {Y : D} (f : X ⟶ H.obj Y) : ((ofNatIsoLeft adj iso).homEqui
v X Y).symm f = iso.inv.app _ ≫ (adj.homEquiv _ _).symm f
参数：adj : F ⊣ H；iso : F ≅ G；f : X ⟶ H.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.ofNatIsoLeft_counit`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_ofNatIsoLeft_symm_apply {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G)
    {X : C} {Y : D} (f : X ⟶ H.obj Y) :
    ((ofNatIsoLeft adj iso).homEquiv X Y).symm f = iso.inv.app _ ≫ (adj.homEquiv _ _).symm f := by
  simp

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_ofNatIsoRight_apply {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso 
: G ≅ H) {X : C} {Y : D} (f : F.obj X ⟶ Y) : (ofNatIsoRight adj iso).homEquiv X 
Y f = adj.homEquiv _ _ f ≫ iso.hom.app _
参数：adj : F ⊣ G；iso : G ≅ H；f : F.obj X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.ofNatIsoRight_unit`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_ofNatIsoRight_apply {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
    {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    (ofNatIsoRight adj iso).homEquiv X Y f = adj.homEquiv _ _ f ≫ iso.hom.app _ := by
  simp

@[to_dual none]
/-
**CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_symm_apply** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：homEquiv_ofNatIsoRight_symm_apply {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) 
(iso : G ≅ H) {X : C} {Y : D} (f : X ⟶ H.obj Y) : ((ofNatIsoRight adj iso).homEq
uiv X Y).symm f = (adj.homEquiv _ _).symm (f ≫ iso.inv.app _)
参数：adj : F ⊣ G；iso : G ≅ H；f : X ⟶ H.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Adjunction.ofNatIsoRight_counit`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_ofNatIsoRight_symm_apply {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H)
    {X : C} {Y : D} (f : X ⟶ H.obj Y) :
    ((ofNatIsoRight adj iso).homEquiv X Y).symm f =
      (adj.homEquiv _ _).symm (f ≫ iso.inv.app _) := by
  simp

/-- The isomorphism which an adjunction `F ⊣ G` induces on `G ⋙ yoneda`. This states that
`Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
/-
**CategoryTheory.Adjunction.compYonedaIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：compYonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁}
 D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : G ⋙ yoneda ≅ yoneda ⋙ (whiskeringLef
t _ _ _).obj F.op
参数：adj : F ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism which an adjunction `F ⊣ G` induces on `G ⋙ yoneda`. This states
 that
`Adjunction.homEquiv` is natural in both arguments.
-/
def compYonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    G ⋙ yoneda ≅ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv Y.unop X).toIso.symm

/-- The isomorphism which an adjunction `F ⊣ G` induces on `F.op ⋙ coyoneda`. This states that
`Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
/-
**CategoryTheory.Adjunction.compCoyonedaIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：compCoyonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v
₁} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : F.op ⋙ coyoneda ≅ coyoneda ⋙ (whis
keringLeft _ _ _).obj G
参数：adj : F ⊣ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism which an adjunction `F ⊣ G` induces on `F.op ⋙ coyoneda`. This s
tates that
`Adjunction.homEquiv` is natural in both arguments.
-/
def compCoyonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    F.op ⋙ coyoneda ≅ coyoneda ⋙ (whiskeringLeft _ _ _).obj G :=
  NatIso.ofComponents fun X => NatIso.ofComponents fun Y => (adj.homEquiv X.unop Y).toIso

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism which an adjunction `F ⊣ G` induces on `F.op ⋙ uliftCoyoneda`.
This states that `Adjunction.homEquiv` is natural in both arguments. -/
@[simps!]
/-
**CategoryTheory.Adjunction.compUliftCoyonedaIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：compUliftCoyonedaIso (adj : F ⊣ G) : F.op ⋙ uliftCoyoneda.{max w v₁} ≅ uli
ftCoyoneda.{max w v₂} ⋙ (whiskeringLeft _ _ _).obj G
参数：adj : F ⊣ G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The isomorphism which an adjunction `F ⊣ G` induces on `F.op ⋙ uliftCoyoneda`.
This states that `Adjunction.homEquiv` is natural in both arguments.
-/
def compUliftCoyonedaIso (adj : F ⊣ G) :
    F.op ⋙ uliftCoyoneda.{max w v₁} ≅
      uliftCoyoneda.{max w v₂} ⋙ (whiskeringLeft _ _ _).obj G :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans
      ((adj.homEquiv X.unop Y).trans Equiv.ulift.symm)).toIso))

section

variable {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
  (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)

/-- Composition of adjunctions. -/
@[to_dual self (reorder := C E, 2 6, F I, G H, adj₁ adj₂), simps! -isSimp unit counit, stacks 0DV0]
/-
**CategoryTheory.Adjunction.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Adjun
ction`。
形式化陈述：comp : F ⋙ H ⊣ I ⋙ G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of adjunctions.
-/
def comp : F ⋙ H ⊣ I ⋙ G :=
  mk' {
    homEquiv := fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _)
    unit := adj₁.unit ≫ whiskerRight (F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit ≫
      (associator _ _ _).inv) G ≫ (associator _ _ _).hom
    counit := (associator _ _ _).inv ≫ whiskerRight ((associator _ _ _).hom ≫
      whiskerLeft _ adj₁.counit ≫ I.rightUnitor.hom) _ ≫ adj₂.counit }
/-
**CategoryTheory.Adjunction.comp_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：comp_unit_app (X : C) : dsimp% (adj₁.comp adj₂).unit.app X = adj₁.unit.app
 X ≫ G.map (adj₂.unit.app (F.obj X))
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Adjunction.CoreHomEquivUnitCounit.mk.congr_simp`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.mk'_unit`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F : CategoryTheor…
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
lemma comp_unit_app (X : C) : dsimp%
    (adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) := by
  simp [Adjunction.comp]

@[to_dual existing (attr := simp, reassoc)]
/-
**CategoryTheory.Adjunction.comp_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：comp_counit_app (X : E) : dsimp% (adj₁.comp adj₂).counit.app X = H.map (ad
j₁.counit.app (I.obj X)) ≫ adj₂.counit.app X
参数：X : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Adjunction.CoreHomEquivUnitCounit.mk.congr_simp`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.mk'_counit`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_counit_app (X : E) : dsimp%
    (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.counit.app X := by
  simp [Adjunction.comp]
/-
**CategoryTheory.Adjunction.comp_homEquiv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：comp_homEquiv : (adj₁.comp adj₂).homEquiv = fun _ _ => Equiv.trans (adj₂.h
omEquiv _ _) (adj₁.homEquiv _ _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.mk'_homEquiv`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {F : CategoryTheor…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
lemma comp_homEquiv : (adj₁.comp adj₂).homEquiv =
    fun _ _ ↦ Equiv.trans (adj₂.homEquiv _ _) (adj₁.homEquiv _ _) :=
  mk'_homEquiv _

end

section ConstructLeft

-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variable {F_obj : C → D}
variable (e : ∀ X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `rightAdjointOfEquiv`. -/
@[implicit_reducible, simps!]
/-
**CategoryTheory.Adjunction.leftAdjointOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Adjunction`。
形式化陈述：leftAdjointOfEquiv (he : forall X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.m
ap g) : C ⥤ D where obj
参数：he : forall X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Construct a left adjoint functor to `G`, given the functor's value on objects `F
_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality 
law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `rightAdjointOfEquiv`.
-/
def leftAdjointOfEquiv (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g) : C ⥤ D where
  obj := F_obj
  map {X} {X'} f := (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _))
  map_comp := fun f f' => by
    rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]
    conv =>
      rhs
      rw [assoc, ← he, id_comp, Equiv.apply_symm_apply]
    simp

variable (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)

/-- Show that the functor given by `leftAdjointOfEquiv` is indeed left adjoint to `G`. Dual
to `adjunctionOfEquivRight`. -/
@[simps!]
/-
**CategoryTheory.Adjunction.adjunctionOfEquivLeft** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that the functor given by `leftAdjointOfEquiv` is indeed left adjoint to `G
`. Dual
to `adjunctionOfEquivRight`.
-/
def adjunctionOfEquivLeft : leftAdjointOfEquiv e he ⊣ G :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := fun {X'} {X} {Y} f g => by
        have {X : C} {Y Y' : D} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
            (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g := by
          rw [Equiv.symm_apply_eq, he]; simp
        simp [← this, ← he] }

end ConstructLeft

section ConstructRight

-- Construction of a right adjoint, analogous to the above.
variable {G_obj : D → C}
variable (e : ∀ X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))

/-
**CategoryTheory.Adjunction.he''** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Adjun
ction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem he'' (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
    {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) := by
  rw [Equiv.eq_symm_apply, he]; simp

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `leftAdjointOfEquiv`. -/
@[implicit_reducible, simps!]
/-
**CategoryTheory.Adjunction.rightAdjointOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Adjunction`。
形式化陈述：rightAdjointOfEquiv (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e 
X Y g) : D ⥤ C where obj
参数：he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Construct a right adjoint functor to `F`, given the functor's value on objects `
G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality 
law
`he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `leftAdjointOfEquiv`.
-/
def rightAdjointOfEquiv (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) : D ⥤ C where
  obj := G_obj
  map {Y} {Y'} g := (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g)
  map_comp := fun {Y} {Y'} {Y''} g g' => by
    rw [← Equiv.eq_symm_apply, ← he'' e he, Equiv.symm_apply_apply]
    conv =>
      rhs
      rw [← assoc, he'' e he, comp_id, Equiv.symm_apply_apply]
    simp

/-- Show that the functor given by `rightAdjointOfEquiv` is indeed right adjoint to `F`. Dual
to `adjunctionOfEquivLeft`. -/
@[simps!]
/-
**CategoryTheory.Adjunction.adjunctionOfEquivRight** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：adjunctionOfEquivRight (he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫
 e X Y g) : F ⊣ (rightAdjointOfEquiv e he)
参数：he : forall X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that the functor given by `rightAdjointOfEquiv` is indeed right adjoint to 
`F`. Dual
to `adjunctionOfEquivLeft`.
-/
def adjunctionOfEquivRight (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g) :
    F ⊣ (rightAdjointOfEquiv e he) :=
  mkOfHomEquiv
    { homEquiv := e
      homEquiv_naturality_left_symm := by
        intro X X' Y f g; rw [Equiv.symm_apply_eq]; simp [he]
      homEquiv_naturality_right := by
        intro X Y Y' g h
        simp [← he, reassoc_of% (he'' e)] }

end ConstructRight

/--
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps!]
/-
**CategoryTheory.Adjunction.toEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Adjunction`。
形式化陈述：toEquivalence (adj : F ⊣ G) [forall X, IsIso (adj.unit.app X)] [forall Y, 
IsIso (adj.counit.app Y)] : C ≌ D where functor
参数：adj : F ⊣ G；adj.unit.app X；adj.counit.app Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then 
we can upgrade the
adjunction to an equivalence.
-/
noncomputable def toEquivalence (adj : F ⊣ G) [∀ X, IsIso (adj.unit.app X)]
    [∀ Y, IsIso (adj.counit.app Y)] : C ≌ D where
  functor := F
  inverse := G
  unitIso := NatIso.ofComponents fun X => asIso (adj.unit.app X)
  counitIso := NatIso.ofComponents fun Y => asIso (adj.counit.app Y)
/-
**CategoryTheory.Adjunction.map_comp_bijective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：map_comp_bijective_iff (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D) : Funct
ion.Bijective (fun (g : F.obj Y ⟶ Z) => F.map f ≫ g) ↔ Function.Bijective (fun (
g : Y ⟶ G.obj Z) => f ≫ g)
参数：adj : F ⊣ G；f : X ⟶ Y；Z : D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp_bijective_iff (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D) :
    Function.Bijective (fun (g : F.obj Y ⟶ Z) ↦ F.map f ≫ g) ↔
      Function.Bijective (fun (g : Y ⟶ G.obj Z) ↦ f ≫ g) := by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective,
    ← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  ext g
  simp
/-
**CategoryTheory.Adjunction.comp_map_bijective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：comp_map_bijective_iff (adj : F ⊣ G) {X Y : D} (g : X ⟶ Y) (Z : C) : Funct
ion.Bijective (fun (f : Z ⟶ G.obj X) => f ≫ G.map g) ↔ Function.Bijective (fun (
f : F.obj Z ⟶ X) => f ≫ g)
参数：adj : F ⊣ G；g : X ⟶ Y；Z : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_map_bijective_iff (adj : F ⊣ G) {X Y : D} (g : X ⟶ Y) (Z : C) :
    Function.Bijective (fun (f : Z ⟶ G.obj X) ↦ f ≫ G.map g) ↔
      Function.Bijective (fun (f : F.obj Z ⟶ X) ↦ f ≫ g) := by
  rw [← Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective,
    ← Function.Bijective.of_comp_iff _ (adj.homEquiv _ _).symm.bijective]
  congr!
  simp

end Adjunction

open Adjunction

/--
If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
/-
**CategoryTheory.Functor.isEquivalence_of_isRightAdjoint** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 [inst_2 : G.IsRightAdjoint]   [∀ (X : D), CategoryTheory.IsIso ((CategoryTheory
.Adjunction.ofIsRightAdjoint G).unit.app X)]   [∀ (Y : C), CategoryTheory.IsIso 
((CategoryTheory.Adjunction.ofIsRightAdjoint G).counit.app Y)], G.IsEquivalence
参数：G : CategoryTheory.Functor C D；X : D；(CategoryTheory.Adjunction.ofIsRightAdjo
int G).unit.app X；Y : C；(CategoryTheory.Adjunction.ofIsRightAdjoint G).counit.ap
p Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…

--- 原说明 ---
If the unit and counit for the adjunction corresponding to a right adjoint funct
or are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
lemma Functor.isEquivalence_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G]
    [∀ X, IsIso ((Adjunction.ofIsRightAdjoint G).unit.app X)]
    [∀ Y, IsIso ((Adjunction.ofIsRightAdjoint G).counit.app Y)] : G.IsEquivalence :=
  (Adjunction.ofIsRightAdjoint G).toEquivalence.isEquivalence_inverse

namespace Equivalence

variable (e : C ≌ D)

/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.toAdjunction`.) -/
/-
**CategoryTheory.Equivalence.toAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Equivalence`。
形式化陈述：toAdjunction : e.functor ⊣ e.inverse where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction given by an equivalence of categories. (To obtain the opposite ad
junction,
simply use `e.symm.toAdjunction`.)
-/
def toAdjunction : e.functor ⊣ e.inverse where
  unit := e.unit
  counit := e.counit

/-- `toAdjunction'` is the dual of `ToAdjunction`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing toAdjunction]
/-
**CategoryTheory.Equivalence.toAdjunction'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：toAdjunction' : e.inverse ⊣ e.functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toAdjunction'` is the dual of `ToAdjunction`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev toAdjunction' : e.inverse ⊣ e.functor := e.symm.toAdjunction

attribute [simps (attr := to_dual none)] toAdjunction

@[to_dual]
/-
**CategoryTheory.Equivalence.isLeftAdjoint_functor** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Equivalence`。
形式化陈述：isLeftAdjoint_functor : e.functor.IsLeftAdjoint where exists_rightAdjoint
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLeftAdjoint_functor : e.functor.IsLeftAdjoint where
  exists_rightAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual]
/-
**CategoryTheory.Equivalence.isRightAdjoint_inverse** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Equivalence`。
形式化陈述：isRightAdjoint_inverse : e.inverse.IsRightAdjoint where exists_leftAdjoint
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRightAdjoint_inverse : e.inverse.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨e.toAdjunction⟩⟩

@[to_dual none]
/-
**CategoryTheory.Equivalence.refl_toAdjunction** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Equivalence`。
形式化陈述：refl_toAdjunction : (refl (C
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma refl_toAdjunction : (refl (C := C)).toAdjunction = Adjunction.id := rfl
/-
**CategoryTheory.Equivalence.trans_toAdjunction** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Equivalence`。
形式化陈述：trans_toAdjunction {E : Type*} [Category* E] (e' : D ≌ E) : (e.trans e').t
oAdjunction = e.toAdjunction.comp e'.toAdjunction
参数：e' : D ≌ E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trans_toAdjunction {E : Type*} [Category* E] (e' : D ≌ E) :
    (e.trans e').toAdjunction = e.toAdjunction.comp e'.toAdjunction := rfl

end Equivalence

namespace Functor

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
/-
**CategoryTheory.Functor.isLeftAdjoint_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：isLeftAdjoint_comp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
 [F.IsLeftAdjoint] [G.IsLeftAdjoint] : (F ⋙ G).IsLeftAdjoint where exists_rightA
djoint
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too.
-/
instance isLeftAdjoint_comp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] : (F ⋙ G).IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsLeftAdjoint F).comp (Adjunction.ofIsLeftAdjoint G)⟩⟩

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
/-
**CategoryTheory.Functor.isRightAdjoint_comp** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Functor`。
形式化陈述：isRightAdjoint_comp {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E
} [IsRightAdjoint F] [IsRightAdjoint G] : IsRightAdjoint (F ⋙ G) where exists_le
ftAdjoint
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too.
-/
instance isRightAdjoint_comp {E : Type u₃} [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
    [IsRightAdjoint F] [IsRightAdjoint G] : IsRightAdjoint (F ⋙ G) where
  exists_leftAdjoint :=
    ⟨_, ⟨(Adjunction.ofIsRightAdjoint G).comp (Adjunction.ofIsRightAdjoint F)⟩⟩

/-- Transport being a right adjoint along a natural isomorphism. -/
@[to_dual /-- Transport being a left adjoint along a natural isomorphism. -/]
/-
**CategoryTheory.Functor.isRightAdjoint_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：isRightAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] : IsRig
htAdjoint G where exists_leftAdjoint
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport being a right adjoint along a natural isomorphism.
-/
lemma isRightAdjoint_of_iso {F G : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] :
    IsRightAdjoint G where
  exists_leftAdjoint := ⟨_, ⟨(Adjunction.ofIsRightAdjoint F).ofNatIsoRight h⟩⟩

/-- An equivalence `E` is left adjoint to its inverse. -/
/-
**CategoryTheory.Functor.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv
参数：E : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `E` is left adjoint to its inverse.
-/
noncomputable def adjunction (E : C ⥤ D) [IsEquivalence E] : E ⊣ E.inv :=
  E.asEquivalence.toAdjunction

/-- If `F` is an equivalence, it's a left adjoint. -/
@[to_dual /-- If `F` is an equivalence, it's a right adjoint. -/]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is an equivalence, it's a left adjoint.
-/
instance (priority := 10) isLeftAdjoint_of_isEquivalence {F : C ⥤ D} [F.IsEquivalence] :
    IsLeftAdjoint F :=
  F.asEquivalence.isLeftAdjoint_functor
/-
**CategoryTheory.Functor.isLeftAdjoint_comp_iff_right** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：isLeftAdjoint_comp_iff_right {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (
G : D ⥤ E) [F.IsEquivalence] : (F ⋙ G).IsLeftAdjoint ↔ G.IsLeftAdjoint
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_iso`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma isLeftAdjoint_comp_iff_right {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsEquivalence] :
    (F ⋙ G).IsLeftAdjoint ↔ G.IsLeftAdjoint := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isLeftAdjoint_of_iso iso.symm
/-
**CategoryTheory.Functor.isRightAdjoint_comp_iff_right** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isRightAdjoint_comp_iff_right {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) 
(G : D ⥤ E) [F.IsEquivalence] : (F ⋙ G).IsRightAdjoint ↔ G.IsRightAdjoint
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isRightAdjoint_of_iso`：isRightAdjoint_of_iso {F G
 : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] : IsRightAdjoint G where exists_leftAdj
oint
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma isRightAdjoint_comp_iff_right {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsEquivalence] :
    (F ⋙ G).IsRightAdjoint ↔ G.IsRightAdjoint := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  let iso : G ≅ F.asEquivalence.inverse ⋙ F ⋙ G :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (F.asEquivalence.counitIso).symm _ ≪≫
      Functor.associator _ _ _
  exact isRightAdjoint_of_iso iso.symm
/-
**CategoryTheory.Functor.isLeftAdjoint_comp_iff_left** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：isLeftAdjoint_comp_iff_left {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G
 : D ⥤ E) [G.IsEquivalence] : (F ⋙ G).IsLeftAdjoint ↔ F.IsLeftAdjoint
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_iso`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma isLeftAdjoint_comp_iff_left {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [G.IsEquivalence] :
    (F ⋙ G).IsLeftAdjoint ↔ F.IsLeftAdjoint := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isLeftAdjoint_of_iso iso.symm
/-
**CategoryTheory.Functor.isRightAdjoint_comp_iff_left** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：isRightAdjoint_comp_iff_left {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (
G : D ⥤ E) [G.IsEquivalence] : (F ⋙ G).IsRightAdjoint ↔ F.IsRightAdjoint
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isRightAdjoint_of_iso`：isRightAdjoint_of_iso {F G
 : C ⥤ D} (h : F ≅ G) [F.IsRightAdjoint] : IsRightAdjoint G where exists_leftAdj
oint
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
lemma isRightAdjoint_comp_iff_left {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [G.IsEquivalence] :
    (F ⋙ G).IsRightAdjoint ↔ F.IsRightAdjoint := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  let iso : F ≅ (F ⋙ G) ⋙ G.asEquivalence.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ G.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm
  exact isRightAdjoint_of_iso iso.symm

end Functor

end CategoryTheory

