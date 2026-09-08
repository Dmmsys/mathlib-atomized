/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts.
Binary biproducts are defined in `CategoryTheory.Limits.Shapes.BinaryBiproducts`.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

For biproducts indexed by a `Fintype J`, a `bicone` consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.

## Implementation notes

Prior to https://github.com/leanprover-community/mathlib3/pull/14046,
`HasFiniteBiproducts` required a `DecidableEq` instance on the indexing type.
As this had no pay-off (everything about limits is non-constructive in mathlib),
and occasional cost
(constructing decidability instances appropriate for constructions involving the indexing type),
we made everything classical.
-/

@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

open scoped Classical in
/-- A `c : Bicone F` is:
* an object `c.pt` and
* morphisms `π j : pt ⟶ F j` and `ι j : F j ⟶ pt` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
/-
**CategoryTheory.Limits.Bicone** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：Bicone (F : J -> C) where pt : C π : forall j, pt ⟶ F j ι : forall j, F j 
⟶ pt ι_π : forall j j', ι j ≫ π j' = if h : j = j' then eqToHom (congrArg F h) e
lse 0
参数：F : J -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `c : Bicone F` is:
* an object `c.pt` and
* morphisms `π j : pt ⟶ F j` and `ι j : F j ⟶ pt` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
structure Bicone (F : J → C) where
  pt : C
  π : ∀ j, pt ⟶ F j
  ι : ∀ j, F j ⟶ pt
  ι_π : ∀ j j', ι j ≫ π j' =
    if h : j = j' then eqToHom (congrArg F h) else 0 := by aesop

attribute [inherit_doc Bicone] Bicone.pt Bicone.π Bicone.ι Bicone.ι_π

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.bicone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bicone_ι_π_self {F : J → C} (B : Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) := by
  simpa using B.ι_π j j

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.bicone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bicone_ι_π_ne {F : J → C} (B : Bicone F) {j j' : J} (h : j ≠ j') : B.ι j ≫ B.π j' = 0 := by
  simpa [h] using B.ι_π j j'

variable {F : J → C}

/-- A bicone morphism between two bicones for the same diagram is a morphism of the bicone points
which commutes with the cone and cocone legs. -/
/-
**CategoryTheory.Limits.BiconeMorphism** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：BiconeMorphism {F : J -> C} (A B : Bicone F) where /-- A morphism between 
the two vertex objects of the bicones -/ hom : A.pt ⟶ B.pt /-- The triangle cons
isting of the two natural transformations and `hom` commutes -/ wπ : forall j : 
J, hom ≫ B.π j = A.π j
参数：A B : Bicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicone morphism between two bicones for the same diagram is a morphism of the 
bicone points
which commutes with the cone and cocone legs.
-/
structure BiconeMorphism {F : J → C} (A B : Bicone F) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wπ : ∀ j : J, hom ≫ B.π j = A.π j := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wι : ∀ j : J, A.ι j ≫ hom = B.ι j := by cat_disch

attribute [reassoc (attr := simp)] BiconeMorphism.wι BiconeMorphism.wπ

/-- The category of bicones on a given diagram. -/
@[simps]
/-
**CategoryTheory.Limits.Bicone.category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Bicone`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {F
 : J → C} → CategoryTheory.Category.{uC', max (max uC uC') w} (CategoryTheory.Li
mits.Bicone F)
参数：max uC uC'；CategoryTheory.Limits.Bicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of bicones on a given diagram.
-/
instance Bicone.category : Category (Bicone F) where
  Hom A B := BiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/-! We do not want `simps` automatically generate the lemma for simplifying the `Hom` field of
a category. So we need to write the `ext` lemma in terms of the categorical morphism, rather than
the underlying structure. -/
@[ext]
/-
**CategoryTheory.Limits.BiconeMorphism.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.BiconeMorphism`。
形式化陈述：∀ {J : Type w} {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] 
  [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {F : J → C} {c c' : Catego
ryTheory.Limits.Bicone F}   (f g : c ⟶ c'), f.hom = g.hom → f = g
参数：f g : c ⟶ c'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
We do not want `simps` automatically generate the lemma for simplifying the `Hom
` field of
a category. So we need to write the `ext` lemma in terms of the categorical morp
hism, rather than
the underlying structure.
-/
theorem BiconeMorphism.ext {c c' : Bicone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace Bicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
/-
**CategoryTheory.Limits.Bicones.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Bicones`。
形式化陈述：ext {c c' : Bicone F} (φ : c.pt ≅ c'.pt) (wι : forall j, c.ι j ≫ φ.hom = c
'.ι j
参数：φ : c.pt ≅ c'.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps.
-/
def ext {c c' : Bicone F} (φ : c.pt ≅ c'.pt)
    (wι : ∀ j, c.ι j ≫ φ.hom = c'.ι j := by cat_disch)
    (wπ : ∀ j, φ.hom ≫ c'.π j = c.π j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wι := fun j => φ.comp_inv_eq.mpr (wι j).symm
      wπ := fun j => φ.inv_comp_eq.mpr (wπ j).symm }

variable (F) in
/-- A functor `G : C ⥤ D` sends bicones over `F` to bicones over `G.obj ∘ F` functorially. -/
@[simps]
/-
**CategoryTheory.Limits.Bicones.functoriality** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.Bicones`。
形式化陈述：functoriality (G : C ⥤ D) [Functor.PreservesZeroMorphisms G] : Bicone F ⥤ 
Bicone (G.obj ∘ F) where obj A
参数：G : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : C ⥤ D` sends bicones over `F` to bicones over `G.obj ∘ F` functor
ially.
-/
def functoriality (G : C ⥤ D) [Functor.PreservesZeroMorphisms G] :
    Bicone F ⥤ Bicone (G.obj ∘ F) where
  obj A :=
    { pt := G.obj A.pt
      π := fun j => G.map (A.π j)
      ι := fun j => G.map (A.ι j)
      ι_π := fun i j => (Functor.map_comp _ _ _).symm.trans <| by
        rw [A.ι_π]
        cat_disch }
  map f :=
    { hom := G.map f.hom
      wπ := fun j => by simp [-BiconeMorphism.wπ, ← f.wπ j]
      wι := fun j => by simp [-BiconeMorphism.wι, ← f.wι j] }

variable (G : C ⥤ D)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.Bicones.functoriality_full** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits.Bicones`。
形式化陈述：functoriality_full [G.PreservesZeroMorphisms] [G.Full] [G.Faithful] : (fun
ctoriality F G).Full where map_surjective t
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.Bicones.functoriality_obj_π`：∀ {J : Type w} {C : T
ype uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] {D : Type uD…
· 使用定理 `CategoryTheory.Limits.BiconeMorphism.wπ`：∀ {J : Type w} {C : Type uC} [i
nst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.Bicones.functoriality_obj_ι`：∀ {J : Type w} {C : T
ype uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] {D : Type uD…
· 使用定理 `CategoryTheory.Limits.BiconeMorphism.wι`：∀ {J : Type w} {C : Type uC} [i
nst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.BiconeMorphism.ext`：∀ {J : Type w} {C : Type uC} [
inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] {F : J → C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.Bicones.functoriality_map_hom`：∀ {J : Type w} {C :
 Type uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C] {D : Type uD…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance functoriality_full [G.PreservesZeroMorphisms] [G.Full] [G.Faithful] :
    (functoriality F G).Full where
  map_surjective t :=
   ⟨{ hom := G.preimage t.hom
      wι := fun j => G.map_injective (by simpa using! t.wι j)
      wπ := fun j => G.map_injective (by simpa using! t.wπ j) }, by cat_disch⟩
/-
**CategoryTheory.Limits.Bicones.functoriality_faithful** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits.Bicones`。
形式化陈述：functoriality_faithful [G.PreservesZeroMorphisms] [G.Faithful] : (functori
ality F G).Faithful where map_injective {_X} {_Y} f g h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BiconeMorphism.ext`：∀ {J : Type w} {C : Type uC} [
inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance functoriality_faithful [G.PreservesZeroMorphisms] [G.Faithful] :
    (functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    BiconeMorphism.ext f g <| G.map_injective <| congr_arg BiconeMorphism.hom h

end Bicones

namespace Bicone

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- Porting note: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

set_option backward.defeqAttrib.useBackward true in
/-- Extract the cone from a bicone. -/
/-
**CategoryTheory.Limits.Bicone.toConeFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Bicone`。
形式化陈述：toConeFunctor : Bicone F ⥤ Cone (Discrete.functor F) where obj B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the cone from a bicone.
-/
def toConeFunctor : Bicone F ⥤ Cone (Discrete.functor F) where
  obj B := { pt := B.pt, π := { app := fun j => B.π j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wπ _ }

/-- A shorthand for `toConeFunctor.obj` -/
/-
**CategoryTheory.Limits.Bicone.toCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits.Bicone`。
形式化陈述：toCone (B : Bicone F) : Cone (Discrete.functor F)
参数：B : Bicone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for `toConeFunctor.obj`
-/
abbrev toCone (B : Bicone F) : Cone (Discrete.functor F) := toConeFunctor.obj B

-- TODO Consider changing this API to `toFan (B : Bicone F) : Fan F`.
/-
**CategoryTheory.Limits.Bicone.toCone_pt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Bicone`。
形式化陈述：∀ {J : Type w} {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] 
  [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {F : J → C} (B : CategoryT
heory.Limits.Bicone F),   B.toCone.pt = B.pt
参数：B : CategoryTheory.Limits.Bicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCone_pt (B : Bicone F) : B.toCone.pt = B.pt := rfl
/-
**CategoryTheory.Limits.Bicone.toCone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCone_π_app (B : Bicone F) (j : Discrete J) : B.toCone.π.app j = B.π j.as := rfl
/-
**CategoryTheory.Limits.Bicone.toCone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCone_π_app_mk (B : Bicone F) (j : J) : B.toCone.π.app ⟨j⟩ = B.π j := rfl
/-
**CategoryTheory.Limits.Bicone.toCone_proj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.Bicone`。
形式化陈述：∀ {J : Type w} {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] 
  [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {F : J → C} (B : CategoryT
heory.Limits.Bicone F) (j : J),   CategoryTheory.Limits.Fan.proj B.toCone j = B.
π j
参数：B : CategoryTheory.Limits.Bicone F；j : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCone_proj (B : Bicone F) (j : J) : Fan.proj B.toCone j = B.π j := rfl

set_option backward.defeqAttrib.useBackward true in
/-- Extract the cocone from a bicone. -/
/-
**CategoryTheory.Limits.Bicone.toCoconeFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Bicone`。
形式化陈述：toCoconeFunctor : Bicone F ⥤ Cocone (Discrete.functor F) where obj B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the cocone from a bicone.
-/
def toCoconeFunctor : Bicone F ⥤ Cocone (Discrete.functor F) where
  obj B := { pt := B.pt, ι := { app := fun j => B.ι j.as } }
  map {_ _} F := { hom := F.hom, w := fun _ => F.wι _ }

/-- A shorthand for `toCoconeFunctor.obj` -/
/-
**CategoryTheory.Limits.Bicone.toCocone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits.Bicone`。
形式化陈述：toCocone (B : Bicone F) : Cocone (Discrete.functor F)
参数：B : Bicone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for `toCoconeFunctor.obj`
-/
abbrev toCocone (B : Bicone F) : Cocone (Discrete.functor F) := toCoconeFunctor.obj B
/-
**CategoryTheory.Limits.Bicone.toCocone_pt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.Bicone`。
形式化陈述：∀ {J : Type w} {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] 
  [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {F : J → C} (B : CategoryT
heory.Limits.Bicone F),   B.toCocone.pt = B.pt
参数：B : CategoryTheory.Limits.Bicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCocone_pt (B : Bicone F) : B.toCocone.pt = B.pt := rfl

@[simp]
/-
**CategoryTheory.Limits.Bicone.toCocone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCocone_ι_app (B : Bicone F) (j : Discrete J) : B.toCocone.ι.app j = B.ι j.as := rfl
/-
**CategoryTheory.Limits.Bicone.toCocone_inj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Bicone`。
形式化陈述：∀ {J : Type w} {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] 
  [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {F : J → C} (B : CategoryT
heory.Limits.Bicone F) (j : J),   CategoryTheory.Limits.Cofan.inj B.toCocone j =
 B.ι j
参数：B : CategoryTheory.Limits.Bicone F；j : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toCocone_inj (B : Bicone F) (j : J) : Cofan.inj B.toCocone j = B.ι j := rfl
/-
**CategoryTheory.Limits.Bicone.toCocone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCocone_ι_app_mk (B : Bicone F) (j : J) : B.toCocone.ι.app ⟨j⟩ = B.ι j := rfl

/-- The retract of a bicone `B` given by `B.ι j` and `B.π j`. -/
/-
**CategoryTheory.Limits.Bicone.retract** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Bicone`。
形式化陈述：retract (B : Bicone F) (j : J) : Retract (F j) B.pt where i
参数：B : Bicone F；j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The retract of a bicone `B` given by `B.ι j` and `B.π j`.
-/
def retract (B : Bicone F) (j : J) : Retract (F j) B.pt where
  i := B.ι j
  r := B.π j
/-
**CategoryTheory.Limits.Bicone.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits
.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : Bicone F) (j : J) : IsSplitMono (B.ι j) := (B.retract j).instIsSplitMonoI
/-
**CategoryTheory.Limits.Bicone.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits
.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (B : Bicone F) (j : J) : IsSplitEpi (B.π j) := (B.retract j).instIsSplitEpiR

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- We can turn any limit cone over a discrete collection of objects into a bicone. -/
@[simps]
/-
**CategoryTheory.Limits.Bicone.ofLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Bicone`。
形式化陈述：ofLimitCone {f : J -> C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) 
: Bicone f where pt
参数：Discrete.functor f；ht : IsLimit t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
We can turn any limit cone over a discrete collection of objects into a bicone.
-/
def ofLimitCone {f : J → C} {t : Cone (Discrete.functor f)} (ht : IsLimit t) : Bicone f where
  pt := t.pt
  π j := t.π.app ⟨j⟩
  ι j := ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0)
  ι_π j j' := by simp

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-
**CategoryTheory.Limits.Bicone.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_of_isLimit {f : J → C} {t : Bicone f} (ht : IsLimit t.toCone) (j : J) :
    t.ι j = ht.lift (Fan.mk _ fun j' => if h : j = j' then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- We can turn any colimit cocone over a discrete collection of objects into a bicone. -/
@[simps]
/-
**CategoryTheory.Limits.Bicone.ofColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Bicone`。
形式化陈述：ofColimitCocone {f : J -> C} {t : Cocone (Discrete.functor f)} (ht : IsCol
imit t) : Bicone f where pt
参数：Discrete.functor f；ht : IsColimit t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
We can turn any colimit cocone over a discrete collection of objects into a bico
ne.
-/
def ofColimitCocone {f : J → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t) :
    Bicone f where
  pt := t.pt
  π j := ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0)
  ι j := t.ι.app ⟨j⟩
  ι_π j j' := by simp

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-
**CategoryTheory.Limits.Bicone.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
.Bicone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_of_isColimit {f : J → C} {t : Bicone f} (ht : IsColimit t.toCocone) (j : J) :
    t.π j = ht.desc (Cofan.mk _ fun j' => if h : j' = j then eqToHom (congr_arg f h) else 0) :=
  ht.hom_ext fun j' => by
    rw [ht.fac]
    simp [t.ι_π]

/-- Structure witnessing that a bicone is both a limit cone and a colimit cocone. -/
/-
**CategoryTheory.Limits.Bicone.IsBilimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Limits.Bicone`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {F
 : J → C} → CategoryTheory.Limits.Bicone F → Type (max (max uC uC') w)
参数：max (max uC uC') w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure witnessing that a bicone is both a limit cone and a colimit cocone.
-/
structure IsBilimit {F : J → C} (B : Bicone F) where
  isLimit : IsLimit B.toCone
  isColimit : IsColimit B.toCocone

attribute [inherit_doc IsBilimit] IsBilimit.isLimit IsBilimit.isColimit

attribute [simp] IsBilimit.mk.injEq

attribute [local ext] Bicone.IsBilimit
/-
**CategoryTheory.Limits.Bicone.subsingleton_isBilimit** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits.Bicone`。
形式化陈述：subsingleton_isBilimit {f : J -> C} {c : Bicone f} : Subsingleton c.IsBili
mit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Bicone.IsBilimit.ext`：∀ {J : Type w} {C : Type uC}
 {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C} {F : J → C} …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Limits.IsColimit.subsingleton`：∀ {J : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Categor
y.{v₃, u₃} C]   {F : CategoryTheor…
-/
instance subsingleton_isBilimit {f : J → C} {c : Bicone f} : Subsingleton c.IsBilimit :=
  ⟨fun _ _ => Bicone.IsBilimit.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩

section Whisker

variable {K : Type w'}

set_option backward.isDefEq.respectTransparency false in
/-- Whisker a bicone with an equivalence between the indexing types. -/
@[simps]
/-
**CategoryTheory.Limits.Bicone.whisker** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Bicone`。
形式化陈述：whisker {f : J -> C} (c : Bicone f) (g : K ≃ J) : Bicone (f ∘ g) where pt
参数：c : Bicone f；g : K ≃ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whisker a bicone with an equivalence between the indexing types.
-/
def whisker {f : J → C} (c : Bicone f) (g : K ≃ J) : Bicone (f ∘ g) where
  pt := c.pt
  π k := c.π (g k)
  ι k := c.ι (g k)
  ι_π k k' := by
    simp only [c.ι_π]
    split_ifs with h h' h' <;> simp [Equiv.apply_eq_iff_eq g] at h h' <;> tauto

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Taking the cone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cone and postcomposing with a suitable isomorphism. -/
/-
**CategoryTheory.Limits.Bicone.whiskerToCone** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Bicone`。
形式化陈述：whiskerToCone {f : J -> C} (c : Bicone f) (g : K ≃ J) : (c.whisker g).toCo
ne ≅ (Cone.postcompose (Discrete.functorComp f g).inv).obj (c.toCone.whisker (Di
screte.functor (Discrete.mk ∘ g)))
参数：c : Bicone f；g : K ≃ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the cone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cone and postcomposing with a suitable isomorphism.
-/
def whiskerToCone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCone ≅
      (Cone.postcompose (Discrete.functorComp f g).inv).obj
        (c.toCone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cone.ext (Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Taking the cocone of a whiskered bicone results in a cone isomorphic to one gained
by whiskering the cocone and precomposing with a suitable isomorphism. -/
/-
**CategoryTheory.Limits.Bicone.whiskerToCocone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Bicone`。
形式化陈述：whiskerToCocone {f : J -> C} (c : Bicone f) (g : K ≃ J) : (c.whisker g).to
Cocone ≅ (Cocone.precompose (Discrete.functorComp f g).hom).obj (c.toCocone.whis
ker (Discrete.functor (Discrete.mk ∘ g)))
参数：c : Bicone f；g : K ≃ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the cocone of a whiskered bicone results in a cone isomorphic to one gain
ed
by whiskering the cocone and precomposing with a suitable isomorphism.
-/
def whiskerToCocone {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).toCocone ≅
      (Cocone.precompose (Discrete.functorComp f g).hom).obj
        (c.toCocone.whisker (Discrete.functor (Discrete.mk ∘ g))) :=
  Cocone.ext (Iso.refl _) (by simp)

/-- Whiskering a bicone with an equivalence between types preserves being a bilimit bicone. -/
/-
**CategoryTheory.Limits.Bicone.whiskerIsBilimitIff** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Bicone`。
形式化陈述：whiskerIsBilimitIff {f : J -> C} (c : Bicone f) (g : K ≃ J) : (c.whisker g
).IsBilimit ≃ c.IsBilimit
参数：c : Bicone f；g : K ≃ J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Whiskering a bicone with an equivalence between types preserves being a bilimit 
bicone.
-/
noncomputable def whiskerIsBilimitIff {f : J → C} (c : Bicone f) (g : K ≃ J) :
    (c.whisker g).IsBilimit ≃ c.IsBilimit := by
  refine equivOfSubsingletonOfSubsingleton (fun hc => ⟨?_, ?_⟩) fun hc => ⟨?_, ?_⟩
  · let := IsLimit.ofIsoLimit hc.isLimit (Bicone.whiskerToCone c g)
    let := (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _) this
    exact IsLimit.ofWhiskerEquivalence (Discrete.equivalence g) this
  · let := IsColimit.ofIsoColimit hc.isColimit (Bicone.whiskerToCocone c g)
    let := (IsColimit.precomposeHomEquiv (Discrete.functorComp f g) _) this
    exact IsColimit.ofWhiskerEquivalence (Discrete.equivalence g) this
  · apply IsLimit.ofIsoLimit _ (Bicone.whiskerToCone c g).symm
    apply (IsLimit.postcomposeHomEquiv (Discrete.functorComp f g).symm _).symm _
    exact IsLimit.whiskerEquivalence hc.isLimit (Discrete.equivalence g)
  · apply IsColimit.ofIsoColimit _ (Bicone.whiskerToCocone c g).symm
    apply (IsColimit.precomposeHomEquiv (Discrete.functorComp f g) _).symm _
    exact IsColimit.whiskerEquivalence hc.isColimit (Discrete.equivalence g)

end Whisker

end Bicone

/-- A bicone over `F : J → C`, which is both a limit cone and a colimit cocone. -/
/-
**CategoryTheory.Limits.LimitBicone** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] →       [CategoryTheory.Limits.HasZeroMorphisms C] → (J → C) → Type (max
 (max uC uC') w)
参数：J → C；max (max uC uC') w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
structure LimitBicone (F : J → C) where
  bicone : Bicone F
  isBilimit : bicone.IsBilimit

attribute [inherit_doc LimitBicone] LimitBicone.bicone LimitBicone.isBilimit

/-- `HasBiproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`. -/
/-
**CategoryTheory.Limits.HasBiproduct** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] → [CategoryTheory.Limits.HasZeroMorphisms C] → (J → C) → Prop
参数：J → C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasBiproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class HasBiproduct (F : J → C) : Prop where mk' ::
  exists_biproduct : Nonempty (LimitBicone F)

attribute [inherit_doc HasBiproduct] HasBiproduct.exists_biproduct
/-
**CategoryTheory.Limits.HasBiproduct.mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.HasBiproduct`。
形式化陈述：∀ {J : Type w} {C : Type uC} [inst : CategoryTheory.Category.{uC', uC} C] 
  [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {F : J → C} (d : CategoryT
heory.Limits.LimitBicone F),   CategoryTheory.Limits.HasBiproduct F
参数：d : CategoryTheory.Limits.LimitBicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasBiproduct.mk {F : J → C} (d : LimitBicone F) : HasBiproduct F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `BiproductData F` from `HasBiproduct F`. -/
/-
**CategoryTheory.Limits.getBiproductData** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：getBiproductData (F : J -> C) [HasBiproduct F] : LimitBicone F
参数：F : J -> C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproduct.exists_biproduct`：∀ {J : Type w} {C :
 Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C} {F : J → C} …

--- 原说明 ---
Use the axiom of choice to extract explicit `BiproductData F` from `HasBiproduct
 F`.
-/
def getBiproductData (F : J → C) [HasBiproduct F] : LimitBicone F :=
  Classical.choice HasBiproduct.exists_biproduct

/-- A bicone for `F` which is both a limit cone and a colimit cocone. -/
/-
**CategoryTheory.Limits.biproduct.bicone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (F
 : J → C) → [CategoryTheory.Limits.HasBiproduct F] → CategoryTheory.Limits.Bicon
e F
参数：F : J → C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bicone for `F` which is both a limit cone and a colimit cocone.
-/
def biproduct.bicone (F : J → C) [HasBiproduct F] : Bicone F :=
  (getBiproductData F).bicone

/-- `biproduct.bicone F` is a bilimit bicone. -/
/-
**CategoryTheory.Limits.biproduct.isBilimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (F
 : J → C) →           [inst_2 : CategoryTheory.Limits.HasBiproduct F] → (Categor
yTheory.Limits.biproduct.bicone F).IsBilimit
参数：F : J → C；CategoryTheory.Limits.biproduct.bicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biproduct.bicone F` is a bilimit bicone.
-/
def biproduct.isBilimit (F : J → C) [HasBiproduct F] : (biproduct.bicone F).IsBilimit :=
  (getBiproductData F).isBilimit

/-- `biproduct.bicone F` is a limit cone. -/
/-
**CategoryTheory.Limits.biproduct.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (F
 : J → C) →           [inst_2 : CategoryTheory.Limits.HasBiproduct F] →         
    CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.biproduct.bicone F).toC
one
参数：F : J → C；CategoryTheory.Limits.biproduct.bicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biproduct.bicone F` is a limit cone.
-/
def biproduct.isLimit (F : J → C) [HasBiproduct F] : IsLimit (biproduct.bicone F).toCone :=
  (getBiproductData F).isBilimit.isLimit

/-- `biproduct.bicone F` is a colimit cocone. -/
/-
**CategoryTheory.Limits.biproduct.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type uC} →     [inst : CategoryTheory.Category.{uC',
 uC} C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (F
 : J → C) →           [inst_2 : CategoryTheory.Limits.HasBiproduct F] →         
    CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.biproduct.bicone F).t
oCocone
参数：F : J → C；CategoryTheory.Limits.biproduct.bicone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biproduct.bicone F` is a colimit cocone.
-/
def biproduct.isColimit (F : J → C) [HasBiproduct F] : IsColimit (biproduct.bicone F).toCocone :=
  (getBiproductData F).isBilimit.isColimit
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasProduct_of_hasBiproduct [HasBiproduct F] : HasProduct F :=
  HasLimit.mk
    { cone := (biproduct.bicone F).toCone
      isLimit := biproduct.isLimit F }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCoproduct_of_hasBiproduct [HasBiproduct F] : HasCoproduct F :=
  HasColimit.mk
    { cocone := (biproduct.bicone F).toCocone
      isColimit := biproduct.isColimit F }

variable (J C)

/-- `C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`. -/
/-
**CategoryTheory.Limits.HasBiproductsOfShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：Type w →   (C : Type uC) → [inst : CategoryTheory.Category.{uC', uC} C] → 
[CategoryTheory.Limits.HasZeroMorphisms C] → Prop
参数：C : Type uC。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`.
-/
class HasBiproductsOfShape : Prop where
  has_biproduct : ∀ F : J → C, HasBiproduct F

attribute [instance 100] HasBiproductsOfShape.has_biproduct

/-- A category `HasFiniteBiproducts` if it has a biproduct for every finite family of objects in `C`
indexed by a finite type. -/
/-
**CategoryTheory.Limits.HasFiniteBiproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：(C : Type uC) → [inst : CategoryTheory.Category.{uC', uC} C] → [CategoryTh
eory.Limits.HasZeroMorphisms C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasFiniteBiproducts` if it has a biproduct for every finite family o
f objects in `C`
indexed by a finite type.
-/
class HasFiniteBiproducts : Prop where
  out : ∀ n, HasBiproductsOfShape (Fin n) C

attribute [inherit_doc HasFiniteBiproducts] HasFiniteBiproducts.out

variable {J}
/-
**CategoryTheory.Limits.hasBiproductsOfShape_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasBiproductsOfShape_of_equiv {K : Type w'} [HasBiproductsOfShape K C] (e 
: J ≃ K) : HasBiproductsOfShape J C
参数：e : J ≃ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.HasBiproduct.mk`：∀ {J : Type w} {C : Type uC} [ins
t : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] {F : J → C} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem hasBiproductsOfShape_of_equiv {K : Type w'} [HasBiproductsOfShape K C] (e : J ≃ K) :
    HasBiproductsOfShape J C :=
  ⟨fun F =>
    let ⟨⟨h⟩⟩ := HasBiproductsOfShape.has_biproduct (F ∘ e.symm)
    let ⟨c, hc⟩ := h
    HasBiproduct.mk <| by
      simpa only [Function.comp_def, e.symm_apply_apply] using
        LimitBicone.mk (c.whisker e) ((c.whiskerIsBilimitIff _).2 hc)⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasBiproductsOfShape_finite [HasFiniteBiproducts C] [Finite J] :
    HasBiproductsOfShape J C := by
  rcases Finite.exists_equiv_fin J with ⟨n, ⟨e⟩⟩
  have : HasBiproductsOfShape (Fin n) C := HasFiniteBiproducts.out n
  exact hasBiproductsOfShape_of_equiv C e
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteProducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteProducts C where
  out _ := ⟨fun _ => hasLimit_of_iso Discrete.natIsoFunctor.symm⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasFiniteCoproducts_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteCoproducts C where
  out _ := ⟨fun _ => hasColimit_of_iso Discrete.natIsoFunctor⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasProductsOfShape_of_hasBiproductsOfShape [HasBiproductsOfShape J C] :
    HasProductsOfShape J C where
  has_limit _ := hasLimit_of_iso Discrete.natIsoFunctor.symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCoproductsOfShape_of_hasBiproductsOfShape [HasBiproductsOfShape J C] :
    HasCoproductsOfShape J C where
  has_colimit _ := hasColimit_of_iso Discrete.natIsoFunctor

variable {C}

/-- The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit. -/
/-
**CategoryTheory.Limits.biproductIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：biproductIso (F : J -> C) [HasBiproduct F] : Limits.piObj F ≅ Limits.sigma
Obj F
参数：F : J -> C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.hasCoproduct_of_hasBiproduct`：∀ {J : Type w} {C : 
Type uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory
.Limits.HasZeroMorphisms C] {F : J → C} …

--- 原说明 ---
The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproductIso (F : J → C) [HasBiproduct F] : Limits.piObj F ≅ Limits.sigmaObj F :=
  (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (biproduct.isLimit F)).trans <|
    IsColimit.coconePointUniqueUpToIso (biproduct.isColimit F) (colimit.isColimit _)

variable {J : Type w} {K : Type*}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
abbreviation for `limit (Discrete.functor f)`, so for most facts about `biproduct f`, you will
just use general facts about limits and colimits.) -/
/-
**CategoryTheory.Limits.biproduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：biproduct (f : J -> C) [HasBiproduct f] : C
参数：f : J -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`biproduct f` computes the biproduct of a family of elements `f`. (It is defined
 as an
abbreviation for `limit (Discrete.functor f)`, so for most facts about `biproduc
t f`, you will
just use general facts about limits and colimits.)
-/
abbrev biproduct (f : J → C) [HasBiproduct f] : C :=
  (biproduct.bicone f).pt

@[inherit_doc biproduct]
notation "⨁ " f:20 => biproduct f

/-- The projection onto a summand of a biproduct. -/
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection onto a summand of a biproduct.
-/
abbrev biproduct.π (f : J → C) [HasBiproduct f] (b : J) : ⨁ f ⟶ f b :=
  (biproduct.bicone f).π b

@[simp]
/-
**CategoryTheory.Limits.biproduct.bicone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.bicone_π (f : J → C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).π b = biproduct.π f b := rfl

/-- The inclusion into a summand of a biproduct. -/
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion into a summand of a biproduct.
-/
abbrev biproduct.ι (f : J → C) [HasBiproduct f] (b : J) : f b ⟶ ⨁ f :=
  (biproduct.bicone f).ι b

@[simp]
/-
**CategoryTheory.Limits.biproduct.bicone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.bicone_ι (f : J → C) [HasBiproduct f] (b : J) :
    (biproduct.bicone f).ι b = biproduct.ι f b := rfl

/-- Note that as this lemma has an `if` in the statement, we include a `DecidableEq` argument.
This means you may not be able to `simp` using this lemma unless you `open scoped Classical`. -/
@[reassoc]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that as this lemma has an `if` in the statement, we include a `DecidableEq`
 argument.
This means you may not be able to `simp` using this lemma unless you `open scope
d Classical`.
-/
theorem biproduct.ι_π [DecidableEq J] (f : J → C) [HasBiproduct f] (j j' : J) :
    biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eqToHom (congr_arg f h) else 0 := by
  convert! (biproduct.bicone f).ι_π j j'

@[reassoc] -- Not `simp` because `simp` can prove this
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_π_self (f : J → C) [HasBiproduct f] (j : J) :
    biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ := by simp

@[reassoc]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_π_ne (f : J → C) [HasBiproduct f] {j j' : J} (h : j ≠ j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 := by simp [h]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.eqToHom_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.eqToHom_comp_ι (f : J → C) [HasBiproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ biproduct.ι f j' = biproduct.ι f j := by
  cases w
  simp

-- TODO?: simp can prove this using `eqToHom_naturality`
-- but `eqToHom_naturality` applies less easily than this lemma
@[reassoc]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.π_comp_eqToHom (f : J → C) [HasBiproduct f] {j j' : J} (w : j = j') :
    biproduct.π f j ≫ eqToHom (by simp [w]) = biproduct.π f j' := by
  simp [*]

/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
/-
**CategoryTheory.Limits.biproduct.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {f : J
 → C} → [inst_2 : CategoryTheory.Limits.HasBiproduct f] → {P : C} → ((b : J) → P
 ⟶ f b) → (P ⟶ ⨁ f)
参数：(b : J) → P ⟶ f b；P ⟶ ⨁ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a collection of maps into the summands, we obtain a map into the biproduct
.
-/
abbrev biproduct.lift {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ⨁ f :=
  (biproduct.isLimit f).lift (Fan.mk P p)

/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
/-
**CategoryTheory.Limits.biproduct.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {f : J
 → C} → [inst_2 : CategoryTheory.Limits.HasBiproduct f] → {P : C} → ((b : J) → f
 b ⟶ P) → (⨁ f ⟶ P)
参数：(b : J) → f b ⟶ P；⨁ f ⟶ P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a collection of maps out of the summands, we obtain a map out of the bipro
duct.
-/
abbrev biproduct.desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ⨁ f ⟶ P :=
  (biproduct.isColimit f).desc (Cofan.mk P p)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.lift_π {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, P ⟶ f b) (j : J) :
    biproduct.lift p ≫ biproduct.π f j = p j := (biproduct.isLimit f).fac _ ⟨j⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_desc {f : J → C} [HasBiproduct f] {P : C} (p : ∀ b, f b ⟶ P) (j : J) :
    biproduct.ι f j ≫ biproduct.desc p = p j := (biproduct.isColimit f).fac _ ⟨j⟩

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
/-
**CategoryTheory.Limits.biproduct.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {f g :
 J → C} →           [inst_2 : CategoryTheory.Limits.HasBiproduct f] →           
  [inst_3 : CategoryTheory.Limits.HasBiproduct g] → ((b : J) → f b ⟶ g b) → (⨁ f
 ⟶ ⨁ g)
参数：(b : J) → f b ⟶ g b；⨁ f ⟶ ⨁ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a collection of maps between corresponding summands of a pair of biproduct
s
indexed by the same type, we obtain a map between the biproducts.
-/
abbrev biproduct.map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsLimit.map (biproduct.bicone f).toCone (biproduct.isLimit g)
    (Discrete.natTrans (fun j => p j.as))

/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
/-
**CategoryTheory.Limits.biproduct.map'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {f g :
 J → C} →           [inst_2 : CategoryTheory.Limits.HasBiproduct f] →           
  [inst_3 : CategoryTheory.Limits.HasBiproduct g] → ((b : J) → f b ⟶ g b) → (⨁ f
 ⟶ ⨁ g)
参数：(b : J) → f b ⟶ g b；⨁ f ⟶ ⨁ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`.
-/
abbrev biproduct.map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  IsColimit.map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as)

-- We put this at slightly higher priority than `biproduct.hom_ext'`,
-- to get the matrix indices in the "right" order.
@[ext 1001]
/-
**CategoryTheory.Limits.biproduct.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} [inst_2 : Category
Theory.Limits.HasBiproduct f]   {Z : C} (g h : Z ⟶ ⨁ f),   (∀ (j : J),       Cat
egoryTheory.CategoryStruct.comp g (CategoryTheory.Limits.biproduct.π f j) =     
    CategoryTheory.CategoryStruct.comp h (CategoryTheory.Limits.biproduct.π f j)
) →     g = h
参数：g h : Z ⟶ ⨁ f；∀ (j : J),       CategoryTheory.CategoryStruct.comp g (Category
Theory.Limits.biproduct.π f j) =         CategoryTheory.CategoryStruct.comp h (C
ategoryTheory.Limits.biproduct.π f j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
-/
theorem biproduct.hom_ext {f : J → C} [HasBiproduct f] {Z : C} (g h : Z ⟶ ⨁ f)
    (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
  (biproduct.isLimit f).hom_ext fun j => w j.as

@[ext]
/-
**CategoryTheory.Limits.biproduct.hom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} [inst_2 : Category
Theory.Limits.HasBiproduct f]   {Z : C} (g h : ⨁ f ⟶ Z),   (∀ (j : J),       Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biproduct.ι f j) g =     
    CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.biproduct.ι f j) h
) →     g = h
参数：g h : ⨁ f ⟶ Z；∀ (j : J),       CategoryTheory.CategoryStruct.comp (CategoryTh
eory.Limits.biproduct.ι f j) g =         CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.Limits.biproduct.ι f j) h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
-/
theorem biproduct.hom_ext' {f : J → C} [HasBiproduct f] {Z : C} (g h : ⨁ f ⟶ Z)
    (w : ∀ j, biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
  (biproduct.isColimit f).hom_ext fun j => w j.as

/-- The canonical isomorphism between the chosen biproduct and the chosen product. -/
/-
**CategoryTheory.Limits.biproduct.isoProduct** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (f : J
 → C) → [inst_2 : CategoryTheory.Limits.HasBiproduct f] → ⨁ f ≅ ∏ᶜ f
参数：f : J → C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …

--- 原说明 ---
The canonical isomorphism between the chosen biproduct and the chosen product.
-/
def biproduct.isoProduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∏ᶜ f :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biproduct.isoProduct_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} [inst_2 : Category
Theory.Limits.HasBiproduct f],   (CategoryTheory.Limits.biproduct.isoProduct f).
hom =     CategoryTheory.Limits.Pi.lift (CategoryTheory.Limits.biproduct.π f)
参数：CategoryTheory.Limits.biproduct.isoProduct f；CategoryTheory.Limits.biproduct.
π f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.isoProduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).hom = Pi.lift (biproduct.π f) :=
  limit.hom_ext fun j => by simp [biproduct.isoProduct]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biproduct.isoProduct_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} [inst_2 : Category
Theory.Limits.HasBiproduct f],   (CategoryTheory.Limits.biproduct.isoProduct f).
inv =     CategoryTheory.Limits.biproduct.lift (CategoryTheory.Limits.Pi.π f)
参数：CategoryTheory.Limits.biproduct.isoProduct f；CategoryTheory.Limits.Pi.π f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biproduct.isoProduct_hom`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.isoProduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoProduct f).inv = biproduct.lift (Pi.π f) :=
  biproduct.hom_ext _ _ fun j => by simp [Iso.inv_comp_eq]

/-- The canonical isomorphism between the chosen biproduct and the chosen coproduct. -/
/-
**CategoryTheory.Limits.biproduct.isoCoproduct** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (f : J
 → C) → [inst_2 : CategoryTheory.Limits.HasBiproduct f] → ⨁ f ≅ ∐ f
参数：f : J → C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproduct_of_hasBiproduct`：∀ {J : Type w} {C : 
Type uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory
.Limits.HasZeroMorphisms C] {F : J → C} …

--- 原说明 ---
The canonical isomorphism between the chosen biproduct and the chosen coproduct.
-/
def biproduct.isoCoproduct (f : J → C) [HasBiproduct f] : ⨁ f ≅ ∐ f :=
  IsColimit.coconePointUniqueUpToIso (biproduct.isColimit f) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biproduct.isoCoproduct_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} [inst_2 : Category
Theory.Limits.HasBiproduct f],   (CategoryTheory.Limits.biproduct.isoCoproduct f
).inv =     CategoryTheory.Limits.Sigma.desc (CategoryTheory.Limits.biproduct.ι 
f)
参数：CategoryTheory.Limits.biproduct.isoCoproduct f；CategoryTheory.Limits.biproduc
t.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.hasCoproduct_of_hasBiproduct`：∀ {J : Type w} {C : 
Type uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory
.Limits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_inv`：∀ {J : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Cate
goryTheory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.isoCoproduct_inv {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).inv = Sigma.desc (biproduct.ι f) :=
  colimit.hom_ext fun j => by simp [biproduct.isoCoproduct]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.biproduct.isoCoproduct_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} [inst_2 : Category
Theory.Limits.HasBiproduct f],   (CategoryTheory.Limits.biproduct.isoCoproduct f
).hom =     CategoryTheory.Limits.biproduct.desc (CategoryTheory.Limits.Sigma.ι 
f)
参数：CategoryTheory.Limits.biproduct.isoCoproduct f；CategoryTheory.Limits.Sigma.ι 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.hasCoproduct_of_hasBiproduct`：∀ {J : Type w} {C : 
Type uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory
.Limits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.isoCoproduct_inv`：∀ {J : Type w} {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.isoCoproduct_hom {f : J → C} [HasBiproduct f] :
    (biproduct.isoCoproduct f).hom = biproduct.desc (Sigma.ι f) :=
  biproduct.hom_ext' _ _ fun j => by simp [← Iso.eq_comp_inv]

set_option backward.isDefEq.respectTransparency false in
/-- If a category has biproducts of a shape `J`, its `colim` and `lim` functor on diagrams over `J`
are isomorphic. -/
@[simps!]
/-
**CategoryTheory.Limits.HasBiproductsOfShape.colimIsoLim** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.HasBiproductsOfShape`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         [inst_
2 : CategoryTheory.Limits.HasBiproductsOfShape J C] →           CategoryTheory.L
imits.colim ≅ CategoryTheory.Limits.lim
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproductsOfShape_of_hasBiproductsOfShape`：∀ {J
 : Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 
: CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_hasBiproductsOfShape`：∀ {J :
 Type w} (C : Type uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : 
CategoryTheory.Limits.HasZeroMorphisms C] [CategoryThe…

--- 原说明 ---
If a category has biproducts of a shape `J`, its `colim` and `lim` functor on di
agrams over `J`
are isomorphic.
-/
def HasBiproductsOfShape.colimIsoLim [HasBiproductsOfShape J C] :
    colim (J := Discrete J) (C := C) ≅ lim :=
  NatIso.ofComponents (fun F => (Sigma.isoColimit F).symm ≪≫
      (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _ ≪≫ Pi.isoLimit F)
    fun η => colimit.hom_ext fun ⟨i⟩ => limit.hom_ext fun ⟨j⟩ => by
      classical
      by_cases h : i = j <;>
       simp_all [Sigma.isoColimit, Pi.isoLimit, biproduct.ι_π, biproduct.ι_π_assoc]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.biproduct.map_eq_map'** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f g : J → C} [inst_2 : Catego
ryTheory.Limits.HasBiproduct f]   [inst_3 : CategoryTheory.Limits.HasBiproduct g
] (p : (b : J) → f b ⟶ g b),   CategoryTheory.Limits.biproduct.map p = CategoryT
heory.Limits.biproduct.map' p
参数：p : (b : J) → f b ⟶ g b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.map_π`：map_π {F G : J ⥤ C} (c : Cone F) {d
 : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) : hd.map c α ≫ d.π.app j = c.π.a
pp j ≫ α.app j
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_map_assoc`：∀ {J : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category
.{v₃, u₃} C]   {F G : CategoryThe…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_assoc`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem biproduct.map_eq_map' {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ⟶ g b) :
    biproduct.map p = biproduct.map' p := by
  classical
  ext
  simp only [Discrete.natTrans_app, Limits.IsColimit.ι_map_assoc, Limits.IsLimit.map_π,
    ← Bicone.toCone_π_app_mk, ← Bicone.toCocone_ι_app_mk]
  dsimp
  rw [biproduct.ι_π_assoc, biproduct.ι_π]
  split_ifs with h
  · subst h; simp
  · simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.map_π {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    (j : J) : biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
  Limits.IsLimit.map_π _ _ _ (Discrete.mk j)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    (j : J) : biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j := by
  rw [biproduct.map_eq_map']
  apply
    Limits.IsColimit.ι_map (biproduct.isColimit f) (biproduct.bicone g).toCocone
    (Discrete.natTrans fun j => p j.as) (Discrete.mk j)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.map_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f g : J → C} [inst_2 : Catego
ryTheory.Limits.HasBiproduct f]   [inst_3 : CategoryTheory.Limits.HasBiproduct g
] (p : (j : J) → f j ⟶ g j) {P : C} (k : (j : J) → g j ⟶ P),   CategoryTheory.Ca
tegoryStruct.comp (CategoryTheory.Limits.biproduct.map p) (CategoryTheory.Limits
.biproduct.desc k) =     CategoryTheory.Limits.biproduct.desc fun j => CategoryT
heory.CategoryStruct.comp (p j) (k j)
参数：p : (j : J) → f j ⟶ g j；k : (j : J) → g j ⟶ P；CategoryTheory.Limits.biproduct
.map p；CategoryTheory.Limits.biproduct.desc k；p j；k j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_map_assoc`：∀ {J : Type w} {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.map_desc {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    {P : C} (k : ∀ j, g j ⟶ P) :
    biproduct.map p ≫ biproduct.desc k = biproduct.desc fun j => p j ≫ k j := by
  ext; simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.lift_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f g : J → C} [inst_2 : Catego
ryTheory.Limits.HasBiproduct f]   [inst_3 : CategoryTheory.Limits.HasBiproduct g
] {P : C} (k : (j : J) → P ⟶ f j) (p : (j : J) → f j ⟶ g j),   CategoryTheory.Ca
tegoryStruct.comp (CategoryTheory.Limits.biproduct.lift k) (CategoryTheory.Limit
s.biproduct.map p) =     CategoryTheory.Limits.biproduct.lift fun j => CategoryT
heory.CategoryStruct.comp (k j) (p j)
参数：k : (j : J) → P ⟶ f j；p : (j : J) → f j ⟶ g j；CategoryTheory.Limits.biproduct
.lift k；CategoryTheory.Limits.biproduct.map p；k j；p j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.map_π`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π_assoc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.lift_map {f g : J → C} [HasBiproduct f] [HasBiproduct g] {P : C}
    (k : ∀ j, P ⟶ f j) (p : ∀ j, f j ⟶ g j) :
    biproduct.lift k ≫ biproduct.map p = biproduct.lift fun j => k j ≫ p j := by
  ext; simp

/-- Given a collection of isomorphisms between corresponding summands of a pair of biproducts
indexed by the same type, we obtain an isomorphism between the biproducts. -/
@[simps]
/-
**CategoryTheory.Limits.biproduct.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         {f g :
 J → C} →           [inst_2 : CategoryTheory.Limits.HasBiproduct f] →           
  [inst_3 : CategoryTheory.Limits.HasBiproduct g] → ((b : J) → f b ≅ g b) → (⨁ f
 ≅ ⨁ g)
参数：(b : J) → f b ≅ g b；⨁ f ≅ ⨁ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a collection of isomorphisms between corresponding summands of a pair of b
iproducts
indexed by the same type, we obtain an isomorphism between the biproducts.
-/
def biproduct.mapIso {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ b, f b ≅ g b) :
    ⨁ f ≅ ⨁ g where
  hom := biproduct.map fun b => (p b).hom
  inv := biproduct.map fun b => (p b).inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.biproduct.map_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f g : J → C} [inst_2 : Catego
ryTheory.Limits.HasBiproduct f]   [inst_3 : CategoryTheory.Limits.HasBiproduct g
] (p : (j : J) → f j ⟶ g j) [∀ (j : J), CategoryTheory.Epi (p j)],   CategoryThe
ory.Epi (CategoryTheory.Limits.biproduct.map p)
参数：p : (j : J) → f j ⟶ g j；j : J；p j；CategoryTheory.Limits.biproduct.map p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproduct_of_hasBiproduct`：∀ {J : Type w} {C : 
Type uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory
.Limits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biproduct.map_π`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_assoc`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] [inst_2 : Decida…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biproduct.isoCoproduct_hom`：∀ {J : Type w} {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.isoCoproduct_inv`：∀ {J : Type w} {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc_assoc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map_assoc`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.
Limits.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_ne`：bicone_ι_π_ne {F : J -> C} (B : Bic
one F) {j j' : J} (h : j != j') : B.ι j ≫ B.π j' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_self`：bicone_ι_π_self {F : J -> C} (B :
 Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
（共 33 条，此处仅展示前 30 条）
-/
instance biproduct.map_epi {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Epi (p j)] : Epi (biproduct.map p) := by
  classical
  have : biproduct.map p =
      (biproduct.isoCoproduct _).hom ≫ Sigma.map p ≫ (biproduct.isoCoproduct _).inv := by
    ext
    simp only [map_π, isoCoproduct_hom, isoCoproduct_inv, Category.assoc, ι_desc_assoc, ι_π_assoc]
    split
    · subst_vars
      simp
    · simp_all
  rw [this]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Pi.map_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.Pi`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f g : J → C} [inst_2 : Catego
ryTheory.Limits.HasBiproduct f]   [inst_3 : CategoryTheory.Limits.HasBiproduct g
] (p : (j : J) → f j ⟶ g j) [∀ (j : J), CategoryTheory.Epi (p j)],   CategoryThe
ory.Epi (CategoryTheory.Limits.Pi.map p)
参数：p : (j : J) → f j ⟶ g j；j : J；p j；CategoryTheory.Limits.Pi.map p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.isoProduct_inv`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.isoProduct_hom`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_map_assoc`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.biproduct.map_epi`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance Pi.map_epi {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Epi (p j)] : Epi (Pi.map p) := by
  rw [show Pi.map p = (biproduct.isoProduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoProduct _).hom by aesop]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.biproduct.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f g : J → C} [inst_2 : Catego
ryTheory.Limits.HasBiproduct f]   [inst_3 : CategoryTheory.Limits.HasBiproduct g
] (p : (j : J) → f j ⟶ g j) [∀ (j : J), CategoryTheory.Mono (p j)],   CategoryTh
eory.Mono (CategoryTheory.Limits.biproduct.map p)
参数：p : (j : J) → f j ⟶ g j；j : J；p j；CategoryTheory.Limits.biproduct.map p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProduct_of_hasBiproduct`：∀ {J : Type w} {C : Ty
pe uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.isoProduct_hom`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.isoProduct_inv`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biproduct.map_π`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.Pi.map_mono`：∀ {β : Type w} {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits
.HasProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance biproduct.map_mono {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Mono (p j)] : Mono (biproduct.map p) := by
  rw [show biproduct.map p = (biproduct.isoProduct _).hom ≫ Pi.map p ≫
    (biproduct.isoProduct _).inv by aesop]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.Sigma.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.Sigma`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f g : J → C} [inst_2 : Catego
ryTheory.Limits.HasBiproduct f]   [inst_3 : CategoryTheory.Limits.HasBiproduct g
] (p : (j : J) → f j ⟶ g j) [∀ (j : J), CategoryTheory.Mono (p j)],   CategoryTh
eory.Mono (CategoryTheory.Limits.Sigma.map p)
参数：p : (j : J) → f j ⟶ g j；j : J；p j；CategoryTheory.Limits.Sigma.map p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproduct_of_hasBiproduct`：∀ {J : Type w} {C : 
Type uC} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory
.Limits.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.isoCoproduct_inv`：∀ {J : Type w} {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.biproduct.isoCoproduct_hom`：∀ {J : Type w} {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.map_desc`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map`：∀ {β : Type w} {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.biproduct.map_mono`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f g : J → C} [i…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance Sigma.map_mono {f g : J → C} [HasBiproduct f] [HasBiproduct g] (p : ∀ j, f j ⟶ g j)
    [∀ j, Mono (p j)] : Mono (Sigma.map p) := by
  rw [show Sigma.map p = (biproduct.isoCoproduct _).inv ≫ biproduct.map p ≫
    (biproduct.isoCoproduct _).hom by aesop]
  infer_instance

/-- Two biproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.

Unfortunately there are two natural ways to define each direction of this isomorphism
(because it is true for both products and coproducts separately).
We give the alternative definitions as lemmas below. -/
@[simps]
/-
**CategoryTheory.Limits.biproduct.whiskerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {K : Type u_1} →     {C : Type u} →       [inst : Categor
yTheory.Category.{v, u} C] →         [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] →           {f : J → C} →             {g : K → C} →               (e : 
J ≃ K) →                 ((j : J) → g (e j) ≅ f j) →                   [inst_2 :
 CategoryTheory.Limits.HasBiproduct f] →                     [inst_3 : CategoryT
heory.Limits.HasBiproduct g] → ⨁ f ≅ ⨁ g
参数：e : J ≃ K；(j : J) → g (e j) ≅ f j。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Two biproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.

Unfortunately there are two natural ways to define each direction of this isomor
phism
(because it is true for both products and coproducts separately).
We give the alternative definitions as lemmas below.
-/
def biproduct.whiskerEquiv {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasBiproduct f] [HasBiproduct g] : ⨁ f ≅ ⨁ g where
  hom := biproduct.desc fun j => (w j).inv ≫ biproduct.ι g (e j)
  inv := biproduct.desc fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom ≫ biproduct.ι f _
/-
**CategoryTheory.Limits.biproduct.whiskerEquiv_hom_eq_lift** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {K : Type u_1} {C : Type u} [inst : CategoryTheory.Category
.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} {g 
: K → C} (e : J ≃ K) (w : (j : J) → g (e j) ≅ f j)   [inst_2 : CategoryTheory.Li
mits.HasBiproduct f] [inst_3 : CategoryTheory.Limits.HasBiproduct g],   (Categor
yTheory.Limits.biproduct.whiskerEquiv e w).hom =     CategoryTheory.Limits.bipro
duct.lift fun k =>       CategoryTheory.CategoryStruct.comp (CategoryTheory.Limi
ts.biproduct.π f (e.symm k))         (CategoryTheory.CategoryStruct.comp (w (e.s
ymm k)).inv (CategoryTheory.eqToHom ⋯))
参数：e : J ≃ K；w : (j : J) → g (e j) ≅ f j；CategoryTheory.Limits.biproduct.whisker
Equiv e w；CategoryTheory.Limits.biproduct.π f (e.symm k)；CategoryTheory.Category
Struct.comp (w (e.symm k)).inv (CategoryTheory.eqToHom ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.whiskerEquiv_hom`：∀ {J : Type w} {K : Ty
pe u_1} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.Limits.HasZeroMorphisms C] {…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc_assoc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_self`：bicone_ι_π_self {F : J -> C} (B :
 Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.eqToHom_iso_inv_naturality`：eqToHom_iso_inv_naturality {f
 g : β -> C} (z : forall b, f b ≅ g b) {j j' : β} (w : j = j') : (z j).inv ≫ eqT
oHom (by simp [w]) = eqToHom (b…
· 使用定理 `CategoryTheory.eqToHom_naturality_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {β : Sort u_1} {f g : β → C} (z : (b : β) → f b ⟶ g
 b)   {j j' : β} (w : j = j')…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_self_assoc`：∀ {J : Type w} {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits
.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_ne`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] (f : J → C) [ins…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_ne_assoc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma biproduct.whiskerEquiv_hom_eq_lift {f : J → C} {g : K → C} (e : J ≃ K)
    (w : ∀ j, g (e j) ≅ f j) [HasBiproduct f] [HasBiproduct g] :
    (biproduct.whiskerEquiv e w).hom =
      biproduct.lift fun k => biproduct.π f (e.symm k) ≫ (w _).inv ≫ eqToHom (by simp) := by
  simp only [whiskerEquiv_hom]
  ext k j
  by_cases h : k = e j
  · subst h
    simp
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne, biproduct.ι_π_ne_assoc]
    · simp
    · rintro rfl
      simp at h
    · exact Ne.symm h
/-
**CategoryTheory.Limits.biproduct.whiskerEquiv_inv_eq_lift** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {K : Type u_1} {C : Type u} [inst : CategoryTheory.Category
.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {f : J → C} {g 
: K → C} (e : J ≃ K) (w : (j : J) → g (e j) ≅ f j)   [inst_2 : CategoryTheory.Li
mits.HasBiproduct f] [inst_3 : CategoryTheory.Limits.HasBiproduct g],   (Categor
yTheory.Limits.biproduct.whiskerEquiv e w).inv =     CategoryTheory.Limits.bipro
duct.lift fun j =>       CategoryTheory.CategoryStruct.comp (CategoryTheory.Limi
ts.biproduct.π g (e j)) (w j).hom
参数：e : J ≃ K；w : (j : J) → g (e j) ≅ f j；CategoryTheory.Limits.biproduct.whisker
Equiv e w；CategoryTheory.Limits.biproduct.π g (e j)；w j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.whiskerEquiv_inv`：∀ {J : Type w} {K : Ty
pe u_1} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.Limits.HasZeroMorphisms C] {…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc_assoc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] {f : J → C} [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `CategoryTheory.eqToHom_iso_hom_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {β : Sort u_1} {f g : β → C} (z : (b : β) →
 f b ≅ g b)   {j j' : β} (w : j = j')…
· 使用定理 `CategoryTheory.Limits.biproduct.eqToHom_comp_ι`：∀ {J : Type w} {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.
HasZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_self`：bicone_ι_π_self {F : J -> C} (B :
 Bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.bicone_ι_π_self_assoc`：∀ {J : Type w} {C : Type uC
} [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits
.HasZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_ne`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] (f : J → C) [ins…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_ne_assoc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma biproduct.whiskerEquiv_inv_eq_lift {f : J → C} {g : K → C} (e : J ≃ K)
    (w : ∀ j, g (e j) ≅ f j) [HasBiproduct f] [HasBiproduct g] :
    (biproduct.whiskerEquiv e w).inv =
      biproduct.lift fun j => biproduct.π g (e j) ≫ (w j).hom := by
  simp only [whiskerEquiv_inv]
  ext j k
  by_cases h : k = e j
  · subst h
    simp only [ι_desc_assoc, ← eqToHom_iso_hom_naturality_assoc w (e.symm_apply_apply j).symm,
      Equiv.symm_apply_apply, eqToHom_comp_ι, Category.assoc, bicone_ι_π_self, Category.comp_id,
      lift_π, bicone_ι_π_self_assoc]
  · simp only [ι_desc_assoc, Category.assoc, lift_π]
    rw [biproduct.ι_π_ne, biproduct.ι_π_ne_assoc]
    · simp
    · exact h
    · rintro rfl
      simp at h

set_option backward.isDefEq.respectTransparency.types false in
attribute [local simp] Sigma.forall in
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasBiproduct (g i)] [HasBiproduct fun i => ⨁ g i] :
    HasBiproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_biproduct := Nonempty.intro
    { bicone :=
      { pt := ⨁ fun i => ⨁ g i
        ι := fun X => biproduct.ι (g X.1) X.2 ≫ biproduct.ι (fun i => ⨁ g i) X.1
        π := fun X => biproduct.π (fun i => ⨁ g i) X.1 ≫ biproduct.π (g X.1) X.2
        ι_π := fun ⟨j, x⟩ ⟨j', y⟩ => by
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            simp
          · simp only [Sigma.mk.inj_iff, not_and] at h
            by_cases w : j = j'
            · cases w
              simp only [heq_eq_eq, forall_true_left] at h
              simp [biproduct.ι_π_ne _ h]
            · simp [biproduct.ι_π_ne_assoc _ w] }
      isBilimit :=
      { isLimit := Fan.IsLimit.mk _
          (fun s => biproduct.lift fun b => biproduct.lift fun c => s.proj ⟨b, c⟩)
        isColimit := Cofan.IsColimit.mk _
          (fun s => biproduct.desc fun b => biproduct.desc fun c => s.inj ⟨b, c⟩) } }

/-- An iterated biproduct is a biproduct over a sigma type. -/
@[simps]
/-
**CategoryTheory.Limits.biproductBiproductIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：biproductBiproductIso {ι} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C) [fo
rall i, HasBiproduct (g i)] [HasBiproduct fun i => ⨁ g i] : (⨁ fun i => ⨁ g i) ≅
 (⨁ fun p : Σ i, f i => g p.1 p.2) where hom
参数：f : ι -> Type*；g : (i : ι) -> (f i) -> C；g i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasBiproductSigmaFstSndOfBiproduct`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   {ι : Type u_3} (f : ι → Type …

--- 原说明 ---
An iterated biproduct is a biproduct over a sigma type.
-/
def biproductBiproductIso {ι} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasBiproduct (g i)] [HasBiproduct fun i => ⨁ g i] :
    (⨁ fun i => ⨁ g i) ≅ (⨁ fun p : Σ i, f i => g p.1 p.2) where
  hom := biproduct.lift fun ⟨i, x⟩ => biproduct.π _ i ≫ biproduct.π _ x
  inv := biproduct.lift fun i => biproduct.lift fun x => biproduct.π _ (⟨i, x⟩ : Σ i, f i)

section πKernel

section

variable (f : J → C) [HasBiproduct f]
variable (p : J → Prop) [HasBiproduct (Subtype.restrict p f)]

/-- The canonical morphism from the biproduct over a restricted index type to the biproduct of
the full index type. -/
/-
**CategoryTheory.Limits.biproduct.fromSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (f : J
 → C) →           [inst_2 : CategoryTheory.Limits.HasBiproduct f] →             
(p : J → Prop) →               [inst_3 : CategoryTheory.Limits.HasBiproduct (Sub
type.restrict p f)] → ⨁ Subtype.restrict p f ⟶ ⨁ f
参数：f : J → C；p : J → Prop；Subtype.restrict p f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from the biproduct over a restricted index type to the bi
product of
the full index type.
-/
def biproduct.fromSubtype : ⨁ Subtype.restrict p f ⟶ ⨁ f :=
  biproduct.desc fun j => biproduct.ι _ j.val

/-- The canonical morphism from a biproduct to the biproduct over a restriction of its index
type. -/
/-
**CategoryTheory.Limits.biproduct.toSubtype** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (f : J
 → C) →           [inst_2 : CategoryTheory.Limits.HasBiproduct f] →             
(p : J → Prop) →               [inst_3 : CategoryTheory.Limits.HasBiproduct (Sub
type.restrict p f)] → ⨁ f ⟶ ⨁ Subtype.restrict p f
参数：f : J → C；p : J → Prop；Subtype.restrict p f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from a biproduct to the biproduct over a restriction of i
ts index
type.
-/
def biproduct.toSubtype : ⨁ f ⟶ ⨁ Subtype.restrict p f :=
  biproduct.lift fun _ => biproduct.π _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.fromSubtype_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.fromSubtype_π [DecidablePred p] (j : J) :
    biproduct.fromSubtype f p ≫ biproduct.π f j =
      if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
  classical
  ext i
  rw [biproduct.fromSubtype, biproduct.ι_desc_assoc, biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show (i : J) ≠ j from fun h₂ => h (h₂ ▸ i.2)), comp_zero]
/-
**CategoryTheory.Limits.biproduct.fromSubtype_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (f : J → C) [inst_2 : Category
Theory.Limits.HasBiproduct f]   (p : J → Prop) [inst_3 : CategoryTheory.Limits.H
asBiproduct (Subtype.restrict p f)] [inst_4 : DecidablePred p],   CategoryTheory
.Limits.biproduct.fromSubtype f p =     CategoryTheory.Limits.biproduct.lift fun
 j =>       if h : p j then CategoryTheory.Limits.biproduct.π (Subtype.restrict 
p f) ⟨j, h⟩ else 0
参数：f : J → C；p : J → Prop；Subtype.restrict p f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.fromSubtype_π`：∀ {J : Type w} {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem biproduct.fromSubtype_eq_lift [DecidablePred p] :
    biproduct.fromSubtype f p =
      biproduct.lift fun j => if h : p j then biproduct.π (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext _ _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc] -- Not `@[simp]` because `simp` can prove this
/-
**CategoryTheory.Limits.biproduct.fromSubtype_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.fromSubtype_π_subtype (j : Subtype p) :
    biproduct.fromSubtype f p ≫ biproduct.π f j = biproduct.π (Subtype.restrict p f) j := by
  classical
  ext
  rw [biproduct.fromSubtype, biproduct.ι_desc_assoc, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.toSubtype_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.toSubtype_π (j : Subtype p) :
    biproduct.toSubtype f p ≫ biproduct.π (Subtype.restrict p f) j = biproduct.π f j :=
  biproduct.lift_π _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_toSubtype [DecidablePred p] (j : J) :
    biproduct.ι f j ≫ biproduct.toSubtype f p =
      if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 := by
  classical
  ext i
  rw [biproduct.toSubtype, Category.assoc, biproduct.lift_π, biproduct.ι_π]
  by_cases h : p j
  · rw [dif_pos h, biproduct.ι_π]
    split_ifs with h₁ h₂ h₂
    exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]
  · rw [dif_neg h, dif_neg (show j ≠ i from fun h₂ => h (h₂.symm ▸ i.2)), zero_comp]
/-
**CategoryTheory.Limits.biproduct.toSubtype_eq_desc** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (f : J → C) [inst_2 : Category
Theory.Limits.HasBiproduct f]   (p : J → Prop) [inst_3 : CategoryTheory.Limits.H
asBiproduct (Subtype.restrict p f)] [inst_4 : DecidablePred p],   CategoryTheory
.Limits.biproduct.toSubtype f p =     CategoryTheory.Limits.biproduct.desc fun j
 =>       if h : p j then CategoryTheory.Limits.biproduct.ι (Subtype.restrict p 
f) ⟨j, h⟩ else 0
参数：f : J → C；p : J → Prop；Subtype.restrict p f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_toSubtype`：∀ {J : Type w} {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem biproduct.toSubtype_eq_desc [DecidablePred p] :
    biproduct.toSubtype f p =
      biproduct.desc fun j => if h : p j then biproduct.ι (Subtype.restrict p f) ⟨j, h⟩ else 0 :=
  biproduct.hom_ext' _ _ (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_toSubtype_subtype (j : Subtype p) :
    biproduct.ι f j ≫ biproduct.toSubtype f p = biproduct.ι (Subtype.restrict p f) j := by
  classical
  ext
  rw [biproduct.toSubtype, Category.assoc, biproduct.lift_π, biproduct.ι_π, biproduct.ι_π]
  split_ifs with h₁ h₂ h₂
  exacts [rfl, False.elim (h₂ (Subtype.ext h₁)), False.elim (h₁ (congr_arg Subtype.val h₂)), rfl]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_fromSubtype (j : Subtype p) :
    biproduct.ι (Subtype.restrict p f) j ≫ biproduct.fromSubtype f p = biproduct.ι f j :=
  biproduct.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.fromSubtype_toSubtype** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (f : J → C) [inst_2 : Category
Theory.Limits.HasBiproduct f]   (p : J → Prop) [inst_3 : CategoryTheory.Limits.H
asBiproduct (Subtype.restrict p f)],   CategoryTheory.CategoryStruct.comp (Categ
oryTheory.Limits.biproduct.fromSubtype f p)       (CategoryTheory.Limits.biprodu
ct.toSubtype f p) =     CategoryTheory.CategoryStruct.id (⨁ Subtype.restrict p f
)
参数：f : J → C；p : J → Prop；Subtype.restrict p f；CategoryTheory.Limits.biproduct.f
romSubtype f p；CategoryTheory.Limits.biproduct.toSubtype f p；⨁ Subtype.restrict 
p f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.toSubtype_π`：∀ {J : Type w} {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.fromSubtype_π_subtype`：∀ {J : Type w} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem biproduct.fromSubtype_toSubtype :
    biproduct.fromSubtype f p ≫ biproduct.toSubtype f p = 𝟙 (⨁ Subtype.restrict p f) := by
  refine biproduct.hom_ext _ _ fun j => ?_
  rw [Category.assoc, biproduct.toSubtype_π, biproduct.fromSubtype_π_subtype, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.toSubtype_fromSubtype** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (f : J → C) [inst_2 : Category
Theory.Limits.HasBiproduct f]   (p : J → Prop) [inst_3 : CategoryTheory.Limits.H
asBiproduct (Subtype.restrict p f)] [inst_4 : DecidablePred p],   CategoryTheory
.CategoryStruct.comp (CategoryTheory.Limits.biproduct.toSubtype f p)       (Cate
goryTheory.Limits.biproduct.fromSubtype f p) =     CategoryTheory.Limits.biprodu
ct.map fun j => if p j then CategoryTheory.CategoryStruct.id (f j) else 0
参数：f : J → C；p : J → Prop；Subtype.restrict p f；CategoryTheory.Limits.biproduct.t
oSubtype f p；CategoryTheory.Limits.biproduct.fromSubtype f p；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.fromSubtype_π`：∀ {J : Type w} {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Limits.biproduct.toSubtype_π`：∀ {J : Type w} {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C] (f : J → C) [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.map_π`：∀ {J : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C] {f g : J → C} [i…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem biproduct.toSubtype_fromSubtype [DecidablePred p] :
    biproduct.toSubtype f p ≫ biproduct.fromSubtype f p =
      biproduct.map fun j => if p j then 𝟙 (f j) else 0 := by
  ext1 i
  by_cases h : p i
  · simp [h]
  · simp [h]

end

section

variable (f : J → C) (i : J) [HasBiproduct f] [HasBiproduct (Subtype.restrict (fun j => j ≠ i) f)]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The kernel of `biproduct.π f i` is the inclusion from the biproduct which omits `i`
from the index set `J` into the biproduct over `J`. -/
/-
**CategoryTheory.Limits.biproduct.isLimitFromSubtype** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (f : J
 → C) →           (i : J) →             [inst_2 : CategoryTheory.Limits.HasBipro
duct f] →               [inst_3 : CategoryTheory.Limits.HasBiproduct (Subtype.re
strict (fun j => j ≠ i) f)] →                 CategoryTheory.Limits.IsLimit     
              (CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limits.bipro
duct.fromSubtype f fun j => j ≠ i)                     ⋯)
参数：f : J → C；i : J；Subtype.restrict (fun j => j ≠ i) f；CategoryTheory.Limits.Ker
nelFork.ofι (CategoryTheory.Limits.biproduct.fromSubtype f fun j => j ≠ i)      
               ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `biproduct.π f i` is the inclusion from the biproduct which omits 
`i`
from the index set `J` into the biproduct over `J`.
-/
def biproduct.isLimitFromSubtype :
    IsLimit (KernelFork.ofι (biproduct.fromSubtype f fun j => j ≠ i) (by simp) :
    KernelFork (biproduct.π f i)) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ biproduct.toSubtype _ _, by
      apply biproduct.hom_ext; intro j
      rw [KernelFork.ι_ofι, Category.assoc, Category.assoc,
        biproduct.toSubtype_fromSubtype_assoc, biproduct.map_π]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), comp_zero, comp_zero, KernelFork.condition]
      · rw [if_pos (Ne.symm h), Category.comp_id], by
      intro m hm
      rw [← hm, KernelFork.ι_ofι, Category.assoc, biproduct.fromSubtype_toSubtype]
      exact (Category.comp_id _).symm⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasKernel (biproduct.π f i) :=
  HasLimit.mk ⟨_, biproduct.isLimitFromSubtype f i⟩

/-- The kernel of `biproduct.π f i` is `⨁ Subtype.restrict {i}ᶜ f`. -/
@[simps!]
/-
**CategoryTheory.Limits.kernelBiproduct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of `biproduct.π f i` is `⨁ Subtype.restrict {i}ᶜ f`.
-/
def kernelBiproductπIso : kernel (biproduct.π f i) ≅ ⨁ Subtype.restrict (fun j => j ≠ i) f :=
  limit.isoLimitCone ⟨_, biproduct.isLimitFromSubtype f i⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The cokernel of `biproduct.ι f i` is the projection from the biproduct over the index set `J`
onto the biproduct omitting `i`. -/
/-
**CategoryTheory.Limits.biproduct.isColimitToSubtype** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (f : J
 → C) →           (i : J) →             [inst_2 : CategoryTheory.Limits.HasBipro
duct f] →               [inst_3 : CategoryTheory.Limits.HasBiproduct (Subtype.re
strict (fun j => j ≠ i) f)] →                 CategoryTheory.Limits.IsColimit   
                (CategoryTheory.Limits.CokernelCofork.ofπ (CategoryTheory.Limits
.biproduct.toSubtype f fun j => j ≠ i)                     ⋯)
参数：f : J → C；i : J；Subtype.restrict (fun j => j ≠ i) f；CategoryTheory.Limits.Cok
ernelCofork.ofπ (CategoryTheory.Limits.biproduct.toSubtype f fun j => j ≠ i)    
                 ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `biproduct.ι f i` is the projection from the biproduct over the 
index set `J`
onto the biproduct omitting `i`.
-/
def biproduct.isColimitToSubtype :
    IsColimit (CokernelCofork.ofπ (biproduct.toSubtype f fun j => j ≠ i) (by simp) :
    CokernelCofork (biproduct.ι f i)) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨biproduct.fromSubtype _ _ ≫ s.π, by
      apply biproduct.hom_ext'; intro j
      rw [CokernelCofork.π_ofπ, biproduct.toSubtype_fromSubtype_assoc, biproduct.ι_map_assoc]
      rcases Classical.em (i = j) with (rfl | h)
      · rw [if_neg (Classical.not_not.2 rfl), zero_comp, CokernelCofork.condition]
      · rw [if_pos (Ne.symm h), Category.id_comp], by
      intro m hm
      rw [← hm, CokernelCofork.π_ofπ, ← Category.assoc, biproduct.fromSubtype_toSubtype]
      exact (Category.id_comp _).symm⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCokernel (biproduct.ι f i) :=
  HasColimit.mk ⟨_, biproduct.isColimitToSubtype f i⟩

/-- The cokernel of `biproduct.ι f i` is `⨁ Subtype.restrict {i}ᶜ f`. -/
@[simps!]
/-
**CategoryTheory.Limits.cokernelBiproduct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of `biproduct.ι f i` is `⨁ Subtype.restrict {i}ᶜ f`.
-/
def cokernelBiproductιIso : cokernel (biproduct.ι f i) ≅ ⨁ Subtype.restrict (fun j => j ≠ i) f :=
  colimit.isoColimitCocone ⟨_, biproduct.isColimitToSubtype f i⟩

end

section

-- Per https://github.com/leanprover-community/mathlib3/pull/15067, we only allow indexing in `Type 0` here.
variable {K : Type} [Finite K] [HasFiniteBiproducts C] (f : K → C)

set_option backward.isDefEq.respectTransparency false in
/-- The limit cone exhibiting `⨁ Subtype.restrict pᶜ f` as the kernel of
`biproduct.toSubtype f p` -/
@[simps]
/-
**CategoryTheory.Limits.kernelForkBiproductToSubtype** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：kernelForkBiproductToSubtype (p : K -> Prop) : LimitCone (parallelPair (bi
product.toSubtype f p) 0) where cone
参数：p : K -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone exhibiting `⨁ Subtype.restrict pᶜ f` as the kernel of
`biproduct.toSubtype f p`
-/
def kernelForkBiproductToSubtype (p : K → Prop) :
    LimitCone (parallelPair (biproduct.toSubtype f p) 0) where
  cone :=
    KernelFork.ofι (biproduct.fromSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, biproduct.ι_fromSubtype_assoc, biproduct.ι_toSubtype_assoc,
          comp_zero, zero_comp]
        rw [dif_neg k.2]
        simp only [zero_comp])
  isLimit :=
    KernelFork.IsLimit.ofι _ _ (fun {_} g _ => g ≫ biproduct.toSubtype f pᶜ)
      (by
        classical
        intro W' g' w
        ext j
        simp only [Category.assoc, biproduct.toSubtype_fromSubtype, Pi.compl_apply,
          biproduct.map_π]
        split_ifs with h
        · simp
        · replace w := w =≫ biproduct.π _ ⟨j, not_not.mp h⟩
          simpa using w.symm)
      (by cat_disch)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : K → Prop) : HasKernel (biproduct.toSubtype f p) :=
  HasLimit.mk (kernelForkBiproductToSubtype f p)

/-- The kernel of `biproduct.toSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
/-
**CategoryTheory.Limits.kernelBiproductToSubtypeIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：kernelBiproductToSubtypeIso (p : K -> Prop) : kernel (biproduct.toSubtype 
f p) ≅ ⨁ Subtype.restrict pᶜ f
参数：p : K -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasKernelToSubtype`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C] {K : Type}   [inst_2 : Finite K…

--- 原说明 ---
The kernel of `biproduct.toSubtype f p` is `⨁ Subtype.restrict pᶜ f`.
-/
def kernelBiproductToSubtypeIso (p : K → Prop) :
    kernel (biproduct.toSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  limit.isoLimitCone (kernelForkBiproductToSubtype f p)

set_option backward.isDefEq.respectTransparency false in
/-- The colimit cocone exhibiting `⨁ Subtype.restrict pᶜ f` as the cokernel of
`biproduct.fromSubtype f p` -/
@[simps]
/-
**CategoryTheory.Limits.cokernelCoforkBiproductFromSubtype** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：cokernelCoforkBiproductFromSubtype (p : K -> Prop) : ColimitCocone (parall
elPair (biproduct.fromSubtype f p) 0) where cocone
参数：p : K -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone exhibiting `⨁ Subtype.restrict pᶜ f` as the cokernel of
`biproduct.fromSubtype f p`
-/
def cokernelCoforkBiproductFromSubtype (p : K → Prop) :
    ColimitCocone (parallelPair (biproduct.fromSubtype f p) 0) where
  cocone :=
    CokernelCofork.ofπ (biproduct.toSubtype f pᶜ)
      (by
        classical
        ext j k
        simp only [Category.assoc, Pi.compl_apply, biproduct.ι_fromSubtype_assoc,
          biproduct.ι_toSubtype_assoc, comp_zero, zero_comp]
        rw [dif_neg]
        · simp only [zero_comp]
        · exact not_not.mpr k.2)
  isColimit :=
    CokernelCofork.IsColimit.ofπ _ _ (fun {_} g _ => biproduct.fromSubtype f pᶜ ≫ g)
      (by
        classical
        intro W g' w
        ext j
        simp only [biproduct.toSubtype_fromSubtype_assoc, Pi.compl_apply, biproduct.ι_map_assoc]
        split_ifs with h
        · simp
        · replace w := biproduct.ι _ (⟨j, not_not.mp h⟩ : Subtype p) ≫= w
          simpa using w.symm)
      (by cat_disch)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : K → Prop) : HasCokernel (biproduct.fromSubtype f p) :=
  HasColimit.mk (cokernelCoforkBiproductFromSubtype f p)

/-- The cokernel of `biproduct.fromSubtype f p` is `⨁ Subtype.restrict pᶜ f`. -/
@[simps!]
/-
**CategoryTheory.Limits.cokernelBiproductFromSubtypeIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：cokernelBiproductFromSubtypeIso (p : K -> Prop) : cokernel (biproduct.from
Subtype f p) ≅ ⨁ Subtype.restrict pᶜ f
参数：p : K -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCokernelFromSubtype`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C] {K : Type}   [inst_2 : Finite K…

--- 原说明 ---
The cokernel of `biproduct.fromSubtype f p` is `⨁ Subtype.restrict pᶜ f`.
-/
def cokernelBiproductFromSubtypeIso (p : K → Prop) :
    cokernel (biproduct.fromSubtype f p) ≅ ⨁ Subtype.restrict pᶜ f :=
  colimit.isoColimitCocone (cokernelCoforkBiproductFromSubtype f p)

end

end πKernel

section FiniteBiproducts

variable {J : Type} [Finite J] {K : Type} [Finite K] {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasFiniteBiproducts C] {f : J → C} {g : K → C}

/-- Convert a (dependently typed) matrix to a morphism of biproducts. -/
/-
**CategoryTheory.Limits.biproduct.matrix** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.biproduct`。
形式化陈述：{J : Type} →   [inst : Finite J] →     {K : Type} →       [inst_1 : Finite
 K] →         {C : Type u} →           [inst_2 : CategoryTheory.Category.{v, u} 
C] →             [inst_3 : CategoryTheory.Limits.HasZeroMorphisms C] →          
     [inst_4 : CategoryTheory.Limits.HasFiniteBiproducts C] →                 {f
 : J → C} → {g : K → C} → ((j : J) → (k : K) → f j ⟶ g k) → (⨁ f ⟶ ⨁ g)
参数：(j : J) → (k : K) → f j ⟶ g k；⨁ f ⟶ ⨁ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a (dependently typed) matrix to a morphism of biproducts.
-/
def biproduct.matrix (m : ∀ j k, f j ⟶ g k) : ⨁ f ⟶ ⨁ g :=
  biproduct.desc fun j => biproduct.lift fun k => m j k

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.matrix_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.matrix_π (m : ∀ j k, f j ⟶ g k) (k : K) :
    biproduct.matrix m ≫ biproduct.π g k = biproduct.desc fun j => m j k := by
  ext
  simp [biproduct.matrix]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct.ι_matrix (m : ∀ j k, f j ⟶ g k) (j : J) :
    biproduct.ι f j ≫ biproduct.matrix m = biproduct.lift fun k => m j k := by
  simp [biproduct.matrix]

/-- Extract the matrix components from a morphism of biproducts. -/
/-
**CategoryTheory.Limits.biproduct.components** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.biproduct`。
形式化陈述：{J : Type} →   [inst : Finite J] →     {K : Type} →       [inst_1 : Finite
 K] →         {C : Type u} →           [inst_2 : CategoryTheory.Category.{v, u} 
C] →             [inst_3 : CategoryTheory.Limits.HasZeroMorphisms C] →          
     [inst_4 : CategoryTheory.Limits.HasFiniteBiproducts C] →                 {f
 : J → C} → {g : K → C} → (⨁ f ⟶ ⨁ g) → (j : J) → (k : K) → f j ⟶ g k
参数：⨁ f ⟶ ⨁ g；j : J；k : K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the matrix components from a morphism of biproducts.
-/
def biproduct.components (m : ⨁ f ⟶ ⨁ g) (j : J) (k : K) : f j ⟶ g k :=
  biproduct.ι f j ≫ m ≫ biproduct.π g k

@[simp]
/-
**CategoryTheory.Limits.biproduct.matrix_components** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type} [inst : Finite J] {K : Type} [inst_1 : Finite K] {C : Type u}
 [inst_2 : CategoryTheory.Category.{v, u} C]   [inst_3 : CategoryTheory.Limits.H
asZeroMorphisms C] [inst_4 : CategoryTheory.Limits.HasFiniteBiproducts C] {f : J
 → C}   {g : K → C} (m : (j : J) → (k : K) → f j ⟶ g k) (j : J) (k : K),   Categ
oryTheory.Limits.biproduct.components (CategoryTheory.Limits.biproduct.matrix m)
 j k = m j k
参数：m : (j : J) → (k : K) → f j ⟶ g k；j : J；k : K；CategoryTheory.Limits.biproduct
.matrix m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π`：∀ {J : Type} [inst : Finite J]
 {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Category.{
v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.matrix_components (m : ∀ j k, f j ⟶ g k) (j : J) (k : K) :
    biproduct.components (biproduct.matrix m) j k = m j k := by simp [biproduct.components]

@[simp]
/-
**CategoryTheory.Limits.biproduct.components_matrix** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type} [inst : Finite J] {K : Type} [inst_1 : Finite K] {C : Type u}
 [inst_2 : CategoryTheory.Category.{v, u} C]   [inst_3 : CategoryTheory.Limits.H
asZeroMorphisms C] [inst_4 : CategoryTheory.Limits.HasFiniteBiproducts C] {f : J
 → C}   {g : K → C} (m : ⨁ f ⟶ ⨁ g),   (CategoryTheory.Limits.biproduct.matrix f
un j k => CategoryTheory.Limits.biproduct.components m j k) = m
参数：m : ⨁ f ⟶ ⨁ g；CategoryTheory.Limits.biproduct.matrix fun j k => CategoryTheor
y.Limits.biproduct.components m j k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.matrix_π`：∀ {J : Type} [inst : Finite J]
 {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.Category.{
v, u} C]   [inst_3 : CategoryT…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biproduct.components_matrix (m : ⨁ f ⟶ ⨁ g) :
    (biproduct.matrix fun j k => biproduct.components m j k) = m := by
  ext
  simp [biproduct.components]

/-- Morphisms between direct sums are matrices. -/
@[simps]
/-
**CategoryTheory.Limits.biproduct.matrixEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.biproduct`。
形式化陈述：{J : Type} →   [inst : Finite J] →     {K : Type} →       [inst_1 : Finite
 K] →         {C : Type u} →           [inst_2 : CategoryTheory.Category.{v, u} 
C] →             [inst_3 : CategoryTheory.Limits.HasZeroMorphisms C] →          
     [inst_4 : CategoryTheory.Limits.HasFiniteBiproducts C] →                 {f
 : J → C} → {g : K → C} → (⨁ f ⟶ ⨁ g) ≃ ((j : J) → (k : K) → f j ⟶ g k)
参数：⨁ f ⟶ ⨁ g；(j : J) → (k : K) → f j ⟶ g k。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.components_matrix`：∀ {J : Type} [inst : 
Finite J] {K : Type} [inst_1 : Finite K] {C : Type u} [inst_2 : CategoryTheory.C
ategory.{v, u} C]   [inst_3 : CategoryT…

--- 原说明 ---
Morphisms between direct sums are matrices.
-/
def biproduct.matrixEquiv : (⨁ f ⟶ ⨁ g) ≃ ∀ j k, f j ⟶ g k where
  toFun := biproduct.components
  invFun := biproduct.matrix
  left_inv := biproduct.components_matrix
  right_inv m := by
    ext
    apply biproduct.matrix_components

end FiniteBiproducts

variable {J : Type w}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance biproduct.ι_mono (f : J → C) [HasBiproduct f] (b : J) : IsSplitMono (biproduct.ι f b) :=
  (biproduct.bicone f).instIsSplitMonoι b
/-
**CategoryTheory.Limits.biproduct.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance biproduct.π_epi (f : J → C) [HasBiproduct f] (b : J) : IsSplitEpi (biproduct.π f b) :=
  (biproduct.bicone f).instIsSplitEpiπ b

/-- Auxiliary lemma for `biproduct.uniqueUpToIso`. -/
/-
**CategoryTheory.Limits.biproduct.conePointUniqueUpToIso_hom** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (f : J → C) [inst_2 : Category
Theory.Limits.HasBiproduct f]   {b : CategoryTheory.Limits.Bicone f} (hb : b.IsB
ilimit),   (hb.isLimit.conePointUniqueUpToIso (CategoryTheory.Limits.biproduct.i
sLimit f)).hom =     CategoryTheory.Limits.biproduct.lift b.π
参数：f : J → C；hb : b.IsBilimit；hb.isLimit.conePointUniqueUpToIso (CategoryTheory.
Limits.biproduct.isLimit f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `biproduct.uniqueUpToIso`.
-/
theorem biproduct.conePointUniqueUpToIso_hom (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).hom = biproduct.lift b.π :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary lemma for `biproduct.uniqueUpToIso`. -/
/-
**CategoryTheory.Limits.biproduct.conePointUniqueUpToIso_inv** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.biproduct`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [i
nst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (f : J → C) [inst_2 : Category
Theory.Limits.HasBiproduct f]   {b : CategoryTheory.Limits.Bicone f} (hb : b.IsB
ilimit),   (hb.isLimit.conePointUniqueUpToIso (CategoryTheory.Limits.biproduct.i
sLimit f)).inv =     CategoryTheory.Limits.biproduct.desc b.ι
参数：f : J → C；hb : b.IsBilimit；hb.isLimit.conePointUniqueUpToIso (CategoryTheory.
Limits.biproduct.isLimit f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `CategoryTheory.Limits.Bicone.toCone_π_app`：∀ {J : Type w} {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C] {F : J → C} …
· 使用定理 `CategoryTheory.Limits.biproduct.bicone_π`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] (f : J → C) [ins…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.Limits.Bicone.ι_π`：∀ {J : Type w} {C : Type uC} [inst : C
ategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C] {F : J → C} …

--- 原说明 ---
Auxiliary lemma for `biproduct.uniqueUpToIso`.
-/
theorem biproduct.conePointUniqueUpToIso_inv (f : J → C) [HasBiproduct f] {b : Bicone f}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (biproduct.isLimit _)).inv = biproduct.desc b.ι := by
  classical
  refine biproduct.hom_ext' _ _ fun j => hb.isLimit.hom_ext fun j' => ?_
  rw [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp, Bicone.toCone_π_app,
    biproduct.bicone_π, biproduct.ι_desc, biproduct.ι_π, b.toCone_π_app, b.ι_π]

set_option backward.isDefEq.respectTransparency.types false in
/-- Biproducts are unique up to isomorphism. This already follows because bilimits are limits,
but in the case of biproducts we can give an isomorphism with particularly nice definitional
properties, namely that `biproduct.lift b.π` and `biproduct.desc b.ι` are inverses of each
other. -/
@[simps]
/-
**CategoryTheory.Limits.biproduct.uniqueUpToIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.biproduct`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] →         (f : J
 → C) →           [inst_2 : CategoryTheory.Limits.HasBiproduct f] →             
{b : CategoryTheory.Limits.Bicone f} → b.IsBilimit → (b.pt ≅ ⨁ f)
参数：f : J → C；b.pt ≅ ⨁ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Biproducts are unique up to isomorphism. This already follows because bilimits a
re limits,
but in the case of biproducts we can give an isomorphism with particularly nice 
definitional
properties, namely that `biproduct.lift b.π` and `biproduct.desc b.ι` are invers
es of each
other.
-/
def biproduct.uniqueUpToIso (f : J → C) [HasBiproduct f] {b : Bicone f} (hb : b.IsBilimit) :
    b.pt ≅ ⨁ f where
  hom := biproduct.lift b.π
  inv := biproduct.desc b.ι
  hom_inv_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb, ←
      biproduct.conePointUniqueUpToIso_inv f hb, Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biproduct.conePointUniqueUpToIso_hom f hb, ←
      biproduct.conePointUniqueUpToIso_inv f hb, Iso.inv_hom_id]

variable (C)

-- see Note [lower instance priority]
/-- A category with finite biproducts has a zero object. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with finite biproducts has a zero object.
-/
instance (priority := 100) hasZeroObject_of_hasFiniteBiproducts [HasFiniteBiproducts C] :
    HasZeroObject C := by
  refine ⟨⟨biproduct Empty.elim, fun X => ⟨⟨⟨0⟩, ?_⟩⟩, fun X => ⟨⟨⟨0⟩, ?_⟩⟩⟩⟩
  · intro a; apply biproduct.hom_ext'; simp
  · intro a; apply biproduct.hom_ext; simp

section

variable {C}

attribute [local simp] eq_iff_true_of_subsingleton in
/-- The limit bicone for the biproduct over an index type with exactly one term. -/
@[simps]
/-
**CategoryTheory.Limits.limitBiconeOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：limitBiconeOfUnique [Unique J] (f : J -> C) : LimitBicone f where bicone
参数：f : J -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit bicone for the biproduct over an index type with exactly one term.
-/
def limitBiconeOfUnique [Unique J] (f : J → C) : LimitBicone f where
  bicone :=
    { pt := f default
      π := fun j => eqToHom (by congr; rw [← Unique.uniq])
      ι := fun j => eqToHom (by congr; rw [← Unique.uniq]) }
  isBilimit :=
    { isLimit := (limitConeOfUnique f).isLimit
      isColimit := (colimitCoconeOfUnique f).isColimit }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasBiproduct_unique [Subsingleton J] [Nonempty J] (f : J → C) :
    HasBiproduct f :=
  let ⟨_⟩ := nonempty_unique J; .mk (limitBiconeOfUnique f)

/-- A biproduct over an index type with exactly one term is just the object over that term. -/
@[simps!]
/-
**CategoryTheory.Limits.biproductUniqueIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：biproductUniqueIso [Unique J] (f : J -> C) : ⨁ f ≅ f default
参数：f : J -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A biproduct over an index type with exactly one term is just the object over tha
t term.
-/
def biproductUniqueIso [Unique J] (f : J → C) : ⨁ f ≅ f default :=
  (biproduct.uniqueUpToIso _ (limitBiconeOfUnique f).isBilimit).symm

end

end CategoryTheory.Limits

