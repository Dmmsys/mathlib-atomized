/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Binary (co)products

We define a category `WalkingPair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `HasBinaryProducts` and `HasBinaryCoproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

@[expose] public section

universe v v₁ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
/-
**CategoryTheory.Limits.WalkingPair** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects for the diagram indexing a binary (co)product.
-/
inductive WalkingPair : Type
  | left
  | right
  deriving DecidableEq, Inhabited

open WalkingPair

/-- The equivalence swapping left and right.
-/
/-
**CategoryTheory.Limits.WalkingPair.swap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair ≃ CategoryTheory.Limits.WalkingPair
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence swapping left and right.
-/
def WalkingPair.swap : WalkingPair ≃ WalkingPair where
  toFun
    | left => right
    | right => left
  invFun
    | left => right
    | right => left
  left_inv j := by cases j <;> rfl
  right_inv j := by cases j <;> rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.swap_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.swap CategoryTheory.Limits.WalkingPair.l
eft = CategoryTheory.Limits.WalkingPair.right
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem WalkingPair.swap_apply_left : WalkingPair.swap left = right :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.swap_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.swap CategoryTheory.Limits.WalkingPair.r
ight = CategoryTheory.Limits.WalkingPair.left
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem WalkingPair.swap_apply_right : WalkingPair.swap right = left :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.swap_symm_apply_tt** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.swap.symm CategoryTheory.Limits.WalkingP
air.left =   CategoryTheory.Limits.WalkingPair.right
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem WalkingPair.swap_symm_apply_tt : WalkingPair.swap.symm left = right :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.swap_symm_apply_ff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.swap.symm CategoryTheory.Limits.WalkingP
air.right =   CategoryTheory.Limits.WalkingPair.left
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem WalkingPair.swap_symm_apply_ff : WalkingPair.swap.symm right = left :=
  rfl

/-- An equivalence from `WalkingPair` to `Bool`, sometimes useful when reindexing limits.
-/
/-
**CategoryTheory.Limits.WalkingPair.equivBool** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair ≃ Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence from `WalkingPair` to `Bool`, sometimes useful when reindexing li
mits.
-/
def WalkingPair.equivBool : WalkingPair ≃ Bool where
  toFun
    | left => true
    | right => false
  -- to match equiv.sum_equiv_sigma_bool
  invFun b := Bool.recOn b right left
  left_inv j := by cases j <;> rfl
  right_inv b := by cases b <;> rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.equivBool_apply_left** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.equivBool CategoryTheory.Limits.WalkingP
air.left = true
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem WalkingPair.equivBool_apply_left : WalkingPair.equivBool left = true :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.equivBool_apply_right** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.equivBool CategoryTheory.Limits.WalkingP
air.right = false
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem WalkingPair.equivBool_apply_right : WalkingPair.equivBool right = false :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.equivBool_symm_apply_true** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.equivBool.symm true = CategoryTheory.Lim
its.WalkingPair.left
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem WalkingPair.equivBool_symm_apply_true : WalkingPair.equivBool.symm true = left :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingPair.equivBool_symm_apply_false** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.WalkingPair`。
形式化陈述：CategoryTheory.Limits.WalkingPair.equivBool.symm false = CategoryTheory.Li
mits.WalkingPair.right
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem WalkingPair.equivBool_symm_apply_false : WalkingPair.equivBool.symm false = right :=
  rfl

variable {C : Type u}

/-- The function on the walking pair, sending the two points to `X` and `Y`. -/
/-
**CategoryTheory.Limits.pairFunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：pairFunction (X Y : C) : WalkingPair -> C
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function on the walking pair, sending the two points to `X` and `Y`.
-/
def pairFunction (X Y : C) : WalkingPair → C := fun j => WalkingPair.casesOn j X Y

@[simp]
/-
**CategoryTheory.Limits.pairFunction_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：pairFunction_left (X Y : C) : pairFunction X Y left = X
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pairFunction_left (X Y : C) : pairFunction X Y left = X :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.pairFunction_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pairFunction_right (X Y : C) : pairFunction X Y right = Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pairFunction_right (X Y : C) : pairFunction X Y right = Y :=
  rfl

variable [Category.{v} C]

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
/-
**CategoryTheory.Limits.pair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pair (X Y : C) : Discrete WalkingPair ⥤ C
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram on the walking pair, sending the two points to `X` and `Y`.
-/
def pair (X Y : C) : Discrete WalkingPair ⥤ C :=
  Discrete.functor fun j => WalkingPair.casesOn j X Y

@[simp]
/-
**CategoryTheory.Limits.pair_obj_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：pair_obj_left (X Y : C) : (pair X Y).obj ⟨left⟩ = X
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_obj_left (X Y : C) : (pair X Y).obj ⟨left⟩ = X :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.pair_obj_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：pair_obj_right (X Y : C) : (pair X Y).obj ⟨right⟩ = Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_obj_right (X Y : C) : (pair X Y).obj ⟨right⟩ = Y :=
  rfl

section

variable {F G : Discrete WalkingPair ⥤ C} (f : F.obj ⟨left⟩ ⟶ G.obj ⟨left⟩)
  (g : F.obj ⟨right⟩ ⟶ G.obj ⟨right⟩)

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

/-- The natural transformation between two functors out of the
walking pair, specified by its components. -/
/-
**CategoryTheory.Limits.mapPair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：mapPair : F ⟶ G where app | ⟨left⟩ => f | ⟨right⟩ => g naturality
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation between two functors out of the
walking pair, specified by its components.
-/
def mapPair : F ⟶ G where
  app
    | ⟨left⟩ => f
    | ⟨right⟩ => g
  naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨u⟩⟩ => by cat_disch

@[simp]
/-
**CategoryTheory.Limits.mapPair_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：mapPair_left : (mapPair f g).app ⟨left⟩ = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPair_left : (mapPair f g).app ⟨left⟩ = f :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.mapPair_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：mapPair_right : (mapPair f g).app ⟨right⟩ = g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPair_right : (mapPair f g).app ⟨right⟩ = g :=
  rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its
components. -/
@[simps!]
/-
**CategoryTheory.Limits.mapPairIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：mapPairIso (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨r
ight⟩) : F ≅ G
参数：f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩；g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between two functors out of the walking pair, specified 
by its
components.
-/
def mapPairIso (f : F.obj ⟨left⟩ ≅ G.obj ⟨left⟩) (g : F.obj ⟨right⟩ ≅ G.obj ⟨right⟩) : F ≅ G :=
  NatIso.ofComponents (fun j ↦ match j with
    | ⟨left⟩ => f
    | ⟨right⟩ => g)
    (fun ⟨⟨u⟩⟩ => by cat_disch)

end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simps!]
/-
**CategoryTheory.Limits.diagramIsoPair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：diagramIsoPair (F : Discrete WalkingPair ⥤ C) : F ≅ pair (F.obj ⟨WalkingPa
ir.left⟩) (F.obj ⟨WalkingPair.right⟩)
参数：F : Discrete WalkingPair ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every functor out of the walking pair is naturally isomorphic (actually, equal) 
to a `pair`
-/
def diagramIsoPair (F : Discrete WalkingPair ⥤ C) :
    F ≅ pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩) :=
  mapPairIso (Iso.refl _) (Iso.refl _)

section

variable {D : Type u₁} [Category.{v₁} D]

/-- The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`. -/
/-
**CategoryTheory.Limits.pairComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：pairComp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y)
参数：X Y : C；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`.
-/
def pairComp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
  diagramIsoPair _

end

/-- A binary fan is just a cone on a diagram indexing a product. -/
/-
**CategoryTheory.Limits.BinaryFan** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：BinaryFan (X Y : C)
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary fan is just a cone on a diagram indexing a product.
-/
abbrev BinaryFan (X Y : C) :=
  Cone (pair X Y)

/-- The first projection of a binary fan. -/
/-
**CategoryTheory.Limits.BinaryFan.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (s : CategoryTheory.Limits.BinaryFan X Y) →         ((CategoryTheory.Fu
nctor.const (CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair)).obj s.p
t).obj             { as := CategoryTheory.Limits.WalkingPair.left } ⟶           
(CategoryTheory.Limits.pair X Y).obj { as := CategoryTheory.Limits.WalkingPair.l
eft }
参数：s : CategoryTheory.Limits.BinaryFan X Y；(CategoryTheory.Functor.const (Catego
ryTheory.Discrete CategoryTheory.Limits.WalkingPair)).obj s.pt；CategoryTheory.Li
mits.pair X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of a binary fan.
-/
abbrev BinaryFan.fst {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.left⟩

/-- The second projection of a binary fan. -/
/-
**CategoryTheory.Limits.BinaryFan.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (s : CategoryTheory.Limits.BinaryFan X Y) →         ((CategoryTheory.Fu
nctor.const (CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair)).obj s.p
t).obj             { as := CategoryTheory.Limits.WalkingPair.right } ⟶          
 (CategoryTheory.Limits.pair X Y).obj { as := CategoryTheory.Limits.WalkingPair.
right }
参数：s : CategoryTheory.Limits.BinaryFan X Y；(CategoryTheory.Functor.const (Catego
ryTheory.Discrete CategoryTheory.Limits.WalkingPair)).obj s.pt；CategoryTheory.Li
mits.pair X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of a binary fan.
-/
abbrev BinaryFan.snd {X Y : C} (s : BinaryFan X Y) :=
  s.π.app ⟨WalkingPair.right⟩

-- Marking this `@[simp]` causes loops since `s.fst` is reducibly defeq to the LHS.
/-
**CategoryTheory.Limits.BinaryFan.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryFan.π_app_left {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.left⟩ = s.fst :=
  rfl

-- Marking this `@[simp]` causes loops since `s.snd` is reducibly defeq to the LHS.
/-
**CategoryTheory.Limits.BinaryFan.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryFan.π_app_right {X Y : C} (s : BinaryFan X Y) : s.π.app ⟨WalkingPair.right⟩ = s.snd :=
  rfl

/-- Constructs an isomorphism of `BinaryFan`s out of an isomorphism of the tips that commutes with
the projections. -/
/-
**CategoryTheory.Limits.BinaryFan.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A B : C}
 →       {c c' : CategoryTheory.Limits.BinaryFan A B} →         (e : c.pt ≅ c'.p
t) →           c.fst = CategoryTheory.CategoryStruct.comp e.hom c'.fst →        
     c.snd = CategoryTheory.CategoryStruct.comp e.hom c'.snd → (c ≅ c')
参数：e : c.pt ≅ c'.pt；c ≅ c'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of `BinaryFan`s out of an isomorphism of the tips that
 commutes with
the projections.
-/
def BinaryFan.ext {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) : c ≅ c' :=
  Cone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.ext_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B : C} {c c' :
 CategoryTheory.Limits.BinaryFan A B}   (e : c.pt ≅ c'.pt) (h₁ : c.fst = Categor
yTheory.CategoryStruct.comp e.hom c'.fst)   (h₂ : c.snd = CategoryTheory.Categor
yStruct.comp e.hom c'.snd),   (CategoryTheory.Limits.BinaryFan.ext e h₁ h₂).hom.
hom = e.hom
参数：e : c.pt ≅ c'.pt；h₁ : c.fst = CategoryTheory.CategoryStruct.comp e.hom c'.fst
；h₂ : c.snd = CategoryTheory.CategoryStruct.comp e.hom c'.snd；CategoryTheory.Lim
its.BinaryFan.ext e h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryFan.ext_hom_hom {A B : C} {c c' : BinaryFan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.fst = e.hom ≫ c'.fst) (h₂ : c.snd = e.hom ≫ c'.snd) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

/-- A convenient way to show that a binary fan is a limit. -/
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.BinaryFan.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (s : CategoryTheory.Limits.BinaryFan X Y) →         (lift : {T : C} → (
T ⟶ X) → (T ⟶ Y) → (T ⟶ s.pt)) →           (∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), C
ategoryTheory.CategoryStruct.comp (lift f g) s.fst = f) →             (∀ {T : C}
 (f : T ⟶ X) (g : T ⟶ Y), CategoryTheory.CategoryStruct.comp (lift f g) s.snd = 
g) →               (∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ s.pt),           
        CategoryTheory.CategoryStruct.comp m s.fst = f →                     Cat
egoryTheory.CategoryStruct.comp m s.snd = g → m = lift f g) →                 Ca
tegoryTheory.Limits.IsLimit s
参数：s : CategoryTheory.Limits.BinaryFan X Y；lift : {T : C} → (T ⟶ X) → (T ⟶ Y) → 
(T ⟶ s.pt)；∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), CategoryTheory.CategoryStruct.comp
 (lift f g) s.fst = f；∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), CategoryTheory.Category
Struct.comp (lift f g) s.snd = g；∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ s.pt
),                   CategoryTheory.CategoryStruct.comp m s.fst = f →           
          CategoryTheory.CategoryStruct.comp m s.snd = g → m = lift f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenient way to show that a binary fan is a limit.
-/
def BinaryFan.IsLimit.mk {X Y : C} (s : BinaryFan X Y)
    (lift : ∀ {T : C} (_ : T ⟶ X) (_ : T ⟶ Y), T ⟶ s.pt)
    (hl₁ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.fst = f)
    (hl₂ : ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y), lift f g ≫ s.snd = g)
    (uniq :
      ∀ {T : C} (f : T ⟶ X) (g : T ⟶ Y) (m : T ⟶ s.pt) (_ : m ≫ s.fst = f) (_ : m ≫ s.snd = g),
        m = lift f g) :
    IsLimit s :=
  Limits.IsLimit.mk (fun t => lift (BinaryFan.fst t) (BinaryFan.snd t))
    (by
      rintro t (rfl | rfl)
      · exact hl₁ _ _
      · exact hl₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.BinaryFan.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : 
CategoryTheory.Limits.BinaryFan X Y}   (h : CategoryTheory.Limits.IsLimit s) {f 
g : W ⟶ s.pt},   CategoryTheory.CategoryStruct.comp f s.fst = CategoryTheory.Cat
egoryStruct.comp g s.fst →     CategoryTheory.CategoryStruct.comp f s.snd = Cate
goryTheory.CategoryStruct.comp g s.snd → f = g
参数：h : CategoryTheory.Limits.IsLimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
-/
theorem BinaryFan.IsLimit.hom_ext {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) {f g : W ⟶ s.pt}
    (h₁ : f ≫ s.fst = g ≫ s.fst) (h₂ : f ≫ s.snd = g ≫ s.snd) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
/-
**CategoryTheory.Limits.BinaryCofan** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：BinaryCofan (X Y : C)
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary cofan is just a cocone on a diagram indexing a coproduct.
-/
abbrev BinaryCofan (X Y : C) := Cocone (pair X Y)

/-- The first inclusion of a binary cofan. -/
/-
**CategoryTheory.Limits.BinaryCofan.inl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (s : CategoryTheory.Limits.BinaryCofan X Y) →         (CategoryTheory.L
imits.pair X Y).obj { as := CategoryTheory.Limits.WalkingPair.left } ⟶          
 ((CategoryTheory.Functor.const (CategoryTheory.Discrete CategoryTheory.Limits.W
alkingPair)).obj s.pt).obj             { as := CategoryTheory.Limits.WalkingPair
.left }
参数：s : CategoryTheory.Limits.BinaryCofan X Y；CategoryTheory.Limits.pair X Y；(Cat
egoryTheory.Functor.const (CategoryTheory.Discrete CategoryTheory.Limits.Walking
Pair)).obj s.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first inclusion of a binary cofan.
-/
abbrev BinaryCofan.inl {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.left⟩

/-- The second inclusion of a binary cofan. -/
/-
**CategoryTheory.Limits.BinaryCofan.inr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (s : CategoryTheory.Limits.BinaryCofan X Y) →         (CategoryTheory.L
imits.pair X Y).obj { as := CategoryTheory.Limits.WalkingPair.right } ⟶         
  ((CategoryTheory.Functor.const (CategoryTheory.Discrete CategoryTheory.Limits.
WalkingPair)).obj s.pt).obj             { as := CategoryTheory.Limits.WalkingPai
r.right }
参数：s : CategoryTheory.Limits.BinaryCofan X Y；CategoryTheory.Limits.pair X Y；(Cat
egoryTheory.Functor.const (CategoryTheory.Discrete CategoryTheory.Limits.Walking
Pair)).obj s.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second inclusion of a binary cofan.
-/
abbrev BinaryCofan.inr {X Y : C} (s : BinaryCofan X Y) := s.ι.app ⟨WalkingPair.right⟩

/-- Constructs an isomorphism of `BinaryCofan`s out of an isomorphism of the tips that commutes with
the injections. -/
/-
**CategoryTheory.Limits.BinaryCofan.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A B : C}
 →       {c c' : CategoryTheory.Limits.BinaryCofan A B} →         (e : c.pt ≅ c'
.pt) →           CategoryTheory.CategoryStruct.comp c.inl e.hom = c'.inl →      
       CategoryTheory.CategoryStruct.comp c.inr e.hom = c'.inr → (c ≅ c')
参数：e : c.pt ≅ c'.pt；c ≅ c'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of `BinaryCofan`s out of an isomorphism of the tips th
at commutes with
the injections.
-/
def BinaryCofan.ext {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) : c ≅ c' :=
  Cocone.ext e (fun j => by rcases j with ⟨⟨⟩⟩ <;> assumption)

@[simp]
/-
**CategoryTheory.Limits.BinaryCofan.ext_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B : C} {c c' :
 CategoryTheory.Limits.BinaryCofan A B}   (e : c.pt ≅ c'.pt) (h₁ : CategoryTheor
y.CategoryStruct.comp c.inl e.hom = c'.inl)   (h₂ : CategoryTheory.CategoryStruc
t.comp c.inr e.hom = c'.inr),   (CategoryTheory.Limits.BinaryCofan.ext e h₁ h₂).
hom.hom = e.hom
参数：e : c.pt ≅ c'.pt；h₁ : CategoryTheory.CategoryStruct.comp c.inl e.hom = c'.inl
；h₂ : CategoryTheory.CategoryStruct.comp c.inr e.hom = c'.inr；CategoryTheory.Lim
its.BinaryCofan.ext e h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryCofan.ext_hom_hom {A B : C} {c c' : BinaryCofan A B} (e : c.pt ≅ c'.pt)
    (h₁ : c.inl ≫ e.hom = c'.inl) (h₂ : c.inr ≫ e.hom = c'.inr) :
    (ext e h₁ h₂).hom.hom = e.hom := rfl

-- This cannot be `@[simp]` because `s.inl` is reducibly defeq to the LHS.
/-
**CategoryTheory.Limits.BinaryCofan.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryCofan.ι_app_left {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.left⟩ = s.inl := rfl

-- This cannot be `@[simp]` because `s.inr` is reducibly defeq to the LHS.
/-
**CategoryTheory.Limits.BinaryCofan.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryCofan.ι_app_right {X Y : C} (s : BinaryCofan X Y) :
    s.ι.app ⟨WalkingPair.right⟩ = s.inr := rfl

/-- A convenient way to show that a binary cofan is a colimit. -/
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (s : CategoryTheory.Limits.BinaryCofan X Y) →         (desc : {T : C} →
 (X ⟶ T) → (Y ⟶ T) → (s.pt ⟶ T)) →           (∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T),
 CategoryTheory.CategoryStruct.comp s.inl (desc f g) = f) →             (∀ {T : 
C} (f : X ⟶ T) (g : Y ⟶ T), CategoryTheory.CategoryStruct.comp s.inr (desc f g) 
= g) →               (∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T) (m : s.pt ⟶ T),         
          CategoryTheory.CategoryStruct.comp s.inl m = f →                     C
ategoryTheory.CategoryStruct.comp s.inr m = g → m = desc f g) →                 
CategoryTheory.Limits.IsColimit s
参数：s : CategoryTheory.Limits.BinaryCofan X Y；desc : {T : C} → (X ⟶ T) → (Y ⟶ T) 
→ (s.pt ⟶ T)；∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), CategoryTheory.CategoryStruct.co
mp s.inl (desc f g) = f；∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), CategoryTheory.Catego
ryStruct.comp s.inr (desc f g) = g；∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T) (m : s.pt ⟶
 T),                   CategoryTheory.CategoryStruct.comp s.inl m = f →         
            CategoryTheory.CategoryStruct.comp s.inr m = g → m = desc f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenient way to show that a binary cofan is a colimit.
-/
def BinaryCofan.IsColimit.mk {X Y : C} (s : BinaryCofan X Y)
    (desc : ∀ {T : C} (_ : X ⟶ T) (_ : Y ⟶ T), s.pt ⟶ T)
    (hd₁ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inl ≫ desc f g = f)
    (hd₂ : ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T), s.inr ≫ desc f g = g)
    (uniq :
      ∀ {T : C} (f : X ⟶ T) (g : Y ⟶ T) (m : s.pt ⟶ T) (_ : s.inl ≫ m = f) (_ : s.inr ≫ m = g),
        m = desc f g) :
    IsColimit s :=
  Limits.IsColimit.mk (fun t => desc (BinaryCofan.inl t) (BinaryCofan.inr t))
    (by
      rintro t (rfl | rfl)
      · exact hd₁ _ _
      · exact hd₂ _ _)
    fun _ _ h => uniq _ _ _ (h ⟨WalkingPair.left⟩) (h ⟨WalkingPair.right⟩)
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : 
CategoryTheory.Limits.BinaryCofan X Y}   (h : CategoryTheory.Limits.IsColimit s)
 {f g : s.pt ⟶ W},   CategoryTheory.CategoryStruct.comp s.inl f = CategoryTheory
.CategoryStruct.comp s.inl g →     CategoryTheory.CategoryStruct.comp s.inr f = 
CategoryTheory.CategoryStruct.comp s.inr g → f = g
参数：h : CategoryTheory.Limits.IsColimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
-/
theorem BinaryCofan.IsColimit.hom_ext {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s)
    {f g : s.pt ⟶ W} (h₁ : s.inl ≫ f = s.inl ≫ g) (h₂ : s.inr ≫ f = s.inr ≫ g) : f = g :=
  h.hom_ext fun j => Discrete.recOn j fun j => WalkingPair.casesOn j h₁ h₂

variable {X Y : C}

section

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases
-- TODO: would it be okay to use this more generally?
attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Eq

set_option backward.defeqAttrib.useBackward true in
/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
@[simps pt, implicit_reducible]
/-
**CategoryTheory.Limits.BinaryFan.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {X Y P : C} →
 (P ⟶ X) → (P ⟶ Y) → CategoryTheory.Limits.BinaryFan X Y
参数：P ⟶ X；P ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π
₂ : P ⟶ Y`.
-/
def BinaryFan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : BinaryFan X Y where
  pt := P
  π := { app := fun | { as := j } => match j with | left => π₁ | right => π₂ }

set_option backward.defeqAttrib.useBackward true in
/-- A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P`. -/
@[simps pt]
/-
**CategoryTheory.Limits.BinaryCofan.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {X Y P : C} →
 (X ⟶ P) → (Y ⟶ P) → CategoryTheory.Limits.BinaryCofan X Y
参数：X ⟶ P；Y ⟶ P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `
ι₂ : Y ⟶ P`.
-/
def BinaryCofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : BinaryCofan X Y where
  pt := P
  ι := { app := fun | { as := j } => match j with | left => ι₁ | right => ι₂ }

end

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.mk_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (π₁ :
 P ⟶ X) (π₂ : P ⟶ Y),   (CategoryTheory.Limits.BinaryFan.mk π₁ π₂).fst = π₁
参数：π₁ : P ⟶ X；π₂ : P ⟶ Y；CategoryTheory.Limits.BinaryFan.mk π₁ π₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryFan.mk_fst {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).fst = π₁ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.mk_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (π₁ :
 P ⟶ X) (π₂ : P ⟶ Y),   (CategoryTheory.Limits.BinaryFan.mk π₁ π₂).snd = π₂
参数：π₁ : P ⟶ X；π₂ : P ⟶ Y；CategoryTheory.Limits.BinaryFan.mk π₁ π₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryFan.mk_snd {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : (BinaryFan.mk π₁ π₂).snd = π₂ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryCofan.mk_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (ι₁ :
 X ⟶ P) (ι₂ : Y ⟶ P),   (CategoryTheory.Limits.BinaryCofan.mk ι₁ ι₂).inl = ι₁
参数：ι₁ : X ⟶ P；ι₂ : Y ⟶ P；CategoryTheory.Limits.BinaryCofan.mk ι₁ ι₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryCofan.mk_inl {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inl = ι₁ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryCofan.mk_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (ι₁ :
 X ⟶ P) (ι₂ : Y ⟶ P),   (CategoryTheory.Limits.BinaryCofan.mk ι₁ ι₂).inr = ι₂
参数：ι₁ : X ⟶ P；ι₂ : Y ⟶ P；CategoryTheory.Limits.BinaryCofan.mk ι₁ ι₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem BinaryCofan.mk_inr {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : (BinaryCofan.mk ι₁ ι₂).inr = ι₂ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`. -/
/-
**CategoryTheory.Limits.isoBinaryFanMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ≅ BinaryFan.mk c.fst c.sn
d
参数：c : BinaryFan X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`.
-/
def isoBinaryFanMk {X Y : C} (c : BinaryFan X Y) : c ≅ BinaryFan.mk c.fst c.snd :=
    Cone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`. -/
/-
**CategoryTheory.Limits.isoBinaryCofanMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.in
l c.inr
参数：c : BinaryCofan X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every `BinaryFan` is isomorphic to an application of `BinaryFan.mk`.
-/
def isoBinaryCofanMk {X Y : C} (c : BinaryCofan X Y) : c ≅ BinaryCofan.mk c.inl c.inr :=
    Cocone.ext (Iso.refl _) fun ⟨l⟩ => by cases l; repeat simp

/-- This is a more convenient formulation to show that a `BinaryFan` constructed using
`BinaryFan.mk` is a limit cone.
-/
/-
**CategoryTheory.Limits.BinaryFan.isLimitMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y W : 
C} →       {fst : W ⟶ X} →         {snd : W ⟶ Y} →           (lift : (s : Catego
ryTheory.Limits.BinaryFan X Y) → s.pt ⟶ W) →             (∀ (s : CategoryTheory.
Limits.BinaryFan X Y), CategoryTheory.CategoryStruct.comp (lift s) fst = s.fst) 
→               (∀ (s : CategoryTheory.Limits.BinaryFan X Y), CategoryTheory.Cat
egoryStruct.comp (lift s) snd = s.snd) →                 (∀ (s : CategoryTheory.
Limits.BinaryFan X Y) (m : s.pt ⟶ W),                     CategoryTheory.Categor
yStruct.comp m fst = s.fst →                       CategoryTheory.CategoryStruct
.comp m snd = s.snd → m = lift s) →                   CategoryTheory.Limits.IsLi
mit (CategoryTheory.Limits.BinaryFan.mk fst snd)
参数：lift : (s : CategoryTheory.Limits.BinaryFan X Y) → s.pt ⟶ W；∀ (s : CategoryTh
eory.Limits.BinaryFan X Y), CategoryTheory.CategoryStruct.comp (lift s) fst = s.
fst；∀ (s : CategoryTheory.Limits.BinaryFan X Y), CategoryTheory.CategoryStruct.c
omp (lift s) snd = s.snd；∀ (s : CategoryTheory.Limits.BinaryFan X Y) (m : s.pt ⟶
 W),                     CategoryTheory.CategoryStruct.comp m fst = s.fst →     
                  CategoryTheory.CategoryStruct.comp m snd = s.snd → m = lift s；
CategoryTheory.Limits.BinaryFan.mk fst snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `BinaryFan` constructed usi
ng
`BinaryFan.mk` is a limit cone.
-/
def BinaryFan.isLimitMk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (lift : ∀ s : BinaryFan X Y, s.pt ⟶ W)
    (fac_left : ∀ s : BinaryFan X Y, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : BinaryFan X Y, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : BinaryFan X Y) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (BinaryFan.mk fst snd) :=
  { lift := lift
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

/-- This is a more convenient formulation to show that a `BinaryCofan` constructed using
`BinaryCofan.mk` is a colimit cocone.
-/
/-
**CategoryTheory.Limits.BinaryCofan.isColimitMk** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y W : 
C} →       {inl : X ⟶ W} →         {inr : Y ⟶ W} →           (desc : (s : Catego
ryTheory.Limits.BinaryCofan X Y) → W ⟶ s.pt) →             (∀ (s : CategoryTheor
y.Limits.BinaryCofan X Y), CategoryTheory.CategoryStruct.comp inl (desc s) = s.i
nl) →               (∀ (s : CategoryTheory.Limits.BinaryCofan X Y), CategoryTheo
ry.CategoryStruct.comp inr (desc s) = s.inr) →                 (∀ (s : CategoryT
heory.Limits.BinaryCofan X Y) (m : W ⟶ s.pt),                     CategoryTheory
.CategoryStruct.comp inl m = s.inl →                       CategoryTheory.Catego
ryStruct.comp inr m = s.inr → m = desc s) →                   CategoryTheory.Lim
its.IsColimit (CategoryTheory.Limits.BinaryCofan.mk inl inr)
参数：desc : (s : CategoryTheory.Limits.BinaryCofan X Y) → W ⟶ s.pt；∀ (s : Category
Theory.Limits.BinaryCofan X Y), CategoryTheory.CategoryStruct.comp inl (desc s) 
= s.inl；∀ (s : CategoryTheory.Limits.BinaryCofan X Y), CategoryTheory.CategorySt
ruct.comp inr (desc s) = s.inr；∀ (s : CategoryTheory.Limits.BinaryCofan X Y) (m 
: W ⟶ s.pt),                     CategoryTheory.CategoryStruct.comp inl m = s.in
l →                       CategoryTheory.CategoryStruct.comp inr m = s.inr → m =
 desc s；CategoryTheory.Limits.BinaryCofan.mk inl inr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `BinaryCofan` constructed u
sing
`BinaryCofan.mk` is a colimit cocone.
-/
def BinaryCofan.isColimitMk {W : C} {inl : X ⟶ W} {inr : Y ⟶ W}
    (desc : ∀ s : BinaryCofan X Y, W ⟶ s.pt)
    (fac_left : ∀ s : BinaryCofan X Y, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : BinaryCofan X Y, inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : BinaryCofan X Y) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (BinaryCofan.mk inl inr) :=
  { desc := desc
    fac := fun s j => by
      rcases j with ⟨⟨⟩⟩
      exacts [fac_left s, fac_right s]
    uniq := fun s m w => uniq s m (w ⟨WalkingPair.left⟩) (w ⟨WalkingPair.right⟩) }

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
`g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
-/
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.BinaryFan.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y W : 
C} →       {s : CategoryTheory.Limits.BinaryFan X Y} → CategoryTheory.Limits.IsL
imit s → (W ⟶ X) → (W ⟶ Y) → (W ⟶ s.pt)
参数：W ⟶ X；W ⟶ Y；W ⟶ s.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f :
 W ⟶ X` and
`g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l 
≫ s.snd = g`.
-/
def BinaryFan.IsLimit.lift {W : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ s.pt :=
  h.lift (BinaryFan.mk f g)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryFan.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : 
CategoryTheory.Limits.BinaryFan X Y}   (h : CategoryTheory.Limits.IsLimit s) (f 
: W ⟶ X) (g : W ⟶ Y),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.BinaryFan.IsLimit.lift h f g) s.fst = f
参数：h : CategoryTheory.Limits.IsLimit s；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits
.BinaryFan.IsLimit.lift h f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma BinaryFan.IsLimit.lift_fst {W : C} {s : BinaryFan X Y} (h : IsLimit s)
    (f : W ⟶ X) (g : W ⟶ Y) :
    lift h f g ≫ s.fst = f :=
  h.fac (BinaryFan.mk f g) _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryFan.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : 
CategoryTheory.Limits.BinaryFan X Y}   (h : CategoryTheory.Limits.IsLimit s) (f 
: W ⟶ X) (g : W ⟶ Y),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.BinaryFan.IsLimit.lift h f g) s.snd = g
参数：h : CategoryTheory.Limits.IsLimit s；f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits
.BinaryFan.IsLimit.lift h f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma BinaryFan.IsLimit.lift_snd {W : C} {s : BinaryFan X Y} (h : IsLimit s)
    (f : W ⟶ X) (g : W ⟶ Y) :
    lift h f g ≫ s.snd = g :=
  h.fac (BinaryFan.mk f g) _

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
`g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
-/
@[simps]
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.lift'** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.BinaryFan.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y : 
C} →       {s : CategoryTheory.Limits.BinaryFan X Y} →         CategoryTheory.Li
mits.IsLimit s →           (f : W ⟶ X) →             (g : W ⟶ Y) →              
 { l // CategoryTheory.CategoryStruct.comp l s.fst = f ∧ CategoryTheory.Category
Struct.comp l s.snd = g }
参数：f : W ⟶ X；g : W ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f :
 W ⟶ X` and
`g : W ⟶ Y` induces a morphism `l : W ⟶ s.pt` satisfying `l ≫ s.fst = f` and `l 
≫ s.snd = g`.
-/
def BinaryFan.IsLimit.lift' {W X Y : C} {s : BinaryFan X Y} (h : IsLimit s) (f : W ⟶ X)
    (g : W ⟶ Y) : { l : W ⟶ s.pt // l ≫ s.fst = f ∧ l ≫ s.snd = g } :=
  ⟨h.lift <| BinaryFan.mk f g, h.fac _ _, h.fac _ _⟩

/-- If `s` is a colimit binary cofan over `X` and `Y`, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
-/
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.desc** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y W : 
C} →       {s : CategoryTheory.Limits.BinaryCofan X Y} → CategoryTheory.Limits.I
sColimit s → (X ⟶ W) → (Y ⟶ W) → (s.pt ⟶ W)
参数：X ⟶ W；Y ⟶ W；s.pt ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a colimit binary cofan over `X` and `Y`, then every pair of morphisms 
`f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.
inr ≫ l = g`.
-/
def BinaryCofan.IsColimit.desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.pt ⟶ W :=
  h.desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.inl_desc** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : 
CategoryTheory.Limits.BinaryCofan X Y}   (h : CategoryTheory.Limits.IsColimit s)
 (f : X ⟶ W) (g : Y ⟶ W),   CategoryTheory.CategoryStruct.comp s.inl (CategoryTh
eory.Limits.BinaryCofan.IsColimit.desc h f g) = f
参数：h : CategoryTheory.Limits.IsColimit s；f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limi
ts.BinaryCofan.IsColimit.desc h f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma BinaryCofan.IsColimit.inl_desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.inl ≫ desc h f g = f :=
  h.fac (BinaryCofan.mk f g) _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.inr_desc** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y W : C} {s : 
CategoryTheory.Limits.BinaryCofan X Y}   (h : CategoryTheory.Limits.IsColimit s)
 (f : X ⟶ W) (g : Y ⟶ W),   CategoryTheory.CategoryStruct.comp s.inr (CategoryTh
eory.Limits.BinaryCofan.IsColimit.desc h f g) = g
参数：h : CategoryTheory.Limits.IsColimit s；f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limi
ts.BinaryCofan.IsColimit.desc h f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma BinaryCofan.IsColimit.inr_desc {W : C} {s : BinaryCofan X Y} (h : IsColimit s)
    (f : X ⟶ W) (g : Y ⟶ W) :
    s.inr ≫ desc h f g = g :=
  h.fac (BinaryCofan.mk f g) _

/-- If `s` is a colimit binary cofan over `X` and `Y`, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
-/
@[simps]
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.desc'** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y : 
C} →       {s : CategoryTheory.Limits.BinaryCofan X Y} →         CategoryTheory.
Limits.IsColimit s →           (f : X ⟶ W) →             (g : Y ⟶ W) →          
     { l // CategoryTheory.CategoryStruct.comp s.inl l = f ∧ CategoryTheory.Cate
goryStruct.comp s.inr l = g }
参数：f : X ⟶ W；g : Y ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a colimit binary cofan over `X` and `Y`, then every pair of morphisms 
`f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : s.pt ⟶ W` satisfying `s.inl ≫ l = f` and `s.
inr ≫ l = g`.
-/
def BinaryCofan.IsColimit.desc' {W X Y : C} {s : BinaryCofan X Y} (h : IsColimit s) (f : X ⟶ W)
    (g : Y ⟶ W) : { l : s.pt ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g } :=
  ⟨h.desc <| BinaryCofan.mk f g, h.fac _ _, h.fac _ _⟩

/-- Binary products are symmetric. -/
/-
**CategoryTheory.Limits.BinaryFan.isLimitFlip** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {c : CategoryTheory.Limits.BinaryFan X Y} →         CategoryTheory.Limi
ts.IsLimit c → CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.BinaryFan.mk
 c.snd c.fst)
参数：CategoryTheory.Limits.BinaryFan.mk c.snd c.fst。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Binary products are symmetric.
-/
def BinaryFan.isLimitFlip {X Y : C} {c : BinaryFan X Y} (hc : IsLimit c) :
    IsLimit (BinaryFan.mk c.snd c.fst) :=
  BinaryFan.isLimitMk (fun s => IsLimit.lift hc s.snd s.fst) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryFan.IsLimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryFan.mk s.snd s.fst) ⟨WalkingPair.right⟩).symm)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.BinaryFan.isLimit_iff_isIso_fst** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : Ca
tegoryTheory.Limits.IsTerminal Y)   (c : CategoryTheory.Limits.BinaryFan X Y), N
onempty (CategoryTheory.Limits.IsLimit c) ↔ CategoryTheory.IsIso c.fst
参数：h : CategoryTheory.Limits.IsTerminal Y；c : CategoryTheory.Limits.BinaryFan X 
Y；CategoryTheory.Limits.IsLimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.BinaryF
an X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
-/
theorem BinaryFan.isLimit_iff_isIso_fst {X Y : C} (h : IsTerminal Y) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.fst := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryFan.IsLimit.lift' H (𝟙 X) (h.from X)
    exact
      ⟨⟨l,
          BinaryFan.IsLimit.hom_ext H (by simpa [hl, -Category.comp_id] using Category.comp_id _)
            (h.hom_ext _ _),
          hl⟩⟩
  · intro
    exact
      ⟨BinaryFan.IsLimit.mk _ (fun f _ => f ≫ inv c.fst) (fun _ _ => by simp)
          (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ => by simp [← e]⟩
/-
**CategoryTheory.Limits.BinaryFan.isLimit_iff_isIso_snd** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : Ca
tegoryTheory.Limits.IsTerminal X)   (c : CategoryTheory.Limits.BinaryFan X Y), N
onempty (CategoryTheory.Limits.IsLimit c) ↔ CategoryTheory.IsIso c.snd
参数：h : CategoryTheory.Limits.IsTerminal X；c : CategoryTheory.Limits.BinaryFan X 
Y；CategoryTheory.Limits.IsLimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.Limits.BinaryFan.isLimit_iff_isIso_fst`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Limits.IsT
erminal Y)   (c : CategoryTheory.Limits.Bin…
-/
theorem BinaryFan.isLimit_iff_isIso_snd {X Y : C} (h : IsTerminal X) (c : BinaryFan X Y) :
    Nonempty (IsLimit c) ↔ IsIso c.snd := by
  refine Iff.trans ?_ (BinaryFan.isLimit_iff_isIso_fst h (BinaryFan.mk c.snd c.fst))
  exact
    ⟨fun h => ⟨BinaryFan.isLimitFlip h.some⟩, fun h =>
      ⟨(BinaryFan.isLimitFlip h.some).ofIsoLimit (isoBinaryFanMk c).symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `X' ≅ X`, then `X × Y` also is the product of `X'` and `Y`. -/
/-
**CategoryTheory.Limits.BinaryFan.isLimitCompLeftIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y X' :
 C} →       (c : CategoryTheory.Limits.BinaryFan X Y) →         (f : X ⟶ X') →  
         [CategoryTheory.IsIso f] →             CategoryTheory.Limits.IsLimit c 
→               CategoryTheory.Limits.IsLimit                 (CategoryTheory.Li
mits.BinaryFan.mk (CategoryTheory.CategoryStruct.comp c.fst f) c.snd)
参数：c : CategoryTheory.Limits.BinaryFan X Y；f : X ⟶ X'；CategoryTheory.Limits.Bina
ryFan.mk (CategoryTheory.CategoryStruct.comp c.fst f) c.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X' ≅ X`, then `X × Y` also is the product of `X'` and `Y`.
-/
noncomputable def BinaryFan.isLimitCompLeftIso {X Y X' : C} (c : BinaryFan X Y) (f : X ⟶ X')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk (c.fst ≫ f) c.snd) := by
  fapply BinaryFan.isLimitMk
  · exact fun s => IsLimit.lift h (s.fst ≫ inv f) s.snd
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryFan.IsLimit.hom_ext h
    · simpa
    · simpa

/-- If `Y' ≅ Y`, then `X x Y` also is the product of `X` and `Y'`. -/
/-
**CategoryTheory.Limits.BinaryFan.isLimitCompRightIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Y' :
 C} →       (c : CategoryTheory.Limits.BinaryFan X Y) →         (f : Y ⟶ Y') →  
         [CategoryTheory.IsIso f] →             CategoryTheory.Limits.IsLimit c 
→               CategoryTheory.Limits.IsLimit                 (CategoryTheory.Li
mits.BinaryFan.mk c.fst (CategoryTheory.CategoryStruct.comp c.snd f))
参数：c : CategoryTheory.Limits.BinaryFan X Y；f : Y ⟶ Y'；CategoryTheory.Limits.Bina
ryFan.mk c.fst (CategoryTheory.CategoryStruct.comp c.snd f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Y' ≅ Y`, then `X x Y` also is the product of `X` and `Y'`.
-/
noncomputable def BinaryFan.isLimitCompRightIso {X Y Y' : C} (c : BinaryFan X Y) (f : Y ⟶ Y')
    [IsIso f] (h : IsLimit c) : IsLimit (BinaryFan.mk c.fst (c.snd ≫ f)) :=
  BinaryFan.isLimitFlip <| BinaryFan.isLimitCompLeftIso _ f (BinaryFan.isLimitFlip h)

/-- Binary coproducts are symmetric. -/
/-
**CategoryTheory.Limits.BinaryCofan.isColimitFlip** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {c : CategoryTheory.Limits.BinaryCofan X Y} →         CategoryTheory.Li
mits.IsColimit c →           CategoryTheory.Limits.IsColimit (CategoryTheory.Lim
its.BinaryCofan.mk c.inr c.inl)
参数：CategoryTheory.Limits.BinaryCofan.mk c.inr c.inl。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Binary coproducts are symmetric.
-/
def BinaryCofan.isColimitFlip {X Y : C} {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsColimit (BinaryCofan.mk c.inr c.inl) :=
  BinaryCofan.isColimitMk (fun s => IsColimit.desc hc s.inr s.inl) (fun _ => hc.fac _ _)
    (fun _ => hc.fac _ _) fun s _ e₁ e₂ =>
    BinaryCofan.IsColimit.hom_ext hc
      (e₂.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.left⟩).symm)
      (e₁.trans (hc.fac (BinaryCofan.mk s.inr s.inl) ⟨WalkingPair.right⟩).symm)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.BinaryCofan.isColimit_iff_isIso_inl** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : Ca
tegoryTheory.Limits.IsInitial Y)   (c : CategoryTheory.Limits.BinaryCofan X Y), 
Nonempty (CategoryTheory.Limits.IsColimit c) ↔ CategoryTheory.IsIso c.inl
参数：h : CategoryTheory.Limits.IsInitial Y；c : CategoryTheory.Limits.BinaryCofan X
 Y；CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
-/
theorem BinaryCofan.isColimit_iff_isIso_inl {X Y : C} (h : IsInitial Y) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inl := by
  constructor
  · rintro ⟨H⟩
    obtain ⟨l, hl, -⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X) (h.to X)
    refine ⟨⟨l, hl, BinaryCofan.IsColimit.hom_ext H (?_) (h.hom_ext _ _)⟩⟩
    rw [Category.comp_id]
    have e : (inl c ≫ l) ≫ inl c = 𝟙 X ≫ inl c := congrArg (· ≫ inl c) hl
    rwa [Category.assoc, Category.id_comp] at e
  · intro
    exact
      ⟨BinaryCofan.IsColimit.mk _ (fun f _ => inv c.inl ≫ f)
          (fun _ _ => IsIso.hom_inv_id_assoc _ _) (fun _ _ => h.hom_ext _ _) fun _ _ _ e _ =>
          (IsIso.eq_inv_comp _).mpr e⟩
/-
**CategoryTheory.Limits.BinaryCofan.isColimit_iff_isIso_inr** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : Ca
tegoryTheory.Limits.IsInitial X)   (c : CategoryTheory.Limits.BinaryCofan X Y), 
Nonempty (CategoryTheory.Limits.IsColimit c) ↔ CategoryTheory.IsIso c.inr
参数：h : CategoryTheory.Limits.IsInitial X；c : CategoryTheory.Limits.BinaryCofan X
 Y；CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CategoryTheory.Limits.BinaryCofan.isColimit_iff_isIso_inl`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (h : CategoryTheory.Limits
.IsInitial Y)   (c : CategoryTheory.Limits.Bina…
-/
theorem BinaryCofan.isColimit_iff_isIso_inr {X Y : C} (h : IsInitial X) (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔ IsIso c.inr := by
  refine Iff.trans ?_ (BinaryCofan.isColimit_iff_isIso_inl h (BinaryCofan.mk c.inr c.inl))
  exact
    ⟨fun h => ⟨BinaryCofan.isColimitFlip h.some⟩, fun h =>
      ⟨(BinaryCofan.isColimitFlip h.some).ofIsoColimit (isoBinaryCofanMk c).symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `X' ≅ X`, then `X ⨿ Y` also is the coproduct of `X'` and `Y`. -/
/-
**CategoryTheory.Limits.BinaryCofan.isColimitCompLeftIso** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y X' :
 C} →       (c : CategoryTheory.Limits.BinaryCofan X Y) →         (f : X' ⟶ X) →
           [CategoryTheory.IsIso f] →             CategoryTheory.Limits.IsColimi
t c →               CategoryTheory.Limits.IsColimit                 (CategoryThe
ory.Limits.BinaryCofan.mk (CategoryTheory.CategoryStruct.comp f c.inl) c.inr)
参数：c : CategoryTheory.Limits.BinaryCofan X Y；f : X' ⟶ X；CategoryTheory.Limits.Bi
naryCofan.mk (CategoryTheory.CategoryStruct.comp f c.inl) c.inr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X' ≅ X`, then `X ⨿ Y` also is the coproduct of `X'` and `Y`.
-/
noncomputable def BinaryCofan.isColimitCompLeftIso {X Y X' : C} (c : BinaryCofan X Y) (f : X' ⟶ X)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk (f ≫ c.inl) c.inr) := by
  fapply BinaryCofan.isColimitMk
  · exact fun s => BinaryCofan.IsColimit.desc h (inv f ≫ s.inl) s.inr
  · simp
  · simp
  · intro s m e₁ e₂
    apply BinaryCofan.IsColimit.hom_ext h
    · rw [← cancel_epi f]
      simpa using e₁
    · simpa

/-- If `Y' ≅ Y`, then `X ⨿ Y` also is the coproduct of `X` and `Y'`. -/
/-
**CategoryTheory.Limits.BinaryCofan.isColimitCompRightIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Y' :
 C} →       (c : CategoryTheory.Limits.BinaryCofan X Y) →         (f : Y' ⟶ Y) →
           [CategoryTheory.IsIso f] →             CategoryTheory.Limits.IsColimi
t c →               CategoryTheory.Limits.IsColimit                 (CategoryThe
ory.Limits.BinaryCofan.mk c.inl (CategoryTheory.CategoryStruct.comp f c.inr))
参数：c : CategoryTheory.Limits.BinaryCofan X Y；f : Y' ⟶ Y；CategoryTheory.Limits.Bi
naryCofan.mk c.inl (CategoryTheory.CategoryStruct.comp f c.inr)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Y' ≅ Y`, then `X ⨿ Y` also is the coproduct of `X` and `Y'`.
-/
noncomputable def BinaryCofan.isColimitCompRightIso {X Y Y' : C} (c : BinaryCofan X Y) (f : Y' ⟶ Y)
    [IsIso f] (h : IsColimit c) : IsColimit (BinaryCofan.mk c.inl (f ≫ c.inr)) :=
  BinaryCofan.isColimitFlip <| BinaryCofan.isColimitCompLeftIso _ f (BinaryCofan.isColimitFlip h)

/-- An abbreviation for `HasLimit (pair X Y)`. -/
/-
**CategoryTheory.Limits.HasBinaryProduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasBinaryProduct (X Y : C)
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HasLimit (pair X Y)`.
-/
abbrev HasBinaryProduct (X Y : C) :=
  HasLimit (pair X Y)

/-- An abbreviation for `HasColimit (pair X Y)`. -/
/-
**CategoryTheory.Limits.HasBinaryCoproduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：HasBinaryCoproduct (X Y : C)
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HasColimit (pair X Y)`.
-/
abbrev HasBinaryCoproduct (X Y : C) :=
  HasColimit (pair X Y)

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or `X ⨯ Y`. -/
/-
**CategoryTheory.Limits.prod** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：prod (X Y : C) [HasBinaryProduct X Y]
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have a product of `X` and `Y`, we can access it using `prod X Y` or `X ⨯ Y
`.
-/
noncomputable abbrev prod (X Y : C) [HasBinaryProduct X Y] :=
  limit (pair X Y)

/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y` or `X ⨿ Y`. -/
/-
**CategoryTheory.Limits.coprod** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：coprod (X Y : C) [HasBinaryCoproduct X Y]
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y` or `X
 ⨿ Y`.
-/
noncomputable abbrev coprod (X Y : C) [HasBinaryCoproduct X Y] :=
  colimit (pair X Y)

/-- Notation for the product -/
notation:20 X " ⨯ " Y:20 => prod X Y

/-- Notation for the coproduct -/
notation:20 X " ⨿ " Y:20 => coprod X Y

/-- The projection map to the first component of the product. -/
/-
**CategoryTheory.Limits.prod.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → [inst_1 : CategoryTheory.Limits.HasBinaryProduct X Y] → X ⨯ Y ⟶ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map to the first component of the product.
-/
noncomputable abbrev prod.fst {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) ⟨WalkingPair.left⟩

/-- The projection map to the second component of the product. -/
/-
**CategoryTheory.Limits.prod.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → [inst_1 : CategoryTheory.Limits.HasBinaryProduct X Y] → X ⨯ Y ⟶ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map to the second component of the product.
-/
noncomputable abbrev prod.snd {X Y : C} [HasBinaryProduct X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) ⟨WalkingPair.right⟩

/-- The inclusion map from the first component of the coproduct. -/
/-
**CategoryTheory.Limits.coprod.inl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] → X ⟶ X ⨿ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from the first component of the coproduct.
-/
noncomputable abbrev coprod.inl {X Y : C} [HasBinaryCoproduct X Y] : X ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.left⟩

/-- The inclusion map from the second component of the coproduct. -/
/-
**CategoryTheory.Limits.coprod.inr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] → Y ⟶ X ⨿ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion map from the second component of the coproduct.
-/
noncomputable abbrev coprod.inr {X Y : C} [HasBinaryCoproduct X Y] : Y ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) ⟨WalkingPair.right⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The binary fan constructed from the projection maps is a limit. -/
/-
**CategoryTheory.Limits.prodIsProd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：prodIsProd (X Y : C) [HasBinaryProduct X Y] : IsLimit (BinaryFan.mk (prod.
fst : X ⨯ Y ⟶ X) prod.snd)
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary fan constructed from the projection maps is a limit.
-/
noncomputable def prodIsProd (X Y : C) [HasBinaryProduct X Y] :
    IsLimit (BinaryFan.mk (prod.fst : X ⨯ Y ⟶ X) prod.snd) :=
  (limit.isLimit _).ofIsoLimit (Cone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · simp [Category.id_comp]
    · simp [Category.id_comp]
  ))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The binary cofan constructed from the coprojection maps is a colimit. -/
/-
**CategoryTheory.Limits.coprodIsCoprod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] : IsColimit (BinaryCofan
.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr)
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary cofan constructed from the coprojection maps is a colimit.
-/
noncomputable def coprodIsCoprod (X Y : C) [HasBinaryCoproduct X Y] :
    IsColimit (BinaryCofan.mk (coprod.inl : X ⟶ X ⨿ Y) coprod.inr) :=
  (colimit.isColimit _).ofIsoColimit (Cocone.ext (Iso.refl _) (fun ⟨u⟩ => by
    cases u
    · dsimp; simp only [Category.comp_id]
    · dsimp; simp only [Category.comp_id]
  ))

@[ext 1100]
/-
**CategoryTheory.Limits.prod.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y},   Category
Theory.CategoryStruct.comp f CategoryTheory.Limits.prod.fst =       CategoryTheo
ry.CategoryStruct.comp g CategoryTheory.Limits.prod.fst →     CategoryTheory.Cat
egoryStruct.comp f CategoryTheory.Limits.prod.snd =         CategoryTheory.Categ
oryStruct.comp g CategoryTheory.Limits.prod.snd →       f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.BinaryF
an X Y}   (h : CategoryTheory.Limits.…
-/
theorem prod.hom_ext {W X Y : C} [HasBinaryProduct X Y] {f g : W ⟶ X ⨯ Y}
    (h₁ : f ≫ prod.fst = g ≫ prod.fst) (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (limit.isLimit _) h₁ h₂

@[ext 1100]
/-
**CategoryTheory.Limits.coprod.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W},   Catego
ryTheory.CategoryStruct.comp CategoryTheory.Limits.coprod.inl f =       Category
Theory.CategoryStruct.comp CategoryTheory.Limits.coprod.inl g →     CategoryTheo
ry.CategoryStruct.comp CategoryTheory.Limits.coprod.inr f =         CategoryTheo
ry.CategoryStruct.comp CategoryTheory.Limits.coprod.inr g →       f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryCofan.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Bin
aryCofan X Y}   (h : CategoryTheory.Limit…
-/
theorem coprod.hom_ext {W X Y : C} [HasBinaryCoproduct X Y] {f g : X ⨿ Y ⟶ W}
    (h₁ : coprod.inl ≫ f = coprod.inl ≫ g) (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (colimit.isColimit _) h₁ h₂

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`. -/
/-
**CategoryTheory.Limits.prod.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y : 
C} → [inst_1 : CategoryTheory.Limits.HasBinaryProduct X Y] → (W ⟶ X) → (W ⟶ Y) →
 (W ⟶ X ⨯ Y)
参数：W ⟶ X；W ⟶ Y；W ⟶ X ⨯ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` a
nd `g : W ⟶ Y`
induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`.
-/
noncomputable abbrev prod.lift {W X Y : C} [HasBinaryProduct X Y]
    (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift _ (BinaryFan.mk f g)

/-- diagonal arrow of the binary product in the category `fam I` -/
/-
**CategoryTheory.Limits.diag** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
diagonal arrow of the binary product in the category `fam I`
-/
noncomputable abbrev diag (X : C) [HasBinaryProduct X X] : X ⟶ X ⨯ X :=
  prod.lift (𝟙 _) (𝟙 _)

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`. -/
/-
**CategoryTheory.Limits.coprod.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y : 
C} → [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] → (X ⟶ W) → (Y ⟶ W)
 → (X ⨿ Y ⟶ W)
参数：X ⟶ W；Y ⟶ W；X ⨿ Y ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W`
 and
`g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`.
-/
noncomputable abbrev coprod.desc {W X Y : C} [HasBinaryCoproduct X Y]
    (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
  colimit.desc _ (BinaryCofan.mk f g)

/-- codiagonal arrow of the binary coproduct -/
/-
**CategoryTheory.Limits.codiag** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：codiag (X : C) [HasBinaryCoproduct X X] : X ⨿ X ⟶ X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
codiagonal arrow of the binary coproduct
-/
noncomputable abbrev codiag (X : C) [HasBinaryCoproduct X X] : X ⨿ X ⟶ X :=
  coprod.desc (𝟙 _) (𝟙 _)

@[reassoc]
/-
**CategoryTheory.Limits.prod.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.prod.lift f g) CategoryT
heory.Limits.prod.fst = f
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.prod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem prod.lift_fst {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.fst = f :=
  limit.lift_π _ _

@[reassoc]
/-
**CategoryTheory.Limits.prod.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.prod.lift f g) CategoryT
heory.Limits.prod.snd = g
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.prod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem prod.lift_snd {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ prod.snd = g :=
  limit.lift_π _ _

@[reassoc]
/-
**CategoryTheory.Limits.coprod.inl_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W),   
CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.coprod.inl (CategoryThe
ory.Limits.coprod.desc f g) = f
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.coprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem coprod.inl_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inl ≫ coprod.desc f g = f :=
  colimit.ι_desc _ _

@[reassoc]
/-
**CategoryTheory.Limits.coprod.inr_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W),   
CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.coprod.inr (CategoryThe
ory.Limits.coprod.desc f g) = g
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.coprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem coprod.inr_desc {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    coprod.inr ≫ coprod.desc f g = g :=
  colimit.ι_desc _ _
/-
**CategoryTheory.Limits.prod.mono_lift_of_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [Cate
goryTheory.Mono f],   CategoryTheory.Mono (CategoryTheory.Limits.prod.lift f g)
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.prod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
-/
instance prod.mono_lift_of_mono_left {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_fst _ _
/-
**CategoryTheory.Limits.prod.mono_lift_of_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [Cate
goryTheory.Mono g],   CategoryTheory.Mono (CategoryTheory.Limits.prod.lift f g)
参数：f : W ⟶ X；g : W ⟶ Y；CategoryTheory.Limits.prod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
-/
instance prod.mono_lift_of_mono_right {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (prod.lift f g) :=
  mono_of_mono_fac <| prod.lift_snd _ _
/-
**CategoryTheory.Limits.coprod.epi_desc_of_epi_left** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [Ca
tegoryTheory.Epi f],   CategoryTheory.Epi (CategoryTheory.Limits.coprod.desc f g
)
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.coprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
instance coprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inl_desc _ _
/-
**CategoryTheory.Limits.coprod.epi_desc_of_epi_right** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y : C}   [in
st_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [Ca
tegoryTheory.Epi g],   CategoryTheory.Epi (CategoryTheory.Limits.coprod.desc f g
)
参数：f : X ⟶ W；g : Y ⟶ W；CategoryTheory.Limits.coprod.desc f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
instance coprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (coprod.desc f g) :=
  epi_of_epi_fac <| coprod.inr_desc _ _

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ Prod.fst = f` and `l ≫ Prod.snd = g`. -/
/-
**CategoryTheory.Limits.prod.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y : 
C} →       [inst_1 : CategoryTheory.Limits.HasBinaryProduct X Y] →         (f : 
W ⟶ X) →           (g : W ⟶ Y) →             { l //               CategoryTheory
.CategoryStruct.comp l CategoryTheory.Limits.prod.fst = f ∧                 Cate
goryTheory.CategoryStruct.comp l CategoryTheory.Limits.prod.snd = g }
参数：f : W ⟶ X；g : W ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` a
nd `g : W ⟶ Y`
induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ Prod.fst = f` and `l ≫ Prod.s
nd = g`.
-/
noncomputable def prod.lift' {W X Y : C} [HasBinaryProduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    { l : W ⟶ X ⨯ Y // l ≫ prod.fst = f ∧ l ≫ prod.snd = g } :=
  ⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
`g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` and
`coprod.inr ≫ l = g`. -/
/-
**CategoryTheory.Limits.coprod.desc'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y : 
C} →       [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] →         (f 
: X ⟶ W) →           (g : Y ⟶ W) →             { l //               CategoryTheo
ry.CategoryStruct.comp CategoryTheory.Limits.coprod.inl l = f ∧                 
CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.coprod.inr l = g }
参数：f : X ⟶ W；g : Y ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W`
 and
`g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` a
nd
`coprod.inr ≫ l = g`.
-/
noncomputable def coprod.desc' {W X Y : C} [HasBinaryCoproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    { l : X ⨿ Y ⟶ W // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g } :=
  ⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
`g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`. -/
/-
**CategoryTheory.Limits.prod.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       [inst_1 : CategoryTheory.Limits.HasBinaryProduct W X] →         [in
st_2 : CategoryTheory.Limits.HasBinaryProduct Y Z] → (W ⟶ Y) → (X ⟶ Z) → (W ⨯ X 
⟶ Y ⨯ Z)
参数：W ⟶ Y；X ⟶ Z；W ⨯ X ⟶ Y ⨯ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶
 Y` and
`g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`.
-/
noncomputable def prod.map {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
  limMap (mapPair f g)

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
`g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`. -/
/-
**CategoryTheory.Limits.coprod.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct W X] →         [
inst_2 : CategoryTheory.Limits.HasBinaryCoproduct Y Z] → (W ⟶ Y) → (X ⟶ Z) → (W 
⨿ X ⟶ Y ⨿ Z)
参数：W ⟶ Y；X ⟶ Z；W ⨿ X ⟶ Y ⨿ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W
 ⟶ Y` and
`g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`.
-/
noncomputable def coprod.map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
  colimMap (mapPair f g)

noncomputable section ProdLemmas

set_option backward.isDefEq.respectTransparency false in
-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.
@[reassoc, simp]
/-
**CategoryTheory.Limits.prod.comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {V W X Y : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h 
: W ⟶ Y),   CategoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.prod.lif
t g h) =     CategoryTheory.Limits.prod.lift (CategoryTheory.CategoryStruct.comp
 f g) (CategoryTheory.CategoryStruct.comp f h)
参数：f : V ⟶ W；g : W ⟶ X；h : W ⟶ Y；CategoryTheory.Limits.prod.lift g h；CategoryThe
ory.CategoryStruct.comp f g；CategoryTheory.CategoryStruct.comp f h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.comp_lift {V W X Y : C} [HasBinaryProduct X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ prod.lift g h = prod.lift (f ≫ g) (f ≫ h) := by ext <;> simp
/-
**CategoryTheory.Limits.prod.comp_diag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1
 : CategoryTheory.Limits.HasBinaryProduct Y Y]   (f : X ⟶ Y), CategoryTheory.Cat
egoryStruct.comp f (CategoryTheory.Limits.diag Y) = CategoryTheory.Limits.prod.l
ift f f
参数：f : X ⟶ Y；CategoryTheory.Limits.diag Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.comp_diag {X Y : C} [HasBinaryProduct Y Y] (f : X ⟶ Y) :
    f ≫ diag Y = prod.lift f f := by simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.map_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryProduct W X] [inst_2 : CategoryTheory.Li
mits.HasBinaryProduct Y Z]   (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.prod.map f g) CategoryTheory.Limits.prod.fst =
     CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.prod.fst f
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
-/
theorem prod.map_fst {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.fst = prod.fst ≫ f :=
  limMap_π _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.map_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryProduct W X] [inst_2 : CategoryTheory.Li
mits.HasBinaryProduct Y Z]   (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryS
truct.comp (CategoryTheory.Limits.prod.map f g) CategoryTheory.Limits.prod.snd =
     CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.prod.snd g
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
-/
theorem prod.map_snd {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : prod.map f g ≫ prod.snd = prod.snd ≫ g :=
  limMap_π _ _

@[simp]
/-
**CategoryTheory.Limits.prod.map_id_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryProduct X Y],   CategoryTheory.Limits.prod.m
ap (CategoryTheory.CategoryStruct.id X) (CategoryTheory.CategoryStruct.id Y) =  
   CategoryTheory.CategoryStruct.id (X ⨯ Y)
参数：CategoryTheory.CategoryStruct.id X；CategoryTheory.CategoryStruct.id Y；X ⨯ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
-/
theorem prod.map_id_id {X Y : C} [HasBinaryProduct X Y] : prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.prod.lift_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryProduct X Y],   CategoryTheory.Limits.prod.l
ift CategoryTheory.Limits.prod.fst CategoryTheory.Limits.prod.snd =     Category
Theory.CategoryStruct.id (X ⨯ Y)
参数：X ⨯ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.lift_fst_snd {X Y : C} [HasBinaryProduct X Y] :
    prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.lift_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {V W X Y Z : C}  
 [inst_1 : CategoryTheory.Limits.HasBinaryProduct W X] [inst_2 : CategoryTheory.
Limits.HasBinaryProduct Y Z]   (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z), 
  CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.prod.lift f g) (Cate
goryTheory.Limits.prod.map h k) =     CategoryTheory.Limits.prod.lift (CategoryT
heory.CategoryStruct.comp f h) (CategoryTheory.CategoryStruct.comp g k)
参数：f : V ⟶ W；g : V ⟶ X；h : W ⟶ Y；k : X ⟶ Z；CategoryTheory.Limits.prod.lift f g；C
ategoryTheory.Limits.prod.map h k；CategoryTheory.CategoryStruct.comp f h；Categor
yTheory.CategoryStruct.comp g k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
-/
theorem prod.lift_map {V W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : V ⟶ W)
    (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
/-
**CategoryTheory.Limits.prod.lift_fst_comp_snd_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryProduct W Y] [inst_2 : CategoryTheory.Li
mits.HasBinaryProduct X Z]   (g : W ⟶ X) (g' : Y ⟶ Z),   CategoryTheory.Limits.p
rod.lift (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.prod.fst g)  
     (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.prod.snd g') =   
  CategoryTheory.Limits.prod.map g g'
参数：g : W ⟶ X；g' : Y ⟶ Z；CategoryTheory.CategoryStruct.comp CategoryTheory.Limits
.prod.fst g；CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.prod.snd g'
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryP
roduct X Y],   CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.lift_fst_comp_snd_comp {W X Y Z : C} [HasBinaryProduct W Y] [HasBinaryProduct X Z]
    (g : W ⟶ X) (g' : Y ⟶ Z) : prod.lift (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by
  rw [← prod.lift_map]
  simp

-- We take the right-hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (e.g. `id_comp`), while `map_fst` and `map_snd` can still work just
-- as well.
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.map_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B
₃ : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProduct A₁ B₁] [inst_2 : Categ
oryTheory.Limits.HasBinaryProduct A₂ B₂]   [inst_3 : CategoryTheory.Limits.HasBi
naryProduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.prod.map f g) (CategoryT
heory.Limits.prod.map h k) =     CategoryTheory.Limits.prod.map (CategoryTheory.
CategoryStruct.comp f h) (CategoryTheory.CategoryStruct.comp g k)
参数：f : A₁ ⟶ A₂；g : B₁ ⟶ B₂；h : A₂ ⟶ A₃；k : B₂ ⟶ B₃；CategoryTheory.Limits.prod.ma
p f g；CategoryTheory.Limits.prod.map h k；CategoryTheory.CategoryStruct.comp f h；
CategoryTheory.CategoryStruct.comp g k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_fst_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
-/
theorem prod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryProduct A₁ B₁] [HasBinaryProduct A₂ B₂]
    [HasBinaryProduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    prod.map f g ≫ prod.map h k = prod.map (f ≫ h) (g ≫ k) := by ext <;> simp

-- TODO: is it necessary to weaken the assumption here?
@[reassoc]
/-
**CategoryTheory.Limits.prod.map_swap** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B X Y : C} (f 
: A ⟶ B) (g : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasLimitsOfShape (Categor
yTheory.Discrete CategoryTheory.Limits.WalkingPair) C],   CategoryTheory.Categor
yStruct.comp (CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct.id X
) f)       (CategoryTheory.Limits.prod.map g (CategoryTheory.CategoryStruct.id B
)) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.prod.map g (C
ategoryTheory.CategoryStruct.id A))       (CategoryTheory.Limits.prod.map (Categ
oryTheory.CategoryStruct.id Y) f)
参数：f : A ⟶ B；g : X ⟶ Y；CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair
；CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct.id X) f；CategoryT
heory.Limits.prod.map g (CategoryTheory.CategoryStruct.id B)；CategoryTheory.Limi
ts.prod.map g (CategoryTheory.CategoryStruct.id A)；CategoryTheory.Limits.prod.ma
p (CategoryTheory.CategoryStruct.id Y) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits.H
asBinaryProduct A₁ B₁] […
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasLimitsOfShape (Discrete WalkingPair) C] :
    prod.map (𝟙 X) f ≫ prod.map g (𝟙 B) = prod.map g (𝟙 A) ≫ prod.map (𝟙 Y) f := by simp

@[reassoc]
/-
**CategoryTheory.Limits.prod.map_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z W : C} (f 
: X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasBinaryProduct X W] [in
st_2 : CategoryTheory.Limits.HasBinaryProduct Z W]   [inst_3 : CategoryTheory.Li
mits.HasBinaryProduct Y W],   CategoryTheory.Limits.prod.map (CategoryTheory.Cat
egoryStruct.comp f g) (CategoryTheory.CategoryStruct.id W) =     CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.prod.map f (CategoryTheory.CategorySt
ruct.id W))       (CategoryTheory.Limits.prod.map g (CategoryTheory.CategoryStru
ct.id W))
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Cat
egoryStruct.id W；CategoryTheory.Limits.prod.map f (CategoryTheory.CategoryStruct
.id W)；CategoryTheory.Limits.prod.map g (CategoryTheory.CategoryStruct.id W)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits.H
asBinaryProduct A₁ B₁] […
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct X W]
    [HasBinaryProduct Z W] [HasBinaryProduct Y W] :
    prod.map (f ≫ g) (𝟙 W) = prod.map f (𝟙 W) ≫ prod.map g (𝟙 W) := by simp

@[reassoc]
/-
**CategoryTheory.Limits.prod.map_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z W : C} (f 
: X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasBinaryProduct W X] [in
st_2 : CategoryTheory.Limits.HasBinaryProduct W Y]   [inst_3 : CategoryTheory.Li
mits.HasBinaryProduct W Z],   CategoryTheory.Limits.prod.map (CategoryTheory.Cat
egoryStruct.id W) (CategoryTheory.CategoryStruct.comp f g) =     CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStru
ct.id W) f)       (CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct
.id W) g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.id W；CategoryTheory.Categor
yStruct.comp f g；CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct.i
d W) f；CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct.id W) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits.H
asBinaryProduct A₁ B₁] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryProduct W X]
    [HasBinaryProduct W Y] [HasBinaryProduct W Z] :
    prod.map (𝟙 W) (f ≫ g) = prod.map (𝟙 W) f ≫ prod.map (𝟙 W) g := by simp

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : X ≅ Z` induces an isomorphism `prod.mapIso f g : W ⨯ X ≅ Y ⨯ Z`. -/
@[simps]
/-
**CategoryTheory.Limits.prod.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       [inst_1 : CategoryTheory.Limits.HasBinaryProduct W X] →         [in
st_2 : CategoryTheory.Limits.HasBinaryProduct Y Z] → (W ≅ Y) → (X ≅ Z) → (W ⨯ X 
≅ Y ⨯ Z)
参数：W ≅ Y；X ≅ Z；W ⨯ X ≅ Y ⨯ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : 
W ≅ Y` and
`g : X ≅ Z` induces an isomorphism `prod.mapIso f g : W ⨯ X ≅ Y ⨯ Z`.
-/
def prod.mapIso {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨯ X ≅ Y ⨯ Z where
  hom := prod.map f.hom g.hom
  inv := prod.map f.inv g.inv
/-
**CategoryTheory.Limits.isIso_prod** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：isIso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f 
: W ⟶ Y) (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (prod.map f g)
参数：f : W ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_prod {W X Y Z : C} [HasBinaryProduct W X] [HasBinaryProduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (prod.map f g) :=
  (prod.mapIso (asIso f) (asIso g)).isIso_hom
/-
**CategoryTheory.Limits.prod.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} (f : W ⟶ Y) (g : X ⟶ Z)   [CategoryTheory.Mono f] [CategoryTheory.Mono g] [in
st_3 : CategoryTheory.Limits.HasBinaryProduct W X]   [inst_4 : CategoryTheory.Li
mits.HasBinaryProduct Y Z], CategoryTheory.Mono (CategoryTheory.Limits.prod.map 
f g)
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
-/
instance prod.map_mono {C : Type*} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryProduct W X] [HasBinaryProduct Y Z] : Mono (prod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_mono f]
      simpa using congr_arg (fun f => f ≫ prod.fst) h
    · rw [← cancel_mono g]
      simpa using congr_arg (fun f => f ≫ prod.snd) h⟩

@[reassoc]
/-
**CategoryTheory.Limits.prod.diag_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y)   [inst_1 : CategoryTheory.Limits.HasBinaryProduct X X] [inst_2 : CategoryT
heory.Limits.HasBinaryProduct Y Y],   CategoryTheory.CategoryStruct.comp (Catego
ryTheory.Limits.diag X) (CategoryTheory.Limits.prod.map f f) =     CategoryTheor
y.CategoryStruct.comp f (CategoryTheory.Limits.diag Y)
参数：f : X ⟶ Y；CategoryTheory.Limits.diag X；CategoryTheory.Limits.prod.map f f；Cat
egoryTheory.Limits.diag Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.diag_map {X Y : C} (f : X ⟶ Y) [HasBinaryProduct X X] [HasBinaryProduct Y Y] :
    diag X ≫ prod.map f f = f ≫ diag Y := by simp

@[reassoc]
/-
**CategoryTheory.Limits.prod.diag_map_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1
 : CategoryTheory.Limits.HasBinaryProduct X Y]   [inst_2 : CategoryTheory.Limits
.HasBinaryProduct (X ⨯ Y) (X ⨯ Y)],   CategoryTheory.CategoryStruct.comp (Catego
ryTheory.Limits.diag (X ⨯ Y))       (CategoryTheory.Limits.prod.map CategoryTheo
ry.Limits.prod.fst CategoryTheory.Limits.prod.snd) =     CategoryTheory.Category
Struct.id (X ⨯ Y)
参数：X ⨯ Y；X ⨯ Y；CategoryTheory.Limits.diag (X ⨯ Y)；CategoryTheory.Limits.prod.map
 CategoryTheory.Limits.prod.fst CategoryTheory.Limits.prod.snd；X ⨯ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryP
roduct X Y],   CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.diag_map_fst_snd {X Y : C} [HasBinaryProduct X Y] [HasBinaryProduct (X ⨯ Y) (X ⨯ Y)] :
    diag (X ⨯ Y) ≫ prod.map prod.fst prod.snd = 𝟙 (X ⨯ Y) := by simp

@[reassoc]
/-
**CategoryTheory.Limits.prod.diag_map_fst_snd_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.Limits.HasLimitsOfShape (CategoryTheory.Discrete CategoryTheory.Limits
.WalkingPair) C]   {X X' Y Y' : C} (g : X ⟶ Y) (g' : X' ⟶ Y'),   CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.diag (X ⨯ X'))       (CategoryTheory.
Limits.prod.map (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.prod.f
st g)         (CategoryTheory.CategoryStruct.comp CategoryTheory.Limits.prod.snd
 g')) =     CategoryTheory.Limits.prod.map g g'
参数：CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair；g : X ⟶ Y；g' : X' ⟶
 Y'；CategoryTheory.Limits.diag (X ⨯ X')；CategoryTheory.Limits.prod.map (Category
Theory.CategoryStruct.comp CategoryTheory.Limits.prod.fst g)         (CategoryTh
eory.CategoryStruct.comp CategoryTheory.Limits.prod.snd g')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_comp_snd_comp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Lim
its.HasBinaryProduct W Y] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.diag_map_fst_snd_comp [HasLimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    diag (X ⨯ X') ≫ prod.map (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' := by simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} [HasBinaryProduct X X] : IsSplitMono (diag X) :=
  IsSplitMono.mk' { retraction := prod.fst }

end ProdLemmas

noncomputable section CoprodLemmas

set_option backward.isDefEq.respectTransparency false in
@[reassoc, simp]
/-
**CategoryTheory.Limits.coprod.desc_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {V W X Y : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V) (
h : Y ⟶ V),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.d
esc g h) f =     CategoryTheory.Limits.coprod.desc (CategoryTheory.CategoryStruc
t.comp g f) (CategoryTheory.CategoryStruct.comp h f)
参数：f : V ⟶ W；g : X ⟶ V；h : Y ⟶ V；CategoryTheory.Limits.coprod.desc g h；CategoryT
heory.CategoryStruct.comp g f；CategoryTheory.CategoryStruct.comp h f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.desc_comp {V W X Y : C} [HasBinaryCoproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
    (h : Y ⟶ V) : coprod.desc g h ≫ f = coprod.desc (g ≫ f) (h ≫ f) := by
  ext <;> simp
/-
**CategoryTheory.Limits.coprod.diag_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryCoproduct X X] (f : X ⟶ Y),   CategoryTheory
.CategoryStruct.comp (CategoryTheory.Limits.codiag X) f = CategoryTheory.Limits.
coprod.desc f f
参数：f : X ⟶ Y；CategoryTheory.Limits.codiag X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.diag_comp {X Y : C} [HasBinaryCoproduct X X] (f : X ⟶ Y) :
    codiag X ≫ f = coprod.desc f f := by simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprod.inl_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryCoproduct W X] [inst_2 : CategoryTheory.
Limits.HasBinaryCoproduct Y Z]   (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.Categ
oryStruct.comp CategoryTheory.Limits.coprod.inl (CategoryTheory.Limits.coprod.ma
p f g) =     CategoryTheory.CategoryStruct.comp f CategoryTheory.Limits.coprod.i
nl
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.coprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
-/
theorem coprod.inl_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inl ≫ coprod.map f g = f ≫ coprod.inl :=
  ι_colimMap _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprod.inr_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryCoproduct W X] [inst_2 : CategoryTheory.
Limits.HasBinaryCoproduct Y Z]   (f : W ⟶ Y) (g : X ⟶ Z),   CategoryTheory.Categ
oryStruct.comp CategoryTheory.Limits.coprod.inr (CategoryTheory.Limits.coprod.ma
p f g) =     CategoryTheory.CategoryStruct.comp g CategoryTheory.Limits.coprod.i
nr
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.coprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
-/
theorem coprod.inr_map {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : coprod.inr ≫ coprod.map f g = g ≫ coprod.inr :=
  ι_colimMap _ _

@[simp]
/-
**CategoryTheory.Limits.coprod.map_id_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y],   CategoryTheory.Limits.copr
od.map (CategoryTheory.CategoryStruct.id X) (CategoryTheory.CategoryStruct.id Y)
 =     CategoryTheory.CategoryStruct.id (X ⨿ Y)
参数：CategoryTheory.CategoryStruct.id X；CategoryTheory.CategoryStruct.id Y；X ⨿ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
-/
theorem coprod.map_id_id {X Y : C} [HasBinaryCoproduct X Y] : coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.coprod.desc_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y],   CategoryTheory.Limits.copr
od.desc CategoryTheory.Limits.coprod.inl CategoryTheory.Limits.coprod.inr =     
CategoryTheory.CategoryStruct.id (X ⨿ Y)
参数：X ⨿ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.desc_inl_inr {X Y : C} [HasBinaryCoproduct X Y] :
    coprod.desc coprod.inl coprod.inr = 𝟙 (X ⨿ Y) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
-- The simp linter says simp can prove the reassoc version of this lemma.
@[reassoc, simp]
/-
**CategoryTheory.Limits.coprod.map_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {S T U V W : C}  
 [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct U W] [inst_2 : CategoryTheor
y.Limits.HasBinaryCoproduct T V]   (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ 
W),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.map h k) 
(CategoryTheory.Limits.coprod.desc f g) =     CategoryTheory.Limits.coprod.desc 
(CategoryTheory.CategoryStruct.comp h f) (CategoryTheory.CategoryStruct.comp k g
)
参数：f : U ⟶ S；g : W ⟶ S；h : T ⟶ U；k : V ⟶ W；CategoryTheory.Limits.coprod.map h k；
CategoryTheory.Limits.coprod.desc f g；CategoryTheory.CategoryStruct.comp h f；Cat
egoryTheory.CategoryStruct.comp k g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.coprod.inr_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
-/
theorem coprod.map_desc {S T U V W : C} [HasBinaryCoproduct U W] [HasBinaryCoproduct T V]
    (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
    coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) := by
  ext <;> simp

@[simp]
/-
**CategoryTheory.Limits.coprod.desc_comp_inl_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [
inst_1 : CategoryTheory.Limits.HasBinaryCoproduct W Y] [inst_2 : CategoryTheory.
Limits.HasBinaryCoproduct X Z]   (g : W ⟶ X) (g' : Y ⟶ Z),   CategoryTheory.Limi
ts.coprod.desc (CategoryTheory.CategoryStruct.comp g CategoryTheory.Limits.copro
d.inl)       (CategoryTheory.CategoryStruct.comp g' CategoryTheory.Limits.coprod
.inr) =     CategoryTheory.Limits.coprod.map g g'
参数：g : W ⟶ X；g' : Y ⟶ Z；CategoryTheory.CategoryStruct.comp g CategoryTheory.Limi
ts.coprod.inl；CategoryTheory.CategoryStruct.comp g' CategoryTheory.Limits.coprod
.inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.desc_inl_inr`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yCoproduct X Y],   CategoryTheo…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.desc_comp_inl_comp_inr {W X Y Z : C} [HasBinaryCoproduct W Y]
    [HasBinaryCoproduct X Z] (g : W ⟶ X) (g' : Y ⟶ Z) :
    coprod.desc (g ≫ coprod.inl) (g' ≫ coprod.inr) = coprod.map g g' := by
  rw [← coprod.map_desc]; simp

-- We take the right-hand side here to be simp normal form, as this way composition lemmas for
-- `f ≫ h` and `g ≫ k` can fire (e.g. `id_comp`), while `inl_map` and `inr_map` can still work just
-- as well.
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprod.map_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B
₃ : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct A₁ B₁] [inst_2 : Cat
egoryTheory.Limits.HasBinaryCoproduct A₂ B₂]   [inst_3 : CategoryTheory.Limits.H
asBinaryCoproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃)
,   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.map f g) (C
ategoryTheory.Limits.coprod.map h k) =     CategoryTheory.Limits.coprod.map (Cat
egoryTheory.CategoryStruct.comp f h) (CategoryTheory.CategoryStruct.comp g k)
参数：f : A₁ ⟶ A₂；g : B₁ ⟶ B₂；h : A₂ ⟶ A₃；k : B₂ ⟶ B₃；CategoryTheory.Limits.coprod.
map f g；CategoryTheory.Limits.coprod.map h k；CategoryTheory.CategoryStruct.comp 
f h；CategoryTheory.CategoryStruct.comp g k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.coprod.inr_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
-/
theorem coprod.map_map {A₁ A₂ A₃ B₁ B₂ B₃ : C} [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
    [HasBinaryCoproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) := by
  ext <;> simp

-- I don't think it's a good idea to make any of the following three simp lemmas.
@[reassoc]
/-
**CategoryTheory.Limits.coprod.map_swap** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A B X Y : C} (f 
: A ⟶ B) (g : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasColimitsOfShape (Categ
oryTheory.Discrete CategoryTheory.Limits.WalkingPair) C],   CategoryTheory.Categ
oryStruct.comp (CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStruct.
id X) f)       (CategoryTheory.Limits.coprod.map g (CategoryTheory.CategoryStruc
t.id B)) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.
map g (CategoryTheory.CategoryStruct.id A))       (CategoryTheory.Limits.coprod.
map (CategoryTheory.CategoryStruct.id Y) f)
参数：f : A ⟶ B；g : X ⟶ Y；CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair
；CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStruct.id X) f；Categor
yTheory.Limits.coprod.map g (CategoryTheory.CategoryStruct.id B)；CategoryTheory.
Limits.coprod.map g (CategoryTheory.CategoryStruct.id A)；CategoryTheory.Limits.c
oprod.map (CategoryTheory.CategoryStruct.id Y) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.map_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits
.HasBinaryCoproduct A₁ B₁]…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.map_swap {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    [HasColimitsOfShape (Discrete WalkingPair) C] :
    coprod.map (𝟙 X) f ≫ coprod.map g (𝟙 B) = coprod.map g (𝟙 A) ≫ coprod.map (𝟙 Y) f := by simp

@[reassoc]
/-
**CategoryTheory.Limits.coprod.map_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z W : C} (f 
: X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct Z W] [
inst_2 : CategoryTheory.Limits.HasBinaryCoproduct Y W]   [inst_3 : CategoryTheor
y.Limits.HasBinaryCoproduct X W],   CategoryTheory.Limits.coprod.map (CategoryTh
eory.CategoryStruct.comp f g) (CategoryTheory.CategoryStruct.id W) =     Categor
yTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.map f (CategoryTheory.
CategoryStruct.id W))       (CategoryTheory.Limits.coprod.map g (CategoryTheory.
CategoryStruct.id W))
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Cat
egoryStruct.id W；CategoryTheory.Limits.coprod.map f (CategoryTheory.CategoryStru
ct.id W)；CategoryTheory.Limits.coprod.map g (CategoryTheory.CategoryStruct.id W)
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.map_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits
.HasBinaryCoproduct A₁ B₁]…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct Z W]
    [HasBinaryCoproduct Y W] [HasBinaryCoproduct X W] :
    coprod.map (f ≫ g) (𝟙 W) = coprod.map f (𝟙 W) ≫ coprod.map g (𝟙 W) := by simp

@[reassoc]
/-
**CategoryTheory.Limits.coprod.map_id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z W : C} (f 
: X ⟶ Y) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct W X] [
inst_2 : CategoryTheory.Limits.HasBinaryCoproduct W Y]   [inst_3 : CategoryTheor
y.Limits.HasBinaryCoproduct W Z],   CategoryTheory.Limits.coprod.map (CategoryTh
eory.CategoryStruct.id W) (CategoryTheory.CategoryStruct.comp f g) =     Categor
yTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.map (CategoryTheory.Ca
tegoryStruct.id W) f)       (CategoryTheory.Limits.coprod.map (CategoryTheory.Ca
tegoryStruct.id W) g)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.id W；CategoryTheory.Categor
yStruct.comp f g；CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStruct
.id W) f；CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStruct.id W) g
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.map_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits
.HasBinaryCoproduct A₁ B₁]…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasBinaryCoproduct W X]
    [HasBinaryCoproduct W Y] [HasBinaryCoproduct W Z] :
    coprod.map (𝟙 W) (f ≫ g) = coprod.map (𝟙 W) f ≫ coprod.map (𝟙 W) g := by simp

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
`g : W ≅ Z` induces an isomorphism `coprod.mapIso f g : W ⨿ X ≅ Y ⨿ Z`. -/
@[simps]
/-
**CategoryTheory.Limits.coprod.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct W X] →         [
inst_2 : CategoryTheory.Limits.HasBinaryCoproduct Y Z] → (W ≅ Y) → (X ≅ Z) → (W 
⨿ X ≅ Y ⨿ Z)
参数：W ≅ Y；X ≅ Z；W ⨿ X ≅ Y ⨿ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f 
: W ≅ Y` and
`g : W ≅ Z` induces an isomorphism `coprod.mapIso f g : W ⨿ X ≅ Y ⨿ Z`.
-/
def coprod.mapIso {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⨿ X ≅ Y ⨿ Z where
  hom := coprod.map f.hom g.hom
  inv := coprod.map f.inv g.inv
/-
**CategoryTheory.Limits.isIso_coprod** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：isIso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y 
Z] (f : W ⟶ Y) (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (coprod.map f g)
参数：f : W ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_coprod {W X Y Z : C} [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) [IsIso f] [IsIso g] : IsIso (coprod.map f g) :=
  (coprod.mapIso (asIso f) (asIso g)).isIso_hom
/-
**CategoryTheory.Limits.coprod.map_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} (f : W ⟶ Y) (g : X ⟶ Z)   [CategoryTheory.Epi f] [CategoryTheory.Epi g] [inst
_3 : CategoryTheory.Limits.HasBinaryCoproduct W X]   [inst_4 : CategoryTheory.Li
mits.HasBinaryCoproduct Y Z], CategoryTheory.Epi (CategoryTheory.Limits.coprod.m
ap f g)
参数：f : W ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.coprod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.coprod.inl_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.inr_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
-/
instance coprod.map_epi {C : Type*} [Category* C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryCoproduct W X] [HasBinaryCoproduct Y Z] : Epi (coprod.map f g) :=
  ⟨fun i₁ i₂ h => by
    ext
    · rw [← cancel_epi f]
      simpa using congr_arg (fun f => coprod.inl ≫ f) h
    · rw [← cancel_epi g]
      simpa using congr_arg (fun f => coprod.inr ≫ f) h⟩

@[reassoc]
/-
**CategoryTheory.Limits.coprod.map_codiag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y)   [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct X X] [inst_2 : Categor
yTheory.Limits.HasBinaryCoproduct Y Y],   CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Limits.coprod.map f f) (CategoryTheory.Limits.codiag Y) =     Categ
oryTheory.CategoryStruct.comp (CategoryTheory.Limits.codiag X) f
参数：f : X ⟶ Y；CategoryTheory.Limits.coprod.map f f；CategoryTheory.Limits.codiag Y
；CategoryTheory.Limits.codiag X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.map_codiag {X Y : C} (f : X ⟶ Y) [HasBinaryCoproduct X X] [HasBinaryCoproduct Y Y] :
    coprod.map f f ≫ codiag Y = codiag X ≫ f := by simp

@[reassoc]
/-
**CategoryTheory.Limits.coprod.map_inl_inr_codiag** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryCoproduct X Y]   [inst_2 : CategoryTheory.Li
mits.HasBinaryCoproduct (X ⨿ Y) (X ⨿ Y)],   CategoryTheory.CategoryStruct.comp  
     (CategoryTheory.Limits.coprod.map CategoryTheory.Limits.coprod.inl Category
Theory.Limits.coprod.inr)       (CategoryTheory.Limits.codiag (X ⨿ Y)) =     Cat
egoryTheory.CategoryStruct.id (X ⨿ Y)
参数：X ⨿ Y；X ⨿ Y；CategoryTheory.Limits.coprod.map CategoryTheory.Limits.coprod.inl
 CategoryTheory.Limits.coprod.inr；CategoryTheory.Limits.codiag (X ⨿ Y)；X ⨿ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.coprod.desc_inl_inr`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yCoproduct X Y],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.map_inl_inr_codiag {X Y : C} [HasBinaryCoproduct X Y]
    [HasBinaryCoproduct (X ⨿ Y) (X ⨿ Y)] :
    coprod.map coprod.inl coprod.inr ≫ codiag (X ⨿ Y) = 𝟙 (X ⨿ Y) := by simp

@[reassoc]
/-
**CategoryTheory.Limits.coprod.map_comp_inl_inr_codiag** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.Limits.HasColimitsOfShape (CategoryTheory.Discrete CategoryTheory.Limi
ts.WalkingPair) C]   {X X' Y Y' : C} (g : X ⟶ Y) (g' : X' ⟶ Y'),   CategoryTheor
y.CategoryStruct.comp       (CategoryTheory.Limits.coprod.map (CategoryTheory.Ca
tegoryStruct.comp g CategoryTheory.Limits.coprod.inl)         (CategoryTheory.Ca
tegoryStruct.comp g' CategoryTheory.Limits.coprod.inr))       (CategoryTheory.Li
mits.codiag (Y ⨿ Y')) =     CategoryTheory.Limits.coprod.map g g'
参数：CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair；g : X ⟶ Y；g' : X' ⟶
 Y'；CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStruct.comp g Categ
oryTheory.Limits.coprod.inl)         (CategoryTheory.CategoryStruct.comp g' Cate
goryTheory.Limits.coprod.inr)；CategoryTheory.Limits.codiag (Y ⨿ Y')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp_inl_comp_inr`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.L
imits.HasBinaryCoproduct W Y] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.map_comp_inl_inr_codiag [HasColimitsOfShape (Discrete WalkingPair) C] {X X' Y Y' : C}
    (g : X ⟶ Y) (g' : X' ⟶ Y') :
    coprod.map (g ≫ coprod.inl) (g' ≫ coprod.inr) ≫ codiag (Y ⨿ Y') = coprod.map g g' := by simp

end CoprodLemmas

variable (C)

/-- A category `HasBinaryProducts` if it has all limits of shape `Discrete WalkingPair`,
i.e. if it has a product for every pair of objects. -/
@[stacks 001T]
/-
**CategoryTheory.Limits.HasBinaryProducts** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：HasBinaryProducts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasBinaryProducts` if it has all limits of shape `Discrete WalkingPa
ir`,
i.e. if it has a product for every pair of objects.
-/
abbrev HasBinaryProducts :=
  HasLimitsOfShape (Discrete WalkingPair) C

/-- A category `HasBinaryCoproducts` if it has all colimit of shape `Discrete WalkingPair`,
i.e. if it has a coproduct for every pair of objects. -/
@[stacks 04AP]
/-
**CategoryTheory.Limits.HasBinaryCoproducts** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：HasBinaryCoproducts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasBinaryCoproducts` if it has all colimit of shape `Discrete Walkin
gPair`,
i.e. if it has a coproduct for every pair of objects.
-/
abbrev HasBinaryCoproducts :=
  HasColimitsOfShape (Discrete WalkingPair) C

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
/-
**CategoryTheory.Limits.hasBinaryProducts_of_hasLimit_pair** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasBinaryProducts_of_hasLimit_pair [forall {X Y : C}, HasLimit (pair X Y)]
 : HasBinaryProducts C
参数：pair X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G

--- 原说明 ---
If `C` has all limits of diagrams `pair X Y`, then it has all binary products
-/
theorem hasBinaryProducts_of_hasLimit_pair [∀ {X Y : C}, HasLimit (pair X Y)] :
    HasBinaryProducts C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoPair F).symm }

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
/-
**CategoryTheory.Limits.hasBinaryCoproducts_of_hasColimit_pair** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasBinaryCoproducts_of_hasColimit_pair [forall {X Y : C}, HasColimit (pair
 X Y)] : HasBinaryCoproducts C
参数：pair X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G

--- 原说明 ---
If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproduct
s
-/
theorem hasBinaryCoproducts_of_hasColimit_pair [∀ {X Y : C}, HasColimit (pair X Y)] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoPair F) }

noncomputable section

variable {C}

set_option backward.isDefEq.respectTransparency false in
/-- The braiding isomorphism which swaps a binary product. -/
@[simps]
/-
**CategoryTheory.Limits.prod.braiding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (P Q : C)
 →       [inst_1 : CategoryTheory.Limits.HasBinaryProduct P Q] →         [inst_2
 : CategoryTheory.Limits.HasBinaryProduct Q P] → P ⨯ Q ≅ Q ⨯ P
参数：P Q : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The braiding isomorphism which swaps a binary product.
-/
def prod.braiding (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] : P ⨯ Q ≅ Q ⨯ P where
  hom := prod.lift prod.snd prod.fst
  inv := prod.lift prod.snd prod.fst

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/-
**CategoryTheory.Limits.braid_natural** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) 
: prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g 
f
参数：f : X ⟶ Y；g : Z ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.braiding_hom`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] (P Q : C) [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct P Q]   [inst_2 : Categor…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The braiding isomorphism can be passed through a map by swapping the order.
-/
theorem braid_natural [HasBinaryProducts C] {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g f := by simp

@[reassoc]
/-
**CategoryTheory.Limits.prod.symmetry'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P Q : C) [inst_1
 : CategoryTheory.Limits.HasBinaryProduct P Q]   [inst_2 : CategoryTheory.Limits
.HasBinaryProduct Q P],   CategoryTheory.CategoryStruct.comp       (CategoryTheo
ry.Limits.prod.lift CategoryTheory.Limits.prod.snd CategoryTheory.Limits.prod.fs
t)       (CategoryTheory.Limits.prod.lift CategoryTheory.Limits.prod.snd Categor
yTheory.Limits.prod.fst) =     CategoryTheory.CategoryStruct.id (P ⨯ Q)
参数：P Q : C；CategoryTheory.Limits.prod.lift CategoryTheory.Limits.prod.snd Catego
ryTheory.Limits.prod.fst；CategoryTheory.Limits.prod.lift CategoryTheory.Limits.p
rod.snd CategoryTheory.Limits.prod.fst；P ⨯ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
theorem prod.symmetry' (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
  (prod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
/-
**CategoryTheory.Limits.prod.symmetry** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P Q : C) [inst_1
 : CategoryTheory.Limits.HasBinaryProduct P Q]   [inst_2 : CategoryTheory.Limits
.HasBinaryProduct Q P],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Lim
its.prod.braiding P Q).hom       (CategoryTheory.Limits.prod.braiding Q P).hom =
     CategoryTheory.CategoryStruct.id (P ⨯ Q)
参数：P Q : C；CategoryTheory.Limits.prod.braiding P Q；CategoryTheory.Limits.prod.br
aiding Q P；P ⨯ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …

--- 原说明 ---
The braiding isomorphism is symmetric.
-/
theorem prod.symmetry (P Q : C) [HasBinaryProduct P Q] [HasBinaryProduct Q P] :
    (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
  (prod.braiding _ _).hom_inv_id

set_option backward.isDefEq.respectTransparency false in
/-- The associator isomorphism for binary products. -/
@[simps]
/-
**CategoryTheory.Limits.prod.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasBinaryProducts C] → (P Q R : C) → (P ⨯ Q) ⨯ R ≅ P ⨯ Q 
⨯ R
参数：P Q R : C；P ⨯ Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism for binary products.
-/
def prod.associator [HasBinaryProducts C] (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ Q ⨯ R where
  hom := prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
  inv := prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.prod.pentagon** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasBinaryProducts C]   (W X Y Z : C),   CategoryTheory.CategorySt
ruct.comp       (CategoryTheory.Limits.prod.map (CategoryTheory.Limits.prod.asso
ciator W X Y).hom         (CategoryTheory.CategoryStruct.id Z))       (CategoryT
heory.CategoryStruct.comp (CategoryTheory.Limits.prod.associator W (X ⨯ Y) Z).ho
m         (CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct.id W)  
         (CategoryTheory.Limits.prod.associator X Y Z).hom)) =     CategoryTheor
y.CategoryStruct.comp (CategoryTheory.Limits.prod.associator (W ⨯ X) Y Z).hom   
    (CategoryTheory.Limits.prod.associator W X (Y ⨯ Z)).hom
参数：W X Y Z : C；CategoryTheory.Limits.prod.map (CategoryTheory.Limits.prod.associ
ator W X Y).hom         (CategoryTheory.CategoryStruct.id Z)；CategoryTheory.Cate
goryStruct.comp (CategoryTheory.Limits.prod.associator W (X ⨯ Y) Z).hom         
(CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct.id W)           (
CategoryTheory.Limits.prod.associator X Y Z).hom)；CategoryTheory.Limits.prod.ass
ociator (W ⨯ X) Y Z；CategoryTheory.Limits.prod.associator W X (Y ⨯ Z)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.associator_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryProducts C]
   (P Q R : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.map_fst_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.pentagon [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (prod.associator W X Y).hom (𝟙 Z) ≫
        (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) (prod.associator X Y Z).hom =
      (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y ⨯ Z)).hom := by
  simp

@[reassoc]
/-
**CategoryTheory.Limits.prod.associator_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasBinaryProducts C]   {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂
 : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.prod.map (CategoryTheory.Limits.prod.map f₁ f₂) f₃)       (CategoryTheor
y.Limits.prod.associator Y₁ Y₂ Y₃).hom =     CategoryTheory.CategoryStruct.comp 
(CategoryTheory.Limits.prod.associator X₁ X₂ X₃).hom       (CategoryTheory.Limit
s.prod.map f₁ (CategoryTheory.Limits.prod.map f₂ f₃))
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃；CategoryTheory.Limits.prod.map (Catego
ryTheory.Limits.prod.map f₁ f₂) f₃；CategoryTheory.Limits.prod.associator Y₁ Y₂ Y
₃；CategoryTheory.Limits.prod.associator X₁ X₂ X₃；CategoryTheory.Limits.prod.map 
f₁ (CategoryTheory.Limits.prod.map f₂ f₃)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prod.associator_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryProducts C]
   (P Q R : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.map_fst_assoc`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBi
naryProduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.lift_fst_comp_snd_comp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Lim
its.HasBinaryProduct W Y] [inst_2 : Cat…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod.associator_naturality [HasBinaryProducts C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
      (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) := by
  simp

variable [HasTerminal C]

set_option backward.isDefEq.respectTransparency false in
/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps]
/-
**CategoryTheory.Limits.prod.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasTerminal C] →       (P : C) → [inst_2 : CategoryTheory
.Limits.HasBinaryProduct (⊤_ C) P] → (⊤_ C) ⨯ P ≅ P
参数：P : C；⊤_ C；⊤_ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left unitor isomorphism for binary products with the terminal object.
-/
def prod.leftUnitor (P : C) [HasBinaryProduct (⊤_ C) P] : (⊤_ C) ⨯ P ≅ P where
  hom := prod.snd
  inv := prod.lift (terminal.from P) (𝟙 _)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps]
/-
**CategoryTheory.Limits.prod.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasTerminal C] →       (P : C) → [inst_2 : CategoryTheory
.Limits.HasBinaryProduct P (⊤_ C)] → P ⨯ ⊤_ C ≅ P
参数：P : C；⊤_ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right unitor isomorphism for binary products with the terminal object.
-/
def prod.rightUnitor (P : C) [HasBinaryProduct P (⊤_ C)] : P ⨯ ⊤_ C ≅ P where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (terminal.from P)
  hom_inv_id := by apply prod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp

@[reassoc]
/-
**CategoryTheory.Limits.prod.leftUnitor_hom_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1
 : CategoryTheory.Limits.HasTerminal C]   [inst_2 : CategoryTheory.Limits.HasBin
aryProducts C] (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.prod.map (CategoryTheory.CategoryStruct.id (⊤_ C)) f)       (CategoryThe
ory.Limits.prod.leftUnitor Y).hom =     CategoryTheory.CategoryStruct.comp (Cate
goryTheory.Limits.prod.leftUnitor X).hom f
参数：f : X ⟶ Y；CategoryTheory.Limits.prod.map (CategoryTheory.CategoryStruct.id (⊤
_ C)) f；CategoryTheory.Limits.prod.leftUnitor Y；CategoryTheory.Limits.prod.leftU
nitor X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem prod.leftUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map (𝟙 _) f ≫ (prod.leftUnitor Y).hom = (prod.leftUnitor X).hom ≫ f :=
  prod.map_snd _ _

@[reassoc]
/-
**CategoryTheory.Limits.prod.leftUnitor_inv_naturality** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1
 : CategoryTheory.Limits.HasTerminal C]   [inst_2 : CategoryTheory.Limits.HasBin
aryProducts C] (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.prod.leftUnitor X).inv       (CategoryTheory.Limits.prod.map (CategoryTh
eory.CategoryStruct.id (⊤_ C)) f) =     CategoryTheory.CategoryStruct.comp f (Ca
tegoryTheory.Limits.prod.leftUnitor Y).inv
参数：f : X ⟶ Y；CategoryTheory.Limits.prod.leftUnitor X；CategoryTheory.Limits.prod.
map (CategoryTheory.CategoryStruct.id (⊤_ C)) f；CategoryTheory.Limits.prod.leftU
nitor Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Limits.prod.leftUnitor_hom_naturality`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limits
.HasTerminal C]   [inst_2 : CategoryTheory…
-/
theorem prod.leftUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.leftUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.leftUnitor_hom_naturality]

@[reassoc]
/-
**CategoryTheory.Limits.prod.rightUnitor_hom_naturality** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1
 : CategoryTheory.Limits.HasTerminal C]   [inst_2 : CategoryTheory.Limits.HasBin
aryProducts C] (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (CategoryTheory
.Limits.prod.map f (CategoryTheory.CategoryStruct.id (⊤_ C)))       (CategoryThe
ory.Limits.prod.rightUnitor Y).hom =     CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.Limits.prod.rightUnitor X).hom f
参数：f : X ⟶ Y；CategoryTheory.Limits.prod.map f (CategoryTheory.CategoryStruct.id 
(⊤_ C))；CategoryTheory.Limits.prod.rightUnitor Y；CategoryTheory.Limits.prod.righ
tUnitor X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem prod.rightUnitor_hom_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    prod.map f (𝟙 _) ≫ (prod.rightUnitor Y).hom = (prod.rightUnitor X).hom ≫ f :=
  prod.map_fst _ _

@[reassoc]
/-
**CategoryTheory.Limits.prod_rightUnitor_inv_naturality** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：prod_rightUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) : (prod.
rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Limits.prod.rightUnitor_hom_naturality`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory.Limit
s.HasTerminal C]   [inst_2 : CategoryTheory…
-/
theorem prod_rightUnitor_inv_naturality [HasBinaryProducts C] (f : X ⟶ Y) :
    (prod.rightUnitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.rightUnitor Y).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, prod.rightUnitor_hom_naturality]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.prod.triangle** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasTerminal C]   [inst_2 : CategoryTheory.Limits.HasBinaryProduct
s C] (X Y : C),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.prod
.associator X (⊤_ C) Y).hom       (CategoryTheory.Limits.prod.map (CategoryTheor
y.CategoryStruct.id X)         (CategoryTheory.Limits.prod.leftUnitor Y).hom) = 
    CategoryTheory.Limits.prod.map (CategoryTheory.Limits.prod.rightUnitor X).ho
m (CategoryTheory.CategoryStruct.id Y)
参数：X Y : C；CategoryTheory.Limits.prod.associator X (⊤_ C) Y；CategoryTheory.Limit
s.prod.map (CategoryTheory.CategoryStruct.id X)         (CategoryTheory.Limits.p
rod.leftUnitor Y).hom；CategoryTheory.Limits.prod.rightUnitor X；CategoryTheory.Ca
tegoryStruct.id Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.associator_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryProducts C]
   (P Q R : C),   (CategoryTheo…
· 使用定理 `CategoryTheory.Limits.prod.leftUnitor_hom`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] (P : 
C)   [inst_2 : CategoryTheory.L…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.prod.rightUnitor_hom`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] (P :
 C)   [inst_2 : CategoryTheory.L…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
-/
theorem prod.triangle [HasBinaryProducts C] (X Y : C) :
    (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) (prod.leftUnitor Y).hom =
      prod.map (prod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section

variable {C}
variable [HasBinaryCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps]
/-
**CategoryTheory.Limits.coprod.braiding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasBinaryCoproducts C] → (P Q : C) → P ⨿ Q ≅ Q ⨿ P
参数：P Q : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The braiding isomorphism which swaps a binary coproduct.
-/
def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P where
  hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl

@[reassoc]
/-
**CategoryTheory.Limits.coprod.symmetry'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasBinaryCoproducts C]   (P Q : C),   CategoryTheory.CategoryStru
ct.comp       (CategoryTheory.Limits.coprod.desc CategoryTheory.Limits.coprod.in
r CategoryTheory.Limits.coprod.inl)       (CategoryTheory.Limits.coprod.desc Cat
egoryTheory.Limits.coprod.inr CategoryTheory.Limits.coprod.inl) =     CategoryTh
eory.CategoryStruct.id (P ⨿ Q)
参数：P Q : C；CategoryTheory.Limits.coprod.desc CategoryTheory.Limits.coprod.inr Ca
tegoryTheory.Limits.coprod.inl；CategoryTheory.Limits.coprod.desc CategoryTheory.
Limits.coprod.inr CategoryTheory.Limits.coprod.inl；P ⨿ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
theorem coprod.symmetry' (P Q : C) :
    coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
  (coprod.braiding _ _).hom_inv_id

/-- The braiding isomorphism is symmetric. -/
/-
**CategoryTheory.Limits.coprod.symmetry** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasBinaryCoproducts C]   (P Q : C),   CategoryTheory.CategoryStru
ct.comp (CategoryTheory.Limits.coprod.braiding P Q).hom       (CategoryTheory.Li
mits.coprod.braiding Q P).hom =     CategoryTheory.CategoryStruct.id (P ⨿ Q)
参数：P Q : C；CategoryTheory.Limits.coprod.braiding P Q；CategoryTheory.Limits.copro
d.braiding Q P；P ⨿ Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.symmetry'`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproducts C] 
  (P Q : C),   CategoryTheor…

--- 原说明 ---
The braiding isomorphism is symmetric.
-/
theorem coprod.symmetry (P Q : C) : (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
  coprod.symmetry' _ _

set_option backward.isDefEq.respectTransparency false in
/-- The associator isomorphism for binary coproducts. -/
@[simps]
/-
**CategoryTheory.Limits.coprod.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasBinaryCoproducts C] → (P Q R : C) → (P ⨿ Q) ⨿ R ≅ P ⨿ 
Q ⨿ R
参数：P Q R : C；P ⨿ Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism for binary coproducts.
-/
def coprod.associator (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ Q ⨿ R where
  hom := coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr)
  inv := coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.coprod.pentagon** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasBinaryCoproducts C]   (W X Y Z : C),   CategoryTheory.Category
Struct.comp       (CategoryTheory.Limits.coprod.map (CategoryTheory.Limits.copro
d.associator W X Y).hom         (CategoryTheory.CategoryStruct.id Z))       (Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.associator W (X ⨿ 
Y) Z).hom         (CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStru
ct.id W)           (CategoryTheory.Limits.coprod.associator X Y Z).hom)) =     C
ategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coprod.associator (W ⨿ 
X) Y Z).hom       (CategoryTheory.Limits.coprod.associator W X (Y ⨿ Z)).hom
参数：W X Y Z : C；CategoryTheory.Limits.coprod.map (CategoryTheory.Limits.coprod.as
sociator W X Y).hom         (CategoryTheory.CategoryStruct.id Z)；CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.coprod.associator W (X ⨿ Y) Z).hom   
      (CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStruct.id W)    
       (CategoryTheory.Limits.coprod.associator X Y Z).hom)；CategoryTheory.Limit
s.coprod.associator (W ⨿ X) Y Z；CategoryTheory.Limits.coprod.associator W X (Y ⨿
 Z)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.associator_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct
s C]   (P Q R : C),   (CategoryTh…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.pentagon (W X Y Z : C) :
    coprod.map (coprod.associator W X Y).hom (𝟙 Z) ≫
        (coprod.associator W (X ⨿ Y) Z).hom ≫ coprod.map (𝟙 W) (coprod.associator X Y Z).hom =
      (coprod.associator (W ⨿ X) Y Z).hom ≫ (coprod.associator W X (Y ⨿ Z)).hom := by
  simp
/-
**CategoryTheory.Limits.coprod.associator_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasBinaryCoproducts C]   {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (
f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),   CategoryTheory.CategoryStruct.comp (CategoryTheo
ry.Limits.coprod.map (CategoryTheory.Limits.coprod.map f₁ f₂) f₃)       (Categor
yTheory.Limits.coprod.associator Y₁ Y₂ Y₃).hom =     CategoryTheory.CategoryStru
ct.comp (CategoryTheory.Limits.coprod.associator X₁ X₂ X₃).hom       (CategoryTh
eory.Limits.coprod.map f₁ (CategoryTheory.Limits.coprod.map f₂ f₃))
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃；CategoryTheory.Limits.coprod.map (Cate
goryTheory.Limits.coprod.map f₁ f₂) f₃；CategoryTheory.Limits.coprod.associator Y
₁ Y₂ Y₃；CategoryTheory.Limits.coprod.associator X₁ X₂ X₃；CategoryTheory.Limits.c
oprod.map f₁ (CategoryTheory.Limits.coprod.map f₂ f₃)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.associator_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct
s C]   (P Q R : C),   (CategoryTh…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.coprod.inl_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.coprod.inr_map_assoc`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.Has
BinaryCoproduct W X] [inst_2 : C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
      (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) := by
  simp

variable [HasInitial C]

set_option backward.isDefEq.respectTransparency false in
/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
/-
**CategoryTheory.Limits.coprod.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasBinaryCoproducts C] →       [inst_2 : CategoryTheory.L
imits.HasInitial C] → (P : C) → (⊥_ C) ⨿ P ≅ P
参数：P : C；⊥_ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left unitor isomorphism for binary coproducts with the initial object.
-/
def coprod.leftUnitor (P : C) : (⊥_ C) ⨿ P ≅ P where
  hom := coprod.desc (initial.to P) (𝟙 _)
  inv := coprod.inr
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp
/-
**CategoryTheory.Limits.coprod.leftUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryCoproducts C] [inst_2 : CategoryTheory.Limit
s.HasInitial C] (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Limits.coprod.map (CategoryTheory.CategoryStruct.id (⊥_ C)) f)       (Category
Theory.Limits.coprod.leftUnitor Y).hom =     CategoryTheory.CategoryStruct.comp 
(CategoryTheory.Limits.coprod.leftUnitor X).hom f
参数：f : X ⟶ Y；CategoryTheory.Limits.coprod.map (CategoryTheory.CategoryStruct.id 
(⊥_ C)) f；CategoryTheory.Limits.coprod.leftUnitor Y；CategoryTheory.Limits.coprod
.leftUnitor X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.leftUnitor_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct
s C]   [inst_2 : CategoryTheory.L…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.leftUnitor_naturality (f : X ⟶ Y) :
    coprod.map (𝟙 _) f ≫ (coprod.leftUnitor Y).hom = (coprod.leftUnitor X).hom ≫ f := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps]
/-
**CategoryTheory.Limits.coprod.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasBinaryCoproducts C] →       [inst_2 : CategoryTheory.L
imits.HasInitial C] → (P : C) → P ⨿ ⊥_ C ≅ P
参数：P : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right unitor isomorphism for binary coproducts with the initial object.
-/
def coprod.rightUnitor (P : C) : P ⨿ ⊥_ C ≅ P where
  hom := coprod.desc (𝟙 _) (initial.to P)
  inv := coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp [eq_iff_true_of_subsingleton]
  inv_hom_id := by simp
/-
**CategoryTheory.Limits.coprod.rightUnitor_naturality** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C}   [inst
_1 : CategoryTheory.Limits.HasBinaryCoproducts C] [inst_2 : CategoryTheory.Limit
s.HasInitial C] (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Limits.coprod.map f (CategoryTheory.CategoryStruct.id (⊥_ C)))       (Category
Theory.Limits.coprod.rightUnitor Y).hom =     CategoryTheory.CategoryStruct.comp
 (CategoryTheory.Limits.coprod.rightUnitor X).hom f
参数：f : X ⟶ Y；CategoryTheory.Limits.coprod.map f (CategoryTheory.CategoryStruct.i
d (⊥_ C))；CategoryTheory.Limits.coprod.rightUnitor Y；CategoryTheory.Limits.copro
d.rightUnitor X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.rightUnitor_hom`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproduc
ts C]   [inst_2 : CategoryTheory.L…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod.rightUnitor_naturality (f : X ⟶ Y) :
    coprod.map f (𝟙 _) ≫ (coprod.rightUnitor Y).hom = (coprod.rightUnitor X).hom ≫ f := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.coprod.triangle** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasBinaryCoproducts C]   [inst_2 : CategoryTheory.Limits.HasIniti
al C] (X Y : C),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.cop
rod.associator X (⊥_ C) Y).hom       (CategoryTheory.Limits.coprod.map (Category
Theory.CategoryStruct.id X)         (CategoryTheory.Limits.coprod.leftUnitor Y).
hom) =     CategoryTheory.Limits.coprod.map (CategoryTheory.Limits.coprod.rightU
nitor X).hom       (CategoryTheory.CategoryStruct.id Y)
参数：X Y : C；CategoryTheory.Limits.coprod.associator X (⊥_ C) Y；CategoryTheory.Lim
its.coprod.map (CategoryTheory.CategoryStruct.id X)         (CategoryTheory.Limi
ts.coprod.leftUnitor Y).hom；CategoryTheory.Limits.coprod.rightUnitor X；CategoryT
heory.CategoryStruct.id Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.associator_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct
s C]   (P Q R : C),   (CategoryTh…
· 使用定理 `CategoryTheory.Limits.coprod.leftUnitor_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproduct
s C]   [inst_2 : CategoryTheory.L…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.initial.to_comp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P Q : 
C}   (f : P ⟶ Q),   Categor…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.coprod.rightUnitor_hom`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasBinaryCoproduc
ts C]   [inst_2 : CategoryTheory.L…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.initial.hom_ext`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P : C}
   (f g : ⊥_ C ⟶ P), f = g
-/
theorem coprod.triangle (X Y : C) :
    (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) (coprod.leftUnitor Y).hom =
      coprod.map (coprod.rightUnitor X).hom (𝟙 Y) := by
  ext <;> simp

end

noncomputable section ProdFunctor

variable {C} [HasBinaryProducts C]

/-- The binary product functor. -/
@[simps]
/-
**CategoryTheory.Limits.prod.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasBinaryProducts C] → CategoryTheory.Functor C (CategoryTheory.Fu
nctor C C)
参数：CategoryTheory.Functor C C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary product functor.
-/
def prod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨯ Y
      map := fun {_ _} => prod.map (𝟙 X) }
  map f :=
    { app := fun T => prod.map f (𝟙 T) }

set_option backward.defeqAttrib.useBackward true in
/-- The product functor can be decomposed. -/
/-
**CategoryTheory.Limits.prod.functorLeftComp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasBinaryProducts C] →       (X Y : C) →         Category
Theory.Limits.prod.functor.obj (X ⨯ Y) ≅           (CategoryTheory.Limits.prod.f
unctor.obj Y).comp (CategoryTheory.Limits.prod.functor.obj X)
参数：X Y : C；X ⨯ Y；CategoryTheory.Limits.prod.functor.obj Y；CategoryTheory.Limits.
prod.functor.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product functor can be decomposed.
-/
def prod.functorLeftComp (X Y : C) :
    prod.functor.obj (X ⨯ Y) ≅ prod.functor.obj Y ⋙ prod.functor.obj X :=
  NatIso.ofComponents (prod.associator _ _)

end ProdFunctor

noncomputable section CoprodFunctor

variable {C} [HasBinaryCoproducts C]

/-- The binary coproduct functor. -/
@[simps]
/-
**CategoryTheory.Limits.coprod.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasBinaryCoproducts C] → CategoryTheory.Functor C (CategoryTheory.
Functor C C)
参数：CategoryTheory.Functor C C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary coproduct functor.
-/
def coprod.functor : C ⥤ C ⥤ C where
  obj X :=
    { obj := fun Y => X ⨿ Y
      map := fun {_ _} => coprod.map (𝟙 X) }
  map f := { app := fun T => coprod.map f (𝟙 T) }

set_option backward.defeqAttrib.useBackward true in
/-- The coproduct functor can be decomposed. -/
/-
**CategoryTheory.Limits.coprod.functorLeftComp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasBinaryCoproducts C] →       (X Y : C) →         Catego
ryTheory.Limits.coprod.functor.obj (X ⨿ Y) ≅           (CategoryTheory.Limits.co
prod.functor.obj Y).comp (CategoryTheory.Limits.coprod.functor.obj X)
参数：X Y : C；X ⨿ Y；CategoryTheory.Limits.coprod.functor.obj Y；CategoryTheory.Limit
s.coprod.functor.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct functor can be decomposed.
-/
def coprod.functorLeftComp (X Y : C) :
    coprod.functor.obj (X ⨿ Y) ≅ coprod.functor.obj Y ⋙ coprod.functor.obj X :=
  NatIso.ofComponents (coprod.associator _ _)

end CoprodFunctor

section

variable {C} {D : Type*} [Category* D] {F : C ⥤ D}

variable (F) in
/-- The image of a binary fan by a functor. -/
/-
**CategoryTheory.Limits.BinaryFan.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         (F : Cat
egoryTheory.Functor C D) →           {X Y : C} → CategoryTheory.Limits.BinaryFan
 X Y → CategoryTheory.Limits.BinaryFan (F.obj X) (F.obj Y)
参数：F : CategoryTheory.Functor C D；F.obj X；F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a binary fan by a functor.
-/
abbrev BinaryFan.map {X Y : C} (s : BinaryFan X Y) : BinaryFan (F.obj X) (F.obj Y) :=
  mk (F.map s.fst) (F.map s.snd)

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.map_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   {F : CategoryTheory.Functor C D}
 {X Y : C} (s : CategoryTheory.Limits.BinaryFan X Y),   (CategoryTheory.Limits.B
inaryFan.map F s).fst = F.map s.fst
参数：s : CategoryTheory.Limits.BinaryFan X Y；CategoryTheory.Limits.BinaryFan.map F
 s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryFan.map_fst {X Y : C} (s : BinaryFan X Y) : (s.map F).fst = F.map s.fst := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.map_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   {F : CategoryTheory.Functor C D}
 {X Y : C} (s : CategoryTheory.Limits.BinaryFan X Y),   (CategoryTheory.Limits.B
inaryFan.map F s).snd = F.map s.snd
参数：s : CategoryTheory.Limits.BinaryFan X Y；CategoryTheory.Limits.BinaryFan.map F
 s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryFan.map_snd {X Y : C} (s : BinaryFan X Y) : (s.map F).snd = F.map s.snd := rfl

variable (F) in
/-- The image of a binary cofan by a functor. -/
/-
**CategoryTheory.Limits.BinaryCofan.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         (F : Cat
egoryTheory.Functor C D) →           {X Y : C} → CategoryTheory.Limits.BinaryCof
an X Y → CategoryTheory.Limits.BinaryCofan (F.obj X) (F.obj Y)
参数：F : CategoryTheory.Functor C D；F.obj X；F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a binary cofan by a functor.
-/
abbrev BinaryCofan.map {X Y : C} (s : BinaryCofan X Y) : BinaryCofan (F.obj X) (F.obj Y) :=
  mk (F.map s.inl) (F.map s.inr)

@[simp]
/-
**CategoryTheory.Limits.BinaryCofan.map_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   {F : CategoryTheory.Functor C D}
 {X Y : C} (s : CategoryTheory.Limits.BinaryCofan X Y),   (CategoryTheory.Limits
.BinaryCofan.map F s).inl = F.map s.inl
参数：s : CategoryTheory.Limits.BinaryCofan X Y；CategoryTheory.Limits.BinaryCofan.m
ap F s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryCofan.map_inl {X Y : C} (s : BinaryCofan X Y) : (s.map F).inl = F.map s.inl := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryCofan.map_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} D]   {F : CategoryTheory.Functor C D}
 {X Y : C} (s : CategoryTheory.Limits.BinaryCofan X Y),   (CategoryTheory.Limits
.BinaryCofan.map F s).inr = F.map s.inr
参数：s : CategoryTheory.Limits.BinaryCofan X Y；CategoryTheory.Limits.BinaryCofan.m
ap F s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryCofan.map_inr {X Y : C} (s : BinaryCofan X Y) : (s.map F).inr = F.map s.inr := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `F.mapCone s` being limiting is the same as the induced binary fan being limiting. -/
/-
**CategoryTheory.Limits.BinaryFan.isLimitMapConeEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         {F : Cat
egoryTheory.Functor C D} →           {X Y : C} →             {s : CategoryTheory
.Limits.BinaryFan X Y} →               CategoryTheory.Limits.IsLimit (F.mapCone 
s) ≃                 CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Binary
Fan.map F s)
参数：F.mapCone s；CategoryTheory.Limits.BinaryFan.map F s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.mapCone s` being limiting is the same as the induced binary fan being limitin
g.
-/
def BinaryFan.isLimitMapConeEquiv {X Y : C} {s : BinaryFan X Y} :
    IsLimit (F.mapCone s) ≃ IsLimit (s.map F) :=
  IsLimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ <| ext (Iso.refl _)
    (by simp [fst]) (by simp [snd])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `F.mapCocone s` being colimiting is the same as the induced binary cofan being colimiting. -/
/-
**CategoryTheory.Limits.BinaryCofan.isColimitMapConeEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u_1} →       [inst_1 : CategoryTheory.Category.{v_1, u_1} D] →         {F : Cat
egoryTheory.Functor C D} →           {X Y : C} →             {s : CategoryTheory
.Limits.BinaryCofan X Y} →               CategoryTheory.Limits.IsColimit (F.mapC
ocone s) ≃                 CategoryTheory.Limits.IsColimit (CategoryTheory.Limit
s.BinaryCofan.map F s)
参数：F.mapCocone s；CategoryTheory.Limits.BinaryCofan.map F s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.mapCocone s` being colimiting is the same as the induced binary cofan being c
olimiting.
-/
def BinaryCofan.isColimitMapConeEquiv {X Y : C} {s : BinaryCofan X Y} :
    IsColimit (F.mapCocone s) ≃ IsColimit (s.map F) :=
  IsColimit.equivOfNatIsoOfIso (diagramIsoPair _) _ _ <| ext (Iso.refl _)
    (by simp [inl]) (by simp [inr])

end

noncomputable section ProdComparison

universe w w' u₃

variable {C} {D : Type u₂} [Category.{w} D] {E : Type u₃} [Category.{w'} E]
variable (F : C ⥤ D) (G : D ⥤ E) {A A' B B' : C}
variable [HasBinaryProduct A B] [HasBinaryProduct A' B']
variable [HasBinaryProduct (F.obj A) (F.obj B)]
variable [HasBinaryProduct (F.obj A') (F.obj B')]
variable [HasBinaryProduct (G.obj (F.obj A)) (G.obj (F.obj B))]
variable [HasBinaryProduct ((F ⋙ G).obj A) ((F ⋙ G).obj B)]

/-- The product comparison morphism.

In `CategoryTheory/Limits/Preserves` we show this is always an iso iff F preserves binary products.
-/
/-
**CategoryTheory.Limits.prodComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B] [HasBinaryProd
uct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B
参数：F : C ⥤ D；A B : C；F.obj A；F.obj B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product comparison morphism.

In `CategoryTheory/Limits/Preserves` we show this is always an iso iff F preserv
es binary products.
-/
def prodComparison (F : C ⥤ D) (A B : C) [HasBinaryProduct A B]
    [HasBinaryProduct (F.obj A) (F.obj B)] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
  prod.lift (F.map prod.fst) (F.map prod.snd)

variable (A B)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prodComparison_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
-/
theorem prodComparison_fst : prodComparison F A B ≫ prod.fst = F.map prod.fst :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prodComparison_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
-/
theorem prodComparison_snd : prodComparison F A B ≫ prod.snd = F.map prod.snd :=
  prod.lift_snd _ _

variable {A B}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
/-
**CategoryTheory.Limits.prodComparison_natural** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') : F.map (prod.map f g) ≫ 
prodComparison F A' B' = prodComparison F A B ≫ prod.map (F.map f) (F.map g)
参数：f : A ⟶ A'；g : B ⟶ B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prodComparison.eq_1`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{w, 
u₂} D]   (F : CategoryTheory.Fu…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…

--- 原说明 ---
Naturality of the `prodComparison` morphism in both arguments.
-/
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (prod.map f g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ prod.map (F.map f) (F.map g) := by
  rw [prodComparison, prodComparison, prod.lift_map, ← F.map_comp, ← F.map_comp, prod.comp_lift, ←
    F.map_comp, prod.map_fst, ← F.map_comp, prod.map_snd]

variable {F}

/-- Naturality of the `prodComparison` morphism in a natural transformation. -/
@[reassoc]
/-
**CategoryTheory.Limits.prodComparison_natural_of_natTrans** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：prodComparison_natural_of_natTrans {H : C ⥤ D} [HasBinaryProduct (H.obj A)
 (H.obj B)] (α : F ⟶ H) : α.app (prod A B) ≫ prodComparison H A B = prodComparis
on F A B ≫ prod.map (α.app A) (α.app B)
参数：H.obj A；H.obj B；α : F ⟶ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prodComparison.eq_1`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{w, 
u₂} D]   (F : CategoryTheory.Fu…
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
Naturality of the `prodComparison` morphism in a natural transformation.
-/
theorem prodComparison_natural_of_natTrans {H : C ⥤ D} [HasBinaryProduct (H.obj A) (H.obj B)]
    (α : F ⟶ H) :
    α.app (prod A B) ≫ prodComparison H A B =
      prodComparison F A B ≫ prod.map (α.app A) (α.app B) := by
  rw [prodComparison, prodComparison, prod.lift_map, prod.comp_lift, α.naturality, α.naturality]

variable (F)

set_option backward.defeqAttrib.useBackward true in
/-- The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prodComparison`.
-/
@[simps]
/-
**CategoryTheory.Limits.prodComparisonNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C 
⥤ D) (A : C) : prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where app
 B
参数：F : C ⥤ D；A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components a
re given by
`prodComparison`.
-/
def prodComparisonNatTrans [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (A : C) :
    prod.functor.obj A ⋙ F ⟶ F ⋙ prod.functor.obj (F.obj A) where
  app B := prodComparison F A B
  naturality f := by simp [prodComparison_natural]

@[reassoc]
/-
**CategoryTheory.Limits.inv_prodComparison_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inv_prodComparison_map_fst [IsIso (prodComparison F A B)] : inv (prodCompa
rison F A B) ≫ F.map prod.fst = prod.fst
参数：prodComparison F A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prodComparison_fst`：prodComparison_fst : prodCompa
rison F A B ≫ prod.fst = F.map prod.fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.fst = prod.fst := by simp [IsIso.inv_comp_eq]

@[reassoc]
/-
**CategoryTheory.Limits.inv_prodComparison_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inv_prodComparison_map_snd [IsIso (prodComparison F A B)] : inv (prodCompa
rison F A B) ≫ F.map prod.snd = prod.snd
参数：prodComparison F A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.prodComparison_snd`：prodComparison_snd : prodCompa
rison F A B ≫ prod.snd = F.map prod.snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map prod.snd = prod.snd := by simp [IsIso.inv_comp_eq]

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
/-
**CategoryTheory.Limits.prodComparison_inv_natural** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodCompariso
n F A B)] [IsIso (prodComparison F A' B')] : inv (prodComparison F A B) ≫ F.map 
(prod.map f g) = prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B')
参数：f : A ⟶ A'；g : B ⟶ B'；prodComparison F A B；prodComparison F A' B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `CategoryTheory.Limits.prodComparison_natural`：prodComparison_natural (f 
: A ⟶ A') (g : B ⟶ B') : F.map (prod.map f g) ≫ prodComparison F A' B' = prodCom
parison F A B ≫ prod.map (F.map f)…

--- 原说明 ---
If the product comparison morphism is an iso, its inverse is natural.
-/
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A B)]
    [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (prod.map f g) =
      prod.map (F.map f) (F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
/-
**CategoryTheory.Limits.prodComparisonNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C) [
forall B, IsIso (prodComparison F A B)] : prod.functor.obj A ⋙ F ≅ F ⋙ prod.func
tor.obj (F.obj A)
参数：A : C；prodComparison F A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prodComparison F A 
B` is an
isomorphism (as `B` changes).
-/
def prodComparisonNatIso [HasBinaryProducts C] [HasBinaryProducts D] (A : C)
    [∀ B, IsIso (prodComparison F A B)] :
    prod.functor.obj A ⋙ F ≅ F ⋙ prod.functor.obj (F.obj A) := by
  refine { @asIso _ _ _ _ _ (?_) with hom := prodComparisonNatTrans F A }
  apply NatIso.isIso_of_isIso_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.prodComparison_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：prodComparison_comp : prodComparison (F ⋙ G) A B = G.map (prodComparison F
 A B) ≫ prodComparison G (F.obj A) (F.obj B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

end ProdComparison

noncomputable section CoprodComparison

universe w

variable {C} {D : Type u₂} [Category.{w} D]
variable (F : C ⥤ D) {A A' B B' : C}
variable [HasBinaryCoproduct A B] [HasBinaryCoproduct A' B']
variable [HasBinaryCoproduct (F.obj A) (F.obj B)] [HasBinaryCoproduct (F.obj A') (F.obj B')]

/-- The coproduct comparison morphism.

In `Mathlib/CategoryTheory/Limits/Preserves/` we show
this is always an iso iff F preserves binary coproducts.
-/
/-
**CategoryTheory.Limits.coprodComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B] [HasBinary
Coproduct (F.obj A) (F.obj B)] : F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B)
参数：F : C ⥤ D；A B : C；F.obj A；F.obj B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct comparison morphism.

In `Mathlib/CategoryTheory/Limits/Preserves/` we show
this is always an iso iff F preserves binary coproducts.
-/
def coprodComparison (F : C ⥤ D) (A B : C) [HasBinaryCoproduct A B]
    [HasBinaryCoproduct (F.obj A) (F.obj B)] : F.obj A ⨿ F.obj B ⟶ F.obj (A ⨿ B) :=
  coprod.desc (F.map coprod.inl) (F.map coprod.inr)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprodComparison_inl** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：coprodComparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.
inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
theorem coprodComparison_inl : coprod.inl ≫ coprodComparison F A B = F.map coprod.inl :=
  coprod.inl_desc _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprodComparison_inr** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：coprodComparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.
inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
theorem coprodComparison_inr : coprod.inr ≫ coprodComparison F A B = F.map coprod.inr :=
  coprod.inr_desc _ _

/-- Naturality of the `coprodComparison` morphism in both arguments. -/
@[reassoc]
/-
**CategoryTheory.Limits.coprodComparison_natural** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') : coprodComparison F A 
B ≫ F.map (coprod.map f g) = coprod.map (F.map f) (F.map g) ≫ coprodComparison F
 A' B'
参数：f : A ⟶ A'；g : B ⟶ B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprodComparison.eq_1`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{w
, u₂} D]   (F : CategoryTheory.Fu…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.Limits.coprod.inl_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Limits.coprod.inr_map`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Coproduct W X] [inst_2 : C…

--- 原说明 ---
Naturality of the `coprodComparison` morphism in both arguments.
-/
theorem coprodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    coprodComparison F A B ≫ F.map (coprod.map f g) =
      coprod.map (F.map f) (F.map g) ≫ coprodComparison F A' B' := by
  rw [coprodComparison, coprodComparison, coprod.map_desc, ← F.map_comp, ← F.map_comp,
    coprod.desc_comp, ← F.map_comp, coprod.inl_map, ← F.map_comp, coprod.inr_map]

set_option backward.defeqAttrib.useBackward true in
/-- The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components are given by
`coprodComparison`.
-/
@[simps]
/-
**CategoryTheory.Limits.coprodComparisonNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (
F : C ⥤ D) (A : C) : F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F
 where app B
参数：F : C ⥤ D；A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct comparison morphism from `FA ⨿ F-` to `F(A ⨿ -)`, whose components
 are given by
`coprodComparison`.
-/
def coprodComparisonNatTrans [HasBinaryCoproducts C] [HasBinaryCoproducts D] (F : C ⥤ D) (A : C) :
    F ⋙ coprod.functor.obj (F.obj A) ⟶ coprod.functor.obj A ⋙ F where
  app B := coprodComparison F A B
  naturality f := by simp [coprodComparison_natural]

@[reassoc]
/-
**CategoryTheory.Limits.map_inl_inv_coprodComparison** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] : F.map copr
od.inl ≫ inv (coprodComparison F A B) = coprod.inl
参数：coprodComparison F A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprodComparison_inl`：coprodComparison_inl : copro
d.inl ≫ coprodComparison F A B = F.map coprod.inl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inl_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inl ≫ inv (coprodComparison F A B) = coprod.inl := by simp

@[reassoc]
/-
**CategoryTheory.Limits.map_inr_inv_coprodComparison** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] : F.map copr
od.inr ≫ inv (coprodComparison F A B) = coprod.inr
参数：coprodComparison F A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprodComparison_inr`：coprodComparison_inr : copro
d.inr ≫ coprodComparison F A B = F.map coprod.inr
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inr_inv_coprodComparison [IsIso (coprodComparison F A B)] :
    F.map coprod.inr ≫ inv (coprodComparison F A B) = coprod.inr := by simp

/-- If the coproduct comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
/-
**CategoryTheory.Limits.coprodComparison_inv_natural** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodCompa
rison F A B)] [IsIso (coprodComparison F A' B')] : inv (coprodComparison F A B) 
≫ coprod.map (F.map f) (F.map g) = F.map (coprod.map f g) ≫ inv (coprodCompariso
n F A' B')
参数：f : A ⟶ A'；g : B ⟶ B'；coprodComparison F A B；coprodComparison F A' B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `CategoryTheory.Limits.coprodComparison_natural`：coprodComparison_natural
 (f : A ⟶ A') (g : B ⟶ B') : coprodComparison F A B ≫ F.map (coprod.map f g) = c
oprod.map (F.map f) (F.map g) ≫ copr…

--- 原说明 ---
If the coproduct comparison morphism is an iso, its inverse is natural.
-/
theorem coprodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (coprodComparison F A B)]
    [IsIso (coprodComparison F A' B')] :
    inv (coprodComparison F A B) ≫ coprod.map (F.map f) (F.map g) =
      F.map (coprod.map f g) ≫ inv (coprodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, coprodComparison_natural]

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprodComparison F A B` is an
isomorphism (as `B` changes).
-/
@[simps]
/-
**CategoryTheory.Limits.coprodComparisonNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A 
: C) [forall B, IsIso (coprodComparison F A B)] : F ⋙ coprod.functor.obj (F.obj 
A) ≅ coprod.functor.obj A ⋙ F
参数：A : C；coprodComparison F A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `FA ⨿ F- ≅ F(A ⨿ -)`, provided each `coprodComparison F 
A B` is an
isomorphism (as `B` changes).
-/
def coprodComparisonNatIso [HasBinaryCoproducts C] [HasBinaryCoproducts D] (A : C)
    [∀ B, IsIso (coprodComparison F A B)] :
    F ⋙ coprod.functor.obj (F.obj A) ≅ coprod.functor.obj A ⋙ F :=
  { @asIso _ _ _ _ _ (NatIso.isIso_of_isIso_app ..) with hom := coprodComparisonNatTrans F A }

end CoprodComparison

end CategoryTheory.Limits

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `Over.coprod`. -/
@[simps]
/-
**CategoryTheory.Over.coprodObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasBinaryCoproducts C] →       {A : C} → CategoryTheory.Over A → C
ategoryTheory.Functor (CategoryTheory.Over A) (CategoryTheory.Over A)
参数：CategoryTheory.Over A；CategoryTheory.Over A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Over.coprod`.
-/
noncomputable def Over.coprodObj [HasBinaryCoproducts C] {A : C} :
    Over A → Over A ⥤ Over A :=
  fun f =>
  { obj := fun g => Over.mk (coprod.desc f.hom g.hom)
    map := fun k => Over.homMk (coprod.map (𝟙 _) k.left) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A category with binary coproducts has a functorial `sup` operation on over categories. -/
@[simps]
/-
**CategoryTheory.Over.coprod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasBinaryCoproducts C] →       {A : C} →         CategoryTheory.Fu
nctor (CategoryTheory.Over A)           (CategoryTheory.Functor (CategoryTheory.
Over A) (CategoryTheory.Over A))
参数：CategoryTheory.Over A；CategoryTheory.Functor (CategoryTheory.Over A) (Categor
yTheory.Over A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with binary coproducts has a functorial `sup` operation on over categ
ories.
-/
noncomputable def Over.coprod [HasBinaryCoproducts C] {A : C} : Over A ⥤ Over A ⥤ Over A where
  obj f := Over.coprodObj f
  map k :=
    { app := fun g => Over.homMk (coprod.map k.left (𝟙 _)) (by
        dsimp; rw [coprod.map_desc, Category.id_comp, Over.w k])
      naturality := fun f g k => by
        ext
        simp }
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

end CategoryTheory

namespace CategoryTheory.Limits
open Opposite

variable {C : Type u} [Category.{v} C] {X Y Z P : C}

section opposite

/-- A binary fan gives a binary cofan in the opposite category. -/
/-
**CategoryTheory.Limits.BinaryFan.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → CategoryTheory.Limits.BinaryFan X Y → CategoryTheory.Limits.BinaryCofan (Oppo
site.op X) (Opposite.op Y)
参数：Opposite.op X；Opposite.op Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary fan gives a binary cofan in the opposite category.
-/
protected abbrev BinaryFan.op (c : BinaryFan X Y) : BinaryCofan (op X) (op Y) :=
  .mk c.fst.op c.snd.op

/-- A binary cofan gives a binary fan in the opposite category. -/
/-
**CategoryTheory.Limits.BinaryCofan.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → CategoryTheory.Limits.BinaryCofan X Y → CategoryTheory.Limits.BinaryFan (Oppo
site.op X) (Opposite.op Y)
参数：Opposite.op X；Opposite.op Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary cofan gives a binary fan in the opposite category.
-/
protected abbrev BinaryCofan.op (c : BinaryCofan X Y) : BinaryFan (op X) (op Y) :=
  .mk c.inl.op c.inr.op

/-- A binary fan in the opposite category gives a binary cofan. -/
/-
**CategoryTheory.Limits.BinaryFan.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → CategoryTheory.Limits.BinaryFan (Opposite.op X) (Opposite.op Y) → CategoryThe
ory.Limits.BinaryCofan X Y
参数：Opposite.op X；Opposite.op Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary fan in the opposite category gives a binary cofan.
-/
protected abbrev BinaryFan.unop (c : BinaryFan (op X) (op Y)) : BinaryCofan X Y :=
  .mk c.fst.unop c.snd.unop

/-- A binary cofan in the opposite category gives a binary fan. -/
/-
**CategoryTheory.Limits.BinaryCofan.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.BinaryCofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → CategoryTheory.Limits.BinaryCofan (Opposite.op X) (Opposite.op Y) → CategoryT
heory.Limits.BinaryFan X Y
参数：Opposite.op X；Opposite.op Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary cofan in the opposite category gives a binary fan.
-/
protected abbrev BinaryCofan.unop (c : BinaryCofan (op X) (op Y)) : BinaryFan X Y :=
  .mk c.inl.unop c.inr.unop
/-
**CategoryTheory.Limits.BinaryFan.op_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (π₁ :
 P ⟶ X) (π₂ : P ⟶ Y),   (CategoryTheory.Limits.BinaryFan.mk π₁ π₂).op = Category
Theory.Limits.BinaryCofan.mk π₁.op π₂.op
参数：π₁ : P ⟶ X；π₂ : P ⟶ Y；CategoryTheory.Limits.BinaryFan.mk π₁ π₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma BinaryFan.op_mk (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
    BinaryFan.op (mk π₁ π₂) = .mk π₁.op π₂.op := rfl
/-
**CategoryTheory.Limits.BinaryFan.unop_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (π₁ :
 Opposite.op P ⟶ Opposite.op X)   (π₂ : Opposite.op P ⟶ Opposite.op Y),   (Categ
oryTheory.Limits.BinaryFan.mk π₁ π₂).unop = CategoryTheory.Limits.BinaryCofan.mk
 π₁.unop π₂.unop
参数：π₁ : Opposite.op P ⟶ Opposite.op X；π₂ : Opposite.op P ⟶ Opposite.op Y；Categor
yTheory.Limits.BinaryFan.mk π₁ π₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma BinaryFan.unop_mk (π₁ : op P ⟶ op X) (π₂ : op P ⟶ op Y) :
    BinaryFan.unop (mk π₁ π₂) = .mk π₁.unop π₂.unop := rfl
/-
**CategoryTheory.Limits.BinaryCofan.op_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (ι₁ :
 X ⟶ P) (ι₂ : Y ⟶ P),   (CategoryTheory.Limits.BinaryCofan.mk ι₁ ι₂).op = Catego
ryTheory.Limits.BinaryFan.mk ι₁.op ι₂.op
参数：ι₁ : X ⟶ P；ι₂ : Y ⟶ P；CategoryTheory.Limits.BinaryCofan.mk ι₁ ι₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma BinaryCofan.op_mk (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
    BinaryCofan.op (mk ι₁ ι₂) = .mk ι₁.op ι₂.op := rfl
/-
**CategoryTheory.Limits.BinaryCofan.unop_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.BinaryCofan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y P : C} (ι₁ :
 Opposite.op X ⟶ Opposite.op P)   (ι₂ : Opposite.op Y ⟶ Opposite.op P),   (Categ
oryTheory.Limits.BinaryCofan.mk ι₁ ι₂).unop = CategoryTheory.Limits.BinaryFan.mk
 ι₁.unop ι₂.unop
参数：ι₁ : Opposite.op X ⟶ Opposite.op P；ι₂ : Opposite.op Y ⟶ Opposite.op P；Categor
yTheory.Limits.BinaryCofan.mk ι₁ ι₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma BinaryCofan.unop_mk (ι₁ : op X ⟶ op P) (ι₂ : op Y ⟶ op P) :
    BinaryCofan.unop (mk ι₁ ι₂) = .mk ι₁.unop ι₂.unop := rfl

set_option backward.isDefEq.respectTransparency false in
/-- If a `BinaryFan` is a limit, then its opposite is a colimit. -/
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.op** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.BinaryFan.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {c : CategoryTheory.Limits.BinaryFan X Y} → CategoryTheory.Limits.IsLim
it c → CategoryTheory.Limits.IsColimit c.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `BinaryFan` is a limit, then its opposite is a colimit.
-/
protected def BinaryFan.IsLimit.op {c : BinaryFan X Y} (hc : IsLimit c) : IsColimit c.op :=
  BinaryCofan.isColimitMk (fun s ↦ (hc.lift s.unop).op)
    (fun _ ↦ Quiver.Hom.unop_inj (by simp)) (fun _ ↦ Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.unop_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

set_option backward.isDefEq.respectTransparency false in
/-- If a `BinaryCofan` is a colimit, then its opposite is a limit. -/
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.op** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {c : CategoryTheory.Limits.BinaryCofan X Y} →         CategoryTheory.Li
mits.IsColimit c → CategoryTheory.Limits.IsLimit c.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `BinaryCofan` is a colimit, then its opposite is a limit.
-/
protected def BinaryCofan.IsColimit.op {c : BinaryCofan X Y} (hc : IsColimit c) : IsLimit c.op :=
  BinaryFan.isLimitMk (fun s ↦ (hc.desc s.unop).op)
    (fun _ ↦ Quiver.Hom.unop_inj (by simp)) (fun _ ↦ Quiver.Hom.unop_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.unop_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

set_option backward.isDefEq.respectTransparency false in
/-- If a `BinaryFan` in the opposite category is a limit, then its `unop` is a colimit. -/
/-
**CategoryTheory.Limits.BinaryFan.IsLimit.unop** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.BinaryFan.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {c : CategoryTheory.Limits.BinaryFan (Opposite.op X) (Opposite.op Y)} →
         CategoryTheory.Limits.IsLimit c → CategoryTheory.Limits.IsColimit c.uno
p
参数：Opposite.op X；Opposite.op Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `BinaryFan` in the opposite category is a limit, then its `unop` is a colim
it.
-/
protected def BinaryFan.IsLimit.unop {c : BinaryFan (op X) (op Y)} (hc : IsLimit c) :
    IsColimit c.unop :=
  BinaryCofan.isColimitMk (fun s ↦ (hc.lift s.op).unop)
    (fun _ ↦ Quiver.Hom.op_inj (by simp)) (fun _ ↦ Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.op_inj
      (BinaryFan.IsLimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

set_option backward.isDefEq.respectTransparency false in
/-- If a `BinaryCofan` in the opposite category is a colimit, then its `unop` is a limit. -/
/-
**CategoryTheory.Limits.BinaryCofan.IsColimit.unop** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.BinaryCofan.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {c : CategoryTheory.Limits.BinaryCofan (Opposite.op X) (Opposite.op Y)}
 →         CategoryTheory.Limits.IsColimit c → CategoryTheory.Limits.IsLimit c.u
nop
参数：Opposite.op X；Opposite.op Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `BinaryCofan` in the opposite category is a colimit, then its `unop` is a l
imit.
-/
protected def BinaryCofan.IsColimit.unop {c : BinaryCofan (op X) (op Y)} (hc : IsColimit c) :
    IsLimit c.unop :=
  BinaryFan.isLimitMk (fun s ↦ (hc.desc s.op).unop)
    (fun _ ↦ Quiver.Hom.op_inj (by simp)) (fun _ ↦ Quiver.Hom.op_inj (by simp))
    (fun s m h₁ h₂ ↦ Quiver.Hom.op_inj
      (BinaryCofan.IsColimit.hom_ext hc (by simp [← h₁]) (by simp [← h₂])))

end opposite

section swap
variable {s : BinaryFan X Y} {t : BinaryFan Y X}

/-- Swap the two sides of a `BinaryFan`. -/
/-
**CategoryTheory.Limits.BinaryFan.swap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → CategoryTheory.Limits.BinaryFan X Y → CategoryTheory.Limits.BinaryFan Y X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Swap the two sides of a `BinaryFan`.
-/
def BinaryFan.swap (s : BinaryFan X Y) : BinaryFan Y X := .mk s.snd s.fst
/-
**CategoryTheory.Limits.BinaryFan.swap_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (s : Ca
tegoryTheory.Limits.BinaryFan X Y),   s.swap.fst = s.snd
参数：s : CategoryTheory.Limits.BinaryFan X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma BinaryFan.swap_fst (s : BinaryFan X Y) : s.swap.fst = s.snd := rfl
/-
**CategoryTheory.Limits.BinaryFan.swap_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (s : Ca
tegoryTheory.Limits.BinaryFan X Y),   s.swap.snd = s.fst
参数：s : CategoryTheory.Limits.BinaryFan X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma BinaryFan.swap_snd (s : BinaryFan X Y) : s.swap.snd = s.fst := rfl

set_option backward.isDefEq.respectTransparency false in
/-- If a binary fan `s` over `X Y` is a limit cone, then `s.swap` is a limit cone over `Y X`. -/
@[simps]
/-
**CategoryTheory.Limits.IsLimit.binaryFanSwap** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {s : CategoryTheory.Limits.BinaryFan X Y} → CategoryTheory.Limits.IsLim
it s → CategoryTheory.Limits.IsLimit s.swap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a binary fan `s` over `X Y` is a limit cone, then `s.swap` is a limit cone ov
er `Y X`.
-/
def IsLimit.binaryFanSwap (I : IsLimit s) : IsLimit s.swap where
  lift t := I.lift (BinaryFan.swap t)
  fac t := by rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := I.uniq (BinaryFan.swap t) m
    rw [h]
    rintro ⟨j⟩
    specialize w ⟨WalkingPair.swap j⟩
    cases j <;> exact w

/-- Construct `HasBinaryProduct Y X` from `HasBinaryProduct X Y`.
This can't be an instance, as it would cause a loop in typeclass search. -/
/-
**CategoryTheory.Limits.HasBinaryProduct.swap** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.HasBinaryProduct`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (X Y : C) [Catego
ryTheory.Limits.HasBinaryProduct X Y],   CategoryTheory.Limits.HasBinaryProduct 
Y X
参数：X Y : C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
Construct `HasBinaryProduct Y X` from `HasBinaryProduct X Y`.
This can't be an instance, as it would cause a loop in typeclass search.
-/
lemma HasBinaryProduct.swap (X Y : C) [HasBinaryProduct X Y] : HasBinaryProduct Y X :=
  .mk ⟨BinaryFan.swap (limit.cone (pair X Y)), (limit.isLimit (pair X Y)).binaryFanSwap⟩

end swap

section braiding
variable {X Y : C} {s : BinaryFan X Y} (P : IsLimit s) {t : BinaryFan Y X} (Q : IsLimit t)

/-- Given a limit cone over `X` and `Y`, and another limit cone over `Y` and `X`, we can construct
an isomorphism between the cone points. Relative to some fixed choice of limits cones for every
pair, these isomorphisms constitute a braiding. -/
/-
**CategoryTheory.Limits.BinaryFan.braiding** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {s : CategoryTheory.Limits.BinaryFan X Y} →         {t : CategoryTheory
.Limits.BinaryFan Y X} →           CategoryTheory.Limits.IsLimit s → CategoryThe
ory.Limits.IsLimit t → (s.pt ≅ t.pt)
参数：s.pt ≅ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a limit cone over `X` and `Y`, and another limit cone over `Y` and `X`, we
 can construct
an isomorphism between the cone points. Relative to some fixed choice of limits 
cones for every
pair, these isomorphisms constitute a braiding.
-/
def BinaryFan.braiding (P : IsLimit s) (Q : IsLimit t) : s.pt ≅ t.pt :=
  P.conePointUniqueUpToIso Q.binaryFanSwap

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryFan.braiding_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {s : Ca
tegoryTheory.Limits.BinaryFan X Y}   (P : CategoryTheory.Limits.IsLimit s) {t : 
CategoryTheory.Limits.BinaryFan Y X} (Q : CategoryTheory.Limits.IsLimit t),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.BinaryFan.braiding P Q).
hom t.fst = s.snd
参数：P : CategoryTheory.Limits.IsLimit s；Q : CategoryTheory.Limits.IsLimit t；Categ
oryTheory.Limits.BinaryFan.braiding P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
lemma BinaryFan.braiding_hom_fst : (braiding P Q).hom ≫ t.fst = s.snd :=
  P.conePointUniqueUpToIso_hom_comp _ ⟨.right⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryFan.braiding_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {s : Ca
tegoryTheory.Limits.BinaryFan X Y}   (P : CategoryTheory.Limits.IsLimit s) {t : 
CategoryTheory.Limits.BinaryFan Y X} (Q : CategoryTheory.Limits.IsLimit t),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.BinaryFan.braiding P Q).
hom t.snd = s.fst
参数：P : CategoryTheory.Limits.IsLimit s；Q : CategoryTheory.Limits.IsLimit t；Categ
oryTheory.Limits.BinaryFan.braiding P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
lemma BinaryFan.braiding_hom_snd : (braiding P Q).hom ≫ t.snd = s.fst :=
  P.conePointUniqueUpToIso_hom_comp _ ⟨.left⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryFan.braiding_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {s : Ca
tegoryTheory.Limits.BinaryFan X Y}   (P : CategoryTheory.Limits.IsLimit s) {t : 
CategoryTheory.Limits.BinaryFan Y X} (Q : CategoryTheory.Limits.IsLimit t),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.BinaryFan.braiding P Q).
inv s.fst = t.snd
参数：P : CategoryTheory.Limits.IsLimit s；Q : CategoryTheory.Limits.IsLimit t；Categ
oryTheory.Limits.BinaryFan.braiding P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
lemma BinaryFan.braiding_inv_fst : (braiding P Q).inv ≫ s.fst = t.snd :=
  P.conePointUniqueUpToIso_inv_comp _ ⟨.left⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.BinaryFan.braiding_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {s : Ca
tegoryTheory.Limits.BinaryFan X Y}   (P : CategoryTheory.Limits.IsLimit s) {t : 
CategoryTheory.Limits.BinaryFan Y X} (Q : CategoryTheory.Limits.IsLimit t),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.BinaryFan.braiding P Q).
inv s.snd = t.fst
参数：P : CategoryTheory.Limits.IsLimit s；Q : CategoryTheory.Limits.IsLimit t；Categ
oryTheory.Limits.BinaryFan.braiding P Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
lemma BinaryFan.braiding_inv_snd : (braiding P Q).inv ≫ s.snd = t.fst :=
  P.conePointUniqueUpToIso_inv_comp _ ⟨.right⟩

end braiding

section assoc
variable {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z}

/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `sXY.X Z`,
if `sYZ` is a limit cone we can construct a binary fan over `X sYZ.X`.

This is an ingredient of building the associator for a Cartesian category. -/
/-
**CategoryTheory.Limits.BinaryFan.assoc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {sXY : CategoryTheory.Limits.BinaryFan X Y} →         {sYZ : Category
Theory.Limits.BinaryFan Y Z} →           CategoryTheory.Limits.IsLimit sYZ →    
         CategoryTheory.Limits.BinaryFan sXY.pt Z → CategoryTheory.Limits.Binary
Fan X sYZ.pt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `sXY.X Z`
,
if `sYZ` is a limit cone we can construct a binary fan over `X sYZ.X`.

This is an ingredient of building the associator for a Cartesian category.
-/
def BinaryFan.assoc (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) : BinaryFan X sYZ.pt :=
  mk (s.fst ≫ sXY.fst) (Q.lift (mk (s.fst ≫ sXY.snd) s.snd))

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.assoc_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {sXY 
: CategoryTheory.Limits.BinaryFan X Y}   {sYZ : CategoryTheory.Limits.BinaryFan 
Y Z} (Q : CategoryTheory.Limits.IsLimit sYZ)   (s : CategoryTheory.Limits.Binary
Fan sXY.pt Z),   (CategoryTheory.Limits.BinaryFan.assoc Q s).fst = CategoryTheor
y.CategoryStruct.comp s.fst sXY.fst
参数：Q : CategoryTheory.Limits.IsLimit sYZ；s : CategoryTheory.Limits.BinaryFan sXY
.pt Z；CategoryTheory.Limits.BinaryFan.assoc Q s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryFan.assoc_fst (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (assoc Q s).fst = s.fst ≫ sXY.fst := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.assoc_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {sXY 
: CategoryTheory.Limits.BinaryFan X Y}   {sYZ : CategoryTheory.Limits.BinaryFan 
Y Z} (Q : CategoryTheory.Limits.IsLimit sYZ)   (s : CategoryTheory.Limits.Binary
Fan sXY.pt Z),   (CategoryTheory.Limits.BinaryFan.assoc Q s).snd =     Q.lift (C
ategoryTheory.Limits.BinaryFan.mk (CategoryTheory.CategoryStruct.comp s.fst sXY.
snd) s.snd)
参数：Q : CategoryTheory.Limits.IsLimit sYZ；s : CategoryTheory.Limits.BinaryFan sXY
.pt Z；CategoryTheory.Limits.BinaryFan.assoc Q s；CategoryTheory.Limits.BinaryFan.
mk (CategoryTheory.CategoryStruct.comp s.fst sXY.snd) s.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryFan.assoc_snd (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (assoc Q s).snd = Q.lift (mk (s.fst ≫ sXY.snd) s.snd) := rfl

/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `X sYZ.X`,
if `sYZ` is a limit cone we can construct a binary fan over `sXY.X Z`.

This is an ingredient of building the associator for a Cartesian category. -/
/-
**CategoryTheory.Limits.BinaryFan.assocInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {sXY : CategoryTheory.Limits.BinaryFan X Y} →         {sYZ : Category
Theory.Limits.BinaryFan Y Z} →           CategoryTheory.Limits.IsLimit sXY →    
         CategoryTheory.Limits.BinaryFan X sYZ.pt → CategoryTheory.Limits.Binary
Fan sXY.pt Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `X sYZ.X`
,
if `sYZ` is a limit cone we can construct a binary fan over `sXY.X Z`.

This is an ingredient of building the associator for a Cartesian category.
-/
def BinaryFan.assocInv (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) : BinaryFan sXY.pt Z :=
  BinaryFan.mk (IsLimit.lift P s.fst (s.snd ≫ sYZ.fst)) (s.snd ≫ sYZ.snd)

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.assocInv_fst** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {sXY 
: CategoryTheory.Limits.BinaryFan X Y}   {sYZ : CategoryTheory.Limits.BinaryFan 
Y Z} (P : CategoryTheory.Limits.IsLimit sXY)   (s : CategoryTheory.Limits.Binary
Fan X sYZ.pt),   (CategoryTheory.Limits.BinaryFan.assocInv P s).fst =     Catego
ryTheory.Limits.BinaryFan.IsLimit.lift P s.fst (CategoryTheory.CategoryStruct.co
mp s.snd sYZ.fst)
参数：P : CategoryTheory.Limits.IsLimit sXY；s : CategoryTheory.Limits.BinaryFan X s
YZ.pt；CategoryTheory.Limits.BinaryFan.assocInv P s；CategoryTheory.CategoryStruct
.comp s.snd sYZ.fst。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryFan.assocInv_fst (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).fst = IsLimit.lift P s.fst (s.snd ≫ sYZ.fst) := rfl

@[simp]
/-
**CategoryTheory.Limits.BinaryFan.assocInv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.BinaryFan`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {sXY 
: CategoryTheory.Limits.BinaryFan X Y}   {sYZ : CategoryTheory.Limits.BinaryFan 
Y Z} (P : CategoryTheory.Limits.IsLimit sXY)   (s : CategoryTheory.Limits.Binary
Fan X sYZ.pt),   (CategoryTheory.Limits.BinaryFan.assocInv P s).snd = CategoryTh
eory.CategoryStruct.comp s.snd sYZ.snd
参数：P : CategoryTheory.Limits.IsLimit sXY；s : CategoryTheory.Limits.BinaryFan X s
YZ.pt；CategoryTheory.Limits.BinaryFan.assocInv P s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma BinaryFan.assocInv_snd (P : IsLimit sXY) (s : BinaryFan X sYZ.pt) :
    (assocInv P s).snd = s.snd ≫ sYZ.snd := rfl

set_option backward.isDefEq.respectTransparency false in
/-- If all the binary fans involved a limit cones, `BinaryFan.assoc` produces another limit cone. -/
@[simps]
/-
**CategoryTheory.Limits.IsLimit.assoc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {sXY : CategoryTheory.Limits.BinaryFan X Y} →         {sYZ : Category
Theory.Limits.BinaryFan Y Z} →           CategoryTheory.Limits.IsLimit sXY →    
         (Q : CategoryTheory.Limits.IsLimit sYZ) →               {s : CategoryTh
eory.Limits.BinaryFan sXY.pt Z} →                 CategoryTheory.Limits.IsLimit 
s →                   CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Binar
yFan.assoc Q s)
参数：Q : CategoryTheory.Limits.IsLimit sYZ；CategoryTheory.Limits.BinaryFan.assoc Q
 s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all the binary fans involved a limit cones, `BinaryFan.assoc` produces anothe
r limit cone.
-/
protected def IsLimit.assoc (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
    (R : IsLimit s) : IsLimit (BinaryFan.assoc Q s) where
  lift t := R.lift (BinaryFan.assocInv P t)
  fac t := by
    rintro ⟨⟨⟩⟩
    · simp
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (BinaryFan.assocInv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
      · simpa using w ⟨.left⟩
      · replace w : m ≫ BinaryFan.IsLimit.lift Q (s.fst ≫ sXY.snd) s.snd = t.π.app ⟨.right⟩ := by
          simpa using! w ⟨.right⟩
        simp [← w]
    · replace w : m ≫ BinaryFan.IsLimit.lift Q (s.fst ≫ sXY.snd) s.snd = t.π.app ⟨.right⟩ := by
        simpa using! w ⟨.right⟩
      simp [← w]

/-- Given two pairs of limit cones corresponding to the parenthesisations of `X × Y × Z`,
we obtain an isomorphism between the cone points. -/
/-
**CategoryTheory.Limits.BinaryFan.associator** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {sXY : CategoryTheory.Limits.BinaryFan X Y} →         {sYZ : Category
Theory.Limits.BinaryFan Y Z} →           CategoryTheory.Limits.IsLimit sXY →    
         CategoryTheory.Limits.IsLimit sYZ →               {s : CategoryTheory.L
imits.BinaryFan sXY.pt Z} →                 CategoryTheory.Limits.IsLimit s →   
                {t : CategoryTheory.Limits.BinaryFan X sYZ.pt} → CategoryTheory.
Limits.IsLimit t → (s.pt ≅ t.pt)
参数：s.pt ≅ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two pairs of limit cones corresponding to the parenthesisations of `X × Y 
× Z`,
we obtain an isomorphism between the cone points.
-/
abbrev BinaryFan.associator (P : IsLimit sXY) (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z}
    (R : IsLimit s) {t : BinaryFan X sYZ.pt} (S : IsLimit t) : s.pt ≅ t.pt :=
  (P.assoc Q R).conePointUniqueUpToIso S

/-- Given a fixed family of limit data for every pair `X Y`, we obtain an associator. -/
/-
**CategoryTheory.Limits.BinaryFan.associatorOfLimitCone** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (L : (X Y
 : C) → CategoryTheory.Limits.LimitCone (CategoryTheory.Limits.pair X Y)) →     
  (X Y Z : C) → (L (L X Y).cone.pt Z).cone.pt ≅ (L X (L Y Z).cone.pt).cone.pt
参数：L : (X Y : C) → CategoryTheory.Limits.LimitCone (CategoryTheory.Limits.pair X
 Y)；X Y Z : C；L (L X Y).cone.pt Z；L X (L Y Z).cone.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fixed family of limit data for every pair `X Y`, we obtain an associator
.
-/
abbrev BinaryFan.associatorOfLimitCone (L : ∀ X Y : C, LimitCone (pair X Y)) (X Y Z : C) :
    (L (L X Y).cone.pt Z).cone.pt ≅ (L X (L Y Z).cone.pt).cone.pt :=
  associator (L X Y).isLimit (L Y Z).isLimit (L (L X Y).cone.pt Z).isLimit
    (L X (L Y Z).cone.pt).isLimit

end assoc

section unitor

set_option backward.isDefEq.respectTransparency false in
/-- Construct a left unitor from specified limit cones. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryFan.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       {s : CategoryTheory.Limits.Cone (CategoryTheory.Functor.empty C)} →      
   CategoryTheory.Limits.IsLimit s →           {t : CategoryTheory.Limits.Binary
Fan s.pt X} → CategoryTheory.Limits.IsLimit t → (t.pt ≅ X)
参数：CategoryTheory.Functor.empty C；t.pt ≅ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a left unitor from specified limit cones.
-/
def BinaryFan.leftUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan s.pt X} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.snd
  inv := Q.lift <| BinaryFan.mk (P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩) (𝟙 _)
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
    · simp

set_option backward.isDefEq.respectTransparency false in
/-- Construct a right unitor from specified limit cones. -/
@[simps]
/-
**CategoryTheory.Limits.BinaryFan.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.BinaryFan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       {s : CategoryTheory.Limits.Cone (CategoryTheory.Functor.empty C)} →      
   CategoryTheory.Limits.IsLimit s →           {t : CategoryTheory.Limits.Binary
Fan X s.pt} → CategoryTheory.Limits.IsLimit t → (t.pt ≅ X)
参数：CategoryTheory.Functor.empty C；t.pt ≅ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a right unitor from specified limit cones.
-/
def BinaryFan.rightUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan X s.pt} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.fst
  inv := Q.lift <| BinaryFan.mk (𝟙 _) <| P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩

end unitor
end CategoryTheory.Limits
set_option linter.style.longFile 1700

