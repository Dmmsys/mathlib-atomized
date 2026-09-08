/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
/-!

# The simplicial nerve of a simplicial category

This file defines the simplicial nerve (sometimes called homotopy coherent nerve) of a simplicial
category.

We define the *simplicial thickening* of a linear order `J` as the simplicial category whose hom
objects `i ⟶ j` are given by the nerve of the poset of "paths" from `i` to `j` in `J`. This is the
poset of subsets of the interval `[i, j]` in `J`, containing the endpoints.

The simplicial nerve of a simplicial category `C` is then defined as the simplicial set whose
`n`-simplices are given by the set of simplicial functors from the simplicial thickening of
the linear order `Fin (n + 1)` to `C`, in other words
`SimplicialNerve C _⦋n⦌ := EnrichedFunctor SSet (SimplicialThickening (Fin (n + 1))) C`.

## Projects

* Prove that the 0-simplices of `SimplicialNerve C` may be identified with the objects of `C`
* Prove that the 1-simplices of `SimplicialNerve C` may be identified with the morphisms of `C`
* Prove that the simplicial nerve of a simplicial category `C`, such that `sHom X Y` is a Kan
  complex for every pair of objects `X Y : C`, is a quasicategory.
* Define the quasicategory of anima as the simplicial nerve of the simplicial category of
  Kan complexes.
* Define the functor from topological spaces to anima.

## References
* [Jacob Lurie, *Higher Topos Theory*, Section 1.1.5][LurieHTT]
-/

@[expose] public section

universe v u

namespace CategoryTheory

open SimplicialCategory EnrichedCategory EnrichedOrdinaryCategory MonoidalCategory

open scoped Simplicial

section SimplicialNerve

/-- A type synonym for a linear order `J`, will be equipped with a simplicial category structure. -/
@[nolint unusedArguments]
/-
**CategoryTheory.SimplicialThickening** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：(J : Type u_1) → [LinearOrder J] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for a linear order `J`, will be equipped with a simplicial catego
ry structure.
-/
structure SimplicialThickening (J : Type*) [LinearOrder J] : Type _ where
  /-- The underlying object of the linear order. -/
  as : J

namespace SimplicialThickening

/--
A path from `i` to `j` in a linear order `J` is a subset of the interval `[i, j]` in `J` containing
the endpoints.
-/
@[ext]
/-
**CategoryTheory.SimplicialThickening.Path** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTh
eory.SimplicialThickening`。
形式化陈述：Path {J : Type*} [LinearOrder J] (i j : J) where /-- The underlying subset
 -/ I : Set J left : i in I
参数：i j : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path from `i` to `j` in a linear order `J` is a subset of the interval `[i, j]
` in `J` containing
the endpoints.
-/
structure Path {J : Type*} [LinearOrder J] (i j : J) where
  /-- The underlying subset -/
  I : Set J
  left : i ∈ I := by simp
  right : j ∈ I := by simp
  left_le (k : J) (_ : k ∈ I) : i ≤ k := by simp
  le_right (k : J) (_ : k ∈ I) : k ≤ j := by simp
/-
**CategoryTheory.SimplicialThickening.Path.le** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.SimplicialThickening.Path`。
形式化陈述：∀ {J : Type u_1} [inst : LinearOrder J] {i j : J} (f : CategoryTheory.Simp
licialThickening.Path i j), i ≤ j
参数：f : CategoryTheory.SimplicialThickening.Path i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialThickening.Path.left_le`：∀ {J : Type u_1} [inst
 : LinearOrder J] {i j : J} (self : CategoryTheory.SimplicialThickening.Path i j
),   ∀ k ∈ self.I, i ≤ k
· 使用定理 `CategoryTheory.SimplicialThickening.Path.right`：∀ {J : Type u_1} [inst :
 LinearOrder J] {i j : J} (self : CategoryTheory.SimplicialThickening.Path i j),
 j ∈ self.I
-/
lemma Path.le {J : Type*} [LinearOrder J] {i j : J} (f : Path i j) : i ≤ j :=
  f.left_le _ f.right
/-
**CategoryTheory.SimplicialThickening.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.SimplicialThickening`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [LinearOrder J] (i j : J) : Category (Path i j) :=
  inferInstanceAs (Category (InducedCategory _ (fun f : Path i j ↦ f.I)))

@[simps -isSimp]
/-
**CategoryTheory.SimplicialThickening.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.SimplicialThickening`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [LinearOrder J] : CategoryStruct (SimplicialThickening J) where
  Hom i j := Path i.as j.as
  id i := { I := {i.as} }
  comp {i j k} f g := {
    I := f.I ∪ g.I
    left := Or.inl f.left
    right := Or.inr g.right
    left_le l := by
      rintro (h | h)
      exacts [(f.left_le l h), (Path.le f).trans (g.left_le l h)]
    le_right l := by
      rintro (h | h)
      exacts [(f.le_right _ h).trans (Path.le g), (g.le_right l h)] }

attribute [local simp] SimplicialThickening.comp_I SimplicialThickening.id_I
/-
**CategoryTheory.SimplicialThickening.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.SimplicialThickening`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [LinearOrder J] (i j : SimplicialThickening J) : Category (i ⟶ j) :=
  inferInstanceAs (Category (Path i.as j.as))

@[ext]
/-
**CategoryTheory.SimplicialThickening.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.SimplicialThickening`。
形式化陈述：hom_ext {J : Type*} [LinearOrder J] (i j : SimplicialThickening J) (x y : 
i ⟶ j) (h : forall t, t in x.I ↔ t in y.I) : x = y
参数：i j : SimplicialThickening J；x y : i ⟶ j；h : forall t, t in x.I ↔ t in y.I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialThickening.Path.ext`：∀ {J : Type u_1} {inst : L
inearOrder J} {i j : J} {x y : CategoryTheory.SimplicialThickening.Path i j},   
x.I = y.I → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
lemma hom_ext {J : Type*} [LinearOrder J]
    (i j : SimplicialThickening J) (x y : i ⟶ j) (h : ∀ t, t ∈ x.I ↔ t ∈ y.I) : x = y := by
  apply Path.ext
  ext
  apply h
/-
**CategoryTheory.SimplicialThickening.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.SimplicialThickening`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [LinearOrder J] : Category (SimplicialThickening J) where
  id_comp f := by ext; simpa using fun h ↦ h ▸ f.left
  comp_id f := by ext; simpa using fun h ↦ h ▸ f.right

/--
Composition of morphisms in `SimplicialThickening J`, as a functor `(i ⟶ j) × (j ⟶ k) ⥤ (i ⟶ k)`
-/
@[simps]
/-
**CategoryTheory.SimplicialThickening.compFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.SimplicialThickening`。
形式化陈述：compFunctor {J : Type*} [LinearOrder J] (i j k : SimplicialThickening J) :
 (i ⟶ j) × (j ⟶ k) ⥤ (i ⟶ k) where obj x
参数：i j k : SimplicialThickening J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms in `SimplicialThickening J`, as a functor `(i ⟶ j) × (j
 ⟶ k) ⥤ (i ⟶ k)`
-/
def compFunctor {J : Type*} [LinearOrder J]
    (i j k : SimplicialThickening J) : (i ⟶ j) × (j ⟶ k) ⥤ (i ⟶ k) where
  obj x := x.1 ≫ x.2
  map f := ⟨⟨⟨Set.union_subset_union f.1.1.1.1 f.2.1.1.1⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local ext (iff := false)] Functor.ext in
attribute [local simp] types_tensorObj_def in
@[simps -isSimp]
/-
**CategoryTheory.SimplicialThickening.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.SimplicialThickening`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type*) [LinearOrder J] :
    SimplicialCategory (SimplicialThickening J) where
  Hom i j := nerve (i ⟶ j)
  id _ := ⟨fun _ ↦ ↾fun _ ↦ (Functor.const _).obj (𝟙 _), fun _ _ _ ↦ by simp; rfl⟩
  comp i j k := ⟨fun _ ↦ ↾fun x ↦ x.1.prod' x.2 ⋙ compFunctor i j k,
    fun _ _ _ ↦ by simp; rfl⟩
  homEquiv {i j} := nerveEquiv.symm.trans (SSet.unitHomEquiv (nerve (i ⟶ j))).symm

set_option backward.isDefEq.respectTransparency.types false in
attribute [local simp] SimplicialThickening.Hom_def

/-- Auxiliary definition for `SimplicialThickening.functor` -/
/-
**CategoryTheory.SimplicialThickening.functorMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.SimplicialThickening`。
形式化陈述：functorMap {J K : Type u} [LinearOrder J] [LinearOrder K] (f : J ->o K) (i
 j : SimplicialThickening J) : (i ⟶ j) ⥤ ((SimplicialThickening.mk <| f i.as) ⟶ 
(SimplicialThickening.mk <| f j.as)) where obj I
参数：f : J ->o K；i j : SimplicialThickening J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `SimplicialThickening.functor`
-/
abbrev functorMap {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J →o K) (i j : SimplicialThickening J) :
      (i ⟶ j) ⥤ ((SimplicialThickening.mk <| f i.as) ⟶ (SimplicialThickening.mk <| f j.as)) where
  obj I := ⟨f '' I.I, Set.mem_image_of_mem f I.left, Set.mem_image_of_mem f I.right,
    by rintro _ ⟨k, hk, rfl⟩; exact f.monotone (I.left_le k hk),
    by rintro _ ⟨k, hk, rfl⟩; exact f.monotone (I.le_right k hk)⟩
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

@[deprecated "No replacement, was using a bad instance" (since := "01-12-2026")]
alias orderHom := functorMap

attribute [local simp] nerveMap_app

set_option backward.isDefEq.respectTransparency.types false in
attribute [local simp] types_tensorObj_def in
/--
The simplicial thickening defines a functor from the category of linear orders to the category of
simplicial categories
-/
@[simps]
/-
**CategoryTheory.SimplicialThickening.functor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.SimplicialThickening`。
形式化陈述：functor {J K : Type u} [LinearOrder J] [LinearOrder K] (f : J ->o K) : Enr
ichedFunctor SSet (SimplicialThickening J) (SimplicialThickening K) where obj x
参数：f : J ->o K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial thickening defines a functor from the category of linear orders t
o the category of
simplicial categories
-/
def functor {J K : Type u} [LinearOrder J] [LinearOrder K]
    (f : J →o K) : EnrichedFunctor SSet (SimplicialThickening J) (SimplicialThickening K) where
  obj x := .mk (f x.as)
  map i j := nerveMap ((functorMap f i j))
  map_id i := by
    ext
    simp only [eId, EnrichedCategory.id]
    exact Functor.ext (by cat_disch)
  map_comp i j k := by
    ext
    simp only [eComp, EnrichedCategory.comp]
    exact Functor.ext (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SimplicialThickening.functor_id** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.SimplicialThickening`。
形式化陈述：functor_id (J : Type u) [LinearOrder J] : (functor (OrderHom.id (α
参数：J : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.EnrichedFunctor.ext`：ext {C : Type u₁} {D : Type u₂} [Enr
ichedCategory V C] [EnrichedCategory V D] {F G : EnrichedFunctor V C D} (h_obj :
 forall X, F.obj X = G.o…
· 使用引理 `SSet.hom_ext`：hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n 
= g.app n) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SimplicialThickening.functor_map`：∀ {J K : Type u} [inst 
: LinearOrder J] [inst_1 : LinearOrder K] (f : J →o K)   (i j : CategoryTheory.S
implicialThickening J),   (CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.nerveMap_app`：∀ {C D : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] [inst_1 : CategoryTheory.Category.{v, u} D]   (F : CategoryTheor
y.Functor C D) (x…
· 使用定理 `CategoryTheory.Functor.mapComposableArrows_obj_obj`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.SimplicialThickening.Path.mk.congr_simp`：∀ {J : Type u_1}
 [inst : LinearOrder J] {i j : J} (I I_1 : Set J) (e_I : I = I_1) (left : i ∈ I)
 (right : j ∈ I)   (left_le : ∀ k ∈ I, i ≤ k…
· 使用定理 `CategoryTheory.EnrichedFunctor.id_map`：∀ (V : Type v) [inst : CategoryTh
eory.Category.{w, v} V] [inst_1 : CategoryTheory.MonoidalCategory V] (C : Type u
₁)   [inst_2 : CategoryTheo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma functor_id (J : Type u) [LinearOrder J] :
    (functor (OrderHom.id (α := J))) = EnrichedFunctor.id _ _ := by
  refine EnrichedFunctor.ext _ (fun _ ↦ rfl) fun i j ↦ ?_
  ext
  exact Functor.ext (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.SimplicialThickening.functor_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.SimplicialThickening`。
形式化陈述：functor_comp {J K L : Type u} [LinearOrder J] [LinearOrder K] [LinearOrder
 L] (f : J ->o K) (g : K ->o L) : functor (g.comp f) = (functor f).comp _ (funct
or g)
参数：f : J ->o K；g : K ->o L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.EnrichedFunctor.ext`：ext {C : Type u₁} {D : Type u₂} [Enr
ichedCategory V C] [EnrichedCategory V D] {F G : EnrichedFunctor V C D} (h_obj :
 forall X, F.obj X = G.o…
· 使用引理 `SSet.hom_ext`：hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : forall n, f.app n 
= g.app n) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapComposableArrows_obj_obj`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTh
eory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SimplicialThickening.functor_map`：∀ {J K : Type u} [inst 
: LinearOrder J] [inst_1 : LinearOrder K] (f : J →o K)   (i j : CategoryTheory.S
implicialThickening J),   (CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.nerveMap_app`：∀ {C D : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] [inst_1 : CategoryTheory.Category.{v, u} D]   (F : CategoryTheor
y.Functor C D) (x…
· 使用定理 `CategoryTheory.SimplicialThickening.Path.mk.congr_simp`：∀ {J : Type u_1}
 [inst : LinearOrder J] {i j : J} (I I_1 : Set J) (e_I : I = I_1) (left : i ∈ I)
 (right : j ∈ I)   (left_le : ∀ k ∈ I, i ≤ k…
· 使用定理 `CategoryTheory.EnrichedFunctor.comp_map`：∀ (V : Type v) [inst : Category
Theory.Category.{w, v} V] [inst_1 : CategoryTheory.MonoidalCategory V] {C : Type
 u₁}   {D : Type u₂} {E : Typ…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用引理 `CategoryTheory.SimplicialThickening.hom_ext`：hom_ext {J : Type*} [Linear
Order J] (i j : SimplicialThickening J) (x y : i ⟶ j) (h : forall t, t in x.I ↔ 
t in y.I) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma functor_comp {J K L : Type u} [LinearOrder J] [LinearOrder K]
    [LinearOrder L] (f : J →o K) (g : K →o L) :
    functor (g.comp f) =
      (functor f).comp _ (functor g) := by
  refine EnrichedFunctor.ext _ (fun _ ↦ rfl) fun i j ↦ ?_
  ext
  exact Functor.ext (by cat_disch)

end SimplicialThickening

set_option backward.isDefEq.respectTransparency.types false in
/--
The simplicial nerve of a simplicial category `C` is defined as the simplicial set whose
`n`-simplices are given by the set of simplicial functors from the simplicial thickening of
the linear order `Fin (n + 1)` to `C`
-/
/-
**CategoryTheory.SimplicialNerve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：SimplicialNerve (C : Type u) [Category.{v} C] [SimplicialCategory C] : SSe
t.{max u v} where obj n
参数：C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplicial nerve of a simplicial category `C` is defined as the simplicial s
et whose
`n`-simplices are given by the set of simplicial functors from the simplicial th
ickening of
the linear order `Fin (n + 1)` to `C`
-/
def SimplicialNerve (C : Type u) [Category.{v} C] [SimplicialCategory C] :
    SSet.{max u v} where
  obj n := EnrichedFunctor SSet (SimplicialThickening (ULift (Fin (n.unop.len + 1)))) C
  map f := ↾((SimplicialThickening.functor f.unop.toOrderHom.uliftMap).comp
    (E := C) SSet)
  map_id i := by
    ext
    change EnrichedFunctor.comp SSet (SimplicialThickening.functor OrderHom.id) _ = _
    rw [SimplicialThickening.functor_id]
    rfl
  map_comp f g := by
    ext
    change EnrichedFunctor.comp SSet (SimplicialThickening.functor
      (f.unop.toOrderHom.uliftMap.comp g.unop.toOrderHom.uliftMap)) _ = _
    rw [SimplicialThickening.functor_comp]
    rfl

end SimplicialNerve

end CategoryTheory

