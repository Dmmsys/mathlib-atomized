/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Data.Finite.Prod

/-!
# The category of finite types.

We define the category of finite types, denoted `FintypeCat` as
the full subcategory of types with a `Finite` instance.

We also define `FintypeCat.Skeleton`, the standard skeleton of `FintypeCat` whose objects
are `Fin n` for `n : ℕ`. We prove that the obvious inclusion functor
`FintypeCat.Skeleton ⥤ FintypeCat` is an equivalence of categories in
`FintypeCat.Skeleton.equivalence`.
We prove that `FintypeCat.Skeleton` is a skeleton of `FintypeCat` in `FintypeCat.isSkeleton`.
-/

@[expose] public section

open CategoryTheory

/-- The category of finite types. -/
/-
**FintypeCat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FintypeCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite types.
-/
abbrev FintypeCat := ObjectProperty.FullSubcategory (C := Type*) Finite

namespace FintypeCat

/-- Construct a term of `FintypeCat` from a type endowed with a `Finite` instance. -/
/-
**FintypeCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `FintypeCat`。
形式化陈述：of (X : Type*) [Finite X] : FintypeCat
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a term of `FintypeCat` from a type endowed with a `Finite` instance.
-/
abbrev of (X : Type*) [Finite X] : FintypeCat :=
  ⟨X, inferInstance⟩
/-
**FintypeCat.instCoeSort** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
形式化陈述：instCoeSort : CoeSort FintypeCat Type*
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeSort : CoeSort FintypeCat Type* :=
  ⟨fun X ↦ X.obj⟩
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited FintypeCat :=
  ⟨of PEmpty⟩
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : FintypeCat} : Finite X :=
  X.property

/-- A `Fintype` instance on objects on `FintypeCat`, that should be turned on as needed.
Prefer the `Finite` instance if possible. -/
@[instance_reducible]
/-
**FintypeCat.fintype** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat`。
形式化陈述：fintype {X : FintypeCat} : Fintype X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FintypeCat.instFiniteObj`：∀ {X : FintypeCat}, Finite X.obj

--- 原说明 ---
A `Fintype` instance on objects on `FintypeCat`, that should be turned on as nee
ded.
Prefer the `Finite` instance if possible.
-/
noncomputable def fintype {X : FintypeCat} : Fintype X :=
  Fintype.ofFinite X.obj

/-- The fully faithful embedding of `FintypeCat` into the category of types. -/
@[simps!]
/-
**FintypeCat.incl** 是 Mathlib 中的一个缩写定义，位于命名空间 `FintypeCat`。
形式化陈述：incl : FintypeCat ⥤ Type*
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful embedding of `FintypeCat` into the category of types.
-/
abbrev incl : FintypeCat ⥤ Type* := ObjectProperty.ι _
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : incl.Full := ObjectProperty.full_ι _
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : incl.Faithful := ObjectProperty.faithful_ι _
/-
**FintypeCat.** 是 Mathlib 中的一个示例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ConcreteCategory FintypeCat
    (fun X Y ↦ TypeCat.Fun X.obj Y.obj) :=
  inferInstance

/-- Help typeclass inference infer fullness of forgetful functor. -/
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help typeclass inference infer fullness of forgetful functor.
-/
instance : (forget FintypeCat).Full := inferInstanceAs <| FintypeCat.incl.Full

@[simp]
/-
**FintypeCat.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `FintypeCat`。
形式化陈述：id_apply (X : FintypeCat) (x : X) : (𝟙 X : X -> X) x = x
参数：X : FintypeCat；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (X : FintypeCat) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
/-
**FintypeCat.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `FintypeCat`。
形式化陈述：comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) 
x = g (f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl

@[simp]
/-
**FintypeCat.hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：hom_apply {X Y : FintypeCat} (f : X ⟶ Y) (x : X) : f.hom x = f x
参数：f : X ⟶ Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_apply {X Y : FintypeCat} (f : X ⟶ Y) (x : X) :
    f.hom x = f x := rfl

-- Isn't `@[simp]` because `simp` can prove it after importing `Mathlib.CategoryTheory.Elementwise`.
/-
**FintypeCat.hom_inv_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：hom_inv_id_apply {X Y : FintypeCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) 
= x
参数：f : X ≅ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
-/
lemma hom_inv_id_apply {X Y : FintypeCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  ConcreteCategory.congr_hom f.hom_inv_id x

-- Isn't `@[simp]` because `simp` can prove it after importing `Mathlib.CategoryTheory.Elementwise`.
/-
**FintypeCat.inv_hom_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：inv_hom_id_apply {X Y : FintypeCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) 
= y
参数：f : X ≅ Y；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
lemma inv_hom_id_apply {X Y : FintypeCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  ConcreteCategory.congr_hom f.inv_hom_id y

@[ext]
/-
**FintypeCat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
参数：f g : X ⟶ Y；h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ h

/-- Constructor for morphisms in `FintypeCat`. -/
/-
**FintypeCat.homMk** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat`。
形式化陈述：homMk {X Y : FintypeCat} (f : X -> Y) : X ⟶ Y where hom
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `FintypeCat`.
-/
def homMk {X Y : FintypeCat} (f : X → Y) : X ⟶ Y where
  hom := ↾f

@[simp]
/-
**FintypeCat.homMk_apply** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：homMk_apply {X Y : FintypeCat} (f : X -> Y) (x : X) : homMk f x = f x
参数：f : X -> Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_apply {X Y : FintypeCat} (f : X → Y) (x : X) :
    homMk f x = f x := rfl

@[simp]
/-
**FintypeCat.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：id_hom (X : FintypeCat) : 𝟙 X.obj = ↾id
参数：X : FintypeCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (X : FintypeCat) : 𝟙 X.obj = ↾id := rfl

@[simp, reassoc]
/-
**FintypeCat.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：comp_hom {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) : f.hom ≫ g.hom = ↾(
g.hom ∘ f.hom)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {X Y Z : FintypeCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.hom ≫ g.hom = ↾(g.hom ∘ f.hom) := rfl

@[simp]
/-
**FintypeCat.homMk_eq_id_iff** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：homMk_eq_id_iff {X : FintypeCat} (f : X -> X) : homMk f = 𝟙 X ↔ f = id
参数：f : X -> X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma homMk_eq_id_iff {X : FintypeCat} (f : X → X) :
    homMk f = 𝟙 X ↔ f = id := by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

@[simp]
/-
**FintypeCat.homMk_eq_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：homMk_eq_comp_iff {X Y Z : FintypeCat} (f : X -> Y) (g : Y -> Z) (h : X ->
 Z) : homMk h = homMk f ≫ homMk g ↔ h = g ∘ f
参数：f : X -> Y；g : Y -> Z；h : X -> Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma homMk_eq_comp_iff {X Y Z : FintypeCat} (f : X → Y) (g : Y → Z) (h : X → Z) :
    homMk h = homMk f ≫ homMk g ↔ h = g ∘ f := by
  constructor
  · intro h
    ext x
    exact ConcreteCategory.congr_hom h x
  · rintro rfl
    rfl

-- See `equivEquivIso` in the root namespace for the analogue in `Type`.
/-- Equivalences between finite types are the same as isomorphisms in `FintypeCat`. -/
@[simps]
/-
**FintypeCat.equivEquivIso** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat`。
形式化陈述：equivEquivIso {A B : FintypeCat} : A ≃ B ≃ (A ≅ B) where toFun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Equivalences between finite types are the same as isomorphisms in `FintypeCat`.
-/
def equivEquivIso {A B : FintypeCat} : A ≃ B ≃ (A ≅ B) where
  toFun e :=
    { hom := homMk e
      inv := homMk e.symm }
  invFun i :=
    { toFun := i.hom
      invFun := i.inv
      left_inv := ConcreteCategory.congr_hom i.hom_inv_id
      right_inv := ConcreteCategory.congr_hom i.inv_hom_id }
  left_inv := by cat_disch
  right_inv := by cat_disch
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : FintypeCat) : Finite (X ⟶ Y) :=
  Finite.of_equiv _ (show (X ⟶ Y) ≃ (X → Y) from
    InducedCategory.homEquiv.trans TypeCat.homEquiv).symm
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : FintypeCat) : Finite (X ≅ Y) :=
  Finite.of_injective _ (fun _ _ h ↦ Iso.ext h)
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FintypeCat) : Finite (Aut X) :=
  inferInstanceAs <| Finite (X ≅ X)

universe u

/--
The "standard" skeleton for `FintypeCat`. This is the full subcategory of `FintypeCat`
spanned by objects of the form `ULift (Fin n)` for `n : ℕ`. We parameterize the objects
of `FintypeCat.Skeleton` directly as `ULift ℕ`, as the type `ULift (Fin m) ≃ ULift (Fin n)`
is nonempty if and only if `n = m`. Specifying universes, `Skeleton : Type u` is a small
skeletal category equivalent to `FintypeCat.{u}`.
-/
/-
**FintypeCat.Skeleton** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat`。
形式化陈述：Skeleton : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "standard" skeleton for `FintypeCat`. This is the full subcategory of `Finty
peCat`
spanned by objects of the form `ULift (Fin n)` for `n : ℕ`. We parameterize the 
objects
of `FintypeCat.Skeleton` directly as `ULift ℕ`, as the type `ULift (Fin m) ≃ ULi
ft (Fin n)`
is nonempty if and only if `n = m`. Specifying universes, `Skeleton : Type u` is
 a small
skeletal category equivalent to `FintypeCat.{u}`.
-/
def Skeleton : Type u :=
  ULift ℕ

namespace Skeleton

/-- Given any natural number `n`, this creates the associated object of `FintypeCat.Skeleton`. -/
/-
**FintypeCat.Skeleton.mk** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat.Skeleton`。
形式化陈述：mk : Nat -> Skeleton
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any natural number `n`, this creates the associated object of `FintypeCat.
Skeleton`.
-/
def mk : ℕ → Skeleton :=
  ULift.up
/-
**FintypeCat.Skeleton.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat.Skeleton`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Skeleton :=
  ⟨mk 0⟩

/-- Given any object of `FintypeCat.Skeleton`, this returns the associated natural number. -/
/-
**FintypeCat.Skeleton.len** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat.Skeleton`。
形式化陈述：len : Skeleton -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any object of `FintypeCat.Skeleton`, this returns the associated natural n
umber.
-/
def len : Skeleton → ℕ :=
  ULift.down

@[ext]
/-
**FintypeCat.Skeleton.ext** 是 Mathlib 中的一个定理，位于命名空间 `FintypeCat.Skeleton`。
形式化陈述：ext (X Y : Skeleton) : X.len = Y.len -> X = Y
参数：X Y : Skeleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
-/
theorem ext (X Y : Skeleton) : X.len = Y.len → X = Y :=
  ULift.ext _ _
/-
**FintypeCat.Skeleton.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat.Skeleton`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SmallCategory Skeleton.{u} where
  Hom X Y := ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)
  id _ := id
  comp f g := g ∘ f
/-
**FintypeCat.Skeleton.is_skeletal** 是 Mathlib 中的一个定理，位于命名空间 `FintypeCat.Skeleton
`。
形式化陈述：is_skeletal : Skeletal Skeleton.{u}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FintypeCat.Skeleton.ext`：ext (X Y : Skeleton) : X.len = Y.len -> X = Y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.equiv_iff_eq`：equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ULift.up_down`：∀ {α : Type u} (b : ULift.{v, u} α), { down := b.down } =
 b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
-/
theorem is_skeletal : Skeletal Skeleton.{u} := fun X Y ⟨h⟩ =>
  ext _ _ <|
    Fin.equiv_iff_eq.mp <|
      Nonempty.intro <|
        { toFun := fun x => (h.hom ⟨x⟩).down
          invFun := fun x => (h.inv ⟨x⟩).down
          left_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.hom ≫ h.inv) _).down = _
            simp
            rfl
          right_inv := by
            intro a
            change ULift.down _ = _
            rw [ULift.up_down]
            change ((h.inv ≫ h.hom) _).down = _
            simp
            rfl }

/-- The canonical fully faithful embedding of `FintypeCat.Skeleton` into `FintypeCat`. -/
/-
**FintypeCat.Skeleton.incl** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat.Skeleton`。
形式化陈述：incl : Skeleton.{u} ⥤ FintypeCat.{u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical fully faithful embedding of `FintypeCat.Skeleton` into `FintypeCat
`.
-/
def incl : Skeleton.{u} ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of (ULift (Fin X.len))
  map f := homMk f
/-
**FintypeCat.Skeleton.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat.Skeleton`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : incl.Full where map_surjective _ := ⟨_, rfl⟩
/-
**FintypeCat.Skeleton.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat.Skeleton`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : incl.Faithful where
  map_injective h := by
    simpa using TypeCat.homEquiv.symm.injective (InducedCategory.homEquiv.symm.injective h)

set_option backward.isDefEq.respectTransparency.types false in
/-
**FintypeCat.Skeleton.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat.Skeleton`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : incl.EssSurj :=
  Functor.EssSurj.mk fun X =>
    letI := X.fintype
    let F := Fintype.equivFin X
    ⟨mk (Fintype.card X),
      Nonempty.intro
        { hom := homMk (F.symm ∘ ULift.down)
          inv := homMk (ULift.up ∘ F) }⟩
/-
**FintypeCat.Skeleton.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat.Skeleton`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : incl.IsEquivalence where

/-- The equivalence between `FintypeCat.Skeleton` and `FintypeCat`. -/
/-
**FintypeCat.Skeleton.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat.Skeleton
`。
形式化陈述：equivalence : Skeleton ≌ FintypeCat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FintypeCat.Skeleton.instIsEquivalenceIncl`：FintypeCat.Skeleton.incl.IsEq
uivalence

--- 原说明 ---
The equivalence between `FintypeCat.Skeleton` and `FintypeCat`.
-/
noncomputable def equivalence : Skeleton ≌ FintypeCat :=
  incl.asEquivalence

attribute [local instance] FintypeCat.fintype in
@[simp]
/-
**FintypeCat.Skeleton.incl_mk_nat_card** 是 Mathlib 中的一个定理，位于命名空间 `FintypeCat.Ske
leton`。
形式化陈述：incl_mk_nat_card (n : Nat) : Fintype.card (incl.obj (mk n)) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
-/
theorem incl_mk_nat_card (n : ℕ) :
    Fintype.card (incl.obj (mk n)) = n := by
  convert! Finset.card_fin n
  dsimp [incl, mk, len]
  convert! (Fintype.ofEquiv_card Equiv.ulift).symm

end Skeleton

/-- `FintypeCat.Skeleton` is a skeleton of `FintypeCat`. -/
/-
**FintypeCat.isSkeleton** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：isSkeleton : IsSkeletonOf FintypeCat Skeleton Skeleton.incl where skel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FintypeCat.Skeleton.is_skeletal`：is_skeletal : Skeletal Skeleton.{u}
· 使用定理 `FintypeCat.Skeleton.instIsEquivalenceIncl`：FintypeCat.Skeleton.incl.IsEq
uivalence

--- 原说明 ---
`FintypeCat.Skeleton` is a skeleton of `FintypeCat`.
-/
lemma isSkeleton : IsSkeletonOf FintypeCat Skeleton Skeleton.incl where
  skel := Skeleton.is_skeletal
  eqv := by infer_instance

section Universes

universe v

attribute [local instance] FintypeCat.fintype in
/-- If `u` and `v` are two arbitrary universes, we may construct a functor
`uSwitch.{u, v} : FintypeCat.{u} ⥤ FintypeCat.{v}` by sending
`X : FintypeCat.{u}` to `ULift.{v} (Fin (Fintype.card X))`. -/
/-
**FintypeCat.uSwitch** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat`。
形式化陈述：uSwitch : FintypeCat.{u} ⥤ FintypeCat.{v} where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `u` and `v` are two arbitrary universes, we may construct a functor
`uSwitch.{u, v} : FintypeCat.{u} ⥤ FintypeCat.{v}` by sending
`X : FintypeCat.{u}` to `ULift.{v} (Fin (Fintype.card X))`.
-/
noncomputable def uSwitch : FintypeCat.{u} ⥤ FintypeCat.{v} where
  obj X := FintypeCat.of <| ULift.{v} (Fin (Fintype.card X))
  map {X Y} f :=
    homMk (ULift.up ∘ Fintype.equivFin Y ∘ f.hom ∘ (Fintype.equivFin X).symm ∘ ULift.down)

attribute [local instance] FintypeCat.fintype in
/-- Switching the universe of an object `X : FintypeCat.{u}` does not change `X` up to equivalence
of types. This is natural in the sense that it commutes with `uSwitch.map f` for
any `f : X ⟶ Y` in `FintypeCat.{u}`. -/
/-
**FintypeCat.uSwitchEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat`。
形式化陈述：uSwitchEquiv (X : FintypeCat.{u}) : uSwitch.{u, v}.obj X ≃ X
参数：X : FintypeCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Switching the universe of an object `X : FintypeCat.{u}` does not change `X` up 
to equivalence
of types. This is natural in the sense that it commutes with `uSwitch.map f` for
any `f : X ⟶ Y` in `FintypeCat.{u}`.
-/
noncomputable def uSwitchEquiv (X : FintypeCat.{u}) :
    uSwitch.{u, v}.obj X ≃ X :=
  Equiv.ulift.trans (Fintype.equivFin X).symm

set_option backward.isDefEq.respectTransparency false in
/-
**FintypeCat.uSwitchEquiv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：uSwitchEquiv_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : uSwitch.{u
, v}.obj X) : f (X.uSwitchEquiv x) = Y.uSwitchEquiv (uSwitch.map f x)
参数：f : X ⟶ Y；x : uSwitch.{u, v}.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.ulift_apply`：∀ {α : Type v}, ⇑Equiv.ulift = ULift.down
· 使用引理 `FintypeCat.homMk_apply`：homMk_apply {X Y : FintypeCat} (f : X -> Y) (x :
 X) : homMk f x = f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma uSwitchEquiv_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y)
    (x : uSwitch.{u, v}.obj X) :
    f (X.uSwitchEquiv x) = Y.uSwitchEquiv (uSwitch.map f x) := by
  simp only [uSwitch, uSwitchEquiv, Equiv.trans_apply, Equiv.ulift_apply]
  rw [homMk_apply]
  aesop
/-
**FintypeCat.uSwitchEquiv_symm_naturality** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`
。
形式化陈述：uSwitchEquiv_symm_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : X) : 
uSwitch.map f (X.uSwitchEquiv.symm x) = Y.uSwitchEquiv.symm (f x)
参数：f : X ⟶ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FintypeCat.uSwitchEquiv_naturality`：uSwitchEquiv_naturality {X Y : Finty
peCat.{u}} (f : X ⟶ Y) (x : uSwitch.{u, v}.obj X) : f (X.uSwitchEquiv x) = Y.uSw
itchEquiv (uSwitch.map f…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma uSwitchEquiv_symm_naturality {X Y : FintypeCat.{u}} (f : X ⟶ Y) (x : X) :
    uSwitch.map f (X.uSwitchEquiv.symm x) = Y.uSwitchEquiv.symm (f x) := by
  rw [Equiv.eq_symm_apply, ← uSwitchEquiv_naturality f, Equiv.apply_symm_apply]
/-
**FintypeCat.uSwitch_map_uSwitch_map** 是 Mathlib 中的一个引理，位于命名空间 `FintypeCat`。
形式化陈述：uSwitch_map_uSwitch_map {X Y : FintypeCat.{u}} (f : X ⟶ Y) : uSwitch.map (
uSwitch.map f) = (equivEquivIso ((uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEqu
iv)).hom ≫ f ≫ (equivEquivIso ((uSwitch.obj Y).uSwitchEquiv.trans Y.uSwitchEquiv
)).inv
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uSwitch_map_uSwitch_map {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    uSwitch.map (uSwitch.map f) =
    (equivEquivIso ((uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)).hom ≫
      f ≫ (equivEquivIso ((uSwitch.obj Y).uSwitchEquiv.trans
      Y.uSwitchEquiv)).inv := rfl

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] uSwitch_map_uSwitch_map in
/-- `uSwitch.{u, v}` is an equivalence of categories with quasi-inverse `uSwitch.{v, u}`. -/
/-
**FintypeCat.uSwitchEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `FintypeCat`。
形式化陈述：uSwitchEquivalence : FintypeCat.{u} ≌ FintypeCat.{v} where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`uSwitch.{u, v}` is an equivalence of categories with quasi-inverse `uSwitch.{v,
 u}`.
-/
noncomputable def uSwitchEquivalence : FintypeCat.{u} ≌ FintypeCat.{v} where
  functor := uSwitch
  inverse := uSwitch
  unitIso := NatIso.ofComponents (fun X ↦ (equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv).symm)
  counitIso := NatIso.ofComponents (fun X ↦ equivEquivIso <|
    (uSwitch.obj X).uSwitchEquiv.trans X.uSwitchEquiv)
  functor_unitIso_comp X := by
    ext x
    simp [← uSwitchEquiv_naturality]
/-
**FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : uSwitch.IsEquivalence :=
  uSwitchEquivalence.isEquivalence_functor

end Universes

end FintypeCat

namespace FunctorToFintypeCat

universe u v w

variable {C : Type u} [Category.{v} C] (F G : C ⥤ FintypeCat.{w}) {X Y : C}

/-
**FunctorToFintypeCat.naturality** 是 Mathlib 中的一个引理，位于命名空间 `FunctorToFintypeCat`
。
形式化陈述：naturality (σ : F ⟶ G) (f : X ⟶ Y) (x : F.obj X) : σ.app Y (F.map f x) = G
.map f (σ.app X x)
参数：σ : F ⟶ G；f : X ⟶ Y；x : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma naturality (σ : F ⟶ G) (f : X ⟶ Y) (x : F.obj X) :
    σ.app Y (F.map f x) = G.map f (σ.app X x) :=
  (σ.naturality_apply f) x

end FunctorToFintypeCat

