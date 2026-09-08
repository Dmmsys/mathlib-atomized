/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# The equalizer of two morphisms of functors, as a subfunctor

If `F₁` and `F₂` are type-valued functors, `A : Subfunctor F₁`, and
`f` and `g` are two morphisms `A.toFunctor ⟶ F₂`, we introduce
`Subcomplex.equalizer f g`, which is the subfunctor of `F₁` contained in `A`
where `f` and `g` coincide.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F₁ F₂ : C ⥤ Type w} {A : Subfunctor F₁}
  (f g : A.toFunctor ⟶ F₂)

namespace Subfunctor

/-- The equalizer of two morphisms of type-valued functors of types of the form
`A.toFunctor ⟶ F₂` with `A : Subfunctor F₁`, as a subcomplex of `F₁`. -/
@[simps -isSimp]
/-
**CategoryTheory.Subfunctor.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Subfunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F₁ F₂ : 
CategoryTheory.Functor C (Type w)} →       {A : CategoryTheory.Subfunctor F₁} → 
(A.toFunctor ⟶ F₂) → (A.toFunctor ⟶ F₂) → CategoryTheory.Subfunctor F₁
参数：Type w；A.toFunctor ⟶ F₂；A.toFunctor ⟶ F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of two morphisms of type-valued functors of types of the form
`A.toFunctor ⟶ F₂` with `A : Subfunctor F₁`, as a subcomplex of `F₁`.
-/
protected def equalizer : Subfunctor F₁ where
  obj U := Set.ofPred (fun x ↦ ∃ (hx : x ∈ A.obj _), f.app _ ⟨x, hx⟩ = g.app _ ⟨x, hx⟩)
  map φ x := by
    rintro ⟨hx, h⟩
    exact ⟨A.map _ hx,
      (NatTrans.naturality_apply f φ ⟨x, hx⟩).trans (Eq.trans (by rw [h])
        (NatTrans.naturality_apply g φ ⟨x, hx⟩).symm)⟩

attribute [local simp] equalizer_obj
/-
**CategoryTheory.Subfunctor.equalizer_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Subfunctor`。
形式化陈述：equalizer_le : Subfunctor.equalizer f g <= A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equalizer_le : Subfunctor.equalizer f g ≤ A :=
  fun _ _ h ↦ h.1

@[simp]
/-
**CategoryTheory.Subfunctor.equalizer_self** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Subfunctor`。
形式化陈述：equalizer_self : Subfunctor.equalizer f f = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subfunctor.equalizer_obj`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {F₁ F₂ : CategoryTheory.Functor C (Type w)}   {A : Cat
egoryTheory.Subfunctor F₁} (f…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equalizer_self : Subfunctor.equalizer f f = A := by aesop

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subfunctor.mem_equalizer_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Subfunctor`。
形式化陈述：mem_equalizer_iff {i : C} (x : A.toFunctor.obj i) : x.1 in (Subfunctor.equ
alizer f g).obj i ↔ f.app i x = g.app i x
参数：x : A.toFunctor.obj i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CategoryTheory.Subfunctor.equalizer_obj`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {F₁ F₂ : CategoryTheory.Functor C (Type w)}   {A : Cat
egoryTheory.Subfunctor F₁} (f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_equalizer_iff {i : C} (x : A.toFunctor.obj i) :
    x.1 ∈ (Subfunctor.equalizer f g).obj i ↔ f.app i x = g.app i x := by
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Subfunctor.range_le_equalizer_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Subfunctor`。
形式化陈述：range_le_equalizer_iff {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor) : range (φ ≫
 A.ι) <= Subfunctor.equalizer f g ↔ φ ≫ f = φ ≫ g
参数：φ : G ⟶ A.toFunctor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.ext_iff`：∀ {C : Type u₁} {inst : CategoryTheory.
Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}
   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `CategoryTheory.Subfunctor.range_obj`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {F F' : CategoryTheory.Functor C (Type w)} (p : F' ⟶ F)   
(U : C), (CategoryTheory.…
· 使用定理 `CategoryTheory.Subfunctor.ι_app`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (G : CategoryTheory.
Subfunctor F) (x : C)…
· 使用定理 `CategoryTheory.Subfunctor.equalizer_obj`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {F₁ F₂ : CategoryTheory.Functor C (Type w)}   {A : Cat
egoryTheory.Subfunctor F₁} (f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma range_le_equalizer_iff {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor) :
    range (φ ≫ A.ι) ≤ Subfunctor.equalizer f g ↔ φ ≫ f = φ ≫ g := by
  rw [NatTrans.ext_iff]
  simp [le_def, Set.subset_def, ConcreteCategory.hom_ext_iff, funext_iff]
/-
**CategoryTheory.Subfunctor.equalizer_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Subfunctor`。
形式化陈述：equalizer_eq_iff : Subfunctor.equalizer f g = A ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subfunctor.range_le_equalizer_iff`：range_le_equalizer_iff
 {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor) : range (φ ≫ A.ι) <= Subfunctor.equalize
r f g ↔ φ ≫ f = φ ≫ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.Subfunctor.range_ι`：range_ι (G : Subfunctor F) : range G.
ι = G
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.Subfunctor.equalizer_le`：equalizer_le : Subfunctor.equali
zer f g <= A
-/
lemma equalizer_eq_iff :
    Subfunctor.equalizer f g = A ↔ f = g := by
  have := range_le_equalizer_iff f g (𝟙 _)
  simp only [Category.id_comp, range_ι] at this
  rw [← this]
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm (equalizer_le f g) h

/-- Given two morphisms `f` and `g` in `A.toFunctor ⟶ F₂`, this is the monomorphism
of functors corresponding to the inclusion `Subfunctor.equalizer f g ≤ A`. -/
/-
**CategoryTheory.Subfunctor.equalizer.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Subfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two morphisms `f` and `g` in `A.toFunctor ⟶ F₂`, this is the monomorphism
of functors corresponding to the inclusion `Subfunctor.equalizer f g ≤ A`.
-/
def equalizer.ι : (Subfunctor.equalizer f g).toFunctor ⟶ A.toFunctor :=
  homOfLe (equalizer_le f g)
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (equalizer.ι f g) := by
  dsimp [equalizer.ι]
  infer_instance

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subfunctor.equalizer.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Subfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equalizer.ι_ι : equalizer.ι f g ≫ A.ι = (Subfunctor.equalizer f g).ι := rfl

@[reassoc]
/-
**CategoryTheory.Subfunctor.equalizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subfunctor.equalizer`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F₁ F₂ : Category
Theory.Functor C (Type w)}   {A : CategoryTheory.Subfunctor F₁} (f g : A.toFunct
or ⟶ F₂),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Subfunctor.equali
zer.ι f g) f =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Subfunctor
.equalizer.ι f g) g
参数：Type w；f g : A.toFunctor ⟶ F₂；CategoryTheory.Subfunctor.equalizer.ι f g；Categ
oryTheory.Subfunctor.equalizer.ι f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Subfunctor.range_ι`：range_ι (G : Subfunctor F) : range G.
ι = G
-/
lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g := by
  simp [← range_le_equalizer_iff]

/-- Given two morphisms `f` and `g` in `A.toFunctor ⟶ F₂`, if `φ : G ⟶ A.toFunctor`
is such that `φ ≫ f = φ ≫ g`, then this is the lifted morphism
`G ⟶ (Subfunctor.equalizer f g).toFunctor`. This is part of the universal
property of the equalizer that is satisfied by
the functor `(Subfunctor.equalizer f g).toFunctor`. -/
/-
**CategoryTheory.Subfunctor.equalizer.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Subfunctor.equalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F₁ F₂ : 
CategoryTheory.Functor C (Type w)} →       {A : CategoryTheory.Subfunctor F₁} → 
        (f g : A.toFunctor ⟶ F₂) →           {G : CategoryTheory.Functor C (Type
 w)} →             (φ : G ⟶ A.toFunctor) →               CategoryTheory.Category
Struct.comp φ f = CategoryTheory.CategoryStruct.comp φ g →                 (G ⟶ 
(CategoryTheory.Subfunctor.equalizer f g).toFunctor)
参数：Type w；f g : A.toFunctor ⟶ F₂；Type w；φ : G ⟶ A.toFunctor；G ⟶ (CategoryTheory.
Subfunctor.equalizer f g).toFunctor。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two morphisms `f` and `g` in `A.toFunctor ⟶ F₂`, if `φ : G ⟶ A.toFunctor`
is such that `φ ≫ f = φ ≫ g`, then this is the lifted morphism
`G ⟶ (Subfunctor.equalizer f g).toFunctor`. This is part of the universal
property of the equalizer that is satisfied by
the functor `(Subfunctor.equalizer f g).toFunctor`.
-/
def equalizer.lift {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    G ⟶ (Subfunctor.equalizer f g).toFunctor :=
  Subfunctor.lift (φ ≫ A.ι) (by simpa only [range_le_equalizer_iff] using w)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subfunctor.equalizer.lift_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Subfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equalizer.lift_ι' {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ (Subfunctor.equalizer f g).ι = φ ≫ A.ι :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subfunctor.equalizer.lift_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Subfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equalizer.lift_ι {G : C ⥤ Type w} (φ : G ⟶ A.toFunctor)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ equalizer.ι f g = φ :=
  rfl

/-- The (limit) fork which expresses `(Subfunctor.equalizer f g).toFunctor` as
the equalizer of `f` and `g`. -/
@[simps! pt]
/-
**CategoryTheory.Subfunctor.equalizer.fork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Subfunctor.equalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F₁ F₂ : 
CategoryTheory.Functor C (Type w)} →       {A : CategoryTheory.Subfunctor F₁} → 
(f g : A.toFunctor ⟶ F₂) → CategoryTheory.Limits.Fork f g
参数：Type w；f g : A.toFunctor ⟶ F₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.equalizer.condition`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {F₁ F₂ : CategoryTheory.Functor C (Type w)}   {A
 : CategoryTheory.Subfunctor F₁} (f…

--- 原说明 ---
The (limit) fork which expresses `(Subfunctor.equalizer f g).toFunctor` as
the equalizer of `f` and `g`.
-/
def equalizer.fork : Limits.Fork f g :=
  Limits.Fork.ofι (equalizer.ι f g) (equalizer.condition f g)

@[simp]
/-
**CategoryTheory.Subfunctor.equalizer.fork_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Subfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equalizer.fork_ι :
    (equalizer.fork f g).ι = equalizer.ι f g := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `(Subfunctor.equalizer f g).toFunctor` is the equalizer of `f` and `g`. -/
/-
**CategoryTheory.Subfunctor.equalizer.forkIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Subfunctor.equalizer`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F₁ F₂ : 
CategoryTheory.Functor C (Type w)} →       {A : CategoryTheory.Subfunctor F₁} → 
        (f g : A.toFunctor ⟶ F₂) → CategoryTheory.Limits.IsLimit (CategoryTheory
.Subfunctor.equalizer.fork f g)
参数：Type w；f g : A.toFunctor ⟶ F₂；CategoryTheory.Subfunctor.equalizer.fork f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(Subfunctor.equalizer f g).toFunctor` is the equalizer of `f` and `g`.
-/
def equalizer.forkIsLimit : Limits.IsLimit (equalizer.fork f g) :=
  Limits.Fork.IsLimit.mk _
    (fun s ↦ equalizer.lift _ _ s.ι s.condition)
    (fun s ↦ by dsimp)
    (fun s m hm ↦ by simp [← cancel_mono (Subfunctor.equalizer f g).ι, ← hm])

end Subfunctor

end CategoryTheory

