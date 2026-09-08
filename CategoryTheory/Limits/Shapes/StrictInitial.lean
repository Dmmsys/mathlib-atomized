/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Strict initial objects

This file sets up the basic theory of strict initial objects: initial objects where every morphism
to it is an isomorphism. This generalises a property of the empty set in the category of sets:
namely that the only function to the empty set is from itself.

We say `C` has strict initial objects if every initial object is strict, i.e. given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.
Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist, which turns out to be a more useful notion to formalise.

If the binary product of `X` with a strict initial object exists, it is also initial.

To show a category `C` with an initial object has strict initial objects, the most convenient way
is to show any morphism to the (chosen) initial object is an isomorphism and use
`hasStrictInitialObjects_of_initial_is_strict`.

The dual notion (strict terminal objects) occurs much less frequently in practice so is ignored.

## TODO

* Construct examples of this: `Type*`, `TopCat`, `Groupoid`, simplicial types, posets.
* Construct the bottom element of the subobject lattice given strict initials.
* Show Cartesian closed categories have strict initials

## References
* https://ncatlab.org/nlab/show/strict+initial+object
-/

@[expose] public section


universe v u

namespace CategoryTheory

namespace Limits

open Category

variable (C : Type u) [Category.{v} C]

section StrictInitial

/-- We say `C` has strict initial objects if every initial object is strict, i.e. given any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.

Strictly speaking, this says that *any* initial object must be strict, rather than that strict
initial objects exist.
-/
/-
**CategoryTheory.Limits.HasStrictInitialObjects** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say `C` has strict initial objects if every initial object is strict, i.e. gi
ven any morphism
`f : A ⟶ I` where `I` is initial, then `f` is an isomorphism.

Strictly speaking, this says that *any* initial object must be strict, rather th
an that strict
initial objects exist.
-/
class HasStrictInitialObjects : Prop where
  out : ∀ {I A : C} (f : A ⟶ I), IsInitial I → IsIso f

variable {C}

section

variable [HasStrictInitialObjects C] {I : C}

/-
**CategoryTheory.Limits.IsInitial.isIso_to** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictInitialObjects C] {I : C}   (hI : CategoryTheory.Limits.IsInitial
 I) {A : C} (f : A ⟶ I), CategoryTheory.IsIso f
参数：hI : CategoryTheory.Limits.IsInitial I；f : A ⟶ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasStrictInitialObjects.out`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasStrictIniti
alObjects C]   {I A : C} (f : A ⟶ I) (a…
-/
theorem IsInitial.isIso_to (hI : IsInitial I) {A : C} (f : A ⟶ I) : IsIso f :=
  HasStrictInitialObjects.out f hI
/-
**CategoryTheory.Limits.IsInitial.strict_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictInitialObjects C] {I : C}   (hI : CategoryTheory.Limits.IsInitial
 I) {A : C} (f g : A ⟶ I), f = g
参数：hI : CategoryTheory.Limits.IsInitial I；f g : A ⟶ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.isIso_to`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects C] {I 
: C}   (hI : CategoryTheory.Li…
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
theorem IsInitial.strict_hom_ext (hI : IsInitial I) {A : C} (f g : A ⟶ I) : f = g := by
  have := hI.isIso_to f
  have := hI.isIso_to g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))
/-
**CategoryTheory.Limits.IsInitial.subsingleton_to** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictInitialObjects C] {I : C}   (hI : CategoryTheory.Limits.IsInitial
 I) {A : C}, Subsingleton (A ⟶ I)
参数：hI : CategoryTheory.Limits.IsInitial I；A ⟶ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.strict_hom_ext`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects 
C] {I : C}   (hI : CategoryTheory.Li…
-/
theorem IsInitial.subsingleton_to (hI : IsInitial I) {A : C} : Subsingleton (A ⟶ I) :=
  ⟨hI.strict_hom_ext⟩

/-- If `X ⟶ Y` with `Y` being a strict initial object, then `X` is also an initial object. -/
noncomputable
/-
**CategoryTheory.Limits.IsInitial.ofStrict** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.IsInitial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasStrictInitialObjects C] →       {X Y : C} → (X ⟶ Y) → CategoryT
heory.Limits.IsInitial Y → CategoryTheory.Limits.IsInitial X
参数：X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.isIso_to`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects C] {I 
: C}   (hI : CategoryTheory.Li…
-/
def IsInitial.ofStrict {X Y : C} (f : X ⟶ Y)
    (hY : IsInitial Y) : IsInitial X :=
  letI := hY.isIso_to f
  hY.ofIso (asIso f).symm
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) initial_mono_of_strict_initial_objects : InitialMonoClass C where
  isInitial_mono_from := fun _ hI => { right_cancellation := fun _ _ _ => hI.strict_hom_ext _ _ }

/-- If `I` is initial, then `X ⨯ I` is isomorphic to it. -/
@[simps! hom]
/-
**CategoryTheory.Limits.mulIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：mulIsInitial (X : C) [HasBinaryProduct X I] (hI : IsInitial I) : X ⨯ I ≅ I
参数：X : C；hI : IsInitial I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` is initial, then `X ⨯ I` is isomorphic to it.
-/
noncomputable def mulIsInitial (X : C) [HasBinaryProduct X I] (hI : IsInitial I) : X ⨯ I ≅ I := by
  have := hI.isIso_to (prod.snd : X ⨯ I ⟶ I)
  exact asIso prod.snd

@[simp]
/-
**CategoryTheory.Limits.mulIsInitial_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：mulIsInitial_inv (X : C) [HasBinaryProduct X I] (hI : IsInitial I) : (mulI
sInitial X hI).inv = hI.to _
参数：X : C；hI : IsInitial I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
theorem mulIsInitial_inv (X : C) [HasBinaryProduct X I] (hI : IsInitial I) :
    (mulIsInitial X hI).inv = hI.to _ :=
  hI.hom_ext _ _

/-- If `I` is initial, then `I ⨯ X` is isomorphic to it. -/
@[simps! hom]
/-
**CategoryTheory.Limits.isInitialMul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：isInitialMul (X : C) [HasBinaryProduct I X] (hI : IsInitial I) : I ⨯ X ≅ I
参数：X : C；hI : IsInitial I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` is initial, then `I ⨯ X` is isomorphic to it.
-/
noncomputable def isInitialMul (X : C) [HasBinaryProduct I X] (hI : IsInitial I) : I ⨯ X ≅ I := by
  have := hI.isIso_to (prod.fst : I ⨯ X ⟶ I)
  exact asIso prod.fst

@[simp]
/-
**CategoryTheory.Limits.isInitialMul_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isInitialMul_inv (X : C) [HasBinaryProduct I X] (hI : IsInitial I) : (isIn
itialMul X hI).inv = hI.to _
参数：X : C；hI : IsInitial I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
theorem isInitialMul_inv (X : C) [HasBinaryProduct I X] (hI : IsInitial I) :
    (isInitialMul X hI).inv = hI.to _ :=
  hI.hom_ext _ _

variable [HasInitial C]
/-
**CategoryTheory.Limits.initial_isIso_to** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：initial_isIso_to {A : C} (f : A ⟶ ⊥_ C) : IsIso f
参数：f : A ⟶ ⊥_ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.isIso_to`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects C] {I 
: C}   (hI : CategoryTheory.Li…
-/
instance initial_isIso_to {A : C} (f : A ⟶ ⊥_ C) : IsIso f :=
  initialIsInitial.isIso_to _

@[ext]
/-
**CategoryTheory.Limits.initial.strict_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.initial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictInitialObjects C]   [inst_2 : CategoryTheory.Limits.HasInitial C]
 {A : C} (f g : A ⟶ ⊥_ C), f = g
参数：f g : A ⟶ ⊥_ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.strict_hom_ext`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects 
C] {I : C}   (hI : CategoryTheory.Li…
-/
theorem initial.strict_hom_ext {A : C} (f g : A ⟶ ⊥_ C) : f = g :=
  initialIsInitial.strict_hom_ext _ _
/-
**CategoryTheory.Limits.initial.subsingleton_to** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.initial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictInitialObjects C]   [inst_2 : CategoryTheory.Limits.HasInitial C]
 {A : C}, Subsingleton (A ⟶ ⊥_ C)
参数：A ⟶ ⊥_ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.subsingleton_to`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictInitialObjects
 C] {I : C}   (hI : CategoryTheory.Li…
-/
theorem initial.subsingleton_to {A : C} : Subsingleton (A ⟶ ⊥_ C) :=
  initialIsInitial.subsingleton_to

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `X × Empty ≃ Empty` for types (or `n * 0 = 0`).
-/
@[simps! hom]
/-
**CategoryTheory.Limits.mulInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：mulInitial (X : C) [HasBinaryProduct X (⊥_ C)] : X ⨯ ⊥_ C ≅ ⊥_ C
参数：X : C；⊥_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of `X` with an initial object in a category with strict initial obje
cts is itself
initial.
This is the generalisation of the fact that `X × Empty ≃ Empty` for types (or `n
 * 0 = 0`).
-/
noncomputable def mulInitial (X : C) [HasBinaryProduct X (⊥_ C)] : X ⨯ ⊥_ C ≅ ⊥_ C :=
  mulIsInitial _ initialIsInitial

@[simp]
/-
**CategoryTheory.Limits.mulInitial_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：mulInitial_inv (X : C) [HasBinaryProduct X (⊥_ C)] : (mulInitial X).inv = 
initial.to _
参数：X : C；⊥_ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem mulInitial_inv (X : C) [HasBinaryProduct X (⊥_ C)] : (mulInitial X).inv = initial.to _ :=
  Subsingleton.elim _ _

/-- The product of `X` with an initial object in a category with strict initial objects is itself
initial.
This is the generalisation of the fact that `Empty × X ≃ Empty` for types (or `0 * n = 0`).
-/
@[simps! hom]
/-
**CategoryTheory.Limits.initialMul** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：initialMul (X : C) [HasBinaryProduct (⊥_ C) X] : (⊥_ C) ⨯ X ≅ ⊥_ C
参数：X : C；⊥_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of `X` with an initial object in a category with strict initial obje
cts is itself
initial.
This is the generalisation of the fact that `Empty × X ≃ Empty` for types (or `0
 * n = 0`).
-/
noncomputable def initialMul (X : C) [HasBinaryProduct (⊥_ C) X] : (⊥_ C) ⨯ X ≅ ⊥_ C :=
  isInitialMul _ initialIsInitial

@[simp]
/-
**CategoryTheory.Limits.initialMul_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：initialMul_inv (X : C) [HasBinaryProduct (⊥_ C) X] : (initialMul X).inv = 
initial.to _
参数：X : C；⊥_ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem initialMul_inv (X : C) [HasBinaryProduct (⊥_ C) X] : (initialMul X).inv = initial.to _ :=
  Subsingleton.elim _ _

end

/-- If `C` has an initial object such that every morphism *to* it is an isomorphism, then `C`
has strict initial objects. -/
/-
**CategoryTheory.Limits.hasStrictInitialObjects_of_initial_is_strict** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasStrictInitialObjects_of_initial_is_strict [HasInitial C] (h : forall (A
) (f : A ⟶ ⊥_ C), IsIso f) : HasStrictInitialObjects C
参数：h : forall (A) (f : A ⟶ ⊥_ C), IsIso f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g

--- 原说明 ---
If `C` has an initial object such that every morphism *to* it is an isomorphism,
 then `C`
has strict initial objects.
-/
theorem hasStrictInitialObjects_of_initial_is_strict [HasInitial C]
    (h : ∀ (A) (f : A ⟶ ⊥_ C), IsIso f) : HasStrictInitialObjects C :=
  { out := fun {I A} f hI =>
      haveI := h A (f ≫ hI.to _)
      ⟨⟨hI.to _ ≫ inv (f ≫ hI.to (⊥_ C)), by rw [← assoc, IsIso.hom_inv_id], hI.hom_ext _ _⟩⟩ }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Quiver.IsThin C] : HasStrictInitialObjects C where
  out {I A} f hI := by
    rw [isIso_iff_of_thin]
    exact ⟨hI.to _⟩

end StrictInitial

section StrictTerminal

/-- We say `C` has strict terminal objects if every terminal object is strict, i.e. given any
morphism `f : I ⟶ A` where `I` is terminal, then `f` is an isomorphism.

Strictly speaking, this says that *any* terminal object must be strict, rather than that strict
terminal objects exist.
-/
/-
**CategoryTheory.Limits.HasStrictTerminalObjects** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say `C` has strict terminal objects if every terminal object is strict, i.e. 
given any
morphism `f : I ⟶ A` where `I` is terminal, then `f` is an isomorphism.

Strictly speaking, this says that *any* terminal object must be strict, rather t
han that strict
terminal objects exist.
-/
class HasStrictTerminalObjects : Prop where
  out : ∀ {I A : C} (f : I ⟶ A), IsTerminal I → IsIso f

variable {C}

section

variable [HasStrictTerminalObjects C] {I : C}

/-
**CategoryTheory.Limits.IsTerminal.isIso_from** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictTerminalObjects C] {I : C}   (hI : CategoryTheory.Limits.IsTermin
al I) {A : C} (f : I ⟶ A), CategoryTheory.IsIso f
参数：hI : CategoryTheory.Limits.IsTerminal I；f : I ⟶ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasStrictTerminalObjects.out`：∀ {C : Type u} {inst
 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasStrictTerm
inalObjects C]   {I A : C} (f : I ⟶ A) (…
-/
theorem IsTerminal.isIso_from (hI : IsTerminal I) {A : C} (f : I ⟶ A) : IsIso f :=
  HasStrictTerminalObjects.out f hI
/-
**CategoryTheory.Limits.IsTerminal.strict_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictTerminalObjects C] {I : C}   (hI : CategoryTheory.Limits.IsTermin
al I) {A : C} (f g : I ⟶ A), f = g
参数：hI : CategoryTheory.Limits.IsTerminal I；f g : I ⟶ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isIso_from`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictTerminalObjects C]
 {I : C}   (hI : CategoryTheory.L…
· 使用定理 `CategoryTheory.eq_of_inv_eq_inv`：eq_of_inv_eq_inv {f g : X ⟶ Y} [IsIso f
] [IsIso g] (p : inv f = inv g) : f = g
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
theorem IsTerminal.strict_hom_ext (hI : IsTerminal I) {A : C} (f g : I ⟶ A) : f = g := by
  have := hI.isIso_from f
  have := hI.isIso_from g
  exact eq_of_inv_eq_inv (hI.hom_ext (inv f) (inv g))

/-- If `X ⟶ Y` with `Y` being a strict terminal object, then `X` is also a terminal object. -/
noncomputable
/-
**CategoryTheory.Limits.IsTerminal.ofStrict** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.IsTerminal`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasStrictTerminalObjects C] →       {X Y : C} → (X ⟶ Y) → Category
Theory.Limits.IsTerminal X → CategoryTheory.Limits.IsTerminal Y
参数：X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isIso_from`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictTerminalObjects C]
 {I : C}   (hI : CategoryTheory.L…
-/
def IsTerminal.ofStrict {X Y : C} (f : X ⟶ Y)
    (hY : IsTerminal X) : IsTerminal Y :=
  letI := hY.isIso_from f
  hY.ofIso (asIso f)
/-
**CategoryTheory.Limits.IsTerminal.subsingleton_to** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictTerminalObjects C] {I : C}   (hI : CategoryTheory.Limits.IsTermin
al I) {A : C}, Subsingleton (I ⟶ A)
参数：hI : CategoryTheory.Limits.IsTerminal I；I ⟶ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.strict_hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictTerminalObject
s C] {I : C}   (hI : CategoryTheory.L…
-/
theorem IsTerminal.subsingleton_to (hI : IsTerminal I) {A : C} : Subsingleton (I ⟶ A) :=
  ⟨hI.strict_hom_ext⟩

variable {J : Type v} [SmallCategory J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If all but one object in a diagram is strict terminal, then the limit is isomorphic to the
said object via `limit.π`. -/
/-
**CategoryTheory.Limits.limit_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all but one object in a diagram is strict terminal, then the limit is isomorp
hic to the
said object via `limit.π`.
-/
theorem limit_π_isIso_of_is_strict_terminal (F : J ⥤ C) [HasLimit F] (i : J)
    (H : ∀ (j) (_ : j ≠ i), IsTerminal (F.obj j)) [Subsingleton (i ⟶ i)] : IsIso (limit.π F i) := by
  classical
    refine ⟨⟨limit.lift _ ⟨_, ⟨?_, ?_⟩⟩, ?_, ?_⟩⟩
    · exact fun j =>
        dite (j = i)
          (fun h => eqToHom (by cases h; rfl))
          fun h => (H _ h).from _
    · intro j k f
      split_ifs with h h_1 h_1
      · cases h
        cases h_1
        obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
        simp
      · cases h
        have : IsIso (F.map f) := (H _ h_1).isIso_from _
        rw [← IsIso.comp_inv_eq]
        apply (H _ h_1).hom_ext
      · cases h_1
        apply (H _ h).hom_ext
      · apply (H _ h).hom_ext
    · ext
      rw [assoc, limit.lift_π]
      dsimp only
      split_ifs with h
      · cases h
        rw [id_comp, eqToHom_refl]
        exact comp_id _
      · apply (H _ h).hom_ext
    · simp

variable [HasTerminal C]
/-
**CategoryTheory.Limits.terminal_isIso_from** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：terminal_isIso_from {A : C} (f : ⊤_ C ⟶ A) : IsIso f
参数：f : ⊤_ C ⟶ A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isIso_from`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictTerminalObjects C]
 {I : C}   (hI : CategoryTheory.L…
-/
instance terminal_isIso_from {A : C} (f : ⊤_ C ⟶ A) : IsIso f :=
  terminalIsTerminal.isIso_from _

@[ext]
/-
**CategoryTheory.Limits.terminal.strict_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.terminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictTerminalObjects C]   [inst_2 : CategoryTheory.Limits.HasTerminal 
C] {A : C} (f g : ⊤_ C ⟶ A), f = g
参数：f g : ⊤_ C ⟶ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.strict_hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictTerminalObject
s C] {I : C}   (hI : CategoryTheory.L…
-/
theorem terminal.strict_hom_ext {A : C} (f g : ⊤_ C ⟶ A) : f = g :=
  terminalIsTerminal.strict_hom_ext _ _
/-
**CategoryTheory.Limits.terminal.subsingleton_to** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.terminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasStrictTerminalObjects C]   [inst_2 : CategoryTheory.Limits.HasTerminal 
C] {A : C}, Subsingleton (⊤_ C ⟶ A)
参数：⊤_ C ⟶ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.subsingleton_to`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasStrictTerminalObjec
ts C] {I : C}   (hI : CategoryTheory.L…
-/
theorem terminal.subsingleton_to {A : C} : Subsingleton (⊤_ C ⟶ A) :=
  terminalIsTerminal.subsingleton_to

end

/-- If `C` has an object such that every morphism *from* it is an isomorphism, then `C`
has strict terminal objects. -/
/-
**CategoryTheory.Limits.hasStrictTerminalObjects_of_terminal_is_strict** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasStrictTerminalObjects_of_terminal_is_strict (I : C) (h : forall (A) (f 
: I ⟶ A), IsIso f) : HasStrictTerminalObjects C
参数：I : C；h : forall (A) (f : I ⟶ A), IsIso f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y

--- 原说明 ---
If `C` has an object such that every morphism *from* it is an isomorphism, then 
`C`
has strict terminal objects.
-/
theorem hasStrictTerminalObjects_of_terminal_is_strict (I : C) (h : ∀ (A) (f : I ⟶ A), IsIso f) :
    HasStrictTerminalObjects C :=
  { out := fun {I' A} f hI' =>
      haveI := h A (hI'.from _ ≫ f)
      ⟨⟨inv (hI'.from I ≫ f) ≫ hI'.from I, hI'.hom_ext _ _, by rw [assoc, IsIso.inv_hom_id]⟩⟩ }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Quiver.IsThin C] : HasStrictTerminalObjects C where
  out {I A} f hI := by
    rw [CategoryTheory.isIso_iff_of_thin]
    exact ⟨hI.from _⟩

end StrictTerminal

end Limits

end CategoryTheory

