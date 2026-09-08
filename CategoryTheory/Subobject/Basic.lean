/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Skeleton
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Subobjects

We define `Subobject X` as the quotient (by isomorphisms) of
`MonoOver X := {f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.

There is a coercion from `Subobject X` back to the ambient category `C`
(using choice to pick a representative), and for `P : Subobject X`,
`P.arrow : (P : C) ⟶ X` is the inclusion morphism.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : Subobject Y ⥤ Subobject X`
* `def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y`
* `def «exists_» [HasImages C] (f : X ⟶ Y) : Subobject X ⥤ Subobject Y`

and prove their basic properties and relationships.
These are all easy consequences of the earlier development
of the corresponding functors for `MonoOver`.

The subobjects of `X` form a preorder making them into a category. We have `X ≤ Y` if and only if
`X.arrow` factors through `Y.arrow`: see `ofLE`/`ofLEMk`/`ofMkLE`/`ofMkLEMk` and
`le_of_comm`. Similarly, to show that two subobjects are equal, we can supply an isomorphism between
the underlying objects that commutes with the arrows (`eq_of_comm`).

See also

* `CategoryTheory.Subobject.factorThru` :
  an API describing factorization of morphisms through subobjects.
* `CategoryTheory.Subobject.lattice` :
  the lattice structures on subobjects.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

### Implementation note

Currently we describe `pullback`, `map`, etc., as functors.
It may be better to just say that they are monotone functions,
and even avoid using categorical language entirely when describing `Subobject X`.
(It's worth keeping this in mind in future use; it should be a relatively easy change here
if it looks preferable.)

### Relation to pseudoelements

There is a separate development of pseudoelements in `CategoryTheory.Abelian.Pseudoelements`,
as a quotient (but not by isomorphism) of `Over X`.

When a morphism `f` has an image, the image represents the same pseudoelement.
In a category with images `Pseudoelements X` could be constructed as a quotient of `MonoOver X`.
In fact, in an abelian category (I'm not sure in what generality beyond that),
`Pseudoelements X` agrees with `Subobject X`, but we haven't developed this in mathlib yet.

-/

@[expose] public section


universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

/-!
We now construct the subobject lattice for `X : C`,
as the quotient by isomorphisms of `MonoOver X`.

Since `MonoOver X` is a thin category, we use `ThinSkeleton` to take the quotient.

Essentially all the structure defined above on `MonoOver X` descends to `Subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/


/-- The category of subobjects of `X : C`, defined as isomorphism classes of monomorphisms into `X`.
-/
@[implicit_reducible]
/-
**CategoryTheory.Subobject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Subobject (X : C)
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of subobjects of `X : C`, defined as isomorphism classes of monomor
phisms into `X`.
-/
def Subobject (X : C) :=
  ThinSkeleton (MonoOver X)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : PartialOrder (Subobject X) :=
  inferInstanceAs <| PartialOrder (ThinSkeleton (MonoOver X))

namespace Subobject

/-
**CategoryTheory.Subobject.skeletal** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：skeletal (X : C) : Skeletal (Subobject X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ThinSkeleton.skeletal`：skeletal : Skeletal (ThinSkeleton 
C)
-/
lemma skeletal (X : C) : Skeletal (Subobject X) := ThinSkeleton.skeletal

/-- Convenience constructor for a subobject. -/
@[implicit_reducible]
/-
**CategoryTheory.Subobject.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobjec
t`。
形式化陈述：mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X
参数：f : A ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience constructor for a subobject.
-/
def mk {X A : C} (f : A ⟶ X) [Mono f] : Subobject X :=
  (toThinSkeleton _).obj (MonoOver.mk f)

section

attribute [local ext] CategoryTheory.Comma

/-
**CategoryTheory.Subobject.ind** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Subobje
ct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (p : C
ategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ (f : A ⟶ X) [inst_1 : CategoryTh
eory.Mono f], p (CategoryTheory.Subobject.mk f)) →     ∀ (P : CategoryTheory.Sub
object X), p P
参数：p : CategoryTheory.Subobject X → Prop；∀ ⦃A : C⦄ (f : A ⟶ X) [inst_1 : Categor
yTheory.Mono f], p (CategoryTheory.Subobject.mk f)；P : CategoryTheory.Subobject 
X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
protected theorem ind {X : C} (p : Subobject X → Prop)
    (h : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], p (Subobject.mk f)) (P : Subobject X) : p P := by
  induction P using Quotient.inductionOn' with | _ a
  exact h a.arrow
/-
**CategoryTheory.Subobject.ind** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Subobje
ct`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (p : C
ategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ (f : A ⟶ X) [inst_1 : CategoryTh
eory.Mono f], p (CategoryTheory.Subobject.mk f)) →     ∀ (P : CategoryTheory.Sub
object X), p P
参数：p : CategoryTheory.Subobject X → Prop；∀ ⦃A : C⦄ (f : A ⟶ X) [inst_1 : Categor
yTheory.Mono f], p (CategoryTheory.Subobject.mk f)；P : CategoryTheory.Subobject 
X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
protected theorem ind₂ {X : C} (p : Subobject X → Subobject X → Prop)
    (h : ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g],
      p (Subobject.mk f) (Subobject.mk g))
    (P Q : Subobject X) : p P Q := by
  induction P, Q using Quotient.inductionOn₂' with | _ a b
  exact h a.arrow b.arrow

end

/-- Declare a function on subobjects of `X` by specifying a function on monomorphisms with
codomain `X`. -/
/-
**CategoryTheory.Subobject.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobj
ect`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {α : S
ort u_1} →       {X : C} →         (F : ⦃A : C⦄ → (f : A ⟶ X) → [CategoryTheory.
Mono f] → α) →           (∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [inst_1 : Category
Theory.Mono f] [inst_2 : CategoryTheory.Mono g]               (i : A ≅ B), Categ
oryTheory.CategoryStruct.comp i.hom g = f → F f = F g) →             CategoryThe
ory.Subobject X → α
参数：F : ⦃A : C⦄ → (f : A ⟶ X) → [CategoryTheory.Mono f] → α；∀ ⦃A B : C⦄ (f : A ⟶ 
X) (g : B ⟶ X) [inst_1 : CategoryTheory.Mono f] [inst_2 : CategoryTheory.Mono g]
               (i : A ≅ B), CategoryTheory.CategoryStruct.comp i.hom g = f → F f
 = F g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Declare a function on subobjects of `X` by specifying a function on monomorphism
s with
codomain `X`.
-/
protected def lift {α : Sort*} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α)
    (h :
      ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] (i : A ≅ B),
        i.hom ≫ g = f → F f = F g) :
    Subobject X → α := fun P =>
  Quotient.liftOn' P (fun m => F m.arrow) fun m n ⟨i⟩ =>
    h m.arrow n.arrow ((MonoOver.forget X ⋙ Over.forget X).mapIso i) (Over.w i.hom.hom)

@[simp]
/-
**CategoryTheory.Subobject.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Sort u_1}
 {X : C}   (F : ⦃A : C⦄ → (f : A ⟶ X) → [CategoryTheory.Mono f] → α)   {h :     
∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [inst_1 : CategoryTheory.Mono f] [inst_2 : C
ategoryTheory.Mono g] (i : A ≅ B),       CategoryTheory.CategoryStruct.comp i.ho
m g = f → F f = F g}   {A : C} (f : A ⟶ X) [inst_1 : CategoryTheory.Mono f],   C
ategoryTheory.Subobject.lift F h (CategoryTheory.Subobject.mk f) = F f
参数：F : ⦃A : C⦄ → (f : A ⟶ X) → [CategoryTheory.Mono f] → α；f : A ⟶ X；g : B ⟶ X；i
 : A ≅ B；f : A ⟶ X；CategoryTheory.Subobject.mk f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem lift_mk {α : Sort*} {X : C} (F : ∀ ⦃A : C⦄ (f : A ⟶ X) [Mono f], α) {h A}
    (f : A ⟶ X) [Mono f] : Subobject.lift F h (Subobject.mk f) = F f :=
  rfl

/-- The category of subobjects is equivalent to the `MonoOver` category. It is more convenient to
use the former due to the partial order instance, but oftentimes it is easier to define structures
on the latter. -/
/-
**CategoryTheory.Subobject.equivMonoOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：equivMonoOver (X : C) : Subobject X ≌ MonoOver X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of subobjects is equivalent to the `MonoOver` category. It is more 
convenient to
use the former due to the partial order instance, but oftentimes it is easier to
 define structures
on the latter.
-/
noncomputable def equivMonoOver (X : C) : Subobject X ≌ MonoOver X :=
  ThinSkeleton.equivalence _

/-- Use choice to pick a representative `MonoOver X` for each `Subobject X`.
-/
/-
**CategoryTheory.Subobject.representative** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：representative {X : C} : Subobject X ⥤ MonoOver X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use choice to pick a representative `MonoOver X` for each `Subobject X`.
-/
noncomputable def representative {X : C} : Subobject X ⥤ MonoOver X :=
  (equivMonoOver X).functor
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (representative (X := X)).IsEquivalence :=
  (equivMonoOver X).isEquivalence_functor

/-- Starting with `A : MonoOver X`, we can take its equivalence class in `Subobject X`
then pick an arbitrary representative using `representative.obj`.
This is isomorphic (in `MonoOver X`) to the original `A`.
-/
/-
**CategoryTheory.Subobject.representativeIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：representativeIso {X : C} (A : MonoOver X) : representative.obj ((toThinSk
eleton _).obj A) ≅ A
参数：A : MonoOver X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Starting with `A : MonoOver X`, we can take its equivalence class in `Subobject 
X`
then pick an arbitrary representative using `representative.obj`.
This is isomorphic (in `MonoOver X`) to the original `A`.
-/
noncomputable def representativeIso {X : C} (A : MonoOver X) :
    representative.obj ((toThinSkeleton _).obj A) ≅ A :=
  (equivMonoOver X).counitIso.app A

@[simp]
/-
**CategoryTheory.Subobject.thinSkeleton_mk_representative_eq_self** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Subobject`。
形式化陈述：thinSkeleton_mk_representative_eq_self {X : C} (A : Subobject X) : ThinSke
leton.mk (representative.obj A) = A
参数：A : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subobject.skeletal`：skeletal (X : C) : Skeletal (Subobjec
t X)
-/
lemma thinSkeleton_mk_representative_eq_self {X : C} (A : Subobject X) :
    ThinSkeleton.mk (representative.obj A) = A :=
  Subobject.skeletal _ ⟨((equivMonoOver X).unitIso.app _).symm⟩

/-- Use choice to pick a representative underlying object in `C` for any `Subobject X`.

Prefer to use the coercion `P : C` rather than explicitly writing `underlying.obj P`.
-/
/-
**CategoryTheory.Subobject.underlying** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：underlying {X : C} : Subobject X ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use choice to pick a representative underlying object in `C` for any `Subobject 
X`.

Prefer to use the coercion `P : C` rather than explicitly writing `underlying.ob
j P`.
-/
noncomputable def underlying {X : C} : Subobject X ⥤ C :=
  representative ⋙ MonoOver.forget _ ⋙ Over.forget _
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (Subobject X) C where coe Y := underlying.obj Y

/-- If we construct a `Subobject Y` from an explicit `f : X ⟶ Y` with `[Mono f]`,
then pick an arbitrary choice of underlying object `(Subobject.mk f : C)` back in `C`,
it is isomorphic (in `C`) to the original `X`.
-/
/-
**CategoryTheory.Subobject.underlyingIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：underlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] : (Subobject.mk f : C) ≅ X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we construct a `Subobject Y` from an explicit `f : X ⟶ Y` with `[Mono f]`,
then pick an arbitrary choice of underlying object `(Subobject.mk f : C)` back i
n `C`,
it is isomorphic (in `C`) to the original `X`.
-/
noncomputable def underlyingIso {X Y : C} (f : X ⟶ Y) [Mono f] : (Subobject.mk f : C) ≅ X :=
  (MonoOver.forget _ ⋙ Over.forget _).mapIso (representativeIso (MonoOver.mk f))

/-- The morphism in `C` from the arbitrarily chosen underlying object to the ambient object.
-/
/-
**CategoryTheory.Subobject.arrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subob
ject`。
形式化陈述：arrow {X : C} (Y : Subobject X) : (Y : C) ⟶ X
参数：Y : Subobject X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in `C` from the arbitrarily chosen underlying object to the ambient
 object.
-/
noncomputable def arrow {X : C} (Y : Subobject X) : (Y : C) ⟶ X :=
  (representative.obj Y).obj.hom
/-
**CategoryTheory.Subobject.arrow_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：arrow_mono {X : C} (Y : Subobject X) : Mono Y.arrow
参数：Y : Subobject X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
instance arrow_mono {X : C} (Y : Subobject X) : Mono Y.arrow :=
  (representative.obj Y).property

@[simp]
/-
**CategoryTheory.Subobject.arrow_congr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：arrow_congr {A : C} (X Y : Subobject A) (h : X = Y) : eqToHom (congr_arg (
fun X : Subobject A => (X : C)) h) ≫ Y.arrow = X.arrow
参数：X Y : Subobject A；h : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arrow_congr {A : C} (X Y : Subobject A) (h : X = Y) :
    eqToHom (congr_arg (fun X : Subobject A => (X : C)) h) ≫ Y.arrow = X.arrow := by
  induction h
  simp

@[simp]
/-
**CategoryTheory.Subobject.representative_coe** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：representative_coe (Y : Subobject X) : (representative.obj Y : C) = (Y : C
)
参数：Y : Subobject X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem representative_coe (Y : Subobject X) : (representative.obj Y : C) = (Y : C) :=
  rfl

@[simp]
/-
**CategoryTheory.Subobject.representative_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subobject`。
形式化陈述：representative_arrow (Y : Subobject X) : (representative.obj Y).arrow = Y.
arrow
参数：Y : Subobject X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem representative_arrow (Y : Subobject X) : (representative.obj Y).arrow = Y.arrow :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.underlying_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：underlying_arrow {X : C} {Y Z : Subobject X} (f : Y ⟶ Z) : underlying.map 
f ≫ arrow Z = arrow Y
参数：f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
theorem underlying_arrow {X : C} {Y Z : Subobject X} (f : Y ⟶ Z) :
    underlying.map f ≫ arrow Z = arrow Y :=
  Over.w (representative.map f).hom

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**CategoryTheory.Subobject.underlyingIso_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subobject`。
形式化陈述：underlyingIso_arrow {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv
 ≫ (Subobject.mk f).arrow = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
-/
theorem underlyingIso_arrow {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f :=
  Over.w _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Subobject`。
形式化陈述：underlyingIso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingI
so f).hom ≫ f = (mk f).arrow
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
-/
theorem underlyingIso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    (underlyingIso f).hom ≫ f = (mk f).arrow :=
  (Iso.eq_inv_comp _).1 (underlyingIso_arrow f).symm

/-- Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal -/
@[ext]
/-
**CategoryTheory.Subobject.eq_of_comp_arrow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Subobject`。
形式化陈述：eq_of_comp_arrow_eq {X Y : C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.a
rrow = g ≫ P.arrow) : f = g
参数：h : f ≫ P.arrow = g ≫ P.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…

--- 原说明 ---
Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal
-/
theorem eq_of_comp_arrow_eq {X Y : C} {P : Subobject Y} {f g : X ⟶ P}
    (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
  (cancel_mono P.arrow).mp h
/-
**CategoryTheory.Subobject.mk_le_mk_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono
 f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) : mk f₁ <= mk f₂
参数：g : A₁ ⟶ A₂；w : g ≫ f₂ = f₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂)
    (w : g ≫ f₂ = f₁) : mk f₁ ≤ mk f₂ :=
  ⟨MonoOver.homMk _ w⟩

@[simp]
/-
**CategoryTheory.Subobject.mk_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：mk_arrow (P : Subobject X) : mk P.arrow = P
参数：P : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.mk_out'`：mk_out' (a : α) : s₁ (Quotient.mk'' a : Quotient s₁).o
ut a
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_arrow (P : Subobject X) : mk P.arrow = P :=
  Quotient.inductionOn' P fun Q => by
    obtain ⟨e⟩ := @Quotient.mk_out' _ (isIsomorphicSetoid _) Q
    exact Quotient.sound' ⟨MonoOver.isoMk (Iso.refl _) ≪≫ e⟩
/-
**CategoryTheory.Subobject.le_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：le_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.
arrow = X.arrow) : X <= Y
参数：f : (X : C) ⟶ (Y : C)；w : f ≫ Y.arrow = X.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.mk_arrow`：mk_arrow (P : Subobject X) : mk P.arr
ow = P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
-/
theorem le_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) :
    X ≤ Y := by
  convert! mk_le_mk_of_comm _ w <;> simp
/-
**CategoryTheory.Subobject.le_mk_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：le_mk_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C
) ⟶ A) (w : g ≫ f = X.arrow) : X <= mk f
参数：g : (X : C) ⟶ A；w : g ≫ f = X.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_mk_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : (X : C) ⟶ A)
    (w : g ≫ f = X.arrow) : X ≤ mk f :=
  le_of_comm (g ≫ (underlyingIso f).inv) <| by simp [w]
/-
**CategoryTheory.Subobject.mk_le_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：mk_le_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X
 : C)) (w : g ≫ X.arrow = f) : mk f <= X
参数：g : A ⟶ (X : C)；w : g ≫ X.arrow = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_le_of_comm {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (g : A ⟶ (X : C))
    (w : g ≫ X.arrow = f) : mk f ≤ X :=
  le_of_comm ((underlyingIso f).hom ≫ g) <| by simp [w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
the arrows. -/
@[ext (iff := false)]
/-
**CategoryTheory.Subobject.eq_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：eq_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C)) (w : f.hom 
≫ Y.arrow = X.arrow) : X = Y
参数：f : (X : C) ≅ (Y : C)；w : f.hom ≫ Y.arrow = X.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Subobject.le_of_comm`：le_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) : X <= Y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
To show that two subobjects are equal, it suffices to exhibit an isomorphism com
muting with
the arrows.
-/
theorem eq_of_comm {B : C} {X Y : Subobject B} (f : (X : C) ≅ (Y : C))
    (w : f.hom ≫ Y.arrow = X.arrow) : X = Y :=
  le_antisymm (le_of_comm f.hom w) <| le_of_comm f.inv <| f.inv_comp_eq.2 w.symm

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
the arrows. -/
/-
**CategoryTheory.Subobject.eq_mk_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：eq_mk_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C
) ≅ A) (w : i.hom ≫ f = X.arrow) : X = mk f
参数：f : A ⟶ B；i : (X : C) ≅ A；w : i.hom ≫ f = X.arrow。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comm`：eq_of_comm {B : C} {X Y : Subobject
 B} (f : (X : C) ≅ (Y : C)) (w : f.hom ≫ Y.arrow = X.arrow) : X = Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
To show that two subobjects are equal, it suffices to exhibit an isomorphism com
muting with
the arrows.
-/
theorem eq_mk_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A)
    (w : i.hom ≫ f = X.arrow) : X = mk f :=
  eq_of_comm (i.trans (underlyingIso f).symm) <| by simp [w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
the arrows. -/
/-
**CategoryTheory.Subobject.mk_eq_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：mk_eq_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X
 : C)) (w : i.hom ≫ X.arrow = f) : mk f = X
参数：f : A ⟶ B；i : A ≅ (X : C)；w : i.hom ≫ X.arrow = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subobject.eq_mk_of_comm`：eq_mk_of_comm {B A : C} {X : Sub
object B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A) (w : i.hom ≫ f = X.arrow) : X =
 mk f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g

--- 原说明 ---
To show that two subobjects are equal, it suffices to exhibit an isomorphism com
muting with
the arrows.
-/
theorem mk_eq_of_comm {B A : C} {X : Subobject B} (f : A ⟶ B) [Mono f] (i : A ≅ (X : C))
    (w : i.hom ≫ X.arrow = f) : mk f = X :=
  Eq.symm <| eq_mk_of_comm _ i.symm <| by rw [Iso.symm_hom, Iso.inv_comp_eq, w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
the arrows. -/
/-
**CategoryTheory.Subobject.mk_eq_mk_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g]
 (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) : mk f = mk g
参数：f : A₁ ⟶ B；g : A₂ ⟶ B；i : A₁ ≅ A₂；w : i.hom ≫ g = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_mk_of_comm`：eq_mk_of_comm {B A : C} {X : Sub
object B} (f : A ⟶ B) [Mono f] (i : (X : C) ≅ A) (w : i.hom ≫ f = X.arrow) : X =
 mk f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
To show that two subobjects are equal, it suffices to exhibit an isomorphism com
muting with
the arrows.
-/
theorem mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂)
    (w : i.hom ≫ g = f) : mk f = mk g :=
  eq_mk_of_comm _ ((underlyingIso f).trans i) <| by simp [w]
/-
**CategoryTheory.Subobject.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：mk_surjective {X : C} (S : Subobject X) : exists (A : C) (i : A ⟶ X) (_ : 
Mono i), S = Subobject.mk i
参数：S : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.mk_arrow`：mk_arrow (P : Subobject X) : mk P.arr
ow = P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk_surjective {X : C} (S : Subobject X) :
    ∃ (A : C) (i : A ⟶ X) (_ : Mono i), S = Subobject.mk i :=
  ⟨_, S.arrow, inferInstance, by simp⟩

-- We make `X` and `Y` explicit arguments here so that when `ofLE` appears in goal statements
-- it is possible to see its source and target
-- (`h` will just display as `_`, because it is in `Prop`).
/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
/-
**CategoryTheory.Subobject.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobj
ect`。
形式化陈述：ofLE {B : C} (X Y : Subobject B) (h : X <= Y) : (X : C) ⟶ (Y : C)
参数：X Y : Subobject B；h : X <= Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inequality of subobjects is witnessed by some morphism between the correspond
ing objects.
-/
def ofLE {B : C} (X Y : Subobject B) (h : X ≤ Y) : (X : C) ⟶ (Y : C) :=
  underlying.map <| h.hom

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofLE_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：ofLE_arrow {B : C} {X Y : Subobject B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow
 = X.arrow
参数：h : X <= Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.underlying_arrow`：underlying_arrow {X : C} {Y Z
 : Subobject X} (f : Y ⟶ Z) : underlying.map f ≫ arrow Z = arrow Y
-/
theorem ofLE_arrow {B : C} {X Y : Subobject B} (h : X ≤ Y) : ofLE X Y h ≫ Y.arrow = X.arrow :=
  underlying_arrow _
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : C} (X Y : Subobject B) (h : X ≤ Y) : Mono (ofLE X Y h) := by
  fconstructor
  intro Z f g w
  replace w := w =≫ Y.arrow
  ext
  simpa using w
/-
**CategoryTheory.Subobject.ofLE_mk_le_mk_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subobject`。
形式化陈述：ofLE_mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] 
[Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) : ofLE _ _ (mk_le_mk_of_comm g w) = (u
nderlyingIso _).hom ≫ g ≫ (underlyingIso _).inv
参数：g : A₁ ⟶ A₂；w : g ≫ f₂ = f₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLE_mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂]
    (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) :
    ofLE _ _ (mk_le_mk_of_comm g w) = (underlyingIso _).hom ≫ g ≫ (underlyingIso _).inv := by
  ext
  simp [w]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
/-
**CategoryTheory.Subobject.ofLEMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subo
bject`。
形式化陈述：ofLEMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X <= mk f) : 
(X : C) ⟶ A
参数：X : Subobject B；f : A ⟶ B；h : X <= mk f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inequality of subobjects is witnessed by some morphism between the correspond
ing objects.
-/
def ofLEMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) : (X : C) ⟶ A :=
  ofLE X (mk f) h ≫ (underlyingIso f).hom
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X ≤ mk f) :
    Mono (ofLEMk X f h) := by
  dsimp only [ofLEMk]
  infer_instance

@[simp]
/-
**CategoryTheory.Subobject.ofLEMk_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：ofLEMk_comp {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X <= mk 
f) : ofLEMk X f h ≫ f = X.arrow
参数：h : X <= mk f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLEMk_comp {B A : C} {X : Subobject B} {f : A ⟶ B} [Mono f] (h : X ≤ mk f) :
    ofLEMk X f h ≫ f = X.arrow := by simp [ofLEMk]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
/-
**CategoryTheory.Subobject.ofMkLE** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subo
bject`。
形式化陈述：ofMkLE {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f <= X) : 
A ⟶ (X : C)
参数：f : A ⟶ B；X : Subobject B；h : mk f <= X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inequality of subobjects is witnessed by some morphism between the correspond
ing objects.
-/
def ofMkLE {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) : A ⟶ (X : C) :=
  (underlyingIso f).inv ≫ ofLE (mk f) X h
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f ≤ X) :
    Mono (ofMkLE f X h) := by
  dsimp only [ofMkLE]
  infer_instance

@[simp]
/-
**CategoryTheory.Subobject.ofMkLE_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：ofMkLE_arrow {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f <=
 X) : ofMkLE f X h ≫ X.arrow = f
参数：h : mk f <= X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofMkLE_arrow {B A : C} {f : A ⟶ B} [Mono f] {X : Subobject B} (h : mk f ≤ X) :
    ofMkLE f X h ≫ X.arrow = f := by simp [ofMkLE]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
/-
**CategoryTheory.Subobject.ofMkLEMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：ofMkLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk
 f <= mk g) : A₁ ⟶ A₂
参数：f : A₁ ⟶ B；g : A₂ ⟶ B；h : mk f <= mk g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inequality of subobjects is witnessed by some morphism between the correspond
ing objects.
-/
def ofMkLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    A₁ ⟶ A₂ :=
  (underlyingIso f).inv ≫ ofLE (mk f) (mk g) h ≫ (underlyingIso g).hom
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f ≤ mk g) :
    Mono (ofMkLEMk f g h) := by
  dsimp only [ofMkLEMk]
  infer_instance

@[simp]
/-
**CategoryTheory.Subobject.ofMkLEMk_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：ofMkLEMk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h
 : mk f <= mk g) : ofMkLEMk f g h ≫ g = f
参数：h : mk f <= mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk`：underlyingIso_hom
_comp_eq_mk {X Y : C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).hom ≫ f = (mk f).
arrow
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofMkLEMk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f ≤ mk g) :
    ofMkLEMk f g h ≫ g = f := by simp [ofMkLEMk]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofLE_comp_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：ofLE_comp_ofLE {B : C} (X Y Z : Subobject B) (h₁ : X <= Y) (h₂ : Y <= Z) :
 ofLE X Y h₁ ≫ ofLE Y Z h₂ = ofLE X Z (h₁.trans h₂)
参数：X Y Z : Subobject B；h₁ : X <= Y；h₂ : Y <= Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem ofLE_comp_ofLE {B : C} (X Y Z : Subobject B) (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    ofLE X Y h₁ ≫ ofLE Y Z h₂ = ofLE X Z (h₁.trans h₂) := by
  simp only [ofLE, ← Functor.map_comp underlying]
  congr 1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofLE_comp_ofLEMk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：ofLE_comp_ofLEMk {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : 
X <= Y) (h₂ : Y <= mk f) : ofLE X Y h₁ ≫ ofLEMk Y f h₂ = ofLEMk X f (h₁.trans h₂
)
参数：X Y : Subobject B；f : A ⟶ B；h₁ : X <= Y；h₂ : Y <= mk f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
-/
theorem ofLE_comp_ofLEMk {B A : C} (X Y : Subobject B) (f : A ⟶ B) [Mono f] (h₁ : X ≤ Y)
    (h₂ : Y ≤ mk f) : ofLE X Y h₁ ≫ ofLEMk Y f h₂ = ofLEMk X f (h₁.trans h₂) := by
  simp only [ofLEMk, ofLE, ← Functor.map_comp_assoc underlying]
  congr 1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofLEMk_comp_ofMkLE** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：ofLEMk_comp_ofMkLE {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : S
ubobject B) (h₁ : X <= mk f) (h₂ : mk f <= Y) : ofLEMk X f h₁ ≫ ofMkLE f Y h₂ = 
ofLE X Y (h₁.trans h₂)
参数：X : Subobject B；f : A ⟶ B；Y : Subobject B；h₁ : X <= mk f；h₂ : mk f <= Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem ofLEMk_comp_ofMkLE {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (Y : Subobject B)
    (h₁ : X ≤ mk f) (h₂ : mk f ≤ Y) : ofLEMk X f h₁ ≫ ofMkLE f Y h₂ = ofLE X Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ← Functor.map_comp underlying, assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofLEMk_comp_ofMkLEMk** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subobject`。
形式化陈述：ofLEMk_comp_ofMkLEMk {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f]
 (g : A₂ ⟶ B) [Mono g] (h₁ : X <= mk f) (h₂ : mk f <= mk g) : ofLEMk X f h₁ ≫ of
MkLEMk f g h₂ = ofLEMk X g (h₁.trans h₂)
参数：X : Subobject B；f : A₁ ⟶ B；g : A₂ ⟶ B；h₁ : X <= mk f；h₂ : mk f <= mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
-/
theorem ofLEMk_comp_ofMkLEMk {B A₁ A₂ : C} (X : Subobject B) (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
    [Mono g] (h₁ : X ≤ mk f) (h₂ : mk f ≤ mk g) :
    ofLEMk X f h₁ ≫ ofMkLEMk f g h₂ = ofLEMk X g (h₁.trans h₂) := by
  simp only [ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofMkLE_comp_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：ofMkLE_comp_ofLE {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ 
: mk f <= X) (h₂ : X <= Y) : ofMkLE f X h₁ ≫ ofLE X Y h₂ = ofMkLE f Y (h₁.trans 
h₂)
参数：f : A₁ ⟶ B；X Y : Subobject B；h₁ : mk f <= X；h₂ : X <= Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem ofMkLE_comp_ofLE {B A₁ : C} (f : A₁ ⟶ B) [Mono f] (X Y : Subobject B) (h₁ : mk f ≤ X)
    (h₂ : X ≤ Y) : ofMkLE f X h₁ ≫ ofLE X Y h₂ = ofMkLE f Y (h₁.trans h₂) := by
  simp only [ofMkLE, ofLE, ← Functor.map_comp underlying,
    assoc]
  congr 1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofMkLE_comp_ofLEMk** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：ofMkLE_comp_ofLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (
g : A₂ ⟶ B) [Mono g] (h₁ : mk f <= X) (h₂ : X <= mk g) : ofMkLE f X h₁ ≫ ofLEMk 
X g h₂ = ofMkLEMk f g (h₁.trans h₂)
参数：f : A₁ ⟶ B；X : Subobject B；g : A₂ ⟶ B；h₁ : mk f <= X；h₂ : X <= mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
-/
theorem ofMkLE_comp_ofLEMk {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (X : Subobject B) (g : A₂ ⟶ B)
    [Mono g] (h₁ : mk f ≤ X) (h₂ : X ≤ mk g) :
    ofMkLE f X h₁ ≫ ofLEMk X g h₂ = ofMkLEMk f g (h₁.trans h₂) := by
  simp only [ofMkLE, ofLEMk, ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc]
  congr 1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofMkLEMk_comp_ofMkLE** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Subobject`。
形式化陈述：ofMkLEMk_comp_ofMkLE {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mon
o g] (X : Subobject B) (h₁ : mk f <= mk g) (h₂ : mk g <= X) : ofMkLEMk f g h₁ ≫ 
ofMkLE g X h₂ = ofMkLE f X (h₁.trans h₂)
参数：f : A₁ ⟶ B；g : A₂ ⟶ B；X : Subobject B；h₁ : mk f <= mk g；h₂ : mk g <= X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem ofMkLEMk_comp_ofMkLE {B A₁ A₂ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (X : Subobject B) (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ X) :
    ofMkLEMk f g h₁ ≫ ofMkLE g X h₂ = ofMkLE f X (h₁.trans h₂) := by
  simp only [ofMkLE, ofLE, ofMkLEMk, ← Functor.map_comp underlying,
    assoc, Iso.hom_inv_id_assoc]
  congr 1

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subobject.ofMkLEMk_comp_ofMkLEMk** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Subobject`。
形式化陈述：ofMkLEMk_comp_ofMkLEMk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B)
 [Mono g] (h : A₃ ⟶ B) [Mono h] (h₁ : mk f <= mk g) (h₂ : mk g <= mk h) : ofMkLE
Mk f g h₁ ≫ ofMkLEMk g h h₂ = ofMkLEMk f h (h₁.trans h₂)
参数：f : A₁ ⟶ B；g : A₂ ⟶ B；h : A₃ ⟶ B；h₁ : mk f <= mk g；h₂ : mk g <= mk h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
-/
theorem ofMkLEMk_comp_ofMkLEMk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [Mono f] (g : A₂ ⟶ B) [Mono g]
    (h : A₃ ⟶ B) [Mono h] (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ mk h) :
    ofMkLEMk f g h₁ ≫ ofMkLEMk g h h₂ = ofMkLEMk f h (h₁.trans h₂) := by
  simp only [ofLE, ofMkLEMk, ← Functor.map_comp_assoc underlying, assoc,
    Iso.hom_inv_id_assoc]
  congr 1

@[simp]
/-
**CategoryTheory.Subobject.ofLE_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubobject`。
形式化陈述：ofLE_refl {B : C} (X : Subobject B) : ofLE X X le_rfl = 𝟙 _
参数：X : Subobject B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLE_refl {B : C} (X : Subobject B) : ofLE X X le_rfl = 𝟙 _ := by
  apply (cancel_mono X.arrow).mp
  simp

@[simp]
/-
**CategoryTheory.Subobject.ofMkLEMk_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：ofMkLEMk_refl {B A₁ : C} (f : A₁ ⟶ B) [Mono f] : ofMkLEMk f f le_rfl = 𝟙 _
参数：f : A₁ ⟶ B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.ofMkLEMk_comp`：ofMkLEMk_comp {B A₁ A₂ : C} {f :
 A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) : ofMkLEMk f g h ≫ g 
= f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofMkLEMk_refl {B A₁ : C} (f : A₁ ⟶ B) [Mono f] : ofMkLEMk f f le_rfl = 𝟙 _ := by
  apply (cancel_mono f).mp
  simp

-- As with `ofLE`, we have `X` and `Y` as explicit arguments for readability.
/-- An equality of subobjects gives an isomorphism of the corresponding objects.
(One could use `underlying.mapIso (eqToIso h))` here, but this is more readable.) -/
@[simps]
/-
**CategoryTheory.Subobject.isoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sub
object`。
形式化陈述：isoOfEq {B : C} (X Y : Subobject B) (h : X = Y) : (X : C) ≅ (Y : C) where 
hom
参数：X Y : Subobject B；h : X = Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equality of subobjects gives an isomorphism of the corresponding objects.
(One could use `underlying.mapIso (eqToIso h))` here, but this is more readable.
)
-/
def isoOfEq {B : C} (X Y : Subobject B) (h : X = Y) : (X : C) ≅ (Y : C) where
  hom := ofLE _ _ h.le
  inv := ofLE _ _ h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
/-
**CategoryTheory.Subobject.isoOfEqMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
ubobject`。
形式化陈述：isoOfEqMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f) 
: (X : C) ≅ A where hom
参数：X : Subobject B；f : A ⟶ B；h : X = mk f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equality of subobjects gives an isomorphism of the corresponding objects.
-/
def isoOfEqMk {B A : C} (X : Subobject B) (f : A ⟶ B) [Mono f] (h : X = mk f) : (X : C) ≅ A where
  hom := ofLEMk X f h.le
  inv := ofMkLE f X h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
/-
**CategoryTheory.Subobject.isoOfMkEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
ubobject`。
形式化陈述：isoOfMkEq {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X) 
: A ≅ (X : C) where hom
参数：f : A ⟶ B；X : Subobject B；h : mk f = X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equality of subobjects gives an isomorphism of the corresponding objects.
-/
def isoOfMkEq {B A : C} (f : A ⟶ B) [Mono f] (X : Subobject B) (h : mk f = X) : A ≅ (X : C) where
  hom := ofMkLE f X h.le
  inv := ofLEMk X f h.ge

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
/-
**CategoryTheory.Subobject.isoOfMkEqMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：isoOfMkEqMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h :
 mk f = mk g) : A₁ ≅ A₂ where hom
参数：f : A₁ ⟶ B；g : A₂ ⟶ B；h : mk f = mk g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equality of subobjects gives an isomorphism of the corresponding objects.
-/
def isoOfMkEqMk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (h : mk f = mk g) :
    A₁ ≅ A₂ where
  hom := ofMkLEMk f g h.le
  inv := ofMkLEMk g f h.ge
/-
**CategoryTheory.Subobject.mk_lt_mk_of_comm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：mk_lt_mk_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono
 i₂] (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) (hf : ¬ IsIso f) : Subobject.mk i₁ < Subo
bject.mk i₂
参数：f : A₁ ⟶ A₂；fac : f ≫ i₂ = i₁；hf : ¬ IsIso f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Subobject.isoOfMkEqMk_hom`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B)   [inst_1 
: CategoryTheory.Mono f] [inst…
· 使用定理 `CategoryTheory.Subobject.ofMkLEMk_comp`：ofMkLEMk_comp {B A₁ A₂ : C} {f :
 A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) : ofMkLEMk f g h ≫ g 
= f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma mk_lt_mk_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) (hf : ¬ IsIso f) :
    Subobject.mk i₁ < Subobject.mk i₂ := by
  obtain _ | h := (mk_le_mk_of_comm _ fac).lt_or_eq
  · assumption
  · exfalso
    apply hf
    convert! (isoOfMkEqMk i₁ i₂ h).isIso_hom
    rw [← cancel_mono i₂, isoOfMkEqMk_hom, ofMkLEMk_comp, fac]
/-
**CategoryTheory.Subobject.mk_lt_mk_iff_of_comm** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Subobject`。
形式化陈述：mk_lt_mk_iff_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [
Mono i₂] (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) : Subobject.mk i₁ < Subobject.mk i₂ ↔
 ¬ IsIso f
参数：f : A₁ ⟶ A₂；fac : f ≫ i₂ = i₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用引理 `CategoryTheory.Subobject.mk_lt_mk_of_comm`：mk_lt_mk_of_comm {X A₁ A₂ : C
} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂] (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = 
i₁) (hf : ¬ IsIso f) : Subobjec…
-/
lemma mk_lt_mk_iff_of_comm {X A₁ A₂ : C} {i₁ : A₁ ⟶ X} {i₂ : A₂ ⟶ X} [Mono i₁] [Mono i₂]
    (f : A₁ ⟶ A₂) (fac : f ≫ i₂ = i₁) :
    Subobject.mk i₁ < Subobject.mk i₂ ↔ ¬ IsIso f :=
  ⟨fun h hf ↦ by simp only [mk_eq_mk_of_comm i₁ i₂ (asIso f) fac, lt_self_iff_false] at h,
    mk_lt_mk_of_comm f fac⟩

end Subobject

namespace MonoOver

variable {P Q : MonoOver X} (f : P ⟶ Q)

include f in
/-
**CategoryTheory.MonoOver.subobjectMk_le_mk_of_hom** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MonoOver`。
形式化陈述：subobjectMk_le_mk_of_hom : Subobject.mk P.obj.hom <= Subobject.mk Q.obj.ho
m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.mk_le_mk_of_comm`：mk_le_mk_of_comm {B A₁ A₂ : C
} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [Mono f₁] [Mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁
) : mk f₁ <= mk f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma subobjectMk_le_mk_of_hom :
    Subobject.mk P.obj.hom ≤ Subobject.mk Q.obj.hom :=
  Subobject.mk_le_mk_of_comm f.hom.left (by simp)
/-
**CategoryTheory.MonoOver.isIso_hom_left_iff_subobjectMk_eq** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MonoOver`。
形式化陈述：isIso_hom_left_iff_subobjectMk_eq : IsIso f.hom.left ↔ Subobject.mk P.1.ho
m = Subobject.mk Q.1.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofMkLEMk_comp`：ofMkLEMk_comp {B A₁ A₂ : C} {f :
 A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) : ofMkLEMk f g h ≫ g 
= f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma isIso_hom_left_iff_subobjectMk_eq :
    IsIso f.hom.left ↔ Subobject.mk P.1.hom = Subobject.mk Q.1.hom :=
  ⟨fun _ ↦ Subobject.mk_eq_mk_of_comm _ _ (asIso f.hom.left) (by simp),
    fun h ↦ ⟨Subobject.ofMkLEMk _ _ h.symm.le, by simp [← cancel_mono P.1.hom],
      by simp [← cancel_mono Q.1.hom]⟩⟩
/-
**CategoryTheory.MonoOver.isIso_iff_subobjectMk_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.MonoOver`。
形式化陈述：isIso_iff_subobjectMk_eq : IsIso f ↔ Subobject.mk P.1.hom = Subobject.mk Q
.1.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MonoOver.isIso_iff_isIso_hom_left`：isIso_iff_isIso_hom_le
ft {A B : MonoOver X} (f : A ⟶ B) : IsIso f ↔ IsIso f.hom.left
· 使用引理 `CategoryTheory.MonoOver.isIso_hom_left_iff_subobjectMk_eq`：isIso_hom_lef
t_iff_subobjectMk_eq : IsIso f.hom.left ↔ Subobject.mk P.1.hom = Subobject.mk Q.
1.hom
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isIso_iff_subobjectMk_eq :
    IsIso f ↔ Subobject.mk P.1.hom = Subobject.mk Q.1.hom := by
  rw [isIso_iff_isIso_hom_left, isIso_hom_left_iff_subobjectMk_eq]

end MonoOver

open CategoryTheory.Limits

namespace Subobject

/-- Any functor `MonoOver X ⥤ MonoOver Y` descends to a functor
`Subobject X ⥤ Subobject Y`, because `MonoOver Y` is thin. -/
@[implicit_reducible]
/-
**CategoryTheory.Subobject.lower** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subob
ject`。
形式化陈述：lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y
参数：F : MonoOver X ⥤ MonoOver Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor `MonoOver X ⥤ MonoOver Y` descends to a functor
`Subobject X ⥤ Subobject Y`, because `MonoOver Y` is thin.
-/
def lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y :=
  ThinSkeleton.map F

/-- Isomorphic functors become equal when lowered to `Subobject`.
(It's not as evil as usual to talk about equality between functors
because the categories are thin and skeletal.) -/
/-
**CategoryTheory.Subobject.lower_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubobject`。
形式化陈述：lower_iso (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂) : lower F₁ = low
er F₂
参数：F₁ F₂ : MonoOver X ⥤ MonoOver Y；h : F₁ ≅ F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ThinSkeleton.map_iso_eq`：map_iso_eq {F₁ F₂ : D ⥤ C} (h : 
F₁ ≅ F₂) : map F₁ = map F₂

--- 原说明 ---
Isomorphic functors become equal when lowered to `Subobject`.
(It's not as evil as usual to talk about equality between functors
because the categories are thin and skeletal.)
-/
theorem lower_iso (F₁ F₂ : MonoOver X ⥤ MonoOver Y) (h : F₁ ≅ F₂) : lower F₁ = lower F₂ :=
  ThinSkeleton.map_iso_eq h

/-- A ternary version of `Subobject.lower`. -/
/-
**CategoryTheory.Subobject.lower** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subob
ject`。
形式化陈述：lower {Y : D} (F : MonoOver X ⥤ MonoOver Y) : Subobject X ⥤ Subobject Y
参数：F : MonoOver X ⥤ MonoOver Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ternary version of `Subobject.lower`.
-/
def lower₂ (F : MonoOver X ⥤ MonoOver Y ⥤ MonoOver Z) : Subobject X ⥤ Subobject Y ⥤ Subobject Z :=
  ThinSkeleton.map₂ F

@[simp]
/-
**CategoryTheory.Subobject.lower_comm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：lower_comm (F : MonoOver Y ⥤ MonoOver X) : toThinSkeleton _ ⋙ lower F = F 
⋙ toThinSkeleton _
参数：F : MonoOver Y ⥤ MonoOver X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lower_comm (F : MonoOver Y ⥤ MonoOver X) :
    toThinSkeleton _ ⋙ lower F = F ⋙ toThinSkeleton _ :=
  rfl

/--
Applying `lower F` and then `representative` is isomorphic to first applying `representative`
and then applying `F`.
-/
/-
**CategoryTheory.Subobject.lowerCompRepresentativeIso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Subobject`。
形式化陈述：lowerCompRepresentativeIso (F : MonoOver Y ⥤ MonoOver X) : lower F ⋙ repre
sentative ≅ representative ⋙ F
参数：F : MonoOver Y ⥤ MonoOver X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `lower F` and then `representative` is isomorphic to first applying `re
presentative`
and then applying `F`.
-/
def lowerCompRepresentativeIso (F : MonoOver Y ⥤ MonoOver X) :
    lower F ⋙ representative ≅ representative ⋙ F :=
  ThinSkeleton.mapCompFromThinSkeletonIso _

/-- An adjunction between `MonoOver A` and `MonoOver B` gives an adjunction
between `Subobject A` and `Subobject B`. -/
/-
**CategoryTheory.Subobject.lowerAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：lowerAdjunction {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOve
r B ⥤ MonoOver A} (h : L ⊣ R) : lower L ⊣ lower R
参数：h : L ⊣ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An adjunction between `MonoOver A` and `MonoOver B` gives an adjunction
between `Subobject A` and `Subobject B`.
-/
def lowerAdjunction {A : C} {B : D} {L : MonoOver A ⥤ MonoOver B} {R : MonoOver B ⥤ MonoOver A}
    (h : L ⊣ R) : lower L ⊣ lower R :=
  ThinSkeleton.lowerAdjunction _ _ h

set_option backward.isDefEq.respectTransparency.types false in
/-- An equivalence between `MonoOver A` and `MonoOver B` gives an equivalence
between `Subobject A` and `Subobject B`. -/
@[simps]
/-
**CategoryTheory.Subobject.lowerEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：lowerEquivalence {A : C} {B : D} (e : MonoOver A ≌ MonoOver B) : Subobject
 A ≌ Subobject B where functor
参数：e : MonoOver A ≌ MonoOver B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between `MonoOver A` and `MonoOver B` gives an equivalence
between `Subobject A` and `Subobject B`.
-/
def lowerEquivalence {A : C} {B : D} (e : MonoOver A ≌ MonoOver B) : Subobject A ≌ Subobject B where
  functor := lower e.functor
  inverse := lower e.inverse
  unitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.unitIso
    · exact ThinSkeleton.map_id_eq.symm
    · exact (ThinSkeleton.map_comp_eq _ _).symm
  counitIso := by
    apply eqToIso
    convert! ThinSkeleton.map_iso_eq e.counitIso
    · exact (ThinSkeleton.map_comp_eq _ _).symm
    · exact ThinSkeleton.map_id_eq.symm

section Limits

variable {J : Type u₃} [Category.{v₃} J]

/-
**CategoryTheory.Subobject.hasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：hasLimitsOfShape [HasLimitsOfShape J (Over X)] : HasLimitsOfShape J (Subob
ject X)
参数：Over X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoOver.hasLimitsOfShape`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {J : Type u₃} [inst_1 : CategoryTheory.Category.{v
₃, u₃} J]   (X : C) [CategoryT…
-/
instance hasLimitsOfShape [HasLimitsOfShape J (Over X)] :
    HasLimitsOfShape J (Subobject X) := by
  apply hasLimitsOfShape_thinSkeleton
/-
**CategoryTheory.Subobject.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：hasFiniteLimits [HasFiniteLimits (Over X)] : HasFiniteLimits (Subobject X)
 where out _ _ _
参数：Over X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance hasFiniteLimits [HasFiniteLimits (Over X)] : HasFiniteLimits (Subobject X) where
  out _ _ _ := by infer_instance
/-
**CategoryTheory.Subobject.hasLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：hasLimitsOfSize [HasLimitsOfSize.{w, w'} (Over X)] : HasLimitsOfSize.{w, w
'} (Subobject X) where has_limits_of_shape _ _
参数：Over X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} (Over X)] :
    HasLimitsOfSize.{w, w'} (Subobject X) where
  has_limits_of_shape _ _ := by infer_instance

end Limits

section Colimits

variable [HasCoproducts C] [HasStrongEpiMonoFactorisations C]

/-
**CategoryTheory.Subobject.hasColimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：hasColimitsOfSize : HasColimitsOfSize.{w, w'} (Subobject X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasColimitsOfSize : HasColimitsOfSize.{w, w'} (Subobject X) := by
  apply hasColimitsOfSize_thinSkeleton

end Colimits

section Pullback

variable [HasPullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `Subobject Y ⥤ Subobject X`,
by pulling back a monomorphism along `f`. -/
/-
**CategoryTheory.Subobject.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `Subobject Y ⥤ 
Subobject X`,
by pulling back a monomorphism along `f`.
-/
def pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X :=
  lower (MonoOver.pullback f)
/-
**CategoryTheory.Subobject.pullback_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Subobject`。
形式化陈述：pullback_id (x : Subobject X) : (pullback (𝟙 X)).obj x = x
参数：x : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem pullback_id (x : Subobject X) : (pullback (𝟙 X)).obj x = x := by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨MonoOver.pullbackId.app f⟩
/-
**CategoryTheory.Subobject.pullback_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Subobject`。
形式化陈述：pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z) : (pullback (f ≫ g
)).obj x = (pullback f).obj ((pullback g).obj x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : Subobject Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : Subobject Z) :
    (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) := by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.pullbackComp _ _).app t⟩
/-
**CategoryTheory.Subobject.pullback_obj_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Subobject`。
形式化陈述：pullback_obj_mk {A B X Y : C} {f : Y ⟶ X} {i : A ⟶ X} [Mono i] {j : B ⟶ Y}
 [Mono j] {f' : B ⟶ A} (h : IsPullback f' j i f) : (pullback f).obj (mk i) = mk 
j
参数：h : IsPullback f' j i f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.to_eq`：∀ {X : Type u} [inst : PartialOrder X] {x y : 
X} (f : x ≅ y), x = y
-/
theorem pullback_obj_mk {A B X Y : C} {f : Y ⟶ X} {i : A ⟶ X} [Mono i]
    {j : B ⟶ Y} [Mono j] {f' : B ⟶ A}
    (h : IsPullback f' j i f) :
    (pullback f).obj (mk i) = mk j :=
  ((equivMonoOver Y).inverse.mapIso
    (MonoOver.pullbackObjIsoOfIsPullback _ _ _ _ h)).to_eq

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.pullback_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：pullback_obj {X Y : C} (f : Y ⟶ X) (x : Subobject X) : (pullback f).obj x 
= mk (pullback.snd x.arrow f)
参数：f : Y ⟶ X；x : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.snd_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.Subobject.mk_surjective`：mk_surjective {X : C} (S : Subob
ject X) : exists (A : C) (i : A ⟶ X) (_ : Mono i), S = Subobject.mk i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.pullback_obj_mk`：pullback_obj_mk {A B X Y : C} 
{f : Y ⟶ X} {i : A ⟶ X} [Mono i] {j : B ⟶ Y} [Mono j] {f' : B ⟶ A} (h : IsPullba
ck f' j i f) : (pullback f).ob…
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pullback_obj {X Y : C} (f : Y ⟶ X) (x : Subobject X) :
    (pullback f).obj x = mk (pullback.snd x.arrow f) := by
  obtain ⟨Z, i, _, rfl⟩ := mk_surjective x
  rw [pullback_obj_mk (IsPullback.of_hasPullback i f)]
  exact mk_eq_mk_of_comm _ _ (asIso (pullback.map i f (mk i).arrow f
    (underlyingIso i).inv (𝟙 _) (𝟙 _) (by simp) (by simp))) (by simp)
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) : (pullback f).Faithful where
/-
**CategoryTheory.Subobject.isPullback_aux** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：isPullback_aux (f : X ⟶ Y) (y : Subobject Y) : exists φ, IsPullback φ ((pu
llback f).obj y).arrow y.arrow f
参数：f : X ⟶ Y；y : Subobject Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Subobject.mk_surjective`：mk_surjective {X : C} (S : Subob
ject X) : exists (A : C) (i : A ⟶ X) (_ : Mono i), S = Subobject.mk i
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.snd_of_mono`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cat
egoryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.pullback_obj`：pullback_obj {X Y : C} (f : Y ⟶ X
) (x : Subobject X) : (pullback f).obj x = mk (pullback.snd x.arrow f)
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Subobject.underlyingIso_arrow`：underlyingIso_arrow {X Y :
 C} (f : X ⟶ Y) [Mono f] : (underlyingIso f).inv ≫ (Subobject.mk f).arrow = f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isPullback_aux (f : X ⟶ Y) (y : Subobject Y) :
    ∃ φ, IsPullback φ ((pullback f).obj y).arrow y.arrow f := by
  obtain ⟨A, i, ⟨_, rfl⟩⟩ := mk_surjective y
  rw [pullback_obj]
  exists (underlyingIso (pullback.snd (mk i).arrow f)).hom ≫ pullback.fst (mk i).arrow f
  exact IsPullback.of_iso (IsPullback.of_hasPullback (mk i).arrow f)
        (underlyingIso (pullback.snd (mk i).arrow f)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)

/-- For any morphism `f : X ⟶ Y` and subobject `y` of `Y`, `Subobject.pullbackπ f y` is the first
    projection in the following pullback square:

    ```
    (Subobject.pullback f).obj y ----pullbackπ f y---> (y : C)
             |                                            |
    ((Subobject.pullback f).obj y).arrow               y.arrow
             |                                            |
             v                                            v
             X ---------------------f-------------------> Y
    ```

    For instance in the category of sets, `Subobject.pullbackπ f y` is the restriction of `f` to
    elements of `X` that are in the preimage of `y ⊆ Y`.
-/
/-
**CategoryTheory.Subobject.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：pullback (f : X ⟶ Y) : Subobject Y ⥤ Subobject X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any morphism `f : X ⟶ Y` and subobject `y` of `Y`, `Subobject.pullbackπ f y`
 is the first
    projection in the following pullback square:

    ```
    (Subobject.pullback f).obj y ----pullbackπ f y---> (y : C)
             |                                            |
    ((Subobject.pullback f).obj y).arrow               y.arrow
             |                                            |
             v                                            v
             X ---------------------f-------------------> Y
    ```

    For instance in the category of sets, `Subobject.pullbackπ f y` is the restr
iction of `f` to
    elements of `X` that are in the preimage of `y ⊆ Y`.
-/
noncomputable def pullbackπ (f : X ⟶ Y) (y : Subobject Y) :
    ((Subobject.pullback f).obj y : C) ⟶ (y : C) :=
  (isPullback_aux f y).choose

/-- This states that `pullbackπ f y` indeed forms a pullback square (see `Subobject.pullbackπ`). -/
/-
**CategoryTheory.Subobject.isPullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Subobject`。
形式化陈述：isPullback (f : X ⟶ Y) (y : Subobject Y) : IsPullback (pullbackπ f y) ((pu
llback f).obj y).arrow y.arrow f
参数：f : X ⟶ Y；y : Subobject Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `CategoryTheory.Subobject.isPullback_aux`：isPullback_aux (f : X ⟶ Y) (y :
 Subobject Y) : exists φ, IsPullback φ ((pullback f).obj y).arrow y.arrow f

--- 原说明 ---
This states that `pullbackπ f y` indeed forms a pullback square (see `Subobject.
pullbackπ`).
-/
theorem isPullback (f : X ⟶ Y) (y : Subobject Y) :
    IsPullback (pullbackπ f y) ((pullback f).obj y).arrow y.arrow f :=
  (isPullback_aux f y).choose_spec

end Pullback

section Map

/-- We can map subobjects of `X` to subobjects of `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
/-
**CategoryTheory.Subobject.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobje
ct`。
形式化陈述：map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can map subobjects of `X` to subobjects of `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [Mono f] : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.map f)
/-
**CategoryTheory.Subobject.map_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Subo
bject`。
形式化陈述：map_mk {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f] : (map f).obj
 (mk i) = mk (i ≫ f)
参数：i : A ⟶ X；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_mk {A X Y : C} (i : A ⟶ X) [Mono i] (f : X ⟶ Y) [Mono f] :
    (map f).obj (mk i) = mk (i ≫ f) :=
  rfl
/-
**CategoryTheory.Subobject.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Subo
bject`。
形式化陈述：map_id (x : Subobject X) : (map (𝟙 X)).obj x = x
参数：x : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `CategoryTheory.instMonoId`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (X : C),   CategoryTheory.Mono (CategoryTheory.CategoryStruct.id X)
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem map_id (x : Subobject X) : (map (𝟙 X)).obj x = x := by
  induction x using Quotient.inductionOn' with | _ f
  exact Quotient.sound ⟨(MonoOver.mapId _).app f⟩
/-
**CategoryTheory.Subobject.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Su
bobject`。
形式化陈述：map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X) : (ma
p (f ≫ g)).obj x = (map g).obj ((map f).obj x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] (x : Subobject X) :
    (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) := by
  induction x using Quotient.inductionOn' with | _ t
  exact Quotient.sound ⟨(MonoOver.mapComp _ _).app t⟩
/-
**CategoryTheory.Subobject.map_obj_injective** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：map_obj_injective {X Y : C} (f : X ⟶ Y) [Mono f] : Function.Injective (Sub
object.map f).obj
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.ind`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X : C} (p : CategoryTheory.Subobject X → Prop),   (∀ ⦃A : C⦄ 
(f : A ⟶ X) [inst_…
· 使用定理 `CategoryTheory.Subobject.mk_eq_mk_of_comm`：mk_eq_mk_of_comm {B A₁ A₂ : C
} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [Mono f] [Mono g] (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) 
: mk f = mk g
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.isoOfMkEqMk_hom`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B)   [inst_1 
: CategoryTheory.Mono f] [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofMkLEMk_comp`：ofMkLEMk_comp {B A₁ A₂ : C} {f :
 A₁ ⟶ B} {g : A₂ ⟶ B} [Mono f] [Mono g] (h : mk f <= mk g) : ofMkLEMk f g h ≫ g 
= f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_obj_injective {X Y : C} (f : X ⟶ Y) [Mono f] :
    Function.Injective (Subobject.map f).obj := fun X₁ X₂ h ↦ by
  induction X₁ using Subobject.ind
  induction X₂ using Subobject.ind
  simp only [map_mk] at h
  exact mk_eq_mk_of_comm _ _ (isoOfMkEqMk _ _ h) (by simp [← cancel_mono f])

/-- Isomorphic objects have equivalent subobject lattices. -/
/-
**CategoryTheory.Subobject.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subo
bject`。
形式化陈述：mapIso {A B : C} (e : A ≅ B) : Subobject A ≌ Subobject B
参数：e : A ≅ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic objects have equivalent subobject lattices.
-/
def mapIso {A B : C} (e : A ≅ B) : Subobject A ≌ Subobject B :=
  lowerEquivalence (MonoOver.mapIso e)

set_option backward.isDefEq.respectTransparency.types false in
/-- In fact, there's a type level bijection between the subobjects of isomorphic objects,
which preserves the order. -/
@[simps]
/-
**CategoryTheory.Subobject.mapIsoToOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Subobject`。
形式化陈述：mapIsoToOrderIso (e : X ≅ Y) : Subobject X ≃o Subobject Y where toFun
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In fact, there's a type level bijection between the subobjects of isomorphic obj
ects,
which preserves the order.
-/
def mapIsoToOrderIso (e : X ≅ Y) : Subobject X ≃o Subobject Y where
  toFun := (map e.hom).obj
  invFun := (map e.inv).obj
  left_inv g := by simp_rw [← map_comp, e.hom_inv_id, map_id]
  right_inv g := by simp_rw [← map_comp, e.inv_hom_id, map_id]
  map_rel_iff' {A B} := by
    dsimp
    constructor
    · intro h
      apply_fun (map e.inv).obj at h
      · simpa only [← map_comp, e.hom_inv_id, map_id] using h
      · apply Functor.monotone
    · intro h
      apply_fun (map e.hom).obj at h
      · exact h
      · apply Functor.monotone

/-- `map f : Subobject X ⥤ Subobject Y` is
the left adjoint of `pullback f : Subobject Y ⥤ Subobject X`. -/
/-
**CategoryTheory.Subobject.mapPullbackAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：mapPullbackAdj [HasPullbacks C] (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map f : Subobject X ⥤ Subobject Y` is
the left adjoint of `pullback f : Subobject Y ⥤ Subobject X`.
-/
def mapPullbackAdj [HasPullbacks C] (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  lowerAdjunction (MonoOver.mapPullbackAdj f)

@[simp]
/-
**CategoryTheory.Subobject.pullback_map_self** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：pullback_map_self [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) 
: (pullback f).obj ((map f).obj g) = g
参数：f : X ⟶ Y；g : Subobject X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem pullback_map_self [HasPullbacks C] (f : X ⟶ Y) [Mono f] (g : Subobject X) :
    (pullback f).obj ((map f).obj g) = g := by
  revert g
  exact Quotient.ind (fun g' => Quotient.sound ⟨(MonoOver.pullbackMapSelf f).app _⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Subobject.map_pullback** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Subobject`。
形式化陈述：map_pullback [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y
 ⟶ W} {k : Z ⟶ W} [Mono h] [Mono g] (comm : f ≫ h = g ≫ k) (t : IsLimit (Pullbac
kCone.mk f g comm)) (p : Subobject Y) : (map g).obj ((pullback f).obj p) = (pull
back k).obj ((map h).obj p)
参数：comm : f ≫ h = g ≫ k；t : IsLimit (PullbackCone.mk f g comm)；p : Subobject Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `CategoryTheory.ThinSkeleton.equiv_of_both_ways`：equiv_of_both_ways {X Y 
: C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {t :
 CategoryTheory.Limits.PullbackCone f g} …
-/
theorem map_pullback [HasPullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
    [Mono h] [Mono g] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk f g comm))
    (p : Subobject Y) : (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) := by
  revert p
  apply Quotient.ind'
  intro a
  apply Quotient.sound
  apply ThinSkeleton.equiv_of_both_ways
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _) _ ?_) (pullback.lift_snd _ _ _)
    simp [← comm, pullback.condition_assoc]
  · refine MonoOver.homMk (pullback.lift (pullback.fst _ _)
      (PullbackCone.IsLimit.lift t (pullback.fst _ _ ≫ a.arrow) (pullback.snd _ _) _)
      (PullbackCone.IsLimit.lift_fst _ _ _ ?_).symm) ?_
    · rw [← pullback.condition, assoc]
      rfl
    · dsimp
      rw [pullback.lift_snd_assoc]
      apply PullbackCone.IsLimit.lift_snd

end Map

section Exists

variable [HasImages C]

/-- The functor from subobjects of `X` to subobjects of `Y` given by
sending the subobject `S` to its "image" under `f`, usually denoted $\exists_f$.
For instance, when `C` is the category of types,
viewing `Subobject X` as `Set X` this is just `Set.image f`.

This functor is left adjoint to the `pullback f` functor (shown in `existsPullbackAdj`)
provided both are defined, and generalises the `map f` functor, again provided it is defined.
-/
/-
**CategoryTheory.Subobject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subobject`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from subobjects of `X` to subobjects of `Y` given by
sending the subobject `S` to its "image" under `f`, usually denoted $\exists_f$.
For instance, when `C` is the category of types,
viewing `Subobject X` as `Set X` this is just `Set.image f`.

This functor is left adjoint to the `pullback f` functor (shown in `existsPullba
ckAdj`)
provided both are defined, and generalises the `map f` functor, again provided i
t is defined.
-/
def «exists» (f : X ⟶ Y) : Subobject X ⥤ Subobject Y :=
  lower (MonoOver.exists f)

/-- When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
/-
**CategoryTheory.Subobject.exists_iso_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：exists_iso_map (f : X ⟶ Y) [Mono f] : «exists» f = map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.lower_iso`：lower_iso (F₁ F₂ : MonoOver X ⥤ Mono
Over Y) (h : F₁ ≅ F₂) : lower F₁ = lower F₂

--- 原说明 ---
When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
theorem exists_iso_map (f : X ⟶ Y) [Mono f] : «exists» f = map f :=
  lower_iso _ _ (MonoOver.existsIsoMap f)

/-- `exists f : Subobject X ⥤ Subobject Y` is
left adjoint to `pullback f : Subobject Y ⥤ Subobject X`.
-/
/-
**CategoryTheory.Subobject.existsPullbackAdj** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Subobject`。
形式化陈述：existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`exists f : Subobject X ⥤ Subobject Y` is
left adjoint to `pullback f : Subobject Y ⥤ Subobject X`.
-/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  lowerAdjunction (MonoOver.existsPullbackAdj f)

/--
Taking representatives and then `MonoOver.exists` is isomorphic to taking `Subobject.exists`
and then taking representatives.
-/
/-
**CategoryTheory.Subobject.existsCompRepresentativeIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Subobject`。
形式化陈述：existsCompRepresentativeIso (f : X ⟶ Y) : «exists» f ⋙ representative ≅ re
presentative ⋙ MonoOver.exists f
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking representatives and then `MonoOver.exists` is isomorphic to taking `Subob
ject.exists`
and then taking representatives.
-/
def existsCompRepresentativeIso (f : X ⟶ Y) :
    «exists» f ⋙ representative ≅ representative ⋙ MonoOver.exists f :=
  lowerCompRepresentativeIso _

/-- `exists f` applied to a subobject `x` is isomorphic to the image of `x.arrow ≫ f`. -/
/-
**CategoryTheory.Subobject.existsIsoImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Subobject`。
形式化陈述：existsIsoImage (f : X ⟶ Y) (x : Subobject X) : ((«exists» f).obj x : C) ≅ 
Limits.image (x.arrow ≫ f)
参数：f : X ⟶ Y；x : Subobject X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`exists f` applied to a subobject `x` is isomorphic to the image of `x.arrow ≫ f
`.
-/
def existsIsoImage (f : X ⟶ Y) (x : Subobject X) :
    ((«exists» f).obj x : C) ≅ Limits.image (x.arrow ≫ f) :=
  (MonoOver.forget Y ⋙ Over.forget Y).mapIso <| (existsCompRepresentativeIso f).app x

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given a subobject `x`, the `ImageFactorisation` of `x.arrow ≫ f` through `(exists f).obj x`. -/
@[simps! F_I F_m]
/-
**CategoryTheory.Subobject.imageFactorisation** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Subobject`。
形式化陈述：imageFactorisation (f : X ⟶ Y) (x : Subobject X) : ImageFactorisation (x.a
rrow ≫ f)
参数：f : X ⟶ Y；x : Subobject X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subobject `x`, the `ImageFactorisation` of `x.arrow ≫ f` through `(exist
s f).obj x`.
-/
def imageFactorisation (f : X ⟶ Y) (x : Subobject X) :
    ImageFactorisation (x.arrow ≫ f) :=
  let :=
    ImageFactorisation.ofIsoI
      (Image.imageFactorisation (x.arrow ≫ f))
      (existsIsoImage f x).symm
  ImageFactorisation.copy this ((«exists» f).obj x).arrow this.F.e (by
    simpa [this, -Over.w] using! (Over.w ((existsCompRepresentativeIso f).app x).hom.hom).symm)

end Exists

end Subobject

end CategoryTheory

