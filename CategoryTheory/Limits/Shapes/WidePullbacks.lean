/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Wide pullbacks

We define the category `WidePullbackShape`, (resp. `WidePushoutShape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wideCospan` (`wideSpan`) constructs a functor from this category, hitting
the given morphisms.

We use `WidePullbackShape` to define ordinary pullbacks (pushouts) by using `J := WalkingPair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `HasWidePullbacks` and `HasFiniteWidePullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/

@[expose] public section

universe w w' v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

variable (J : Type w)

/-- A wide pullback shape for any type `J` can be written simply as `Option J`. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.WidePullbackShape** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：WidePullbackShape
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide pullback shape for any type `J` can be written simply as `Option J`.
-/
def WidePullbackShape := Option J
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (WidePullbackShape J) where
  default := none

/-- A wide pushout shape for any type `J` can be written simply as `Option J`. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.WidePushoutShape** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：WidePushoutShape
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide pushout shape for any type `J` can be written simply as `Option J`.
-/
def WidePushoutShape := Option J
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (WidePushoutShape J) where
  default := none

namespace WidePullbackShape

variable {J}

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of arrows for the shape indexing a wide pullback. -/
/-
**CategoryTheory.Limits.WidePullbackShape.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Limits.WidePullbackShape`。
形式化陈述：{J : Type w} → CategoryTheory.Limits.WidePullbackShape J → CategoryTheory.
Limits.WidePullbackShape J → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of arrows for the shape indexing a wide pullback.
-/
inductive Hom : WidePullbackShape J → WidePullbackShape J → Type w
  | id : ∀ X, Hom X X
  | term : ∀ j : J, Hom (some j) none
  deriving DecidableEq

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] instDecidableEqHom.decEq
/-
**CategoryTheory.Limits.WidePullbackShape.struct** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits.WidePullbackShape`。
形式化陈述：struct : CategoryStruct (WidePullbackShape J) where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance struct : CategoryStruct (WidePullbackShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.term _
/-
**CategoryTheory.Limits.WidePullbackShape.Hom.inhabited** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.WidePullbackShape.Hom`。
形式化陈述：{J : Type w} → Inhabited (CategoryTheory.Limits.WidePullbackShape.Hom none
 none)
参数：CategoryTheory.Limits.WidePullbackShape.Hom none none。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.inhabited : Inhabited (Hom (none : WidePullbackShape J) none) :=
  ⟨Hom.id (none : WidePullbackShape J)⟩

open Lean Elab Tactic
/- Pointing note: experimenting with manual scoping of aesop tactics. Attempted to define
aesop rule directing on `WidePushoutOut` and it didn't take for some reason -/
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
meta def evalCasesBash : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePullbackShape _,
      (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.WidePullbackShape.subsingleton_hom** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：subsingleton_hom : Quiver.IsThin (WidePullbackShape J)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
instance subsingleton_hom : Quiver.IsThin (WidePullbackShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl
/-
**CategoryTheory.Limits.WidePullbackShape.category** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits.WidePullbackShape`。
形式化陈述：category : SmallCategory (WidePullbackShape J)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : SmallCategory (WidePullbackShape J) :=
  thin_category

@[simp]
/-
**CategoryTheory.Limits.WidePullbackShape.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.WidePullbackShape`。
形式化陈述：hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X
参数：X : WidePullbackShape J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simps]
/-
**CategoryTheory.Limits.WidePullbackShape.wideCospan** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：wideCospan (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B) : W
idePullbackShape J ⥤ C where obj j
参数：B : C；objs : J -> C；arrows : forall j : J, objs j ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a functor out of the wide pullback shape given a J-indexed collection 
of arrows to a
fixed object.
-/
def wideCospan (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : WidePullbackShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every diagram is naturally isomorphic (actually, equal) to a `wideCospan` -/
/-
**CategoryTheory.Limits.WidePullbackShape.diagramIsoWideCospan** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) : F ≅ wideCospan (F.obj
 none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j)
参数：F : WidePullbackShape J ⥤ C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every diagram is naturally isomorphic (actually, equal) to a `wideCospan`
-/
def diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) :
    F ≅ wideCospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j) :=
  NatIso.ofComponents fun j => eqToIso <| by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct a cone over a wide cospan. -/
@[simps]
/-
**CategoryTheory.Limits.WidePullbackShape.mkCone** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.WidePullbackShape`。
形式化陈述：mkCone {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : for
all j, X ⟶ F.obj (some j)) (w : forall j, π j ≫ F.map (Hom.term j) = f) : Cone F
参数：f : X ⟶ F.obj none；π : forall j, X ⟶ F.obj (some j)；w : forall j, π j ≫ F.map
 (Hom.term j) = f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cone over a wide cospan.
-/
def mkCone {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : ∀ j, X ⟶ F.obj (some j))
    (w : ∀ j, π j ≫ F.map (Hom.term j) = f) : Cone F :=
  { pt := X
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

set_option backward.isDefEq.respectTransparency.types false in
/-- Wide pullback diagrams of equivalent index types are equivalent. -/
/-
**CategoryTheory.Limits.WidePullbackShape.equivalenceOfEquiv** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePullbackShape J ≌ Wid
ePullbackShape J' where functor
参数：J' : Type w'；h : J ≃ J'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Wide pullback diagrams of equivalent index types are equivalent.
-/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') :
    WidePullbackShape J ≌ WidePullbackShape J' where
  functor := wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))

@[simp]
/-
**CategoryTheory.Limits.WidePullbackShape.equivalenceOfEquiv_functor_obj_none** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：equivalenceOfEquiv_functor_obj_none {ι ι' : Type*} (e : ι ≃ ι') : (WidePul
lbackShape.equivalenceOfEquiv _ e).functor.obj none = none
参数：e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivalenceOfEquiv_functor_obj_none {ι ι' : Type*} (e : ι ≃ ι') :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj none = none := rfl

@[simp]
/-
**CategoryTheory.Limits.WidePullbackShape.equivalenceOfEquiv_functor_obj_some** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：equivalenceOfEquiv_functor_obj_some {ι ι' : Type*} (e : ι ≃ ι') (i) : (Wid
ePullbackShape.equivalenceOfEquiv _ e).functor.obj (some i) = some (e i)
参数：e : ι ≃ ι'；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivalenceOfEquiv_functor_obj_some {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj (some i) = some (e i) := rfl

@[simp]
/-
**CategoryTheory.Limits.WidePullbackShape.equivalenceOfEquiv_functor_map_term** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：equivalenceOfEquiv_functor_map_term {ι ι' : Type*} (e : ι ≃ ι') (i) : (Wid
ePullbackShape.equivalenceOfEquiv _ e).functor.map (.term i) = .term (e i)
参数：e : ι ≃ ι'；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivalenceOfEquiv_functor_map_term {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.map (.term i) = .term (e i) := rfl

attribute [local instance] uliftCategory in
/-- Lifting universe and morphism levels preserves wide pullback diagrams. -/
/-
**CategoryTheory.Limits.WidePullbackShape.uliftEquivalence** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：uliftEquivalence : ULiftHom.{w'} (ULift.{w'} (WidePullbackShape J)) ≌ Wide
PullbackShape (ULift J)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lifting universe and morphism levels preserves wide pullback diagrams.
-/
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePullbackShape J)) ≌ WidePullbackShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

/-- Show two functors out of a wide pullback shape are isomorphic by showing their components are
isomorphic. -/
@[simps!]
/-
**CategoryTheory.Limits.WidePullbackShape.functorExt** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.WidePullbackShape`。
形式化陈述：functorExt {ι : Type*} {F G : WidePullbackShape ι ⥤ C} (base : F.obj none 
≅ G.obj none) (comp : forall i, F.obj (some i) ≅ G.obj (some i)) (w : forall i, 
F.map (.term i) ≫ base.hom = (comp i).hom ≫ G.map (.term i)
参数：base : F.obj none ≅ G.obj none；comp : forall i, F.obj (some i) ≅ G.obj (some 
i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show two functors out of a wide pullback shape are isomorphic by showing their c
omponents are
isomorphic.
-/
def functorExt {ι : Type*} {F G : WidePullbackShape ι ⥤ C}
    (base : F.obj none ≅ G.obj none) (comp : ∀ i, F.obj (some i) ≅ G.obj (some i))
    (w : ∀ i, F.map (.term i) ≫ base.hom = (comp i).hom ≫ G.map (.term i) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | none => base
      | some i => comp i)
    (fun f ↦ by rcases f <;> simp [w])

end WidePullbackShape

namespace WidePushoutShape

variable {J}

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of arrows for the shape indexing a wide pushout. -/
/-
**CategoryTheory.Limits.WidePushoutShape.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Limits.WidePushoutShape`。
形式化陈述：{J : Type w} → CategoryTheory.Limits.WidePushoutShape J → CategoryTheory.L
imits.WidePushoutShape J → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of arrows for the shape indexing a wide pushout.
-/
inductive Hom : WidePushoutShape J → WidePushoutShape J → Type w
  | id : ∀ X, Hom X X
  | init : ∀ j : J, Hom none (some j)
  deriving DecidableEq

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments] instDecidableEqHom.decEq
/-
**CategoryTheory.Limits.WidePushoutShape.struct** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Limits.WidePushoutShape`。
形式化陈述：struct : CategoryStruct (WidePushoutShape J) where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance struct : CategoryStruct (WidePushoutShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.init _
/-
**CategoryTheory.Limits.WidePushoutShape.Hom.inhabited** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.WidePushoutShape.Hom`。
形式化陈述：{J : Type w} → Inhabited (CategoryTheory.Limits.WidePushoutShape.Hom none 
none)
参数：CategoryTheory.Limits.WidePushoutShape.Hom none none。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Hom.inhabited : Inhabited (Hom (none : WidePushoutShape J) none) :=
  ⟨Hom.id (none : WidePushoutShape J)⟩

open Lean Elab Tactic
-- Pointing note: experimenting with manual scoping of aesop tactics; only this worked
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
meta def evalCasesBash' : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePushoutShape _,
      (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash'

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.WidePushoutShape.subsingleton_hom** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Limits.WidePushoutShape`。
形式化陈述：subsingleton_hom : Quiver.IsThin (WidePushoutShape J)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
instance subsingleton_hom : Quiver.IsThin (WidePushoutShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePushoutShape _, (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)
  repeat rfl
/-
**CategoryTheory.Limits.WidePushoutShape.category** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits.WidePushoutShape`。
形式化陈述：category : SmallCategory (WidePushoutShape J)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : SmallCategory (WidePushoutShape J) :=
  thin_category

@[simp]
/-
**CategoryTheory.Limits.WidePushoutShape.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.WidePushoutShape`。
形式化陈述：hom_id (X : WidePushoutShape J) : Hom.id X = 𝟙 X
参数：X : WidePushoutShape J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_id (X : WidePushoutShape J) : Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simps]
/-
**CategoryTheory.Limits.WidePushoutShape.wideSpan** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.WidePushoutShape`。
形式化陈述：wideSpan (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j) : Wid
ePushoutShape J ⥤ C where obj j
参数：B : C；objs : J -> C；arrows : forall j : J, B ⟶ objs j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a functor out of the wide pushout shape given a J-indexed collection o
f arrows from a
fixed object.
-/
def wideSpan (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : WidePushoutShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j
  map_comp := fun f g => by
    cases f
    · simp only [hom_id, Category.id_comp]; congr
    · cases g
      simp only [hom_id, Category.comp_id]; congr

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every diagram is naturally isomorphic (actually, equal) to a `wideSpan` -/
/-
**CategoryTheory.Limits.WidePushoutShape.diagramIsoWideSpan** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.WidePushoutShape`。
形式化陈述：diagramIsoWideSpan (F : WidePushoutShape J ⥤ C) : F ≅ wideSpan (F.obj none
) (fun j => F.obj (some j)) fun j => F.map (Hom.init j)
参数：F : WidePushoutShape J ⥤ C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every diagram is naturally isomorphic (actually, equal) to a `wideSpan`
-/
def diagramIsoWideSpan (F : WidePushoutShape J ⥤ C) :
    F ≅ wideSpan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.init j) :=
  NatIso.ofComponents fun j => eqToIso <| by cases j; repeat rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct a cocone over a wide span. -/
@[simps]
/-
**CategoryTheory.Limits.WidePushoutShape.mkCocone** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.WidePushoutShape`。
形式化陈述：mkCocone {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : fo
rall j, F.obj (some j) ⟶ X) (w : forall j, F.map (Hom.init j) ≫ ι j = f) : Cocon
e F
参数：f : F.obj none ⟶ X；ι : forall j, F.obj (some j) ⟶ X；w : forall j, F.map (Hom.
init j) ≫ ι j = f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cocone over a wide span.
-/
def mkCocone {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : ∀ j, F.obj (some j) ⟶ X)
    (w : ∀ j, F.map (Hom.init j) ≫ ι j = f) : Cocone F :=
  { pt := X
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

set_option backward.isDefEq.respectTransparency.types false in
/-- Wide pushout diagrams of equivalent index types are equivalent. -/
/-
**CategoryTheory.Limits.WidePushoutShape.equivalenceOfEquiv** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.WidePushoutShape`。
形式化陈述：equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePushoutShape J ≌ Wide
PushoutShape J' where functor
参数：J' : Type w'；h : J ≃ J'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Wide pushout diagrams of equivalent index types are equivalent.
-/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePushoutShape J ≌ WidePushoutShape J' where
  functor := wideSpan none (fun j => some (h j)) fun j => Hom.init (h j)
  inverse := wideSpan none (fun j => some (h.invFun j)) fun j => Hom.init (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))

attribute [local instance] uliftCategory in
/-- Lifting universe and morphism levels preserves wide pushout diagrams. -/
/-
**CategoryTheory.Limits.WidePushoutShape.uliftEquivalence** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits.WidePushoutShape`。
形式化陈述：uliftEquivalence : ULiftHom.{w'} (ULift.{w'} (WidePushoutShape J)) ≌ WideP
ushoutShape (ULift J)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lifting universe and morphism levels preserves wide pushout diagrams.
-/
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePushoutShape J)) ≌ WidePushoutShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePushoutShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

end WidePushoutShape

variable (C : Type u) [Category.{v} C]

/-- A category `HasWidePullbacks` if it has all limits of shape `WidePullbackShape J`, i.e. if it
has a wide pullback for every collection of morphisms with the same codomain. -/
/-
**CategoryTheory.Limits.HasWidePullbacks** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasWidePullbacks : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasWidePullbacks` if it has all limits of shape `WidePullbackShape J
`, i.e. if it
has a wide pullback for every collection of morphisms with the same codomain.
-/
abbrev HasWidePullbacks : Prop :=
  ∀ J : Type w, HasLimitsOfShape (WidePullbackShape J) C

/-- A category `HasWidePushouts` if it has all colimits of shape `WidePushoutShape J`, i.e. if it
has a wide pushout for every collection of morphisms with the same domain. -/
/-
**CategoryTheory.Limits.HasWidePushouts** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：HasWidePushouts : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasWidePushouts` if it has all colimits of shape `WidePushoutShape J
`, i.e. if it
has a wide pushout for every collection of morphisms with the same domain.
-/
abbrev HasWidePushouts : Prop :=
  ∀ J : Type w, HasColimitsOfShape (WidePushoutShape J) C

variable {C J}

/-- `HasWidePullback B objs arrows` means that `wideCospan B objs arrows` has a limit. -/
/-
**CategoryTheory.Limits.HasWidePullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：HasWidePullback (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B
) : Prop
参数：B : C；objs : J -> C；arrows : forall j : J, objs j ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasWidePullback B objs arrows` means that `wideCospan B objs arrows` has a limi
t.
-/
abbrev HasWidePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : Prop :=
  HasLimit (WidePullbackShape.wideCospan B objs arrows)

/-- `HasWidePushout B objs arrows` means that `wideSpan B objs arrows` has a colimit. -/
/-
**CategoryTheory.Limits.HasWidePushout** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：HasWidePushout (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j)
 : Prop
参数：B : C；objs : J -> C；arrows : forall j : J, B ⟶ objs j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasWidePushout B objs arrows` means that `wideSpan B objs arrows` has a colimit
.
-/
abbrev HasWidePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : Prop :=
  HasColimit (WidePushoutShape.wideSpan B objs arrows)

/-- A choice of wide pullback. -/
/-
**CategoryTheory.Limits.widePullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：widePullback (B : C) (objs : J -> C) (arrows : forall j : J, objs j ⟶ B) [
HasWidePullback B objs arrows] : C
参数：B : C；objs : J -> C；arrows : forall j : J, objs j ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of wide pullback.
-/
noncomputable abbrev widePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    [HasWidePullback B objs arrows] : C :=
  limit (WidePullbackShape.wideCospan B objs arrows)

/-- A choice of wide pushout. -/
/-
**CategoryTheory.Limits.widePushout** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：widePushout (B : C) (objs : J -> C) (arrows : forall j : J, B ⟶ objs j) [H
asWidePushout B objs arrows] : C
参数：B : C；objs : J -> C；arrows : forall j : J, B ⟶ objs j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of wide pushout.
-/
noncomputable abbrev widePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j)
    [HasWidePushout B objs arrows] : C :=
  colimit (WidePushoutShape.wideSpan B objs arrows)

namespace WidePullback

variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, objs j ⟶ B)
variable [HasWidePullback B objs arrows]

/-- The `j`-th projection from the pullback. -/
/-
**CategoryTheory.Limits.WidePullback.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits.WidePullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `j`-th projection from the pullback.
-/
noncomputable abbrev π (j : J) : widePullback _ _ arrows ⟶ objs j :=
  limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)


/-- The unique map to the base from the pullback. -/
/-
**CategoryTheory.Limits.WidePullback.base** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.WidePullback`。
形式化陈述：base : widePullback _ _ arrows ⟶ B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique map to the base from the pullback.
-/
noncomputable abbrev base : widePullback _ _ arrows ⟶ B :=
  limit.π (WidePullbackShape.wideCospan _ _ _) Option.none

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.WidePullback.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.WidePullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)

variable {arrows} in
/-- Lift a collection of morphisms to a morphism to the pullback. -/
/-
**CategoryTheory.Limits.WidePullback.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.WidePullback`。
形式化陈述：lift {X : C} (f : X ⟶ B) (fs : forall j : J, X ⟶ objs j) (w : forall j, fs
 j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows
参数：f : X ⟶ B；fs : forall j : J, X ⟶ objs j；w : forall j, fs j ≫ arrows j = f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a collection of morphisms to a morphism to the pullback.
-/
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j)
    (w : ∀ j, fs j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows :=
  limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)

variable {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.WidePullback.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.WidePullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.WidePullback.lift_base** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.WidePullback`。
形式化陈述：lift_base : lift f fs w ≫ base arrows = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.WidePullbackShape.mkCone_π_app`：∀ {J : Type w} {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functo
r (CategoryTheory.Limits.WidePullbackShape…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_base : lift f fs w ≫ base arrows = f := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]
/-
**CategoryTheory.Limits.WidePullback.eq_lift_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.WidePullback`。
形式化陈述：eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) : (forall j : J, g ≫ 
π arrows j = fs j) -> g ≫ base arrows = f -> g = lift f fs w
参数：g : X ⟶ widePullback _ _ arrows。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.uniq`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃}
 C]   {F : CategoryTheor…
-/
theorem eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) :
    (∀ j : J, g ≫ π arrows j = fs j) → g ≫ base arrows = f → g = lift f fs w := by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.WidePullback.hom_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.WidePullback`。
形式化陈述：hom_eq_lift (g : X ⟶ widePullback _ _ arrows) : g = lift (g ≫ base arrows)
 (fun j => g ≫ π arrows j) (by simp)
参数：g : X ⟶ widePullback _ _ arrows。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.WidePullbackShape.mkCone_π_app`：∀ {J : Type w} {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Functo
r (CategoryTheory.Limits.WidePullbackShape…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hom_eq_lift (g : X ⟶ widePullback _ _ arrows) :
    g = lift (g ≫ base arrows) (fun j => g ≫ π arrows j) (by simp) := by
  aesop

@[ext 1100]
/-
**CategoryTheory.Limits.WidePullback.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.WidePullback`。
形式化陈述：hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) : (forall j : J, g1 ≫ π arro
ws j = g2 ≫ π arrows j) -> g1 ≫ base arrows = g2 ≫ base arrows -> g1 = g2
参数：g1 g2 : X ⟶ widePullback _ _ arrows。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
theorem hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) : (∀ j : J,
    g1 ≫ π arrows j = g2 ≫ π arrows j) → g1 ≫ base arrows = g2 ≫ base arrows → g1 = g2 := by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

end WidePullback

/-- A wide pullback cone is a cone on the wide cospan formed by a family of morphisms. -/
/-
**CategoryTheory.Limits.WidePullbackCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：WidePullbackCone {ι : Type*} {X : C} {Y : ι -> C} (f : forall i, Y i ⟶ X)
参数：f : forall i, Y i ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide pullback cone is a cone on the wide cospan formed by a family of morphism
s.
-/
abbrev WidePullbackCone {ι : Type*} {X : C} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :=
  Cone (WidePullbackShape.wideCospan X Y f)

namespace WidePullbackCone

variable {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}

/-- The projection on the components of a wide pullback cone. -/
/-
**CategoryTheory.Limits.WidePullbackCone.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.WidePullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on the components of a wide pullback cone.
-/
def π (s : WidePullbackCone f) (i : ι) : s.pt ⟶ Y i :=
  (Cone.π s).app (some i)

/-- The projection to the base of a wide pullback cone. -/
/-
**CategoryTheory.Limits.WidePullbackCone.base** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.WidePullbackCone`。
形式化陈述：base (s : WidePullbackCone f) : s.pt ⟶ X
参数：s : WidePullbackCone f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection to the base of a wide pullback cone.
-/
def base (s : WidePullbackCone f) : s.pt ⟶ X :=
  (Cone.π s).app none

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.WidePullbackCone.condition** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits.WidePullbackCone`。
形式化陈述：condition (s : WidePullbackCone f) (i : ι) : s.π i ≫ f i = s.base
参数：s : WidePullbackCone f；i : ι。
该定理/引理给出了一组等式。
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
lemma condition (s : WidePullbackCone f) (i : ι) : s.π i ≫ f i = s.base := by
  simpa using! ((Cone.π s).naturality (.term i)).symm

/-- Construct a wide pullback cone from the projections. -/
@[simps! pt]
/-
**CategoryTheory.Limits.WidePullbackCone.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.WidePullbackCone`。
形式化陈述：mk {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f i = 
b) : WidePullbackCone f
参数：b : W ⟶ X；π : forall i, W ⟶ Y i；h : forall i, π i ≫ f i = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a wide pullback cone from the projections.
-/
def mk {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) :
    WidePullbackCone f :=
  WidePullbackShape.mkCone b π h

@[simp]
/-
**CategoryTheory.Limits.WidePullbackCone.mk_base** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Limits.WidePullbackCone`。
形式化陈述：mk_base {W : C} (b : W ⟶ X) (π : forall i, W ⟶ Y i) (h : forall i, π i ≫ f
 i = b) : (WidePullbackCone.mk b π h).base = b
参数：b : W ⟶ X；π : forall i, W ⟶ Y i；h : forall i, π i ≫ f i = b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_base {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) :
    (WidePullbackCone.mk b π h).base = b := rfl

@[simp]
/-
**CategoryTheory.Limits.WidePullbackCone.mk_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits.WidePullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_π {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) (i : ι) :
    (WidePullbackCone.mk b π h).π i = π i := rfl

/-- Constructor to show a wide pullback cone is limiting. -/
/-
**CategoryTheory.Limits.WidePullbackCone.IsLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.WidePullbackCone.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {ι : Type
 u_1} →       {X : C} →         {Y : ι → C} →           {f : (i : ι) → Y i ⟶ X} 
→             (s : CategoryTheory.Limits.WidePullbackCone f) →               (li
ft : (t : CategoryTheory.Limits.WidePullbackCone f) → t.pt ⟶ s.pt) →            
     (∀ (t : CategoryTheory.Limits.WidePullbackCone f),                     Cate
goryTheory.CategoryStruct.comp (lift t) s.base = t.base) →                   (∀ 
(t : CategoryTheory.Limits.WidePullbackCone f) (i : ι),                       Ca
tegoryTheory.CategoryStruct.comp (lift t) (s.π i) = t.π i) →                    
 (∀ (t : CategoryTheory.Limits.WidePullbackCone f) (m : t.pt ⟶ s.pt),           
              CategoryTheory.CategoryStruct.comp m s.base = t.base →            
               (∀ (i : ι), CategoryTheory.CategoryStruct.comp m (s.π i) = t.π i)
 → m = lift t) →                       CategoryTheory.Limits.IsLimit s
参数：i : ι；s : CategoryTheory.Limits.WidePullbackCone f；lift : (t : CategoryTheory
.Limits.WidePullbackCone f) → t.pt ⟶ s.pt；∀ (t : CategoryTheory.Limits.WidePullb
ackCone f),                     CategoryTheory.CategoryStruct.comp (lift t) s.ba
se = t.base；∀ (t : CategoryTheory.Limits.WidePullbackCone f) (i : ι),           
            CategoryTheory.CategoryStruct.comp (lift t) (s.π i) = t.π i；∀ (t : C
ategoryTheory.Limits.WidePullbackCone f) (m : t.pt ⟶ s.pt),                     
    CategoryTheory.CategoryStruct.comp m s.base = t.base →                      
     (∀ (i : ι), CategoryTheory.CategoryStruct.comp m (s.π i) = t.π i) → m = lif
t t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor to show a wide pullback cone is limiting.
-/
def IsLimit.mk (s : WidePullbackCone f) (lift : ∀ t : WidePullbackCone f, t.pt ⟶ s.pt)
    (facbase : ∀ t, lift t ≫ s.base = t.base) (facπ : ∀ t i, lift t ≫ s.π i = t.π i)
    (uniq : ∀ (t) (m : t.pt ⟶ s.pt), m ≫ s.base = t.base → (∀ i, m ≫ s.π i = t.π i) → m = lift t) :
    IsLimit s where
  lift := lift
  fac t j := by
    cases j
    · exact facbase t
    · exact facπ t _
  uniq t m hm := uniq _ _ (hm none) fun _ ↦ hm (some _)
/-
**CategoryTheory.Limits.WidePullbackCone.IsLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.WidePullbackCone.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X
 : C} {Y : ι → C} {f : (i : ι) → Y i ⟶ X}   {s : CategoryTheory.Limits.WidePullb
ackCone f} (hs : CategoryTheory.Limits.IsLimit s) {W : C} {k l : W ⟶ s.pt},   Ca
tegoryTheory.CategoryStruct.comp k s.base = CategoryTheory.CategoryStruct.comp l
 s.base →     (∀ (i : ι), CategoryTheory.CategoryStruct.comp k (s.π i) = Categor
yTheory.CategoryStruct.comp l (s.π i)) → k = l
参数：i : ι；hs : CategoryTheory.Limits.IsLimit s；∀ (i : ι), CategoryTheory.Category
Struct.comp k (s.π i) = CategoryTheory.CategoryStruct.comp l (s.π i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
-/
lemma IsLimit.hom_ext {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} {k l : W ⟶ s.pt} (hbase : k ≫ s.base = l ≫ s.base)
    (hπ : ∀ i, k ≫ s.π i = l ≫ s.π i) :
    k = l := by
  apply hs.hom_ext
  rintro (_ | j)
  · exact hbase
  · exact hπ j

/-- Lift a family of morphisms to a limiting wide pullback cone. -/
/-
**CategoryTheory.Limits.WidePullbackCone.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.WidePullbackCone.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {ι : Type
 u_1} →       {X : C} →         {Y : ι → C} →           {f : (i : ι) → Y i ⟶ X} 
→             {s : CategoryTheory.Limits.WidePullbackCone f} →               Cat
egoryTheory.Limits.IsLimit s →                 {W : C} →                   (b : 
W ⟶ X) →                     (a : (i : ι) → W ⟶ Y i) →                       (∀ 
(i : ι), CategoryTheory.CategoryStruct.comp (a i) (f i) = b) → (W ⟶ s.pt)
参数：i : ι；b : W ⟶ X；a : (i : ι) → W ⟶ Y i；∀ (i : ι), CategoryTheory.CategoryStruc
t.comp (a i) (f i) = b；W ⟶ s.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a family of morphisms to a limiting wide pullback cone.
-/
def IsLimit.lift {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) :
    W ⟶ s.pt :=
  hs.lift (WidePullbackCone.mk b a w)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.WidePullbackCone.IsLimit.lift_base** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.WidePullbackCone.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} {X
 : C} {Y : ι → C} {f : (i : ι) → Y i ⟶ X}   {s : CategoryTheory.Limits.WidePullb
ackCone f} (hs : CategoryTheory.Limits.IsLimit s) {W : C} (b : W ⟶ X)   (a : (i 
: ι) → W ⟶ Y i) (w : ∀ (i : ι), CategoryTheory.CategoryStruct.comp (a i) (f i) =
 b),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.WidePullbackCon
e.IsLimit.lift hs b a w) s.base = b
参数：i : ι；hs : CategoryTheory.Limits.IsLimit s；b : W ⟶ X；a : (i : ι) → W ⟶ Y i；w 
: ∀ (i : ι), CategoryTheory.CategoryStruct.comp (a i) (f i) = b；CategoryTheory.L
imits.WidePullbackCone.IsLimit.lift hs b a w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma IsLimit.lift_base {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) :
    IsLimit.lift hs b a w ≫ s.base = b :=
  hs.fac _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.WidePullbackCone.IsLimit.lift_** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits.WidePullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsLimit.lift_π {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) (i : ι) :
    IsLimit.lift hs b a w ≫ s.π i = a i :=
  hs.fac _ _

/-- To show two wide pullback cones are isomorphic, it suffices to give a compatible isomorphism
of their cone points. -/
/-
**CategoryTheory.Limits.WidePullbackCone.ext** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.WidePullbackCone`。
形式化陈述：ext {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} {s t : WidePu
llbackCone f} (e : s.pt ≅ t.pt) (base : e.hom ≫ t.base = s.base
参数：e : s.pt ≅ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show two wide pullback cones are isomorphic, it suffices to give a compatible
 isomorphism
of their cone points.
-/
def ext {ι : Type*}
    {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {s t : WidePullbackCone f}
    (e : s.pt ≅ t.pt)
    (base : e.hom ≫ t.base = s.base := by cat_disch)
    (π : ∀ i, e.hom ≫ t.π i = s.π i := by cat_disch) :
    s ≅ t :=
  Cone.ext e <| by
    rintro (_ | _)
    · exact base.symm
    · exact (π _).symm

/-- Reindex a wide pullback cone. -/
@[simps! pt]
/-
**CategoryTheory.Limits.WidePullbackCone.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.WidePullbackCone`。
形式化陈述：reindex {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s : Wide
PullbackCone f) {ι' : Type*} (e : ι' ≃ ι) : WidePullbackCone (fun i => f (e i))
参数：s : WidePullbackCone f；e : ι' ≃ ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindex a wide pullback cone.
-/
def reindex {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    WidePullbackCone (fun i ↦ f (e i)) :=
  .mk s.base (fun i ↦ s.π _) (by simp)

@[simp]
/-
**CategoryTheory.Limits.WidePullbackCone.reindex_base** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.WidePullbackCone`。
形式化陈述：reindex_base {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ X} (s :
 WidePullbackCone f) {ι' : Type*} (e : ι' ≃ ι) : (s.reindex e).base = s.base
参数：s : WidePullbackCone f；e : ι' ≃ ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reindex_base {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    (s.reindex e).base = s.base := rfl

@[simp]
/-
**CategoryTheory.Limits.WidePullbackCone.reindex_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits.WidePullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reindex_π {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) (i : ι') :
    (s.reindex e).π i = s.π (e i) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Reindexing a pullback cone preserves being limiting. -/
/-
**CategoryTheory.Limits.WidePullbackCone.reindexIsLimitEquiv** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.WidePullbackCone`。
形式化陈述：reindexIsLimitEquiv {ι : Type*} {X : C} {Y : ι -> C} {f : forall i, Y i ⟶ 
X} (s : WidePullbackCone f) {ι' : Type*} (e : ι' ≃ ι) : IsLimit (s.reindex e) ≃ 
IsLimit s
参数：s : WidePullbackCone f；e : ι' ≃ ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reindexing a pullback cone preserves being limiting.
-/
def reindexIsLimitEquiv {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}
    (s : WidePullbackCone f) {ι' : Type*} (e : ι' ≃ ι) :
    IsLimit (s.reindex e) ≃ IsLimit s :=
  (IsLimit.whiskerEquivalenceEquiv <| WidePullbackShape.equivalenceOfEquiv _ e.symm).trans <|
    IsLimit.equivOfNatIsoOfIso
      (WidePullbackShape.functorExt (Iso.refl X) (fun i ↦ eqToIso (by simp))
        fun i ↦ by simp [← eqToHom_naturality]) _ _
      (WidePullbackCone.ext (Iso.refl _) (by simp [base, reindex, mk])
        (fun i ↦ by
          simp [π, reindex, mk,
            eqToHom_naturality (fun i ↦ (Cone.π s).app (some i)) (e.apply_symm_apply i)]))

end WidePullbackCone

namespace WidePushout

variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, B ⟶ objs j)
variable [HasWidePushout B objs arrows]

/-- The `j`-th inclusion to the pushout. -/
/-
**CategoryTheory.Limits.WidePushout.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits.WidePushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `j`-th inclusion to the pushout.
-/
noncomputable abbrev ι (j : J) : objs j ⟶ widePushout _ _ arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)

/-- The unique map from the head to the pushout. -/
/-
**CategoryTheory.Limits.WidePushout.head** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits.WidePushout`。
形式化陈述：head : B ⟶ widePushout B objs arrows
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique map from the head to the pushout.
-/
noncomputable abbrev head : B ⟶ widePushout B objs arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none

@[reassoc, simp]
/-
**CategoryTheory.Limits.WidePushout.arrow_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.WidePushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrow_ι (j : J) : arrows j ≫ ι arrows j = head arrows := by
  apply colimit.w (WidePushoutShape.wideSpan _ _ _) (WidePushoutShape.Hom.init j)

variable {arrows} in
/-- Descend a collection of morphisms to a morphism from the pushout. -/
/-
**CategoryTheory.Limits.WidePushout.desc** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits.WidePushout`。
形式化陈述：desc {X : C} (f : B ⟶ X) (fs : forall j : J, objs j ⟶ X) (w : forall j, ar
rows j ≫ fs j = f) : widePushout _ _ arrows ⟶ X
参数：f : B ⟶ X；fs : forall j : J, objs j ⟶ X；w : forall j, arrows j ≫ fs j = f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Descend a collection of morphisms to a morphism from the pushout.
-/
noncomputable abbrev desc {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X)
    (w : ∀ j, arrows j ≫ fs j = f) : widePushout _ _ arrows ⟶ X :=
  colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)

variable {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X) (w : ∀ j, arrows j ≫ fs j = f)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.WidePushout.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.WidePushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_desc (j : J) : ι arrows j ≫ desc f fs w = fs _ := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.WidePushout.head_desc** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.WidePushout`。
形式化陈述：head_desc : head arrows ≫ desc f fs w = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.WidePushoutShape.mkCocone_ι_app`：∀ {J : Type w} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Funct
or (CategoryTheory.Limits.WidePushoutShape …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem head_desc : head arrows ≫ desc f fs w = f := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_ι_app]
/-
**CategoryTheory.Limits.WidePushout.eq_desc_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.WidePushout`。
形式化陈述：eq_desc_of_comp_eq (g : widePushout _ _ arrows ⟶ X) : (forall j : J, ι arr
ows j ≫ g = fs j) -> head arrows ≫ g = f -> g = desc f fs w
参数：g : widePushout _ _ arrows ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.uniq`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u
₃} C]   {F : CategoryTheor…
-/
theorem eq_desc_of_comp_eq (g : widePushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g = fs j) → head arrows ≫ g = f → g = desc f fs w := by
  intro h1 h2
  apply
    (colimit.isColimit (WidePushoutShape.wideSpan B objs arrows)).uniq
      (WidePushoutShape.mkCocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.WidePushout.hom_eq_desc** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.WidePushout`。
形式化陈述：hom_eq_desc (g : widePushout _ _ arrows ⟶ X) : g = desc (head arrows ≫ g) 
(fun j => ι arrows j ≫ g) fun j => by rw [← Category.assoc] simp
参数：g : widePushout _ _ arrows ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.WidePushoutShape.mkCocone_ι_app`：∀ {J : Type w} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C]   {F : CategoryTheory.Funct
or (CategoryTheory.Limits.WidePushoutShape …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hom_eq_desc (g : widePushout _ _ arrows ⟶ X) :
    g =
      desc (head arrows ≫ g) (fun j => ι arrows j ≫ g) fun j => by
        rw [← Category.assoc]
        simp := by
  cat_disch

@[ext 1100]
/-
**CategoryTheory.Limits.WidePushout.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.WidePushout`。
形式化陈述：hom_ext (g1 g2 : widePushout _ _ arrows ⟶ X) : (forall j : J, ι arrows j ≫
 g1 = ι arrows j ≫ g2) -> head arrows ≫ g1 = head arrows ≫ g2 -> g1 = g2
参数：g1 g2 : widePushout _ _ arrows ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
-/
theorem hom_ext (g1 g2 : widePushout _ _ arrows ⟶ X) : (∀ j : J,
    ι arrows j ≫ g1 = ι arrows j ≫ g2) → head arrows ≫ g1 = head arrows ≫ g2 → g1 = g2 := by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

end WidePushout

variable (J)

/-- The action on morphisms of the obvious functor
  `WidePullbackShape_op : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
/-
**CategoryTheory.Limits.widePullbackShapeOpMap** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：(J : Type w) → (X Y : CategoryTheory.Limits.WidePullbackShape J) → (X ⟶ Y)
 → (Opposite.op X ⟶ Opposite.op Y)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on morphisms of the obvious functor
  `WidePullbackShape_op : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ`
-/
def widePullbackShapeOpMap :
    ∀ X Y : WidePullbackShape J,
      (X ⟶ Y) → ((op X : (WidePushoutShape J)ᵒᵖ) ⟶ (op Y : (WidePushoutShape J)ᵒᵖ))
  | _, _, WidePullbackShape.Hom.id X => Quiver.Hom.op (WidePushoutShape.Hom.id _)
  | _, _, WidePullbackShape.Hom.term _ => Quiver.Hom.op (WidePushoutShape.Hom.init _)

/-- The obvious functor `WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
@[simps]
/-
**CategoryTheory.Limits.widePullbackShapeOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where o
bj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor `WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ`
-/
def widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  obj X := op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂

/-- The action on morphisms of the obvious functor
`widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/
/-
**CategoryTheory.Limits.widePushoutShapeOpMap** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：(J : Type w) → (X Y : CategoryTheory.Limits.WidePushoutShape J) → (X ⟶ Y) 
→ (Opposite.op X ⟶ Opposite.op Y)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on morphisms of the obvious functor
`widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ`
-/
def widePushoutShapeOpMap :
    ∀ X Y : WidePushoutShape J,
      (X ⟶ Y) → ((op X : (WidePullbackShape J)ᵒᵖ) ⟶ (op Y : (WidePullbackShape J)ᵒᵖ))
  | _, _, WidePushoutShape.Hom.id X => Quiver.Hom.op (WidePullbackShape.Hom.id _)
  | _, _, WidePushoutShape.Hom.init _ => Quiver.Hom.op (WidePullbackShape.Hom.term _)

/-- The obvious functor `WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/
@[simps]
/-
**CategoryTheory.Limits.widePushoutShapeOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where ob
j X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor `WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ`
-/
def widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where
  obj X := op X
  map := fun {X} {Y} => widePushoutShapeOpMap J X Y

/-- The obvious functor `(WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J` -/
@[simps!]
/-
**CategoryTheory.Limits.widePullbackShapeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor `(WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J`
-/
def widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J :=
  (widePullbackShapeOp J).leftOp

/-- The obvious functor `(WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J` -/
@[simps!]
/-
**CategoryTheory.Limits.widePushoutShapeUnop** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：widePushoutShapeUnop : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor `(WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J`
-/
def widePushoutShapeUnop : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J :=
  (widePushoutShapeOp J).leftOp

/-- The inverse of the unit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
/-
**CategoryTheory.Limits.widePushoutShapeOpUnop** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 
𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of the unit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J`
-/
def widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The counit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
/-
**CategoryTheory.Limits.widePushoutShapeUnopOp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 
𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J`
-/
def widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The inverse of the unit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
/-
**CategoryTheory.Limits.widePullbackShapeOpUnop** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：widePullbackShapeOpUnop : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅
 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of the unit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J`
-/
def widePullbackShapeOpUnop : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The counit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
/-
**CategoryTheory.Limits.widePullbackShapeUnopOp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：widePullbackShapeUnopOp : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅
 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J`
-/
def widePullbackShapeUnopOp : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The duality equivalence `(WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
@[simps]
/-
**CategoryTheory.Limits.widePushoutShapeOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J whe
re functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The duality equivalence `(WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J`
-/
def widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  functor := widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J

/-- The duality equivalence `(WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
@[simps]
/-
**CategoryTheory.Limits.widePullbackShapeOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J wh
ere functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The duality equivalence `(WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J`
-/
def widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J where
  functor := widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J

/-- If a category has wide pushouts on a higher universe level it also has wide pushouts
on a lower universe level. -/
/-
**CategoryTheory.Limits.hasWidePushouts_shrink** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasWidePushouts_shrink [HasWidePushouts.{max w w'} C] : HasWidePushouts.{w
} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C

--- 原说明 ---
If a category has wide pushouts on a higher universe level it also has wide push
outs
on a lower universe level.
-/
theorem hasWidePushouts_shrink [HasWidePushouts.{max w w'} C] : HasWidePushouts.{w} C := fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

/-- If a category has wide pullbacks on a higher universe level it also has wide pullbacks
on a lower universe level. -/
/-
**CategoryTheory.Limits.hasWidePullbacks_shrink** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasWidePullbacks_shrink [HasWidePullbacks.{max w w'} C] : HasWidePullbacks
.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C

--- 原说明 ---
If a category has wide pullbacks on a higher universe level it also has wide pul
lbacks
on a lower universe level.
-/
theorem hasWidePullbacks_shrink [HasWidePullbacks.{max w w'} C] : HasWidePullbacks.{w} C := fun _ =>
  hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

end CategoryTheory.Limits

