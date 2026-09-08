/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Equalizers and coequalizers

This file defines (co)equalizers as special cases of (co)limits.

An equalizer is the categorical generalization of the subobject ${a ∈ A | f(a) = g(a)}$ known
from abelian groups or modules. It is a limit cone over the diagram formed by `f` and `g`.

A coequalizer is the dual concept.

## Main definitions

* `WalkingParallelPair` is the indexing category used for (co)equalizer diagrams
* `parallelPair` is a functor from `WalkingParallelPair` to our category `C`.
* a `fork` is a cone over a parallel pair.
  * there is really only one interesting morphism in a fork: the arrow from the vertex of the fork
    to the domain of f and g. It is called `fork.ι`.
* an `equalizer` is now just a `limit (parallelPair f g)`

Each of these has a dual.

## Main statements

* `equalizer.ι_mono` states that every equalizer map is a monomorphism
* `isIso_limit_cone_parallelPair_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

@[expose] public section

section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v v₂ u u₂

/-- The type of objects for the diagram indexing a (co)equalizer. -/
/-
**CategoryTheory.Limits.WalkingParallelPair** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects for the diagram indexing a (co)equalizer.
-/
inductive WalkingParallelPair : Type
  | zero
  | one
  deriving DecidableEq, Inhabited

open WalkingParallelPair

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
/-
**CategoryTheory.Limits.WalkingParallelPairHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：CategoryTheory.Limits.WalkingParallelPair → CategoryTheory.Limits.WalkingP
arallelPair → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type family of morphisms for the diagram indexing a (co)equalizer.
-/
inductive WalkingParallelPairHom : WalkingParallelPair → WalkingParallelPair → Type
  | left : WalkingParallelPairHom zero one
  | right : WalkingParallelPairHom zero one
  | id (X : WalkingParallelPair) : WalkingParallelPairHom X X
  deriving DecidableEq

/-- Satisfying the inhabited linter -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Satisfying the inhabited linter
-/
instance : Inhabited (WalkingParallelPairHom zero one) where default := WalkingParallelPairHom.left

open WalkingParallelPairHom

/-- Composition of morphisms in the indexing diagram for (co)equalizers. -/
/-
**CategoryTheory.Limits.WalkingParallelPairHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.WalkingParallelPairHom`。
形式化陈述：{X Y Z : CategoryTheory.Limits.WalkingParallelPair} →   CategoryTheory.Lim
its.WalkingParallelPairHom X Y →     CategoryTheory.Limits.WalkingParallelPairHo
m Y Z → CategoryTheory.Limits.WalkingParallelPairHom X Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms in the indexing diagram for (co)equalizers.
-/
def WalkingParallelPairHom.comp :
    ∀ {X Y Z : WalkingParallelPair} (_ : WalkingParallelPairHom X Y)
      (_ : WalkingParallelPairHom Y Z), WalkingParallelPairHom X Z
  | _, _, _, id _, h => h
  | _, _, _, left, id one => left
  | _, _, _, right, id one => right
/-
**CategoryTheory.Limits.WalkingParallelPairHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.WalkingParallelPairHom`。
形式化陈述：∀ {X Y : CategoryTheory.Limits.WalkingParallelPair} (g : CategoryTheory.Li
mits.WalkingParallelPairHom X Y),   (CategoryTheory.Limits.WalkingParallelPairHo
m.id X).comp g = g
参数：g : CategoryTheory.Limits.WalkingParallelPairHom X Y；CategoryTheory.Limits.Wa
lkingParallelPairHom.id X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem WalkingParallelPairHom.id_comp
    {X Y : WalkingParallelPair} (g : WalkingParallelPairHom X Y) : comp (id X) g = g :=
  rfl
/-
**CategoryTheory.Limits.WalkingParallelPairHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.WalkingParallelPairHom`。
形式化陈述：∀ {X Y : CategoryTheory.Limits.WalkingParallelPair} (f : CategoryTheory.Li
mits.WalkingParallelPairHom X Y),   f.comp (CategoryTheory.Limits.WalkingParalle
lPairHom.id Y) = f
参数：f : CategoryTheory.Limits.WalkingParallelPairHom X Y；CategoryTheory.Limits.Wa
lkingParallelPairHom.id Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem WalkingParallelPairHom.comp_id
    {X Y : WalkingParallelPair} (f : WalkingParallelPairHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl
/-
**CategoryTheory.Limits.WalkingParallelPairHom.assoc** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.WalkingParallelPairHom`。
形式化陈述：∀ {X Y Z W : CategoryTheory.Limits.WalkingParallelPair} (f : CategoryTheor
y.Limits.WalkingParallelPairHom X Y)   (g : CategoryTheory.Limits.WalkingParalle
lPairHom Y Z) (h : CategoryTheory.Limits.WalkingParallelPairHom Z W),   (f.comp 
g).comp h = f.comp (g.comp h)
参数：f : CategoryTheory.Limits.WalkingParallelPairHom X Y；g : CategoryTheory.Limit
s.WalkingParallelPairHom Y Z；h : CategoryTheory.Limits.WalkingParallelPairHom Z 
W；f.comp g；g.comp h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem WalkingParallelPairHom.assoc {X Y Z W : WalkingParallelPair}
    (f : WalkingParallelPairHom X Y) (g : WalkingParallelPairHom Y Z)
    (h : WalkingParallelPairHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl
/-
**CategoryTheory.Limits.walkingParallelPairHomCategory** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairHomCategory : SmallCategory WalkingParallelPair where H
om
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.WalkingParallelPairHom.id_comp`：∀ {X Y : CategoryT
heory.Limits.WalkingParallelPair} (g : CategoryTheory.Limits.WalkingParallelPair
Hom X Y),   (CategoryTheory.Limits.Walking…
· 使用定理 `CategoryTheory.Limits.WalkingParallelPairHom.comp_id`：∀ {X Y : CategoryT
heory.Limits.WalkingParallelPair} (f : CategoryTheory.Limits.WalkingParallelPair
Hom X Y),   f.comp (CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.WalkingParallelPairHom.assoc`：∀ {X Y Z W : Categor
yTheory.Limits.WalkingParallelPair} (f : CategoryTheory.Limits.WalkingParallelPa
irHom X Y)   (g : CategoryTheory.Limits.…
-/
instance walkingParallelPairHomCategory : SmallCategory WalkingParallelPair where
  Hom := WalkingParallelPairHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：walkingParallelPairHom_id (X : WalkingParallelPair) : WalkingParallelPairH
om.id X = 𝟙 X
参数：X : WalkingParallelPair。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairHom_id (X : WalkingParallelPair) : WalkingParallelPairHom.id X = 𝟙 X :=
  rfl

/-- The functor `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
@[implicit_reducible]
/-
**CategoryTheory.Limits.walkingParallelPairOp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：walkingParallelPairOp : WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ where 
obj x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The functor `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left a
nd right to
right.
-/
def walkingParallelPairOp : WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ where
  obj x := op <| match x with | zero => one | one => zero
  map f := by
    cases f <;> apply Quiver.Hom.op
    exacts [left, right, WalkingParallelPairHom.id _]
  map_comp := by rintro _ _ _ (_ | _ | _) g <;> cases g <;> rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：walkingParallelPairOp_zero : walkingParallelPairOp.obj zero = op one
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOp_zero : walkingParallelPairOp.obj zero = op one := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOp_one** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：walkingParallelPairOp_one : walkingParallelPairOp.obj one = op zero
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOp_one : walkingParallelPairOp.obj one = op zero := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOp_left** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：walkingParallelPairOp_left : walkingParallelPairOp.map left = @Quiver.Hom.
op _ _ zero one left
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOp_left :
    walkingParallelPairOp.map left = @Quiver.Hom.op _ _ zero one left := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOp_right** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：walkingParallelPairOp_right : walkingParallelPairOp.map right = @Quiver.Ho
m.op _ _ zero one right
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOp_right :
    walkingParallelPairOp.map right = @Quiver.Hom.op _ _ zero one right := rfl

/--
The equivalence `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
@[simps functor inverse]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv : WalkingParallelPair ≌ WalkingParallelPairᵒᵖ w
here functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to le
ft and right to
right.
-/
def walkingParallelPairOpEquiv : WalkingParallelPair ≌ WalkingParallelPairᵒᵖ where
  functor := walkingParallelPairOp
  inverse := walkingParallelPairOp.leftOp
  unitIso :=
    NatIso.ofComponents (fun j => eqToIso (by cases j <;> rfl))
      (by rintro _ _ (_ | _ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun j => eqToIso (by
            induction j with | _ X
            cases X <;> rfl))
      (fun {i} {j} f => by
      induction i with | _ i
      induction j with | _ j
      let g := f.unop
      have : f = g.op := rfl
      rw [this]
      cases i <;> cases j <;> cases g <;> rfl)
  functor_unitIso_comp := fun j => by cases j <;> rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_zero** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_unitIso_zero : walkingParallelPairOpEquiv.unitI
so.app zero = Iso.refl zero
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_unitIso_zero :
    walkingParallelPairOpEquiv.unitIso.app zero = Iso.refl zero := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_one** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_unitIso_one : walkingParallelPairOpEquiv.unitIs
o.app one = Iso.refl one
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_unitIso_one :
    walkingParallelPairOpEquiv.unitIso.app one = Iso.refl one := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_zero** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_counitIso_zero : walkingParallelPairOpEquiv.cou
nitIso.app (op zero) = Iso.refl (op zero)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_counitIso_zero :
    walkingParallelPairOpEquiv.counitIso.app (op zero) = Iso.refl (op zero) := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_one** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_counitIso_one : walkingParallelPairOpEquiv.coun
itIso.app (op one) = Iso.refl (op one)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_counitIso_one :
    walkingParallelPairOpEquiv.counitIso.app (op one) = Iso.refl (op one) :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_hom_app_zero** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_unitIso_hom_app_zero : walkingParallelPairOpEqu
iv.unitIso.hom.app zero = 𝟙 zero
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_unitIso_hom_app_zero :
    walkingParallelPairOpEquiv.unitIso.hom.app zero = 𝟙 zero := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_hom_app_one** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_unitIso_hom_app_one : walkingParallelPairOpEqui
v.unitIso.hom.app one = 𝟙 one
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_unitIso_hom_app_one :
    walkingParallelPairOpEquiv.unitIso.hom.app one = 𝟙 one := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_inv_app_zero** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_unitIso_inv_app_zero : walkingParallelPairOpEqu
iv.unitIso.inv.app zero = 𝟙 zero
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_unitIso_inv_app_zero :
    walkingParallelPairOpEquiv.unitIso.inv.app zero = 𝟙 zero := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_unitIso_inv_app_one** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_unitIso_inv_app_one : walkingParallelPairOpEqui
v.unitIso.inv.app one = 𝟙 one
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_unitIso_inv_app_one :
    walkingParallelPairOpEquiv.unitIso.inv.app one = 𝟙 one := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_hom_app_op_zero** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_counitIso_hom_app_op_zero : walkingParallelPair
OpEquiv.counitIso.hom.app (op zero) = 𝟙 (op zero)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_counitIso_hom_app_op_zero :
    walkingParallelPairOpEquiv.counitIso.hom.app (op zero) = 𝟙 (op zero) := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_hom_app_op_one** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_counitIso_hom_app_op_one : walkingParallelPairO
pEquiv.counitIso.hom.app (op one) = 𝟙 (op one)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_counitIso_hom_app_op_one :
    walkingParallelPairOpEquiv.counitIso.hom.app (op one) = 𝟙 (op one) :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_inv_app_op_zero** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_counitIso_inv_app_op_zero : walkingParallelPair
OpEquiv.counitIso.inv.app (op zero) = 𝟙 (op zero)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_counitIso_inv_app_op_zero :
    walkingParallelPairOpEquiv.counitIso.inv.app (op zero) = 𝟙 (op zero) := rfl

@[simp]
/-
**CategoryTheory.Limits.walkingParallelPairOpEquiv_counitIso_inv_app_op_one** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelPairOpEquiv_counitIso_inv_app_op_one : walkingParallelPairO
pEquiv.counitIso.inv.app (op one) = 𝟙 (op one)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem walkingParallelPairOpEquiv_counitIso_inv_app_op_one :
    walkingParallelPairOpEquiv.counitIso.inv.app (op one) = 𝟙 (op one) :=
  rfl

variable {C : Type u}
variable {X Y : C}

namespace parallelPair

/-- Implementation of `parallelPair`, do not use directly. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.parallelPair.parallelPairObj** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.parallelPair`。
形式化陈述：parallelPairObj (X Y : C) (x : WalkingParallelPair) : C
参数：X Y : C；x : WalkingParallelPair。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `parallelPair`, do not use directly.
-/
def parallelPairObj (X Y : C) (x : WalkingParallelPair) : C :=
  match x with
  | zero => X
  | one => Y
/-
**CategoryTheory.Limits.parallelPair.parallelPairObj_zero** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.parallelPair`。
形式化陈述：∀ {C : Type u} {X Y : C},   CategoryTheory.Limits.parallelPair.parallelPai
rObj X Y CategoryTheory.Limits.WalkingParallelPair.zero = X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem parallelPairObj_zero : parallelPairObj X Y zero = X := rfl
/-
**CategoryTheory.Limits.parallelPair.parallelPairObj_one** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.parallelPair`。
形式化陈述：∀ {C : Type u} {X Y : C},   CategoryTheory.Limits.parallelPair.parallelPai
rObj X Y CategoryTheory.Limits.WalkingParallelPair.one = Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem parallelPairObj_one : parallelPairObj X Y one = Y := rfl

variable [Category.{v} C]

/-- Implementation of `parallelPair`, do not use directly. -/
/-
**CategoryTheory.Limits.parallelPair.parallelPairHom** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.parallelPair`。
形式化陈述：parallelPairHom (f g : X ⟶ Y) {x y : WalkingParallelPair} (h : x ⟶ y) : pa
rallelPairObj X Y x ⟶ parallelPairObj X Y y
参数：f g : X ⟶ Y；h : x ⟶ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of `parallelPair`, do not use directly.
-/
def parallelPairHom (f g : X ⟶ Y) {x y : WalkingParallelPair} (h : x ⟶ y) :
    parallelPairObj X Y x ⟶ parallelPairObj X Y y :=
  match h with
  | .id _ => 𝟙 _
  | .left => f
  | .right => g
/-
**CategoryTheory.Limits.parallelPair.parallelPairHom_id** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.parallelPair`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y}   {x : CategoryTheory.Limits.WalkingParallelPair},   CategoryTheory.Limit
s.parallelPair.parallelPairHom f g (CategoryTheory.CategoryStruct.id x) =     Ca
tegoryTheory.CategoryStruct.id (CategoryTheory.Limits.parallelPair.parallelPairO
bj X Y x)
参数：CategoryTheory.CategoryStruct.id x；CategoryTheory.Limits.parallelPair.paralle
lPairObj X Y x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem parallelPairHom_id {f g : X ⟶ Y} {x : WalkingParallelPair} :
  parallelPairHom f g (𝟙 x) = 𝟙 (parallelPairObj X Y x) := (rfl)
/-
**CategoryTheory.Limits.parallelPair.parallelPairHom_left** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.parallelPair`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y},   CategoryTheory.Limits.parallelPair.parallelPairHom f g CategoryTheory.
Limits.WalkingParallelPairHom.left = f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem parallelPairHom_left {f g : X ⟶ Y} :
  parallelPairHom f g .left = f := (rfl)
/-
**CategoryTheory.Limits.parallelPair.parallelPairHom_right** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.parallelPair`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y},   CategoryTheory.Limits.parallelPair.parallelPairHom f g CategoryTheory.
Limits.WalkingParallelPairHom.right = g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem parallelPairHom_right {f g : X ⟶ Y} :
  parallelPairHom f g .right = g := (rfl)

end parallelPair

variable [Category.{v} C]

open parallelPair in
/-- `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
common domain and codomain. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.parallelPair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：parallelPair (f g : X ⟶ Y) : WalkingParallelPair ⥤ C where obj x
参数：f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and
 `g` with
common domain and codomain.
-/
def parallelPair (f g : X ⟶ Y) : WalkingParallelPair ⥤ C where
  obj x := parallelPairObj X Y x
  map h := parallelPairHom f g h
  map_comp := by rintro _ _ _ ⟨⟩ ⟨⟩ <;> simp

@[simp]
/-
**CategoryTheory.Limits.parallelPair_obj_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：parallelPair_obj_zero (f g : X ⟶ Y) : (parallelPair f g).obj zero = X
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelPair_obj_zero (f g : X ⟶ Y) : (parallelPair f g).obj zero = X := rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPair_obj_one** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：parallelPair_obj_one (f g : X ⟶ Y) : (parallelPair f g).obj one = Y
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelPair_obj_one (f g : X ⟶ Y) : (parallelPair f g).obj one = Y := rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPair_map_left** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：parallelPair_map_left (f g : X ⟶ Y) : (parallelPair f g).map left = f
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelPair_map_left (f g : X ⟶ Y) : (parallelPair f g).map left = f := rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPair_map_right** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：parallelPair_map_right (f g : X ⟶ Y) : (parallelPair f g).map right = g
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelPair_map_right (f g : X ⟶ Y) : (parallelPair f g).map right = g := rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPair_functor_obj** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：parallelPair_functor_obj {F : WalkingParallelPair ⥤ C} (j : WalkingParalle
lPair) : (parallelPair (F.map left) (F.map right)).obj j = F.obj j
参数：j : WalkingParallelPair。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem parallelPair_functor_obj {F : WalkingParallelPair ⥤ C} (j : WalkingParallelPair) :
    (parallelPair (F.map left) (F.map right)).obj j = F.obj j := by cases j <;> rfl

/-- Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal) to a
`parallelPair` -/
@[simps!]
/-
**CategoryTheory.Limits.diagramIsoParallelPair** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：diagramIsoParallelPair (F : WalkingParallelPair ⥤ C) : F ≅ parallelPair (F
.map left) (F.map right)
参数：F : WalkingParallelPair ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal)
 to a
`parallelPair`
-/
def diagramIsoParallelPair (F : WalkingParallelPair ⥤ C) :
    F ≅ parallelPair (F.map left) (F.map right) :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_ | _ | _) <;> simp)

/-- Constructor for natural transformations between parallel pairs. -/
@[simps]
/-
**CategoryTheory.Limits.parallelPairHomMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：parallelPairHomMk {F G : WalkingParallelPair ⥤ C} (p : F.obj zero ⟶ G.obj 
zero) (q : F.obj one ⟶ G.obj one) (hl : F.map left ≫ q = p ≫ G.map left
参数：p : F.obj zero ⟶ G.obj zero；q : F.obj one ⟶ G.obj one。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations between parallel pairs.
-/
def parallelPairHomMk {F G : WalkingParallelPair ⥤ C}
    (p : F.obj zero ⟶ G.obj zero)
    (q : F.obj one ⟶ G.obj one)
    (hl : F.map left ≫ q = p ≫ G.map left := by cat_disch)
    (hr : F.map right ≫ q = p ≫ G.map right := by cat_disch) : F ⟶ G where
  app := by rintro (_ | _); exacts [p, q]
  naturality := by rintro _ _ (_ | _); all_goals cat_disch

/-- Constructor for natural isomorphisms between parallel pairs. -/
@[simps!]
/-
**CategoryTheory.Limits.parallelPairIsoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：parallelPairIsoMk {F G : WalkingParallelPair ⥤ C} (p : F.obj zero ≅ G.obj 
zero) (q : F.obj one ≅ G.obj one) (hl : F.map left ≫ q.hom = p.hom ≫ G.map left
参数：p : F.obj zero ≅ G.obj zero；q : F.obj one ≅ G.obj one。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural isomorphisms between parallel pairs.
-/
def parallelPairIsoMk {F G : WalkingParallelPair ⥤ C}
    (p : F.obj zero ≅ G.obj zero)
    (q : F.obj one ≅ G.obj one)
    (hl : F.map left ≫ q.hom = p.hom ≫ G.map left := by cat_disch)
    (hr : F.map right ≫ q.hom = p.hom ≫ G.map right := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _); exacts [p, q])
    (by rintro _ _ (_ | _); all_goals cat_disch)

/-- Construct a morphism between parallel pairs. -/
/-
**CategoryTheory.Limits.parallelPairHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：parallelPairHom {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (
q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : parallelPair f g ⟶ par
allelPair f' g'
参数：f g : X ⟶ Y；f' g' : X' ⟶ Y'；p : X ⟶ X'；q : Y ⟶ Y'；wf : f ≫ q = p ≫ f'；wg : g 
≫ q = p ≫ g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between parallel pairs.
-/
def parallelPairHom {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : parallelPair f g ⟶ parallelPair f' g' :=
  parallelPairHomMk p q

/-- Construct a isomorphism between parallel pairs. -/
/-
**CategoryTheory.Limits.parallelPairIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：parallelPairIso {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ≅ X') (
q : Y ≅ Y') (wf : f ≫ q.hom = p.hom ≫ f') (wg : g ≫ q.hom = p.hom ≫ g') : parall
elPair f g ≅ parallelPair f' g'
参数：f g : X ⟶ Y；f' g' : X' ⟶ Y'；p : X ≅ X'；q : Y ≅ Y'；wf : f ≫ q.hom = p.hom ≫ f'
；wg : g ≫ q.hom = p.hom ≫ g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a isomorphism between parallel pairs.
-/
def parallelPairIso {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ≅ X') (q : Y ≅ Y')
    (wf : f ≫ q.hom = p.hom ≫ f') (wg : g ≫ q.hom = p.hom ≫ g') :
    parallelPair f g ≅ parallelPair f' g' := parallelPairIsoMk p q

@[simp]
/-
**CategoryTheory.Limits.parallelPairHom_app_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：parallelPairHom_app_zero {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : 
X ⟶ X') (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : (parallelPair
Hom f g f' g' p q wf wg).app zero = p
参数：f g : X ⟶ Y；f' g' : X' ⟶ Y'；p : X ⟶ X'；q : Y ⟶ Y'；wf : f ≫ q = p ≫ f'；wg : g 
≫ q = p ≫ g'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelPairHom_app_zero {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app zero = p :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.parallelPairHom_app_one** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：parallelPairHom_app_one {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X
 ⟶ X') (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : (parallelPairH
om f g f' g' p q wf wg).app one = q
参数：f g : X ⟶ Y；f' g' : X' ⟶ Y'；p : X ⟶ X'；q : Y ⟶ Y'；wf : f ≫ q = p ≫ f'；wg : g 
≫ q = p ≫ g'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelPairHom_app_one {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app one = q :=
  rfl

/-- Construct a natural isomorphism between functors out of the walking parallel pair from
its components. -/
@[simps!]
/-
**CategoryTheory.Limits.parallelPair.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.parallelPair`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F G : Ca
tegoryTheory.Functor CategoryTheory.Limits.WalkingParallelPair C} →       (zero 
:           F.obj CategoryTheory.Limits.WalkingParallelPair.zero ≅ G.obj Categor
yTheory.Limits.WalkingParallelPair.zero) →         (one :             F.obj Cate
goryTheory.Limits.WalkingParallelPair.one ≅ G.obj CategoryTheory.Limits.WalkingP
arallelPair.one) →           autoParam               (CategoryTheory.CategoryStr
uct.comp (F.map CategoryTheory.Limits.WalkingParallelPairHom.left) one.hom =    
             CategoryTheory.CategoryStruct.comp zero.hom (G.map CategoryTheory.L
imits.WalkingParallelPairHom.left))               CategoryTheory.Limits.parallel
Pair.ext._auto_1 →             autoParam                 (CategoryTheory.Categor
yStruct.comp (F.map CategoryTheory.Limits.WalkingParallelPairHom.right) one.hom 
=                   CategoryTheory.CategoryStruct.comp zero.hom                 
    (G.map CategoryTheory.Limits.WalkingParallelPairHom.right))                 
CategoryTheory.Limits.parallelPair.ext._auto_3 →               (F ≅ G)
参数：zero :           F.obj CategoryTheory.Limits.WalkingParallelPair.zero ≅ G.obj
 CategoryTheory.Limits.WalkingParallelPair.zero；one :             F.obj Category
Theory.Limits.WalkingParallelPair.one ≅ G.obj CategoryTheory.Limits.WalkingParal
lelPair.one；CategoryTheory.CategoryStruct.comp (F.map CategoryTheory.Limits.Walk
ingParallelPairHom.left) one.hom =                 CategoryTheory.CategoryStruct
.comp zero.hom (G.map CategoryTheory.Limits.WalkingParallelPairHom.left)；Categor
yTheory.CategoryStruct.comp (F.map CategoryTheory.Limits.WalkingParallelPairHom.
right) one.hom =                   CategoryTheory.CategoryStruct.comp zero.hom  
                   (G.map CategoryTheory.Limits.WalkingParallelPairHom.right)；F 
≅ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a natural isomorphism between functors out of the walking parallel pai
r from
its components.
-/
def parallelPair.ext {F G : WalkingParallelPair ⥤ C} (zero : F.obj zero ≅ G.obj zero)
    (one : F.obj one ≅ G.obj one)
    (left : F.map left ≫ one.hom = zero.hom ≫ G.map left := by cat_disch)
    (right : F.map right ≫ one.hom = zero.hom ≫ G.map right := by cat_disch) : F ≅ G :=
  NatIso.ofComponents
    (by
      rintro ⟨j⟩
      exacts [zero, one])
    (by rintro _ _ ⟨_⟩ <;> simp [left, right])

/-- Construct a natural isomorphism between `parallelPair f g` and `parallelPair f' g'` given
equalities `f = f'` and `g = g'`. -/
@[simps!]
/-
**CategoryTheory.Limits.parallelPair.eqOfHomEq** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.parallelPair`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g f' g' : X ⟶ Y} →         f = f' → g = g' → (CategoryTheory.Limits.
parallelPair f g ≅ CategoryTheory.Limits.parallelPair f' g')
参数：CategoryTheory.Limits.parallelPair f g ≅ CategoryTheory.Limits.parallelPair f
' g'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a natural isomorphism between `parallelPair f g` and `parallelPair f' 
g'` given
equalities `f = f'` and `g = g'`.
-/
def parallelPair.eqOfHomEq {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    parallelPair f g ≅ parallelPair f' g' :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])

/-- A fork on `f` and `g` is just a `Cone (parallelPair f g)`. -/
/-
**CategoryTheory.Limits.Fork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：Fork (f g : X ⟶ Y)
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fork on `f` and `g` is just a `Cone (parallelPair f g)`.
-/
abbrev Fork (f g : X ⟶ Y) :=
  Cone (parallelPair f g)

/-- A cofork on `f` and `g` is just a `Cocone (parallelPair f g)`. -/
/-
**CategoryTheory.Limits.Cofork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：Cofork (f g : X ⟶ Y)
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cofork on `f` and `g` is just a `Cocone (parallelPair f g)`.
-/
abbrev Cofork (f g : X ⟶ Y) :=
  Cocone (parallelPair f g)

variable {f g : X ⟶ Y}

/-- A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms
`t.π.app zero : t.pt ⟶ X` and `t.π.app one : t.pt ⟶ Y`. Of these,
only the first one is interesting, and we give it the shorter name `Fork.ι t`. -/
/-
**CategoryTheory.Limits.Fork.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms
`t.π.app zero : t.pt ⟶ X` and `t.π.app one : t.pt ⟶ Y`. Of these,
only the first one is interesting, and we give it the shorter name `Fork.ι t`.
-/
def Fork.ι (t : Fork f g) : t.pt ⟶ X :=
  t.π.app zero

@[simp]
/-
**CategoryTheory.Limits.Fork.app_zero_eq_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.app_zero_eq_ι (t : Fork f g) : t.π.app zero = t.ι :=
  rfl

/-- A cofork `t` on the parallelPair `f g : X ⟶ Y` consists of two morphisms
`t.ι.app zero : X ⟶ t.pt` and `t.ι.app one : Y ⟶ t.pt`. Of these, only the second one is
interesting, and we give it the shorter name `Cofork.π t`. -/
/-
**CategoryTheory.Limits.Cofork.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cofork `t` on the parallelPair `f g : X ⟶ Y` consists of two morphisms
`t.ι.app zero : X ⟶ t.pt` and `t.ι.app one : Y ⟶ t.pt`. Of these, only the secon
d one is
interesting, and we give it the shorter name `Cofork.π t`.
-/
def Cofork.π (t : Cofork f g) : Y ⟶ t.pt :=
  t.ι.app one

@[simp]
/-
**CategoryTheory.Limits.Cofork.app_one_eq_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cofork.app_one_eq_π (t : Cofork f g) : t.ι.app one = t.π :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Fork.app_one_eq_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.app_one_eq_ι_comp_left (s : Fork f g) : s.π.app one = s.ι ≫ f := by
  rw [← s.app_zero_eq_ι, ← s.w left, parallelPair_map_left]

@[reassoc]
/-
**CategoryTheory.Limits.Fork.app_one_eq_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.app_one_eq_ι_comp_right (s : Fork f g) : s.π.app one = s.ι ≫ g := by
  rw [← s.app_zero_eq_ι, ← s.w right, parallelPair_map_right]

@[simp]
/-
**CategoryTheory.Limits.Cofork.app_zero_eq_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cofork.app_zero_eq_comp_π_left (s : Cofork f g) : s.ι.app zero = f ≫ s.π := by
  rw [← s.app_one_eq_π, ← s.w left, parallelPair_map_left]

@[reassoc]
/-
**CategoryTheory.Limits.Cofork.app_zero_eq_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cofork.app_zero_eq_comp_π_right (s : Cofork f g) : s.ι.app zero = g ≫ s.π := by
  rw [← s.app_one_eq_π, ← s.w right, parallelPair_map_right]

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.Limits.Fork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι 
≫ f = ι ≫ g`.
-/
def Fork.ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : Fork f g where
  pt := P
  π :=
    { app := fun X => by
        cases X
        · exact ι
        · exact ι ≫ f
      naturality := fun {X} {Y} f =>
        by cases X <;> cases Y <;> cases f <;> simp [w] }

/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
`f ≫ π = g ≫ π`. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Limits.Cofork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
`f ≫ π = g ≫ π`.
-/
def Cofork.ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : Cofork f g where
  pt := P
  ι :=
    { app := fun X => WalkingParallelPair.casesOn X (f ≫ π) π
      naturality := fun i j f => by cases f <;> simp [w] }

@[simp]
/-
**CategoryTheory.Limits.Fork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.ι_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : (Fork.ofι ι w).ι = ι :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Cofork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cofork.π_ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : (Cofork.ofπ π w).π = π :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.Fork.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.Fork`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} (t : CategoryTheory.Limits.Fork f g),   CategoryTheory.CategoryStruct.com
p t.ι f = CategoryTheory.CategoryStruct.comp t.ι g
参数：t : CategoryTheory.Limits.Fork f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Fork.app_one_eq_ι_comp_left`：∀ {C : Type u} {X Y :
 C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheory.
Limits.Fork f g),   s.π.app CategoryThe…
· 使用定理 `CategoryTheory.Limits.Fork.app_one_eq_ι_comp_right`：∀ {C : Type u} {X Y 
: C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheory
.Limits.Fork f g),   s.π.app CategoryThe…
-/
theorem Fork.condition (t : Fork f g) : t.ι ≫ f = t.ι ≫ g := by
  rw [← t.app_one_eq_ι_comp_left, ← t.app_one_eq_ι_comp_right]

@[reassoc]
/-
**CategoryTheory.Limits.Cofork.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Cofork`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} (t : CategoryTheory.Limits.Cofork f g),   CategoryTheory.CategoryStruct.c
omp f t.π = CategoryTheory.CategoryStruct.comp g t.π
参数：t : CategoryTheory.Limits.Cofork f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cofork.app_zero_eq_comp_π_left`：∀ {C : Type u} {X 
Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheo
ry.Limits.Cofork f g),   s.ι.app CategoryT…
· 使用定理 `CategoryTheory.Limits.Cofork.app_zero_eq_comp_π_right`：∀ {C : Type u} {X
 Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryThe
ory.Limits.Cofork f g),   s.ι.app CategoryT…
-/
theorem Cofork.condition (t : Cofork f g) : f ≫ t.π = g ≫ t.π := by
  rw [← t.app_zero_eq_comp_π_left, ← t.app_zero_eq_comp_π_right]

/-- To check whether two maps are equalized by both maps of a fork, it suffices to check it for the
first map -/
/-
**CategoryTheory.Limits.Fork.equalizer_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.Fork`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} (s : CategoryTheory.Limits.Fork f g)   {W : C} {k l : W ⟶ s.pt},   Catego
ryTheory.CategoryStruct.comp k s.ι = CategoryTheory.CategoryStruct.comp l s.ι → 
    ∀ (j : CategoryTheory.Limits.WalkingParallelPair),       CategoryTheory.Cate
goryStruct.comp k (s.π.app j) = CategoryTheory.CategoryStruct.comp l (s.π.app j)
参数：s : CategoryTheory.Limits.Fork f g；j : CategoryTheory.Limits.WalkingParallelP
air；s.π.app j；s.π.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Fork.app_one_eq_ι_comp_left`：∀ {C : Type u} {X Y :
 C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheory.
Limits.Fork f g),   s.π.app CategoryThe…

--- 原说明 ---
To check whether two maps are equalized by both maps of a fork, it suffices to c
heck it for the
first map
-/
theorem Fork.equalizer_ext (s : Fork f g) {W : C} {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι) :
    ∀ j : WalkingParallelPair, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by
    have : k ≫ ι s ≫ f = l ≫ ι s ≫ f := by
      simp only [← Category.assoc]; exact congrArg (· ≫ f) h
    rw [s.app_one_eq_ι_comp_left, this]

/-- To check whether two maps are coequalized by both maps of a cofork, it suffices to check it for
the second map -/
/-
**CategoryTheory.Limits.Cofork.coequalizer_ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.Cofork`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} (s : CategoryTheory.Limits.Cofork f g)   {W : C} {k l : s.pt ⟶ W},   Cate
goryTheory.CategoryStruct.comp s.π k = CategoryTheory.CategoryStruct.comp s.π l 
→     ∀ (j : CategoryTheory.Limits.WalkingParallelPair),       CategoryTheory.Ca
tegoryStruct.comp (s.ι.app j) k = CategoryTheory.CategoryStruct.comp (s.ι.app j)
 l
参数：s : CategoryTheory.Limits.Cofork f g；j : CategoryTheory.Limits.WalkingParalle
lPair；s.ι.app j；s.ι.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Cofork.app_zero_eq_comp_π_left`：∀ {C : Type u} {X 
Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheo
ry.Limits.Cofork f g),   s.ι.app CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
To check whether two maps are coequalized by both maps of a cofork, it suffices 
to check it for
the second map
-/
theorem Cofork.coequalizer_ext (s : Cofork f g) {W : C} {k l : s.pt ⟶ W}
    (h : Cofork.π s ≫ k = Cofork.π s ≫ l) : ∀ j : WalkingParallelPair, s.ι.app j ≫ k = s.ι.app j ≫ l
  | zero => by simp only [s.app_zero_eq_comp_π_left, Category.assoc, h]
  | one => h
/-
**CategoryTheory.Limits.Fork.IsLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Fork.IsLimit`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} {s : CategoryTheory.Limits.Fork f g}   (hs : CategoryTheory.Limits.IsLimi
t s) {W : C} {k l : W ⟶ s.pt},   CategoryTheory.CategoryStruct.comp k s.ι = Cate
goryTheory.CategoryStruct.comp l s.ι → k = l
参数：hs : CategoryTheory.Limits.IsLimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Limits.Fork.equalizer_ext`：∀ {C : Type u} {X Y : C} [inst
 : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheory.Limits.Fo
rk f g)   {W : C} {k l : W ⟶ s…
-/
theorem Fork.IsLimit.hom_ext {s : Fork f g} (hs : IsLimit s) {W : C} {k l : W ⟶ s.pt}
    (h : k ≫ Fork.ι s = l ≫ Fork.ι s) : k = l :=
  hs.hom_ext <| Fork.equalizer_ext _ h
/-
**CategoryTheory.Limits.Cofork.IsColimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Cofork.IsColimit`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} {s : CategoryTheory.Limits.Cofork f g}   (hs : CategoryTheory.Limits.IsCo
limit s) {W : C} {k l : s.pt ⟶ W},   CategoryTheory.CategoryStruct.comp s.π k = 
CategoryTheory.CategoryStruct.comp s.π l → k = l
参数：hs : CategoryTheory.Limits.IsColimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Cofork.coequalizer_ext`：∀ {C : Type u} {X Y : C} [
inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (s : CategoryTheory.Limit
s.Cofork f g)   {W : C} {k l : s.p…
-/
theorem Cofork.IsColimit.hom_ext {s : Cofork f g} (hs : IsColimit s) {W : C} {k l : s.pt ⟶ W}
    (h : Cofork.π s ≫ k = Cofork.π s ≫ l) : k = l :=
  hs.hom_ext <| Cofork.coequalizer_ext _ h

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Fork.IsLimit.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.IsLimit.lift_ι {s t : Fork f g} (hs : IsLimit s) : hs.lift t ≫ s.ι = t.ι :=
  hs.fac _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Cofork.IsColimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cofork.IsColimit.π_desc {s t : Cofork f g} (hs : IsColimit s) : s.π ≫ hs.desc t = t.π :=
  hs.fac _ _

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
`k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`. -/
/-
**CategoryTheory.Limits.Fork.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.Fork.IsLimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s : CategoryTheory.Limits.Fork f g} →         
  CategoryTheory.Limits.IsLimit s →             {W : C} →               (k : W ⟶
 X) → CategoryTheory.CategoryStruct.comp k f = CategoryTheory.CategoryStruct.com
p k g → (W ⟶ s.pt)
参数：k : W ⟶ X；W ⟶ s.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
`k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`.
-/
def Fork.IsLimit.lift {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ s.pt :=
  hs.lift (Fork.ofι _ h)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Fork.IsLimit.lift_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Fork.IsLimit.lift_ι' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    Fork.IsLimit.lift hs k h ≫ Fork.ι s = k :=
    hs.fac _ _

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
`k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`. -/
/-
**CategoryTheory.Limits.Fork.IsLimit.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Fork.IsLimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s : CategoryTheory.Limits.Fork f g} →         
  CategoryTheory.Limits.IsLimit s →             {W : C} →               (k : W ⟶
 X) →                 CategoryTheory.CategoryStruct.comp k f = CategoryTheory.Ca
tegoryStruct.comp k g →                   { l // CategoryTheory.CategoryStruct.c
omp l s.ι = k }
参数：k : W ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
`k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`.
-/
def Fork.IsLimit.lift' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
  ⟨Fork.IsLimit.lift hs k h, by simp⟩
/-
**CategoryTheory.Limits.Fork.IsLimit.mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Fork.IsLimit`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} {s : CategoryTheory.Limits.Fork f g}   (hs : CategoryTheory.Limits.IsLimi
t s), CategoryTheory.Mono s.ι
参数：hs : CategoryTheory.Limits.IsLimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
-/
lemma Fork.IsLimit.mono {s : Fork f g} (hs : IsLimit s) : Mono s.ι where
  right_cancellation _ _ h := hom_ext hs h

/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
`f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`. -/
/-
**CategoryTheory.Limits.Cofork.IsColimit.desc** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.Cofork.IsColimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s : CategoryTheory.Limits.Cofork f g} →       
    CategoryTheory.Limits.IsColimit s →             {W : C} →               (k :
 Y ⟶ W) → CategoryTheory.CategoryStruct.comp f k = CategoryTheory.CategoryStruct
.comp g k → (s.pt ⟶ W)
参数：k : Y ⟶ W；s.pt ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfy
ing
`f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`
.
-/
def Cofork.IsColimit.desc {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : s.pt ⟶ W :=
  hs.desc (Cofork.ofπ _ h)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Cofork.IsColimit.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cofork.IsColimit.π_desc' {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : Cofork.π s ≫ Cofork.IsColimit.desc hs k h = k :=
  hs.fac _ _

/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
`f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`. -/
/-
**CategoryTheory.Limits.Cofork.IsColimit.desc'** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Cofork.IsColimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s : CategoryTheory.Limits.Cofork f g} →       
    CategoryTheory.Limits.IsColimit s →             {W : C} →               (k :
 Y ⟶ W) →                 CategoryTheory.CategoryStruct.comp f k = CategoryTheor
y.CategoryStruct.comp g k →                   { l // CategoryTheory.CategoryStru
ct.comp s.π l = k }
参数：k : Y ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfy
ing
`f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`
.
-/
def Cofork.IsColimit.desc' {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : { l : s.pt ⟶ W // Cofork.π s ≫ l = k } :=
  ⟨Cofork.IsColimit.desc hs k h, by simp⟩
/-
**CategoryTheory.Limits.Cofork.IsColimit.epi** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Cofork.IsColimit`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} {s : CategoryTheory.Limits.Cofork f g}   (hs : CategoryTheory.Limits.IsCo
limit s), CategoryTheory.Epi s.π
参数：hs : CategoryTheory.Limits.IsColimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
-/
lemma Cofork.IsColimit.epi {s : Cofork f g} (hs : IsColimit s) : Epi s.π where
  left_cancellation _ _ h := hom_ext hs h
/-
**CategoryTheory.Limits.Fork.IsLimit.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Fork.IsLimit`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} {s : CategoryTheory.Limits.Fork f g}   (hs : CategoryTheory.Limits.IsLimi
t s) {W : C} (k : W ⟶ X),   CategoryTheory.CategoryStruct.comp k f = CategoryThe
ory.CategoryStruct.comp k g →     ∃! l, CategoryTheory.CategoryStruct.comp l s.ι
 = k
参数：hs : CategoryTheory.Limits.IsLimit s；k : W ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Fork.IsLimit.existsUnique {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = k ≫ g) : ∃! l : W ⟶ s.pt, l ≫ Fork.ι s = k :=
  ⟨hs.lift <| Fork.ofι _ h, hs.fac _ _, fun _ hm =>
    Fork.IsLimit.hom_ext hs <| hm.symm ▸ (hs.fac (Fork.ofι _ h) WalkingParallelPair.zero).symm⟩
/-
**CategoryTheory.Limits.Cofork.IsColimit.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Cofork.IsColimit`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y} {s : CategoryTheory.Limits.Cofork f g}   (hs : CategoryTheory.Limits.IsCo
limit s) {W : C} (k : Y ⟶ W),   CategoryTheory.CategoryStruct.comp f k = Categor
yTheory.CategoryStruct.comp g k →     ∃! d, CategoryTheory.CategoryStruct.comp s
.π d = k
参数：hs : CategoryTheory.Limits.IsColimit s；k : Y ⟶ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Cofork.IsColimit.existsUnique {s : Cofork f g} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = g ≫ k) : ∃! d : s.pt ⟶ W, Cofork.π s ≫ d = k :=
  ⟨hs.desc <| Cofork.ofπ _ h, hs.fac _ _, fun _ hm =>
    Cofork.IsColimit.hom_ext hs <| hm.symm ▸ (hs.fac (Cofork.ofπ _ h) WalkingParallelPair.one).symm⟩

/-- This is a slightly more convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[simps]
/-
**CategoryTheory.Limits.Fork.IsLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Fork.IsLimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         (t : CategoryTheory.Limits.Fork f g) →         
  (lift : (s : CategoryTheory.Limits.Fork f g) → s.pt ⟶ t.pt) →             (∀ (
s : CategoryTheory.Limits.Fork f g), CategoryTheory.CategoryStruct.comp (lift s)
 t.ι = s.ι) →               (∀ (s : CategoryTheory.Limits.Fork f g) (m : s.pt ⟶ 
t.pt),                   CategoryTheory.CategoryStruct.comp m t.ι = s.ι → m = li
ft s) →                 CategoryTheory.Limits.IsLimit t
参数：t : CategoryTheory.Limits.Fork f g；lift : (s : CategoryTheory.Limits.Fork f g
) → s.pt ⟶ t.pt；∀ (s : CategoryTheory.Limits.Fork f g), CategoryTheory.CategoryS
truct.comp (lift s) t.ι = s.ι；∀ (s : CategoryTheory.Limits.Fork f g) (m : s.pt ⟶
 t.pt),                   CategoryTheory.CategoryStruct.comp m t.ι = s.ι → m = l
ift s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a fork is a limit cone.
 It
only asks for a proof of facts that carry any mathematical content
-/
def Fork.IsLimit.mk (t : Fork f g) (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s)
    (uniq : ∀ (s : Fork f g) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j =>
      WalkingParallelPair.casesOn j (fac s) <| by
        simp [← Category.assoc, fac]
    uniq := fun s m j => by aesop }

/-- This is another convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
/-
**CategoryTheory.Limits.Fork.IsLimit.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Fork.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         (t : CategoryTheory.Limits.Fork f g) →         
  ((s : CategoryTheory.Limits.Fork f g) →               { l //                 C
ategoryTheory.CategoryStruct.comp l t.ι = s.ι ∧                   ∀ {m : s.pt ⟶ 
t.pt}, CategoryTheory.CategoryStruct.comp m t.ι = s.ι → m = l }) →             C
ategoryTheory.Limits.IsLimit t
参数：t : CategoryTheory.Limits.Fork f g；(s : CategoryTheory.Limits.Fork f g) →    
           { l //                 CategoryTheory.CategoryStruct.comp l t.ι = s.ι
 ∧                   ∀ {m : s.pt ⟶ t.pt}, CategoryTheory.CategoryStruct.comp m t
.ι = s.ι → m = l }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows a
ccess to the
same `s` for all parts.
-/
def Fork.IsLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : ∀ s : Fork f g, { l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l }) : IsLimit t :=
  Fork.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w => (create s).2.2 w

/-- This is a slightly more convenient method to verify that a cofork is a colimit cocone. It
only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.Cofork.IsColimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Cofork.IsColimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         (t : CategoryTheory.Limits.Cofork f g) →       
    (desc : (s : CategoryTheory.Limits.Cofork f g) → t.pt ⟶ s.pt) →             
(∀ (s : CategoryTheory.Limits.Cofork f g), CategoryTheory.CategoryStruct.comp t.
π (desc s) = s.π) →               (∀ (s : CategoryTheory.Limits.Cofork f g) (m :
 t.pt ⟶ s.pt),                   CategoryTheory.CategoryStruct.comp t.π m = s.π 
→ m = desc s) →                 CategoryTheory.Limits.IsColimit t
参数：t : CategoryTheory.Limits.Cofork f g；desc : (s : CategoryTheory.Limits.Cofork
 f g) → t.pt ⟶ s.pt；∀ (s : CategoryTheory.Limits.Cofork f g), CategoryTheory.Cat
egoryStruct.comp t.π (desc s) = s.π；∀ (s : CategoryTheory.Limits.Cofork f g) (m 
: t.pt ⟶ s.pt),                   CategoryTheory.CategoryStruct.comp t.π m = s.π
 → m = desc s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a cofork is a colimit c
ocone. It
only asks for a proof of facts that carry any mathematical content
-/
def Cofork.IsColimit.mk (t : Cofork f g) (desc : ∀ s : Cofork f g, t.pt ⟶ s.pt)
    (fac : ∀ s : Cofork f g, Cofork.π t ≫ desc s = Cofork.π s)
    (uniq : ∀ (s : Cofork f g) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s) : IsColimit t :=
  { desc
    fac := fun s j =>
      WalkingParallelPair.casesOn j (by simp_all) (fac s)
    uniq := by aesop }

/-- This is another convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
/-
**CategoryTheory.Limits.Cofork.IsColimit.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Cofork.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         (t : CategoryTheory.Limits.Cofork f g) →       
    ((s : CategoryTheory.Limits.Cofork f g) →               { l //              
   CategoryTheory.CategoryStruct.comp t.π l = s.π ∧                   ∀ {m : t.p
t ⟶ s.pt}, CategoryTheory.CategoryStruct.comp t.π m = s.π → m = l }) →          
   CategoryTheory.Limits.IsColimit t
参数：t : CategoryTheory.Limits.Cofork f g；(s : CategoryTheory.Limits.Cofork f g) →
               { l //                 CategoryTheory.CategoryStruct.comp t.π l =
 s.π ∧                   ∀ {m : t.pt ⟶ s.pt}, CategoryTheory.CategoryStruct.comp
 t.π m = s.π → m = l }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows a
ccess to the
same `s` for all parts.
-/
def Cofork.IsColimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Cofork f g)
    (create : ∀ s : Cofork f g, { l : t.pt ⟶ s.pt // t.π ≫ l = s.π
                                    ∧ ∀ {m}, t.π ≫ m = s.π → m = l }) : IsColimit t :=
  Cofork.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 w

/-- Noncomputably make a limit cone from the existence of unique factorizations. -/
/-
**CategoryTheory.Limits.Fork.IsLimit.ofExistsUnique** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Fork.IsLimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {t : CategoryTheory.Limits.Fork f g} →         
  (∀ (s : CategoryTheory.Limits.Fork f g), ∃! l, CategoryTheory.CategoryStruct.c
omp l t.ι = s.ι) →             CategoryTheory.Limits.IsLimit t
参数：∀ (s : CategoryTheory.Limits.Fork f g), ∃! l, CategoryTheory.CategoryStruct.c
omp l t.ι = s.ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputably make a limit cone from the existence of unique factorizations.
-/
noncomputable def Fork.IsLimit.ofExistsUnique {t : Fork f g}
    (hs : ∀ s : Fork f g, ∃! l : s.pt ⟶ t.pt, l ≫ Fork.ι t = Fork.ι s) : IsLimit t := by
  choose d hd hd' using hs
  exact Fork.IsLimit.mk _ d hd fun s m hm => hd' _ _ hm

/-- Noncomputably make a colimit cocone from the existence of unique factorizations. -/
/-
**CategoryTheory.Limits.Cofork.IsColimit.ofExistsUnique** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.Cofork.IsColimit`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {t : CategoryTheory.Limits.Cofork f g} →       
    (∀ (s : CategoryTheory.Limits.Cofork f g), ∃! d, CategoryTheory.CategoryStru
ct.comp t.π d = s.π) →             CategoryTheory.Limits.IsColimit t
参数：∀ (s : CategoryTheory.Limits.Cofork f g), ∃! d, CategoryTheory.CategoryStruct
.comp t.π d = s.π。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Noncomputably make a colimit cocone from the existence of unique factorizations.
-/
noncomputable def Cofork.IsColimit.ofExistsUnique {t : Cofork f g}
    (hs : ∀ s : Cofork f g, ∃! d : t.pt ⟶ s.pt, Cofork.π t ≫ d = Cofork.π s) : IsColimit t := by
  choose d hd hd' using hs
  exact Cofork.IsColimit.mk _ d hd fun s m hm => hd' _ _ hm

/--
Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` to its point are in
bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `Fork.IsLimit.homIso_natural`.
This is a special case of `IsLimit.homIso'`, often useful to construct adjunctions.
-/
@[simps]
/-
**CategoryTheory.Limits.Fork.IsLimit.homIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Fork.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         {t : CategoryTheory.Limits.Fork f g} →         
  CategoryTheory.Limits.IsLimit t →             (Z : C) →               (Z ⟶ t.p
t) ≃ { h // CategoryTheory.CategoryStruct.comp h f = CategoryTheory.CategoryStru
ct.comp h g }
参数：Z : C；Z ⟶ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` t
o its point are in
bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `Fork.IsLimit.homIso_natural`.
This is a special case of `IsLimit.homIso'`, often useful to construct adjunctio
ns.
-/
def Fork.IsLimit.homIso {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.pt) ≃ { h : Z ⟶ X // h ≫ f = h ≫ g } where
  toFun k := ⟨k ≫ t.ι, by simp only [Category.assoc, t.condition]⟩
  invFun h := (Fork.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Fork.IsLimit.hom_ext ht (Fork.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Fork.IsLimit.lift' ht _ _).prop

/-- The bijection of `Fork.IsLimit.homIso` is natural in `Z`. -/
/-
**CategoryTheory.Limits.Fork.IsLimit.homIso_natural** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.Fork.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f g : 
X ⟶ Y} {t : CategoryTheory.Limits.Fork f g}   (ht : CategoryTheory.Limits.IsLimi
t t) {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.pt),   ↑((CategoryTheory.Limits.Fork.IsL
imit.homIso ht Z') (CategoryTheory.CategoryStruct.comp q k)) =     CategoryTheor
y.CategoryStruct.comp q ↑((CategoryTheory.Limits.Fork.IsLimit.homIso ht Z) k)
参数：ht : CategoryTheory.Limits.IsLimit t；q : Z' ⟶ Z；k : Z ⟶ t.pt；(CategoryTheory.
Limits.Fork.IsLimit.homIso ht Z') (CategoryTheory.CategoryStruct.comp q k)；(Cate
goryTheory.Limits.Fork.IsLimit.homIso ht Z) k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
The bijection of `Fork.IsLimit.homIso` is natural in `Z`.
-/
theorem Fork.IsLimit.homIso_natural {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t)
    {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.pt) :
    (Fork.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (Fork.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _

/-- Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from the cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `Cofork.IsColimit.homIso_natural`.
This is a special case of `IsColimit.homIso'`, often useful to construct adjunctions.
-/
@[simps]
/-
**CategoryTheory.Limits.Cofork.IsColimit.homIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Cofork.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         {t : CategoryTheory.Limits.Cofork f g} →       
    CategoryTheory.Limits.IsColimit t →             (Z : C) →               (t.p
t ⟶ Z) ≃ { h // CategoryTheory.CategoryStruct.comp f h = CategoryTheory.Category
Struct.comp g h }
参数：Z : C；t.pt ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from t
he cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `Cofork.IsColimit.homIso_natural`
.
This is a special case of `IsColimit.homIso'`, often useful to construct adjunct
ions.
-/
def Cofork.IsColimit.homIso {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} (ht : IsColimit t) (Z : C) :
    (t.pt ⟶ Z) ≃ { h : Y ⟶ Z // f ≫ h = g ≫ h } where
  toFun k := ⟨t.π ≫ k, by simp only [← Category.assoc, t.condition]⟩
  invFun h := (Cofork.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cofork.IsColimit.hom_ext ht (Cofork.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cofork.IsColimit.desc' ht _ _).prop

/-- The bijection of `Cofork.IsColimit.homIso` is natural in `Z`. -/
/-
**CategoryTheory.Limits.Cofork.IsColimit.homIso_natural** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.Cofork.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f g : 
X ⟶ Y} {t : CategoryTheory.Limits.Cofork f g}   {Z Z' : C} (q : Z ⟶ Z') (ht : Ca
tegoryTheory.Limits.IsColimit t) (k : t.pt ⟶ Z),   ↑((CategoryTheory.Limits.Cofo
rk.IsColimit.homIso ht Z') (CategoryTheory.CategoryStruct.comp k q)) =     Categ
oryTheory.CategoryStruct.comp (↑((CategoryTheory.Limits.Cofork.IsColimit.homIso 
ht Z) k)) q
参数：q : Z ⟶ Z'；ht : CategoryTheory.Limits.IsColimit t；k : t.pt ⟶ Z；(CategoryTheor
y.Limits.Cofork.IsColimit.homIso ht Z') (CategoryTheory.CategoryStruct.comp k q)
；↑((CategoryTheory.Limits.Cofork.IsColimit.homIso ht Z) k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
The bijection of `Cofork.IsColimit.homIso` is natural in `Z`.
-/
theorem Cofork.IsColimit.homIso_natural {X Y : C} {f g : X ⟶ Y} {t : Cofork f g} {Z Z' : C}
    (q : Z ⟶ Z') (ht : IsColimit t) (k : t.pt ⟶ Z) :
    (Cofork.IsColimit.homIso ht _ (k ≫ q) : Y ⟶ Z') =
      (Cofork.IsColimit.homIso ht _ k : Y ⟶ Z) ≫ q :=
  (Category.assoc _ _ _).symm

/-- This is a helper construction that can be useful when verifying that a category has all
equalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)`, and a fork on `F.map left` and `F.map right`,
we get a cone on `F`.

If you're thinking about using this, have a look at `hasEqualizers_of_hasLimit_parallelPair`,
which you may find to be an easier way of achieving your goal. -/
/-
**CategoryTheory.Limits.Cone.ofFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Cone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingParallelPair C} →       Category
Theory.Limits.Fork (F.map CategoryTheory.Limits.WalkingParallelPairHom.left)    
       (F.map CategoryTheory.Limits.WalkingParallelPairHom.right) →         Cate
goryTheory.Limits.Cone F
参数：F.map CategoryTheory.Limits.WalkingParallelPairHom.left；F.map CategoryTheory.
Limits.WalkingParallelPairHom.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a helper construction that can be useful when verifying that a category 
has all
equalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)`, and a fork on `F.map left` and `F.map
 right`,
we get a cone on `F`.

If you're thinking about using this, have a look at `hasEqualizers_of_hasLimit_p
arallelPair`,
which you may find to be an easier way of achieving your goal.
-/
def Cone.ofFork {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) : Cone F where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by simp)
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

/-- This is a helper construction that can be useful when verifying that a category has all
coequalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)`, and a cofork on `F.map left` and `F.map right`,
we get a cocone on `F`.

If you're thinking about using this, have a look at
`hasCoequalizers_of_hasColimit_parallelPair`, which you may find to be an easier way of
achieving your goal. -/
/-
**CategoryTheory.Limits.Cocone.ofCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Cocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingParallelPair C} →       Category
Theory.Limits.Cofork (F.map CategoryTheory.Limits.WalkingParallelPairHom.left)  
         (F.map CategoryTheory.Limits.WalkingParallelPairHom.right) →         Ca
tegoryTheory.Limits.Cocone F
参数：F.map CategoryTheory.Limits.WalkingParallelPairHom.left；F.map CategoryTheory.
Limits.WalkingParallelPairHom.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a helper construction that can be useful when verifying that a category 
has all
coequalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)`, and a cofork on `F.map left` and `F.m
ap right`,
we get a cocone on `F`.

If you're thinking about using this, have a look at
`hasCoequalizers_of_hasColimit_parallelPair`, which you may find to be an easier
 way of
achieving your goal.
-/
def Cocone.ofCofork {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right)) :
    Cocone F where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by simp) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

@[simp]
/-
**CategoryTheory.Limits.Cone.ofFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cone.ofFork_π {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) (j) :
    (Cone.ofFork t).π.app j = t.π.app j ≫ eqToHom (by simp) := rfl

@[simp]
/-
**CategoryTheory.Limits.Cocone.ofCofork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cocone.ofCofork_ι {F : WalkingParallelPair ⥤ C} (t : Cofork (F.map left) (F.map right))
    (j) : (Cocone.ofCofork t).ι.app j = eqToHom (by simp) ≫ t.ι.app j := rfl

/-- Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)` and a cone on `F`, we get a fork on
`F.map left` and `F.map right`. -/
/-
**CategoryTheory.Limits.Fork.ofCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Fork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingParallelPair C} →       Category
Theory.Limits.Cone F →         CategoryTheory.Limits.Fork (F.map CategoryTheory.
Limits.WalkingParallelPairHom.left)           (F.map CategoryTheory.Limits.Walki
ngParallelPairHom.right)
参数：F.map CategoryTheory.Limits.WalkingParallelPairHom.left；F.map CategoryTheory.
Limits.WalkingParallelPairHom.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)` and a cone on `F`, we get a fork on
`F.map left` and `F.map right`.
-/
def Fork.ofCone {F : WalkingParallelPair ⥤ C} (t : Cone F) : Fork (F.map left) (F.map right) where
  pt := t.pt
  π := { app := fun X => t.π.app X ≫ eqToHom (by simp)
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

/-- Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)` and a cocone on `F`, we get a cofork on
`F.map left` and `F.map right`. -/
/-
**CategoryTheory.Limits.Cofork.ofCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Cofork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingParallelPair C} →       Category
Theory.Limits.Cocone F →         CategoryTheory.Limits.Cofork (F.map CategoryThe
ory.Limits.WalkingParallelPairHom.left)           (F.map CategoryTheory.Limits.W
alkingParallelPairHom.right)
参数：F.map CategoryTheory.Limits.WalkingParallelPairHom.left；F.map CategoryTheory.
Limits.WalkingParallelPairHom.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)` and a cocone on `F`, we get a cofork o
n
`F.map left` and `F.map right`.
-/
def Cofork.ofCocone {F : WalkingParallelPair ⥤ C} (t : Cocone F) :
    Cofork (F.map left) (F.map right) where
  pt := t.pt
  ι := { app := fun X => eqToHom (by simp) ≫ t.ι.app X
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

@[simp]
/-
**CategoryTheory.Limits.Fork.ofCone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.ofCone_π {F : WalkingParallelPair ⥤ C} (t : Cone F) (j) :
    (Fork.ofCone t).π.app j = t.π.app j ≫ eqToHom (by simp) := rfl

@[simp]
/-
**CategoryTheory.Limits.Cofork.ofCocone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cofork.ofCocone_ι {F : WalkingParallelPair ⥤ C} (t : Cocone F) (j) :
    (Cofork.ofCocone t).ι.app j = eqToHom (by simp) ≫ t.ι.app j := rfl

@[simp]
/-
**CategoryTheory.Limits.Fork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.ι_postcompose {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
    {c : Fork f g} : Fork.ι ((Cone.postcompose α).obj c) = c.ι ≫ α.app .zero :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Cofork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cofork.π_precompose {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
    {c : Cofork f' g'} :
    Cofork.π ((Cocone.precompose α).obj c) = α.app .one ≫ c.π := rfl

/-- Helper function for constructing morphisms between equalizer forks.
-/
@[simps]
/-
**CategoryTheory.Limits.Fork.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Fork`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s t : CategoryTheory.Limits.Fork f g} →       
    (k : s.pt ⟶ t.pt) → CategoryTheory.CategoryStruct.comp k t.ι = s.ι → (s ⟶ t)
参数：k : s.pt ⟶ t.pt；s ⟶ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for constructing morphisms between equalizer forks.
-/
def Fork.mkHom {s t : Fork f g} (k : s.pt ⟶ t.pt) (w : k ≫ t.ι = s.ι) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simp only [Fork.app_one_eq_ι_comp_left, ← Category.assoc]
      congr

/-- To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
/-
**CategoryTheory.Limits.Fork.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.Fork`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s t : CategoryTheory.Limits.Fork f g} →       
    (i : s.pt ≅ t.pt) →             autoParam (CategoryTheory.CategoryStruct.com
p i.hom t.ι = s.ι) CategoryTheory.Limits.Fork.ext._auto_1 →               (s ≅ t
)
参数：i : s.pt ≅ t.pt；CategoryTheory.CategoryStruct.comp i.hom t.ι = s.ι；s ≅ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
def Fork.ext {s t : Fork f g} (i : s.pt ≅ t.pt) (w : i.hom ≫ t.ι = s.ι := by cat_disch) :
    s ≅ t where
  hom := Fork.mkHom i.hom w
  inv := Fork.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

/-- Two forks of the form `ofι` are isomorphic whenever their `ι`'s are equal. -/
/-
**CategoryTheory.Limits.ForkOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two forks of the form `ofι` are isomorphic whenever their `ι`'s are equal.
-/
def ForkOfι.ext {P : C} {ι ι' : P ⟶ X} (w : ι ≫ f = ι ≫ g) (w' : ι' ≫ f = ι' ≫ g) (h : ι = ι') :
    Fork.ofι ι w ≅ Fork.ofι ι' w' :=
  Fork.ext (Iso.refl _) (by simp [h])

/-- Every fork is isomorphic to one of the form `Fork.of_ι _ _`. -/
@[simps!]
/-
**CategoryTheory.Limits.Fork.isoForkOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every fork is isomorphic to one of the form `Fork.of_ι _ _`.
-/
def Fork.isoForkOfι (c : Fork f g) : c ≅ Fork.ofι c.ι c.condition :=
  Fork.ext (Iso.refl _)

/--
If `f, g : X ⟶ Y` and `f', g : X' ⟶ Y'` pairwise form a commutative square with isomorphisms
`X ≅ X'` and `Y ≅ Y'`, the categories of forks are equivalent.
-/
/-
**CategoryTheory.Limits.Fork.equivOfIsos** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Fork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         {X' Y' : C} →           {f' g' : X' ⟶ Y'} →    
         (e₀ : X ≅ X') →               (e₁ : Y ≅ Y') →                 autoParam
 (CategoryTheory.CategoryStruct.comp e₀.hom f' = CategoryTheory.CategoryStruct.c
omp f e₁.hom)                     CategoryTheory.Limits.Fork.equivOfIsos._auto_1
 →                   autoParam (CategoryTheory.CategoryStruct.comp e₀.hom g' = C
ategoryTheory.CategoryStruct.comp g e₁.hom)                       CategoryTheory
.Limits.Fork.equivOfIsos._auto_3 →                     (CategoryTheory.Limits.Fo
rk f g ≌ CategoryTheory.Limits.Fork f' g')
参数：e₀ : X ≅ X'；e₁ : Y ≅ Y'；CategoryTheory.CategoryStruct.comp e₀.hom f' = Catego
ryTheory.CategoryStruct.comp f e₁.hom；CategoryTheory.CategoryStruct.comp e₀.hom 
g' = CategoryTheory.CategoryStruct.comp g e₁.hom；CategoryTheory.Limits.Fork f g 
≌ CategoryTheory.Limits.Fork f' g'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f, g : X ⟶ Y` and `f', g : X' ⟶ Y'` pairwise form a commutative square with 
isomorphisms
`X ≅ X'` and `Y ≅ Y'`, the categories of forks are equivalent.
-/
def Fork.equivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) :
    Fork f g ≌ Fork f' g' :=
  Cone.postcomposeEquivalence <|
    parallelPair.ext e₀ e₁ (by simp [comm₁]) (by simp [comm₂])

@[simp]
/-
**CategoryTheory.Limits.Fork.equivOfIsos_functor_obj_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Fork.equivOfIsos_functor_obj_ι {X Y : C} {f g : X ⟶ Y}
    {X' Y' : C} {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) (c : Fork f g) :
    ((Fork.equivOfIsos e₀ e₁ comm₁ comm₂).functor.obj c).ι = c.ι ≫ e₀.hom :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Fork.equivOfIsos_inverse_obj_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Fork.equivOfIsos_inverse_obj_ι {X Y : C} {f g : X ⟶ Y}
    {X' Y' : C} {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) (c : Fork f' g') :
    ((Fork.equivOfIsos e₀ e₁ comm₁ comm₂).inverse.obj c).ι = c.ι ≫ e₀.inv :=
  rfl

/--
Given two forks with isomorphic components in such a way that the natural diagrams commute, then
one is a limit if and only if the other one is.
-/
/-
**CategoryTheory.Limits.Fork.isLimitEquivOfIsos** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Fork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         {X' Y' : C} →           (c : CategoryTheory.Lim
its.Fork f g) →             {f' g' : X' ⟶ Y'} →               (c' : CategoryTheo
ry.Limits.Fork f' g') →                 (e₀ : X ≅ X') →                   (e₁ : 
Y ≅ Y') →                     (e : c.pt ≅ c'.pt) →                       autoPar
am                           (CategoryTheory.CategoryStruct.comp e₀.hom f' = Cat
egoryTheory.CategoryStruct.comp f e₁.hom)                           CategoryTheo
ry.Limits.Fork.isLimitEquivOfIsos._auto_1 →                         autoParam   
                          (CategoryTheory.CategoryStruct.comp e₀.hom g' = Catego
ryTheory.CategoryStruct.comp g e₁.hom)                             CategoryTheor
y.Limits.Fork.isLimitEquivOfIsos._auto_3 →                           autoParam  
                             (CategoryTheory.CategoryStruct.comp e.hom c'.ι =   
                              CategoryTheory.CategoryStruct.comp c.ι e₀.hom)    
                           CategoryTheory.Limits.Fork.isLimitEquivOfIsos._auto_5
 →                             CategoryTheory.Limits.IsLimit c ≃ CategoryTheory.
Limits.IsLimit c'
参数：c : CategoryTheory.Limits.Fork f g；c' : CategoryTheory.Limits.Fork f' g'；e₀ :
 X ≅ X'；e₁ : Y ≅ Y'；e : c.pt ≅ c'.pt；CategoryTheory.CategoryStruct.comp e₀.hom f
' = CategoryTheory.CategoryStruct.comp f e₁.hom；CategoryTheory.CategoryStruct.co
mp e₀.hom g' = CategoryTheory.CategoryStruct.comp g e₁.hom；CategoryTheory.Catego
ryStruct.comp e.hom c'.ι =                                 CategoryTheory.Catego
ryStruct.comp c.ι e₀.hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two forks with isomorphic components in such a way that the natural diagra
ms commute, then
one is a limit if and only if the other one is.
-/
def Fork.isLimitEquivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    (c : Fork f g)
    {f' g' : X' ⟶ Y'} (c' : Fork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₀.hom := by cat_disch) :
    IsLimit c ≃ IsLimit c' :=
  let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsLimit.equivOfNatIsoOfIso i c c' (Fork.ext e comm₃)

/--
Given two forks with isomorphic components in such a way that the natural diagrams commute, then if
one is a limit, then the other one is as well.
-/
/-
**CategoryTheory.Limits.Fork.isLimitOfIsos** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Fork`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {X' Y' : C} →           (c : CategoryTheory.Lim
its.Fork f g) →             CategoryTheory.Limits.IsLimit c →               {f' 
g' : X' ⟶ Y'} →                 (c' : CategoryTheory.Limits.Fork f' g') →       
            (e₀ : X ≅ X') →                     (e₁ : Y ≅ Y') →                 
      (e : c.pt ≅ c'.pt) →                         autoParam                    
         (CategoryTheory.CategoryStruct.comp e₀.hom f' = CategoryTheory.Category
Struct.comp f e₁.hom)                             CategoryTheory.Limits.Fork.isL
imitOfIsos._auto_1 →                           autoParam                        
       (CategoryTheory.CategoryStruct.comp e₀.hom g' =                          
       CategoryTheory.CategoryStruct.comp g e₁.hom)                             
  CategoryTheory.Limits.Fork.isLimitOfIsos._auto_3 →                            
 autoParam                                 (CategoryTheory.CategoryStruct.comp e
.hom c'.ι =                                   CategoryTheory.CategoryStruct.comp
 c.ι e₀.hom)                                 CategoryTheory.Limits.Fork.isLimitO
fIsos._auto_5 →                               CategoryTheory.Limits.IsLimit c'
参数：c : CategoryTheory.Limits.Fork f g；c' : CategoryTheory.Limits.Fork f' g'；e₀ :
 X ≅ X'；e₁ : Y ≅ Y'；e : c.pt ≅ c'.pt；CategoryTheory.CategoryStruct.comp e₀.hom f
' = CategoryTheory.CategoryStruct.comp f e₁.hom；CategoryTheory.CategoryStruct.co
mp e₀.hom g' =                                 CategoryTheory.CategoryStruct.com
p g e₁.hom；CategoryTheory.CategoryStruct.comp e.hom c'.ι =                      
             CategoryTheory.CategoryStruct.comp c.ι e₀.hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two forks with isomorphic components in such a way that the natural diagra
ms commute, then if
one is a limit, then the other one is as well.
-/
def Fork.isLimitOfIsos {X' Y' : C} (c : Fork f g) (hc : IsLimit c)
    {f' g' : X' ⟶ Y'} (c' : Fork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₀.hom := by cat_disch) : IsLimit c' :=
  (Fork.isLimitEquivOfIsos c c' e₀ e₁ e) hc

/-- Helper function for constructing morphisms between coequalizer coforks.
-/
@[simps]
/-
**CategoryTheory.Limits.Cofork.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Cofork`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s t : CategoryTheory.Limits.Cofork f g} →     
      (k : s.pt ⟶ t.pt) → CategoryTheory.CategoryStruct.comp s.π k = t.π → (s ⟶ 
t)
参数：k : s.pt ⟶ t.pt；s ⟶ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for constructing morphisms between coequalizer coforks.
-/
def Cofork.mkHom {s t : Cofork f g} (k : s.pt ⟶ t.pt) (w : s.π ≫ k = t.π) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · simp [Cofork.app_zero_eq_comp_π_left, w]
    · exact w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Fork.hom_comp_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.hom_comp_ι {s t : Fork f g} (f : s ⟶ t) : f.hom ≫ t.ι = s.ι := by
  cases s; cases t; cases f; aesop

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Fork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fork.π_comp_hom {s t : Cofork f g} (f : s ⟶ t) : s.π ≫ f.hom = t.π := by
  cases s; cases t; cases f; aesop

/-- To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
@[simps]
/-
**CategoryTheory.Limits.Cofork.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Cofork`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {s t : CategoryTheory.Limits.Cofork f g} →     
      (i : s.pt ≅ t.pt) →             autoParam (CategoryTheory.CategoryStruct.c
omp s.π i.hom = t.π) CategoryTheory.Limits.Cofork.ext._auto_1 →               (s
 ≅ t)
参数：i : s.pt ≅ t.pt；CategoryTheory.CategoryStruct.comp s.π i.hom = t.π；s ≅ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def Cofork.ext {s t : Cofork f g} (i : s.pt ≅ t.pt) (w : s.π ≫ i.hom = t.π := by cat_disch) :
    s ≅ t where
  hom := Cofork.mkHom i.hom w
  inv := Cofork.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

/-- Two coforks of the form `ofπ` are isomorphic whenever their `π`'s are equal. -/
/-
**CategoryTheory.Limits.CoforkOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two coforks of the form `ofπ` are isomorphic whenever their `π`'s are equal.
-/
def CoforkOfπ.ext {P : C} {π π' : Y ⟶ P} (w : f ≫ π = g ≫ π) (w' : f ≫ π' = g ≫ π') (h : π = π') :
    Cofork.ofπ π w ≅ Cofork.ofπ π' w' :=
  Cofork.ext (Iso.refl _) (by simp [h])

/-- Every cofork is isomorphic to one of the form `Cofork.ofπ _ _`. -/
/-
**CategoryTheory.Limits.Cofork.isoCoforkOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every cofork is isomorphic to one of the form `Cofork.ofπ _ _`.
-/
def Cofork.isoCoforkOfπ (c : Cofork f g) : c ≅ Cofork.ofπ c.π c.condition :=
  Cofork.ext (Iso.refl _)

/--
Given two coforks with isomorphic components in such a way that the natural diagrams commute, then
one is a colimit if and only if the other one is.
-/
/-
**CategoryTheory.Limits.Cofork.isColimitEquivOfIsos** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Cofork`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f g : X ⟶ Y} →         {X' Y' : C} →           (c : CategoryTheory.Lim
its.Cofork f g) →             {f' g' : X' ⟶ Y'} →               (c' : CategoryTh
eory.Limits.Cofork f' g') →                 (e₀ : X ≅ X') →                   (e
₁ : Y ≅ Y') →                     (e : c.pt ≅ c'.pt) →                       aut
oParam                           (CategoryTheory.CategoryStruct.comp e₀.hom f' =
 CategoryTheory.CategoryStruct.comp f e₁.hom)                           Category
Theory.Limits.Cofork.isColimitEquivOfIsos._auto_1 →                         auto
Param                             (CategoryTheory.CategoryStruct.comp e₀.hom g' 
= CategoryTheory.CategoryStruct.comp g e₁.hom)                             Categ
oryTheory.Limits.Cofork.isColimitEquivOfIsos._auto_3 →                          
 autoParam                               (CategoryTheory.CategoryStruct.comp e₁.
inv                                   (CategoryTheory.CategoryStruct.comp c.π e.
hom) =                                 c'.π)                               Categ
oryTheory.Limits.Cofork.isColimitEquivOfIsos._auto_5 →                          
   CategoryTheory.Limits.IsColimit c ≃ CategoryTheory.Limits.IsColimit c'
参数：c : CategoryTheory.Limits.Cofork f g；c' : CategoryTheory.Limits.Cofork f' g'；
e₀ : X ≅ X'；e₁ : Y ≅ Y'；e : c.pt ≅ c'.pt；CategoryTheory.CategoryStruct.comp e₀.h
om f' = CategoryTheory.CategoryStruct.comp f e₁.hom；CategoryTheory.CategoryStruc
t.comp e₀.hom g' = CategoryTheory.CategoryStruct.comp g e₁.hom；CategoryTheory.Ca
tegoryStruct.comp e₁.inv                                   (CategoryTheory.Categ
oryStruct.comp c.π e.hom) =                                 c'.π。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two coforks with isomorphic components in such a way that the natural diag
rams commute, then
one is a colimit if and only if the other one is.
-/
def Cofork.isColimitEquivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    (c : Cofork f g)
    {f' g' : X' ⟶ Y'} (c' : Cofork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e₁.inv ≫ c.π ≫ e.hom = c'.π := by cat_disch) :
    IsColimit c ≃ IsColimit c' :=
  let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsColimit.equivOfNatIsoOfIso i c c' (Cofork.ext e (by rw [← comm₃, ← Category.assoc]; rfl))

/--
Given two coforks with isomorphic components in such a way that the natural diagrams commute, then
if one is a colimit, then the other one is as well.
-/
/-
**CategoryTheory.Limits.Cofork.isColimitOfIsos** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Cofork`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         {X' Y' : C} →           (c : CategoryTheory.Lim
its.Cofork f g) →             CategoryTheory.Limits.IsColimit c →               
{f' g' : X' ⟶ Y'} →                 (c' : CategoryTheory.Limits.Cofork f' g') → 
                  (e₀ : X ≅ X') →                     (e₁ : Y ≅ Y') →           
            (e : c.pt ≅ c'.pt) →                         autoParam              
               (CategoryTheory.CategoryStruct.comp e₀.hom f' = CategoryTheory.Ca
tegoryStruct.comp f e₁.hom)                             CategoryTheory.Limits.Co
fork.isColimitOfIsos._auto_1 →                           autoParam              
                 (CategoryTheory.CategoryStruct.comp e₀.hom g' =                
                 CategoryTheory.CategoryStruct.comp g e₁.hom)                   
            CategoryTheory.Limits.Cofork.isColimitOfIsos._auto_3 →              
               autoParam                                 (CategoryTheory.Categor
yStruct.comp e₁.inv                                     (CategoryTheory.Category
Struct.comp c.π e.hom) =                                   c'.π)                
                 CategoryTheory.Limits.Cofork.isColimitOfIsos._auto_5 →         
                      CategoryTheory.Limits.IsColimit c'
参数：c : CategoryTheory.Limits.Cofork f g；c' : CategoryTheory.Limits.Cofork f' g'；
e₀ : X ≅ X'；e₁ : Y ≅ Y'；e : c.pt ≅ c'.pt；CategoryTheory.CategoryStruct.comp e₀.h
om f' = CategoryTheory.CategoryStruct.comp f e₁.hom；CategoryTheory.CategoryStruc
t.comp e₀.hom g' =                                 CategoryTheory.CategoryStruct
.comp g e₁.hom；CategoryTheory.CategoryStruct.comp e₁.inv                        
             (CategoryTheory.CategoryStruct.comp c.π e.hom) =                   
                c'.π。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two coforks with isomorphic components in such a way that the natural diag
rams commute, then
if one is a colimit, then the other one is as well.
-/
def Cofork.isColimitOfIsos {X' Y' : C} (c : Cofork f g) (hc : IsColimit c)
    {f' g' : X' ⟶ Y'} (c' : Cofork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e₁.inv ≫ c.π ≫ e.hom = c'.π := by cat_disch) : IsColimit c' :=
  (Cofork.isColimitEquivOfIsos c c' e₀ e₁ e) hc

variable (f g)

section

/-- Two parallel morphisms `f` and `g` have an equalizer if the diagram `parallelPair f g` has a
limit. -/
/-
**CategoryTheory.Limits.HasEqualizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：HasEqualizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two parallel morphisms `f` and `g` have an equalizer if the diagram `parallelPai
r f g` has a
limit.
-/
abbrev HasEqualizer :=
  HasLimit (parallelPair f g)

variable [HasEqualizer f g]

/-- If an equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
saying `equalizer f g`. -/
/-
**CategoryTheory.Limits.equalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：equalizer : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an equalizer of `f` and `g` exists, we can access an arbitrary choice of such
 by
saying `equalizer f g`.
-/
noncomputable abbrev equalizer : C :=
  limit (parallelPair f g)

/-- If an equalizer of `f` and `g` exists, we can access the inclusion
`equalizer f g ⟶ X` by saying `equalizer.ι f g`. -/
/-
**CategoryTheory.Limits.equalizer.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an equalizer of `f` and `g` exists, we can access the inclusion
`equalizer f g ⟶ X` by saying `equalizer.ι f g`.
-/
noncomputable abbrev equalizer.ι : equalizer f g ⟶ X :=
  limit.π (parallelPair f g) zero

/-- An equalizer cone for a parallel pair `f` and `g` -/
/-
**CategoryTheory.Limits.equalizer.fork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.equalizer`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       (f g : X ⟶ Y) → [CategoryTheory.Limits.HasEqualizer f g] → CategoryTheo
ry.Limits.Fork f g
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equalizer cone for a parallel pair `f` and `g`
-/
noncomputable abbrev equalizer.fork : Fork f g :=
  limit.cone (parallelPair f g)

@[simp]
/-
**CategoryTheory.Limits.equalizer.fork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizer.fork_ι : (equalizer.fork f g).ι = equalizer.ι f g :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.equalizer.fork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizer.fork_π_app_zero : (equalizer.fork f g).π.app zero = equalizer.ι f g :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.equalizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.equalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] (f g : 
X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasEqualizer f g],   CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.Limits.equalizer.ι f g) f =     CategoryTheory.
CategoryStruct.comp (CategoryTheory.Limits.equalizer.ι f g) g
参数：f g : X ⟶ Y；CategoryTheory.Limits.equalizer.ι f g；CategoryTheory.Limits.equal
izer.ι f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…
-/
theorem equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
  Fork.condition <| limit.cone <| parallelPair f g

/-- The equalizer built from `equalizer.ι f g` is limiting. -/
/-
**CategoryTheory.Limits.equalizerIsEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：equalizerIsEqualizer : IsLimit (Fork.ofι (equalizer.ι f g) (equalizer.cond
ition f g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…

--- 原说明 ---
The equalizer built from `equalizer.ι f g` is limiting.
-/
noncomputable def equalizerIsEqualizer : IsLimit (Fork.ofι (equalizer.ι f g)
    (equalizer.condition f g)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

variable {f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the equalizer of `f` and `g`
via `equalizer.lift : W ⟶ equalizer f g`. -/
/-
**CategoryTheory.Limits.equalizer.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.equalizer`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasEqualizer f 
g] →           {W : C} →             (k : W ⟶ X) →               CategoryTheory.
CategoryStruct.comp k f = CategoryTheory.CategoryStruct.comp k g →              
   (W ⟶ CategoryTheory.Limits.equalizer f g)
参数：k : W ⟶ X；W ⟶ CategoryTheory.Limits.equalizer f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the equalizer 
of `f` and `g`
via `equalizer.lift : W ⟶ equalizer f g`.
-/
noncomputable abbrev equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
  limit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]
/-
**CategoryTheory.Limits.equalizer.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    equalizer.lift k h ≫ equalizer.ι f g = k :=
  limit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ equalizer f g`
satisfying `l ≫ equalizer.ι f g = k`. -/
/-
**CategoryTheory.Limits.equalizer.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.equalizer`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasEqualizer f 
g] →           {W : C} →             (k : W ⟶ X) →               CategoryTheory.
CategoryStruct.comp k f = CategoryTheory.CategoryStruct.comp k g →              
   { l // CategoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.equalizer.
ι f g) = k }
参数：k : W ⟶ X；CategoryTheory.Limits.equalizer.ι f g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.lift_ι`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g] {W : C}…

--- 原说明 ---
A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ eq
ualizer f g`
satisfying `l ≫ equalizer.ι f g = k`.
-/
noncomputable def equalizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ equalizer f g // l ≫ equalizer.ι f g = k } :=
  ⟨equalizer.lift k h, equalizer.lift_ι _ _⟩

/-- Two maps into an equalizer are equal if they are equal when composed with the equalizer map. -/
@[ext]
/-
**CategoryTheory.Limits.equalizer.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.equalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y}   [inst_1 : CategoryTheory.Limits.HasEqualizer f g] {W : C} {k l : W ⟶ Ca
tegoryTheory.Limits.equalizer f g},   CategoryTheory.CategoryStruct.comp k (Cate
goryTheory.Limits.equalizer.ι f g) =       CategoryTheory.CategoryStruct.comp l 
(CategoryTheory.Limits.equalizer.ι f g) →     k = l
参数：CategoryTheory.Limits.equalizer.ι f g；CategoryTheory.Limits.equalizer.ι f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…

--- 原说明 ---
Two maps into an equalizer are equal if they are equal when composed with the eq
ualizer map.
-/
theorem equalizer.hom_ext {W : C} {k l : W ⟶ equalizer f g}
    (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
  Fork.IsLimit.hom_ext (limit.isLimit _) h
/-
**CategoryTheory.Limits.equalizer.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.equalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y}   [inst_1 : CategoryTheory.Limits.HasEqualizer f g] {W : C} (k : W ⟶ X), 
  CategoryTheory.CategoryStruct.comp k f = CategoryTheory.CategoryStruct.comp k 
g →     ∃! l, CategoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.equali
zer.ι f g) = k
参数：k : W ⟶ X；CategoryTheory.Limits.equalizer.ι f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.existsUnique`：∀ {C : Type u} {X Y : C
} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Li
mits.Fork f g}   (hs : CategoryTheory…
-/
theorem equalizer.existsUnique {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    ∃! l : W ⟶ equalizer f g, l ≫ equalizer.ι f g = k :=
  Fork.IsLimit.existsUnique (limit.isLimit _) _ h

/-- An equalizer morphism is a monomorphism -/
/-
**CategoryTheory.Limits.equalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equalizer morphism is a monomorphism
-/
instance equalizer.ι_mono : Mono (equalizer.ι f g) where
  right_cancellation _ _ w := equalizer.hom_ext w

end

section

variable {f g}

/-- The equalizer morphism in any limit cone is a monomorphism. -/
/-
**CategoryTheory.Limits.mono_of_isLimit_fork** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：mono_of_isLimit_fork {c : Fork f g} (i : IsLimit c) : Mono (Fork.ι c)
参数：i : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.hom_ext`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Fork f g}   (hs : CategoryTheory…

--- 原说明 ---
The equalizer morphism in any limit cone is a monomorphism.
-/
theorem mono_of_isLimit_fork {c : Fork f g} (i : IsLimit c) : Mono (Fork.ι c) :=
  { right_cancellation := fun _ _ w => Fork.IsLimit.hom_ext i w }

end

section

variable {f g}

/-- The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g`. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.idFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
形式化陈述：idFork (h : f = g) : Fork f g
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g
`.
-/
def idFork (h : f = g) : Fork f g :=
  Fork.ofι (𝟙 X) <| h ▸ rfl

/-- The identity on `X` is an equalizer of `(f, g)`, if `f = g`. -/
/-
**CategoryTheory.Limits.isLimitIdFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：isLimitIdFork (h : f = g) : IsLimit (idFork h)
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity on `X` is an equalizer of `(f, g)`, if `f = g`.
-/
def isLimitIdFork (h : f = g) : IsLimit (idFork h) :=
  Fork.IsLimit.mk _ (fun s => Fork.ι s) (fun _ => Category.comp_id _) fun s m h => by
    convert! h
    exact (Category.comp_id _).symm

/-- Every equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_eq** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIso_limit_cone_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLim
it c) : IsIso c.ι
参数：h₀ : f = g；h : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
Every equalizer of `(f, g)`, where `f = g`, is an isomorphism.
-/
theorem isIso_limit_cone_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLimit c) :
    IsIso c.ι :=
  Iso.isIso_hom <| IsLimit.conePointUniqueUpToIso h <| isLimitIdFork h₀

/-- The equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
/-
**CategoryTheory.Limits.equalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of `(f, g)`, where `f = g`, is an isomorphism.
-/
theorem equalizer.ι_of_eq [HasEqualizer f g] (h : f = g) : IsIso (equalizer.ι f g) :=
  isIso_limit_cone_parallelPair_of_eq h <| limit.isLimit _

/-- Every equalizer of `(f, f)` is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_self** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIso_limit_cone_parallelPair_of_self {c : Fork f f} (h : IsLimit c) : IsI
so c.ι
参数：h : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_eq`：isIso_limit_c
one_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLimit c) : IsIso c.ι

--- 原说明 ---
Every equalizer of `(f, f)` is an isomorphism.
-/
theorem isIso_limit_cone_parallelPair_of_self {c : Fork f f} (h : IsLimit c) : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq rfl h

/-- An equalizer that is an epimorphism is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_epi** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIso_limit_cone_parallelPair_of_epi {c : Fork f g} (h : IsLimit c) [Epi c
.ι] : IsIso c.ι
参数：h : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isIso_limit_cone_parallelPair_of_eq`：isIso_limit_c
one_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLimit c) : IsIso c.ι
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…

--- 原说明 ---
An equalizer that is an epimorphism is an isomorphism.
-/
theorem isIso_limit_cone_parallelPair_of_epi {c : Fork f g} (h : IsLimit c) [Epi c.ι] : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq ((cancel_epi _).1 (Fork.condition c)) h

/-- Two morphisms are equal if there is a fork whose inclusion is epi. -/
/-
**CategoryTheory.Limits.eq_of_epi_fork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two morphisms are equal if there is a fork whose inclusion is epi.
-/
theorem eq_of_epi_fork_ι (t : Fork f g) [Epi (Fork.ι t)] : f = g :=
  (cancel_epi (Fork.ι t)).1 <| Fork.condition t

/-- If the equalizer of two morphisms is an epimorphism, then the two morphisms are equal. -/
/-
**CategoryTheory.Limits.eq_of_epi_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：eq_of_epi_equalizer [HasEqualizer f g] [Epi (equalizer.ι f g)] : f = g
参数：equalizer.ι f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…

--- 原说明 ---
If the equalizer of two morphisms is an epimorphism, then the two morphisms are 
equal.
-/
theorem eq_of_epi_equalizer [HasEqualizer f g] [Epi (equalizer.ι f g)] : f = g :=
  (cancel_epi (equalizer.ι f g)).1 <| equalizer.condition _ _

end

/-
**CategoryTheory.Limits.hasEqualizer_of_self** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasEqualizer_of_self : HasEqualizer f f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasEqualizer_of_self : HasEqualizer f f :=
  HasLimit.mk
    { cone := idFork rfl
      isLimit := isLimitIdFork rfl }

/-- The equalizer inclusion for `(f, f)` is an isomorphism. -/
/-
**CategoryTheory.Limits.equalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer inclusion for `(f, f)` is an isomorphism.
-/
instance equalizer.ι_of_self : IsIso (equalizer.ι f f) :=
  equalizer.ι_of_eq rfl

/-- The equalizer of a morphism with itself is isomorphic to the source. -/
/-
**CategoryTheory.Limits.equalizer.isoSourceOfSelf** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.equalizer`。
形式化陈述：{C : Type u} →   {X Y : C} → [inst : CategoryTheory.Category.{v, u} C] → (
f : X ⟶ Y) → CategoryTheory.Limits.equalizer f f ≅ X
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.ι_of_self`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f : X ⟶ Y),   CategoryTheory.IsIso (Categ
oryTheory.Limits.equalizer.ι f …

--- 原说明 ---
The equalizer of a morphism with itself is isomorphic to the source.
-/
noncomputable def equalizer.isoSourceOfSelf : equalizer f f ≅ X :=
  asIso (equalizer.ι f f)

@[simp]
/-
**CategoryTheory.Limits.equalizer.isoSourceOfSelf_hom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.equalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] (f : X 
⟶ Y),   (CategoryTheory.Limits.equalizer.isoSourceOfSelf f).hom = CategoryTheory
.Limits.equalizer.ι f f
参数：f : X ⟶ Y；CategoryTheory.Limits.equalizer.isoSourceOfSelf f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizer.isoSourceOfSelf_hom : (equalizer.isoSourceOfSelf f).hom = equalizer.ι f f :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.equalizer.isoSourceOfSelf_inv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.equalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] (f : X 
⟶ Y),   (CategoryTheory.Limits.equalizer.isoSourceOfSelf f).inv =     CategoryTh
eory.Limits.equalizer.lift (CategoryTheory.CategoryStruct.id X) ⋯
参数：f : X ⟶ Y；CategoryTheory.Limits.equalizer.isoSourceOfSelf f；CategoryTheory.Ca
tegoryStruct.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Limits.equalizer.ι_of_self`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f : X ⟶ Y),   CategoryTheory.IsIso (Categ
oryTheory.Limits.equalizer.ι f …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equalizer.isoSourceOfSelf_inv :
    (equalizer.isoSourceOfSelf f).inv = equalizer.lift (𝟙 X) (by simp) := by
  ext
  simp [equalizer.isoSourceOfSelf]


section

variable {f g : X ⟶ Y} {Z : C} (h : Z ⟶ X)

/--
Given a fork `s` on morphisms `f, g : X ⟶ Y` and a pullback cone `c` on `s.ι : s.pt ⟶ X` and a
morphism `h : Z ⟶ X`, the projection `c.snd : c.pt ⟶ Z` induces a fork on `h ≫ f` and `h ≫ g`.
```
c.pt → Z
|      |
v      v
s.pt → X ⇉ Y
```
-/
/-
**CategoryTheory.Limits.precompFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：precompFork (s : Fork f g) (c : PullbackCone s.ι h) : Fork (h ≫ f) (h ≫ g)
参数：s : Fork f g；c : PullbackCone s.ι h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fork `s` on morphisms `f, g : X ⟶ Y` and a pullback cone `c` on `s.ι : s
.pt ⟶ X` and a
morphism `h : Z ⟶ X`, the projection `c.snd : c.pt ⟶ Z` induces a fork on `h ≫ f
` and `h ≫ g`.
```
c.pt → Z
|      |
v      v
s.pt → X ⇉ Y
```
-/
def precompFork (s : Fork f g) (c : PullbackCone s.ι h) : Fork (h ≫ f) (h ≫ g) :=
  Fork.ofι c.snd <| by
    rw [← c.condition_assoc, ← c.condition_assoc, s.condition]

/--
Any fork on `h ≫ f` and `h ≫ g` lifts to a pullback along `h` of an equalizer of `f` and `g`.
-/
/-
**CategoryTheory.Limits.liftPrecomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：liftPrecomp {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc :
 IsLimit c) (s' : Fork (h ≫ f) (h ≫ g)) : s'.pt ⟶ (precompFork h s c).pt
参数：hs : IsLimit s；hc : IsLimit c；s' : Fork (h ≫ f) (h ≫ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any fork on `h ≫ f` and `h ≫ g` lifts to a pullback along `h` of an equalizer of
 `f` and `g`.
-/
def liftPrecomp {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c)
    (s' : Fork (h ≫ f) (h ≫ g)) :
    s'.pt ⟶ (precompFork h s c).pt :=
  hc.lift <| PullbackCone.mk
    (hs.lift <| Fork.ofι (s'.ι ≫ h) (by simp [s'.condition])) s'.ι

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of an equalizer is an equalizer. -/
/-
**CategoryTheory.Limits.isLimitPrecompFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：isLimitPrecompFork {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h
} (hc : IsLimit c) : IsLimit (precompFork h s c)
参数：hs : IsLimit s；hc : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of an equalizer is an equalizer.
-/
def isLimitPrecompFork {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c) :
    IsLimit (precompFork h s c) :=
  Fork.IsLimit.mk _
    (fun s' ↦ liftPrecomp h hs hc s')
    (by simp [liftPrecomp, precompFork])
    (fun s' m h ↦ hc.hom_ext <| by
      apply PullbackCone.equalizer_ext
      · simp only [liftPrecomp, IsLimit.fac, PullbackCone.mk_π_app]
        apply hs.hom_ext
        apply Fork.equalizer_ext
        simp only [Fork.ι_ofι, precompFork] at h
        simp [c.condition, reassoc_of% h]
      · simpa [liftPrecomp] using! h)
/-
**CategoryTheory.Limits.hasEqualizer_precomp_of_equalizer** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：hasEqualizer_precomp_of_equalizer {s : Fork f g} (hs : IsLimit s) {c : Pul
lbackCone s.ι h} (hc : IsLimit c) : HasEqualizer (h ≫ f) (h ≫ g)
参数：hs : IsLimit s；hc : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
lemma hasEqualizer_precomp_of_equalizer {s : Fork f g} (hs : IsLimit s)
    {c : PullbackCone s.ι h} (hc : IsLimit c) :
    HasEqualizer (h ≫ f) (h ≫ g) :=
  HasLimit.mk
    { cone := precompFork h s c
      isLimit := isLimitPrecompFork h hs hc }
/-
**CategoryTheory.Limits.hasEqualizer_precomp_of_hasEqualizer** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasEqualizer_precomp_of_hasEqualizer [HasEqualizer f g] [HasPullback (equa
lizer.ι f g) h] : HasEqualizer (h ≫ f) (h ≫ g)
参数：equalizer.ι f g。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasEqualizer_precomp_of_equalizer`：hasEqualizer_pr
ecomp_of_equalizer {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc 
: IsLimit c) : HasEqualizer (h ≫ f) (h ≫ g)
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
-/
instance hasEqualizer_precomp_of_hasEqualizer [HasEqualizer f g] [HasPullback (equalizer.ι f g) h] :
    HasEqualizer (h ≫ f) (h ≫ g) :=
  hasEqualizer_precomp_of_equalizer h
    (equalizerIsEqualizer f g) (pullback.isLimit (equalizer.ι f g) h)

end

section

/-- Two parallel morphisms `f` and `g` have a coequalizer if the diagram `parallelPair f g` has a
colimit. -/
/-
**CategoryTheory.Limits.HasCoequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：HasCoequalizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two parallel morphisms `f` and `g` have a coequalizer if the diagram `parallelPa
ir f g` has a
colimit.
-/
abbrev HasCoequalizer :=
  HasColimit (parallelPair f g)

variable [HasCoequalizer f g]

/-- If a coequalizer of `f` and `g` exists, we can access an arbitrary choice of such by
saying `coequalizer f g`. -/
/-
**CategoryTheory.Limits.coequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：coequalizer : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a coequalizer of `f` and `g` exists, we can access an arbitrary choice of suc
h by
saying `coequalizer f g`.
-/
noncomputable abbrev coequalizer : C :=
  colimit (parallelPair f g)

/-- If a coequalizer of `f` and `g` exists, we can access the corresponding projection by
saying `coequalizer.π f g`. -/
/-
**CategoryTheory.Limits.coequalizer.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a coequalizer of `f` and `g` exists, we can access the corresponding projecti
on by
saying `coequalizer.π f g`.
-/
noncomputable abbrev coequalizer.π : Y ⟶ coequalizer f g :=
  colimit.ι (parallelPair f g) one

/-- An arbitrary choice of coequalizer cocone for a parallel pair `f` and `g`.
-/
/-
**CategoryTheory.Limits.coequalizer.cofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.coequalizer`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       (f g : X ⟶ Y) → [CategoryTheory.Limits.HasCoequalizer f g] → CategoryTh
eory.Limits.Cofork f g
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of coequalizer cocone for a parallel pair `f` and `g`.
-/
noncomputable abbrev coequalizer.cofork : Cofork f g :=
  colimit.cocone (parallelPair f g)

@[simp]
/-
**CategoryTheory.Limits.coequalizer.cofork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coequalizer.cofork_π : (coequalizer.cofork f g).π = coequalizer.π f g :=
  rfl
/-
**CategoryTheory.Limits.coequalizer.cofork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coequalizer.cofork_ι_app_one : (coequalizer.cofork f g).ι.app one = coequalizer.π f g :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.coequalizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.coequalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] (f g : 
X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasCoequalizer f g],   CategoryTheory.C
ategoryStruct.comp f (CategoryTheory.Limits.coequalizer.π f g) =     CategoryThe
ory.CategoryStruct.comp g (CategoryTheory.Limits.coequalizer.π f g)
参数：f g : X ⟶ Y；CategoryTheory.Limits.coequalizer.π f g；CategoryTheory.Limits.coe
qualizer.π f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…
-/
theorem coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
  Cofork.condition <| colimit.cocone <| parallelPair f g

/-- The cofork built from `coequalizer.π f g` is colimiting. -/
/-
**CategoryTheory.Limits.coequalizerIsCoequalizer** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：coequalizerIsCoequalizer : IsColimit (Cofork.ofπ (coequalizer.π f g) (coeq
ualizer.condition f g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…

--- 原说明 ---
The cofork built from `coequalizer.π f g` is colimiting.
-/
noncomputable def coequalizerIsCoequalizer :
    IsColimit (Cofork.ofπ (coequalizer.π f g) (coequalizer.condition f g)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _) (by simp))

variable {f g}

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` factors through the coequalizer of `f`
and `g` via `coequalizer.desc : coequalizer f g ⟶ W`. -/
/-
**CategoryTheory.Limits.coequalizer.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.coequalizer`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasCoequalizer 
f g] →           {W : C} →             (k : Y ⟶ W) →               CategoryTheor
y.CategoryStruct.comp f k = CategoryTheory.CategoryStruct.comp g k →            
     (CategoryTheory.Limits.coequalizer f g ⟶ W)
参数：k : Y ⟶ W；CategoryTheory.Limits.coequalizer f g ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` factors through the coequali
zer of `f`
and `g` via `coequalizer.desc : coequalizer f g ⟶ W`.
-/
noncomputable abbrev coequalizer.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    coequalizer f g ⟶ W :=
  colimit.desc (parallelPair f g) (Cofork.ofπ k h)

@[reassoc]
/-
**CategoryTheory.Limits.coequalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coequalizer.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    coequalizer.π f g ≫ coequalizer.desc k h = k :=
  colimit.ι_desc _ _
/-
**CategoryTheory.Limits.coequalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coequalizer.π_colimMap_desc {X' Y' Z : C} (f' g' : X' ⟶ Y') [HasCoequalizer f' g']
    (p : X ⟶ X') (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') (h : Y' ⟶ Z)
    (wh : f' ≫ h = g' ≫ h) :
    coequalizer.π f g ≫ colimMap (parallelPairHom f g f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h := by
  rw [ι_colimMap_assoc, parallelPairHom_app_one, coequalizer.π_desc]

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` induces a morphism
`l : coequalizer f g ⟶ W` satisfying `coequalizer.π ≫ g = l`. -/
/-
**CategoryTheory.Limits.coequalizer.desc'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.coequalizer`。
形式化陈述：{C : Type u} →   {X Y : C} →     [inst : CategoryTheory.Category.{v, u} C]
 →       {f g : X ⟶ Y} →         [inst_1 : CategoryTheory.Limits.HasCoequalizer 
f g] →           {W : C} →             (k : Y ⟶ W) →               CategoryTheor
y.CategoryStruct.comp f k = CategoryTheory.CategoryStruct.comp g k →            
     { l // CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coequalize
r.π f g) l = k }
参数：k : Y ⟶ W；CategoryTheory.Limits.coequalizer.π f g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.π_desc`：∀ {C : Type u} {X Y : C} [inst
 : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Li
mits.HasCoequalizer f g] {W : …

--- 原说明 ---
Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` induces a morphism
`l : coequalizer f g ⟶ W` satisfying `coequalizer.π ≫ g = l`.
-/
noncomputable def coequalizer.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    { l : coequalizer f g ⟶ W // coequalizer.π f g ≫ l = k } :=
  ⟨coequalizer.desc k h, coequalizer.π_desc _ _⟩

/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
map -/
@[ext]
/-
**CategoryTheory.Limits.coequalizer.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.coequalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y}   [inst_1 : CategoryTheory.Limits.HasCoequalizer f g] {W : C} {k l : Cate
goryTheory.Limits.coequalizer f g ⟶ W},   CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Limits.coequalizer.π f g) k =       CategoryTheory.CategoryStruct.c
omp (CategoryTheory.Limits.coequalizer.π f g) l →     k = l
参数：CategoryTheory.Limits.coequalizer.π f g；CategoryTheory.Limits.coequalizer.π f
 g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…

--- 原说明 ---
Two maps from a coequalizer are equal if they are equal when composed with the c
oequalizer
map
-/
theorem coequalizer.hom_ext {W : C} {k l : coequalizer f g ⟶ W}
    (h : coequalizer.π f g ≫ k = coequalizer.π f g ≫ l) : k = l :=
  Cofork.IsColimit.hom_ext (colimit.isColimit _) h
/-
**CategoryTheory.Limits.coequalizer.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.coequalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] {f g : 
X ⟶ Y}   [inst_1 : CategoryTheory.Limits.HasCoequalizer f g] {W : C} (k : Y ⟶ W)
,   CategoryTheory.CategoryStruct.comp f k = CategoryTheory.CategoryStruct.comp 
g k →     ∃! d, CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coequa
lizer.π f g) d = k
参数：k : Y ⟶ W；CategoryTheory.Limits.coequalizer.π f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.existsUnique`：∀ {C : Type u} {X Y
 : C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheor
y.Limits.Cofork f g}   (hs : CategoryTheo…
-/
theorem coequalizer.existsUnique {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) :
    ∃! d : coequalizer f g ⟶ W, coequalizer.π f g ≫ d = k :=
  Cofork.IsColimit.existsUnique (colimit.isColimit _) _ h

/-- A coequalizer morphism is an epimorphism -/
/-
**CategoryTheory.Limits.coequalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coequalizer morphism is an epimorphism
-/
instance coequalizer.π_epi : Epi (coequalizer.π f g) where
  left_cancellation _ _ w := coequalizer.hom_ext w

end

section

variable {f g}

/-- The coequalizer morphism in any colimit cocone is an epimorphism. -/
/-
**CategoryTheory.Limits.epi_of_isColimit_cofork** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：epi_of_isColimit_cofork {c : Cofork f g} (i : IsColimit c) : Epi c.π
参数：i : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…

--- 原说明 ---
The coequalizer morphism in any colimit cocone is an epimorphism.
-/
theorem epi_of_isColimit_cofork {c : Cofork f g} (i : IsColimit c) : Epi c.π :=
  { left_cancellation := fun _ _ w => Cofork.IsColimit.hom_ext i w }

end

section

variable {f g}

/-- The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `f = g`. -/
@[implicit_reducible]
/-
**CategoryTheory.Limits.idCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：idCofork (h : f = g) : Cofork f g
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `
f = g`.
-/
def idCofork (h : f = g) : Cofork f g :=
  Cofork.ofπ (𝟙 Y) <| h ▸ rfl

/-- The identity on `Y` is a coequalizer of `(f, g)`, where `f = g`. -/
/-
**CategoryTheory.Limits.isColimitIdCofork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：isColimitIdCofork (h : f = g) : IsColimit (idCofork h)
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity on `Y` is a coequalizer of `(f, g)`, where `f = g`.
-/
def isColimitIdCofork (h : f = g) : IsColimit (idCofork h) :=
  Cofork.IsColimit.mk _ (fun s => Cofork.π s) (fun _ => Category.id_comp _) fun s m h => by
    convert! h
    exact (Category.id_comp _).symm

/-- Every coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_eq** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIso_colimit_cocone_parallelPair_of_eq (h₀ : f = g) {c : Cofork f g} (h :
 IsColimit c) : IsIso c.π
参数：h₀ : f = g；h : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
Every coequalizer of `(f, g)`, where `f = g`, is an isomorphism.
-/
theorem isIso_colimit_cocone_parallelPair_of_eq (h₀ : f = g) {c : Cofork f g} (h : IsColimit c) :
    IsIso c.π :=
  Iso.isIso_hom <| IsColimit.coconePointUniqueUpToIso (isColimitIdCofork h₀) h

/-- The coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
/-
**CategoryTheory.Limits.coequalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coequalizer of `(f, g)`, where `f = g`, is an isomorphism.
-/
theorem coequalizer.π_of_eq [HasCoequalizer f g] (h : f = g) : IsIso (coequalizer.π f g) :=
  isIso_colimit_cocone_parallelPair_of_eq h <| colimit.isColimit _

/-- Every coequalizer of `(f, f)` is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_self** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIso_colimit_cocone_parallelPair_of_self {c : Cofork f f} (h : IsColimit 
c) : IsIso c.π
参数：h : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_eq`：isIso_col
imit_cocone_parallelPair_of_eq (h₀ : f = g) {c : Cofork f g} (h : IsColimit c) :
 IsIso c.π

--- 原说明 ---
Every coequalizer of `(f, f)` is an isomorphism.
-/
theorem isIso_colimit_cocone_parallelPair_of_self {c : Cofork f f} (h : IsColimit c) : IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq rfl h

/-- A coequalizer that is a monomorphism is an isomorphism. -/
/-
**CategoryTheory.Limits.isIso_limit_cocone_parallelPair_of_epi** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isIso_limit_cocone_parallelPair_of_epi {c : Cofork f g} (h : IsColimit c) 
[Mono c.π] : IsIso c.π
参数：h : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.isIso_colimit_cocone_parallelPair_of_eq`：isIso_col
imit_cocone_parallelPair_of_eq (h₀ : f = g) {c : Cofork f g} (h : IsColimit c) :
 IsIso c.π
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…

--- 原说明 ---
A coequalizer that is a monomorphism is an isomorphism.
-/
theorem isIso_limit_cocone_parallelPair_of_epi {c : Cofork f g} (h : IsColimit c) [Mono c.π] :
    IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq ((cancel_mono _).1 (Cofork.condition c)) h

/-- Two morphisms are equal if there is a cofork whose projection is mono. -/
/-
**CategoryTheory.Limits.eq_of_mono_cofork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two morphisms are equal if there is a cofork whose projection is mono.
-/
theorem eq_of_mono_cofork_π (t : Cofork f g) [Mono (Cofork.π t)] : f = g :=
  (cancel_mono (Cofork.π t)).1 <| Cofork.condition t

/-- If the coequalizer of two morphisms is a monomorphism, then the two morphisms are equal. -/
/-
**CategoryTheory.Limits.eq_of_mono_coequalizer** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：eq_of_mono_coequalizer [HasCoequalizer f g] [Mono (coequalizer.π f g)] : f
 = g
参数：coequalizer.π f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…

--- 原说明 ---
If the coequalizer of two morphisms is a monomorphism, then the two morphisms ar
e equal.
-/
theorem eq_of_mono_coequalizer [HasCoequalizer f g] [Mono (coequalizer.π f g)] : f = g :=
  (cancel_mono (coequalizer.π f g)).1 <| coequalizer.condition _ _

end

/-
**CategoryTheory.Limits.hasCoequalizer_of_self** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasCoequalizer_of_self : HasCoequalizer f f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasCoequalizer_of_self : HasCoequalizer f f :=
  HasColimit.mk
    { cocone := idCofork rfl
      isColimit := isColimitIdCofork rfl }

/-- The coequalizer projection for `(f, f)` is an isomorphism. -/
/-
**CategoryTheory.Limits.coequalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coequalizer projection for `(f, f)` is an isomorphism.
-/
instance coequalizer.π_of_self : IsIso (coequalizer.π f f) :=
  coequalizer.π_of_eq rfl

/-- The coequalizer of a morphism with itself is isomorphic to the target. -/
/-
**CategoryTheory.Limits.coequalizer.isoTargetOfSelf** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.coequalizer`。
形式化陈述：{C : Type u} →   {X Y : C} → [inst : CategoryTheory.Category.{v, u} C] → (
f : X ⟶ Y) → CategoryTheory.Limits.coequalizer f f ≅ Y
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.π_of_self`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f : X ⟶ Y),   CategoryTheory.IsIso (Cat
egoryTheory.Limits.coequalizer.π …

--- 原说明 ---
The coequalizer of a morphism with itself is isomorphic to the target.
-/
noncomputable def coequalizer.isoTargetOfSelf : coequalizer f f ≅ Y :=
  (asIso (coequalizer.π f f)).symm

@[simp]
/-
**CategoryTheory.Limits.coequalizer.isoTargetOfSelf_hom** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.coequalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] (f : X 
⟶ Y),   (CategoryTheory.Limits.coequalizer.isoTargetOfSelf f).hom =     Category
Theory.Limits.coequalizer.desc (CategoryTheory.CategoryStruct.id Y) ⋯
参数：f : X ⟶ Y；CategoryTheory.Limits.coequalizer.isoTargetOfSelf f；CategoryTheory.
CategoryStruct.id Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Limits.coequalizer.π_of_self`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f : X ⟶ Y),   CategoryTheory.IsIso (Cat
egoryTheory.Limits.coequalizer.π …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coequalizer.isoTargetOfSelf_hom :
    (coequalizer.isoTargetOfSelf f).hom = coequalizer.desc (𝟙 Y) (by simp) := by
  ext
  simp [coequalizer.isoTargetOfSelf]

@[simp]
/-
**CategoryTheory.Limits.coequalizer.isoTargetOfSelf_inv** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.coequalizer`。
形式化陈述：∀ {C : Type u} {X Y : C} [inst : CategoryTheory.Category.{v, u} C] (f : X 
⟶ Y),   (CategoryTheory.Limits.coequalizer.isoTargetOfSelf f).inv = CategoryTheo
ry.Limits.coequalizer.π f f
参数：f : X ⟶ Y；CategoryTheory.Limits.coequalizer.isoTargetOfSelf f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coequalizer.isoTargetOfSelf_inv : (coequalizer.isoTargetOfSelf f).inv = coequalizer.π f f :=
  rfl

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism for the equalizer of `f,g`.
This is an isomorphism iff `G` preserves the equalizer of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Equalizers.lean`
-/
/-
**CategoryTheory.Limits.equalizerComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] 
: G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g)
参数：G.map f；G.map g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the equalizer of `f,g`.
This is an isomorphism iff `G` preserves the equalizer of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Equalizers.lean`
-/
noncomputable def equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
  equalizer.lift (G.map (equalizer.ι _ _))
    (by simp only [← G.map_comp]; rw [equalizer.condition])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.equalizerComparison_comp_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equalizerComparison_comp_π [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    equalizerComparison f g G ≫ equalizer.ι (G.map f) (G.map g) = G.map (equalizer.ι f g) :=
  equalizer.lift_ι _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.map_lift_equalizerComparison** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：map_lift_equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G
.map g)] {Z : C} {h : Z ⟶ X} (w : h ≫ f = h ≫ g) : G.map (equalizer.lift h w) ≫ 
equalizerComparison f g G = equalizer.lift (G.map h) (by simp only [← G.map_comp
, w])
参数：G.map f；G.map g；w : h ≫ f = h ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.equalizerComparison_comp_π`：equalizerComparison_co
mp_π [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] : equalizerComparison
 f g G ≫ equalizer.ι (G.map f) (G.map …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_lift_equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] {Z : C}
    {h : Z ⟶ X} (w : h ≫ f = h ≫ g) :
    G.map (equalizer.lift h w) ≫ equalizerComparison f g G =
      equalizer.lift (G.map h) (by simp only [← G.map_comp, w]) := by
  apply equalizer.hom_ext
  simp [← G.map_comp]

/-- The comparison morphism for the coequalizer of `f,g`. -/
/-
**CategoryTheory.Limits.coequalizerComparison** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：coequalizerComparison [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.ma
p g)] : coequalizer (G.map f) (G.map g) ⟶ G.obj (coequalizer f g)
参数：G.map f；G.map g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the coequalizer of `f,g`.
-/
noncomputable def coequalizerComparison [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)] :
    coequalizer (G.map f) (G.map g) ⟶ G.obj (coequalizer f g) :=
  coequalizer.desc (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp]; rw [coequalizer.condition])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_coequalizerComparison [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)] :
    coequalizer.π _ _ ≫ coequalizerComparison f g G = G.map (coequalizer.π _ _) :=
  coequalizer.π_desc _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coequalizerComparison_map_desc** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：coequalizerComparison_map_desc [HasCoequalizer f g] [HasCoequalizer (G.map
 f) (G.map g)] {Z : C} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) : coequalizerComparison f
 g G ≫ G.map (coequalizer.desc h w) = coequalizer.desc (G.map h) (by simp only [
← G.map_comp, w])
参数：G.map f；G.map g；w : f ≫ h = g ≫ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ι_comp_coequalizerComparison_assoc`：∀ {C : Type u}
 {X Y : C} [inst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y) {D : Type u₂}
   [inst_1 : CategoryTheory.Category.{v₂, u₂} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coequalizerComparison_map_desc [HasCoequalizer f g] [HasCoequalizer (G.map f) (G.map g)]
    {Z : C} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) :
    coequalizerComparison f g G ≫ G.map (coequalizer.desc h w) =
      coequalizer.desc (G.map h) (by simp only [← G.map_comp, w]) := by
  apply coequalizer.hom_ext
  simp [← G.map_comp]

end Comparison

variable (C)

/-- A category `HasEqualizers` if it has all limits of shape `WalkingParallelPair`, i.e. if it has
an equalizer for every parallel pair of morphisms. -/
/-
**CategoryTheory.Limits.HasEqualizers** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：HasEqualizers
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasEqualizers` if it has all limits of shape `WalkingParallelPair`, 
i.e. if it has
an equalizer for every parallel pair of morphisms.
-/
abbrev HasEqualizers :=
  HasLimitsOfShape WalkingParallelPair C

/-- A category `HasCoequalizers` if it has all colimits of shape `WalkingParallelPair`, i.e. if it
has a coequalizer for every parallel pair of morphisms. -/
/-
**CategoryTheory.Limits.HasCoequalizers** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：HasCoequalizers
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasCoequalizers` if it has all colimits of shape `WalkingParallelPai
r`, i.e. if it
has a coequalizer for every parallel pair of morphisms.
-/
abbrev HasCoequalizers :=
  HasColimitsOfShape WalkingParallelPair C

/-- If `C` has all limits of diagrams `parallelPair f g`, then it has all equalizers -/
/-
**CategoryTheory.Limits.hasEqualizers_of_hasLimit_parallelPair** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasEqualizers_of_hasLimit_parallelPair [forall {X Y : C} {f g : X ⟶ Y}, Ha
sLimit (parallelPair f g)] : HasEqualizers C
参数：parallelPair f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G

--- 原说明 ---
If `C` has all limits of diagrams `parallelPair f g`, then it has all equalizers
-/
theorem hasEqualizers_of_hasLimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasLimit (parallelPair f g)] : HasEqualizers C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelPair F).symm }

/-- If `C` has all colimits of diagrams `parallelPair f g`, then it has all coequalizers -/
/-
**CategoryTheory.Limits.hasCoequalizers_of_hasColimit_parallelPair** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasCoequalizers_of_hasColimit_parallelPair [forall {X Y : C} {f g : X ⟶ Y}
, HasColimit (parallelPair f g)] : HasCoequalizers C
参数：parallelPair f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G

--- 原说明 ---
If `C` has all colimits of diagrams `parallelPair f g`, then it has all coequali
zers
-/
theorem hasCoequalizers_of_hasColimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasColimit (parallelPair f g)] : HasCoequalizers C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelPair F) }

section

-- In this section we show that a split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
variable {C} [IsSplitMono f]

/-- A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `isSplitMonoEqualizes` that it is a limit cone.
-/
@[simps (rhsMd := default)]
/-
**CategoryTheory.Limits.coneOfIsSplitMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：coneOfIsSplitMono : Fork (𝟙 Y) (retraction f ≫ f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `isSplitMonoEqualizes` that it is a limit co
ne.
-/
noncomputable def coneOfIsSplitMono : Fork (𝟙 Y) (retraction f ≫ f) :=
  Fork.ofι f (by simp)

@[simp]
/-
**CategoryTheory.Limits.coneOfIsSplitMono_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coneOfIsSplitMono_ι : (coneOfIsSplitMono f).ι = f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
-/
/-
**CategoryTheory.Limits.isSplitMonoEqualizes** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：isSplitMonoEqualizes {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsLimit (cone
OfIsSplitMono f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
-/
noncomputable def isSplitMonoEqualizes {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    IsLimit (coneOfIsSplitMono f) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ retraction f, by
      dsimp
      rw [Category.assoc, ← s.condition]
      apply Category.comp_id, fun hm => by simp [← hm]⟩

end

/-- We show that the converse to `isSplitMonoEqualizes` is true:
Whenever `f` equalizes `(r ≫ f)` and `(𝟙 Y)`, then `r` is a retraction of `f`. -/
/-
**CategoryTheory.Limits.splitMonoOfEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：splitMonoOfEqualizer {X Y : C} {f : X ⟶ Y} {r : Y ⟶ X} (hr : f ≫ r ≫ f = f
) (h : IsLimit (Fork.ofι f (hr.trans (Category.comp_id _).symm : f ≫ r ≫ f = f ≫
 𝟙 Y))) : SplitMono f where retraction
参数：hr : f ≫ r ≫ f = f；h : IsLimit (Fork.ofι f (hr.trans (Category.comp_id _).sym
m : f ≫ r ≫ f = f ≫ 𝟙 Y))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We show that the converse to `isSplitMonoEqualizes` is true:
Whenever `f` equalizes `(r ≫ f)` and `(𝟙 Y)`, then `r` is a retraction of `f`.
-/
def splitMonoOfEqualizer {X Y : C} {f : X ⟶ Y} {r : Y ⟶ X} (hr : f ≫ r ≫ f = f)
    (h : IsLimit (Fork.ofι f (hr.trans (Category.comp_id _).symm : f ≫ r ≫ f = f ≫ 𝟙 Y))) :
    SplitMono f where
  retraction := r
  id := Fork.IsLimit.hom_ext h ((Category.assoc _ _ _).trans <| hr.trans (Category.id_comp _).symm)

variable {C f g}

/-- The fork obtained by postcomposing an equalizer fork with a monomorphism is an equalizer. -/
/-
**CategoryTheory.Limits.isEqualizerCompMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：isEqualizerCompMono {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm
 : Mono h] : have : Fork.ι c ≫ f ≫ h = Fork.ι c ≫ g ≫ h
参数：i : IsLimit c；h : Y ⟶ Z。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…

--- 原说明 ---
The fork obtained by postcomposing an equalizer fork with a monomorphism is an e
qualizer.
-/
def isEqualizerCompMono {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm : Mono h] :
    have : Fork.ι c ≫ f ≫ h = Fork.ι c ≫ g ≫ h := by
      simp only [← Category.assoc]
      exact congrArg (· ≫ h) c.condition
    IsLimit (Fork.ofι c.ι (by simp [this]) : Fork (f ≫ h) (g ≫ h)) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : Fork f g := Fork.ofι s.ι (by apply hm.right_cancellation; simp [s.condition])
    let l := Fork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

variable (C f g)

@[instance]
/-
**CategoryTheory.Limits.hasEqualizer_comp_mono** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasEqualizer_comp_mono [HasEqualizer f g] {Z : C} (h : Y ⟶ Z) [Mono h] : H
asEqualizer (f ≫ h) (g ≫ h)
参数：h : Y ⟶ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasEqualizer_comp_mono [HasEqualizer f g] {Z : C} (h : Y ⟶ Z) [Mono h] :
    HasEqualizer (f ≫ h) (g ≫ h) :=
  ⟨⟨{   cone := _
        isLimit := isEqualizerCompMono (limit.isLimit _) h }⟩⟩

/-- An equalizer of an idempotent morphism and the identity is split mono. -/
@[simps]
/-
**CategoryTheory.Limits.splitMonoOfIdempotentOfIsLimitFork** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：splitMonoOfIdempotentOfIsLimitFork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c
 : Fork (𝟙 X) f} (i : IsLimit c) : SplitMono c.ι where retraction
参数：hf : f ≫ f = f；𝟙 X；i : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equalizer of an idempotent morphism and the identity is split mono.
-/
def splitMonoOfIdempotentOfIsLimitFork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Fork (𝟙 X) f}
    (i : IsLimit c) : SplitMono c.ι where
  retraction := i.lift (Fork.ofι f (by simp [hf]))
  id := by
    let := mono_of_isLimit_fork i
    rw [← cancel_mono_id c.ι, Category.assoc, Fork.IsLimit.lift_ι, Fork.ι_ofι, ← c.condition]
    exact Category.comp_id c.ι

/-- The equalizer of an idempotent morphism and the identity is split mono. -/
/-
**CategoryTheory.Limits.splitMonoOfIdempotentEqualizer** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：splitMonoOfIdempotentEqualizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f) [HasEq
ualizer (𝟙 X) f] : SplitMono (equalizer.ι (𝟙 X) f)
参数：hf : f ≫ f = f；𝟙 X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer of an idempotent morphism and the identity is split mono.
-/
noncomputable def splitMonoOfIdempotentEqualizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
    [HasEqualizer (𝟙 X) f] : SplitMono (equalizer.ι (𝟙 X) f) :=
  splitMonoOfIdempotentOfIsLimitFork _ hf (limit.isLimit _)

section

-- In this section we show that a split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
variable {C} [IsSplitEpi f]

/-- A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `isSplitEpiCoequalizes` that it is a colimit cocone.
-/
@[simps (rhsMd := default)]
/-
**CategoryTheory.Limits.coconeOfIsSplitEpi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：coconeOfIsSplitEpi : Cofork (𝟙 X) (f ≫ section_ f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `isSplitEpiCoequalizes` that it is a colim
it cocone.
-/
noncomputable def coconeOfIsSplitEpi : Cofork (𝟙 X) (f ≫ section_ f) :=
  Cofork.ofπ f (by simp)

@[simp]
/-
**CategoryTheory.Limits.coconeOfIsSplitEpi_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coconeOfIsSplitEpi_π : (coconeOfIsSplitEpi f).π = f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
-/
/-
**CategoryTheory.Limits.isSplitEpiCoequalizes** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：isSplitEpiCoequalizes {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsColimit (co
coneOfIsSplitEpi f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
-/
noncomputable def isSplitEpiCoequalizes {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] :
    IsColimit (coconeOfIsSplitEpi f) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨section_ f ≫ s.π, by
      dsimp
      rw [← Category.assoc, ← s.condition, Category.id_comp], fun hm => by simp [← hm]⟩

end

/-- We show that the converse to `isSplitEpiEqualizes` is true:
Whenever `f` coequalizes `(f ≫ s)` and `(𝟙 X)`, then `s` is a section of `f`. -/
/-
**CategoryTheory.Limits.splitEpiOfCoequalizer** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       {f : X ⟶ Y} →         {s : Y ⟶ X} →           (hs : CategoryTheory.Cate
goryStruct.comp f (CategoryTheory.CategoryStruct.comp s f) = f) →             Ca
tegoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofork.ofπ f ⋯) → CategoryT
heory.SplitEpi f
参数：CategoryTheory.CategoryStruct.comp s f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We show that the converse to `isSplitEpiEqualizes` is true:
Whenever `f` coequalizes `(f ≫ s)` and `(𝟙 X)`, then `s` is a section of `f`.
-/
def splitEpiOfCoequalizer {X Y : C} {f : X ⟶ Y} {s : Y ⟶ X} (hs : f ≫ s ≫ f = f)
    (h :
      IsColimit
        (Cofork.ofπ f
          ((Category.assoc _ _ _).trans <| hs.trans (Category.id_comp f).symm :
            (f ≫ s) ≫ f = 𝟙 X ≫ f))) :
    SplitEpi f where
  section_ := s
  id := Cofork.IsColimit.hom_ext h (hs.trans (Category.comp_id _).symm)

variable {C f g}

/-- The cofork obtained by precomposing a coequalizer cofork with an epimorphism is
a coequalizer. -/
/-
**CategoryTheory.Limits.isCoequalizerEpiComp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：isCoequalizerEpiComp {c : Cofork f g} (i : IsColimit c) {W : C} (h : W ⟶ X
) [hm : Epi h] : have : (h ≫ f) ≫ Cofork.π c = (h ≫ g) ≫ Cofork.π c
参数：i : IsColimit c；h : W ⟶ X。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…

--- 原说明 ---
The cofork obtained by precomposing a coequalizer cofork with an epimorphism is
a coequalizer.
-/
def isCoequalizerEpiComp {c : Cofork f g} (i : IsColimit c) {W : C} (h : W ⟶ X) [hm : Epi h] :
    have : (h ≫ f) ≫ Cofork.π c = (h ≫ g) ≫ Cofork.π c := by
      simp only [Category.assoc]
      exact congrArg (h ≫ ·) c.condition
    IsColimit (Cofork.ofπ c.π (this) : Cofork (h ≫ f) (h ≫ g)) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : Cofork f g :=
      Cofork.ofπ s.π (by apply hm.left_cancellation; simp_rw [← Category.assoc, s.condition])
    let l := Cofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩
/-
**CategoryTheory.Limits.hasCoequalizer_epi_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasCoequalizer_epi_comp [HasCoequalizer f g] {W : C} (h : W ⟶ X) [Epi h] :
 HasCoequalizer (h ≫ f) (h ≫ g)
参数：h : W ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasCoequalizer_epi_comp [HasCoequalizer f g] {W : C} (h : W ⟶ X) [Epi h] :
    HasCoequalizer (h ≫ f) (h ≫ g) :=
  ⟨⟨{   cocone := _
        isColimit := isCoequalizerEpiComp (colimit.isColimit _) h }⟩⟩

variable (C f g)

/-- A coequalizer of an idempotent morphism and the identity is split epi. -/
@[simps]
/-
**CategoryTheory.Limits.splitEpiOfIdempotentOfIsColimitCofork** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       {f : X ⟶ X} →         CategoryTheory.CategoryStruct.comp f f = f →       
    {c : CategoryTheory.Limits.Cofork (CategoryTheory.CategoryStruct.id X) f} → 
            CategoryTheory.Limits.IsColimit c → CategoryTheory.SplitEpi c.π
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coequalizer of an idempotent morphism and the identity is split epi.
-/
def splitEpiOfIdempotentOfIsColimitCofork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Cofork (𝟙 X) f}
    (i : IsColimit c) : SplitEpi c.π where
  section_ := i.desc (Cofork.ofπ f (by simp [hf]))
  id := by
    let := epi_of_isColimit_cofork i
    rw [← cancel_epi_id c.π, ← Category.assoc, Cofork.IsColimit.π_desc, Cofork.π_ofπ, ←
      c.condition]
    exact Category.id_comp _

/-- The coequalizer of an idempotent morphism and the identity is split epi. -/
/-
**CategoryTheory.Limits.splitEpiOfIdempotentCoequalizer** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：splitEpiOfIdempotentCoequalizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f) [HasC
oequalizer (𝟙 X) f] : SplitEpi (coequalizer.π (𝟙 X) f)
参数：hf : f ≫ f = f；𝟙 X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coequalizer of an idempotent morphism and the identity is split epi.
-/
noncomputable def splitEpiOfIdempotentCoequalizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
    [HasCoequalizer (𝟙 X) f] : SplitEpi (coequalizer.π (𝟙 X) f) :=
  splitEpiOfIdempotentOfIsColimitCofork _ hf (colimit.isColimit _)

end CategoryTheory.Limits

end

