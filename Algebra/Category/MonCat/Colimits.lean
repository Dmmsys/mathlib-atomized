/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at what Lean 3's `#print monoid` printed a long time ago (it no longer looks like
this due to the addition of `npow` fields):
```
structure monoid : Type u → Type u
fields:
monoid.mul : Π {M : Type u} [self : monoid M], M → M → M
monoid.mul_assoc : ∀ {M : Type u} [self : monoid M] (a b c : M), a * b * c = a * (b * c)
monoid.one : Π {M : Type u} [self : monoid M], M
monoid.one_mul : ∀ {M : Type u} [self : monoid M] (a : M), 1 * a = a
monoid.mul_one : ∀ {M : Type u} [self : monoid M] (a : M), a * 1 = a
```

and if we'd fed it the output of Lean 3's `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.

Note: `Monoid` and `CommRing` are no longer flat structures in Mathlib4, and so `#print Monoid`
gives the less clear
```
inductive Monoid.{u} : Type u → Type u
number of parameters: 1
constructors:
Monoid.mk : {M : Type u} →
  [toSemigroup : Semigroup M] →
    [toOne : One M] →
      (∀ (a : M), 1 * a = a) →
        (∀ (a : M), a * 1 = a) →
          (npow : ℕ → M → M) →
            autoParam (∀ (x : M), npow 0 x = 1) _auto✝ →
              autoParam (∀ (n : ℕ) (x : M), npow (n + 1) x = x * npow n x) _auto✝¹ → Monoid M
```
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe v u

open CategoryTheory Limits

namespace MonCat.Colimits

/-!
We build the colimit of a diagram in `MonCat` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

/-- An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
/-
**MonCat.Colimits.Prequotient** 是 Mathlib 中的一个归纳类型，位于命名空间 `MonCat.Colimits`。
形式化陈述：{J : Type v} → [inst : CategoryTheory.Category.{u, v} J] → CategoryTheory.
Functor J MonCat → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inductive type representing all monoid expressions (without relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | one : Prequotient
  | mul : Prequotient → Prequotient → Prequotient
/-
**MonCat.Colimits.** 是 Mathlib 中的一个实例，位于命名空间 `MonCat.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.one⟩

open Prequotient

/-- The relation on `Prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
/-
**MonCat.Colimits.Relation** 是 Mathlib 中的一个归纳类型，位于命名空间 `MonCat.Colimits`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.Category.{u, v} J] →     (F : Cate
goryTheory.Functor J MonCat) → MonCat.Colimits.Prequotient F → MonCat.Colimits.P
requotient F → Prop
参数：F : CategoryTheory.Functor J MonCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on `Prequotient` saying when two expressions are equal
because of the monoid laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z),
      Relation x z -- There's always a `map` relation
  | map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      -- Then one relation per operation, describing the interaction with `of`
      Relation (Prequotient.of j' ((F.map f) x)) (Prequotient.of j x)
  | mul : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x * y))
      (mul (Prequotient.of j x) (Prequotient.of j y))
  | one : ∀ j, Relation (Prequotient.of j 1) one -- Then one relation per argument of each operation
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    -- And one relation per axiom
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x

/-- The setoid corresponding to monoid expressions modulo monoid relations and identifications.
-/
/-
**MonCat.Colimits.colimitSetoid** 是 Mathlib 中的一个实例，位于命名空间 `MonCat.Colimits`。
形式化陈述：colimitSetoid : Setoid (Prequotient F) where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid corresponding to monoid expressions modulo monoid relations and ident
ifications.
-/
instance colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

/-- The underlying type of the colimit of a diagram in `MonCat`.
-/
/-
**MonCat.Colimits.ColimitType** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：ColimitType : Type v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying type of the colimit of a diagram in `MonCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
deriving Inhabited
/-
**MonCat.Colimits.monoidColimitType** 是 Mathlib 中的一个实例，位于命名空间 `MonCat.Colimits`。
形式化陈述：monoidColimitType : Monoid (ColimitType F) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidColimitType : Monoid (ColimitType F) where
  one := Quotient.mk _ one
  mul := Quotient.map₂ mul fun _ x' rx y _ ry =>
    Setoid.trans (Relation.mul_1 _ _ y rx) (Relation.mul_2 x' _ _ ry)
  one_mul := Quotient.ind fun _ => Quotient.sound <| Relation.one_mul _
  mul_one := Quotient.ind fun _ => Quotient.sound <| Relation.mul_one _
  mul_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
    Quotient.sound <| Relation.mul_assoc _ _ _

@[simp]
/-
**MonCat.Colimits.quot_one** 是 Mathlib 中的一个定理，位于命名空间 `MonCat.Colimits`。
形式化陈述：quot_one : Quot.mk Setoid.r one = (1 : ColimitType F)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
/-
**MonCat.Colimits.quot_mul** 是 Mathlib 中的一个定理，位于命名空间 `MonCat.Colimits`。
形式化陈述：quot_mul (x y : Prequotient F) : Quot.mk Setoid.r (mul x y) = @HMul.hMul (
ColimitType F) (ColimitType F) (ColimitType F) _ (Quot.mk Setoid.r x) (Quot.mk S
etoid.r y)
参数：x y : Prequotient F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mul (x y : Prequotient F) : Quot.mk Setoid.r (mul x y) =
    @HMul.hMul (ColimitType F) (ColimitType F) (ColimitType F) _
      (Quot.mk Setoid.r x) (Quot.mk Setoid.r y) :=
  rfl

/-- The bundled monoid giving the colimit of a diagram. -/
/-
**MonCat.Colimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：colimit : MonCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled monoid giving the colimit of a diagram.
-/
def colimit : MonCat :=
  of (ColimitType F)

/-- The function from a given monoid in the diagram to the colimit monoid. -/
/-
**MonCat.Colimits.coconeFun** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：coconeFun (j : J) (x : F.obj j) : ColimitType F
参数：j : J；x : F.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from a given monoid in the diagram to the colimit monoid.
-/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/-- The monoid homomorphism from a given monoid in the diagram to the colimit monoid. -/
/-
**MonCat.Colimits.coconeMorphism** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：coconeMorphism (j : J) : F.obj j ⟶ colimit F
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid homomorphism from a given monoid in the diagram to the colimit monoid
.
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
  { toFun := coconeFun F j
    map_one' := Quot.sound (Relation.one _)
    map_mul' _ _ := Quot.sound (Relation.mul _ _ _) }

@[simp]
/-
**MonCat.Colimits.cocone_naturality** 是 Mathlib 中的一个定理，位于命名空间 `MonCat.Colimits`。
形式化陈述：cocone_naturality {j j' : J} (f : j ⟶ j') : F.map f ≫ coconeMorphism F j' 
= coconeMorphism F j
参数：f : j ⟶ j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonCat.hom_ext`：hom_ext {M N : MonCat} {f g : M ⟶ N} (hf : f.hom = g.hom
) : f = g
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
/-
**MonCat.Colimits.cocone_naturality_components** 是 Mathlib 中的一个定理，位于命名空间 `MonCat
.Colimits`。
形式化陈述：cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) : (coco
neMorphism F j') (F.map f x) = (coconeMorphism F j) x
参数：j j' : J；f : j ⟶ j'；x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonCat.Colimits.cocone_naturality`：cocone_naturality {j j' : J} (f : j ⟶
 j') : F.map f ≫ coconeMorphism F j' = coconeMorphism F j
-/
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The cocone over the proposed colimit monoid. -/
/-
**MonCat.Colimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit monoid.
-/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
@[simp]
/-
**MonCat.Colimits.descFunLift** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.Category.{u, v} J] →     (F : Cate
goryTheory.Functor J MonCat) → (s : CategoryTheory.Limits.Cocone F) → MonCat.Col
imits.Prequotient F → ↑s.pt
参数：F : CategoryTheory.Functor J MonCat；s : CategoryTheory.Limits.Cocone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from the free monoid on the diagram to the cone point of any other 
cocone.
-/
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | one => 1
  | mul x y => descFunLift _ x * descFunLift _ y

/-- The function from the colimit monoid to the cone point of any other cocone. -/
/-
**MonCat.Colimits.descFun** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：descFun (s : Cocone F) : ColimitType F -> s.pt
参数：s : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from the colimit monoid to the cone point of any other cocone.
-/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl x => rfl
    | symm x y _ h => exact h.symm
    | trans x y z _ _ h₁ h₂ => exact h₁.trans h₂
    | map j j' f x => exact s.w_apply f x
    | mul j x y => exact map_mul (s.ι.app j).hom x y
    | one j => exact map_one (s.ι.app j).hom
    | mul_1 x x' y _ h => exact congr_arg (· * _) h
    | mul_2 x y y' _ h => exact congr_arg (_ * ·) h
    | mul_assoc x y z => exact mul_assoc _ _ _
    | one_mul x => exact one_mul _
    | mul_one x => exact mul_one _

/-- The monoid homomorphism from the colimit monoid to the cone point of any other cocone. -/
/-
**MonCat.Colimits.descMorphism** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：descMorphism (s : Cocone F) : colimit F ⟶ s.pt
参数：s : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid homomorphism from the colimit monoid to the cone point of any other c
ocone.
-/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt :=
  ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_mul' x y := by
      induction x using Quot.inductionOn
      induction y using Quot.inductionOn
      solve_by_elim }

set_option backward.isDefEq.respectTransparency false in
/-- Evidence that the proposed colimit is the colimit. -/
/-
**MonCat.Colimits.colimitIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.Colimits`。
形式化陈述：colimitIsColimit : IsColimit (colimitCocone F) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evidence that the proposed colimit is the colimit.
-/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := by
    ext x
    induction x using Quot.inductionOn with | h x => ?_
    induction x with
    | of j =>
      change _ = s.ι.app j _
      rw [← w j]
      rfl
    | one =>
      rw [quot_one, map_one]
      rfl
    | mul x y hx hy =>
      rw [quot_mul, map_mul, hx, hy]
      solve_by_elim
/-
**MonCat.Colimits.hasColimits_monCat** 是 Mathlib 中的一个实例，位于命名空间 `MonCat.Colimits`
。
形式化陈述：hasColimits_monCat : HasColimits MonCat where has_colimits_of_shape _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimits_monCat : HasColimits MonCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end MonCat.Colimits

