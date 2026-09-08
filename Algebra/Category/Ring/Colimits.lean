/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for
`Mathlib/Algebra/Category/MonCat/Colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `CommRing` and `RingHom`.
-/

@[expose] public section


universe u v

open CategoryTheory Limits


namespace RingCat.Colimits

/-!
We build the colimit of a diagram in `RingCat` by constructing the
free ring on the disjoint union of all the rings in the diagram,
then taking the quotient by the ring laws within each ring,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

/-- An inductive type representing all ring expressions (without Relations)
on a collection of types indexed by the objects of `J`.
-/
/-
**RingCat.Colimits.Prequotient** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingCat.Colimits`。
形式化陈述：{J : Type v} → [inst : CategoryTheory.SmallCategory J] → CategoryTheory.Fu
nctor J RingCat → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inductive type representing all ring expressions (without Relations)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | mul : Prequotient → Prequotient → Prequotient
/-
**RingCat.Colimits.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The Relation on `Prequotient` saying when two expressions are equal
because of the ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
/-
**RingCat.Colimits.Relation** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingCat.Colimits`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J RingCat) → RingCat.Colimits.Prequotient F → RingCat.Colimits.
Prequotient F → Prop
参数：F : CategoryTheory.Functor J RingCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Relation on `Prequotient` saying when two expressions are equal
because of the ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence Relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  -- Then one Relation per argument of each operation
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  -- And one Relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero

/-- The setoid corresponding to commutative expressions modulo monoid Relations and identifications.
-/
/-
**RingCat.Colimits.colimitSetoid** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.Colimits`。
形式化陈述：colimitSetoid : Setoid (Prequotient F) where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid corresponding to commutative expressions modulo monoid Relations and 
identifications.
-/
instance colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

/-- The underlying type of the colimit of a diagram in `CommRingCat`.
-/
/-
**RingCat.Colimits.ColimitType** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：ColimitType : Type v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying type of the colimit of a diagram in `CommRingCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
/-
**RingCat.Colimits.ColimitType.instZero** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colim
its.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J RingCat) → Zero (RingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J RingCat；RingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero
/-
**RingCat.Colimits.ColimitType.instAdd** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimi
ts.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J RingCat) → Add (RingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J RingCat；RingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.instAdd : Add (ColimitType F) where
  add := Quotient.map₂ add <| fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)
/-
**RingCat.Colimits.ColimitType.instNeg** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimi
ts.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J RingCat) → Neg (RingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J RingCat；RingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
/-
**RingCat.Colimits.ColimitType.AddGroup** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colim
its.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J RingCat) → AddGroup (RingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J RingCat；RingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  neg_add_cancel := Quotient.ind <| fun _ => Quotient.sound <| Relation.neg_add_cancel _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
/-
**RingCat.Colimits.InhabitedColimitType** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.Colim
its`。
形式化陈述：InhabitedColimitType : Inhabited ColimitType F where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := 0
/-
**RingCat.Colimits.ColimitType.AddGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `RingCa
t.Colimits.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J RingCat) → AddGroupWithOne (RingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J RingCat；RingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }
/-
**RingCat.Colimits.** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
    one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.add_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
    mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_zero _
    zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }

@[simp]
/-
**RingCat.Colimits.quot_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingCat.Colimits`。
形式化陈述：quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl

@[simp]
/-
**RingCat.Colimits.quot_one** 是 Mathlib 中的一个定理，位于命名空间 `RingCat.Colimits`。
形式化陈述：quot_one : Quot.mk Setoid.r one = (1 : ColimitType F)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
/-
**RingCat.Colimits.quot_neg** 是 Mathlib 中的一个定理，位于命名空间 `RingCat.Colimits`。
形式化陈述：quot_neg (x : Prequotient F) : Quot.mk Setoid.r (neg x) = -(show ColimitTy
pe F from Quot.mk Setoid.r x)
参数：x : Prequotient F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x) :=
  rfl

@[simp]
/-
**RingCat.Colimits.quot_add** 是 Mathlib 中的一个定理，位于命名空间 `RingCat.Colimits`。
形式化陈述：quot_add (x y) : Quot.mk Setoid.r (add x y) = (show ColimitType F from Quo
t.mk _ x) + (show ColimitType F from Quot.mk _ y)
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) =
      (show ColimitType F from Quot.mk _ x) + (show ColimitType F from Quot.mk _ y) :=
  rfl

@[simp]
/-
**RingCat.Colimits.quot_mul** 是 Mathlib 中的一个定理，位于命名空间 `RingCat.Colimits`。
形式化陈述：quot_mul (x y) : Quot.mk Setoid.r (mul x y) = (show ColimitType F from Quo
t.mk _ x) * (show ColimitType F from Quot.mk _ y)
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show ColimitType F from Quot.mk _ x) * (show ColimitType F from Quot.mk _ y) :=
  rfl

/-- The bundled ring giving the colimit of a diagram. -/
/-
**RingCat.Colimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：colimit : RingCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled ring giving the colimit of a diagram.
-/
def colimit : RingCat :=
  RingCat.of (ColimitType F)

/-- The function from a given ring in the diagram to the colimit ring. -/
/-
**RingCat.Colimits.coconeFun** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：coconeFun (j : J) (x : F.obj j) : ColimitType F
参数：j : J；x : F.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from a given ring in the diagram to the colimit ring.
-/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/-- The ring homomorphism from a given ring in the diagram to the colimit
ring. -/
/-
**RingCat.Colimits.coconeMorphism** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：coconeMorphism (j : J) : F.obj j ⟶ colimit F
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from a given ring in the diagram to the colimit
ring.
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F := ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
/-
**RingCat.Colimits.cocone_naturality** 是 Mathlib 中的一个定理，位于命名空间 `RingCat.Colimits
`。
形式化陈述：cocone_naturality {j j' : J} (f : j ⟶ j') : F.map f ≫ coconeMorphism F j' 
= coconeMorphism F j
参数：f : j ⟶ j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingCat.hom_ext`：hom_ext {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.h
om) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
/-
**RingCat.Colimits.cocone_naturality_components** 是 Mathlib 中的一个定理，位于命名空间 `RingC
at.Colimits`。
形式化陈述：cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) : (coco
neMorphism F j') (F.map f x) = (coconeMorphism F j) x
参数：j j' : J；f : j ⟶ j'；x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingCat.Colimits.cocone_naturality`：cocone_naturality {j j' : J} (f : j 
⟶ j') : F.map f ≫ coconeMorphism F j' = coconeMorphism F j
· 使用引理 `RingCat.comp_apply`：comp_apply {R S T : RingCat} (f : R ⟶ S) (g : S ⟶ T)
 (r : R) : (f ≫ g) r = g (f r)
-/
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f, comp_apply]

set_option backward.defeqAttrib.useBackward true in
/-- The cocone over the proposed colimit ring. -/
/-
**RingCat.Colimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit ring.
-/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free ring on the diagram to the cone point of any other
cocone. -/
@[simp]
/-
**RingCat.Colimits.descFunLift** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J RingCat) →       (s : CategoryTheory.Limits.Cocone F) → RingC
at.Colimits.Prequotient F → ↑s.pt
参数：F : CategoryTheory.Functor J RingCat；s : CategoryTheory.Limits.Cocone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from the free ring on the diagram to the cone point of any other
cocone.
-/
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y

set_option backward.defeqAttrib.useBackward true in
/-- The function from the colimit ring to the cone point of any other cocone. -/
/-
**RingCat.Colimits.descFun** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：descFun (s : Cocone F) : ColimitType F -> s.pt
参数：s : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from the colimit ring to the cone point of any other cocone.
-/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
    | zero j => simp +instances
    | one j => simp +instances
    | neg j x => simp +instances
    | add j x y => simp +instances
    | mul j x y => simp +instances
    | neg_1 x x' r ih => dsimp; rw [ih]
    | add_1 x x' y r ih => dsimp; rw [ih]
    | add_2 x y y' r ih => dsimp; rw [ih]
    | mul_1 x x' y r ih => dsimp; rw [ih]
    | mul_2 x y y' r ih => dsimp; rw [ih]
    | zero_add x => dsimp; rw [zero_add]
    | add_zero x => dsimp; rw [add_zero]
    | one_mul x => dsimp; rw [one_mul]
    | mul_one x => dsimp; rw [mul_one]
    | neg_add_cancel x => dsimp; rw [neg_add_cancel]
    | add_comm x y => dsimp; rw [add_comm]
    | add_assoc x y z => dsimp; rw [add_assoc]
    | mul_assoc x y z => dsimp; rw [mul_assoc]
    | left_distrib x y z => dsimp; rw [mul_add]
    | right_distrib x y z => dsimp; rw [add_mul]
    | zero_mul x => dsimp; rw [zero_mul]
    | mul_zero x => dsimp; rw [mul_zero]

/-- The ring homomorphism from the colimit ring to the cone point of any other
cocone. -/
/-
**RingCat.Colimits.descMorphism** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`。
形式化陈述：descMorphism (s : Cocone F) : colimit F ⟶ s.pt
参数：s : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from the colimit ring to the cone point of any other
cocone.
-/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt := ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y ↦ by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y ↦ by exact Quot.induction_on₂ x y fun a b => rfl }

set_option backward.isDefEq.respectTransparency false in
/-- Evidence that the proposed colimit is the colimit. -/
/-
**RingCat.Colimits.colimitIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `RingCat.Colimits`
。
形式化陈述：colimitIsColimit : IsColimit (colimitCocone F) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evidence that the proposed colimit is the colimit.
-/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
  uniq s m w := hom_ext <| RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j → s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]
/-
**RingCat.Colimits.hasColimits_ringCat** 是 Mathlib 中的一个实例，位于命名空间 `RingCat.Colimi
ts`。
形式化陈述：hasColimits_ringCat : HasColimits RingCat where has_colimits_of_shape _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimits_ringCat : HasColimits RingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end RingCat.Colimits

-- [ROBOT VOICE]:
-- You should pretend for now that this file was automatically generated.
-- It follows the same template as colimits in Mon.
/-
`#print comm_ring` in Lean 3 used to say:

structure comm_ring : Type u → Type u
fields:
comm_ring.zero : Π (α : Type u) [c : comm_ring α], α
comm_ring.one : Π (α : Type u) [c : comm_ring α], α
comm_ring.neg : Π {α : Type u} [c : comm_ring α], α → α
comm_ring.add : Π {α : Type u} [c : comm_ring α], α → α → α
comm_ring.mul : Π {α : Type u} [c : comm_ring α], α → α → α

comm_ring.zero_add : ∀ {α : Type u} [c : comm_ring α] (a : α), 0 + a = a
comm_ring.add_zero : ∀ {α : Type u} [c : comm_ring α] (a : α), a + 0 = a
comm_ring.one_mul : ∀ {α : Type u} [c : comm_ring α] (a : α), 1 * a = a
comm_ring.mul_one : ∀ {α : Type u} [c : comm_ring α] (a : α), a * 1 = a
comm_ring.add_left_neg : ∀ {α : Type u} [c : comm_ring α] (a : α), -a + a = 0
comm_ring.add_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a + b = b + a
comm_ring.mul_comm : ∀ {α : Type u} [c : comm_ring α] (a b : α), a * b = b * a
comm_ring.add_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a + b + c_1 = a + (b + c_1)
comm_ring.mul_assoc : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
comm_ring.left_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α),
                                                            a * (b + c_1) = a * b + a * c_1
comm_ring.right_distrib : ∀ {α : Type u} [c : comm_ring α] (a b c_1 : α),
                                                            (a + b) * c_1 = a * c_1 + b * c_1
-/
namespace CommRingCat.Colimits

/-!
We build the colimit of a diagram in `CommRingCat` by constructing the
free commutative ring on the disjoint union of all the commutative rings in the diagram,
then taking the quotient by the commutative ring laws within each commutative ring,
and the identifications given by the morphisms in the diagram.
-/


variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

/-- An inductive type representing all commutative ring expressions (without Relations)
on a collection of types indexed by the objects of `J`.
-/
/-
**CommRingCat.Colimits.Prequotient** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommRingCat.Coli
mits`。
形式化陈述：{J : Type v} → [inst : CategoryTheory.SmallCategory J] → CategoryTheory.Fu
nctor J CommRingCat → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inductive type representing all commutative ring expressions (without Relatio
ns)
on a collection of types indexed by the objects of `J`.
-/
inductive Prequotient -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient -- Then one generator for each operation
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | mul : Prequotient → Prequotient → Prequotient
/-
**CommRingCat.Colimits.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/-- The Relation on `Prequotient` saying when two expressions are equal
because of the commutative ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
/-
**CommRingCat.Colimits.Relation** 是 Mathlib 中的一个归纳类型，位于命名空间 `CommRingCat.Colimit
s`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J CommRingCat) →       CommRingCat.Colimits.Prequotient F → Com
mRingCat.Colimits.Prequotient F → Prop
参数：F : CategoryTheory.Functor J CommRingCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Relation on `Prequotient` saying when two expressions are equal
because of the commutative ring laws, or
because one element is mapped to another by a morphism in the diagram.
-/
inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence Relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  -- Then one Relation per argument of each operation
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  -- And one Relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | mul_comm : ∀ x y, Relation (mul x y) (mul y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero

/-- The setoid corresponding to commutative expressions modulo monoid Relations and identifications.
-/
/-
**CommRingCat.Colimits.colimitSetoid** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.Coli
mits`。
形式化陈述：colimitSetoid : Setoid (Prequotient F) where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid corresponding to commutative expressions modulo monoid Relations and 
identifications.
-/
instance colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

/-- The underlying type of the colimit of a diagram in `CommRingCat`.
-/
/-
**CommRingCat.Colimits.ColimitType** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Colimi
ts`。
形式化陈述：ColimitType : Type v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying type of the colimit of a diagram in `CommRingCat`.
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
/-
**CommRingCat.Colimits.ColimitType.instZero** 是 Mathlib 中的一个定义，位于命名空间 `CommRingC
at.Colimits.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J CommRingCat) → Zero (CommRingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J CommRingCat；CommRingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero
/-
**CommRingCat.Colimits.ColimitType.instAdd** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCa
t.Colimits.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J CommRingCat) → Add (CommRingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J CommRingCat；CommRingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.instAdd : Add (ColimitType F) where
  add := Quotient.map₂ add <| fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)
/-
**CommRingCat.Colimits.ColimitType.instNeg** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCa
t.Colimits.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J CommRingCat) → Neg (CommRingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J CommRingCat；CommRingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
/-
**CommRingCat.Colimits.ColimitType.AddGroup** 是 Mathlib 中的一个定义，位于命名空间 `CommRingC
at.Colimits.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J CommRingCat) → AddGroup (CommRingCat.Colimits.ColimitType F)
参数：F : CategoryTheory.Functor J CommRingCat；CommRingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
  zero_add := Quotient.ind <| fun _ => Quotient.sound <| Relation.zero_add _
  add_zero := Quotient.ind <| fun _ => Quotient.sound <| Relation.add_zero _
  neg_add_cancel := Quotient.ind <| fun _ => Quotient.sound <| Relation.neg_add_cancel _
  add_assoc := Quotient.ind <| fun _ => Quotient.ind₂ <| fun _ _ =>
    Quotient.sound <| Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
/-
**CommRingCat.Colimits.InhabitedColimitType** 是 Mathlib 中的一个实例，位于命名空间 `CommRingC
at.Colimits`。
形式化陈述：InhabitedColimitType : Inhabited ColimitType F where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance InhabitedColimitType : Inhabited <| ColimitType F where
  default := 0
/-
**CommRingCat.Colimits.ColimitType.AddGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Co
mmRingCat.Colimits.ColimitType`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J CommRingCat) → AddGroupWithOne (CommRingCat.Colimits.ColimitT
ype F)
参数：F : CategoryTheory.Functor J CommRingCat；CommRingCat.Colimits.ColimitType F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }
/-
**CommRingCat.Colimits.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
    one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.one_mul _
    mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_one _
    add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.add_comm _ _
    mul_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound <| Relation.mul_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
    mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.mul_zero _
    zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound <| Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }

@[simp]
/-
**CommRingCat.Colimits.quot_zero** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Colimits
`。
形式化陈述：quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl

@[simp]
/-
**CommRingCat.Colimits.quot_one** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Colimits`
。
形式化陈述：quot_one : Quot.mk Setoid.r one = (1 : ColimitType F)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
/-
**CommRingCat.Colimits.quot_neg** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Colimits`
。
形式化陈述：quot_neg (x : Prequotient F) : Quot.mk Setoid.r (neg x) = -(show ColimitTy
pe F from Quot.mk Setoid.r x)
参数：x : Prequotient F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x) :=
  rfl

-- Porting note: Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- unless we use `by exact` to change the elaboration order.
@[simp]
/-
**CommRingCat.Colimits.quot_add** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Colimits`
。
形式化陈述：quot_add (x y) : Quot.mk Setoid.r (add x y) = (show ColimitType F from Quo
t.mk _ x) + (show ColimitType F from Quot.mk _ y)
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) =
      (show ColimitType F from Quot.mk _ x) + (show ColimitType F from Quot.mk _ y) :=
  rfl

-- Porting note: Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- unless we use `by exact` to change the elaboration order.
@[simp]
/-
**CommRingCat.Colimits.quot_mul** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Colimits`
。
形式化陈述：quot_mul (x y) : Quot.mk Setoid.r (mul x y) = (show ColimitType F from Quo
t.mk _ x) * (show ColimitType F from Quot.mk _ y)
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show ColimitType F from Quot.mk _ x) * (show ColimitType F from Quot.mk _ y) :=
  rfl

/-- The bundled commutative ring giving the colimit of a diagram. -/
/-
**CommRingCat.Colimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Colimits`。
形式化陈述：colimit : CommRingCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled commutative ring giving the colimit of a diagram.
-/
def colimit : CommRingCat :=
  CommRingCat.of (ColimitType F)

/-- The function from a given commutative ring in the diagram to the colimit commutative ring. -/
/-
**CommRingCat.Colimits.coconeFun** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Colimits
`。
形式化陈述：coconeFun (j : J) (x : F.obj j) : ColimitType F
参数：j : J；x : F.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from a given commutative ring in the diagram to the colimit commuta
tive ring.
-/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/-- The ring homomorphism from a given commutative ring in the diagram to the colimit commutative
ring. -/
/-
**CommRingCat.Colimits.coconeMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Col
imits`。
形式化陈述：coconeMorphism (j : J) : F.obj j ⟶ colimit F
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from a given commutative ring in the diagram to the colimi
t commutative
ring.
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F := ofHom <|
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
/-
**CommRingCat.Colimits.cocone_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.
Colimits`。
形式化陈述：cocone_naturality {j j' : J} (f : j ⟶ j') : F.map f ≫ coconeMorphism F j' 
= coconeMorphism F j
参数：f : j ⟶ j'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
/-
**CommRingCat.Colimits.cocone_naturality_components** 是 Mathlib 中的一个定理，位于命名空间 `C
ommRingCat.Colimits`。
形式化陈述：cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) : (coco
neMorphism F j') (F.map f x) = (coconeMorphism F j) x
参数：j j' : J；f : j ⟶ j'；x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CommRingCat.Colimits.cocone_naturality`：cocone_naturality {j j' : J} (f 
: j ⟶ j') : F.map f ≫ coconeMorphism F j' = coconeMorphism F j
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
-/
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f, comp_apply]

set_option backward.defeqAttrib.useBackward true in
/-- The cocone over the proposed colimit commutative ring. -/
/-
**CommRingCat.Colimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Coli
mits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit commutative ring.
-/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free commutative ring on the diagram to the cone point of any other
cocone. -/
@[simp]
/-
**CommRingCat.Colimits.descFunLift** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Colimi
ts`。
形式化陈述：{J : Type v} →   [inst : CategoryTheory.SmallCategory J] →     (F : Catego
ryTheory.Functor J CommRingCat) →       (s : CategoryTheory.Limits.Cocone F) → C
ommRingCat.Colimits.Prequotient F → ↑s.pt
参数：F : CategoryTheory.Functor J CommRingCat；s : CategoryTheory.Limits.Cocone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from the free commutative ring on the diagram to the cone point of 
any other
cocone.
-/
def descFunLift (s : Cocone F) : Prequotient F → s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y

set_option backward.defeqAttrib.useBackward true in
/-- The function from the colimit commutative ring to the cone point of any other cocone. -/
/-
**CommRingCat.Colimits.descFun** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Colimits`。
形式化陈述：descFun (s : Cocone F) : ColimitType F -> s.pt
参数：s : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from the colimit commutative ring to the cone point of any other co
cone.
-/
def descFun (s : Cocone F) : ColimitType F → s.pt := by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
    | zero j => simp +instances
    | one j => simp +instances
    | neg j x => simp +instances
    | add j x y => simp +instances
    | mul j x y => simp +instances
    | neg_1 x x' r ih => dsimp; rw [ih]
    | add_1 x x' y r ih => dsimp; rw [ih]
    | add_2 x y y' r ih => dsimp; rw [ih]
    | mul_1 x x' y r ih => dsimp; rw [ih]
    | mul_2 x y y' r ih => dsimp; rw [ih]
    | zero_add x => dsimp; rw [zero_add]
    | add_zero x => dsimp; rw [add_zero]
    | one_mul x => dsimp; rw [one_mul]
    | mul_one x => dsimp; rw [mul_one]
    | neg_add_cancel x => dsimp; rw [neg_add_cancel]
    | add_comm x y => dsimp; rw [add_comm]
    | mul_comm x y => dsimp; rw [mul_comm]
    | add_assoc x y z => dsimp; rw [add_assoc]
    | mul_assoc x y z => dsimp; rw [mul_assoc]
    | left_distrib x y z => dsimp; rw [mul_add]
    | right_distrib x y z => dsimp; rw [add_mul]
    | zero_mul x => dsimp; rw [zero_mul]
    | mul_zero x => dsimp; rw [mul_zero]

/-- The ring homomorphism from the colimit commutative ring to the cone point of any other
cocone. -/
/-
**CommRingCat.Colimits.descMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Colim
its`。
形式化陈述：descMorphism (s : Cocone F) : colimit F ⟶ s.pt
参数：s : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from the colimit commutative ring to the cone point of any
 other
cocone.
-/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt := ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y ↦ by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y ↦ by exact Quot.induction_on₂ x y fun a b => rfl }

set_option backward.isDefEq.respectTransparency false in
/-- Evidence that the proposed colimit is the colimit. -/
/-
**CommRingCat.Colimits.colimitIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.C
olimits`。
形式化陈述：colimitIsColimit : IsColimit (colimitCocone F) where desc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evidence that the proposed colimit is the colimit.
-/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc := fun s ↦ descMorphism F s
  uniq := fun s m w ↦ hom_ext <| RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j → s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]
/-
**CommRingCat.Colimits.hasColimits_commRingCat** 是 Mathlib 中的一个实例，位于命名空间 `CommRi
ngCat.Colimits`。
形式化陈述：hasColimits_commRingCat : HasColimits CommRingCat where has_colimits_of_sh
ape _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimits_commRingCat : HasColimits CommRingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end CommRingCat.Colimits

