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

/--
Inductive type `Prequotient` / 归纳类型 `Prequotient`

English:
inductive Prequotient
  constructors (6):
    - of: forall (j : J) (_ : F.obj j), Prequotient
    - zero: Prequotient
    - one: Prequotient
    - neg: Prequotient -> Prequotient
    - add: Prequotient -> Prequotient -> Prequotient
    - mul: Prequotient -> Prequotient -> Prequotient

中文:
归纳类型 Prequotient
  构造子 (6 个):
    - of: 对任意 (j : J) (_ : F.obj j), Prequotient
    - zero: Prequotient
    - one: Prequotient
    - neg: Prequotient -> Prequotient
    - add: Prequotient -> Prequotient -> Prequotient
    - mul: Prequotient -> Prequotient -> Prequotient
-/
inductive Prequotient
  -- There's always `of`
  | of : forall (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient -> Prequotient
  | add : Prequotient -> Prequotient -> Prequotient
  | mul : Prequotient -> Prequotient -> Prequotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Prequotient F)
  body: ⟨Prequotient.zero⟩

中文:
实例 :
  签名: 可居 (Prequotient F)
  定义体: ⟨Prequotient.zero⟩

Depends on / 依赖: Prequotient, Prequotient.zero
-/
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/--
Inductive type `Relation` / 归纳类型 `Relation`

English:
inductive Relation
  parameters: : Prequotient F -> Prequotient F -> Prop -- Make it an equivalence Relation:
  constructors (26):
    - refl: forall x, Relation x x
    - symm: forall (x y) (_ : Relation x y), Relation y x
    - trans: forall (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
    - map: forall (j j' : J) (f : j ⟶ j') (x : F.obj j), Relation (Prequotient.of j' (F.map f x)) (Prequotient.of j x)
    - zero: forall j, Relation (Prequotient.of j 0) zero
    - one: forall j, Relation (Prequotient.of j 1) one
    - neg: forall (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
    - add: forall (j) (x y : F.obj j), Relation (Prequotient.of j (x + y)) (add (Prequotient.of j x) (Prequotient.of j y))
    - mul: forall (j) (x y : F.obj j), Relation (Prequotient.of j (x * y)) (mul (Prequotient.of j x) (Prequotient.of j y))
    - neg_1: forall (x x') (_ : Relation x x'), Relation (neg x) (neg x')
    - add_1: forall (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
    - add_2: forall (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
    - mul_1: forall (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
    - mul_2: forall (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    - zero_add: forall x, Relation (add zero x) x
    - add_zero: forall x, Relation (add x zero) x
    - one_mul: forall x, Relation (mul one x) x
    - mul_one: forall x, Relation (mul x one) x
    - neg_add_cancel: forall x, Relation (add (neg x) x) zero
    - add_comm: forall x y, Relation (add x y) (add y x)
    - add_assoc: forall x y z, Relation (add (add x y) z) (add x (add y z))
    - mul_assoc: forall x y z, Relation (mul (mul x y) z) (mul x (mul y z))
    - left_distrib: forall x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
    - right_distrib: forall x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
    - zero_mul: forall x, Relation (mul zero x) zero
    - mul_zero: forall x, Relation (mul x zero) zero

中文:
归纳类型 关系
  参数: : Prequotient F -> Prequotient F -> 命题 -- Make it an equivalence 关系:
  构造子 (26 个):
    - refl: 对任意 x, 关系 x x
    - symm: 对任意 (x y) (_ : 关系 x y), 关系 y x
    - trans: 对任意 (x y z) (_ : 关系 x y) (_ : 关系 y z), 关系 x z
    - map: 对任意 (j j' : J) (f : j ⟶ j') (x : F.obj j), 关系 (Prequotient.of j' (F.map f x)) (Prequotient.of j x)
    - zero: 对任意 j, 关系 (Prequotient.of j 0) zero
    - one: 对任意 j, 关系 (Prequotient.of j 1) one
    - neg: 对任意 (j) (x : F.obj j), 关系 (Prequotient.of j (-x)) (neg (Prequotient.of j x))
    - add: 对任意 (j) (x y : F.obj j), 关系 (Prequotient.of j (x + y)) (add (Prequotient.of j x) (Prequotient.of j y))
    - mul: 对任意 (j) (x y : F.obj j), 关系 (Prequotient.of j (x * y)) (mul (Prequotient.of j x) (Prequotient.of j y))
    - neg_1: 对任意 (x x') (_ : 关系 x x'), 关系 (neg x) (neg x')
    - add_1: 对任意 (x x' y) (_ : 关系 x x'), 关系 (add x y) (add x' y)
    - add_2: 对任意 (x y y') (_ : 关系 y y'), 关系 (add x y) (add x y')
    - mul_1: 对任意 (x x' y) (_ : 关系 x x'), 关系 (mul x y) (mul x' y)
    - mul_2: 对任意 (x y y') (_ : 关系 y y'), 关系 (mul x y) (mul x y')
    - zero_add: 对任意 x, 关系 (add zero x) x
    - add_zero: 对任意 x, 关系 (add x zero) x
    - one_mul: 对任意 x, 关系 (mul one x) x
    - mul_one: 对任意 x, 关系 (mul x one) x
    - neg_add_cancel: 对任意 x, 关系 (add (neg x) x) zero
    - add_comm: 对任意 x y, 关系 (add x y) (add y x)
    - add_assoc: 对任意 x y z, 关系 (add (add x y) z) (add x (add y z))
    - mul_assoc: 对任意 x y z, 关系 (mul (mul x y) z) (mul x (mul y z))
    - left_distrib: 对任意 x y z, 关系 (mul x (add y z)) (add (mul x y) (mul x z))
    - right_distrib: 对任意 x y z, 关系 (mul (add x y) z) (add (mul x z) (mul y z))
    - zero_mul: 对任意 x, 关系 (mul zero x) zero
    - mul_zero: 对任意 x, 关系 (mul x zero) zero
-/
inductive Relation : Prequotient F -> Prequotient F -> Prop -- Make it an equivalence Relation:
  | refl : forall x, Relation x x
  | symm : forall (x y) (_ : Relation x y), Relation y x
  | trans : forall (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : forall (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : forall j, Relation (Prequotient.of j 0) zero
  | one : forall j, Relation (Prequotient.of j 1) one
  | neg : forall (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : forall (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : forall (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  -- Then one Relation per argument of each operation
  | neg_1 : forall (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : forall (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : forall (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : forall (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : forall (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  -- And one Relation per axiom
  | zero_add : forall x, Relation (add zero x) x
  | add_zero : forall x, Relation (add x zero) x
  | one_mul : forall x, Relation (mul one x) x
  | mul_one : forall x, Relation (mul x one) x
  | neg_add_cancel : forall x, Relation (add (neg x) x) zero
  | add_comm : forall x y, Relation (add x y) (add y x)
  | add_assoc : forall x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : forall x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : forall x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : forall x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : forall x, Relation (mul zero x) zero
  | mul_zero : forall x, Relation (mul x zero) zero

/--
Instance `colimitSetoid` / 实例 `colimitSetoid`

English:
instance colimitSetoid
  signature: : Setoid (Prequotient F) where
  body: Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

中文:
实例 colimitSetoid
  签名: : 集合等价关系 (Prequotient F) where
  定义体: Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

Depends on / 依赖: Relation
-/
instance colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

/--
Definition of `ColimitType` / `ColimitType` 的定义

English:
definition ColimitType
  signature: : Type v
  body: Quotient (colimitSetoid F)

中文:
定义 ColimitType
  签名: : 类型v
  定义体: Quotient (colimitSetoid F)

Depends on / 依赖: Quotient, colimitSetoid
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)

/--
Instance `ColimitType.instZero` / 实例 `ColimitType.instZero`

English:
instance ColimitType.instZero
  signature: : Zero (ColimitType F) where zero
  body: Quotient.mk _ zero

中文:
实例 ColimitType.instZero
  签名: : 零 (ColimitType F) where zero
  定义体: Quotient.mk _ zero

Depends on / 依赖: Quotient, Quotient.mk
-/
instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero

/--
Instance `ColimitType.instAdd` / 实例 `ColimitType.instAdd`

English:
instance ColimitType.instAdd
  signature: : Add (ColimitType F) where
  body: Quotient.map₂ add fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

中文:
实例 ColimitType.instAdd
  签名: : 加法 (ColimitType F) where
  定义体: Quotient.map₂ add fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

Depends on / 依赖: Quotient, Quotient.map
-/
instance ColimitType.instAdd : Add (ColimitType F) where
add := Quotient.map₂ add fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

/--
Instance `ColimitType.instNeg` / 实例 `ColimitType.instNeg`

English:
instance ColimitType.instNeg
  signature: : Neg (ColimitType F) where
  body: Quotient.map neg Relation.neg_1

中文:
实例 ColimitType.instNeg
  签名: : 取负 (ColimitType F) where
  定义体: Quotient.map neg Relation.neg_1

Depends on / 依赖: Quotient, Quotient.map, Relation, Relation.neg_1, neg_1
-/
instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1

/--
Instance `ColimitType.AddGroup` / 实例 `ColimitType.AddGroup`

English:
instance ColimitType.AddGroup
  signature: : AddGroup (ColimitType F) where
  body: Quotient.map neg Relation.neg_1
zero_add := Quotient.ind fun _ => Quotient.sound Relation.zero_add _
add_zero := Quotient.ind fun _ => Quotient.sound Relation.add_zero _
neg_add_cancel := Quotient.ind fun _ => Quotient.sound Relation.neg_add_cancel _
add_assoc := Quotient.ind fun _ => Quotient.ind₂ 

中文:
实例 ColimitType.加法群
  签名: : 加法群 (ColimitType F) where
  定义体: Quotient.map neg Relation.neg_1
zero_add := Quotient.ind fun _ => Quotient.sound Relation.zero_add _
add_zero := Quotient.ind fun _ => Quotient.sound Relation.add_zero _
neg_add_cancel := Quotient.ind fun _ => Quotient.sound Relation.neg_add_cancel _
add_assoc := Quotient.ind fun _ => Quotient.ind₂ 

Depends on / 依赖: Quotient, Quotient.map, Relation, Relation.neg_1, neg_1
-/
instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
zero_add := Quotient.ind fun _ => Quotient.sound Relation.zero_add _
add_zero := Quotient.ind fun _ => Quotient.sound Relation.add_zero _
neg_add_cancel := Quotient.ind fun _ => Quotient.sound Relation.neg_add_cancel _
add_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
Quotient.sound Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

/--
Instance `InhabitedColimitType` / 实例 `InhabitedColimitType`

English:
instance InhabitedColimitType
  signature: : Inhabited ColimitType F where
  body: 0

中文:
实例 InhabitedColimitType
  签名: : 可居 ColimitType F where
  定义体: 0
-/
instance InhabitedColimitType : Inhabited ColimitType F where
  default := 0

/--
Instance `ColimitType.AddGroupWithOne` / 实例 `ColimitType.AddGroupWithOne`

English:
instance ColimitType.AddGroupWithOne
  signature: : AddGroupWithOne (ColimitType F)
  body: { ColimitType.AddGroup F with one := Quotient.mk _ one }

中文:
实例 ColimitType.加法带幺群
  签名: : 加法带幺群 (ColimitType F)
  定义体: { ColimitType.AddGroup F with one := Quotient.mk _ one }

Depends on / 依赖: AddGroup, ColimitType, ColimitType.AddGroup, Quotient, Quotient.mk
-/
instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring (ColimitType.{v} F)
  body: { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.one_mul _
mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_one _
add_comm := fun x y => Quot.induction_on

中文:
实例 :
  签名: 环 (ColimitType.{v} F)
  定义体: { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.one_mul _
mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_one _
add_comm := fun x y => Quot.induction_on

Depends on / 依赖: AddGroupWithOne, ColimitType, ColimitType.AddGroupWithOne, Prequotient, Prequotient.mul, Quot.inductionOn, Quot.induction_on, Quot.map, Quot.sound, Relation, Relation.add_comm, Relation.mul_1, Relation.mul_2, Relation.mul_assoc, Relation.mul_one, Relation.one_mul, add_comm, inductionOn, mul_1, mul_2
-/
instance : Ring (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.one_mul _
mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_one _
add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound Relation.add_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_zero _
zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }

@[simp]
/--
theorem `quot_zero` / 定理 `quot_zero`

English:
theorem quot_zero
  statement: Quot.mk Setoid.r zero = (0 : ColimitType F)
  proof: rfl

@[simp]

中文:
定理 quot_zero
  结论: 商.mk 集合等价关系.r zero = (0 : ColimitType F)
  证明: rfl

@[simp]
-/
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl

@[simp]
/--
theorem `quot_one` / 定理 `quot_one`

English:
theorem quot_one
  statement: Quot.mk Setoid.r one = (1 : ColimitType F)
  proof: rfl

@[simp]

中文:
定理 quot_one
  结论: 商.mk 集合等价关系.r one = (1 : ColimitType F)
  证明: rfl

@[simp]
-/
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
/--
theorem `quot_neg` / 定理 `quot_neg`

English:
theorem quot_neg
  given: (x : Prequotient F)
  proof: rfl

@[simp]

中文:
定理 quot_neg
  条件: (x : Prequotient F)
  证明: rfl

@[simp]
-/
theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x) :=
  rfl

@[simp]
/--
theorem `quot_add` / 定理 `quot_add`

English:
theorem quot_add
  given: (x y)
  proof: rfl

@[simp]

中文:
定理 quot_add
  条件: (x y)
  证明: rfl

@[simp]
-/
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) =
      (show ColimitType F from Quot.mk _ x) + (show ColimitType F from Quot.mk _ y) :=
  rfl

@[simp]
/--
theorem `quot_mul` / 定理 `quot_mul`

English:
theorem quot_mul
  given: (x y)
  proof: rfl

中文:
定理 quot_mul
  条件: (x y)
  证明: rfl
-/
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show ColimitType F from Quot.mk _ x) * (show ColimitType F from Quot.mk _ y) :=
  rfl

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : RingCat
  body: RingCat.of (ColimitType F)

中文:
定义 colimit
  签名: : 环范畴
  定义体: RingCat.of (ColimitType F)

Depends on / 依赖: ColimitType, RingCat, RingCat.of
-/
def colimit : RingCat :=
  RingCat.of (ColimitType F)

/--
Definition of `coconeFun` / `coconeFun` 的定义

English:
definition coconeFun
  signature: (j : J) (x : F.obj j)
  body: Quot.mk _ (Prequotient.of j x)

中文:
定义 coconeFun
  签名: (j : J) (x : F.obj j)
  定义体: Quot.mk _ (Prequotient.of j x)

Depends on / 依赖: Prequotient, Prequotient.of, Quot.mk
-/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/--
Definition of `coconeMorphism` / `coconeMorphism` 的定义

English:
definition coconeMorphism
  signature: (j : J)
  body: ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]

中文:
定义 coconeMorphism
  签名: (j : J)
  定义体: ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F := ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
/--
theorem `cocone_naturality` / 定理 `cocone_naturality`

English:
theorem cocone_naturality
  given: {j j' : J} (f : j ⟶ j')
  proof: by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]

中文:
定理 cocone_naturality
  条件: {j j' : J} (f : j ⟶ j')
  证明: by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]

Depends on / 依赖: Quot.sound, Relation, Relation.map
-/
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
/--
theorem `cocone_naturality_components` / 定理 `cocone_naturality_components`

English:
theorem cocone_naturality_components
  given: (j j' : J) (f : j ⟶ j') (x : F.obj j)
  proof: by
  rw [← cocone_naturality F f]; rw [comp_apply]

中文:
定理 cocone_naturality_components
  条件: (j j' : J) (f : j ⟶ j') (x : F.obj j)
  证明: by
  rw [← cocone_naturality F f]; rw [comp_apply]

Depends on / 依赖: cocone_naturality, comp_apply
-/
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]; rw [comp_apply]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit F
  ι := { app := coconeMorphism F }

中文:
定义 colimitCocone
  签名: : 余锥 F where
  定义体: colimit F
  ι := { app := coconeMorphism F }

Depends on / 依赖: colimit
-/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free ring on the diagram to the cone point of any other
cocone. -/
@[simp]
/--
Definition of `descFunLift` / `descFunLift` 的定义

English:
definition descFunLift
  signature: (s : Cocone F)

中文:
定义 descFunLift
  签名: (s : 余锥 F)
-/
def descFunLift (s : Cocone F) : Prequotient F -> s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `descFun` / `descFun` 的定义

English:
definition descFun
  signature: (s : Cocone F)
  body: by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
    | zero j => simp

中文:
定义 descFun
  签名: (s : 余锥 F)
  定义体: by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
    | zero j => simp

Depends on / 依赖: Hom.hom, Quot.lift, RingHom, RingHom.congr_fun, add_1, add_2, congr_fun, descFunLift, fapply, ih.symm, ih1.trans, instances, naturality, neg_1
-/
def descFun (s : Cocone F) : ColimitType F -> s.pt := by
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

/--
Definition of `descMorphism` / `descMorphism` 的定义

English:
definition descMorphism
  signature: (s : Cocone F)
  body: ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y => by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y => by exact Quot.induction_on₂ x y fun a b => rfl }

中文:
定义 descMorphism
  签名: (s : 余锥 F)
  定义体: ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y => by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y => by exact Quot.induction_on₂ x y fun a b => rfl }
-/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt := ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y => by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y => by exact Quot.induction_on₂ x y fun a b => rfl }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitIsColimit` / `colimitIsColimit` 的定义

English:
definition colimitIsColimit
  signature: : IsColimit (colimitCocone F) where
  body: descMorphism F s
uniq s m w := hom_ext RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j -> s.pt)) (w j)) 

中文:
定义 colimitIsColimit
  签名: : 是余极限 (colimitCocone F) where
  定义体: descMorphism F s
uniq s m w := hom_ext RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j -> s.pt)) (w j)) 

Depends on / 依赖: descMorphism
-/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc s := descMorphism F s
uniq s m w := hom_ext RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j -> s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]

/--
Instance `hasColimits_ringCat` / 实例 `hasColimits_ringCat`

English:
instance hasColimits_ringCat
  signature: : HasColimits RingCat where
  body: { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

中文:
实例 hasColimits_ringCat
  签名: : 有余极限 环范畴 where
  定义体: { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimitCocone, colimitIsColimit, has_colimit, isColimit
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

/--
Inductive type `Prequotient` / 归纳类型 `Prequotient`

English:
inductive Prequotient
  parameters: -- There's always `of`
  constructors (6):
    - of: forall (j : J) (_ : F.obj j), Prequotient -- Then one generator for each operation
    - zero: Prequotient
    - one: Prequotient
    - neg: Prequotient -> Prequotient
    - add: Prequotient -> Prequotient -> Prequotient
    - mul: Prequotient -> Prequotient -> Prequotient

中文:
归纳类型 Prequotient
  参数: -- There's always `of`
  构造子 (6 个):
    - of: 对任意 (j : J) (_ : F.obj j), Prequotient -- Then one generator for each operation
    - zero: Prequotient
    - one: Prequotient
    - neg: Prequotient -> Prequotient
    - add: Prequotient -> Prequotient -> Prequotient
    - mul: Prequotient -> Prequotient -> Prequotient
-/
inductive Prequotient -- There's always `of`
  | of : forall (j : J) (_ : F.obj j), Prequotient -- Then one generator for each operation
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient -> Prequotient
  | add : Prequotient -> Prequotient -> Prequotient
  | mul : Prequotient -> Prequotient -> Prequotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Prequotient F)
  body: ⟨Prequotient.zero⟩

中文:
实例 :
  签名: 可居 (Prequotient F)
  定义体: ⟨Prequotient.zero⟩

Depends on / 依赖: Prequotient, Prequotient.zero
-/
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.zero⟩

open Prequotient

/--
Inductive type `Relation` / 归纳类型 `Relation`

English:
inductive Relation
  parameters: : Prequotient F -> Prequotient F -> Prop -- Make it an equivalence Relation:
  constructors (27):
    - refl: forall x, Relation x x
    - symm: forall (x y) (_ : Relation x y), Relation y x
    - trans: forall (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
    - map: forall (j j' : J) (f : j ⟶ j') (x : F.obj j), Relation (Prequotient.of j' (F.map f x)) (Prequotient.of j x)
    - zero: forall j, Relation (Prequotient.of j 0) zero
    - one: forall j, Relation (Prequotient.of j 1) one
    - neg: forall (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
    - add: forall (j) (x y : F.obj j), Relation (Prequotient.of j (x + y)) (add (Prequotient.of j x) (Prequotient.of j y))
    - mul: forall (j) (x y : F.obj j), Relation (Prequotient.of j (x * y)) (mul (Prequotient.of j x) (Prequotient.of j y))
    - neg_1: forall (x x') (_ : Relation x x'), Relation (neg x) (neg x')
    - add_1: forall (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
    - add_2: forall (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
    - mul_1: forall (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
    - mul_2: forall (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    - zero_add: forall x, Relation (add zero x) x
    - add_zero: forall x, Relation (add x zero) x
    - one_mul: forall x, Relation (mul one x) x
    - mul_one: forall x, Relation (mul x one) x
    - neg_add_cancel: forall x, Relation (add (neg x) x) zero
    - add_comm: forall x y, Relation (add x y) (add y x)
    - mul_comm: forall x y, Relation (mul x y) (mul y x)
    - add_assoc: forall x y z, Relation (add (add x y) z) (add x (add y z))
    - mul_assoc: forall x y z, Relation (mul (mul x y) z) (mul x (mul y z))
    - left_distrib: forall x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
    - right_distrib: forall x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
    - zero_mul: forall x, Relation (mul zero x) zero
    - mul_zero: forall x, Relation (mul x zero) zero

中文:
归纳类型 关系
  参数: : Prequotient F -> Prequotient F -> 命题 -- Make it an equivalence 关系:
  构造子 (27 个):
    - refl: 对任意 x, 关系 x x
    - symm: 对任意 (x y) (_ : 关系 x y), 关系 y x
    - trans: 对任意 (x y z) (_ : 关系 x y) (_ : 关系 y z), 关系 x z
    - map: 对任意 (j j' : J) (f : j ⟶ j') (x : F.obj j), 关系 (Prequotient.of j' (F.map f x)) (Prequotient.of j x)
    - zero: 对任意 j, 关系 (Prequotient.of j 0) zero
    - one: 对任意 j, 关系 (Prequotient.of j 1) one
    - neg: 对任意 (j) (x : F.obj j), 关系 (Prequotient.of j (-x)) (neg (Prequotient.of j x))
    - add: 对任意 (j) (x y : F.obj j), 关系 (Prequotient.of j (x + y)) (add (Prequotient.of j x) (Prequotient.of j y))
    - mul: 对任意 (j) (x y : F.obj j), 关系 (Prequotient.of j (x * y)) (mul (Prequotient.of j x) (Prequotient.of j y))
    - neg_1: 对任意 (x x') (_ : 关系 x x'), 关系 (neg x) (neg x')
    - add_1: 对任意 (x x' y) (_ : 关系 x x'), 关系 (add x y) (add x' y)
    - add_2: 对任意 (x y y') (_ : 关系 y y'), 关系 (add x y) (add x y')
    - mul_1: 对任意 (x x' y) (_ : 关系 x x'), 关系 (mul x y) (mul x' y)
    - mul_2: 对任意 (x y y') (_ : 关系 y y'), 关系 (mul x y) (mul x y')
    - zero_add: 对任意 x, 关系 (add zero x) x
    - add_zero: 对任意 x, 关系 (add x zero) x
    - one_mul: 对任意 x, 关系 (mul one x) x
    - mul_one: 对任意 x, 关系 (mul x one) x
    - neg_add_cancel: 对任意 x, 关系 (add (neg x) x) zero
    - add_comm: 对任意 x y, 关系 (add x y) (add y x)
    - mul_comm: 对任意 x y, 关系 (mul x y) (mul y x)
    - add_assoc: 对任意 x y z, 关系 (add (add x y) z) (add x (add y z))
    - mul_assoc: 对任意 x y z, 关系 (mul (mul x y) z) (mul x (mul y z))
    - left_distrib: 对任意 x y z, 关系 (mul x (add y z)) (add (mul x y) (mul x z))
    - right_distrib: 对任意 x y z, 关系 (mul (add x y) z) (add (mul x z) (mul y z))
    - zero_mul: 对任意 x, 关系 (mul zero x) zero
    - mul_zero: 对任意 x, 关系 (mul x zero) zero
-/
inductive Relation : Prequotient F -> Prequotient F -> Prop -- Make it an equivalence Relation:
  | refl : forall x, Relation x x
  | symm : forall (x y) (_ : Relation x y), Relation y x
  | trans : forall (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : forall (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : forall j, Relation (Prequotient.of j 0) zero
  | one : forall j, Relation (Prequotient.of j 1) one
  | neg : forall (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : forall (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : forall (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  -- Then one Relation per argument of each operation
  | neg_1 : forall (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : forall (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : forall (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : forall (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : forall (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  -- And one Relation per axiom
  | zero_add : forall x, Relation (add zero x) x
  | add_zero : forall x, Relation (add x zero) x
  | one_mul : forall x, Relation (mul one x) x
  | mul_one : forall x, Relation (mul x one) x
  | neg_add_cancel : forall x, Relation (add (neg x) x) zero
  | add_comm : forall x y, Relation (add x y) (add y x)
  | mul_comm : forall x y, Relation (mul x y) (mul y x)
  | add_assoc : forall x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : forall x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : forall x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : forall x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : forall x, Relation (mul zero x) zero
  | mul_zero : forall x, Relation (mul x zero) zero

/--
Instance `colimitSetoid` / 实例 `colimitSetoid`

English:
instance colimitSetoid
  signature: : Setoid (Prequotient F) where
  body: Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

中文:
实例 colimitSetoid
  签名: : 集合等价关系 (Prequotient F) where
  定义体: Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

Depends on / 依赖: Relation
-/
instance colimitSetoid : Setoid (Prequotient F) where
  r := Relation F
  iseqv := ⟨Relation.refl, Relation.symm _ _, Relation.trans _ _ _⟩

/--
Definition of `ColimitType` / `ColimitType` 的定义

English:
definition ColimitType
  signature: : Type v
  body: Quotient (colimitSetoid F)

中文:
定义 ColimitType
  签名: : 类型v
  定义体: Quotient (colimitSetoid F)

Depends on / 依赖: Quotient, colimitSetoid
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)

/--
Instance `ColimitType.instZero` / 实例 `ColimitType.instZero`

English:
instance ColimitType.instZero
  signature: : Zero (ColimitType F) where zero
  body: Quotient.mk _ zero

中文:
实例 ColimitType.instZero
  签名: : 零 (ColimitType F) where zero
  定义体: Quotient.mk _ zero
-/
instance ColimitType.instZero : Zero (ColimitType F) where zero := Quotient.mk _ zero

/--
Instance `ColimitType.instAdd` / 实例 `ColimitType.instAdd`

English:
instance ColimitType.instAdd
  signature: : Add (ColimitType F) where
  body: Quotient.map₂ add fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

中文:
实例 ColimitType.instAdd
  签名: : 加法 (ColimitType F) where
  定义体: Quotient.map₂ add fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)
-/
instance ColimitType.instAdd : Add (ColimitType F) where
add := Quotient.map₂ add fun _x x' rx y _y' ry =>
    Setoid.trans (Relation.add_1 _ _ y rx) (Relation.add_2 x' _ _ ry)

/--
Instance `ColimitType.instNeg` / 实例 `ColimitType.instNeg`

English:
instance ColimitType.instNeg
  signature: : Neg (ColimitType F) where
  body: Quotient.map neg Relation.neg_1

中文:
实例 ColimitType.instNeg
  签名: : 取负 (ColimitType F) where
  定义体: Quotient.map neg Relation.neg_1
-/
instance ColimitType.instNeg : Neg (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1

/--
Instance `ColimitType.AddGroup` / 实例 `ColimitType.AddGroup`

English:
instance ColimitType.AddGroup
  signature: : AddGroup (ColimitType F) where
  body: Quotient.map neg Relation.neg_1
zero_add := Quotient.ind fun _ => Quotient.sound Relation.zero_add _
add_zero := Quotient.ind fun _ => Quotient.sound Relation.add_zero _
neg_add_cancel := Quotient.ind fun _ => Quotient.sound Relation.neg_add_cancel _
add_assoc := Quotient.ind fun _ => Quotient.ind₂ 

中文:
实例 ColimitType.加法群
  签名: : 加法群 (ColimitType F) where
  定义体: Quotient.map neg Relation.neg_1
zero_add := Quotient.ind fun _ => Quotient.sound Relation.zero_add _
add_zero := Quotient.ind fun _ => Quotient.sound Relation.add_zero _
neg_add_cancel := Quotient.ind fun _ => Quotient.sound Relation.neg_add_cancel _
add_assoc := Quotient.ind fun _ => Quotient.ind₂ 
-/
instance ColimitType.AddGroup : AddGroup (ColimitType F) where
  neg := Quotient.map neg Relation.neg_1
zero_add := Quotient.ind fun _ => Quotient.sound Relation.zero_add _
add_zero := Quotient.ind fun _ => Quotient.sound Relation.add_zero _
neg_add_cancel := Quotient.ind fun _ => Quotient.sound Relation.neg_add_cancel _
add_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
Quotient.sound Relation.add_assoc _ _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

/--
Instance `InhabitedColimitType` / 实例 `InhabitedColimitType`

English:
instance InhabitedColimitType
  signature: : Inhabited ColimitType F where
  body: 0

中文:
实例 InhabitedColimitType
  签名: : 可居 ColimitType F where
  定义体: 0
-/
instance InhabitedColimitType : Inhabited ColimitType F where
  default := 0

/--
Instance `ColimitType.AddGroupWithOne` / 实例 `ColimitType.AddGroupWithOne`

English:
instance ColimitType.AddGroupWithOne
  signature: : AddGroupWithOne (ColimitType F)
  body: { ColimitType.AddGroup F with one := Quotient.mk _ one }

中文:
实例 ColimitType.加法带幺群
  签名: : 加法带幺群 (ColimitType F)
  定义体: { ColimitType.AddGroup F with one := Quotient.mk _ one }
-/
instance ColimitType.AddGroupWithOne : AddGroupWithOne (ColimitType F) :=
  { ColimitType.AddGroup F with one := Quotient.mk _ one }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (ColimitType.{v} F)
  body: { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.one_mul _
mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_one _
add_comm := fun x y => Quot.induction_on

中文:
实例 :
  签名: 交换环 (ColimitType.{v} F)
  定义体: { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.one_mul _
mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_one _
add_comm := fun x y => Quot.induction_on

Depends on / 依赖: AddGroupWithOne, ColimitType, ColimitType.AddGroupWithOne, Prequotient, Prequotient.mul, Quot.inductionOn, Quot.induction_on, Quot.map, Quot.sound, Relation, Relation.add_comm, Relation.mul_1, Relation.mul_2, Relation.mul_comm, Relation.mul_one, Relation.one_mul, add_comm, inductionOn, mul_1, mul_2
-/
instance : CommRing (ColimitType.{v} F) :=
  { ColimitType.AddGroupWithOne F with
    mul := Quot.map₂ Prequotient.mul Relation.mul_2 Relation.mul_1
one_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.one_mul _
mul_one := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_one _
add_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound Relation.add_comm _ _
mul_comm := fun x y => Quot.induction_on₂ x y fun _ _ => Quot.sound Relation.mul_comm _ _
    mul_assoc := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· * ·)]
      exact Quot.sound (Relation.mul_assoc _ _ _)
mul_zero := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.mul_zero _
zero_mul := fun x => Quot.inductionOn x fun _ => Quot.sound Relation.zero_mul _
    left_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.left_distrib _ _ _)
    right_distrib := fun x y z => Quot.induction_on₃ x y z fun x y z => by
      simp only [(· + ·), (· * ·), Add.add]
      exact Quot.sound (Relation.right_distrib _ _ _) }

@[simp]
/--
theorem `quot_zero` / 定理 `quot_zero`

English:
theorem quot_zero
  statement: Quot.mk Setoid.r zero = (0 : ColimitType F)
  proof: rfl

@[simp]

中文:
定理 quot_zero
  结论: 商.mk 集合等价关系.r zero = (0 : ColimitType F)
  证明: rfl

@[simp]
-/
theorem quot_zero : Quot.mk Setoid.r zero = (0 : ColimitType F) :=
  rfl

@[simp]
/--
theorem `quot_one` / 定理 `quot_one`

English:
theorem quot_one
  statement: Quot.mk Setoid.r one = (1 : ColimitType F)
  proof: rfl

@[simp]

中文:
定理 quot_one
  结论: 商.mk 集合等价关系.r one = (1 : ColimitType F)
  证明: rfl

@[simp]
-/
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
/--
theorem `quot_neg` / 定理 `quot_neg`

English:
theorem quot_neg
  given: (x : Prequotient F)
  proof: rfl

中文:
定理 quot_neg
  条件: (x : Prequotient F)
  证明: rfl
-/
theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show ColimitType F from Quot.mk Setoid.r x) :=
  rfl

-- Porting note: Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- unless we use `by exact` to change the elaboration order.
@[simp]
/--
theorem `quot_add` / 定理 `quot_add`

English:
theorem quot_add
  given: (x y)
  proof: rfl

中文:
定理 quot_add
  条件: (x y)
  证明: rfl
-/
theorem quot_add (x y) :
    Quot.mk Setoid.r (add x y) =
      (show ColimitType F from Quot.mk _ x) + (show ColimitType F from Quot.mk _ y) :=
  rfl

-- Porting note: Lean can't see `Quot.mk Setoid.r x` is a `ColimitType F` even with type annotation
-- unless we use `by exact` to change the elaboration order.
@[simp]
/--
theorem `quot_mul` / 定理 `quot_mul`

English:
theorem quot_mul
  given: (x y)
  proof: rfl

中文:
定理 quot_mul
  条件: (x y)
  证明: rfl
-/
theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show ColimitType F from Quot.mk _ x) * (show ColimitType F from Quot.mk _ y) :=
  rfl

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : CommRingCat
  body: CommRingCat.of (ColimitType F)

中文:
定义 colimit
  签名: : 交换环范畴
  定义体: CommRingCat.of (ColimitType F)

Depends on / 依赖: ColimitType, CommRingCat, CommRingCat.of
-/
def colimit : CommRingCat :=
  CommRingCat.of (ColimitType F)

/--
Definition of `coconeFun` / `coconeFun` 的定义

English:
definition coconeFun
  signature: (j : J) (x : F.obj j)
  body: Quot.mk _ (Prequotient.of j x)

中文:
定义 coconeFun
  签名: (j : J) (x : F.obj j)
  定义体: Quot.mk _ (Prequotient.of j x)

Depends on / 依赖: Prequotient, Prequotient.of, Quot.mk
-/
def coconeFun (j : J) (x : F.obj j) : ColimitType F :=
  Quot.mk _ (Prequotient.of j x)

/--
Definition of `coconeMorphism` / `coconeMorphism` 的定义

English:
definition coconeMorphism
  signature: (j : J)
  body: ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]

中文:
定义 coconeMorphism
  签名: (j : J)
  定义体: ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F := ofHom
  { toFun := coconeFun F j
    map_one' := by apply Quot.sound; apply Relation.one
    map_mul' := by intros; apply Quot.sound; apply Relation.mul
    map_zero' := by apply Quot.sound; apply Relation.zero
    map_add' := by intros; apply Quot.sound; apply Relation.add }

@[simp]
/--
theorem `cocone_naturality` / 定理 `cocone_naturality`

English:
theorem cocone_naturality
  given: {j j' : J} (f : j ⟶ j')
  proof: by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]

中文:
定理 cocone_naturality
  条件: {j j' : J} (f : j ⟶ j')
  证明: by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]

Depends on / 依赖: Quot.sound, Relation, Relation.map
-/
theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ coconeMorphism F j' = coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

@[simp]
/--
theorem `cocone_naturality_components` / 定理 `cocone_naturality_components`

English:
theorem cocone_naturality_components
  given: (j j' : J) (f : j ⟶ j') (x : F.obj j)
  proof: by
  rw [← cocone_naturality F f]; rw [comp_apply]

中文:
定理 cocone_naturality_components
  条件: (j j' : J) (f : j ⟶ j') (x : F.obj j)
  证明: by
  rw [← cocone_naturality F f]; rw [comp_apply]

Depends on / 依赖: cocone_naturality, comp_apply
-/
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]; rw [comp_apply]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F where
  body: colimit F
  ι := { app := coconeMorphism F }

中文:
定义 colimitCocone
  签名: : 余锥 F where
  定义体: colimit F
  ι := { app := coconeMorphism F }

Depends on / 依赖: colimit
-/
def colimitCocone : Cocone F where
  pt := colimit F
  ι := { app := coconeMorphism F }

/-- The function from the free commutative ring on the diagram to the cone point of any other
cocone. -/
@[simp]
/--
Definition of `descFunLift` / `descFunLift` 的定义

English:
definition descFunLift
  signature: (s : Cocone F)

中文:
定义 descFunLift
  签名: (s : 余锥 F)
-/
def descFunLift (s : Cocone F) : Prequotient F -> s.pt
  | Prequotient.of j x => (s.ι.app j) x
  | zero => 0
  | one => 1
  | neg x => -descFunLift s x
  | add x y => descFunLift s x + descFunLift s y
  | mul x y => descFunLift s x * descFunLift s y

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `descFun` / `descFun` 的定义

English:
definition descFun
  signature: (s : Cocone F)
  body: by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
    | zero j => simp

中文:
定义 descFun
  签名: (s : 余锥 F)
  定义体: by
  fapply Quot.lift
  · exact descFunLift F s
  · intro x y r
    induction r with
    | refl => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    | map j j' f x => exact RingHom.congr_fun (congrArg Hom.hom <| s.ι.naturality f) x
    | zero j => simp

Depends on / 依赖: Hom.hom, Quot.lift, RingHom, RingHom.congr_fun, add_1, add_2, congr_fun, descFunLift, fapply, ih.symm, ih1.trans, instances, naturality, neg_1
-/
def descFun (s : Cocone F) : ColimitType F -> s.pt := by
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

/--
Definition of `descMorphism` / `descMorphism` 的定义

English:
definition descMorphism
  signature: (s : Cocone F)
  body: ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y => by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y => by exact Quot.induction_on₂ x y fun a b => rfl }

中文:
定义 descMorphism
  签名: (s : 余锥 F)
  定义体: ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y => by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y => by exact Quot.induction_on₂ x y fun a b => rfl }
-/
def descMorphism (s : Cocone F) : colimit F ⟶ s.pt := ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_zero' := rfl
    map_add' := fun x y => by
      refine Quot.induction_on₂ x y fun a b => ?_
      dsimp [descFun]
      rw [← quot_add]
      rfl
    map_mul' := fun x y => by exact Quot.induction_on₂ x y fun a b => rfl }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitIsColimit` / `colimitIsColimit` 的定义

English:
definition colimitIsColimit
  signature: : IsColimit (colimitCocone F) where
  body: fun s => descMorphism F s
uniq := fun s m w => hom_ext RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j -

中文:
定义 colimitIsColimit
  签名: : 是余极限 (colimitCocone F) where
  定义体: fun s => descMorphism F s
uniq := fun s m w => hom_ext RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j -

Depends on / 依赖: descMorphism
-/
def colimitIsColimit : IsColimit (colimitCocone F) where
  desc := fun s => descMorphism F s
uniq := fun s m w => hom_ext RingHom.ext fun x => by
    refine Quot.inductionOn x ?_
    intro x
    induction x with
    | zero => simp
    | one => simp
    | neg x ih => simp [ih]
    | of j x =>
      exact congr_fun (congr_arg (fun f : F.obj j ⟶ s.pt => (f : F.obj j -> s.pt)) (w j)) x
    | add x y ih_x ih_y => simp [ih_x, ih_y]
    | mul x y ih_x ih_y => simp [ih_x, ih_y]

/--
Instance `hasColimits_commRingCat` / 实例 `hasColimits_commRingCat`

English:
instance hasColimits_commRingCat
  signature: : HasColimits CommRingCat where
  body: { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

中文:
实例 hasColimits_commRingCat
  签名: : 有余极限 交换环范畴 where
  定义体: { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimitCocone, colimitIsColimit, has_colimit, isColimit
-/
instance hasColimits_commRingCat : HasColimits CommRingCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end CommRingCat.Colimits
