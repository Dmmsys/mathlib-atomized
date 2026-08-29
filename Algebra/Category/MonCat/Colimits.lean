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

/--
Inductive type `Prequotient` / 归纳类型 `Prequotient`

English:
inductive Prequotient
  constructors (3):
    - of: forall (j : J) (_ : F.obj j), Prequotient
    - one: Prequotient
    - mul: Prequotient -> Prequotient -> Prequotient

中文:
归纳类型 Prequotient
  构造子 (3 个):
    - of: 对任意 (j : J) (_ : F.obj j), Prequotient
    - one: Prequotient
    - mul: Prequotient -> Prequotient -> Prequotient
-/
inductive Prequotient
  -- There's always `of`
  | of : forall (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | one : Prequotient
  | mul : Prequotient -> Prequotient -> Prequotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Prequotient F)
  body: ⟨Prequotient.one⟩

中文:
实例 :
  签名: 可居 (Prequotient F)
  定义体: ⟨Prequotient.one⟩

Depends on / 依赖: Prequotient, Prequotient.one
-/
instance : Inhabited (Prequotient F) :=
  ⟨Prequotient.one⟩

open Prequotient

/--
Inductive type `Relation` / 归纳类型 `Relation`

English:
inductive Relation
  parameters: : Prequotient F -> Prequotient F -> Prop -- Make it an equivalence relation:
  constructors (11):
    - refl: forall x, Relation x x
    - symm: forall (x y) (_ : Relation x y), Relation y x
    - trans: forall (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z -- There's always a `map` relation
    - map: forall (j j' : J) (f : j ⟶ j') (x : F.obj j), Relation (Prequotient.of j' ((F.map f) x)) (Prequotient.of j x)
    - mul: forall (j) (x y : F.obj j), Relation (Prequotient.of j (x * y)) (mul (Prequotient.of j x) (Prequotient.of j y))
    - one: forall j, Relation (Prequotient.of j 1) one -- Then one relation per argument of each operation
    - mul_1: forall (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
    - mul_2: forall (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    - mul_assoc: forall x y z, Relation (mul (mul x y) z) (mul x (mul y z))
    - one_mul: forall x, Relation (mul one x) x
    - mul_one: forall x, Relation (mul x one) x

中文:
归纳类型 关系
  参数: : Prequotient F -> Prequotient F -> 命题 -- Make it an equivalence relation:
  构造子 (11 个):
    - refl: 对任意 x, 关系 x x
    - symm: 对任意 (x y) (_ : 关系 x y), 关系 y x
    - trans: 对任意 (x y z) (_ : 关系 x y) (_ : 关系 y z), 关系 x z -- There's always a `map` relation
    - map: 对任意 (j j' : J) (f : j ⟶ j') (x : F.obj j), 关系 (Prequotient.of j' ((F.map f) x)) (Prequotient.of j x)
    - mul: 对任意 (j) (x y : F.obj j), 关系 (Prequotient.of j (x * y)) (mul (Prequotient.of j x) (Prequotient.of j y))
    - one: 对任意 j, 关系 (Prequotient.of j 1) one -- Then one relation per argument of each operation
    - mul_1: 对任意 (x x' y) (_ : 关系 x x'), 关系 (mul x y) (mul x' y)
    - mul_2: 对任意 (x y y') (_ : 关系 y y'), 关系 (mul x y) (mul x y')
    - mul_assoc: 对任意 x y z, 关系 (mul (mul x y) z) (mul x (mul y z))
    - one_mul: 对任意 x, 关系 (mul one x) x
    - mul_one: 对任意 x, 关系 (mul x one) x
-/
inductive Relation : Prequotient F -> Prequotient F -> Prop -- Make it an equivalence relation:
  | refl : forall x, Relation x x
  | symm : forall (x y) (_ : Relation x y), Relation y x
  | trans : forall (x y z) (_ : Relation x y) (_ : Relation y z),
      Relation x z -- There's always a `map` relation
  | map :
    forall (j j' : J) (f : j ⟶ j') (x : F.obj j),
      -- Then one relation per operation, describing the interaction with `of`
      Relation (Prequotient.of j' ((F.map f) x)) (Prequotient.of j x)
  | mul : forall (j) (x y : F.obj j), Relation (Prequotient.of j (x * y))
      (mul (Prequotient.of j x) (Prequotient.of j y))
  | one : forall j, Relation (Prequotient.of j 1) one -- Then one relation per argument of each operation
  | mul_1 : forall (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : forall (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    -- And one relation per axiom
  | mul_assoc : forall x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | one_mul : forall x, Relation (mul one x) x
  | mul_one : forall x, Relation (mul x one) x

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
deriving Inhabited

中文:
定义 ColimitType
  签名: : 类型v
  定义体: Quotient (colimitSetoid F)
deriving Inhabited

Depends on / 依赖: Quotient, colimitSetoid
-/
def ColimitType : Type v :=
  Quotient (colimitSetoid F)
deriving Inhabited

/--
Instance `monoidColimitType` / 实例 `monoidColimitType`

English:
instance monoidColimitType
  signature: : Monoid (ColimitType F) where
  body: Quotient.mk _ one
  mul := Quotient.map₂ mul fun _ x' rx y _ ry =>
    Setoid.trans (Relation.mul_1 _ _ y rx) (Relation.mul_2 x' _ _ ry)
one_mul := Quotient.ind fun _ => Quotient.sound Relation.one_mul _
mul_one := Quotient.ind fun _ => Quotient.sound Relation.mul_one _
  mul_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
Quotient.sound Relation.mul_assoc _ _ _

@[simp]

中文:
实例 monoidColimitType
  签名: : 幺半群 (ColimitType F) where
  定义体: Quotient.mk _ one
  mul := Quotient.map₂ mul fun _ x' rx y _ ry =>
    Setoid.trans (Relation.mul_1 _ _ y rx) (Relation.mul_2 x' _ _ ry)
one_mul := Quotient.ind fun _ => Quotient.sound Relation.one_mul _
mul_one := Quotient.ind fun _ => Quotient.sound Relation.mul_one _
  mul_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
Quotient.sound Relation.mul_assoc _ _ _

@[simp]

Depends on / 依赖: Quotient, Quotient.mk
-/
instance monoidColimitType : Monoid (ColimitType F) where
  one := Quotient.mk _ one
  mul := Quotient.map₂ mul fun _ x' rx y _ ry =>
    Setoid.trans (Relation.mul_1 _ _ y rx) (Relation.mul_2 x' _ _ ry)
one_mul := Quotient.ind fun _ => Quotient.sound Relation.one_mul _
mul_one := Quotient.ind fun _ => Quotient.sound Relation.mul_one _
  mul_assoc := Quotient.ind fun _ => Quotient.ind₂ fun _ _ =>
Quotient.sound Relation.mul_assoc _ _ _

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

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalars, R.map, colimit, colimit.isColimit, evaluation, isColimit, isColimitOfPreserves, restrictScalars
-/
theorem quot_one : Quot.mk Setoid.r one = (1 : ColimitType F) :=
  rfl

@[simp]
/--
theorem `quot_mul` / 定理 `quot_mul`

English:
theorem quot_mul
  given: (x y : Prequotient F)
  statement: Quot.mk Setoid.r (mul x y) =
  proof: rfl

中文:
定理 quot_mul
  条件: (x y : Prequotient F)
  结论: 商.mk 集合等价关系.r (mul x y) =
  证明: rfl
-/
theorem quot_mul (x y : Prequotient F) : Quot.mk Setoid.r (mul x y) =
    @HMul.hMul (ColimitType F) (ColimitType F) (ColimitType F) _
      (Quot.mk Setoid.r x) (Quot.mk Setoid.r y) :=
  rfl

/--
Definition of `colimit` / `colimit` 的定义

English:
definition colimit
  signature: : MonCat
  body: of (ColimitType F)

中文:
定义 colimit
  签名: : 幺半群范畴
  定义体: of (ColimitType F)

Depends on / 依赖: ColimitType
-/
def colimit : MonCat :=
  of (ColimitType F)

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
    map_one' := Quot.sound (Relation.one _)
    map_mul' _ _ := Quot.sound (Relation.mul _ _ _) }

@[simp]

中文:
定义 coconeMorphism
  签名: (j : J)
  定义体: ofHom
  { toFun := coconeFun F j
    map_one' := Quot.sound (Relation.one _)
    map_mul' _ _ := Quot.sound (Relation.mul _ _ _) }

@[simp]

Depends on / 依赖: Quot.sound, Relation, Relation.mul, Relation.one, coconeFun, map_mul, map_one
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
  { toFun := coconeFun F j
    map_one' := Quot.sound (Relation.one _)
    map_mul' _ _ := Quot.sound (Relation.mul _ _ _) }

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
  rw [← cocone_naturality F f]
  rfl

中文:
定理 cocone_naturality_components
  条件: (j j' : J) (f : j ⟶ j') (x : F.obj j)
  证明: by
  rw [← cocone_naturality F f]
  rfl

Depends on / 依赖: cocone_naturality
-/
theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (coconeMorphism F j') (F.map f x) = (coconeMorphism F j) x := by
  rw [← cocone_naturality F f]
  rfl

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

/-- The function from the free monoid on the diagram to the cone point of any other cocone. -/
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
  | one => 1
  | mul x y => descFunLift _ x * descFunLift _ y

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

中文:
定义 descFun
  签名: (s : 余锥 F)
  定义体: by
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

Depends on / 依赖: Quot.lift, congr_arg, descFunLift, fapply, h.symm, map_mul, map_one, mul_1, mul_2, mul_assoc, mul_one, one_mul, s.w_apply, w_apply
-/
def descFun (s : Cocone F) : ColimitType F -> s.pt := by
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

/--
Definition of `descMorphism` / `descMorphism` 的定义

English:
definition descMorphism
  signature: (s : Cocone F)
  body: ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_mul' x y := by
      induction x using Quot.inductionOn
      induction y using Quot.inductionOn
      solve_by_elim }

中文:
定义 descMorphism
  签名: (s : 余锥 F)
  定义体: ofHom
  { toFun := descFun F s
    map_one' := rfl
    map_mul' x y := by
      induction x using Quot.inductionOn
      induction y using Quot.inductionOn
      solve_by_elim }

Depends on / 依赖: Quot.inductionOn, descFun, inductionOn, map_mul, map_one, solve_by_elim
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
/--
Definition of `colimitIsColimit` / `colimitIsColimit` 的定义

English:
definition colimitIsColimit
  signature: : IsColimit (colimitCocone F) where
  body: descMorphism F s
  uniq s m w := by
    ext x
    induction x using Quot.inductionOn with | h x => ?_
    induction x with
    | of j =>
      change _ = s.ι.app j _
      rw [← w j]
      rfl
    | one =>
      rw [quot_one]; rw [map_one]
      rfl
    | mul x y hx hy =>
      rw [quot_mul]; rw [map_mul]; rw [hx]; rw [hy]
      solve_by_elim

中文:
定义 colimitIsColimit
  签名: : 是余极限 (colimitCocone F) where
  定义体: descMorphism F s
  uniq s m w := by
    ext x
    induction x using Quot.inductionOn with | h x => ?_
    induction x with
    | of j =>
      change _ = s.ι.app j _
      rw [← w j]
      rfl
    | one =>
      rw [quot_one]; rw [map_one]
      rfl
    | mul x y hx hy =>
      rw [quot_mul]; rw [map_mul]; rw [hx]; rw [hy]
      solve_by_elim

Depends on / 依赖: descMorphism
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
      rw [quot_one]; rw [map_one]
      rfl
    | mul x y hx hy =>
      rw [quot_mul]; rw [map_mul]; rw [hx]; rw [hy]
      solve_by_elim

/--
Instance `hasColimits_monCat` / 实例 `hasColimits_monCat`

English:
instance hasColimits_monCat
  signature: : HasColimits MonCat where
  body: { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

中文:
实例 hasColimits_monCat
  签名: : 有余极限 幺半群范畴 where
  定义体: { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, colimitCocone, colimitIsColimit, has_colimit, isColimit
-/
instance hasColimits_monCat : HasColimits MonCat where
  has_colimits_of_shape _ _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone F
            isColimit := colimitIsColimit F } }

end MonCat.Colimits
