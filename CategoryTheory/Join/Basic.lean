/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Joins of categories

Given categories `C, D`, this file constructs a category `C ⋆ D`. Its objects are either
objects of `C` or objects of `D`, morphisms between objects of `C` are morphisms in `C`,
morphisms between objects of `D` are morphisms in `D`, and finally, given `c : C` and `d : D`,
there is a unique morphism `c ⟶ d` in `C ⋆ D`.

## Main constructions

* `Join.edge c d`: the unique map from `c` to `d`.
* `Join.inclLeft : C ⥤ C ⋆ D`, the left inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `C`.
* `Join.inclRight : D ⥤ C ⋆ D`, the right inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `D`.
* `Join.mkFunctor`, A constructor for functors out of a join of categories.
* `Join.mkNatTrans`, A constructor for natural transformations between functors out of a join
  of categories.
* `Join.mkNatIso`, A constructor for natural isomorphisms between functors out of a join
  of categories.

## References

* [Kerodon: section 1.4.3.2](https://kerodon.net/tag/0160)

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open CategoryTheory.Functor

/-- Elements of `Join C D` are either elements of `C` or elements of `D`. -/
-- Impl. : We are not defining it as a type alias for `C ⊕ D` so that we can have
-- aesop to call cases on `Join C D`
/-
**CategoryTheory.Join** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：Join (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Typ
e (max u₁ u₂) | left : C -> Join C D | right : D -> Join C D  attribute [aesop s
afe cases (rule_sets
参数：C : Type u₁；D : Type u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
inductive Join (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type (max u₁ u₂)
  | left : C → Join C D
  | right : D → Join C D

attribute [aesop safe cases (rule_sets := [CategoryTheory])] Join

namespace Join

@[inherit_doc] scoped infixr:30 " ⋆ " => Join

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

section CategoryStructure

variable {C D}

/-- Morphisms in `C ⋆ D` are those of `C` and `D`, plus a unique
morphism `(left c ⟶ right d)` for every `c : C` and `d : D`. -/
/-
**CategoryTheory.Join.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.Join C D → CategoryTheory.Join C D → Type (max v₁ v₂)
参数：max v₁ v₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in `C ⋆ D` are those of `C` and `D`, plus a unique
morphism `(left c ⟶ right d)` for every `c : C` and `d : D`.
-/
def Hom : C ⋆ D → C ⋆ D → Type (max v₁ v₂)
  | .left x, .left y => ULift (x ⟶ y)
  | .right x, .right y => ULift (x ⟶ y)
  | .left _, .right _ => PUnit
  | .right _, .left _ => PEmpty

/-- Identity morphisms in `C ⋆ D` are inherited from those in `C` and `D`. -/
/-
**CategoryTheory.Join.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → (X : CategoryTheory.Jo
in C D) → X.Hom X
参数：X : CategoryTheory.Join C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity morphisms in `C ⋆ D` are inherited from those in `C` and `D`.
-/
def id : ∀ X : C ⋆ D, Hom X X
  | .left x => ULift.up (𝟙 x)
  | .right x => ULift.up (𝟙 x)

/-- Composition in `C ⋆ D` is inherited from the compositions in `C` and `D`. -/
/-
**CategoryTheory.Join.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → {x y z : Categor
yTheory.Join C D} → x.Hom y → y.Hom z → x.Hom z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition in `C ⋆ D` is inherited from the compositions in `C` and `D`.
-/
def comp : ∀ {x y z : C ⋆ D}, Hom x y → Hom y z → Hom x z
  | .left _x, .left _y, .left _z, f, g => ULift.up (ULift.down f ≫ ULift.down g)
  | .left _x, .left _y, .right _z, _, _ => PUnit.unit
  | .left _x, .right _y, .right _z, _, _ => PUnit.unit
  | .right _x, .right _y, .right _z, f, g => ULift.up (ULift.down f ≫ ULift.down g)
/-
**CategoryTheory.Join.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Join`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category.{max v₁ v₂} (C ⋆ D) where
  Hom X Y := Hom X Y
  id _ := id _
  comp := comp
  assoc {a b c d} f g h := by
    cases a <;>
    cases b <;>
    cases c <;>
    cases d <;>
    simp only [Hom, comp, Category.assoc] <;>
    tauto
  id_comp {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.id_comp] <;> tauto
  comp_id {x y} f := by
    cases x <;> cases y <;> simp only [Hom, id, comp, Category.comp_id] <;> tauto

@[aesop safe destruct (rule_sets := [CategoryTheory])]
/-
**CategoryTheory.Join.false_of_right_to_left** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Join`。
形式化陈述：false_of_right_to_left {X : D} {Y : C} (f : right X ⟶ left Y) : False
参数：f : right X ⟶ left Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma false_of_right_to_left {X : D} {Y : C} (f : right X ⟶ left Y) : False := (f : PEmpty).elim
/-
**CategoryTheory.Join.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Join`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} {Y : D} : Unique (left X ⟶ right Y) := inferInstanceAs (Unique PUnit)

/-- Join.edge c d is the unique morphism from c to d. -/
/-
**CategoryTheory.Join.edge** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：edge (c : C) (d : D) : left c ⟶ right d
参数：c : C；d : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Join.edge c d is the unique morphism from c to d.
-/
def edge (c : C) (d : D) : left c ⟶ right d := default

end CategoryStructure

section Inclusions

/-- The canonical inclusion from C to `C ⋆ D`.
Terms of the form `(inclLeft C D).map f` should be treated as primitive when working with joins
and one should avoid trying to reduce them. For this reason, there is no `inclLeft_map` simp
lemma. -/
@[simps! obj]
/-
**CategoryTheory.Join.inclLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：inclLeft : C ⥤ C ⋆ D where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from C to `C ⋆ D`.
Terms of the form `(inclLeft C D).map f` should be treated as primitive when wor
king with joins
and one should avoid trying to reduce them. For this reason, there is no `inclLe
ft_map` simp
lemma.
-/
def inclLeft : C ⥤ C ⋆ D where
  obj := left
  map := ULift.up

/-- The canonical inclusion from D to `C ⋆ D`.
Terms of the form `(inclRight C D).map f` should be treated as primitive when working with joins
and one should avoid trying to reduce them. For this reason, there is no `inclRight_map` simp
lemma. -/
@[simps! obj]
/-
**CategoryTheory.Join.inclRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：inclRight : D ⥤ C ⋆ D where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from D to `C ⋆ D`.
Terms of the form `(inclRight C D).map f` should be treated as primitive when wo
rking with joins
and one should avoid trying to reduce them. For this reason, there is no `inclRi
ght_map` simp
lemma.
-/
def inclRight : D ⥤ C ⋆ D where
  obj := right
  map := ULift.up

variable {C D}

/-- An induction principle for morphisms in a join of categories: a morphism is either of the form
`(inclLeft _ _).map _`, `(inclRight _ _).map _`, or is `edge _ _`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**CategoryTheory.Join.homInduction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Joi
n`。
形式化陈述：homInduction {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*} (left : forall x y : 
C, (f : x ⟶ y) -> P ((inclLeft C D).map f)) (right : forall x y : D, (f : x ⟶ y)
 -> P ((inclRight C D).map f)) (edge : forall (c : C) (d : D), P (edge c d)) {x 
y : C ⋆ D} (f : x ⟶ y) : P f
参数：x ⟶ y；left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f)；right : 
forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f)；edge : forall (c : C) (
d : D), P (edge c d)；f : x ⟶ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An induction principle for morphisms in a join of categories: a morphism is eith
er of the form
`(inclLeft _ _).map _`, `(inclRight _ _).map _`, or is `edge _ _`.
-/
def homInduction {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {x y : C ⋆ D} (f : x ⟶ y) : P f :=
  match x, y, f with
  | .left x, .left y, .up f => left x y f
  | .right x, .right y, .up f => right x y f
  | .left x, .right y, _ => edge x y

@[simp]
/-
**CategoryTheory.Join.homInduction_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Join`。
形式化陈述：homInduction_left {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*} (left : forall x
 y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f)) (right : forall x y : D, (f : x
 ⟶ y) -> P ((inclRight C D).map f)) (edge : forall (c : C) (d : D), P (edge c d)
) {x y : C} (f : x ⟶ y) : homInduction left right edge ((inclLeft C D).map f) = 
left x y f
参数：x ⟶ y；left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f)；right : 
forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f)；edge : forall (c : C) (
d : D), P (edge c d)；f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homInduction_left {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {x y : C} (f : x ⟶ y) : homInduction left right edge ((inclLeft C D).map f) = left x y f :=
  rfl

@[simp]
/-
**CategoryTheory.Join.homInduction_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Join`。
形式化陈述：homInduction_right {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*} (left : forall 
x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f)) (right : forall x y : D, (f : 
x ⟶ y) -> P ((inclRight C D).map f)) (edge : forall (c : C) (d : D), P (edge c d
)) {x y : D} (f : x ⟶ y) : homInduction left right edge ((inclRight C D).map f) 
= right x y f
参数：x ⟶ y；left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f)；right : 
forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f)；edge : forall (c : C) (
d : D), P (edge c d)；f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homInduction_right {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {x y : D} (f : x ⟶ y) : homInduction left right edge ((inclRight C D).map f) = right x y f :=
  rfl

@[simp]
/-
**CategoryTheory.Join.homInduction_edge** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Join`。
形式化陈述：homInduction_edge {P : {x y : C ⋆ D} -> (x ⟶ y) -> Sort*} (left : forall x
 y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f)) (right : forall x y : D, (f : x
 ⟶ y) -> P ((inclRight C D).map f)) (edge : forall (c : C) (d : D), P (edge c d)
) {c : C} {d : D} : homInduction left right edge (Join.edge c d) = edge c d
参数：x ⟶ y；left : forall x y : C, (f : x ⟶ y) -> P ((inclLeft C D).map f)；right : 
forall x y : D, (f : x ⟶ y) -> P ((inclRight C D).map f)；edge : forall (c : C) (
d : D), P (edge c d)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homInduction_edge {P : {x y : C ⋆ D} → (x ⟶ y) → Sort*}
    (left : ∀ x y : C, (f : x ⟶ y) → P ((inclLeft C D).map f))
    (right : ∀ x y : D, (f : x ⟶ y) → P ((inclRight C D).map f))
    (edge : ∀ (c : C) (d : D), P (edge c d))
    {c : C} {d : D} : homInduction left right edge (Join.edge c d) = edge c d :=
  rfl

variable (C D)

/-- The left inclusion is fully faithful. -/
/-
**CategoryTheory.Join.inclLeftFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Join`。
形式化陈述：inclLeftFullyFaithful : (inclLeft C D).FullyFaithful where preimage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inclusion is fully faithful.
-/
def inclLeftFullyFaithful : (inclLeft C D).FullyFaithful where
  preimage f := f.down

/-- The right inclusion is fully faithful. -/
/-
**CategoryTheory.Join.inclRightFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Join`。
形式化陈述：inclRightFullyFaithful : (inclRight C D).FullyFaithful where preimage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inclusion is fully faithful.
-/
def inclRightFullyFaithful : (inclRight C D).FullyFaithful where
  preimage f := f.down
/-
**CategoryTheory.Join.inclLeftFull** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Joi
n`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D],   (CategoryTheory.Join.inclLeft C
 D).Full
参数：C : Type u₁；D : Type u₂；CategoryTheory.Join.inclLeft C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance inclLeftFull : (inclLeft C D).Full := inclLeftFullyFaithful C D |>.full
/-
**CategoryTheory.Join.inclRightFull** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Jo
in`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D],   (CategoryTheory.Join.inclRight 
C D).Full
参数：C : Type u₁；D : Type u₂；CategoryTheory.Join.inclRight C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance inclRightFull : (inclRight C D).Full := inclRightFullyFaithful C D |>.full
/-
**CategoryTheory.Join.inclLeftFaithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Join`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D],   (CategoryTheory.Join.inclLeft C
 D).Faithful
参数：C : Type u₁；D : Type u₂；CategoryTheory.Join.inclLeft C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance inclLeftFaithful : (inclLeft C D).Faithful := inclLeftFullyFaithful C D |>.faithful
/-
**CategoryTheory.Join.inclRightFaithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Join`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D],   (CategoryTheory.Join.inclRight 
C D).Faithful
参数：C : Type u₁；D : Type u₂；CategoryTheory.Join.inclRight C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance inclRightFaithful : (inclRight C D).Faithful := inclRightFullyFaithful C D |>.faithful

variable {C} in
/-- A situational lemma to help putting identities in the form `(inclLeft _ _).map _` when using
`homInduction`. -/
/-
**CategoryTheory.Join.id_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Join`。
形式化陈述：id_left (c : C) : 𝟙 (left c) = (inclLeft C D).map (𝟙 c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A situational lemma to help putting identities in the form `(inclLeft _ _).map _
` when using
`homInduction`.
-/
lemma id_left (c : C) : 𝟙 (left c) = (inclLeft C D).map (𝟙 c) := rfl

variable {D} in
/-- A situational lemma to help putting identities in the form `(inclRight _ _).map _` when using
`homInduction`. -/
/-
**CategoryTheory.Join.id_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Join`。
形式化陈述：id_right (d : D) : 𝟙 (right d) = (inclRight C D).map (𝟙 d)
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A situational lemma to help putting identities in the form `(inclRight _ _).map 
_` when using
`homInduction`.
-/
lemma id_right (d : D) : 𝟙 (right d) = (inclRight C D).map (𝟙 d) := rfl

/-- The "canonical" natural transformation from `(Prod.fst C D) ⋙ inclLeft C D` to
`(Prod.snd C D) ⋙ inclRight C D`. This is bundling together all the edge morphisms
into the data of a natural transformation. -/
@[simps!]
/-
**CategoryTheory.Join.edgeTransform** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Jo
in`。
形式化陈述：edgeTransform : Prod.fst C D ⋙ inclLeft C D ⟶ Prod.snd C D ⋙ inclRight C D
 where app
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "canonical" natural transformation from `(Prod.fst C D) ⋙ inclLeft C D` to
`(Prod.snd C D) ⋙ inclRight C D`. This is bundling together all the edge morphis
ms
into the data of a natural transformation.
-/
def edgeTransform :
    Prod.fst C D ⋙ inclLeft C D ⟶ Prod.snd C D ⋙ inclRight C D where
  app := fun (c, d) ↦ edge c d

end Inclusions

section Functoriality

variable {C D} {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A pair of functors `F : C ⥤ E, G : D ⥤ E` as well as a natural transformation
`α : (Prod.fst C D) ⋙ F ⟶ (Prod.snd C D) ⋙ G` defines a functor out of `C ⋆ D`.
This is the main entry point to define functors out of a join of categories. -/
/-
**CategoryTheory.Join.mkFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：mkFunctor (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G
) : C ⋆ D ⥤ E where obj X
参数：F : C ⥤ E；G : D ⥤ E；α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of functors `F : C ⥤ E, G : D ⥤ E` as well as a natural transformation
`α : (Prod.fst C D) ⋙ F ⟶ (Prod.snd C D) ⋙ G` defines a functor out of `C ⋆ D`.
This is the main entry point to define functors out of a join of categories.
-/
def mkFunctor (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G) :
    C ⋆ D ⥤ E where
  obj X :=
    match X with
    | .left x => F.obj x
    | .right x => G.obj x
  map f :=
    homInduction
      (left := fun _ _ f ↦ F.map f)
      (right := fun _ _ g ↦ G.map g)
      (edge := fun c d ↦ α.app (c, d))
      f
  map_id x := by
    cases x
    · dsimp only [id_left, homInduction_left]
      simp
    · dsimp only [id_right, homInduction_right]
      simp
  map_comp {x y z} f g := by
    cases f <;> cases g
    · simp [← Functor.map_comp]
    · case left.edge f d => simpa using! (α.naturality <| (Prod.sectL _ d).map f).symm
    · simp [← Functor.map_comp]
    · case edge.right c _ _ f => simpa using! α.naturality <| (Prod.sectR c _).map f

section

variable (F : C ⥤ E) (G : D ⥤ E) (α : Prod.fst C D ⋙ F ⟶ Prod.snd C D ⋙ G)

-- As these equalities of objects are definitional, they should be fine.
@[simp]
/-
**CategoryTheory.Join.mkFunctor_obj_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Join`。
形式化陈述：mkFunctor_obj_left (c : C) : (mkFunctor F G α).obj (left c) = F.obj c
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkFunctor_obj_left (c : C) : (mkFunctor F G α).obj (left c) = F.obj c := rfl

@[simp]
/-
**CategoryTheory.Join.mkFunctor_obj_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Join`。
形式化陈述：mkFunctor_obj_right (d : D) : (mkFunctor F G α).obj (right d) = G.obj d
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkFunctor_obj_right (d : D) : (mkFunctor F G α).obj (right d) = G.obj d := rfl

@[simp]
/-
**CategoryTheory.Join.mkFunctor_map_inclLeft** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Join`。
形式化陈述：mkFunctor_map_inclLeft {c c' : C} (f : c ⟶ c') : (mkFunctor F G α).map ((i
nclLeft C D).map f) = F.map f
参数：f : c ⟶ c'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkFunctor_map_inclLeft {c c' : C} (f : c ⟶ c') :
    (mkFunctor F G α).map ((inclLeft C D).map f) = F.map f :=
  rfl

/-- Precomposing `mkFunctor F G α` with the left inclusion gives back `F`. -/
@[simps!]
/-
**CategoryTheory.Join.mkFunctorLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Jo
in`。
形式化陈述：mkFunctorLeft : inclLeft C D ⋙ mkFunctor F G α ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposing `mkFunctor F G α` with the left inclusion gives back `F`.
-/
def mkFunctorLeft : inclLeft C D ⋙ mkFunctor F G α ≅ F := Iso.refl _

/-- Precomposing `mkFunctor F G α` with the right inclusion gives back `G`. -/
@[simps!]
/-
**CategoryTheory.Join.mkFunctorRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.J
oin`。
形式化陈述：mkFunctorRight : inclRight C D ⋙ mkFunctor F G α ≅ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposing `mkFunctor F G α` with the right inclusion gives back `G`.
-/
def mkFunctorRight : inclRight C D ⋙ mkFunctor F G α ≅ G := Iso.refl _

@[simp]
/-
**CategoryTheory.Join.mkFunctor_map_inclRight** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Join`。
形式化陈述：mkFunctor_map_inclRight {d d' : D} (f : d ⟶ d') : (mkFunctor F G α).map ((
inclRight C D).map f) = G.map f
参数：f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkFunctor_map_inclRight {d d' : D} (f : d ⟶ d') :
    (mkFunctor F G α).map ((inclRight C D).map f) = G.map f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering `mkFunctor F G α` with the universal transformation gives back `α`. -/
@[simp]
/-
**CategoryTheory.Join.mkFunctor_edgeTransform** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Join`。
形式化陈述：mkFunctor_edgeTransform : whiskerRight (edgeTransform C D) (mkFunctor F G 
α) = α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Whiskering `mkFunctor F G α` with the universal transformation gives back `α`.
-/
lemma mkFunctor_edgeTransform :
    whiskerRight (edgeTransform C D) (mkFunctor F G α) = α := by
  ext x
  simp [mkFunctor]

@[simp]
/-
**CategoryTheory.Join.mkFunctor_map_edge** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Join`。
形式化陈述：mkFunctor_map_edge (c : C) (d : D) : (mkFunctor F G α).map (edge c d) = α.
app (c, d)
参数：c : C；d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkFunctor_map_edge (c : C) (d : D) :
    (mkFunctor F G α).map (edge c d) = α.app (c, d) :=
  rfl

end

/-- Construct a natural transformation between functors out of a join from
the data of natural transformations between each side that are compatible with the
action on edge maps. -/
/-
**CategoryTheory.Join.mkNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`
。
形式化陈述：mkNatTrans {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E} (αₗ : inclLeft C D ⋙ F ⟶ inclL
eft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F') (h : whiskerRight (e
dgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ = whiskerLeft (Prod.fst C D)
 αₗ ≫ whiskerRight (edgeTransform C D) F'
参数：αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F'；αᵣ : inclRight C D ⋙ F ⟶ inclRight 
C D ⋙ F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a natural transformation between functors out of a join from
the data of natural transformations between each side that are compatible with t
he
action on edge maps.
-/
def mkNatTrans {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' := by cat_disch) :
    F ⟶ F' where
  app x := match x with
    | left x => αₗ.app x
    | right x => αᵣ.app x
  naturality {x y} f := by
    cases f with
    | @left x y f => simpa using! αₗ.naturality f
    | @right x y f => simpa using! αᵣ.naturality f
    | @edge c d => exact funext_iff.mp (NatTrans.ext_iff.mp h) (c, d)

section

variable {F : C ⋆ D ⥤ E} {F' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' := by cat_disch)

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.Join.mkNatTrans_app_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Join`。
形式化陈述：mkNatTrans_app_left (c : C) : (mkNatTrans αₗ αᵣ h).app (left c) = αₗ.app c
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkNatTrans_app_left (c : C) : (mkNatTrans αₗ αᵣ h).app (left c) = αₗ.app c := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.Join.mkNatTrans_app_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Join`。
形式化陈述：mkNatTrans_app_right (d : D) : (mkNatTrans αₗ αᵣ h).app (right d) = αᵣ.app
 d
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkNatTrans_app_right (d : D) : (mkNatTrans αₗ αᵣ h).app (right d) = αᵣ.app d := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.Join.whiskerLeft_inclLeft_mkNatTrans** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Join`。
形式化陈述：whiskerLeft_inclLeft_mkNatTrans : whiskerLeft (inclLeft C D) (mkNatTrans α
ₗ αᵣ h) = αₗ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_inclLeft_mkNatTrans : whiskerLeft (inclLeft C D) (mkNatTrans αₗ αᵣ h) = αₗ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.Join.whiskerLeft_inclRight_mkNatTrans** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Join`。
形式化陈述：whiskerLeft_inclRight_mkNatTrans : whiskerLeft (inclRight C D) (mkNatTrans
 αₗ αᵣ h) = αᵣ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_inclRight_mkNatTrans :
    whiskerLeft (inclRight C D) (mkNatTrans αₗ αᵣ h) = αᵣ := rfl

end

/-- Two natural transformations between functors out of a join are equal if they are so
after whiskering with the inclusions. -/
/-
**CategoryTheory.Join.natTrans_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Joi
n`。
形式化陈述：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β : F ⟶ F'} (h₁ : whiskerLeft (inclLeft
 C D) α = whiskerLeft (inclLeft C D) β) (h₂ : whiskerLeft (inclRight C D) α = wh
iskerLeft (inclRight C D) β) : α = β
参数：h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β；h₂ : whisker
Left (inclRight C D) α = whiskerLeft (inclRight C D) β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Two natural transformations between functors out of a join are equal if they are
 so
after whiskering with the inclusions.
-/
lemma natTrans_ext {F F' : C ⋆ D ⥤ E} {α β : F ⟶ F'}
    (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β)
    (h₂ : whiskerLeft (inclRight C D) α = whiskerLeft (inclRight C D) β) :
    α = β := by
  ext t
  cases t with
  | left t => exact congrArg (fun x ↦ x.app t) h₁
  | right t => exact congrArg (fun x ↦ x.app t) h₂

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Join.eq_mkNatTrans** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Jo
in`。
形式化陈述：eq_mkNatTrans {F F' : C ⋆ D ⥤ E} (α : F ⟶ F') : mkNatTrans (whiskerLeft (i
nclLeft C D) α) (whiskerLeft (inclRight C D) α) = α
参数：α : F ⟶ F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_mkNatTrans {F F' : C ⋆ D ⥤ E} (α : F ⟶ F') :
    mkNatTrans (whiskerLeft (inclLeft C D) α) (whiskerLeft (inclRight C D) α) = α := by
  apply natTrans_ext <;> simp

section

/-- `mkNatTrans` respects vertical composition. -/
/-
**CategoryTheory.Join.mkNatTransComp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.J
oin`。
形式化陈述：mkNatTransComp {F F' F'' : C ⋆ D ⥤ E} (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C 
D ⋙ F') (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F') (βₗ : inclLeft C D ⋙ F' ⟶ 
inclLeft C D ⋙ F'') (βᵣ : inclRight C D ⋙ F' ⟶ inclRight C D ⋙ F'') (h : whisker
Right (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ = whiskerLeft (Prod.
fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F'
参数：αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F'；αᵣ : inclRight C D ⋙ F ⟶ inclRight 
C D ⋙ F'；βₗ : inclLeft C D ⋙ F' ⟶ inclLeft C D ⋙ F''；βᵣ : inclRight C D ⋙ F' ⟶ i
nclRight C D ⋙ F''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Join.natTrans_ext`：natTrans_ext {F F' : C ⋆ D ⥤ E} {α β :
 F ⟶ F'} (h₁ : whiskerLeft (inclLeft C D) α = whiskerLeft (inclLeft C D) β) (h₂ 
: whiskerLeft (inclRig…

--- 原说明 ---
`mkNatTrans` respects vertical composition.
-/
lemma mkNatTransComp
    {F F' F'' : C ⋆ D ⥤ E}
    (αₗ : inclLeft C D ⋙ F ⟶ inclLeft C D ⋙ F')
    (αᵣ : inclRight C D ⋙ F ⟶ inclRight C D ⋙ F')
    (βₗ : inclLeft C D ⋙ F' ⟶ inclLeft C D ⋙ F'')
    (βᵣ : inclRight C D ⋙ F' ⟶ inclRight C D ⋙ F'')
    (h : whiskerRight (edgeTransform C D) F ≫ whiskerLeft (Prod.snd C D) αᵣ =
      whiskerLeft (Prod.fst C D) αₗ ≫ whiskerRight (edgeTransform C D) F' := by cat_disch)
    (h' : whiskerRight (edgeTransform C D) F' ≫ whiskerLeft (Prod.snd C D) βᵣ =
      whiskerLeft (Prod.fst C D) βₗ ≫ whiskerRight (edgeTransform C D) F'' := by cat_disch) :
    mkNatTrans (αₗ ≫ βₗ) (αᵣ ≫ βᵣ) (by simp [← h', reassoc_of% h]) =
    mkNatTrans αₗ αᵣ h ≫ mkNatTrans βₗ βᵣ h' := by
  apply natTrans_ext <;> cat_disch

end

set_option backward.isDefEq.respectTransparency false in
/-- Two functors out of a join of categories are naturally isomorphic if their
compositions with the inclusions are isomorphic and the whiskering with the canonical
transformation is respected through these isomorphisms. -/
@[simps]
/-
**CategoryTheory.Join.mkNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：mkNatIso {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E} (eₗ : inclLeft C D ⋙ F ≅ inclLeft
 C D ⋙ G) (eᵣ : inclRight C D ⋙ F ≅ inclRight C D ⋙ G) (h : whiskerRight (edgeTr
ansform C D) F ≫ (isoWhiskerLeft (Prod.snd C D) eᵣ).hom = (isoWhiskerLeft (Prod.
fst C D) eₗ).hom ≫ whiskerRight (edgeTransform C D) G
参数：eₗ : inclLeft C D ⋙ F ≅ inclLeft C D ⋙ G；eᵣ : inclRight C D ⋙ F ≅ inclRight C
 D ⋙ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two functors out of a join of categories are naturally isomorphic if their
compositions with the inclusions are isomorphic and the whiskering with the cano
nical
transformation is respected through these isomorphisms.
-/
def mkNatIso {F : C ⋆ D ⥤ E} {G : C ⋆ D ⥤ E}
    (eₗ : inclLeft C D ⋙ F ≅ inclLeft C D ⋙ G)
    (eᵣ : inclRight C D ⋙ F ≅ inclRight C D ⋙ G)
    (h : whiskerRight (edgeTransform C D) F ≫ (isoWhiskerLeft (Prod.snd C D) eᵣ).hom =
      (isoWhiskerLeft (Prod.fst C D) eₗ).hom ≫ whiskerRight (edgeTransform C D) G := by cat_disch) :
    F ≅ G where
  hom := mkNatTrans eₗ.hom eᵣ.hom (by simpa using h)
  inv := mkNatTrans eₗ.inv eᵣ.inv (by rw [Eq.comm, ← isoWhiskerLeft_inv, ← isoWhiskerLeft_inv,
    Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, h])

/-- A pair of functors ((C ⥤ E), (D ⥤ E')) induces a functor `C ⋆ D ⥤ E ⋆ E'`. -/
/-
**CategoryTheory.Join.mapPair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：mapPair (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') : C ⋆ D ⥤ E ⋆ E'
参数：Fₗ : C ⥤ E；Fᵣ : D ⥤ E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of functors ((C ⥤ E), (D ⥤ E')) induces a functor `C ⋆ D ⥤ E ⋆ E'`.
-/
def mapPair (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') : C ⋆ D ⥤ E ⋆ E' :=
  mkFunctor (Fₗ ⋙ inclLeft _ _) (Fᵣ ⋙ inclRight _ _) { app := fun _ ↦ edge _ _ }

section mapPair

variable (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E')

@[simp]
/-
**CategoryTheory.Join.mapPair_obj_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Join`。
形式化陈述：mapPair_obj_left (c : C) : (mapPair Fₗ Fᵣ).obj (left c) = left (Fₗ.obj c)
参数：c : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapPair_obj_left (c : C) : (mapPair Fₗ Fᵣ).obj (left c) = left (Fₗ.obj c) := rfl

@[simp]
/-
**CategoryTheory.Join.mapPair_obj_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Join`。
形式化陈述：mapPair_obj_right (d : D) : (mapPair Fₗ Fᵣ).obj (right d) = right (Fᵣ.obj 
d)
参数：d : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapPair_obj_right (d : D) : (mapPair Fₗ Fᵣ).obj (right d) = right (Fᵣ.obj d) := rfl

@[simp]
/-
**CategoryTheory.Join.mapPair_map_inclLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Join`。
形式化陈述：mapPair_map_inclLeft {c c' : C} (f : c ⟶ c') : (mapPair Fₗ Fᵣ).map ((inclL
eft C D).map f) = (inclLeft E E').map (Fₗ.map f)
参数：f : c ⟶ c'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapPair_map_inclLeft {c c' : C} (f : c ⟶ c') :
    (mapPair Fₗ Fᵣ).map ((inclLeft C D).map f) = (inclLeft E E').map (Fₗ.map f) := rfl

@[simp]
/-
**CategoryTheory.Join.mapPair_map_inclRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Join`。
形式化陈述：mapPair_map_inclRight {d d' : D} (f : d ⟶ d') : (mapPair Fₗ Fᵣ).map ((incl
Right C D).map f) = (inclRight E E').map (Fᵣ.map f)
参数：f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapPair_map_inclRight {d d' : D} (f : d ⟶ d') :
    (mapPair Fₗ Fᵣ).map ((inclRight C D).map f) = (inclRight E E').map (Fᵣ.map f) := rfl

/-- Characterizing `mapPair` on left morphisms. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Join.mapPairLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join
`。
形式化陈述：mapPairLeft : inclLeft _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fₗ ⋙ inclLeft _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterizing `mapPair` on left morphisms.
-/
def mapPairLeft : inclLeft _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fₗ ⋙ inclLeft _ _ := mkFunctorLeft _ _ _

/-- Characterizing `mapPair` on right morphisms. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Join.mapPairRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Joi
n`。
形式化陈述：mapPairRight : inclRight _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fᵣ ⋙ inclRight _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterizing `mapPair` on right morphisms.
-/
def mapPairRight : inclRight _ _ ⋙ mapPair Fₗ Fᵣ ≅ Fᵣ ⋙ inclRight _ _ := mkFunctorRight _ _ _

end mapPair

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Any functor out of a join is naturally isomorphic to a functor of the form `mkFunctor F G α`. -/
@[simps!]
/-
**CategoryTheory.Join.isoMkFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Joi
n`。
形式化陈述：isoMkFunctor (F : C ⋆ D ⥤ E) : F ≅ mkFunctor (inclLeft C D ⋙ F) (inclRight
 C D ⋙ F) (whiskerRight (edgeTransform C D) F)
参数：F : C ⋆ D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor out of a join is naturally isomorphic to a functor of the form `mkFu
nctor F G α`.
-/
def isoMkFunctor (F : C ⋆ D ⥤ E) :
    F ≅ mkFunctor (inclLeft C D ⋙ F) (inclRight C D ⋙ F) (whiskerRight (edgeTransform C D) F) :=
  mkNatIso (mkFunctorLeft _ _ _).symm (mkFunctorRight _ _ _).symm

/-- `mapPair` respects identities -/
@[simps!]
/-
**CategoryTheory.Join.mapPairId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapPair` respects identities
-/
def mapPairId : mapPair (𝟭 C) (𝟭 D) ≅ 𝟭 (C ⋆ D) :=
  mkNatIso
    (mapPairLeft _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
    (mapPairRight _ _ ≪≫ Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

variable {J : Type u₅} [Category.{v₅} J]
  {K : Type u₆} [Category.{v₆} K]

-- @[simps!] times out here
/-- `mapPair` respects composition -/
/-
**CategoryTheory.Join.mapPairComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join
`。
形式化陈述：mapPairComp (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K) : mapPai
r (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≅ mapPair Fₗ Fᵣ ⋙ mapPair Gₗ Gᵣ
参数：Fₗ : C ⥤ E；Fᵣ : D ⥤ E'；Gₗ : E ⥤ J；Gᵣ : E' ⥤ K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapPair` respects composition
-/
def mapPairComp (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K) :
    mapPair (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≅ mapPair Fₗ Fᵣ ⋙ mapPair Gₗ Gᵣ :=
  mkNatIso
    (mapPairLeft (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fₗ Gₗ (inclLeft J K) ≪≫
      (isoWhiskerLeft Fₗ (mapPairLeft Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fₗ (inclLeft E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairLeft Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))
    (mapPairRight (Fₗ ⋙ Gₗ) (Fᵣ ⋙ Gᵣ) ≪≫
      Functor.associator Fᵣ Gᵣ (inclRight J K) ≪≫
      (isoWhiskerLeft Fᵣ (mapPairRight Gₗ Gᵣ).symm) ≪≫
      (Functor.associator Fᵣ (inclRight E E') (mapPair Gₗ Gᵣ)).symm ≪≫
      isoWhiskerRight (mapPairRight Fₗ Fᵣ).symm (mapPair Gₗ Gᵣ))

section mapPairComp

variable (Fₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gₗ : E ⥤ J) (Gᵣ : E' ⥤ K)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapPairComp_hom_app_left** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Join`。
形式化陈述：mapPairComp_hom_app_left (c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left
 c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)))
参数：c : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapPairComp_hom_app_left (c : C) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c))) := by
  dsimp [mapPairComp]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapPairComp_hom_app_right** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Join`。
形式化陈述：mapPairComp_hom_app_right (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (rig
ht d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d)))
参数：d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapPairComp_hom_app_right (d : D) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).hom.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d))) := by
  dsimp [mapPairComp]
  simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapPairComp_inv_app_left** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Join`。
形式化陈述：mapPairComp_inv_app_left (c : C) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left
 c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c)))
参数：c : C。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Join.mkNatTrans.congr_simp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapPairComp_inv_app_left (c : C) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (left c) = 𝟙 (left (Gₗ.obj (Fₗ.obj c))) := by
  dsimp [mapPairComp]
  simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapPairComp_inv_app_right** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Join`。
形式化陈述：mapPairComp_inv_app_right (d : D) : (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (rig
ht d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d)))
参数：d : D。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Join.mkNatTrans.congr_simp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapPairComp_inv_app_right (d : D) :
    (mapPairComp Fₗ Fᵣ Gₗ Gᵣ).inv.app (right d) = 𝟙 (right (Gᵣ.obj (Fᵣ.obj d))) := by
  dsimp [mapPairComp]
  simp

end mapPairComp

end Functoriality

section NaturalTransforms

variable {E : Type u₃} [Category.{v₃} E]
  {E' : Type u₄} [Category.{v₄} E']

variable {C D}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural transformation `Fₗ ⟶ Gₗ` induces a natural transformation
  `mapPair Fₗ H ⟶ mapPair Gₗ H` for every `H : D ⥤ E'`. -/
@[simps!]
/-
**CategoryTheory.Join.mapWhiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Join`。
形式化陈述：mapWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) (H : D ⥤ E') : map
Pair Fₗ H ⟶ mapPair Gₗ H
参数：α : Fₗ ⟶ Gₗ；H : D ⥤ E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation `Fₗ ⟶ Gₗ` induces a natural transformation
  `mapPair Fₗ H ⟶ mapPair Gₗ H` for every `H : D ⥤ E'`.
-/
def mapWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) (H : D ⥤ E') :
    mapPair Fₗ H ⟶ mapPair Gₗ H :=
  mkNatTrans
    ((mapPairLeft Fₗ H).hom ≫ whiskerRight α (inclLeft E E') ≫ (mapPairLeft Gₗ H).inv)
    ((mapPairRight Fₗ H).hom ≫ whiskerRight (𝟙 H) (inclRight E E') ≫ (mapPairRight Gₗ H).inv)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapWhiskerRight_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Join`。
形式化陈述：mapWhiskerRight_comp {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} {Hₗ : C ⥤ E} (α : Fₗ ⟶ Gₗ) 
(β : Gₗ ⟶ Hₗ) (H : D ⥤ E') : mapWhiskerRight (α ≫ β) H = mapWhiskerRight α H ≫ m
apWhiskerRight β H
参数：α : Fₗ ⟶ Gₗ；β : Gₗ ⟶ Hₗ；H : D ⥤ E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma mapWhiskerRight_comp {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} {Hₗ : C ⥤ E}
    (α : Fₗ ⟶ Gₗ) (β : Gₗ ⟶ Hₗ) (H : D ⥤ E') :
    mapWhiskerRight (α ≫ β) H = mapWhiskerRight α H ≫ mapWhiskerRight β H := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapWhiskerRight_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Join`。
形式化陈述：mapWhiskerRight_id (Fₗ : C ⥤ E) (H : D ⥤ E') : mapWhiskerRight (𝟙 Fₗ) H = 
𝟙 _
参数：Fₗ : C ⥤ E；H : D ⥤ E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapWhiskerRight_id (Fₗ : C ⥤ E) (H : D ⥤ E') :
    mapWhiskerRight (𝟙 Fₗ) H = 𝟙 _ := by
  cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural transformation `Fᵣ ⟶ Gᵣ` induces a natural transformation
  `mapPair H Fᵣ ⟶ mapPair H Gᵣ` for every `H : C ⥤ E`. -/
@[simps!]
/-
**CategoryTheory.Join.mapWhiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.J
oin`。
形式化陈述：mapWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ⟶ Gᵣ) : map
Pair H Fᵣ ⟶ mapPair H Gᵣ
参数：H : C ⥤ E；α : Fᵣ ⟶ Gᵣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation `Fᵣ ⟶ Gᵣ` induces a natural transformation
  `mapPair H Fᵣ ⟶ mapPair H Gᵣ` for every `H : C ⥤ E`.
-/
def mapWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ⟶ Gᵣ) :
    mapPair H Fᵣ ⟶ mapPair H Gᵣ :=
  mkNatTrans
    ((mapPairLeft H Fᵣ).hom ≫ whiskerRight (𝟙 H) (inclLeft E E') ≫ (mapPairLeft H Gᵣ).inv)
    ((mapPairRight H Fᵣ).hom ≫ whiskerRight α (inclRight E E') ≫ (mapPairRight H Gᵣ).inv)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapWhiskerLeft_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Join`。
形式化陈述：mapWhiskerLeft_comp {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} {Hᵣ : D ⥤ E'} (H : C ⥤ E) 
(α : Fᵣ ⟶ Gᵣ) (β : Gᵣ ⟶ Hᵣ) : mapWhiskerLeft H (α ≫ β) = mapWhiskerLeft H α ≫ ma
pWhiskerLeft H β
参数：H : C ⥤ E；α : Fᵣ ⟶ Gᵣ；β : Gᵣ ⟶ Hᵣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapWhiskerLeft_comp {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} {Hᵣ : D ⥤ E'}
    (H : C ⥤ E) (α : Fᵣ ⟶ Gᵣ) (β : Gᵣ ⟶ Hᵣ) :
    mapWhiskerLeft H (α ≫ β) = mapWhiskerLeft H α ≫ mapWhiskerLeft H β := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Join.mapWhiskerLeft_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Join`。
形式化陈述：mapWhiskerLeft_id (H : C ⥤ E) (Fᵣ : D ⥤ E') : mapWhiskerLeft H (𝟙 Fᵣ) = 𝟙 
_
参数：H : C ⥤ E；Fᵣ : D ⥤ E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapWhiskerLeft_id (H : C ⥤ E) (Fᵣ : D ⥤ E') :
    mapWhiskerLeft H (𝟙 Fᵣ) = 𝟙 _ := by
  cat_disch

#adaptation_note
/--
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined using `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching normal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- One can exchange `mapWhiskerLeft` and `mapWhiskerRight`. -/
/-
**CategoryTheory.Join.mapWhisker_exchange** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Join`。
形式化陈述：mapWhisker_exchange (Fₗ : C ⥤ E) (Gₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gᵣ : D ⥤ E') 
(αₗ : Fₗ ⟶ Gₗ) (αᵣ : Fᵣ ⟶ Gᵣ) : mapWhiskerLeft Fₗ αᵣ ≫ mapWhiskerRight αₗ Gᵣ = m
apWhiskerRight αₗ Fᵣ ≫ mapWhiskerLeft Gₗ αᵣ
参数：Fₗ : C ⥤ E；Gₗ : C ⥤ E；Fᵣ : D ⥤ E'；Gᵣ : D ⥤ E'；αₗ : Fₗ ⟶ Gₗ；αᵣ : Fᵣ ⟶ Gᵣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
One can exchange `mapWhiskerLeft` and `mapWhiskerRight`.
-/
lemma mapWhisker_exchange (Fₗ : C ⥤ E) (Gₗ : C ⥤ E) (Fᵣ : D ⥤ E') (Gᵣ : D ⥤ E')
    (αₗ : Fₗ ⟶ Gₗ) (αᵣ : Fᵣ ⟶ Gᵣ) :
    mapWhiskerLeft Fₗ αᵣ ≫ mapWhiskerRight αₗ Gᵣ =
      mapWhiskerRight αₗ Fᵣ ≫ mapWhiskerLeft Gₗ αᵣ := by
  ext
  cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair H Fᵣ ≅ mapPair H Gᵣ` for every `H : C ⥤ E`. -/
@[simps!]
/-
**CategoryTheory.Join.mapIsoWhiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Join`。
形式化陈述：mapIsoWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) : 
mapPair H Fᵣ ≅ mapPair H Gᵣ
参数：H : C ⥤ E；α : Fᵣ ≅ Gᵣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair H Fᵣ ≅ mapPair H Gᵣ` for every `H : C ⥤ E`.
-/
def mapIsoWhiskerLeft (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    mapPair H Fᵣ ≅ mapPair H Gᵣ :=
  mkNatIso
    (mapPairLeft H Fᵣ ≪≫ isoWhiskerRight (Iso.refl H) (inclLeft _ _) ≪≫ (mapPairLeft H Gᵣ).symm)
    (mapPairRight H Fᵣ ≪≫ isoWhiskerRight α (inclRight E E') ≪≫ (mapPairRight H Gᵣ).symm)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair Fₗ H ≅ mapPair Gₗ H` for every `H : C ⥤ E`. -/
@[simps!]
/-
**CategoryTheory.Join.mapIsoWhiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Join`。
形式化陈述：mapIsoWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') : 
mapPair Fₗ H ≅ mapPair Gₗ H
参数：α : Fₗ ≅ Gₗ；H : D ⥤ E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism `Fᵣ ≅ Gᵣ` induces a natural isomorphism
  `mapPair Fₗ H ≅ mapPair Gₗ H` for every `H : C ⥤ E`.
-/
def mapIsoWhiskerRight {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    mapPair Fₗ H ≅ mapPair Gₗ H :=
  mkNatIso
    (mapPairLeft Fₗ H ≪≫ isoWhiskerRight α (inclLeft E E') ≪≫ (mapPairLeft Gₗ H).symm)
    (mapPairRight Fₗ H ≪≫ isoWhiskerRight (Iso.refl H) (inclRight E E') ≪≫ (mapPairRight Gₗ H).symm)
/-
**CategoryTheory.Join.mapIsoWhiskerRight_hom** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Join`。
形式化陈述：mapIsoWhiskerRight_hom {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E'
) : (mapIsoWhiskerRight α H).hom = mapWhiskerRight α.hom H
参数：α : Fₗ ≅ Gₗ；H : D ⥤ E'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapIsoWhiskerRight_hom {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    (mapIsoWhiskerRight α H).hom = mapWhiskerRight α.hom H := rfl

#adaptation_note
/--
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined using `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching normal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Join.mapIsoWhiskerRight_inv** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Join`。
形式化陈述：mapIsoWhiskerRight_inv {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E'
) : (mapIsoWhiskerRight α H).inv = mapWhiskerRight α.inv H
参数：α : Fₗ ≅ Gₗ；H : D ⥤ E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.isoWhiskerRight_refl`：isoWhiskerRight_refl (F : C
 ⥤ D) (G : D ⥤ E) : isoWhiskerRight (Iso.refl F) G = Iso.refl _
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Join.mkNatIso.congr_simp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Join.mkNatTrans.congr_simp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Join.mapWhiskerRight_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined u
sing `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching n
ormal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
lemma mapIsoWhiskerRight_inv {Fₗ : C ⥤ E} {Gₗ : C ⥤ E} (α : Fₗ ≅ Gₗ) (H : D ⥤ E') :
    (mapIsoWhiskerRight α H).inv = mapWhiskerRight α.inv H := by
  ext x
  cases x <;> simp [mapIsoWhiskerRight]
/-
**CategoryTheory.Join.mapIsoWhiskerLeft_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Join`。
形式化陈述：mapIsoWhiskerLeft_hom (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ
) : (mapIsoWhiskerLeft H α).hom = mapWhiskerLeft H α.hom
参数：H : C ⥤ E；α : Fᵣ ≅ Gᵣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapIsoWhiskerLeft_hom (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    (mapIsoWhiskerLeft H α).hom = mapWhiskerLeft H α.hom := rfl

#adaptation_note
/--
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined using `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching normal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Join.mapIsoWhiskerLeft_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Join`。
形式化陈述：mapIsoWhiskerLeft_inv (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ
) : (mapIsoWhiskerLeft H α).inv = mapWhiskerLeft H α.inv
参数：H : C ⥤ E；α : Fᵣ ≅ Gᵣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.isoWhiskerRight_refl`：isoWhiskerRight_refl (F : C
 ⥤ D) (G : D ⥤ E) : isoWhiskerRight (Iso.refl F) G = Iso.refl _
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Join.mkNatIso.congr_simp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Join.mkNatTrans.congr_simp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Join.mapWhiskerLeft_app`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {E : Type u₃} [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…

--- 原说明 ---
The statement of `mapWhiskerLeft_app` and `mapWhiskerRight_app` was determined u
sing `simp` with
`respectTransparency.types false`. In order to apply these, we need a matching n
ormal form.
We achieve this using `respectTransparency.types false` on this lemma, too.
Probable fix: Figure out what the intended statement of `mapWhiskerLeft_app` and
`mapWhiskerRight_app` is, and only then fix this lemma.
-/
lemma mapIsoWhiskerLeft_inv (H : C ⥤ E) {Fᵣ : D ⥤ E'} {Gᵣ : D ⥤ E'} (α : Fᵣ ≅ Gᵣ) :
    (mapIsoWhiskerLeft H α).inv = mapWhiskerLeft H α.inv := by
  ext x
  cases x <;> simp [mapIsoWhiskerLeft]

end NaturalTransforms

section mapPairEquiv

variable {C' : Type u₃} [Category.{v₃} C']
  {D' : Type u₄} [Category.{v₄} D']

variable {C D}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equivalent categories have equivalent joins. -/
@[simps]
/-
**CategoryTheory.Join.mapPairEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Joi
n`。
形式化陈述：mapPairEquiv (e : C ≌ C') (e' : D ≌ D') : C ⋆ D ≌ C' ⋆ D' where functor
参数：e : C ≌ C'；e' : D ≌ D'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalent categories have equivalent joins.
-/
def mapPairEquiv (e : C ≌ C') (e' : D ≌ D') : C ⋆ D ≌ C' ⋆ D' where
  functor := mapPair e.functor e'.functor
  inverse := mapPair e.inverse e'.inverse
  unitIso :=
    mapPairId.symm ≪≫
      mapIsoWhiskerRight e.unitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.unitIso ≪≫
      mapPairComp _ _ _ _
  counitIso :=
    (mapPairComp _ _ _ _).symm ≪≫
      mapIsoWhiskerRight e.counitIso _ ≪≫
      mapIsoWhiskerLeft _ e'.counitIso ≪≫
      mapPairId
  functor_unitIso_comp x := by
    cases x <;>
    simp [← (inclLeft C' D').map_comp, ← (inclRight C' D').map_comp]
/-
**CategoryTheory.Join.isEquivalenceMapPair** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Join`。
形式化陈述：isEquivalenceMapPair {F : C ⥤ C'} {F' : D ⥤ D'} [F.IsEquivalence] [F'.IsEq
uivalence] : (mapPair F F').IsEquivalence
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isEquivalenceMapPair {F : C ⥤ C'} {F' : D ⥤ D'} [F.IsEquivalence] [F'.IsEquivalence] :
    (mapPair F F').IsEquivalence :=
  inferInstanceAs (mapPairEquiv F.asEquivalence F'.asEquivalence).functor.IsEquivalence

end mapPairEquiv

end Join

end CategoryTheory

