/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.ConeCategory

/-!

# Multi-(co)equalizers

A *multiequalizer* is an equalizer of two morphisms between two products.
Since both products and equalizers are limits, such an object is again a limit.
This file provides the diagram whose limit is indeed such an object.
In fact, it is well-known that any limit can be obtained as a multiequalizer.
The dual construction (multicoequalizers) is also provided.

## Projects

Prove that a multiequalizer can be identified with
an equalizer between products (and analogously for multicoequalizers).

Prove that the limit of any diagram is a multiequalizer (and similarly for colimits).

-/

@[expose] public section


namespace CategoryTheory.Limits

universe t w w' v u

set_option linter.checkUnivs false in
/--
Definition of `MulticospanShape` / `MulticospanShape` 的定义

English:
structure MulticospanShape
  parameters: where
  axioms and operations (4):
    - L : Type w
    - R : Type w'
    - fst : R -> L
    - snd : R -> L

中文:
结构 MulticospanShape
  参数: where
  公理与运算 (4 个):
    - L : 类型 w
    - R : 类型 w'
    - fst : R -> L
    - snd : R -> L
-/
structure MulticospanShape where
  /-- the left type -/
  L : Type w
  /-- the right type -/
  R : Type w'
  /-- the first map `R → L` -/
  fst : R -> L
  /-- the second map `R → L` -/
  snd : R -> L

/-- Given a type `ι`, this is the shape of multiequalizer diagrams corresponding
to situations where we want to equalize two families of maps `U i ⟶ V ⟨i, j⟩`
and `U j ⟶ V ⟨i, j⟩` with `i : ι` and `j : ι`. -/
@[simps]
/--
Definition of `MulticospanShape.prod` / `MulticospanShape.prod` 的定义

English:
definition MulticospanShape.prod
  signature: (ι : Type w)
  body: ι
  R := ι × ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd

中文:
定义 MulticospanShape.乘积
  签名: (ι : 类型 w)
  定义体: ι
  R := ι × ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd
-/
def MulticospanShape.prod (ι : Type w) : MulticospanShape where
  L := ι
  R := ι × ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd

set_option linter.checkUnivs false in
/--
Definition of `MultispanShape` / `MultispanShape` 的定义

English:
structure MultispanShape
  parameters: where
  axioms and operations (4):
    - L : Type w
    - R : Type w'
    - fst : L -> R
    - snd : L -> R

中文:
结构 MultispanShape
  参数: where
  公理与运算 (4 个):
    - L : 类型 w
    - R : 类型 w'
    - fst : L -> R
    - snd : L -> R
-/
structure MultispanShape where
  /-- the left type -/
  L : Type w
  /-- the right type -/
  R : Type w'
  /-- the first map `L → R` -/
  fst : L -> R
  /-- the second map `L → R` -/
  snd : L -> R

/-- Given a type `ι`, this is the shape of multicoequalizer diagrams corresponding
to situations where we want to coequalize two families of maps `V ⟨i, j⟩ ⟶ U i`
and `V ⟨i, j⟩ ⟶ U j` with `i : ι` and `j : ι`. -/
@[simps]
/--
Definition of `MultispanShape.prod` / `MultispanShape.prod` 的定义

English:
definition MultispanShape.prod
  signature: (ι : Type w)
  body: ι × ι
  R := ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd

中文:
定义 MultispanShape.乘积
  签名: (ι : 类型 w)
  定义体: ι × ι
  R := ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd
-/
def MultispanShape.prod (ι : Type w) : MultispanShape where
  L := ι × ι
  R := ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd

/-- Given a linearly ordered type `ι`, this is the shape of multicoequalizer diagrams
corresponding to situations where we want to coequalize two families of maps
`V ⟨i, j⟩ ⟶ U i` and `V ⟨i, j⟩ ⟶ U j` with `i < j`. -/
@[simps]
/--
Definition of `MultispanShape.ofLinearOrder` / `MultispanShape.ofLinearOrder` 的定义

English:
definition MultispanShape.ofLinearOrder
  signature: (ι : Type w) [LinearOrder ι]
  body: {x : ι × ι | x.1 < x.2}
  R := ι
  fst x := x.1.1
  snd x := x.1.2

中文:
定义 MultispanShape.ofLinearOrder
  签名: (ι : 类型 w) [线性序 ι]
  定义体: {x : ι × ι | x.1 < x.2}
  R := ι
  fst x := x.1.1
  snd x := x.1.2
-/
def MultispanShape.ofLinearOrder (ι : Type w) [LinearOrder ι] : MultispanShape where
  L := {x : ι × ι | x.1 < x.2}
  R := ι
  fst x := x.1.1
  snd x := x.1.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (MultispanShape.ofLinearOrder Bool).L
  body: ⟨⟨False, True⟩, by simp⟩
  uniq := by rintro ⟨⟨(_ | _), (_ | _)⟩, _⟩ <;> tauto

中文:
实例 :
  签名: 唯一 (MultispanShape.ofLinearOrder 布尔值).L
  定义体: ⟨⟨False, True⟩, by simp⟩
  uniq := by rintro ⟨⟨(_ | _), (_ | _)⟩, _⟩ <;> tauto
-/
instance : Unique (MultispanShape.ofLinearOrder Bool).L where
  default := ⟨⟨False, True⟩, by simp⟩
  uniq := by rintro ⟨⟨(_ | _), (_ | _)⟩, _⟩ <;> tauto

/--
Inductive type `WalkingMulticospan` / 归纳类型 `WalkingMulticospan`

English:
inductive WalkingMulticospan
  parameters: (J : MulticospanShape.{w, w'})
  constructors (2):
    - left: J.L -> WalkingMulticospan J
    - right: J.R -> WalkingMulticospan J

中文:
归纳类型 WalkingMulticospan
  参数: (J : MulticospanShape.{w, w'})
  构造子 (2 个):
    - left: J.L -> WalkingMulticospan J
    - right: J.R -> WalkingMulticospan J
-/
inductive WalkingMulticospan (J : MulticospanShape.{w, w'}) : Type max w w'
  | left : J.L -> WalkingMulticospan J
  | right : J.R -> WalkingMulticospan J

/--
Inductive type `WalkingMultispan` / 归纳类型 `WalkingMultispan`

English:
inductive WalkingMultispan
  parameters: (J : MultispanShape.{w, w'})
  constructors (2):
    - left: J.L -> WalkingMultispan J
    - right: J.R -> WalkingMultispan J

中文:
归纳类型 WalkingMultispan
  参数: (J : MultispanShape.{w, w'})
  构造子 (2 个):
    - left: J.L -> WalkingMultispan J
    - right: J.R -> WalkingMultispan J
-/
inductive WalkingMultispan (J : MultispanShape.{w, w'}) : Type max w w'
  | left : J.L -> WalkingMultispan J
  | right : J.R -> WalkingMultispan J

namespace WalkingMulticospan

variable {J : MulticospanShape.{w, w'}}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: J.L] : Inhabited (WalkingMulticospan J)
  body: ⟨left default⟩

中文:
实例 [可居
  签名: J.L] : 可居 (WalkingMulticospan J)
  定义体: ⟨left default⟩
-/
instance [Inhabited J.L] : Inhabited (WalkingMulticospan J) :=
  ⟨left default⟩

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : forall _ _ : WalkingMulticospan J, Type max w w'
  constructors (3):
    - id: (A) : Hom A A
    - fst: (b) : Hom (left (J.fst b)) (right b)
    - snd: (b) : Hom (left (J.snd b)) (right b)

中文:
归纳类型 态射
  参数: : 对任意 _ _ : WalkingMulticospan J, 类型 最大值 w w'
  构造子 (3 个):
    - id: (A) : 态射 A A
    - fst: (b) : 态射 (left (J.fst b)) (right b)
    - snd: (b) : 态射 (left (J.snd b)) (right b)
-/
inductive Hom : forall _ _ : WalkingMulticospan J, Type max w w'
  | id (A) : Hom A A
  | fst (b) : Hom (left (J.fst b)) (right b)
  | snd (b) : Hom (left (J.snd b)) (right b)

instance {a : WalkingMulticospan J} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: : forall {A B C : WalkingMulticospan J} (_ : Hom A B) (_ : Hom B C), Hom A C

中文:
定义 态射.comp
  签名: : 对任意 {A B C : WalkingMulticospan J} (_ : 态射 A B) (_ : 态射 B C), 态射 A C
-/
def Hom.comp : forall {A B C : WalkingMulticospan J} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst b, Hom.id _ => Hom.fst b
  | _, _, _, Hom.snd b, Hom.id _ => Hom.snd b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory (WalkingMulticospan J)
  body: Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]

中文:
实例 :
  签名: 小范畴 (WalkingMulticospan J)
  定义体: Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
-/
instance : SmallCategory (WalkingMulticospan J) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
/--
lemma `Hom.id_eq_id` / 引理 `Hom.id_eq_id`

English:
lemma Hom.id_eq_id
  given: (X : WalkingMulticospan J)
  proof: rfl

@[simp]

中文:
引理 态射.id_eq_id
  条件: (X : WalkingMulticospan J)
  证明: rfl

@[simp]
-/
lemma Hom.id_eq_id (X : WalkingMulticospan J) :
    Hom.id X = 𝟙 X := rfl

@[simp]
/--
lemma `Hom.comp_eq_comp` / 引理 `Hom.comp_eq_comp`

English:
lemma Hom.comp_eq_comp
  statement: {X Y Z : WalkingMulticospan J}
  proof: rfl

中文:
引理 态射.comp_eq_comp
  结论: {X Y Z : WalkingMulticospan J}
  证明: rfl
-/
lemma Hom.comp_eq_comp {X Y Z : WalkingMulticospan J}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

/-- Construct a natural isomorphism between functors out of a walking multicospan from its
components. -/
@[simps!]
/--
Definition of `functorExt` / `functorExt` 的定义

English:
definition functorExt
  signature: {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
  body: NatIso.ofComponents (fun j => match j with | .left i => left i | .right i => right i) by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

中文:
定义 functorExt
  签名: {C : 类型} [范畴* C] {F G : WalkingMulticospan J ⥤ C}
  定义体: NatIso.ofComponents (fun j => match j with | .left i => left i | .right i => right i) by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

Depends on / 依赖: F.map, G.map, NatIso, NatIso.ofComponents, WalkingMulticospan, WalkingMulticospan.Hom.snd, cat_disch, ofComponents
-/
def functorExt {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
    (left : forall i, F.obj (.left i) ≅ G.obj (.left i))
    (right : forall i, F.obj (.right i) ≅ G.obj (.right i))
    (wl : forall i, F.map (WalkingMulticospan.Hom.fst i) ≫ (right i).hom =
      (left _).hom ≫ G.map (WalkingMulticospan.Hom.fst i) := by cat_disch)
    (wr : forall i, F.map (WalkingMulticospan.Hom.snd i) ≫ (right i).hom =
      (left _).hom ≫ G.map (WalkingMulticospan.Hom.snd i) := by cat_disch) :
    F ≅ G :=
NatIso.ofComponents (fun j => match j with | .left i => left i | .right i => right i) by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `functor_ext` / 引理 `functor_ext`

English:
lemma functor_ext
  statement: {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
  proof: Functor.ext_of_iso
    (functorExt (fun _ => eqToIso (left _)) (fun _ => eqToIso (right _)) wl wr)
    (by rintro (_ | _) <;> grind) (by rintro (_ | _) <;> simp)

中文:
引理 functor_ext
  结论: {C : 类型} [范畴* C] {F G : WalkingMulticospan J ⥤ C}
  证明: Functor.ext_of_iso
    (functorExt (fun _ => eqToIso (left _)) (fun _ => eqToIso (right _)) wl wr)
    (by rintro (_ | _) <;> grind) (by rintro (_ | _) <;> simp)

Depends on / 依赖: Functor, Functor.ext_of_iso, eqToIso, ext_of_iso, functorExt
-/
lemma functor_ext {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
    (left : forall i, F.obj (.left i) = G.obj (.left i))
    (right : forall i, F.obj (.right i) = G.obj (.right i))
    (wl : forall i, F.map (Hom.fst i) ≫ eqToHom (right i) = eqToHom (left _) ≫ G.map (Hom.fst i))
    (wr : forall i, F.map (Hom.snd i) ≫ eqToHom (right i) = eqToHom (left _) ≫ G.map (Hom.snd i)) :
    F = G :=
  Functor.ext_of_iso
    (functorExt (fun _ => eqToIso (left _)) (fun _ => eqToIso (right _)) wl wr)
    (by rintro (_ | _) <;> grind) (by rintro (_ | _) <;> simp)

end WalkingMulticospan

namespace WalkingMultispan

variable {J : MultispanShape.{w, w'}}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: J.L] : Inhabited (WalkingMultispan J)
  body: ⟨left default⟩

中文:
实例 [可居
  签名: J.L] : 可居 (WalkingMultispan J)
  定义体: ⟨left default⟩
-/
instance [Inhabited J.L] : Inhabited (WalkingMultispan J) :=
  ⟨left default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{t}
  signature: J.L] [Small.{t} J.R] : Small.{t} (WalkingMultispan J)
  body: small_of_surjective (f := Sum.elim WalkingMultispan.left WalkingMultispan.right)
    (by rintro (_ | _) <;> aesop)

中文:
实例 [Small.{t}
  签名: J.L] [Small.{t} J.R] : Small.{t} (WalkingMultispan J)
  定义体: small_of_surjective (f := Sum.elim WalkingMultispan.left WalkingMultispan.right)
    (by rintro (_ | _) <;> aesop)

Depends on / 依赖: Sum.elim, WalkingMultispan, WalkingMultispan.left, WalkingMultispan.right, small_of_surjective
-/
instance [Small.{t} J.L] [Small.{t} J.R] : Small.{t} (WalkingMultispan J) :=
  small_of_surjective (f := Sum.elim WalkingMultispan.left WalkingMultispan.right)
    (by rintro (_ | _) <;> aesop)

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : forall _ _ : WalkingMultispan J, Type max w w'
  constructors (3):
    - id: (A) : Hom A A
    - fst: (a) : Hom (left a) (right (J.fst a))
    - snd: (a) : Hom (left a) (right (J.snd a))

中文:
归纳类型 态射
  参数: : 对任意 _ _ : WalkingMultispan J, 类型 最大值 w w'
  构造子 (3 个):
    - id: (A) : 态射 A A
    - fst: (a) : 态射 (left a) (right (J.fst a))
    - snd: (a) : 态射 (left a) (right (J.snd a))
-/
inductive Hom : forall _ _ : WalkingMultispan J, Type max w w'
  | id (A) : Hom A A
  | fst (a) : Hom (left a) (right (J.fst a))
  | snd (a) : Hom (left a) (right (J.snd a))

instance {a : WalkingMultispan J} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: : forall {A B C : WalkingMultispan J} (_ : Hom A B) (_ : Hom B C), Hom A C

中文:
定义 态射.comp
  签名: : 对任意 {A B C : WalkingMultispan J} (_ : 态射 A B) (_ : 态射 B C), 态射 A C
-/
def Hom.comp : forall {A B C : WalkingMultispan J} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst a, Hom.id _ => Hom.fst a
  | _, _, _, Hom.snd a, Hom.id _ => Hom.snd a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SmallCategory (WalkingMultispan J)
  body: Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]

中文:
实例 :
  签名: 小范畴 (WalkingMultispan J)
  定义体: Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
-/
instance : SmallCategory (WalkingMultispan J) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  comp_id := by
    rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl
  assoc := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> rfl

@[simp]
/--
lemma `Hom.id_eq_id` / 引理 `Hom.id_eq_id`

English:
lemma Hom.id_eq_id
  given: (X : WalkingMultispan J)
  statement: Hom.id X = 𝟙 X
  proof: rfl

@[simp]

中文:
引理 态射.id_eq_id
  条件: (X : WalkingMultispan J)
  结论: 态射.id X = 𝟙 X
  证明: rfl

@[simp]
-/
lemma Hom.id_eq_id (X : WalkingMultispan J) : Hom.id X = 𝟙 X := rfl

@[simp]
/--
lemma `Hom.comp_eq_comp` / 引理 `Hom.comp_eq_comp`

English:
lemma Hom.comp_eq_comp
  statement: {X Y Z : WalkingMultispan J}
  proof: rfl

中文:
引理 态射.comp_eq_comp
  结论: {X Y Z : WalkingMultispan J}
  证明: rfl
-/
lemma Hom.comp_eq_comp {X Y Z : WalkingMultispan J}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

/-- Construct a natural isomorphism between functors out of a walking multispan from its
components. -/
@[simps!]
/--
Definition of `functorExt` / `functorExt` 的定义

English:
definition functorExt
  signature: {C : Type*} [Category* C] {F G : WalkingMultispan J ⥤ C}
  body: NatIso.ofComponents (fun j => match j with | .left i => left i | .right i => right i) by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

中文:
定义 functorExt
  签名: {C : 类型} [范畴* C] {F G : WalkingMultispan J ⥤ C}
  定义体: NatIso.ofComponents (fun j => match j with | .left i => left i | .right i => right i) by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

Depends on / 依赖: F.map, G.map, NatIso, NatIso.ofComponents, WalkingMultispan, WalkingMultispan.Hom.snd, cat_disch, ofComponents
-/
def functorExt {C : Type*} [Category* C] {F G : WalkingMultispan J ⥤ C}
    (left : forall i, F.obj (.left i) ≅ G.obj (.left i))
    (right : forall i, F.obj (.right i) ≅ G.obj (.right i))
    (wl : forall i, F.map (WalkingMultispan.Hom.fst i) ≫ (right _).hom =
      (left i).hom ≫ G.map (WalkingMultispan.Hom.fst _) := by cat_disch)
    (wr : forall i, F.map (WalkingMultispan.Hom.snd i) ≫ (right _).hom =
      (left i).hom ≫ G.map (WalkingMultispan.Hom.snd _) := by cat_disch) :
    F ≅ G :=
NatIso.ofComponents (fun j => match j with | .left i => left i | .right i => right i) by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

instance (a : WalkingMultispan J) : Unique (a ⟶ a) where
  default := 𝟙 _
  uniq := by rintro ⟨⟩; rfl

instance (a b : J.L) : Subsingleton (left a ⟶ left b) := by
  by_cases h : a = b
  · subst h
    infer_instance
  · have : IsEmpty (left a ⟶ left b) := ⟨by rintro ⟨⟩; simp at h⟩
    infer_instance

instance (a b : J.R) : Subsingleton (right a ⟶ right b) := by
  by_cases h : a = b
  · subst h
    infer_instance
  · have : IsEmpty (right a ⟶ right b) := ⟨by rintro ⟨⟩; simp at h⟩
    infer_instance

instance (a : J.R) (b : J.L) : IsEmpty (right a ⟶ left b) := ⟨by rintro ⟨⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallySmall.{t} (WalkingMultispan J)
  body: by
    rintro (l | r) (l' | r')
    · infer_instance
    · let T₁ := { u : Unit // J.fst l = r' }
      let T₂ := { u : Unit // J.snd l = r' }
      let f : T₁ oplus T₂ -> (left l ⟶ right r') :=
        Sum.elim (fun ⟨_, h⟩ => by subst h; exact Hom.fst l)
          (fun ⟨_, h⟩ => by subst h; exact H

中文:
实例 :
  签名: LocallySmall.{t} (WalkingMultispan J)
  定义体: by
    rintro (l | r) (l' | r')
    · infer_instance
    · let T₁ := { u : Unit // J.fst l = r' }
      let T₂ := { u : Unit // J.snd l = r' }
      let f : T₁ oplus T₂ -> (left l ⟶ right r') :=
        Sum.elim (fun ⟨_, h⟩ => by subst h; exact Hom.fst l)
          (fun ⟨_, h⟩ => by subst h; exact H

Depends on / 依赖: Hom.fst, Hom.snd, J.fst, J.snd, Sum.elim, Sum.inl, Sum.inr, infer_instance, small_of_surjective
-/
instance : LocallySmall.{t} (WalkingMultispan J) where
  hom_small := by
    rintro (l | r) (l' | r')
    · infer_instance
    · let T₁ := { u : Unit // J.fst l = r' }
      let T₂ := { u : Unit // J.snd l = r' }
      let f : T₁ oplus T₂ -> (left l ⟶ right r') :=
        Sum.elim (fun ⟨_, h⟩ => by subst h; exact Hom.fst l)
          (fun ⟨_, h⟩ => by subst h; exact Hom.snd l)
      refine small_of_surjective (f := f) ?_
      rintro (_ | _)
      · exact ⟨Sum.inl ⟨⟨⟩, rfl⟩, rfl⟩
      · exact ⟨Sum.inr ⟨⟨⟩, rfl⟩, rfl⟩
    · infer_instance
    · infer_instance

variable (J) in
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : WalkingMultispan J ≃ J.L oplus J.R where
  body: match x with
    | left a => Sum.inl a
    | right b => Sum.inr b
  invFun := Sum.elim left right
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

中文:
定义 equiv
  签名: : WalkingMultispan J ≃ J.L oplus J.R where
  定义体: match x with
    | left a => Sum.inl a
    | right b => Sum.inr b
  invFun := Sum.elim left right
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl
-/
def equiv : WalkingMultispan J ≃ J.L oplus J.R where
  toFun x := match x with
    | left a => Sum.inl a
    | right b => Sum.inr b
  invFun := Sum.elim left right
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

variable (J) in
/--
Definition of `arrowEquiv` / `arrowEquiv` 的定义

English:
definition arrowEquiv
  signature: :
  body: match f.hom with
    | .id x => Sum.inl x
    | .fst a => Sum.inr (Sum.inl a)
    | .snd a => Sum.inr (Sum.inr a)
  invFun :=
    Sum.elim (fun X => Arrow.mk (𝟙 X))
      (Sum.elim (fun a => Arrow.mk (Hom.fst a : left _ ⟶ right _))
        (fun a => Arrow.mk (Hom.snd a : left _ ⟶ right _)))
  left_i

中文:
定义 arrowEquiv
  签名: :
  定义体: match f.hom with
    | .id x => Sum.inl x
    | .fst a => Sum.inr (Sum.inl a)
    | .snd a => Sum.inr (Sum.inr a)
  invFun :=
    Sum.elim (fun X => Arrow.mk (𝟙 X))
      (Sum.elim (fun a => Arrow.mk (Hom.fst a : left _ ⟶ right _))
        (fun a => Arrow.mk (Hom.snd a : left _ ⟶ right _)))
  left_i

Depends on / 依赖: f.hom
-/
def arrowEquiv :
    Arrow (WalkingMultispan J) ≃ WalkingMultispan J oplus J.L oplus J.L where
  toFun f := match f.hom with
    | .id x => Sum.inl x
    | .fst a => Sum.inr (Sum.inl a)
    | .snd a => Sum.inr (Sum.inr a)
  invFun :=
    Sum.elim (fun X => Arrow.mk (𝟙 X))
      (Sum.elim (fun a => Arrow.mk (Hom.fst a : left _ ⟶ right _))
        (fun a => Arrow.mk (Hom.snd a : left _ ⟶ right _)))
  left_inv := by rintro ⟨_, _, (_ | _ | _)⟩ <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

end WalkingMultispan

/--
Definition of `MulticospanIndex` / `MulticospanIndex` 的定义

English:
structure MulticospanIndex
  parameters: (J : MulticospanShape.{w, w'})
  axioms and operations (4):
    - left : J.L -> C
    - right : J.R -> C
    - fst : forall b, left (J.fst b) ⟶ right b
    - snd : forall b, left (J.snd b) ⟶ right b

中文:
结构 MulticospanIndex
  参数: (J : MulticospanShape.{w, w'})
  公理与运算 (4 个):
    - left : J.L -> C
    - right : J.R -> C
    - fst : 对任意 b, left (J.fst b) ⟶ right b
    - snd : 对任意 b, left (J.snd b) ⟶ right b
-/
structure MulticospanIndex (J : MulticospanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  /-- Left map, from `J.L` to `C` -/
  left : J.L -> C
  /-- Right map, from `J.R` to `C` -/
  right : J.R -> C
  /-- A family of maps from `left (J.fst b)` to `right b` -/
  fst : forall b, left (J.fst b) ⟶ right b
  /-- A family of maps from `left (J.snd b)` to `right b` -/
  snd : forall b, left (J.snd b) ⟶ right b

/--
Definition of `MultispanIndex` / `MultispanIndex` 的定义

English:
structure MultispanIndex
  parameters: (J : MultispanShape.{w, w'})
  axioms and operations (4):
    - left : J.L -> C
    - right : J.R -> C
    - fst : forall a, left a ⟶ right (J.fst a)
    - snd : forall a, left a ⟶ right (J.snd a)

中文:
结构 MultispanIndex
  参数: (J : MultispanShape.{w, w'})
  公理与运算 (4 个):
    - left : J.L -> C
    - right : J.R -> C
    - fst : 对任意 a, left a ⟶ right (J.fst a)
    - snd : 对任意 a, left a ⟶ right (J.snd a)
-/
structure MultispanIndex (J : MultispanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  /-- Left map, from `J.L` to `C` -/
  left : J.L -> C
  /-- Right map, from `J.R` to `C` -/
  right : J.R -> C
  /-- A family of maps from `left a` to `right (J.fst a)` -/
  fst : forall a, left a ⟶ right (J.fst a)
  /-- A family of maps from `left a` to `right (J.snd a)` -/
  snd : forall a, left a ⟶ right (J.snd a)

namespace MulticospanIndex

variable {C : Type u} [Category.{v} C] {J : MulticospanShape.{w, w'}}
  (I : MulticospanIndex J C)

/--
Definition of `multicospan` / `multicospan` 的定义

English:
definition multicospan
  signature: : WalkingMulticospan J ⥤ C where
  body: match x with
    | WalkingMulticospan.left a => I.left a
    | WalkingMulticospan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMulticospan.Hom.id x => 𝟙 _
    | _, _, WalkingMulticospan.Hom.fst b => I.fst _
    | _, _, WalkingMulticospan.Hom.snd b => I.snd _
  map_

中文:
定义 multicospan
  签名: : WalkingMulticospan J ⥤ C where
  定义体: match x with
    | WalkingMulticospan.left a => I.left a
    | WalkingMulticospan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMulticospan.Hom.id x => 𝟙 _
    | _, _, WalkingMulticospan.Hom.fst b => I.fst _
    | _, _, WalkingMulticospan.Hom.snd b => I.snd _
  map_

Depends on / 依赖: I.fst, I.left, I.right, I.snd, WalkingMulticospan, WalkingMulticospan.Hom.fst, WalkingMulticospan.Hom.id, WalkingMulticospan.Hom.snd, WalkingMulticospan.left, WalkingMulticospan.right, cat_disch, map_comp, map_id
-/
def multicospan : WalkingMulticospan J ⥤ C where
  obj x :=
    match x with
    | WalkingMulticospan.left a => I.left a
    | WalkingMulticospan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMulticospan.Hom.id x => 𝟙 _
    | _, _, WalkingMulticospan.Hom.fst b => I.fst _
    | _, _, WalkingMulticospan.Hom.snd b => I.snd _
  map_id := by
    rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> cat_disch

@[simp]
/--
theorem `multicospan_obj_left` / 定理 `multicospan_obj_left`

English:
theorem multicospan_obj_left
  given: (a)
  statement: I.multicospan.obj (WalkingMulticospan.left a) = I.left a
  proof: rfl

@[simp]

中文:
定理 multicospan_obj_left
  条件: (a)
  结论: I.multicospan.obj (WalkingMulticospan.left a) = I.left a
  证明: rfl

@[simp]
-/
theorem multicospan_obj_left (a) : I.multicospan.obj (WalkingMulticospan.left a) = I.left a :=
  rfl

@[simp]
/--
theorem `multicospan_obj_right` / 定理 `multicospan_obj_right`

English:
theorem multicospan_obj_right
  given: (b)
  statement: I.multicospan.obj (WalkingMulticospan.right b) = I.right b
  proof: rfl

@[simp]

中文:
定理 multicospan_obj_right
  条件: (b)
  结论: I.multicospan.obj (WalkingMulticospan.right b) = I.right b
  证明: rfl

@[simp]
-/
theorem multicospan_obj_right (b) : I.multicospan.obj (WalkingMulticospan.right b) = I.right b :=
  rfl

@[simp]
/--
theorem `multicospan_map_fst` / 定理 `multicospan_map_fst`

English:
theorem multicospan_map_fst
  given: (a)
  statement: I.multicospan.map (WalkingMulticospan.Hom.fst a) = I.fst a
  proof: rfl

@[simp]

中文:
定理 multicospan_map_fst
  条件: (a)
  结论: I.multicospan.map (WalkingMulticospan.态射.fst a) = I.fst a
  证明: rfl

@[simp]
-/
theorem multicospan_map_fst (a) : I.multicospan.map (WalkingMulticospan.Hom.fst a) = I.fst a :=
  rfl

@[simp]
/--
theorem `multicospan_map_snd` / 定理 `multicospan_map_snd`

English:
theorem multicospan_map_snd
  given: (a)
  statement: I.multicospan.map (WalkingMulticospan.Hom.snd a) = I.snd a
  proof: rfl

中文:
定理 multicospan_map_snd
  条件: (a)
  结论: I.multicospan.map (WalkingMulticospan.态射.snd a) = I.snd a
  证明: rfl
-/
theorem multicospan_map_snd (a) : I.multicospan.map (WalkingMulticospan.Hom.snd a) = I.snd a :=
  rfl

/--
Definition of `fstPiMapOfIsLimit` / `fstPiMapOfIsLimit` 的定义

English:
definition fstPiMapOfIsLimit
  signature: (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d)
  body: Fan.IsLimit.lift hd fun i => c.proj _ ≫ I.fst i

中文:
定义 fstPiMapOfIsLimit
  签名: (c : Fan I.left) {d : Fan I.right} (hd : 是极限 d)
  定义体: Fan.IsLimit.lift hd fun i => c.proj _ ≫ I.fst i

Depends on / 依赖: Fan.IsLimit.lift, I.fst, IsLimit, c.proj
-/
def fstPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.pt ⟶ d.pt :=
  Fan.IsLimit.lift hd fun i => c.proj _ ≫ I.fst i

/--
Definition of `sndPiMapOfIsLimit` / `sndPiMapOfIsLimit` 的定义

English:
definition sndPiMapOfIsLimit
  signature: (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d)
  body: Fan.IsLimit.lift hd fun i => c.proj _ ≫ I.snd i

@[reassoc (attr := simp)]

中文:
定义 sndPiMapOfIsLimit
  签名: (c : Fan I.left) {d : Fan I.right} (hd : 是极限 d)
  定义体: Fan.IsLimit.lift hd fun i => c.proj _ ≫ I.snd i

@[reassoc (attr := simp)]

Depends on / 依赖: Fan.IsLimit.lift, I.snd, IsLimit, c.proj
-/
def sndPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.pt ⟶ d.pt :=
  Fan.IsLimit.lift hd fun i => c.proj _ ≫ I.snd i

@[reassoc (attr := simp)]
/--
lemma `fstPiMapOfIsLimit_proj` / 引理 `fstPiMapOfIsLimit_proj`

English:
lemma fstPiMapOfIsLimit_proj
  given: (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i)
  proof: by
  simp [fstPiMapOfIsLimit]

@[reassoc (attr := simp)]

中文:
引理 fstPiMapOfIsLimit_proj
  条件: (c : Fan I.left) {d : Fan I.right} (hd : 是极限 d) (i)
  证明: by
  simp [fstPiMapOfIsLimit]

@[reassoc (attr := simp)]

Depends on / 依赖: fstPiMapOfIsLimit
-/
lemma fstPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) :
    fstPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.fst i := by
  simp [fstPiMapOfIsLimit]

@[reassoc (attr := simp)]
/--
lemma `sndPiMapOfIsLimit_proj` / 引理 `sndPiMapOfIsLimit_proj`

English:
lemma sndPiMapOfIsLimit_proj
  given: (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i)
  proof: by
  simp [sndPiMapOfIsLimit]

中文:
引理 sndPiMapOfIsLimit_proj
  条件: (c : Fan I.left) {d : Fan I.right} (hd : 是极限 d) (i)
  证明: by
  simp [sndPiMapOfIsLimit]

Depends on / 依赖: exponentialIdeal_of_preservesBinaryProducts, sndPiMapOfIsLimit
-/
lemma sndPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) :
    sndPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.snd i := by
  simp [sndPiMapOfIsLimit]

/-- Taking the multiequalizer over the multicospan index is equivalent to taking the equalizer over
the two morphisms `∏ᶜ I.left ⇉ ∏ᶜ I.right`. This is the diagram of the latter for limiting fans.
-/
@[simps!]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def parallelPairDiagramOfIsLimit
  body: parallelPair (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)

中文:
定义 noncomputable
  签名: def parallelPairDiagramOfIsLimit
  定义体: parallelPair (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)
-/
protected noncomputable def parallelPairDiagramOfIsLimit
    (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : WalkingParallelPair ⥤ C :=
  parallelPair (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)

variable [HasProduct I.left] [HasProduct I.right]

/--
Definition of `fstPiMap` / `fstPiMap` 的定义

English:
definition fstPiMap
  signature: : ∏ᶜ I.left ⟶ ∏ᶜ I.right
  body: I.fstPiMapOfIsLimit _ limit.isLimit (Discrete.functor I.right)

中文:
定义 fstPiMap
  签名: : ∏ᶜ I.left ⟶ ∏ᶜ I.right
  定义体: I.fstPiMapOfIsLimit _ limit.isLimit (Discrete.functor I.right)

Depends on / 依赖: Discrete, Discrete.functor, I.fstPiMapOfIsLimit, I.right, fstPiMapOfIsLimit, functor, isLimit, limit.isLimit
-/
noncomputable def fstPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
I.fstPiMapOfIsLimit _ limit.isLimit (Discrete.functor I.right)

/--
Definition of `sndPiMap` / `sndPiMap` 的定义

English:
definition sndPiMap
  signature: : ∏ᶜ I.left ⟶ ∏ᶜ I.right
  body: I.sndPiMapOfIsLimit _ limit.isLimit (Discrete.functor I.right)

@[reassoc (attr := simp)]

中文:
定义 sndPiMap
  签名: : ∏ᶜ I.left ⟶ ∏ᶜ I.right
  定义体: I.sndPiMapOfIsLimit _ limit.isLimit (Discrete.functor I.right)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.functor, I.right, I.sndPiMapOfIsLimit, functor, isLimit, limit.isLimit, sndPiMapOfIsLimit
-/
noncomputable def sndPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
I.sndPiMapOfIsLimit _ limit.isLimit (Discrete.functor I.right)

@[reassoc (attr := simp)]
/--
theorem `fstPiMap_π` / 定理 `fstPiMap_π`

English:
theorem fstPiMap_π
  given: (b)
  statement: I.fstPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.fst b
  proof: fstPiMapOfIsLimit_proj ..

@[reassoc (attr := simp)]

中文:
定理 fstPiMap_π
  条件: (b)
  结论: I.fstPiMap ≫ 依赖函数类型.π I.right b = 依赖函数类型.π I.left _ ≫ I.fst b
  证明: fstPiMapOfIsLimit_proj ..

@[reassoc (attr := simp)]

Depends on / 依赖: fstPiMapOfIsLimit_proj
-/
theorem fstPiMap_π (b) : I.fstPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.fst b :=
  fstPiMapOfIsLimit_proj ..

@[reassoc (attr := simp)]
/--
theorem `sndPiMap_π` / 定理 `sndPiMap_π`

English:
theorem sndPiMap_π
  given: (b)
  statement: I.sndPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.snd b
  proof: sndPiMapOfIsLimit_proj ..

中文:
定理 sndPiMap_π
  条件: (b)
  结论: I.sndPiMap ≫ 依赖函数类型.π I.right b = 依赖函数类型.π I.left _ ≫ I.snd b
  证明: sndPiMapOfIsLimit_proj ..

Depends on / 依赖: sndPiMapOfIsLimit_proj
-/
theorem sndPiMap_π (b) : I.sndPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.snd b :=
  sndPiMapOfIsLimit_proj ..

/-- Taking the multiequalizer over the multicospan index is equivalent to taking the equalizer over
the two morphisms `∏ᶜ I.left ⇉ ∏ᶜ I.right`. This is the diagram of the latter.
-/
@[simps!]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def parallelPairDiagram
  body: parallelPair I.fstPiMap I.sndPiMap

中文:
定义 noncomputable
  签名: def parallelPairDiagram
  定义体: parallelPair I.fstPiMap I.sndPiMap
-/
protected noncomputable def parallelPairDiagram :=
  parallelPair I.fstPiMap I.sndPiMap

end MulticospanIndex

namespace MultispanIndex

variable {C : Type u} [Category.{v} C] {J : MultispanShape.{w, w'}}
    (I : MultispanIndex J C)

/--
Definition of `multispan` / `multispan` 的定义

English:
definition multispan
  signature: : WalkingMultispan J ⥤ C where
  body: match x with
    | WalkingMultispan.left a => I.left a
    | WalkingMultispan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMultispan.Hom.id x => 𝟙 _
    | _, _, WalkingMultispan.Hom.fst b => I.fst _
    | _, _, WalkingMultispan.Hom.snd b => I.snd _
  map_id := by
 

中文:
定义 multispan
  签名: : WalkingMultispan J ⥤ C where
  定义体: match x with
    | WalkingMultispan.left a => I.left a
    | WalkingMultispan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMultispan.Hom.id x => 𝟙 _
    | _, _, WalkingMultispan.Hom.fst b => I.fst _
    | _, _, WalkingMultispan.Hom.snd b => I.snd _
  map_id := by
 

Depends on / 依赖: I.fst, I.left, I.right, I.snd, WalkingMultispan, WalkingMultispan.Hom.fst, WalkingMultispan.Hom.id, WalkingMultispan.Hom.snd, WalkingMultispan.left, WalkingMultispan.right, cat_disch, map_comp, map_id
-/
def multispan : WalkingMultispan J ⥤ C where
  obj x :=
    match x with
    | WalkingMultispan.left a => I.left a
    | WalkingMultispan.right b => I.right b
  map {x y} f :=
    match x, y, f with
    | _, _, WalkingMultispan.Hom.id x => 𝟙 _
    | _, _, WalkingMultispan.Hom.fst b => I.fst _
    | _, _, WalkingMultispan.Hom.snd b => I.snd _
  map_id := by
    rintro (_ | _) <;> rfl
  map_comp := by
    rintro (_ | _) (_ | _) (_ | _) (_ | _ | _) (_ | _ | _) <;> cat_disch

@[simp]
/--
theorem `multispan_obj_left` / 定理 `multispan_obj_left`

English:
theorem multispan_obj_left
  given: (a)
  statement: I.multispan.obj (WalkingMultispan.left a) = I.left a
  proof: rfl

@[simp]

中文:
定理 multispan_obj_left
  条件: (a)
  结论: I.multispan.obj (WalkingMultispan.left a) = I.left a
  证明: rfl

@[simp]
-/
theorem multispan_obj_left (a) : I.multispan.obj (WalkingMultispan.left a) = I.left a :=
  rfl

@[simp]
/--
theorem `multispan_obj_right` / 定理 `multispan_obj_right`

English:
theorem multispan_obj_right
  given: (b)
  statement: I.multispan.obj (WalkingMultispan.right b) = I.right b
  proof: rfl

@[simp]

中文:
定理 multispan_obj_right
  条件: (b)
  结论: I.multispan.obj (WalkingMultispan.right b) = I.right b
  证明: rfl

@[simp]
-/
theorem multispan_obj_right (b) : I.multispan.obj (WalkingMultispan.right b) = I.right b :=
  rfl

@[simp]
/--
theorem `multispan_map_fst` / 定理 `multispan_map_fst`

English:
theorem multispan_map_fst
  given: (a)
  statement: I.multispan.map (WalkingMultispan.Hom.fst a) = I.fst a
  proof: rfl

@[simp]

中文:
定理 multispan_map_fst
  条件: (a)
  结论: I.multispan.map (WalkingMultispan.态射.fst a) = I.fst a
  证明: rfl

@[simp]
-/
theorem multispan_map_fst (a) : I.multispan.map (WalkingMultispan.Hom.fst a) = I.fst a :=
  rfl

@[simp]
/--
theorem `multispan_map_snd` / 定理 `multispan_map_snd`

English:
theorem multispan_map_snd
  given: (a)
  statement: I.multispan.map (WalkingMultispan.Hom.snd a) = I.snd a
  proof: rfl

中文:
定理 multispan_map_snd
  条件: (a)
  结论: I.multispan.map (WalkingMultispan.态射.snd a) = I.snd a
  证明: rfl
-/
theorem multispan_map_snd (a) : I.multispan.map (WalkingMultispan.Hom.snd a) = I.snd a :=
  rfl

/--
Definition of `fstSigmaMapOfIsColimit` / `fstSigmaMapOfIsColimit` 的定义

English:
definition fstSigmaMapOfIsColimit
  signature: {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c)
  body: Cofan.IsColimit.desc hc fun i => I.fst i ≫ d.inj _

中文:
定义 fstSigmaMapOfIsColimit
  签名: {c : Cofan I.left} (d : Cofan I.right) (hc : 是余极限 c)
  定义体: Cofan.IsColimit.desc hc fun i => I.fst i ≫ d.inj _

Depends on / 依赖: Cofan.IsColimit.desc, I.fst, IsColimit, d.inj
-/
def fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) :
    c.pt ⟶ d.pt :=
  Cofan.IsColimit.desc hc fun i => I.fst i ≫ d.inj _

/--
Definition of `sndSigmaMapOfIsColimit` / `sndSigmaMapOfIsColimit` 的定义

English:
definition sndSigmaMapOfIsColimit
  signature: {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c)
  body: Cofan.IsColimit.desc hc fun i => I.snd i ≫ d.inj _

@[reassoc (attr := simp)]

中文:
定义 sndSigmaMapOfIsColimit
  签名: {c : Cofan I.left} (d : Cofan I.right) (hc : 是余极限 c)
  定义体: Cofan.IsColimit.desc hc fun i => I.snd i ≫ d.inj _

@[reassoc (attr := simp)]

Depends on / 依赖: Cofan.IsColimit.desc, I.snd, IsColimit, d.inj
-/
def sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) :
    c.pt ⟶ d.pt :=
  Cofan.IsColimit.desc hc fun i => I.snd i ≫ d.inj _

@[reassoc (attr := simp)]
/--
lemma `inj_fstSigmaMapOfIsColimit` / 引理 `inj_fstSigmaMapOfIsColimit`

English:
lemma inj_fstSigmaMapOfIsColimit
  given: {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i)
  proof: by
  simp [fstSigmaMapOfIsColimit]

@[reassoc (attr := simp)]

中文:
引理 inj_fstSigmaMapOfIsColimit
  条件: {c : Cofan I.left} (d : Cofan I.right) (hc : 是余极限 c) (i)
  证明: by
  simp [fstSigmaMapOfIsColimit]

@[reassoc (attr := simp)]

Depends on / 依赖: fstSigmaMapOfIsColimit
-/
lemma inj_fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i) :
    c.inj _ ≫ fstSigmaMapOfIsColimit I d hc = I.fst i ≫ d.inj _ := by
  simp [fstSigmaMapOfIsColimit]

@[reassoc (attr := simp)]
/--
lemma `inj_sndSigmaMapOfIsColimit` / 引理 `inj_sndSigmaMapOfIsColimit`

English:
lemma inj_sndSigmaMapOfIsColimit
  given: {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i)
  proof: by
  simp [sndSigmaMapOfIsColimit]

中文:
引理 inj_sndSigmaMapOfIsColimit
  条件: {c : Cofan I.left} (d : Cofan I.right) (hc : 是余极限 c) (i)
  证明: by
  simp [sndSigmaMapOfIsColimit]

Depends on / 依赖: sndSigmaMapOfIsColimit
-/
lemma inj_sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i) :
    c.inj _ ≫ sndSigmaMapOfIsColimit I d hc = I.snd i ≫ d.inj _ := by
  simp [sndSigmaMapOfIsColimit]

/-- Taking the multicoequalizer over the multispan index is equivalent to taking the coequalizer
over the two morphisms `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter for colimiting
cofans. -/
@[simps!]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def parallelPairDiagramOfIsColimit
  body: parallelPair (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)

中文:
定义 noncomputable
  签名: def parallelPairDiagramOfIsColimit
  定义体: parallelPair (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)
-/
protected noncomputable def parallelPairDiagramOfIsColimit
    {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) : WalkingParallelPair ⥤ C :=
  parallelPair (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)

variable [HasCoproduct I.left] [HasCoproduct I.right]

/--
Definition of `fstSigmaMap` / `fstSigmaMap` 的定义

English:
definition fstSigmaMap
  signature: : ∐ I.left ⟶ ∐ I.right
  body: I.fstSigmaMapOfIsColimit _ colimit.isColimit _

中文:
定义 fstSigmaMap
  签名: : ∐ I.left ⟶ ∐ I.right
  定义体: I.fstSigmaMapOfIsColimit _ colimit.isColimit _

Depends on / 依赖: I.fstSigmaMapOfIsColimit, MonoidalClosed, MonoidalClosed.ofEquiv, colimit, colimit.isColimit, equivalenceTransported, fstSigmaMapOfIsColimit, isColimit, ofEquiv, symm.toAdjunction, toAdjunction
-/
noncomputable def fstSigmaMap : ∐ I.left ⟶ ∐ I.right :=
I.fstSigmaMapOfIsColimit _ colimit.isColimit _

/--
Definition of `sndSigmaMap` / `sndSigmaMap` 的定义

English:
definition sndSigmaMap
  signature: : ∐ I.left ⟶ ∐ I.right
  body: I.sndSigmaMapOfIsColimit _ colimit.isColimit _

@[reassoc (attr := simp)]

中文:
定义 sndSigmaMap
  签名: : ∐ I.left ⟶ ∐ I.right
  定义体: I.sndSigmaMapOfIsColimit _ colimit.isColimit _

@[reassoc (attr := simp)]

Depends on / 依赖: I.sndSigmaMapOfIsColimit, colimit, colimit.isColimit, isColimit, sndSigmaMapOfIsColimit
-/
noncomputable def sndSigmaMap : ∐ I.left ⟶ ∐ I.right :=
I.sndSigmaMapOfIsColimit _ colimit.isColimit _

@[reassoc (attr := simp)]
/--
theorem `ι_fstSigmaMap` / 定理 `ι_fstSigmaMap`

English:
theorem ι_fstSigmaMap
  given: (b)
  statement: Sigma.ι I.left b ≫ I.fstSigmaMap = I.fst b ≫ Sigma.ι I.right _
  proof: inj_fstSigmaMapOfIsColimit ..

@[reassoc (attr := simp)]

中文:
定理 ι_fstSigmaMap
  条件: (b)
  结论: 依赖和类型.ι I.left b ≫ I.fstSigmaMap = I.fst b ≫ 依赖和类型.ι I.right _
  证明: inj_fstSigmaMapOfIsColimit ..

@[reassoc (attr := simp)]

Depends on / 依赖: Types.tensorProductAdjunction, inj_fstSigmaMapOfIsColimit, tensorProductAdjunction
-/
theorem ι_fstSigmaMap (b) : Sigma.ι I.left b ≫ I.fstSigmaMap = I.fst b ≫ Sigma.ι I.right _ :=
  inj_fstSigmaMapOfIsColimit ..

@[reassoc (attr := simp)]
/--
theorem `ι_sndSigmaMap` / 定理 `ι_sndSigmaMap`

English:
theorem ι_sndSigmaMap
  given: (b)
  statement: Sigma.ι I.left b ≫ I.sndSigmaMap = I.snd b ≫ Sigma.ι I.right _
  proof: inj_sndSigmaMapOfIsColimit ..

中文:
定理 ι_sndSigmaMap
  条件: (b)
  结论: 依赖和类型.ι I.left b ≫ I.sndSigmaMap = I.snd b ≫ 依赖和类型.ι I.right _
  证明: inj_sndSigmaMapOfIsColimit ..

Depends on / 依赖: inj_sndSigmaMapOfIsColimit
-/
theorem ι_sndSigmaMap (b) : Sigma.ι I.left b ≫ I.sndSigmaMap = I.snd b ≫ Sigma.ι I.right _ :=
  inj_sndSigmaMapOfIsColimit ..

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev parallelPairDiagram
  body: parallelPair I.fstSigmaMap I.sndSigmaMap

中文:
缩写 noncomputable
  签名: abbrev parallelPairDiagram
  定义体: parallelPair I.fstSigmaMap I.sndSigmaMap

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, Closed, Closed.mk, MonoidalClosed, MonoidalClosed.mk, PreservesColimits, Presheaf, Presheaf.isLeftAdjoint_of_preservesColimits, infer_instance, isLeftAdjoint_of_preservesColimits, ofIsLeftAdjoint, tensorLeft
-/
protected noncomputable abbrev parallelPairDiagram :=
  parallelPair I.fstSigmaMap I.sndSigmaMap

end MultispanIndex

variable {C : Type u} [Category.{v} C]

/--
Definition of `Multifork` / `Multifork` 的定义

English:
abbreviation Multifork
  signature: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  body: Cone I.multicospan

中文:
缩写 Multifork
  签名: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  定义体: Cone I.multicospan

Depends on / 依赖: I.multicospan, multicospan
-/
abbrev Multifork {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :=
  Cone I.multicospan

/--
Definition of `Multicofork` / `Multicofork` 的定义

English:
abbreviation Multicofork
  signature: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  body: Cocone I.multispan

中文:
缩写 Multicofork
  签名: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  定义体: Cocone I.multispan

Depends on / 依赖: Cocone, I.multispan, cartesianClosedFunctorToTypes, multispan
-/
abbrev Multicofork {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) :=
  Cocone I.multispan

namespace Multifork

variable {J : MulticospanShape.{w, w'}} {I : MulticospanIndex J C} (K : Multifork I)

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: (a : J.L)
  body: K.π.app (WalkingMulticospan.left _)

@[simp]

中文:
定义 ι
  签名: (a : J.L)
  定义体: K.π.app (WalkingMulticospan.left _)

@[simp]

Depends on / 依赖: Functor, Functor.asEquivalence, Functor.whiskeringLeft, SmallModel, WalkingMulticospan, WalkingMulticospan.left, asEquivalence, cartesianClosedOfEquiv, equivSmallModel, functor, whiskeringLeft
-/
def ι (a : J.L) : K.pt ⟶ I.left a :=
  K.π.app (WalkingMulticospan.left _)

@[simp]
/--
theorem `app_left_eq_ι` / 定理 `app_left_eq_ι`

English:
theorem app_left_eq_ι
  given: (a)
  statement: K.π.app (WalkingMulticospan.left a) = K.ι a
  proof: rfl

@[simp]

中文:
定理 app_left_eq_ι
  条件: (a)
  结论: K.π.app (WalkingMulticospan.left a) = K.ι a
  证明: rfl

@[simp]
-/
theorem app_left_eq_ι (a) : K.π.app (WalkingMulticospan.left a) = K.ι a :=
  rfl

@[simp]
/--
theorem `app_right_eq_ι_comp_fst` / 定理 `app_right_eq_ι_comp_fst`

English:
theorem app_right_eq_ι_comp_fst
  given: (b)
  proof: by
  rw [← K.w (WalkingMulticospan.Hom.fst b)]
  rfl

@[reassoc]

中文:
定理 app_right_eq_ι_comp_fst
  条件: (b)
  证明: by
  rw [← K.w (WalkingMulticospan.Hom.fst b)]
  rfl

@[reassoc]

Depends on / 依赖: WalkingMulticospan, WalkingMulticospan.Hom.fst
-/
theorem app_right_eq_ι_comp_fst (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (J.fst b) ≫ I.fst b := by
  rw [← K.w (WalkingMulticospan.Hom.fst b)]
  rfl

@[reassoc]
/--
theorem `app_right_eq_ι_comp_snd` / 定理 `app_right_eq_ι_comp_snd`

English:
theorem app_right_eq_ι_comp_snd
  given: (b)
  proof: by
  rw [← K.w (WalkingMulticospan.Hom.snd b)]
  rfl

@[reassoc (attr := simp)]

中文:
定理 app_right_eq_ι_comp_snd
  条件: (b)
  证明: by
  rw [← K.w (WalkingMulticospan.Hom.snd b)]
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: WalkingMulticospan, WalkingMulticospan.Hom.snd
-/
theorem app_right_eq_ι_comp_snd (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (J.snd b) ≫ I.snd b := by
  rw [← K.w (WalkingMulticospan.Hom.snd b)]
  rfl

@[reassoc (attr := simp)]
/--
theorem `hom_comp_ι` / 定理 `hom_comp_ι`

English:
theorem hom_comp_ι
  given: (K₁ K₂ : Multifork I) (f : K₁ ⟶ K₂) (j : J.L)
  statement: f.hom ≫ K₂.ι j = K₁.ι j
  proof: f.w _

中文:
定理 hom_comp_ι
  条件: (K₁ K₂ : Multifork I) (f : K₁ ⟶ K₂) (j : J.L)
  结论: f.hom ≫ K₂.ι j = K₁.ι j
  证明: f.w _
-/
theorem hom_comp_ι (K₁ K₂ : Multifork I) (f : K₁ ⟶ K₂) (j : J.L) : f.hom ≫ K₂.ι j = K₁.ι j :=
  f.w _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct a multifork using a collection `ι` of morphisms. -/
@[simps]
/--
Definition of `ofι` / `ofι` 的定义

English:
definition ofι
  signature: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  body: P
  π :=
    { app := fun x =>
        match x with
        | WalkingMulticospan.left _ => ι _
        | WalkingMulticospan.right b => ι (J.fst b) ≫ I.fst b
      naturality := by
        #adaptation_note /-- Proof repaired after leanprover/lean4#13363.
        The proof used to finish from this poi

中文:
定义 ofι
  签名: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  定义体: P
  π :=
    { app := fun x =>
        match x with
        | WalkingMulticospan.left _ => ι _
        | WalkingMulticospan.right b => ι (J.fst b) ≫ I.fst b
      naturality := by
        #adaptation_note /-- Proof repaired after leanprover/lean4#13363.
        The proof used to finish from this poi
-/
def ofι {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    (P : C) (ι : forall a, P ⟶ I.left a)
    (w : forall b, ι (J.fst b) ≫ I.fst b = ι (J.snd b) ≫ I.snd b) : Multifork I where
  pt := P
  π :=
    { app := fun x =>
        match x with
        | WalkingMulticospan.left _ => ι _
        | WalkingMulticospan.right b => ι (J.fst b) ≫ I.fst b
      naturality := by
        #adaptation_note /-- Proof repaired after leanprover/lean4#13363.
        The proof used to finish from this point as
        ```
        rintro (_ | _) (_ | _) (_ | _ | _) <;>
          dsimp <;> simp only [Category.id_comp, Category.comp_id]
        apply w
        ```
        The replacement proof is a short-term fix, and we request that the authors/maintainers of
        this file review the proof, and either approve it by removing this note,
        revise the proof or the prerequisites appropriately, or minimize a problem in lean4 that
        still needs addressing. -/
        rintro (_ | _) (_ | _) (_ | _ | _) <;>
          simp only [WalkingMulticospan.Hom.id_eq_id,
            Functor.map_id, Functor.const_obj_map, Category.comp_id] <;>
          dsimp <;> simp only [Category.id_comp]
        apply w }

@[simp]
/--
lemma `ι_ofι` / 引理 `ι_ofι`

English:
lemma ι_ofι
  statement: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι_ofι
  结论: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι_ofι {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    (P : C) (ι : forall a, P ⟶ I.left a)
    (w : forall b, ι (J.fst b) ≫ I.fst b = ι (J.snd b) ≫ I.snd b) (i) :
    (ofι I P ι w).ι i = ι i :=
  rfl

@[reassoc (attr := simp)]
/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: (b)
  statement: K.ι (J.fst b) ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b
  proof: by
  rw [← app_right_eq_ι_comp_fst]; rw [← app_right_eq_ι_comp_snd]

中文:
定理 condition
  条件: (b)
  结论: K.ι (J.fst b) ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b
  证明: by
  rw [← app_right_eq_ι_comp_fst]; rw [← app_right_eq_ι_comp_snd]
-/
theorem condition (b) : K.ι (J.fst b) ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b := by
  rw [← app_right_eq_ι_comp_fst]; rw [← app_right_eq_ι_comp_snd]

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for isomorphisms between multiforks. -/
@[simps!]
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {t s : Multifork I} (e : t.pt ≅ s.pt)
  body: Cone.ext e (by rintro (i | j) <;> simp [← h])

中文:
定义 ext
  签名: {t s : Multifork I} (e : t.pt ≅ s.pt)
  定义体: Cone.ext e (by rintro (i | j) <;> simp [← h])

Depends on / 依赖: Cone.ext, cat_disch
-/
def ext {t s : Multifork I} (e : t.pt ≅ s.pt)
    (h : forall i : J.L, e.hom ≫ s.ι i = t.ι i := by cat_disch) : t ≅ s :=
  Cone.ext e (by rintro (i | j) <;> simp [← h])

set_option backward.defeqAttrib.useBackward true in
/-- Every multifork is isomorphic to one of the form `Multifork.ofι`. -/
@[simps!]
/--
Definition of `isoOfι` / `isoOfι` 的定义

English:
definition isoOfι
  signature: (t : Multifork I)
  body: ext (Iso.refl _)

中文:
定义 isoOfι
  签名: (t : Multifork I)
  定义体: ext (Iso.refl _)

Depends on / 依赖: Iso.refl
-/
def isoOfι (t : Multifork I) : t ≅ ofι _ t.pt t.ι t.condition :=
  ext (Iso.refl _)

/-- This definition provides a convenient way to show that a multifork is a limit. -/
@[simps]
/--
Definition of `IsLimit.mk` / `IsLimit.mk` 的定义

English:
definition IsLimit.mk
  signature: (lift : forall E : Multifork I, E.pt ⟶ K.pt)
  body: { lift
    fac := by
      rintro E (a | b)
      · apply fac
      · rw [← E.w (WalkingMulticospan.Hom.fst b), ← K.w (WalkingMulticospan.Hom.fst b), ←
          Category.assoc]
        congr 1
        apply fac
    uniq := by
      rintro E m hm
      apply uniq
      intro i
      apply hm }

中文:
定义 是极限.mk
  签名: (lift : 对任意 E : Multifork I, E.pt ⟶ K.pt)
  定义体: { lift
    fac := by
      rintro E (a | b)
      · apply fac
      · rw [← E.w (WalkingMulticospan.Hom.fst b), ← K.w (WalkingMulticospan.Hom.fst b), ←
          Category.assoc]
        congr 1
        apply fac
    uniq := by
      rintro E m hm
      apply uniq
      intro i
      apply hm }

Depends on / 依赖: Category, Category.assoc, WalkingMulticospan, WalkingMulticospan.Hom.fst
-/
def IsLimit.mk (lift : forall E : Multifork I, E.pt ⟶ K.pt)
    (fac : forall (E : Multifork I) (i : J.L), lift E ≫ K.ι i = E.ι i)
    (uniq : forall (E : Multifork I) (m : E.pt ⟶ K.pt), (forall i : J.L, m ≫ K.ι i = E.ι i) -> m = lift E) :
    IsLimit K :=
  { lift
    fac := by
      rintro E (a | b)
      · apply fac
      · rw [← E.w (WalkingMulticospan.Hom.fst b), ← K.w (WalkingMulticospan.Hom.fst b), ←
          Category.assoc]
        congr 1
        apply fac
    uniq := by
      rintro E m hm
      apply uniq
      intro i
      apply hm }

variable {K}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsLimit.hom_ext` / 引理 `IsLimit.hom_ext`

English:
lemma IsLimit.hom_ext
  statement: (hK : IsLimit K) {T : C} {f g : T ⟶ K.pt}
  proof: by
  apply hK.hom_ext
  rintro (_ | b)
  · apply h
  · dsimp
    rw [app_right_eq_ι_comp_fst]; rw [reassoc_of% h]

中文:
引理 是极限.hom_ext
  结论: (hK : 是极限 K) {T : C} {f g : T ⟶ K.pt}
  证明: by
  apply hK.hom_ext
  rintro (_ | b)
  · apply h
  · dsimp
    rw [app_right_eq_ι_comp_fst]; rw [reassoc_of% h]

Depends on / 依赖: hK.hom_ext, hom_ext, reassoc_of
-/
lemma IsLimit.hom_ext (hK : IsLimit K) {T : C} {f g : T ⟶ K.pt}
    (h : forall a, f ≫ K.ι a = g ≫ K.ι a) : f = g := by
  apply hK.hom_ext
  rintro (_ | b)
  · apply h
  · dsimp
    rw [app_right_eq_ι_comp_fst]; rw [reassoc_of% h]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `IsLimit.lift` / `IsLimit.lift` 的定义

English:
definition IsLimit.lift
  signature: (hK : IsLimit K) {T : C} (k : forall a, T ⟶ I.left a)
  body: hK.lift (Multifork.ofι _ _ k hk)

中文:
定义 是极限.lift
  签名: (hK : 是极限 K) {T : C} (k : 对任意 a, T ⟶ I.left a)
  定义体: hK.lift (Multifork.ofι _ _ k hk)

Depends on / 依赖: Multifork, Multifork.of, adjunction, hK.lift, ihom.adjunction, isLeftAdjoint
-/
def IsLimit.lift (hK : IsLimit K) {T : C} (k : forall a, T ⟶ I.left a)
    (hk : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) :
    T ⟶ K.pt :=
  hK.lift (Multifork.ofι _ _ k hk)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `IsLimit.fac` / 引理 `IsLimit.fac`

English:
lemma IsLimit.fac
  statement: (hK : IsLimit K) {T : C} (k : forall a, T ⟶ I.left a)
  proof: hK.fac _ _

中文:
引理 是极限.fac
  结论: (hK : 是极限 K) {T : C} (k : 对任意 a, T ⟶ I.left a)
  证明: hK.fac _ _

Depends on / 依赖: hK.fac
-/
lemma IsLimit.fac (hK : IsLimit K) {T : C} (k : forall a, T ⟶ I.left a)
    (hk : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (a : J.L) :
    IsLimit.lift hK k hk ≫ K.ι a = k a :=
  hK.fac _ _

/--
Definition of `isLimitEquivOfIsos` / `isLimitEquivOfIsos` 的定义

English:
definition isLimitEquivOfIsos
  signature: {I I' : MulticospanIndex J C} (c : Multifork I) (c' : Multifork I')
  body: letI i : I.multicospan ≅ I'.multicospan :=
    WalkingMulticospan.functorExt el er hl hr
  IsLimit.equivOfNatIsoOfIso i _ _ (Multifork.ext e he)

中文:
定义 isLimitEquivOfIsos
  签名: {I I' : MulticospanIndex J C} (c : Multifork I) (c' : Multifork I')
  定义体: letI i : I.multicospan ≅ I'.multicospan :=
    WalkingMulticospan.functorExt el er hl hr
  IsLimit.equivOfNatIsoOfIso i _ _ (Multifork.ext e he)

Depends on / 依赖: I.multicospan, I.snd, IsLimit, IsLimit.equivOfNatIsoOfIso, J.snd, Multifork, Multifork.ext, WalkingMulticospan, WalkingMulticospan.functorExt, cat_disch, e.hom, equivOfNatIsoOfIso, functorExt, multicospan
-/
def isLimitEquivOfIsos {I I' : MulticospanIndex J C} (c : Multifork I) (c' : Multifork I')
    (e : c.pt ≅ c'.pt) (el : forall i, I.left i ≅ I'.left i) (er : forall i, I.right i ≅ I'.right i)
    (hl : forall (i : J.R), I.fst i ≫ (er i).hom = (el (J.fst i)).hom ≫ I'.fst i := by cat_disch)
    (hr : forall (i : J.R), I.snd i ≫ (er i).hom = (el (J.snd i)).hom ≫ I'.snd i := by cat_disch)
    (he : forall (i : J.L), e.hom ≫ c'.ι i = c.ι i ≫ (el i).hom := by cat_disch) :
    IsLimit c ≃ IsLimit c' :=
  letI i : I.multicospan ≅ I'.multicospan :=
    WalkingMulticospan.functorExt el er hl hr
  IsLimit.equivOfNatIsoOfIso i _ _ (Multifork.ext e he)

variable (K)
variable {c : Fan I.left} (hc : IsLimit c) {d : Fan I.right} (hd : IsLimit d)

@[reassoc (attr := simp)]
/--
theorem `pi_condition` / 定理 `pi_condition`

English:
theorem pi_condition
  proof: by
  apply Fan.IsLimit.hom_ext hd
  simp

中文:
定理 pi_condition
  证明: by
  apply Fan.IsLimit.hom_ext hd
  simp

Depends on / 依赖: Fan.IsLimit.hom_ext, IsLimit, hom_ext
-/
theorem pi_condition :
    Fan.IsLimit.lift hc K.ι ≫ I.fstPiMapOfIsLimit c hd =
      Fan.IsLimit.lift hc K.ι ≫ I.sndPiMapOfIsLimit c hd := by
  apply Fan.IsLimit.hom_ext hd
  simp

/-- Given a multifork, we may obtain a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`. -/
@[simps! pt]
/--
Definition of `toPiFork` / `toPiFork` 的定义

English:
definition toPiFork
  signature: (K : Multifork I)
  body: .ofι (Fan.IsLimit.lift hc K.ι) (by simp)

@[simp]

中文:
定义 toPiFork
  签名: (K : Multifork I)
  定义体: .ofι (Fan.IsLimit.lift hc K.ι) (by simp)

@[simp]

Depends on / 依赖: Fan.IsLimit.lift, IsLimit
-/
def toPiFork (K : Multifork I) :
    Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) :=
  .ofι (Fan.IsLimit.lift hc K.ι) (by simp)

@[simp]
/--
theorem `toPiFork_π_app_zero` / 定理 `toPiFork_π_app_zero`

English:
theorem toPiFork_π_app_zero
  proof: rfl

@[simp]

中文:
定理 toPiFork_π_app_zero
  证明: rfl

@[simp]
-/
theorem toPiFork_π_app_zero :
    (K.toPiFork hc hd).ι = Fan.IsLimit.lift hc K.ι :=
  rfl

@[simp]
/--
theorem `toPiFork_π_app_one` / 定理 `toPiFork_π_app_one`

English:
theorem toPiFork_π_app_one
  proof: rfl

中文:
定理 toPiFork_π_app_one
  证明: rfl
-/
theorem toPiFork_π_app_one :
    (K.toPiFork hc hd).π.app WalkingParallelPair.one =
      Fan.IsLimit.lift hc K.ι ≫ I.fstPiMapOfIsLimit c hd :=
  rfl

set_option backward.defeqAttrib.useBackward true in
variable {hd} in
/-- Given a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`, we may obtain a multifork. -/
@[simps pt]
/--
Definition of `ofPiFork` / `ofPiFork` 的定义

English:
definition ofPiFork
  body: a.pt
  π.app
    | WalkingMulticospan.left _ => a.ι ≫ c.proj _
    | WalkingMulticospan.right _ => a.ι ≫ I.fstPiMapOfIsLimit c hd ≫ d.proj _
  π.naturality := by
    rintro (_ | _) (_ | _) (_ | _ | _)
    · simp
    · simp
    · dsimp; rw [a.condition_assoc]; simp
    · simp

@[simp]

中文:
定义 ofPiFork
  定义体: a.pt
  π.app
    | WalkingMulticospan.left _ => a.ι ≫ c.proj _
    | WalkingMulticospan.right _ => a.ι ≫ I.fstPiMapOfIsLimit c hd ≫ d.proj _
  π.naturality := by
    rintro (_ | _) (_ | _) (_ | _ | _)
    · simp
    · simp
    · dsimp; rw [a.condition_assoc]; simp
    · simp

@[simp]

Depends on / 依赖: a.pt
-/
def ofPiFork
    (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) :
    Multifork I where
  pt := a.pt
  π.app
    | WalkingMulticospan.left _ => a.ι ≫ c.proj _
    | WalkingMulticospan.right _ => a.ι ≫ I.fstPiMapOfIsLimit c hd ≫ d.proj _
  π.naturality := by
    rintro (_ | _) (_ | _) (_ | _ | _)
    · simp
    · simp
    · dsimp; rw [a.condition_assoc]; simp
    · simp

@[simp]
/--
theorem `ofPiFork_ι` / 定理 `ofPiFork_ι`

English:
theorem ofPiFork_ι
  given: (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) (i)
  proof: rfl

@[simp]

中文:
定理 ofPiFork_ι
  条件: (a : 叉 (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) (i)
  证明: rfl

@[simp]
-/
theorem ofPiFork_ι (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) (i) :
    (ofPiFork a).ι i = a.ι ≫ c.proj _ :=
  rfl

@[simp]
/--
theorem `ofPiFork_π_app_right` / 定理 `ofPiFork_π_app_right`

English:
theorem ofPiFork_π_app_right
  proof: rfl

中文:
定理 ofPiFork_π_app_right
  证明: rfl
-/
theorem ofPiFork_π_app_right
    (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) (i) :
    (ofPiFork a).π.app (WalkingMulticospan.right i) =
      a.ι ≫ I.fstPiMapOfIsLimit c hd ≫ d.proj _ :=
  rfl

end Multifork

namespace MulticospanIndex

variable {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
variable {c : Fan I.left} (hc : IsLimit c) {d : Fan I.right} (hd : IsLimit d)

set_option backward.defeqAttrib.useBackward true in
/-- `Multifork.toPiFork` as a functor. -/
@[simps]
/--
Definition of `toPiForkFunctor` / `toPiForkFunctor` 的定义

English:
definition toPiForkFunctor
  signature: :
  body: Multifork.toPiFork hc hd
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by
        rintro (_ | _)
        · apply Fan.IsLimit.hom_ext hc
          simp
        · apply Fan.IsLimit.hom_ext hd
          simp }

中文:
定义 toPiForkFunctor
  签名: :
  定义体: Multifork.toPiFork hc hd
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by
        rintro (_ | _)
        · apply Fan.IsLimit.hom_ext hc
          simp
        · apply Fan.IsLimit.hom_ext hd
          simp }

Depends on / 依赖: Multifork, Multifork.toPiFork, toPiFork
-/
def toPiForkFunctor :
    Multifork I ⥤ Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) where
  obj := Multifork.toPiFork hc hd
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by
        rintro (_ | _)
        · apply Fan.IsLimit.hom_ext hc
          simp
        · apply Fan.IsLimit.hom_ext hd
          simp }

set_option backward.defeqAttrib.useBackward true in
/-- `Multifork.ofPiFork` as a functor. -/
@[simps]
/--
Definition of `ofPiForkFunctor` / `ofPiForkFunctor` 的定义

English:
definition ofPiForkFunctor
  signature: :
  body: Multifork.ofPiFork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

中文:
定义 ofPiForkFunctor
  签名: :
  定义体: Multifork.ofPiFork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

Depends on / 依赖: Multifork, Multifork.ofPiFork, ofPiFork
-/
def ofPiForkFunctor :
    Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) ⥤ Multifork I where
  obj := Multifork.ofPiFork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of multiforks is equivalent to the category of forks over `∏ᶜ I.left ⇉ ∏ᶜ I.right`.
It then follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `reflects`) that it
preserves and reflects limit cones.
-/
@[simps]
/--
Definition of `multiforkEquivPiForkOfIsLimit` / `multiforkEquivPiForkOfIsLimit` 的定义

English:
definition multiforkEquivPiForkOfIsLimit
  signature: :
  body: toPiForkFunctor I hc hd
  inverse := ofPiForkFunctor I hd
  unitIso :=
    NatIso.ofComponents fun K =>
      Cone.ext (Iso.refl _) (by
        rintro (_ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun K =>
Fork.ext (Iso.refl _) Fan.IsLimit.hom_ext hc _ _ (by simp))

中文:
定义 multiforkEquivPiForkOfIsLimit
  签名: :
  定义体: toPiForkFunctor I hc hd
  inverse := ofPiForkFunctor I hd
  unitIso :=
    NatIso.ofComponents fun K =>
      Cone.ext (Iso.refl _) (by
        rintro (_ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun K =>
Fork.ext (Iso.refl _) Fan.IsLimit.hom_ext hc _ _ (by simp))

Depends on / 依赖: toPiForkFunctor
-/
def multiforkEquivPiForkOfIsLimit :
    Multifork I ≌ Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) where
  functor := toPiForkFunctor I hc hd
  inverse := ofPiForkFunctor I hd
  unitIso :=
    NatIso.ofComponents fun K =>
      Cone.ext (Iso.refl _) (by
        rintro (_ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun K =>
Fork.ext (Iso.refl _) Fan.IsLimit.hom_ext hc _ _ (by simp))

variable [HasProduct I.left] [HasProduct I.right]

set_option backward.isDefEq.respectTransparency.types false in
/-- The category of multiforks is equivalent to the category of forks over `∏ᶜ I.left ⇉ ∏ᶜ I.right`.
It then follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `reflects`) that it
preserves and reflects limit cones.
-/
@[simps!]
/--
Definition of `multiforkEquivPiFork` / `multiforkEquivPiFork` 的定义

English:
definition multiforkEquivPiFork
  signature: : Multifork I ≌ Fork I.fstPiMap I.sndPiMap
  body: multiforkEquivPiForkOfIsLimit I (limit.isLimit _) (limit.isLimit _)

中文:
定义 multiforkEquivPiFork
  签名: : Multifork I ≌ 叉 I.fstPiMap I.sndPiMap
  定义体: multiforkEquivPiForkOfIsLimit I (limit.isLimit _) (limit.isLimit _)

Depends on / 依赖: isLimit, limit.isLimit, multiforkEquivPiForkOfIsLimit
-/
noncomputable def multiforkEquivPiFork : Multifork I ≌ Fork I.fstPiMap I.sndPiMap :=
  multiforkEquivPiForkOfIsLimit I (limit.isLimit _) (limit.isLimit _)

/-- The constant `MulticospanShape` for a pair of parallel morphisms. -/
@[simps]
/--
Definition of `ofParallelHoms` / `ofParallelHoms` 的定义

English:
definition ofParallelHoms
  signature: (J : MulticospanShape) {X Y : C} (f g : X ⟶ Y)
  body: X
  right _ := Y
  fst _ := f
  snd _ := g

中文:
定义 ofParallelHoms
  签名: (J : MulticospanShape) {X Y : C} (f g : X ⟶ Y)
  定义体: X
  right _ := Y
  fst _ := f
  snd _ := g
-/
def ofParallelHoms (J : MulticospanShape) {X Y : C} (f g : X ⟶ Y) : MulticospanIndex J C where
  left _ := X
  right _ := Y
  fst _ := f
  snd _ := g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `multiforkOfParallelHomsEquivFork` / `multiforkOfParallelHomsEquivFork` 的定义

English:
definition multiforkOfParallelHomsEquivFork
  signature: (J : MulticospanShape) [Unique J.L] [Unique J.R] {X Y : C}
  body: by
  refine (multiforkEquivPiForkOfIsLimit _
      (Fan.isLimitMkOfUnique (Iso.refl X) _) (Fan.isLimitMkOfUnique (Iso.refl Y) _)).trans
      (Fork.equivOfIsos (.refl _) (.refl _) ?_ ?_)
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ => ?_
    rw [Category.assoc]; 

中文:
定义 multiforkOfParallelHomsEquivFork
  签名: (J : MulticospanShape) [唯一 J.L] [唯一 J.R] {X Y : C}
  定义体: by
  refine (multiforkEquivPiForkOfIsLimit _
      (Fan.isLimitMkOfUnique (Iso.refl X) _) (Fan.isLimitMkOfUnique (Iso.refl Y) _)).trans
      (Fork.equivOfIsos (.refl _) (.refl _) ?_ ?_)
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ => ?_
    rw [Category.assoc]; 

Depends on / 依赖: Category, Category.asso, Category.assoc, Category.comp_id, Fan.IsLimit.hom_ext, Fan.isLimitMkOfUnique, Fan.mk, Fork.equivOfIsos, IsLimit, Iso.refl, Iso.refl_hom, comp_id, equivOfIsos, fstPiMapOfIsLimit_proj, hom_ext, isLimitMkOfUnique, multiforkEquivPiForkOfIsLimit, refl_hom
-/
def multiforkOfParallelHomsEquivFork (J : MulticospanShape) [Unique J.L] [Unique J.R] {X Y : C}
    (f g : X ⟶ Y) :
    Multifork (ofParallelHoms J f g) ≌ Fork f g := by
  refine (multiforkEquivPiForkOfIsLimit _
      (Fan.isLimitMkOfUnique (Iso.refl X) _) (Fan.isLimitMkOfUnique (Iso.refl Y) _)).trans
      (Fork.equivOfIsos (.refl _) (.refl _) ?_ ?_)
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ => ?_
    rw [Category.assoc]; rw [Iso.refl_hom ((Fan.mk Y fun x => (Iso.refl Y).hom).pt)]; rw [Category.comp_id]; rw [fstPiMapOfIsLimit_proj]
    simp
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ => ?_
    rw [Category.assoc]; rw [Iso.refl_hom ((Fan.mk Y fun x => (Iso.refl Y).hom).pt)]; rw [Category.comp_id]; rw [sndPiMapOfIsLimit_proj]
    simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `multiforkOfParallelHomsEquivFork_functor_obj_ι` / 引理 `multiforkOfParallelHomsEquivFork_functor_obj_ι`

English:
lemma multiforkOfParallelHomsEquivFork_functor_obj_ι
  statement: (J : MulticospanShape) [Unique J.L]
  proof: Fan.IsLimit.fac (Fan.isLimitMkOfUnique (Iso.refl X) J.L) _ default

中文:
引理 multiforkOfParallelHomsEquivFork_functor_obj_ι
  结论: (J : MulticospanShape) [唯一 J.L]
  证明: Fan.IsLimit.fac (Fan.isLimitMkOfUnique (Iso.refl X) J.L) _ default

Depends on / 依赖: Fan.IsLimit.fac, Fan.isLimitMkOfUnique, IsLimit, Iso.refl, isLimitMkOfUnique
-/
lemma multiforkOfParallelHomsEquivFork_functor_obj_ι (J : MulticospanShape) [Unique J.L]
    [Unique J.R] {X Y : C} (f g : X ⟶ Y) (c : Multifork (ofParallelHoms J f g)) :
    ((multiforkOfParallelHomsEquivFork J f g).functor.obj c).ι = c.ι default :=
  Fan.IsLimit.fac (Fan.isLimitMkOfUnique (Iso.refl X) J.L) _ default

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `multiforkOfParallelHomsEquivFork_inverse_obj_ι` / 引理 `multiforkOfParallelHomsEquivFork_inverse_obj_ι`

English:
lemma multiforkOfParallelHomsEquivFork_inverse_obj_ι
  statement: (J : MulticospanShape) [Unique J.L]
  proof: by
  simp [multiforkOfParallelHomsEquivFork]

中文:
引理 multiforkOfParallelHomsEquivFork_inverse_obj_ι
  结论: (J : MulticospanShape) [唯一 J.L]
  证明: by
  simp [multiforkOfParallelHomsEquivFork]

Depends on / 依赖: multiforkOfParallelHomsEquivFork
-/
lemma multiforkOfParallelHomsEquivFork_inverse_obj_ι (J : MulticospanShape) [Unique J.L]
    [Unique J.R] {X Y : C} (f g : X ⟶ Y) (c : Fork f g) (a : J.L) :
    ((multiforkOfParallelHomsEquivFork J f g).inverse.obj c).ι a = c.ι := by
  simp [multiforkOfParallelHomsEquivFork]

end MulticospanIndex

namespace Multicofork

variable {J : MultispanShape.{w, w'}} {I : MultispanIndex J C} (K : Multicofork I)

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: (b : J.R)
  body: K.ι.app (WalkingMultispan.right _)

@[simp]

中文:
定义 π
  签名: (b : J.R)
  定义体: K.ι.app (WalkingMultispan.right _)

@[simp]

Depends on / 依赖: WalkingMultispan, WalkingMultispan.right
-/
def π (b : J.R) : I.right b ⟶ K.pt :=
  K.ι.app (WalkingMultispan.right _)

@[simp]
/--
theorem `π_eq_app_right` / 定理 `π_eq_app_right`

English:
theorem π_eq_app_right
  given: (b)
  statement: K.ι.app (WalkingMultispan.right _) = K.π b
  proof: rfl

@[simp]

中文:
定理 π_eq_app_right
  条件: (b)
  结论: K.ι.app (WalkingMultispan.right _) = K.π b
  证明: rfl

@[simp]
-/
theorem π_eq_app_right (b) : K.ι.app (WalkingMultispan.right _) = K.π b :=
  rfl

@[simp]
/--
theorem `fst_app_right` / 定理 `fst_app_right`

English:
theorem fst_app_right
  given: (a)
  statement: K.ι.app (WalkingMultispan.left a) = I.fst a ≫ K.π _
  proof: by
  rw [← K.w (WalkingMultispan.Hom.fst a)]
  rfl

@[reassoc]

中文:
定理 fst_app_right
  条件: (a)
  结论: K.ι.app (WalkingMultispan.left a) = I.fst a ≫ K.π _
  证明: by
  rw [← K.w (WalkingMultispan.Hom.fst a)]
  rfl

@[reassoc]

Depends on / 依赖: WalkingMultispan, WalkingMultispan.Hom.fst
-/
theorem fst_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.fst a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.fst a)]
  rfl

@[reassoc]
/--
theorem `snd_app_right` / 定理 `snd_app_right`

English:
theorem snd_app_right
  given: (a)
  statement: K.ι.app (WalkingMultispan.left a) = I.snd a ≫ K.π _
  proof: by
  rw [← K.w (WalkingMultispan.Hom.snd a)]
  rfl

@[reassoc (attr := simp)]

中文:
定理 snd_app_right
  条件: (a)
  结论: K.ι.app (WalkingMultispan.left a) = I.snd a ≫ K.π _
  证明: by
  rw [← K.w (WalkingMultispan.Hom.snd a)]
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: WalkingMultispan, WalkingMultispan.Hom.snd
-/
theorem snd_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.snd a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.snd a)]
  rfl

@[reassoc (attr := simp)]
/--
lemma `π_comp_hom` / 引理 `π_comp_hom`

English:
lemma π_comp_hom
  given: (K₁ K₂ : Multicofork I) (f : K₁ ⟶ K₂) (b : J.R)
  statement: K₁.π b ≫ f.hom = K₂.π b
  proof: f.w _

中文:
引理 π_comp_hom
  条件: (K₁ K₂ : Multicofork I) (f : K₁ ⟶ K₂) (b : J.R)
  结论: K₁.π b ≫ f.hom = K₂.π b
  证明: f.w _
-/
lemma π_comp_hom (K₁ K₂ : Multicofork I) (f : K₁ ⟶ K₂) (b : J.R) : K₁.π b ≫ f.hom = K₂.π b :=
  f.w _

set_option backward.defeqAttrib.useBackward true in
/-- Construct a multicofork using a collection `π` of morphisms. -/
@[simps]
/--
Definition of `ofπ` / `ofπ` 的定义

English:
definition ofπ
  signature: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  body: P
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left a => I.fst a ≫ π _
        | WalkingMultispan.right _ => π _
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp <;>
          simp only [Functor.map_id, MultispanIndex.multispan_obj_left,
   

中文:
定义 ofπ
  签名: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  定义体: P
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left a => I.fst a ≫ π _
        | WalkingMultispan.right _ => π _
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp <;>
          simp only [Functor.map_id, MultispanIndex.multispan_obj_left,
   
-/
def ofπ {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
    (P : C) (π : forall b, I.right b ⟶ P)
    (w : forall a, I.fst a ≫ π (J.fst a) = I.snd a ≫ π (J.snd a)) : Multicofork I where
  pt := P
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left a => I.fst a ≫ π _
        | WalkingMultispan.right _ => π _
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp <;>
          simp only [Functor.map_id, MultispanIndex.multispan_obj_left,
            Category.id_comp, Category.comp_id, MultispanIndex.multispan_obj_right]
        symm
        apply w }

@[reassoc (attr := simp)]
/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: (a)
  statement: I.fst a ≫ K.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
  proof: by
  rw [← K.snd_app_right]; rw [← K.fst_app_right]

中文:
定理 condition
  条件: (a)
  结论: I.fst a ≫ K.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
  证明: by
  rw [← K.snd_app_right]; rw [← K.fst_app_right]

Depends on / 依赖: K.fst_app_right, K.snd_app_right, fst_app_right, snd_app_right
-/
theorem condition (a) : I.fst a ≫ K.π (J.fst a) = I.snd a ≫ K.π (J.snd a) := by
  rw [← K.snd_app_right]; rw [← K.fst_app_right]

set_option backward.isDefEq.respectTransparency false in
/-- This definition provides a convenient way to show that a multicofork is a colimit. -/
@[simps]
/--
Definition of `IsColimit.mk` / `IsColimit.mk` 的定义

English:
definition IsColimit.mk
  signature: (desc : forall E : Multicofork I, K.pt ⟶ E.pt)
  body: { desc
    fac := by
      rintro S (a | b)
      · rw [← K.w (WalkingMultispan.Hom.fst a), ← S.w (WalkingMultispan.Hom.fst a),
          Category.assoc]
        congr 1
        apply fac
      · apply fac
    uniq := by
      intro S m hm
      apply uniq
      intro i
      apply hm }

中文:
定义 是余极限.mk
  签名: (desc : 对任意 E : Multicofork I, K.pt ⟶ E.pt)
  定义体: { desc
    fac := by
      rintro S (a | b)
      · rw [← K.w (WalkingMultispan.Hom.fst a), ← S.w (WalkingMultispan.Hom.fst a),
          Category.assoc]
        congr 1
        apply fac
      · apply fac
    uniq := by
      intro S m hm
      apply uniq
      intro i
      apply hm }

Depends on / 依赖: Category, Category.assoc, WalkingMultispan, WalkingMultispan.Hom.fst
-/
def IsColimit.mk (desc : forall E : Multicofork I, K.pt ⟶ E.pt)
    (fac : forall (E : Multicofork I) (i : J.R), K.π i ≫ desc E = E.π i)
    (uniq : forall (E : Multicofork I) (m : K.pt ⟶ E.pt), (forall i : J.R, K.π i ≫ m = E.π i) -> m = desc E) :
    IsColimit K :=
  { desc
    fac := by
      rintro S (a | b)
      · rw [← K.w (WalkingMultispan.Hom.fst a), ← S.w (WalkingMultispan.Hom.fst a),
          Category.assoc]
        congr 1
        apply fac
      · apply fac
    uniq := by
      intro S m hm
      apply uniq
      intro i
      apply hm }

variable {K}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsColimit.hom_ext` / 引理 `IsColimit.hom_ext`

English:
lemma IsColimit.hom_ext
  statement: (hK : IsColimit K) {T : C} {f g : K.pt ⟶ T}
  proof: by
  apply hK.hom_ext
  rintro (_ | _) <;> simp [h]

中文:
引理 是余极限.hom_ext
  结论: (hK : 是余极限 K) {T : C} {f g : K.pt ⟶ T}
  证明: by
  apply hK.hom_ext
  rintro (_ | _) <;> simp [h]

Depends on / 依赖: hK.hom_ext, hom_ext
-/
lemma IsColimit.hom_ext (hK : IsColimit K) {T : C} {f g : K.pt ⟶ T}
    (h : forall a, K.π a ≫ f = K.π a ≫ g) : f = g := by
  apply hK.hom_ext
  rintro (_ | _) <;> simp [h]

/--
Definition of `IsColimit.desc` / `IsColimit.desc` 的定义

English:
definition IsColimit.desc
  signature: (hK : IsColimit K) {T : C} (k : forall a, I.right a ⟶ T)
  body: hK.desc (Multicofork.ofπ _ _ k hk)

@[reassoc (attr := simp)]

中文:
定义 是余极限.desc
  签名: (hK : 是余极限 K) {T : C} (k : 对任意 a, I.right a ⟶ T)
  定义体: hK.desc (Multicofork.ofπ _ _ k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: Multicofork, Multicofork.of, hK.desc
-/
def IsColimit.desc (hK : IsColimit K) {T : C} (k : forall a, I.right a ⟶ T)
    (hk : forall b, I.fst b ≫ k (J.fst b) = I.snd b ≫ k (J.snd b)) :
    K.pt ⟶ T :=
  hK.desc (Multicofork.ofπ _ _ k hk)

@[reassoc (attr := simp)]
/--
lemma `IsColimit.fac` / 引理 `IsColimit.fac`

English:
lemma IsColimit.fac
  statement: (hK : IsColimit K) {T : C} (k : forall a, I.right a ⟶ T)
  proof: hK.fac _ _

中文:
引理 是余极限.fac
  结论: (hK : 是余极限 K) {T : C} (k : 对任意 a, I.right a ⟶ T)
  证明: hK.fac _ _

Depends on / 依赖: hK.fac
-/
lemma IsColimit.fac (hK : IsColimit K) {T : C} (k : forall a, I.right a ⟶ T)
    (hk : forall b, I.fst b ≫ k (J.fst b) = I.snd b ≫ k (J.snd b)) (a : J.R) :
    K.π a ≫ IsColimit.desc hK k hk = k a :=
  hK.fac _ _

variable (K)
variable {c : Cofan I.left} (hc : IsColimit c) {d : Cofan I.right} (hd : IsColimit d)

@[reassoc (attr := simp)]
/--
theorem `sigma_condition` / 定理 `sigma_condition`

English:
theorem sigma_condition
  proof: by
  apply Cofan.IsColimit.hom_ext hc
  simp

中文:
定理 sigma_condition
  证明: by
  apply Cofan.IsColimit.hom_ext hc
  simp

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, hom_ext
-/
theorem sigma_condition :
    I.fstSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd K.π =
      I.sndSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd K.π := by
  apply Cofan.IsColimit.hom_ext hc
  simp

/-- Given a multicofork, we may obtain a cofork over `∐ I.left ⇉ ∐ I.right`. -/
@[simps! pt]
/--
Definition of `toSigmaCofork` / `toSigmaCofork` 的定义

English:
definition toSigmaCofork
  signature: (K : Multicofork I)
  body: .ofπ (Cofan.IsColimit.desc hd K.π) (by simp)

@[simp]

中文:
定义 toSigmaCofork
  签名: (K : Multicofork I)
  定义体: .ofπ (Cofan.IsColimit.desc hd K.π) (by simp)

@[simp]

Depends on / 依赖: Cofan.IsColimit.desc, IsColimit
-/
noncomputable def toSigmaCofork (K : Multicofork I) :
    Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) :=
  .ofπ (Cofan.IsColimit.desc hd K.π) (by simp)

@[simp]
/--
theorem `toSigmaCofork_π` / 定理 `toSigmaCofork_π`

English:
theorem toSigmaCofork_π
  proof: rfl

中文:
定理 toSigmaCofork_π
  证明: rfl
-/
theorem toSigmaCofork_π :
    (K.toSigmaCofork hc hd).π = Cofan.IsColimit.desc hd K.π :=
  rfl

set_option backward.defeqAttrib.useBackward true in
variable {hc} in
/-- Given a cofork over `∐ I.left ⇉ ∐ I.right`, we may obtain a multicofork. -/
@[simps pt]
/--
Definition of `ofSigmaCofork` / `ofSigmaCofork` 的定义

English:
definition ofSigmaCofork
  body: a.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left _ => c.inj _ ≫ I.fstSigmaMapOfIsColimit d hc ≫ a.π
        | WalkingMultispan.right _ => d.inj _ ≫ a.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · simp

中文:
定义 ofSigmaCofork
  定义体: a.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left _ => c.inj _ ≫ I.fstSigmaMapOfIsColimit d hc ≫ a.π
        | WalkingMultispan.right _ => d.inj _ ≫ a.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · simp

Depends on / 依赖: a.pt
-/
noncomputable def ofSigmaCofork
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) :
    Multicofork I where
  pt := a.pt
  ι :=
    { app := fun x =>
        match x with
        | WalkingMultispan.left _ => c.inj _ ≫ I.fstSigmaMapOfIsColimit d hc ≫ a.π
        | WalkingMultispan.right _ => d.inj _ ≫ a.π
      naturality := by
        rintro (_ | _) (_ | _) (_ | _ | _)
        · simp
        · simp
        · simp [a.condition]
        · simp }

@[simp]
/--
theorem `ofSigmaCofork_ι_app_left` / 定理 `ofSigmaCofork_ι_app_left`

English:
theorem ofSigmaCofork_ι_app_left
  proof: rfl

@[simp]

中文:
定理 ofSigmaCofork_ι_app_left
  证明: rfl

@[simp]
-/
theorem ofSigmaCofork_ι_app_left
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) (i) :
    (ofSigmaCofork a).ι.app (WalkingMultispan.left i) =
      c.inj _ ≫ I.fstSigmaMapOfIsColimit d hc ≫ a.π :=
  rfl

@[simp]
/--
theorem `ofSigmaCofork_π` / 定理 `ofSigmaCofork_π`

English:
theorem ofSigmaCofork_π
  proof: rfl

中文:
定理 ofSigmaCofork_π
  证明: rfl
-/
theorem ofSigmaCofork_π
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) (i) :
    (ofSigmaCofork a).π i = d.inj i ≫ a.π :=
  rfl

/-- Constructor for isomorphisms between multicoforks. -/
@[simps!]
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {K K' : Multicofork I}
  body: Cocone.ext e (by rintro (i | j) <;> simp [h])

中文:
定义 ext
  签名: {K K' : Multicofork I}
  定义体: Cocone.ext e (by rintro (i | j) <;> simp [h])

Depends on / 依赖: Cocone, Cocone.ext, cat_disch
-/
def ext {K K' : Multicofork I}
    (e : K.pt ≅ K'.pt) (h : forall (i : J.R), K.π i ≫ e.hom = K'.π i := by cat_disch) :
    K ≅ K' :=
  Cocone.ext e (by rintro (i | j) <;> simp [h])

set_option backward.defeqAttrib.useBackward true in
/-- Every multicofork is isomorphic to one of the form `Multicofork.ofπ`. -/
@[simps!]
/--
Definition of `isoOfπ` / `isoOfπ` 的定义

English:
definition isoOfπ
  signature: (t : Multicofork I)
  body: ext (Iso.refl _)

中文:
定义 isoOfπ
  签名: (t : Multicofork I)
  定义体: ext (Iso.refl _)

Depends on / 依赖: Iso.refl
-/
def isoOfπ (t : Multicofork I) : t ≅ ofπ _ t.pt t.π t.condition :=
  ext (Iso.refl _)

end Multicofork

namespace MultispanIndex

variable {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
variable {c : Cofan I.left} (hc : IsColimit c) {d : Cofan I.right} (hd : IsColimit d)

set_option backward.defeqAttrib.useBackward true in
/-- `Multicofork.toSigmaCofork` as a functor. -/
@[simps]
/--
Definition of `toSigmaCoforkFunctor` / `toSigmaCoforkFunctor` 的定义

English:
definition toSigmaCoforkFunctor
  signature: :
  body: Multicofork.toSigmaCofork hc hd
  map {K₁ K₂} f :=
  { hom := f.hom
    w := by
      rintro (_ | _)
      · apply Cofan.IsColimit.hom_ext hc
        simp
      · apply Cofan.IsColimit.hom_ext hd
        simp }

中文:
定义 toSigmaCoforkFunctor
  签名: :
  定义体: Multicofork.toSigmaCofork hc hd
  map {K₁ K₂} f :=
  { hom := f.hom
    w := by
      rintro (_ | _)
      · apply Cofan.IsColimit.hom_ext hc
        simp
      · apply Cofan.IsColimit.hom_ext hd
        simp }

Depends on / 依赖: Multicofork, Multicofork.toSigmaCofork, toSigmaCofork
-/
noncomputable def toSigmaCoforkFunctor :
    Multicofork I ⥤ Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) where
  obj := Multicofork.toSigmaCofork hc hd
  map {K₁ K₂} f :=
  { hom := f.hom
    w := by
      rintro (_ | _)
      · apply Cofan.IsColimit.hom_ext hc
        simp
      · apply Cofan.IsColimit.hom_ext hd
        simp }

set_option backward.defeqAttrib.useBackward true in
/-- `Multicofork.ofSigmaCofork` as a functor. -/
@[simps]
/--
Definition of `ofSigmaCoforkFunctor` / `ofSigmaCoforkFunctor` 的定义

English:
definition ofSigmaCoforkFunctor
  signature: :
  body: Multicofork.ofSigmaCofork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

中文:
定义 ofSigmaCoforkFunctor
  签名: :
  定义体: Multicofork.ofSigmaCofork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

Depends on / 依赖: Multicofork, Multicofork.ofSigmaCofork, ofSigmaCofork
-/
noncomputable def ofSigmaCoforkFunctor :
    Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) ⥤ Multicofork I where
  obj := Multicofork.ofSigmaCofork
  map {K₁ K₂} f :=
    { hom := f.hom
      w := by rintro (_ | _) <;> simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The category of multicoforks is equivalent to the category of coforks over `∐ I.left ⇉ ∐ I.right`.
It then follows from `CategoryTheory.IsColimit.ofPreservesCoconeInitial` (or `reflects`) that
it preserves and reflects colimit cocones.
-/
@[simps]
/--
Definition of `multicoforkEquivSigmaCoforkOfIsColimit` / `multicoforkEquivSigmaCoforkOfIsColimit` 的定义

English:
definition multicoforkEquivSigmaCoforkOfIsColimit
  signature: :
  body: toSigmaCoforkFunctor I hc hd
  inverse := ofSigmaCoforkFunctor I hc
  unitIso := NatIso.ofComponents fun K => Cocone.ext (Iso.refl _) (by
      rintro (_ | _) <;> simp)
  counitIso := NatIso.ofComponents fun K =>
    Cofork.ext (Iso.refl _)
      (by
        apply Cofan.IsColimit.hom_ext hd
        

中文:
定义 multicoforkEquivSigmaCoforkOfIsColimit
  签名: :
  定义体: toSigmaCoforkFunctor I hc hd
  inverse := ofSigmaCoforkFunctor I hc
  unitIso := NatIso.ofComponents fun K => Cocone.ext (Iso.refl _) (by
      rintro (_ | _) <;> simp)
  counitIso := NatIso.ofComponents fun K =>
    Cofork.ext (Iso.refl _)
      (by
        apply Cofan.IsColimit.hom_ext hd
        

Depends on / 依赖: toSigmaCoforkFunctor
-/
noncomputable def multicoforkEquivSigmaCoforkOfIsColimit :
    Multicofork I ≌ Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) where
  functor := toSigmaCoforkFunctor I hc hd
  inverse := ofSigmaCoforkFunctor I hc
  unitIso := NatIso.ofComponents fun K => Cocone.ext (Iso.refl _) (by
      rintro (_ | _) <;> simp)
  counitIso := NatIso.ofComponents fun K =>
    Cofork.ext (Iso.refl _)
      (by
        apply Cofan.IsColimit.hom_ext hd
        simp)

variable [HasCoproduct I.left] [HasCoproduct I.right]

set_option backward.isDefEq.respectTransparency.types false in
/--
The category of multicoforks is equivalent to the category of coforks over `∐ I.left ⇉ ∐ I.right`.
It then follows from `CategoryTheory.IsColimit.ofPreservesCoconeInitial` (or `reflects`) that
it preserves and reflects colimit cocones.
-/
@[simps!]
/--
Definition of `multicoforkEquivSigmaCofork` / `multicoforkEquivSigmaCofork` 的定义

English:
definition multicoforkEquivSigmaCofork
  signature: :
  body: multicoforkEquivSigmaCoforkOfIsColimit _ (colimit.isColimit _) (colimit.isColimit _)

中文:
定义 multicoforkEquivSigmaCofork
  签名: :
  定义体: multicoforkEquivSigmaCoforkOfIsColimit _ (colimit.isColimit _) (colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isLeftKanExtension, isPointwiseLeftKanExtensionConvolutionExtensionUnit, multicoforkEquivSigmaCoforkOfIsColimit
-/
noncomputable def multicoforkEquivSigmaCofork :
    Multicofork I ≌ Cofork I.fstSigmaMap I.sndSigmaMap :=
  multicoforkEquivSigmaCoforkOfIsColimit _ (colimit.isColimit _) (colimit.isColimit _)

end MultispanIndex

/--
Definition of `HasMultiequalizer` / `HasMultiequalizer` 的定义

English:
abbreviation HasMultiequalizer
  signature: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  body: HasLimit I.multicospan

noncomputable section

中文:
缩写 HasMultiequalizer
  签名: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  定义体: HasLimit I.multicospan

noncomputable section

Depends on / 依赖: HasLimit, I.multicospan, multicospan
-/
abbrev HasMultiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :=
  HasLimit I.multicospan

noncomputable section

/--
Definition of `multiequalizer` / `multiequalizer` 的定义

English:
abbreviation multiequalizer
  signature: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  body: limit I.multicospan

中文:
缩写 multiequalizer
  签名: {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
  定义体: limit I.multicospan

Depends on / 依赖: I.multicospan, multicospan
-/
abbrev multiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    [HasMultiequalizer I] : C :=
  limit I.multicospan

/--
Definition of `HasMulticoequalizer` / `HasMulticoequalizer` 的定义

English:
abbreviation HasMulticoequalizer
  signature: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  body: HasColimit I.multispan

中文:
缩写 HasMulticoequalizer
  签名: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  定义体: HasColimit I.multispan

Depends on / 依赖: HasColimit, I.multispan, multispan
-/
abbrev HasMulticoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) :=
  HasColimit I.multispan

/--
Definition of `multicoequalizer` / `multicoequalizer` 的定义

English:
abbreviation multicoequalizer
  signature: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  body: colimit I.multispan

中文:
缩写 multicoequalizer
  签名: {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
  定义体: colimit I.multispan

Depends on / 依赖: I.multispan, colimit, multispan
-/
abbrev multicoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
    [HasMulticoequalizer I] : C :=
  colimit I.multispan

namespace Multiequalizer

variable {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) [HasMultiequalizer I]

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: (a : J.L)
  body: limit.π _ (WalkingMulticospan.left a)

中文:
缩写 ι
  签名: (a : J.L)
  定义体: limit.π _ (WalkingMulticospan.left a)

Depends on / 依赖: WalkingMulticospan, WalkingMulticospan.left
-/
abbrev ι (a : J.L) : multiequalizer I ⟶ I.left a :=
  limit.π _ (WalkingMulticospan.left a)

/--
Definition of `multifork` / `multifork` 的定义

English:
abbreviation multifork
  signature: : Multifork I
  body: limit.cone _

@[simp]

中文:
缩写 multifork
  签名: : Multifork I
  定义体: limit.cone _

@[simp]

Depends on / 依赖: limit.cone
-/
abbrev multifork : Multifork I :=
  limit.cone _

@[simp]
/--
theorem `multifork_ι` / 定理 `multifork_ι`

English:
theorem multifork_ι
  given: (a)
  statement: (Multiequalizer.multifork I).ι a = Multiequalizer.ι I a
  proof: rfl

@[simp]

中文:
定理 multifork_ι
  条件: (a)
  结论: (Multiequalizer.multifork I).ι a = Multiequalizer.ι I a
  证明: rfl

@[simp]
-/
theorem multifork_ι (a) : (Multiequalizer.multifork I).ι a = Multiequalizer.ι I a :=
  rfl

@[simp]
/--
theorem `multifork_π_app_left` / 定理 `multifork_π_app_left`

English:
theorem multifork_π_app_left
  given: (a)
  proof: rfl

@[reassoc]

中文:
定理 multifork_π_app_left
  条件: (a)
  证明: rfl

@[reassoc]
-/
theorem multifork_π_app_left (a) :
    (Multiequalizer.multifork I).π.app (WalkingMulticospan.left a) = Multiequalizer.ι I a :=
  rfl

@[reassoc]
/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: (b)
  proof: Multifork.condition _ _

中文:
定理 condition
  条件: (b)
  证明: Multifork.condition _ _

Depends on / 依赖: Multifork, Multifork.condition, condition
-/
theorem condition (b) :
    Multiequalizer.ι I (J.fst b) ≫ I.fst b = Multiequalizer.ι I (J.snd b) ≫ I.snd b :=
  Multifork.condition _ _

/--
Definition of `lift` / `lift` 的定义

English:
abbreviation lift
  signature: (W : C) (k : forall a, W ⟶ I.left a)
  body: limit.lift _ (Multifork.ofι I _ k h)

@[reassoc]

中文:
缩写 lift
  签名: (W : C) (k : 对任意 a, W ⟶ I.left a)
  定义体: limit.lift _ (Multifork.ofι I _ k h)

@[reassoc]

Depends on / 依赖: Multifork, Multifork.of, limit.lift
-/
abbrev lift (W : C) (k : forall a, W ⟶ I.left a)
    (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) : W ⟶ multiequalizer I :=
  limit.lift _ (Multifork.ofι I _ k h)

@[reassoc]
/--
theorem `lift_ι` / 定理 `lift_ι`

English:
theorem lift_ι
  statement: (W : C) (k : forall a, W ⟶ I.left a)
  proof: limit.lift_π _ _

@[ext]

中文:
定理 lift_ι
  结论: (W : C) (k : 对任意 a, W ⟶ I.left a)
  证明: limit.lift_π _ _

@[ext]

Depends on / 依赖: limit.lift_
-/
theorem lift_ι (W : C) (k : forall a, W ⟶ I.left a)
    (h : forall b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (a) :
    Multiequalizer.lift I _ k h ≫ Multiequalizer.ι I a = k _ :=
  limit.lift_π _ _

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {W : C} (i j : W ⟶ multiequalizer I)
  proof: Multifork.IsLimit.hom_ext (limit.isLimit _) h

中文:
定理 hom_ext
  结论: {W : C} (i j : W ⟶ multiequalizer I)
  证明: Multifork.IsLimit.hom_ext (limit.isLimit _) h

Depends on / 依赖: IsLimit, Multifork, Multifork.IsLimit.hom_ext, hom_ext, isLimit, limit.isLimit
-/
theorem hom_ext {W : C} (i j : W ⟶ multiequalizer I)
    (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.ι I a) : i = j :=
  Multifork.IsLimit.hom_ext (limit.isLimit _) h

variable [HasProduct I.left] [HasProduct I.right]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasEqualizer I.fstPiMap I.sndPiMap
  body: ⟨⟨⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.functor (limit.isLimit _)⟩⟩⟩

中文:
实例 :
  签名: HasEqualizer I.fstPiMap I.sndPiMap
  定义体: ⟨⟨⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.functor (limit.isLimit _)⟩⟩⟩

Depends on / 依赖: I.multiforkEquivPiFork.functor, IsLimit, IsLimit.ofPreservesConeTerminal, functor, isLimit, limit.isLimit, multiforkEquivPiFork, ofPreservesConeTerminal
-/
instance : HasEqualizer I.fstPiMap I.sndPiMap :=
  ⟨⟨⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.functor (limit.isLimit _)⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isoEqualizer` / `isoEqualizer` 的定义

English:
definition isoEqualizer
  signature: : multiequalizer I ≅ equalizer I.fstPiMap I.sndPiMap
  body: limit.isoLimitCone
    ⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.inverse (limit.isLimit _)⟩

中文:
定义 isoEqualizer
  签名: : multiequalizer I ≅ equalizer I.fstPiMap I.sndPiMap
  定义体: limit.isoLimitCone
    ⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.inverse (limit.isLimit _)⟩

Depends on / 依赖: I.multiforkEquivPiFork.inverse, IsLimit, IsLimit.ofPreservesConeTerminal, inverse, isLimit, isoLimitCone, limit.isLimit, limit.isoLimitCone, multiforkEquivPiFork, ofPreservesConeTerminal
-/
def isoEqualizer : multiequalizer I ≅ equalizer I.fstPiMap I.sndPiMap :=
  limit.isoLimitCone
    ⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.inverse (limit.isLimit _)⟩

/--
Definition of `ιPi` / `ιPi` 的定义

English:
definition ιPi
  signature: : multiequalizer I ⟶ ∏ᶜ I.left
  body: (isoEqualizer I).hom ≫ equalizer.ι I.fstPiMap I.sndPiMap

中文:
定义 ιPi
  签名: : multiequalizer I ⟶ ∏ᶜ I.left
  定义体: (isoEqualizer I).hom ≫ equalizer.ι I.fstPiMap I.sndPiMap

Depends on / 依赖: I.fstPiMap, I.sndPiMap, equalizer, fstPiMap, isoEqualizer, sndPiMap
-/
def ιPi : multiequalizer I ⟶ ∏ᶜ I.left :=
  (isoEqualizer I).hom ≫ equalizer.ι I.fstPiMap I.sndPiMap

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ιPi_π` / 定理 `ιPi_π`

English:
theorem ιPi_π
  given: (a)
  statement: ιPi I ≫ Pi.π I.left a = ι I a
  proof: by
  rw [ιPi]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [isoEqualizer]
  simp only [limit.isoLimitCone_inv_π,
    limit.cone_x, MulticospanIndex.multiforkEquivPiFork_inverse_obj_π_app]
  rfl

中文:
定理 ιPi_π
  条件: (a)
  结论: ιPi I ≫ 依赖函数类型.π I.left a = ι I a
  证明: by
  rw [ιPi]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [isoEqualizer]
  simp only [limit.isoLimitCone_inv_π,
    limit.cone_x, MulticospanIndex.multiforkEquivPiFork_inverse_obj_π_app]
  rfl

Depends on / 依赖: Category, Category.assoc, Iso.eq_inv_comp, MulticospanIndex, MulticospanIndex.multiforkEquivPiFork_inverse_obj_, cone_x, eq_inv_comp, isoEqualizer, limit.cone_x, limit.isoLimitCone_inv_
-/
theorem ιPi_π (a) : ιPi I ≫ Pi.π I.left a = ι I a := by
  rw [ιPi]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [isoEqualizer]
  simp only [limit.isoLimitCone_inv_π,
    limit.cone_x, MulticospanIndex.multiforkEquivPiFork_inverse_obj_π_app]
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (ιPi I)
  body: mono_comp _ _

中文:
实例 :
  签名: 单态射 (ιPi I)
  定义体: mono_comp _ _

Depends on / 依赖: mono_comp
-/
instance : Mono (ιPi I) := mono_comp _ _

end Multiequalizer

namespace Multicoequalizer

variable {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) [HasMulticoequalizer I]

/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: (b : J.R)
  body: colimit.ι I.multispan (WalkingMultispan.right _)

中文:
缩写 π
  签名: (b : J.R)
  定义体: colimit.ι I.multispan (WalkingMultispan.right _)

Depends on / 依赖: I.multispan, WalkingMultispan, WalkingMultispan.right, colimit, multispan
-/
abbrev π (b : J.R) : I.right b ⟶ multicoequalizer I :=
  colimit.ι I.multispan (WalkingMultispan.right _)

/--
Definition of `multicofork` / `multicofork` 的定义

English:
abbreviation multicofork
  signature: : Multicofork I
  body: colimit.cocone _

@[simp]

中文:
缩写 multicofork
  签名: : Multicofork I
  定义体: colimit.cocone _

@[simp]

Depends on / 依赖: cocone, colimit, colimit.cocone
-/
abbrev multicofork : Multicofork I :=
  colimit.cocone _

@[simp]
/--
theorem `multicofork_π` / 定理 `multicofork_π`

English:
theorem multicofork_π
  given: (b)
  statement: (Multicoequalizer.multicofork I).π b = Multicoequalizer.π I b
  proof: rfl

中文:
定理 multicofork_π
  条件: (b)
  结论: (Multicoequalizer.multicofork I).π b = Multicoequalizer.π I b
  证明: rfl
-/
theorem multicofork_π (b) : (Multicoequalizer.multicofork I).π b = Multicoequalizer.π I b :=
  rfl

/--
theorem `multicofork_ι_app_right` / 定理 `multicofork_ι_app_right`

English:
theorem multicofork_ι_app_right
  given: (b)
  proof: rfl

中文:
定理 multicofork_ι_app_right
  条件: (b)
  证明: rfl
-/
theorem multicofork_ι_app_right (b) :
    (Multicoequalizer.multicofork I).ι.app (WalkingMultispan.right b) = Multicoequalizer.π I b :=
  rfl

/-- `@[simp]`-normal form of `multicofork_ι_app_right`. -/
@[simp]
/--
theorem `multicofork_ι_app_right'` / 定理 `multicofork_ι_app_right'`

English:
theorem multicofork_ι_app_right'
  given: (b)
  proof: rfl

@[reassoc]

中文:
定理 multicofork_ι_app_right'
  条件: (b)
  证明: rfl

@[reassoc]
-/
theorem multicofork_ι_app_right' (b) :
    colimit.ι (MultispanIndex.multispan I) (WalkingMultispan.right b) = π I b :=
  rfl

@[reassoc]
/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  given: (a)
  proof: Multicofork.condition _ _

中文:
定理 condition
  条件: (a)
  证明: Multicofork.condition _ _

Depends on / 依赖: Multicofork, Multicofork.condition, condition
-/
theorem condition (a) :
    I.fst a ≫ Multicoequalizer.π I (J.fst a) = I.snd a ≫ Multicoequalizer.π I (J.snd a) :=
  Multicofork.condition _ _

/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: (W : C) (k : forall b, I.right b ⟶ W)
  body: colimit.desc _ (Multicofork.ofπ I _ k h)

@[reassoc]

中文:
缩写 desc
  签名: (W : C) (k : 对任意 b, I.right b ⟶ W)
  定义体: colimit.desc _ (Multicofork.ofπ I _ k h)

@[reassoc]

Depends on / 依赖: Multicofork, Multicofork.of, colimit, colimit.desc
-/
abbrev desc (W : C) (k : forall b, I.right b ⟶ W)
    (h : forall a, I.fst a ≫ k (J.fst a) = I.snd a ≫ k (J.snd a)) : multicoequalizer I ⟶ W :=
  colimit.desc _ (Multicofork.ofπ I _ k h)

@[reassoc]
/--
theorem `π_desc` / 定理 `π_desc`

English:
theorem π_desc
  statement: (W : C) (k : forall b, I.right b ⟶ W)
  proof: colimit.ι_desc _ _

中文:
定理 π_desc
  结论: (W : C) (k : 对任意 b, I.right b ⟶ W)
  证明: colimit.ι_desc _ _

Depends on / 依赖: colimit
-/
theorem π_desc (W : C) (k : forall b, I.right b ⟶ W)
    (h : forall a, I.fst a ≫ k (J.fst a) = I.snd a ≫ k (J.snd a)) (b) :
    Multicoequalizer.π I b ≫ Multicoequalizer.desc I _ k h = k _ :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {W : C} (i j : multicoequalizer I ⟶ W)
  proof: colimit.hom_ext
    (by
      rintro (a | b)
      · simp_rw [← colimit.w I.multispan (WalkingMultispan.Hom.fst a), Category.assoc, h]
      · apply h)

中文:
定理 hom_ext
  结论: {W : C} (i j : multicoequalizer I ⟶ W)
  证明: colimit.hom_ext
    (by
      rintro (a | b)
      · simp_rw [← colimit.w I.multispan (WalkingMultispan.Hom.fst a), Category.assoc, h]
      · apply h)

Depends on / 依赖: Category, Category.assoc, I.multispan, WalkingMultispan, WalkingMultispan.Hom.fst, colimit, colimit.hom_ext, colimit.w, hom_ext, multispan, simp_rw
-/
theorem hom_ext {W : C} (i j : multicoequalizer I ⟶ W)
    (h : forall b, Multicoequalizer.π I b ≫ i = Multicoequalizer.π I b ≫ j) : i = j :=
  colimit.hom_ext
    (by
      rintro (a | b)
      · simp_rw [← colimit.w I.multispan (WalkingMultispan.Hom.fst a), Category.assoc, h]
      · apply h)

variable [HasCoproduct I.left] [HasCoproduct I.right]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoequalizer I.fstSigmaMap I.sndSigmaMap
  body: ⟨⟨⟨_,
      IsColimit.ofPreservesCoconeInitial
        I.multicoforkEquivSigmaCofork.functor (colimit.isColimit _)⟩⟩⟩

中文:
实例 :
  签名: HasCoequalizer I.fstSigmaMap I.sndSigmaMap
  定义体: ⟨⟨⟨_,
      IsColimit.ofPreservesCoconeInitial
        I.multicoforkEquivSigmaCofork.functor (colimit.isColimit _)⟩⟩⟩

Depends on / 依赖: I.multicoforkEquivSigmaCofork.functor, IsColimit, IsColimit.ofPreservesCoconeInitial, colimit, colimit.isColimit, functor, isColimit, multicoforkEquivSigmaCofork, ofPreservesCoconeInitial
-/
instance : HasCoequalizer I.fstSigmaMap I.sndSigmaMap :=
  ⟨⟨⟨_,
      IsColimit.ofPreservesCoconeInitial
        I.multicoforkEquivSigmaCofork.functor (colimit.isColimit _)⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isoCoequalizer` / `isoCoequalizer` 的定义

English:
definition isoCoequalizer
  signature: : multicoequalizer I ≅ coequalizer I.fstSigmaMap I.sndSigmaMap
  body: colimit.isoColimitCocone
    ⟨_,
      IsColimit.ofPreservesCoconeInitial I.multicoforkEquivSigmaCofork.inverse
        (colimit.isColimit _)⟩

中文:
定义 isoCoequalizer
  签名: : multicoequalizer I ≅ coequalizer I.fstSigmaMap I.sndSigmaMap
  定义体: colimit.isoColimitCocone
    ⟨_,
      IsColimit.ofPreservesCoconeInitial I.multicoforkEquivSigmaCofork.inverse
        (colimit.isColimit _)⟩

Depends on / 依赖: I.multicoforkEquivSigmaCofork.inverse, IsColimit, IsColimit.ofPreservesCoconeInitial, colimit, colimit.isColimit, colimit.isoColimitCocone, inverse, isColimit, isoColimitCocone, multicoforkEquivSigmaCofork, ofPreservesCoconeInitial
-/
def isoCoequalizer : multicoequalizer I ≅ coequalizer I.fstSigmaMap I.sndSigmaMap :=
  colimit.isoColimitCocone
    ⟨_,
      IsColimit.ofPreservesCoconeInitial I.multicoforkEquivSigmaCofork.inverse
        (colimit.isColimit _)⟩

/--
Definition of `sigmaπ` / `sigmaπ` 的定义

English:
definition sigmaπ
  signature: : ∐ I.right ⟶ multicoequalizer I
  body: coequalizer.π I.fstSigmaMap I.sndSigmaMap ≫ (isoCoequalizer I).inv

中文:
定义 sigmaπ
  签名: : ∐ I.right ⟶ multicoequalizer I
  定义体: coequalizer.π I.fstSigmaMap I.sndSigmaMap ≫ (isoCoequalizer I).inv

Depends on / 依赖: I.fstSigmaMap, I.sndSigmaMap, coequalizer, fstSigmaMap, isoCoequalizer, sndSigmaMap
-/
def sigmaπ : ∐ I.right ⟶ multicoequalizer I :=
  coequalizer.π I.fstSigmaMap I.sndSigmaMap ≫ (isoCoequalizer I).inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_sigmaπ` / 定理 `ι_sigmaπ`

English:
theorem ι_sigmaπ
  given: (b)
  statement: Sigma.ι I.right b ≫ sigmaπ I = π I b
  proof: by
  rw [sigmaπ]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [isoCoequalizer]
  simp
  rfl

中文:
定理 ι_sigmaπ
  条件: (b)
  结论: 依赖和类型.ι I.right b ≫ sigmaπ I = π I b
  证明: by
  rw [sigmaπ]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [isoCoequalizer]
  simp
  rfl

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, comp_inv_eq, isoCoequalizer
-/
theorem ι_sigmaπ (b) : Sigma.ι I.right b ≫ sigmaπ I = π I b := by
  rw [sigmaπ]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [isoCoequalizer]
  simp
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (sigmaπ I)
  body: epi_comp _ _

中文:
实例 :
  签名: 满态射 (sigmaπ I)
  定义体: epi_comp _ _

Depends on / 依赖: epi_comp
-/
instance : Epi (sigmaπ I) := epi_comp _ _

end Multicoequalizer

end

/-- The inclusion functor `WalkingMultispan (.ofLinearOrder ι) ⥤ WalkingMultispan (.prod ι)`. -/
@[simps!]
/--
Definition of `WalkingMultispan.inclusionOfLinearOrder` / `WalkingMultispan.inclusionOfLinearOrder` 的定义

English:
definition WalkingMultispan.inclusionOfLinearOrder
  signature: (ι : Type w) [LinearOrder ι]
  body: MultispanIndex.multispan
    { left j := .left j.1
      right i := .right i
      fst j := WalkingMultispan.Hom.fst (J := .prod ι) j.1
      snd j := WalkingMultispan.Hom.snd (J := .prod ι) j.1 }

中文:
定义 WalkingMultispan.inclusionOfLinearOrder
  签名: (ι : 类型 w) [线性序 ι]
  定义体: MultispanIndex.multispan
    { left j := .left j.1
      right i := .right i
      fst j := WalkingMultispan.Hom.fst (J := .prod ι) j.1
      snd j := WalkingMultispan.Hom.snd (J := .prod ι) j.1 }

Depends on / 依赖: MultispanIndex, MultispanIndex.multispan, WalkingMultispan, WalkingMultispan.Hom.fst, WalkingMultispan.Hom.snd, multispan
-/
def WalkingMultispan.inclusionOfLinearOrder (ι : Type w) [LinearOrder ι] :
    WalkingMultispan (.ofLinearOrder ι) ⥤ WalkingMultispan (.prod ι) :=
  MultispanIndex.multispan
    { left j := .left j.1
      right i := .right i
      fst j := WalkingMultispan.Hom.fst (J := .prod ι) j.1
      snd j := WalkingMultispan.Hom.snd (J := .prod ι) j.1 }

section symmetry

namespace MultispanIndex

variable {ι : Type w} (I : MultispanIndex (.prod ι) C)

/--
Definition of `SymmStruct` / `SymmStruct` 的定义

English:
structure SymmStruct
  parameters: where
  axioms and operations (4):
    - iso((i j : ι)) : I.left ⟨i, j⟩ ≅ I.left ⟨j, i⟩
    - iso_hom_fst((i j : ι)) : (iso i j).hom ≫ I.fst ⟨j, i⟩ = I.snd ⟨i, j⟩
    - iso_hom_snd((i j : ι)) : (iso i j).hom ≫ I.snd ⟨j, i⟩ = I.fst ⟨i, j⟩
    - fst_eq_snd((i : ι)) : I.fst ⟨i, i⟩ = I.snd ⟨i, i⟩

中文:
结构 SymmStruct
  参数: where
  公理与运算 (4 个):
    - iso((i j : ι)) : I.left ⟨i, j⟩ ≅ I.left ⟨j, i⟩
    - iso_hom_fst((i j : ι)) : (iso i j).hom ≫ I.fst ⟨j, i⟩ = I.snd ⟨i, j⟩
    - iso_hom_snd((i j : ι)) : (iso i j).hom ≫ I.snd ⟨j, i⟩ = I.fst ⟨i, j⟩
    - fst_eq_snd((i : ι)) : I.fst ⟨i, i⟩ = I.snd ⟨i, i⟩
-/
structure SymmStruct where
  /-- the symmetry isomorphism -/
  iso (i j : ι) : I.left ⟨i, j⟩ ≅ I.left ⟨j, i⟩
  iso_hom_fst (i j : ι) : (iso i j).hom ≫ I.fst ⟨j, i⟩ = I.snd ⟨i, j⟩
  iso_hom_snd (i j : ι) : (iso i j).hom ≫ I.snd ⟨j, i⟩ = I.fst ⟨i, j⟩
  fst_eq_snd (i : ι) : I.fst ⟨i, i⟩ = I.snd ⟨i, i⟩

attribute [reassoc] SymmStruct.iso_hom_fst SymmStruct.iso_hom_snd

variable [LinearOrder ι]

/-- The multispan index for `MultispanShape.ofLinearOrder ι` deduced from
a multispan index for `MultispanShape.prod ι` when `ι` is linearly ordered. -/
@[simps]
/--
Definition of `toLinearOrder` / `toLinearOrder` 的定义

English:
definition toLinearOrder
  signature: : MultispanIndex (.ofLinearOrder ι) C where
  body: I.left j.1
  right i := I.right i
  fst j := I.fst j.1
  snd j := I.snd j.1

中文:
定义 toLinearOrder
  签名: : MultispanIndex (.ofLinearOrder ι) C where
  定义体: I.left j.1
  right i := I.right i
  fst j := I.fst j.1
  snd j := I.snd j.1

Depends on / 依赖: I.left
-/
def toLinearOrder : MultispanIndex (.ofLinearOrder ι) C where
  left j := I.left j.1
  right i := I.right i
  fst j := I.fst j.1
  snd j := I.snd j.1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a linearly ordered type `ι` and `I : MultispanIndex (.prod ι) C`,
this is the isomorphism of functors between
`WalkingMultispan.inclusionOfLinearOrder ι ⋙ I.multispan`
and `I.toLinearOrder.multispan`. -/
@[simps!]
/--
Definition of `toLinearOrderMultispanIso` / `toLinearOrderMultispanIso` 的定义

English:
definition toLinearOrderMultispanIso
  signature: :
  body: NatIso.ofComponents (fun i => match i with
    | .left _ => Iso.refl _
    | .right _ => Iso.refl _)

中文:
定义 toLinearOrderMultispanIso
  签名: :
  定义体: NatIso.ofComponents (fun i => match i with
    | .left _ => Iso.refl _
    | .right _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def toLinearOrderMultispanIso :
    WalkingMultispan.inclusionOfLinearOrder ι ⋙ I.multispan ≅
      I.toLinearOrder.multispan :=
  NatIso.ofComponents (fun i => match i with
    | .left _ => Iso.refl _
    | .right _ => Iso.refl _)

end MultispanIndex

namespace Multicofork

variable {ι : Type w} [LinearOrder ι] {I : MultispanIndex (.prod ι) C}

/--
Definition of `toLinearOrder` / `toLinearOrder` 的定义

English:
definition toLinearOrder
  signature: (c : Multicofork I)
  body: Multicofork.ofπ _ c.pt c.π (fun _ => c.condition _)

中文:
定义 toLinearOrder
  签名: (c : Multicofork I)
  定义体: Multicofork.ofπ _ c.pt c.π (fun _ => c.condition _)

Depends on / 依赖: Multicofork, Multicofork.of, c.condition, c.pt, condition
-/
def toLinearOrder (c : Multicofork I) : Multicofork I.toLinearOrder :=
  Multicofork.ofπ _ c.pt c.π (fun _ => c.condition _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofLinearOrder` / `ofLinearOrder` 的定义

English:
definition ofLinearOrder
  signature: (c : Multicofork I.toLinearOrder) (h : I.SymmStruct)
  body: Multicofork.ofπ _ c.pt c.π (by
    rintro ⟨x, y⟩
    obtain hxy | rfl | hxy := lt_trichotomy x y
    · exact c.condition ⟨⟨x, y⟩, hxy⟩
    · simp [h.fst_eq_snd]
    · have := c.condition ⟨⟨y, x⟩, hxy⟩
      dsimp at this ⊢
      rw [← h.iso_hom_fst_assoc]; rw [← h.iso_hom_snd_assoc]; rw [this])

中文:
定义 ofLinearOrder
  签名: (c : Multicofork I.toLinearOrder) (h : I.SymmStruct)
  定义体: Multicofork.ofπ _ c.pt c.π (by
    rintro ⟨x, y⟩
    obtain hxy | rfl | hxy := lt_trichotomy x y
    · exact c.condition ⟨⟨x, y⟩, hxy⟩
    · simp [h.fst_eq_snd]
    · have := c.condition ⟨⟨y, x⟩, hxy⟩
      dsimp at this ⊢
      rw [← h.iso_hom_fst_assoc]; rw [← h.iso_hom_snd_assoc]; rw [this])

Depends on / 依赖: Multicofork, Multicofork.of, c.condition, c.pt, condition, fst_eq_snd, h.fst_eq_snd, h.iso_hom_fst_assoc, h.iso_hom_snd_assoc, iso_hom_fst_assoc, iso_hom_snd_assoc, lt_trichotomy
-/
def ofLinearOrder (c : Multicofork I.toLinearOrder) (h : I.SymmStruct) :
    Multicofork I :=
  Multicofork.ofπ _ c.pt c.π (by
    rintro ⟨x, y⟩
    obtain hxy | rfl | hxy := lt_trichotomy x y
    · exact c.condition ⟨⟨x, y⟩, hxy⟩
    · simp [h.fst_eq_snd]
    · have := c.condition ⟨⟨y, x⟩, hxy⟩
      dsimp at this ⊢
      rw [← h.iso_hom_fst_assoc]; rw [← h.iso_hom_snd_assoc]; rw [this])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitToLinearOrder` / `isColimitToLinearOrder` 的定义

English:
definition isColimitToLinearOrder
  signature: (c : Multicofork I) (hc : IsColimit c) (h : I.SymmStruct)
  body: Multicofork.IsColimit.mk _ (fun s => hc.desc (ofLinearOrder s h))
    (fun s _ => hc.fac (ofLinearOrder s h) _)
    (fun s m hm => Multicofork.IsColimit.hom_ext hc (fun i => by
      have := hc.fac (ofLinearOrder s h) (.right i)
      dsimp at this
      rw [this]
      apply hm))

中文:
定义 isColimitToLinearOrder
  签名: (c : Multicofork I) (hc : 是余极限 c) (h : I.SymmStruct)
  定义体: Multicofork.IsColimit.mk _ (fun s => hc.desc (ofLinearOrder s h))
    (fun s _ => hc.fac (ofLinearOrder s h) _)
    (fun s m hm => Multicofork.IsColimit.hom_ext hc (fun i => by
      have := hc.fac (ofLinearOrder s h) (.right i)
      dsimp at this
      rw [this]
      apply hm))

Depends on / 依赖: IsColimit, Multicofork, Multicofork.IsColimit.hom_ext, Multicofork.IsColimit.mk, hc.desc, hc.fac, hom_ext, ofLinearOrder
-/
def isColimitToLinearOrder (c : Multicofork I) (hc : IsColimit c) (h : I.SymmStruct) :
    IsColimit c.toLinearOrder :=
  Multicofork.IsColimit.mk _ (fun s => hc.desc (ofLinearOrder s h))
    (fun s _ => hc.fac (ofLinearOrder s h) _)
    (fun s m hm => Multicofork.IsColimit.hom_ext hc (fun i => by
      have := hc.fac (ofLinearOrder s h) (.right i)
      dsimp at this
      rw [this]
      apply hm))

end Multicofork

end symmetry

end CategoryTheory.Limits
