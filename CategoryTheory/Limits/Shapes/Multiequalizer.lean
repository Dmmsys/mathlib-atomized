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
/-- The shape of a multiequalizer diagram. It involves two types `L` and `R`,
and two maps `R → L`. -/
/-
**CategoryTheory.Limits.MulticospanShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：Type (max (w + 1) (w' + 1))
参数：max (w + 1) (w' + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of a multiequalizer diagram. It involves two types `L` and `R`,
and two maps `R → L`.
-/
structure MulticospanShape where
  /-- the left type -/
  L : Type w
  /-- the right type -/
  R : Type w'
  /-- the first map `R → L` -/
  fst : R → L
  /-- the second map `R → L` -/
  snd : R → L

/-- Given a type `ι`, this is the shape of multiequalizer diagrams corresponding
to situations where we want to equalize two families of maps `U i ⟶ V ⟨i, j⟩`
and `U j ⟶ V ⟨i, j⟩` with `i : ι` and `j : ι`. -/
@[simps]
/-
**CategoryTheory.Limits.MulticospanShape.prod** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.MulticospanShape`。
形式化陈述：Type w → CategoryTheory.Limits.MulticospanShape
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a type `ι`, this is the shape of multiequalizer diagrams corresponding
to situations where we want to equalize two families of maps `U i ⟶ V ⟨i, j⟩`
and `U j ⟶ V ⟨i, j⟩` with `i : ι` and `j : ι`.
-/
def MulticospanShape.prod (ι : Type w) : MulticospanShape where
  L := ι
  R := ι × ι
  fst := _root_.Prod.fst
  snd := _root_.Prod.snd

set_option linter.checkUnivs false in
/-- The shape of a multicoequalizer diagram. It involves two types `L` and `R`,
and two maps `L → R`. -/
/-
**CategoryTheory.Limits.MultispanShape** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：Type (max (w + 1) (w' + 1))
参数：max (w + 1) (w' + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of a multicoequalizer diagram. It involves two types `L` and `R`,
and two maps `L → R`.
-/
structure MultispanShape where
  /-- the left type -/
  L : Type w
  /-- the right type -/
  R : Type w'
  /-- the first map `L → R` -/
  fst : L → R
  /-- the second map `L → R` -/
  snd : L → R

/-- Given a type `ι`, this is the shape of multicoequalizer diagrams corresponding
to situations where we want to coequalize two families of maps `V ⟨i, j⟩ ⟶ U i`
and `V ⟨i, j⟩ ⟶ U j` with `i : ι` and `j : ι`. -/
@[simps]
/-
**CategoryTheory.Limits.MultispanShape.prod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.MultispanShape`。
形式化陈述：Type w → CategoryTheory.Limits.MultispanShape
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a type `ι`, this is the shape of multicoequalizer diagrams corresponding
to situations where we want to coequalize two families of maps `V ⟨i, j⟩ ⟶ U i`
and `V ⟨i, j⟩ ⟶ U j` with `i : ι` and `j : ι`.
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
/-
**CategoryTheory.Limits.MultispanShape.ofLinearOrder** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.MultispanShape`。
形式化陈述：(ι : Type w) → [LinearOrder ι] → CategoryTheory.Limits.MultispanShape
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linearly ordered type `ι`, this is the shape of multicoequalizer diagram
s
corresponding to situations where we want to coequalize two families of maps
`V ⟨i, j⟩ ⟶ U i` and `V ⟨i, j⟩ ⟶ U j` with `i < j`.
-/
def MultispanShape.ofLinearOrder (ι : Type w) [LinearOrder ι] : MultispanShape where
  L := {x : ι × ι | x.1 < x.2}
  R := ι
  fst x := x.1.1
  snd x := x.1.2
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (MultispanShape.ofLinearOrder Bool).L where
  default := ⟨⟨False, True⟩, by simp⟩
  uniq := by rintro ⟨⟨(_ | _), (_ | _)⟩, _⟩ <;> tauto

/-- The type underlying the multiequalizer diagram. -/
/-
**CategoryTheory.Limits.WalkingMulticospan** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Limits`。
形式化陈述：CategoryTheory.Limits.MulticospanShape → Type (max w w')
参数：max w w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type underlying the multiequalizer diagram.
-/
inductive WalkingMulticospan (J : MulticospanShape.{w, w'}) : Type max w w'
  | left : J.L → WalkingMulticospan J
  | right : J.R → WalkingMulticospan J

/-- The type underlying the multicoequalizer diagram. -/
/-
**CategoryTheory.Limits.WalkingMultispan** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：CategoryTheory.Limits.MultispanShape → Type (max w w')
参数：max w w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type underlying the multicoequalizer diagram.
-/
inductive WalkingMultispan (J : MultispanShape.{w, w'}) : Type max w w'
  | left : J.L → WalkingMultispan J
  | right : J.R → WalkingMultispan J

namespace WalkingMulticospan

variable {J : MulticospanShape.{w, w'}}

/-
**CategoryTheory.Limits.WalkingMulticospan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits.WalkingMulticospan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited J.L] : Inhabited (WalkingMulticospan J) :=
  ⟨left default⟩

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- Morphisms for `WalkingMulticospan`. -/
/-
**CategoryTheory.Limits.WalkingMulticospan.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Limits.WalkingMulticospan`。
形式化陈述：{J : CategoryTheory.Limits.MulticospanShape} →   CategoryTheory.Limits.Wal
kingMulticospan J → CategoryTheory.Limits.WalkingMulticospan J → Type (max w w')
参数：max w w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms for `WalkingMulticospan`.
-/
inductive Hom : ∀ _ _ : WalkingMulticospan J, Type max w w'
  | id (A) : Hom A A
  | fst (b) : Hom (left (J.fst b)) (right b)
  | snd (b) : Hom (left (J.snd b)) (right b)
/-
**CategoryTheory.Limits.WalkingMulticospan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits.WalkingMulticospan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : WalkingMulticospan J} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

/-- Composition of morphisms for `WalkingMulticospan`. -/
/-
**CategoryTheory.Limits.WalkingMulticospan.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.WalkingMulticospan.Hom`。
形式化陈述：{J : CategoryTheory.Limits.MulticospanShape} →   {A B C : CategoryTheory.L
imits.WalkingMulticospan J} → A.Hom B → B.Hom C → A.Hom C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms for `WalkingMulticospan`.
-/
def Hom.comp : ∀ {A B C : WalkingMulticospan J} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst b, Hom.id _ => Hom.fst b
  | _, _, _, Hom.snd b, Hom.id _ => Hom.snd b
/-
**CategoryTheory.Limits.WalkingMulticospan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits.WalkingMulticospan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Limits.WalkingMulticospan.Hom.id_eq_id** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.WalkingMulticospan.Hom`。
形式化陈述：∀ {J : CategoryTheory.Limits.MulticospanShape} (X : CategoryTheory.Limits.
WalkingMulticospan J),   CategoryTheory.Limits.WalkingMulticospan.Hom.id X = Cat
egoryTheory.CategoryStruct.id X
参数：X : CategoryTheory.Limits.WalkingMulticospan J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.id_eq_id (X : WalkingMulticospan J) :
    Hom.id X = 𝟙 X := rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingMulticospan.Hom.comp_eq_comp** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.WalkingMulticospan.Hom`。
形式化陈述：∀ {J : CategoryTheory.Limits.MulticospanShape} {X Y Z : CategoryTheory.Lim
its.WalkingMulticospan J} (f : X ⟶ Y)   (g : Y ⟶ Z), CategoryTheory.Limits.Walki
ngMulticospan.Hom.comp f g = CategoryTheory.CategoryStruct.comp f g
参数：f : X ⟶ Y；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.comp_eq_comp {X Y Z : WalkingMulticospan J}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

/-- Construct a natural isomorphism between functors out of a walking multicospan from its
components. -/
@[simps!]
/-
**CategoryTheory.Limits.WalkingMulticospan.functorExt** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.WalkingMulticospan`。
形式化陈述：functorExt {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C} (lef
t : forall i, F.obj (.left i) ≅ G.obj (.left i)) (right : forall i, F.obj (.righ
t i) ≅ G.obj (.right i)) (wl : forall i, F.map (WalkingMulticospan.Hom.fst i) ≫ 
(right i).hom = (left _).hom ≫ G.map (WalkingMulticospan.Hom.fst i)
参数：left : forall i, F.obj (.left i) ≅ G.obj (.left i)；right : forall i, F.obj (.
right i) ≅ G.obj (.right i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a natural isomorphism between functors out of a walking multicospan fr
om its
components.
-/
def functorExt {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
    (left : ∀ i, F.obj (.left i) ≅ G.obj (.left i))
    (right : ∀ i, F.obj (.right i) ≅ G.obj (.right i))
    (wl : ∀ i, F.map (WalkingMulticospan.Hom.fst i) ≫ (right i).hom =
      (left _).hom ≫ G.map (WalkingMulticospan.Hom.fst i) := by cat_disch)
    (wr : ∀ i, F.map (WalkingMulticospan.Hom.snd i) ≫ (right i).hom =
      (left _).hom ≫ G.map (WalkingMulticospan.Hom.snd i) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents (fun j ↦ match j with | .left i => left i | .right i => right i) <| by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Limits.WalkingMulticospan.functor_ext** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits.WalkingMulticospan`。
形式化陈述：functor_ext {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C} (le
ft : forall i, F.obj (.left i) = G.obj (.left i)) (right : forall i, F.obj (.rig
ht i) = G.obj (.right i)) (wl : forall i, F.map (Hom.fst i) ≫ eqToHom (right i) 
= eqToHom (left _) ≫ G.map (Hom.fst i)) (wr : forall i, F.map (Hom.snd i) ≫ eqTo
Hom (right i) = eqToHom (left _) ≫ G.map (Hom.snd i)) : F = G
参数：left : forall i, F.obj (.left i) = G.obj (.left i)；right : forall i, F.obj (.
right i) = G.obj (.right i)；wl : forall i, F.map (Hom.fst i) ≫ eqToHom (right i)
 = eqToHom (left _) ≫ G.map (Hom.fst i)；wr : forall i, F.map (Hom.snd i) ≫ eqToH
om (right i) = eqToHom (left _) ≫ G.map (Hom.snd i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.WalkingMulticospan.functorExt_hom_app`：∀ {J : Cate
goryTheory.Limits.MulticospanShape} {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C]   {F G : CategoryTheory.Functor …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functor_ext {C : Type*} [Category* C] {F G : WalkingMulticospan J ⥤ C}
    (left : ∀ i, F.obj (.left i) = G.obj (.left i))
    (right : ∀ i, F.obj (.right i) = G.obj (.right i))
    (wl : ∀ i, F.map (Hom.fst i) ≫ eqToHom (right i) = eqToHom (left _) ≫ G.map (Hom.fst i))
    (wr : ∀ i, F.map (Hom.snd i) ≫ eqToHom (right i) = eqToHom (left _) ≫ G.map (Hom.snd i)) :
    F = G :=
  Functor.ext_of_iso
    (functorExt (fun _ ↦ eqToIso (left _)) (fun _ ↦ eqToIso (right _)) wl wr)
    (by rintro (_ | _) <;> grind) (by rintro (_ | _) <;> simp)

end WalkingMulticospan

namespace WalkingMultispan

variable {J : MultispanShape.{w, w'}}

/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited J.L] : Inhabited (WalkingMultispan J) :=
  ⟨left default⟩
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{t} J.L] [Small.{t} J.R] : Small.{t} (WalkingMultispan J) :=
  small_of_surjective (f := Sum.elim WalkingMultispan.left WalkingMultispan.right)
    (by rintro (_ | _) <;> aesop)

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- Morphisms for `WalkingMultispan`. -/
/-
**CategoryTheory.Limits.WalkingMultispan.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Limits.WalkingMultispan`。
形式化陈述：{J : CategoryTheory.Limits.MultispanShape} →   CategoryTheory.Limits.Walki
ngMultispan J → CategoryTheory.Limits.WalkingMultispan J → Type (max w w')
参数：max w w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms for `WalkingMultispan`.
-/
inductive Hom : ∀ _ _ : WalkingMultispan J, Type max w w'
  | id (A) : Hom A A
  | fst (a) : Hom (left a) (right (J.fst a))
  | snd (a) : Hom (left a) (right (J.snd a))
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {a : WalkingMultispan J} : Inhabited (Hom a a) :=
  ⟨Hom.id _⟩

/-- Composition of morphisms for `WalkingMultispan`. -/
/-
**CategoryTheory.Limits.WalkingMultispan.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.WalkingMultispan.Hom`。
形式化陈述：{J : CategoryTheory.Limits.MultispanShape} →   {A B C : CategoryTheory.Lim
its.WalkingMultispan J} → A.Hom B → B.Hom C → A.Hom C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms for `WalkingMultispan`.
-/
def Hom.comp : ∀ {A B C : WalkingMultispan J} (_ : Hom A B) (_ : Hom B C), Hom A C
  | _, _, _, Hom.id X, f => f
  | _, _, _, Hom.fst a, Hom.id _ => Hom.fst a
  | _, _, _, Hom.snd a, Hom.id _ => Hom.snd a
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Limits.WalkingMultispan.Hom.id_eq_id** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.WalkingMultispan.Hom`。
形式化陈述：∀ {J : CategoryTheory.Limits.MultispanShape} (X : CategoryTheory.Limits.Wa
lkingMultispan J),   CategoryTheory.Limits.WalkingMultispan.Hom.id X = CategoryT
heory.CategoryStruct.id X
参数：X : CategoryTheory.Limits.WalkingMultispan J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.id_eq_id (X : WalkingMultispan J) : Hom.id X = 𝟙 X := rfl

@[simp]
/-
**CategoryTheory.Limits.WalkingMultispan.Hom.comp_eq_comp** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.WalkingMultispan.Hom`。
形式化陈述：∀ {J : CategoryTheory.Limits.MultispanShape} {X Y Z : CategoryTheory.Limit
s.WalkingMultispan J} (f : X ⟶ Y) (g : Y ⟶ Z),   CategoryTheory.Limits.WalkingMu
ltispan.Hom.comp f g = CategoryTheory.CategoryStruct.comp f g
参数：f : X ⟶ Y；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.comp_eq_comp {X Y Z : WalkingMultispan J}
    (f : X ⟶ Y) (g : Y ⟶ Z) : Hom.comp f g = f ≫ g := rfl

/-- Construct a natural isomorphism between functors out of a walking multispan from its
components. -/
@[simps!]
/-
**CategoryTheory.Limits.WalkingMultispan.functorExt** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.WalkingMultispan`。
形式化陈述：functorExt {C : Type*} [Category* C] {F G : WalkingMultispan J ⥤ C} (left 
: forall i, F.obj (.left i) ≅ G.obj (.left i)) (right : forall i, F.obj (.right 
i) ≅ G.obj (.right i)) (wl : forall i, F.map (WalkingMultispan.Hom.fst i) ≫ (rig
ht _).hom = (left i).hom ≫ G.map (WalkingMultispan.Hom.fst _)
参数：left : forall i, F.obj (.left i) ≅ G.obj (.left i)；right : forall i, F.obj (.
right i) ≅ G.obj (.right i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a natural isomorphism between functors out of a walking multispan from
 its
components.
-/
def functorExt {C : Type*} [Category* C] {F G : WalkingMultispan J ⥤ C}
    (left : ∀ i, F.obj (.left i) ≅ G.obj (.left i))
    (right : ∀ i, F.obj (.right i) ≅ G.obj (.right i))
    (wl : ∀ i, F.map (WalkingMultispan.Hom.fst i) ≫ (right _).hom =
      (left i).hom ≫ G.map (WalkingMultispan.Hom.fst _) := by cat_disch)
    (wr : ∀ i, F.map (WalkingMultispan.Hom.snd i) ≫ (right _).hom =
      (left i).hom ≫ G.map (WalkingMultispan.Hom.snd _) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents (fun j ↦ match j with | .left i => left i | .right i => right i) <| by
    rintro _ _ ⟨_⟩ <;> simp [wl, wr]
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : WalkingMultispan J) : Unique (a ⟶ a) where
  default := 𝟙 _
  uniq := by rintro ⟨⟩; rfl
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : J.L) : Subsingleton (left a ⟶ left b) := by
  by_cases h : a = b
  · subst h
    infer_instance
  · have : IsEmpty (left a ⟶ left b) := ⟨by rintro ⟨⟩; simp at h⟩
    infer_instance
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a b : J.R) : Subsingleton (right a ⟶ right b) := by
  by_cases h : a = b
  · subst h
    infer_instance
  · have : IsEmpty (right a ⟶ right b) := ⟨by rintro ⟨⟩; simp at h⟩
    infer_instance
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : J.R) (b : J.L) : IsEmpty (right a ⟶ left b) := ⟨by rintro ⟨⟩⟩
/-
**CategoryTheory.Limits.WalkingMultispan.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.WalkingMultispan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LocallySmall.{t} (WalkingMultispan J) where
  hom_small := by
    rintro (l | r) (l' | r')
    · infer_instance
    · let T₁ := { u : Unit // J.fst l = r' }
      let T₂ := { u : Unit // J.snd l = r' }
      let f : T₁ ⊕ T₂ → (left l ⟶ right r') :=
        Sum.elim (fun ⟨_, h⟩ ↦ by subst h; exact Hom.fst l)
          (fun ⟨_, h⟩ ↦ by subst h; exact Hom.snd l)
      refine small_of_surjective (f := f) ?_
      rintro (_ | _)
      · exact ⟨Sum.inl ⟨⟨⟩, rfl⟩, rfl⟩
      · exact ⟨Sum.inr ⟨⟨⟩, rfl⟩, rfl⟩
    · infer_instance
    · infer_instance

variable (J) in
/-- The bijection `WalkingMultispan J ≃ J.L ⊕ J.R`. -/
/-
**CategoryTheory.Limits.WalkingMultispan.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.WalkingMultispan`。
形式化陈述：equiv : WalkingMultispan J ≃ J.L oplus J.R where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `WalkingMultispan J ≃ J.L ⊕ J.R`.
-/
def equiv : WalkingMultispan J ≃ J.L ⊕ J.R where
  toFun x := match x with
    | left a => Sum.inl a
    | right b => Sum.inr b
  invFun := Sum.elim left right
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

variable (J) in
/-- The bijection `Arrow (WalkingMultispan J) ≃ WalkingMultispan J ⊕ J.R ⊕ J.R`. -/
/-
**CategoryTheory.Limits.WalkingMultispan.arrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.WalkingMultispan`。
形式化陈述：arrowEquiv : Arrow (WalkingMultispan J) ≃ WalkingMultispan J oplus J.L opl
us J.L where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `Arrow (WalkingMultispan J) ≃ WalkingMultispan J ⊕ J.R ⊕ J.R`.
-/
def arrowEquiv :
    Arrow (WalkingMultispan J) ≃ WalkingMultispan J ⊕ J.L ⊕ J.L where
  toFun f := match f.hom with
    | .id x => Sum.inl x
    | .fst a => Sum.inr (Sum.inl a)
    | .snd a => Sum.inr (Sum.inr a)
  invFun :=
    Sum.elim (fun X ↦ Arrow.mk (𝟙 X))
      (Sum.elim (fun a ↦ Arrow.mk (Hom.fst a : left _ ⟶ right _))
        (fun a ↦ Arrow.mk (Hom.snd a : left _ ⟶ right _)))
  left_inv := by rintro ⟨_, _, (_ | _ | _)⟩ <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

end WalkingMultispan

/-- This is a structure encapsulating the data necessary to define a `Multicospan`. -/
/-
**CategoryTheory.Limits.MulticospanIndex** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：CategoryTheory.Limits.MulticospanShape →   (C : Type u) → [CategoryTheory.
Category.{v, u} C] → Type (max (max (max u v) w) w')
参数：C : Type u；max (max (max u v) w) w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a structure encapsulating the data necessary to define a `Multicospan`.
-/
structure MulticospanIndex (J : MulticospanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  /-- Left map, from `J.L` to `C` -/
  left : J.L → C
  /-- Right map, from `J.R` to `C` -/
  right : J.R → C
  /-- A family of maps from `left (J.fst b)` to `right b` -/
  fst : ∀ b, left (J.fst b) ⟶ right b
  /-- A family of maps from `left (J.snd b)` to `right b` -/
  snd : ∀ b, left (J.snd b) ⟶ right b

/-- This is a structure encapsulating the data necessary to define a `Multispan`. -/
/-
**CategoryTheory.Limits.MultispanIndex** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：CategoryTheory.Limits.MultispanShape →   (C : Type u) → [CategoryTheory.Ca
tegory.{v, u} C] → Type (max (max (max u v) w) w')
参数：C : Type u；max (max (max u v) w) w'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a structure encapsulating the data necessary to define a `Multispan`.
-/
structure MultispanIndex (J : MultispanShape.{w, w'})
    (C : Type u) [Category.{v} C] where
  /-- Left map, from `J.L` to `C` -/
  left : J.L → C
  /-- Right map, from `J.R` to `C` -/
  right : J.R → C
  /-- A family of maps from `left a` to `right (J.fst a)` -/
  fst : ∀ a, left a ⟶ right (J.fst a)
  /-- A family of maps from `left a` to `right (J.snd a)` -/
  snd : ∀ a, left a ⟶ right (J.snd a)

namespace MulticospanIndex

variable {C : Type u} [Category.{v} C] {J : MulticospanShape.{w, w'}}
  (I : MulticospanIndex J C)

/-- The multicospan associated to `I : MulticospanIndex`. -/
/-
**CategoryTheory.Limits.MulticospanIndex.multicospan** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multicospan : WalkingMulticospan J ⥤ C where obj x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicospan associated to `I : MulticospanIndex`.
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
/-
**CategoryTheory.Limits.MulticospanIndex.multicospan_obj_left** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multicospan_obj_left (a) : I.multicospan.obj (WalkingMulticospan.left a) =
 I.left a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multicospan_obj_left (a) : I.multicospan.obj (WalkingMulticospan.left a) = I.left a :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.MulticospanIndex.multicospan_obj_right** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multicospan_obj_right (b) : I.multicospan.obj (WalkingMulticospan.right b)
 = I.right b
参数：b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multicospan_obj_right (b) : I.multicospan.obj (WalkingMulticospan.right b) = I.right b :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.MulticospanIndex.multicospan_map_fst** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multicospan_map_fst (a) : I.multicospan.map (WalkingMulticospan.Hom.fst a)
 = I.fst a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multicospan_map_fst (a) : I.multicospan.map (WalkingMulticospan.Hom.fst a) = I.fst a :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.MulticospanIndex.multicospan_map_snd** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multicospan_map_snd (a) : I.multicospan.map (WalkingMulticospan.Hom.snd a)
 = I.snd a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multicospan_map_snd (a) : I.multicospan.map (WalkingMulticospan.Hom.snd a) = I.snd a :=
  rfl

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.fst` for limiting fans. -/
/-
**CategoryTheory.Limits.MulticospanIndex.fstPiMapOfIsLimit** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：fstPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.
pt ⟶ d.pt
参数：c : Fan I.left；hd : IsLimit d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.fst` for limiting fans.
-/
def fstPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.pt ⟶ d.pt :=
  Fan.IsLimit.lift hd fun i ↦ c.proj _ ≫ I.fst i

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.snd` for limiting fans. -/
/-
**CategoryTheory.Limits.MulticospanIndex.sndPiMapOfIsLimit** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：sndPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.
pt ⟶ d.pt
参数：c : Fan I.left；hd : IsLimit d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.snd` for limiting fans.
-/
def sndPiMapOfIsLimit (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : c.pt ⟶ d.pt :=
  Fan.IsLimit.lift hd fun i ↦ c.proj _ ≫ I.snd i

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MulticospanIndex.fstPiMapOfIsLimit_proj** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：fstPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d)
 (i) : fstPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.fst i
参数：c : Fan I.left；hd : IsLimit d；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Fan.IsLimit.fac`：∀ {β : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.Fan 
F}   (hc : CategoryTheory.L…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fstPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) :
    fstPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.fst i := by
  simp [fstPiMapOfIsLimit]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MulticospanIndex.sndPiMapOfIsLimit_proj** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：sndPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d)
 (i) : sndPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.snd i
参数：c : Fan I.left；hd : IsLimit d；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Fan.IsLimit.fac`：∀ {β : Type w} {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.Fan 
F}   (hc : CategoryTheory.L…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sndPiMapOfIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) :
    sndPiMapOfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.snd i := by
  simp [sndPiMapOfIsLimit]

/-- Taking the multiequalizer over the multicospan index is equivalent to taking the equalizer over
the two morphisms `∏ᶜ I.left ⇉ ∏ᶜ I.right`. This is the diagram of the latter for limiting fans.
-/
@[simps!]
/-
**CategoryTheory.Limits.MulticospanIndex.parallelPairDiagramOfIsLimit** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MulticospanShape} →       (I : CategoryTheory.Limits.Multicosp
anIndex J C) →         CategoryTheory.Limits.Fan I.left →           {d : Categor
yTheory.Limits.Fan I.right} →             CategoryTheory.Limits.IsLimit d → Cate
goryTheory.Functor CategoryTheory.Limits.WalkingParallelPair C
参数：I : CategoryTheory.Limits.MulticospanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the multiequalizer over the multicospan index is equivalent to taking the
 equalizer over
the two morphisms `∏ᶜ I.left ⇉ ∏ᶜ I.right`. This is the diagram of the latter fo
r limiting fans.
-/
protected noncomputable def parallelPairDiagramOfIsLimit
    (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) : WalkingParallelPair ⥤ C :=
  parallelPair (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)

variable [HasProduct I.left] [HasProduct I.right]

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.fst`. -/
/-
**CategoryTheory.Limits.MulticospanIndex.fstPiMap** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.MulticospanIndex`。
形式化陈述：fstPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.fst`.
-/
noncomputable def fstPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  I.fstPiMapOfIsLimit _ <| limit.isLimit (Discrete.functor I.right)

/-- The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.snd`. -/
/-
**CategoryTheory.Limits.MulticospanIndex.sndPiMap** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.MulticospanIndex`。
形式化陈述：sndPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∏ᶜ I.left ⟶ ∏ᶜ I.right` via `I.snd`.
-/
noncomputable def sndPiMap : ∏ᶜ I.left ⟶ ∏ᶜ I.right :=
  I.sndPiMapOfIsLimit _ <| limit.isLimit (Discrete.functor I.right)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MulticospanIndex.fstPiMap_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.MulticospanIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fstPiMap_π (b) : I.fstPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.fst b :=
  fstPiMapOfIsLimit_proj ..

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MulticospanIndex.sndPiMap_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.MulticospanIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sndPiMap_π (b) : I.sndPiMap ≫ Pi.π I.right b = Pi.π I.left _ ≫ I.snd b :=
  sndPiMapOfIsLimit_proj ..

/-- Taking the multiequalizer over the multicospan index is equivalent to taking the equalizer over
the two morphisms `∏ᶜ I.left ⇉ ∏ᶜ I.right`. This is the diagram of the latter.
-/
@[simps!]
/-
**CategoryTheory.Limits.MulticospanIndex.parallelPairDiagram** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MulticospanShape} →       (I : CategoryTheory.Limits.Multicosp
anIndex J C) →         [CategoryTheory.Limits.HasProduct I.left] →           [Ca
tegoryTheory.Limits.HasProduct I.right] →             CategoryTheory.Functor Cat
egoryTheory.Limits.WalkingParallelPair C
参数：I : CategoryTheory.Limits.MulticospanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the multiequalizer over the multicospan index is equivalent to taking the
 equalizer over
the two morphisms `∏ᶜ I.left ⇉ ∏ᶜ I.right`. This is the diagram of the latter.
-/
protected noncomputable def parallelPairDiagram :=
  parallelPair I.fstPiMap I.sndPiMap

end MulticospanIndex

namespace MultispanIndex

variable {C : Type u} [Category.{v} C] {J : MultispanShape.{w, w'}}
    (I : MultispanIndex J C)

/-- The multispan associated to `I : MultispanIndex`. -/
/-
**CategoryTheory.Limits.MultispanIndex.multispan** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.MultispanIndex`。
形式化陈述：multispan : WalkingMultispan J ⥤ C where obj x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multispan associated to `I : MultispanIndex`.
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
/-
**CategoryTheory.Limits.MultispanIndex.multispan_obj_left** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：multispan_obj_left (a) : I.multispan.obj (WalkingMultispan.left a) = I.lef
t a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multispan_obj_left (a) : I.multispan.obj (WalkingMultispan.left a) = I.left a :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.MultispanIndex.multispan_obj_right** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：multispan_obj_right (b) : I.multispan.obj (WalkingMultispan.right b) = I.r
ight b
参数：b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multispan_obj_right (b) : I.multispan.obj (WalkingMultispan.right b) = I.right b :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.MultispanIndex.multispan_map_fst** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：multispan_map_fst (a) : I.multispan.map (WalkingMultispan.Hom.fst a) = I.f
st a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multispan_map_fst (a) : I.multispan.map (WalkingMultispan.Hom.fst a) = I.fst a :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.MultispanIndex.multispan_map_snd** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：multispan_map_snd (a) : I.multispan.map (WalkingMultispan.Hom.snd a) = I.s
nd a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multispan_map_snd (a) : I.multispan.map (WalkingMultispan.Hom.snd a) = I.snd a :=
  rfl

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.fst` for colimiting cofans. -/
/-
**CategoryTheory.Limits.MultispanIndex.fstSigmaMapOfIsColimit** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColi
mit c) : c.pt ⟶ d.pt
参数：d : Cofan I.right；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∐ I.left ⟶ ∐ I.right` via `I.fst` for colimiting cofans.
-/
def fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) :
    c.pt ⟶ d.pt :=
  Cofan.IsColimit.desc hc fun i ↦ I.fst i ≫ d.inj _

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd` for colimiting cofans. -/
/-
**CategoryTheory.Limits.MultispanIndex.sndSigmaMapOfIsColimit** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColi
mit c) : c.pt ⟶ d.pt
参数：d : Cofan I.right；hc : IsColimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd` for colimiting cofans.
-/
def sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) :
    c.pt ⟶ d.pt :=
  Cofan.IsColimit.desc hc fun i ↦ I.snd i ≫ d.inj _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MultispanIndex.inj_fstSigmaMapOfIsColimit** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：inj_fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : Is
Colimit c) (i) : c.inj _ ≫ fstSigmaMapOfIsColimit I d hc = I.fst i ≫ d.inj _
参数：d : Cofan I.right；hc : IsColimit c；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inj_fstSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i) :
    c.inj _ ≫ fstSigmaMapOfIsColimit I d hc = I.fst i ≫ d.inj _ := by
  simp [fstSigmaMapOfIsColimit]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MultispanIndex.inj_sndSigmaMapOfIsColimit** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：inj_sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : Is
Colimit c) (i) : c.inj _ ≫ sndSigmaMapOfIsColimit I d hc = I.snd i ≫ d.inj _
参数：d : Cofan I.right；hc : IsColimit c；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inj_sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) (i) :
    c.inj _ ≫ sndSigmaMapOfIsColimit I d hc = I.snd i ≫ d.inj _ := by
  simp [sndSigmaMapOfIsColimit]

/-- Taking the multicoequalizer over the multispan index is equivalent to taking the coequalizer
over the two morphisms `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter for colimiting
cofans. -/
@[simps!]
/-
**CategoryTheory.Limits.MultispanIndex.parallelPairDiagramOfIsColimit** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MultispanShape} →       (I : CategoryTheory.Limits.MultispanIn
dex J C) →         {c : CategoryTheory.Limits.Cofan I.left} →           Category
Theory.Limits.Cofan I.right →             CategoryTheory.Limits.IsColimit c → Ca
tegoryTheory.Functor CategoryTheory.Limits.WalkingParallelPair C
参数：I : CategoryTheory.Limits.MultispanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the multicoequalizer over the multispan index is equivalent to taking the
 coequalizer
over the two morphisms `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter
 for colimiting
cofans.
-/
protected noncomputable def parallelPairDiagramOfIsColimit
    {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) : WalkingParallelPair ⥤ C :=
  parallelPair (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)

variable [HasCoproduct I.left] [HasCoproduct I.right]

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.fst`. -/
/-
**CategoryTheory.Limits.MultispanIndex.fstSigmaMap** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.MultispanIndex`。
形式化陈述：fstSigmaMap : ∐ I.left ⟶ ∐ I.right
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∐ I.left ⟶ ∐ I.right` via `I.fst`.
-/
noncomputable def fstSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  I.fstSigmaMapOfIsColimit _ <| colimit.isColimit _

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd`. -/
/-
**CategoryTheory.Limits.MultispanIndex.sndSigmaMap** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.MultispanIndex`。
形式化陈述：sndSigmaMap : ∐ I.left ⟶ ∐ I.right
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd`.
-/
noncomputable def sndSigmaMap : ∐ I.left ⟶ ∐ I.right :=
  I.sndSigmaMapOfIsColimit _ <| colimit.isColimit _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MultispanIndex.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.MultispanIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_fstSigmaMap (b) : Sigma.ι I.left b ≫ I.fstSigmaMap = I.fst b ≫ Sigma.ι I.right _ :=
  inj_fstSigmaMapOfIsColimit ..

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.MultispanIndex.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.MultispanIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_sndSigmaMap (b) : Sigma.ι I.left b ≫ I.sndSigmaMap = I.snd b ≫ Sigma.ι I.right _ :=
  inj_sndSigmaMapOfIsColimit ..

/--
Taking the multicoequalizer over the multispan index is equivalent to taking the coequalizer over
the two morphisms `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter.
-/
/-
**CategoryTheory.Limits.MultispanIndex.parallelPairDiagram** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MultispanShape} →       (I : CategoryTheory.Limits.MultispanIn
dex J C) →         [CategoryTheory.Limits.HasCoproduct I.left] →           [Cate
goryTheory.Limits.HasCoproduct I.right] →             CategoryTheory.Functor Cat
egoryTheory.Limits.WalkingParallelPair C
参数：I : CategoryTheory.Limits.MultispanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the multicoequalizer over the multispan index is equivalent to taking the
 coequalizer over
the two morphisms `∐ I.left ⇉ ∐ I.right`. This is the diagram of the latter.
-/
protected noncomputable abbrev parallelPairDiagram :=
  parallelPair I.fstSigmaMap I.sndSigmaMap

end MultispanIndex

variable {C : Type u} [Category.{v} C]

/-- A multifork is a cone over a multicospan. -/
/-
**CategoryTheory.Limits.Multifork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：Multifork {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
参数：I : MulticospanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multifork is a cone over a multicospan.
-/
abbrev Multifork {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :=
  Cone I.multicospan

/-- A multicofork is a cocone over a multispan. -/
/-
**CategoryTheory.Limits.Multicofork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：Multicofork {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
参数：I : MultispanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multicofork is a cocone over a multispan.
-/
abbrev Multicofork {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) :=
  Cocone I.multispan

namespace Multifork

variable {J : MulticospanShape.{w, w'}} {I : MulticospanIndex J C} (K : Multifork I)

/-- The maps from the cone point of a multifork to the objects on the left. -/
/-
**CategoryTheory.Limits.Multifork.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maps from the cone point of a multifork to the objects on the left.
-/
def ι (a : J.L) : K.pt ⟶ I.left a :=
  K.π.app (WalkingMulticospan.left _)

@[simp]
/-
**CategoryTheory.Limits.Multifork.app_left_eq_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_left_eq_ι (a) : K.π.app (WalkingMulticospan.left a) = K.ι a :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Multifork.app_right_eq_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_right_eq_ι_comp_fst (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (J.fst b) ≫ I.fst b := by
  rw [← K.w (WalkingMulticospan.Hom.fst b)]
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.Multifork.app_right_eq_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_right_eq_ι_comp_snd (b) :
    K.π.app (WalkingMulticospan.right b) = K.ι (J.snd b) ≫ I.snd b := by
  rw [← K.w (WalkingMulticospan.Hom.snd b)]
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multifork.hom_comp_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_comp_ι (K₁ K₂ : Multifork I) (f : K₁ ⟶ K₂) (j : J.L) : f.hom ≫ K₂.ι j = K₁.ι j :=
  f.w _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct a multifork using a collection `ι` of morphisms. -/
@[simps]
/-
**CategoryTheory.Limits.Multifork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a multifork using a collection `ι` of morphisms.
-/
def ofι {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    (P : C) (ι : ∀ a, P ⟶ I.left a)
    (w : ∀ b, ι (J.fst b) ≫ I.fst b = ι (J.snd b) ≫ I.snd b) : Multifork I where
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
/-
**CategoryTheory.Limits.Multifork.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_ofι {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    (P : C) (ι : ∀ a, P ⟶ I.left a)
    (w : ∀ b, ι (J.fst b) ≫ I.fst b = ι (J.snd b) ≫ I.snd b) (i) :
    (ofι I P ι w).ι i = ι i :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multifork.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Multifork`。
形式化陈述：condition (b) : K.ι (J.fst b) ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b
参数：b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Multifork.app_right_eq_ι_comp_fst`：app_right_eq_ι_
comp_fst (b) : K.π.app (WalkingMulticospan.right b) = K.ι (J.fst b) ≫ I.fst b
· 使用定理 `CategoryTheory.Limits.Multifork.app_right_eq_ι_comp_snd`：app_right_eq_ι_
comp_snd (b) : K.π.app (WalkingMulticospan.right b) = K.ι (J.snd b) ≫ I.snd b
-/
theorem condition (b) : K.ι (J.fst b) ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b := by
  rw [← app_right_eq_ι_comp_fst, ← app_right_eq_ι_comp_snd]

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for isomorphisms between multiforks. -/
@[simps!]
/-
**CategoryTheory.Limits.Multifork.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Multifork`。
形式化陈述：ext {t s : Multifork I} (e : t.pt ≅ s.pt) (h : forall i : J.L, e.hom ≫ s.ι
 i = t.ι i
参数：e : t.pt ≅ s.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms between multiforks.
-/
def ext {t s : Multifork I} (e : t.pt ≅ s.pt)
    (h : ∀ i : J.L, e.hom ≫ s.ι i = t.ι i := by cat_disch) : t ≅ s :=
  Cone.ext e (by rintro (i | j) <;> simp [← h])

set_option backward.defeqAttrib.useBackward true in
/-- Every multifork is isomorphic to one of the form `Multifork.ofι`. -/
@[simps!]
/-
**CategoryTheory.Limits.Multifork.isoOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every multifork is isomorphic to one of the form `Multifork.ofι`.
-/
def isoOfι (t : Multifork I) : t ≅ ofι _ t.pt t.ι t.condition :=
  ext (Iso.refl _)

/-- This definition provides a convenient way to show that a multifork is a limit. -/
@[simps]
/-
**CategoryTheory.Limits.Multifork.IsLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Multifork.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MulticospanShape} →       {I : CategoryTheory.Limits.Multicosp
anIndex J C} →         (K : CategoryTheory.Limits.Multifork I) →           (lift
 : (E : CategoryTheory.Limits.Multifork I) → E.pt ⟶ K.pt) →             (∀ (E : 
CategoryTheory.Limits.Multifork I) (i : J.L),                 CategoryTheory.Cat
egoryStruct.comp (lift E) (K.ι i) = E.ι i) →               (∀ (E : CategoryTheor
y.Limits.Multifork I) (m : E.pt ⟶ K.pt),                   (∀ (i : J.L), Categor
yTheory.CategoryStruct.comp m (K.ι i) = E.ι i) → m = lift E) →                 C
ategoryTheory.Limits.IsLimit K
参数：K : CategoryTheory.Limits.Multifork I；lift : (E : CategoryTheory.Limits.Multi
fork I) → E.pt ⟶ K.pt；∀ (E : CategoryTheory.Limits.Multifork I) (i : J.L),      
           CategoryTheory.CategoryStruct.comp (lift E) (K.ι i) = E.ι i；∀ (E : Ca
tegoryTheory.Limits.Multifork I) (m : E.pt ⟶ K.pt),                   (∀ (i : J.
L), CategoryTheory.CategoryStruct.comp m (K.ι i) = E.ι i) → m = lift E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition provides a convenient way to show that a multifork is a limit.
-/
def IsLimit.mk (lift : ∀ E : Multifork I, E.pt ⟶ K.pt)
    (fac : ∀ (E : Multifork I) (i : J.L), lift E ≫ K.ι i = E.ι i)
    (uniq : ∀ (E : Multifork I) (m : E.pt ⟶ K.pt), (∀ i : J.L, m ≫ K.ι i = E.ι i) → m = lift E) :
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
/-
**CategoryTheory.Limits.Multifork.IsLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Multifork.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.Limits.MulticospanShape}   {I : CategoryTheory.Limits.MulticospanIndex J C} {
K : CategoryTheory.Limits.Multifork I}   (hK : CategoryTheory.Limits.IsLimit K) 
{T : C} {f g : T ⟶ K.pt},   (∀ (a : J.L), CategoryTheory.CategoryStruct.comp f (
K.ι a) = CategoryTheory.CategoryStruct.comp g (K.ι a)) → f = g
参数：hK : CategoryTheory.Limits.IsLimit K；∀ (a : J.L), CategoryTheory.CategoryStru
ct.comp f (K.ι a) = CategoryTheory.CategoryStruct.comp g (K.ι a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Multifork.app_right_eq_ι_comp_fst`：app_right_eq_ι_
comp_fst (b) : K.π.app (WalkingMulticospan.right b) = K.ι (J.fst b) ≫ I.fst b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma IsLimit.hom_ext (hK : IsLimit K) {T : C} {f g : T ⟶ K.pt}
    (h : ∀ a, f ≫ K.ι a = g ≫ K.ι a) : f = g := by
  apply hK.hom_ext
  rintro (_ | b)
  · apply h
  · dsimp
    rw [app_right_eq_ι_comp_fst, reassoc_of% h]

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for morphisms to the point of a limit multifork. -/
/-
**CategoryTheory.Limits.Multifork.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Multifork.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MulticospanShape} →       {I : CategoryTheory.Limits.Multicosp
anIndex J C} →         {K : CategoryTheory.Limits.Multifork I} →           Categ
oryTheory.Limits.IsLimit K →             {T : C} →               (k : (a : J.L) 
→ T ⟶ I.left a) →                 (∀ (b : J.R),                     CategoryTheo
ry.CategoryStruct.comp (k (J.fst b)) (I.fst b) =                       CategoryT
heory.CategoryStruct.comp (k (J.snd b)) (I.snd b)) →                   (T ⟶ K.pt
)
参数：k : (a : J.L) → T ⟶ I.left a；∀ (b : J.R),                     CategoryTheory.
CategoryStruct.comp (k (J.fst b)) (I.fst b) =                       CategoryTheo
ry.CategoryStruct.comp (k (J.snd b)) (I.snd b)；T ⟶ K.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to the point of a limit multifork.
-/
def IsLimit.lift (hK : IsLimit K) {T : C} (k : ∀ a, T ⟶ I.left a)
    (hk : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) :
    T ⟶ K.pt :=
  hK.lift (Multifork.ofι _ _ k hk)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multifork.IsLimit.fac** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.Multifork.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.Limits.MulticospanShape}   {I : CategoryTheory.Limits.MulticospanIndex J C} {
K : CategoryTheory.Limits.Multifork I}   (hK : CategoryTheory.Limits.IsLimit K) 
{T : C} (k : (a : J.L) → T ⟶ I.left a)   (hk :     ∀ (b : J.R),       CategoryTh
eory.CategoryStruct.comp (k (J.fst b)) (I.fst b) =         CategoryTheory.Catego
ryStruct.comp (k (J.snd b)) (I.snd b))   (a : J.L), CategoryTheory.CategoryStruc
t.comp (CategoryTheory.Limits.Multifork.IsLimit.lift hK k hk) (K.ι a) = k a
参数：hK : CategoryTheory.Limits.IsLimit K；k : (a : J.L) → T ⟶ I.left a；hk :     ∀ 
(b : J.R),       CategoryTheory.CategoryStruct.comp (k (J.fst b)) (I.fst b) =   
      CategoryTheory.CategoryStruct.comp (k (J.snd b)) (I.snd b)；a : J.L；Categor
yTheory.Limits.Multifork.IsLimit.lift hK k hk；K.ι a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma IsLimit.fac (hK : IsLimit K) {T : C} (k : ∀ a, T ⟶ I.left a)
    (hk : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (a : J.L) :
    IsLimit.lift hK k hk ≫ K.ι a = k a :=
  hK.fac _ _

/-- Given two multiforks with isomorphic components in such a way that the natural diagrams
commute, then one is a limit if and only if the other one is. -/
/-
**CategoryTheory.Limits.Multifork.isLimitEquivOfIsos** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Multifork`。
形式化陈述：isLimitEquivOfIsos {I I' : MulticospanIndex J C} (c : Multifork I) (c' : M
ultifork I') (e : c.pt ≅ c'.pt) (el : forall i, I.left i ≅ I'.left i) (er : fora
ll i, I.right i ≅ I'.right i) (hl : forall (i : J.R), I.fst i ≫ (er i).hom = (el
 (J.fst i)).hom ≫ I'.fst i
参数：c : Multifork I；c' : Multifork I'；e : c.pt ≅ c'.pt；el : forall i, I.left i ≅ 
I'.left i；er : forall i, I.right i ≅ I'.right i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two multiforks with isomorphic components in such a way that the natural d
iagrams
commute, then one is a limit if and only if the other one is.
-/
def isLimitEquivOfIsos {I I' : MulticospanIndex J C} (c : Multifork I) (c' : Multifork I')
    (e : c.pt ≅ c'.pt) (el : ∀ i, I.left i ≅ I'.left i) (er : ∀ i, I.right i ≅ I'.right i)
    (hl : ∀ (i : J.R), I.fst i ≫ (er i).hom = (el (J.fst i)).hom ≫ I'.fst i := by cat_disch)
    (hr : ∀ (i : J.R), I.snd i ≫ (er i).hom = (el (J.snd i)).hom ≫ I'.snd i := by cat_disch)
    (he : ∀ (i : J.L), e.hom ≫ c'.ι i = c.ι i ≫ (el i).hom := by cat_disch) :
    IsLimit c ≃ IsLimit c' :=
  letI i : I.multicospan ≅ I'.multicospan :=
    WalkingMulticospan.functorExt el er hl hr
  IsLimit.equivOfNatIsoOfIso i _ _ (Multifork.ext e he)

variable (K)
variable {c : Fan I.left} (hc : IsLimit c) {d : Fan I.right} (hd : IsLimit d)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multifork.pi_condition** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.Multifork`。
形式化陈述：pi_condition : Fan.IsLimit.lift hc K.ι ≫ I.fstPiMapOfIsLimit c hd = Fan.Is
Limit.lift hc K.ι ≫ I.sndPiMapOfIsLimit c hd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fan.IsLimit.hom_ext`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.Limit
s.Fan F}   (hc : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Limits.MulticospanIndex.fstPiMapOfIsLimit_proj`：fstPiMapO
fIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) : fstPiMap
OfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.fst i
· 使用定理 `CategoryTheory.Limits.Fan.IsLimit.fac_assoc`：∀ {β : Type w} {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limit
s.Fan F}   (hc : CategoryTheory.L…
· 使用定理 `CategoryTheory.Limits.Multifork.condition`：condition (b) : K.ι (J.fst b)
 ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b
· 使用引理 `CategoryTheory.Limits.MulticospanIndex.sndPiMapOfIsLimit_proj`：sndPiMapO
fIsLimit_proj (c : Fan I.left) {d : Fan I.right} (hd : IsLimit d) (i) : sndPiMap
OfIsLimit I c hd ≫ d.proj i = c.proj _ ≫ I.snd i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pi_condition :
    Fan.IsLimit.lift hc K.ι ≫ I.fstPiMapOfIsLimit c hd =
      Fan.IsLimit.lift hc K.ι ≫ I.sndPiMapOfIsLimit c hd := by
  apply Fan.IsLimit.hom_ext hd
  simp

/-- Given a multifork, we may obtain a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`. -/
@[simps! pt]
/-
**CategoryTheory.Limits.Multifork.toPiFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Multifork`。
形式化陈述：toPiFork (K : Multifork I) : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOf
IsLimit c hd)
参数：K : Multifork I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multifork, we may obtain a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`.
-/
def toPiFork (K : Multifork I) :
    Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd) :=
  .ofι (Fan.IsLimit.lift hc K.ι) (by simp)

@[simp]
/-
**CategoryTheory.Limits.Multifork.toPiFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPiFork_π_app_zero :
    (K.toPiFork hc hd).ι = Fan.IsLimit.lift hc K.ι :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Multifork.toPiFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPiFork_π_app_one :
    (K.toPiFork hc hd).π.app WalkingParallelPair.one =
      Fan.IsLimit.lift hc K.ι ≫ I.fstPiMapOfIsLimit c hd :=
  rfl

set_option backward.defeqAttrib.useBackward true in
variable {hd} in
/-- Given a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`, we may obtain a multifork. -/
@[simps pt]
/-
**CategoryTheory.Limits.Multifork.ofPiFork** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Multifork`。
形式化陈述：ofPiFork (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) 
: Multifork I where pt
参数：a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a fork over `∏ᶜ I.left ⇉ ∏ᶜ I.right`, we may obtain a multifork.
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
/-
**CategoryTheory.Limits.Multifork.ofPiFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofPiFork_ι (a : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c hd)) (i) :
    (ofPiFork a).ι i = a.ι ≫ c.proj _ :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Multifork.ofPiFork_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Multifork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.Limits.MulticospanIndex.toPiForkFunctor** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：toPiForkFunctor : Multifork I ⥤ Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMa
pOfIsLimit c hd) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multifork.toPiFork` as a functor.
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
/-
**CategoryTheory.Limits.MulticospanIndex.ofPiForkFunctor** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：ofPiForkFunctor : Fork (I.fstPiMapOfIsLimit c hd) (I.sndPiMapOfIsLimit c h
d) ⥤ Multifork I where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multifork.ofPiFork` as a functor.
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
/-
**CategoryTheory.Limits.MulticospanIndex.multiforkEquivPiForkOfIsLimit** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multiforkEquivPiForkOfIsLimit : Multifork I ≌ Fork (I.fstPiMapOfIsLimit c 
hd) (I.sndPiMapOfIsLimit c hd) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of multiforks is equivalent to the category of forks over `∏ᶜ I.lef
t ⇉ ∏ᶜ I.right`.
It then follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `refle
cts`) that it
preserves and reflects limit cones.
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
      Fork.ext (Iso.refl _) <| Fan.IsLimit.hom_ext hc _ _ (by simp))

variable [HasProduct I.left] [HasProduct I.right]

set_option backward.isDefEq.respectTransparency.types false in
/-- The category of multiforks is equivalent to the category of forks over `∏ᶜ I.left ⇉ ∏ᶜ I.right`.
It then follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `reflects`) that it
preserves and reflects limit cones.
-/
@[simps!]
/-
**CategoryTheory.Limits.MulticospanIndex.multiforkEquivPiFork** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multiforkEquivPiFork : Multifork I ≌ Fork I.fstPiMap I.sndPiMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of multiforks is equivalent to the category of forks over `∏ᶜ I.lef
t ⇉ ∏ᶜ I.right`.
It then follows from `CategoryTheory.IsLimit.ofPreservesConeTerminal` (or `refle
cts`) that it
preserves and reflects limit cones.
-/
noncomputable def multiforkEquivPiFork : Multifork I ≌ Fork I.fstPiMap I.sndPiMap :=
  multiforkEquivPiForkOfIsLimit I (limit.isLimit _) (limit.isLimit _)

/-- The constant `MulticospanShape` for a pair of parallel morphisms. -/
@[simps]
/-
**CategoryTheory.Limits.MulticospanIndex.ofParallelHoms** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：ofParallelHoms (J : MulticospanShape) {X Y : C} (f g : X ⟶ Y) : Multicospa
nIndex J C where left _
参数：J : MulticospanShape；f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant `MulticospanShape` for a pair of parallel morphisms.
-/
def ofParallelHoms (J : MulticospanShape) {X Y : C} (f g : X ⟶ Y) : MulticospanIndex J C where
  left _ := X
  right _ := Y
  fst _ := f
  snd _ := g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A fork on a pair of morphisms `f` and `g` is the same as a multifork on the
single point index defined by `f` and `g`. -/
/-
**CategoryTheory.Limits.MulticospanIndex.multiforkOfParallelHomsEquivFork** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
形式化陈述：multiforkOfParallelHomsEquivFork (J : MulticospanShape) [Unique J.L] [Uniq
ue J.R] {X Y : C} (f g : X ⟶ Y) : Multifork (ofParallelHoms J f g) ≌ Fork f g
参数：J : MulticospanShape；f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fork on a pair of morphisms `f` and `g` is the same as a multifork on the
single point index defined by `f` and `g`.
-/
def multiforkOfParallelHomsEquivFork (J : MulticospanShape) [Unique J.L] [Unique J.R] {X Y : C}
    (f g : X ⟶ Y) :
    Multifork (ofParallelHoms J f g) ≌ Fork f g := by
  refine (multiforkEquivPiForkOfIsLimit _
      (Fan.isLimitMkOfUnique (Iso.refl X) _) (Fan.isLimitMkOfUnique (Iso.refl Y) _)).trans
      (Fork.equivOfIsos (.refl _) (.refl _) ?_ ?_)
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ ↦ ?_
    rw [Category.assoc, Iso.refl_hom ((Fan.mk Y fun x ↦ (Iso.refl Y).hom).pt),
      Category.comp_id, fstPiMapOfIsLimit_proj]
    simp
  · refine Fan.IsLimit.hom_ext (Fan.isLimitMkOfUnique (Iso.refl Y) J.R) _ _ fun _ ↦ ?_
    rw [Category.assoc, Iso.refl_hom ((Fan.mk Y fun x ↦ (Iso.refl Y).hom).pt),
      Category.comp_id, sndPiMapOfIsLimit_proj]
    simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Limits.MulticospanIndex.multiforkOfParallelHomsEquivFork_functo
r_obj_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma multiforkOfParallelHomsEquivFork_functor_obj_ι (J : MulticospanShape) [Unique J.L]
    [Unique J.R] {X Y : C} (f g : X ⟶ Y) (c : Multifork (ofParallelHoms J f g)) :
    ((multiforkOfParallelHomsEquivFork J f g).functor.obj c).ι = c.ι default :=
  Fan.IsLimit.fac (Fan.isLimitMkOfUnique (Iso.refl X) J.L) _ default

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.MulticospanIndex.multiforkOfParallelHomsEquivFork_invers
e_obj_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits.MulticospanIndex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma multiforkOfParallelHomsEquivFork_inverse_obj_ι (J : MulticospanShape) [Unique J.L]
    [Unique J.R] {X Y : C} (f g : X ⟶ Y) (c : Fork f g) (a : J.L) :
    ((multiforkOfParallelHomsEquivFork J f g).inverse.obj c).ι a = c.ι := by
  simp [multiforkOfParallelHomsEquivFork]

end MulticospanIndex

namespace Multicofork

variable {J : MultispanShape.{w, w'}} {I : MultispanIndex J C} (K : Multicofork I)

/-- The maps to the cocone point of a multicofork from the objects on the right. -/
/-
**CategoryTheory.Limits.Multicofork.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maps to the cocone point of a multicofork from the objects on the right.
-/
def π (b : J.R) : I.right b ⟶ K.pt :=
  K.ι.app (WalkingMultispan.right _)

@[simp]
/-
**CategoryTheory.Limits.Multicofork.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_eq_app_right (b) : K.ι.app (WalkingMultispan.right _) = K.π b :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Multicofork.fst_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Multicofork`。
形式化陈述：fst_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.fst a ≫ K.π _
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
-/
theorem fst_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.fst a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.fst a)]
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.Multicofork.snd_app_right** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Multicofork`。
形式化陈述：snd_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.snd a ≫ K.π _
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
-/
theorem snd_app_right (a) : K.ι.app (WalkingMultispan.left a) = I.snd a ≫ K.π _ := by
  rw [← K.w (WalkingMultispan.Hom.snd a)]
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multicofork.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.L
imits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_comp_hom (K₁ K₂ : Multicofork I) (f : K₁ ⟶ K₂) (b : J.R) : K₁.π b ≫ f.hom = K₂.π b :=
  f.w _

set_option backward.defeqAttrib.useBackward true in
/-- Construct a multicofork using a collection `π` of morphisms. -/
@[simps]
/-
**CategoryTheory.Limits.Multicofork.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a multicofork using a collection `π` of morphisms.
-/
def ofπ {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
    (P : C) (π : ∀ b, I.right b ⟶ P)
    (w : ∀ a, I.fst a ≫ π (J.fst a) = I.snd a ≫ π (J.snd a)) : Multicofork I where
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
/-
**CategoryTheory.Limits.Multicofork.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.Multicofork`。
形式化陈述：condition (a) : I.fst a ≫ K.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Multicofork.snd_app_right`：snd_app_right (a) : K.ι
.app (WalkingMultispan.left a) = I.snd a ≫ K.π _
· 使用定理 `CategoryTheory.Limits.Multicofork.fst_app_right`：fst_app_right (a) : K.ι
.app (WalkingMultispan.left a) = I.fst a ≫ K.π _
-/
theorem condition (a) : I.fst a ≫ K.π (J.fst a) = I.snd a ≫ K.π (J.snd a) := by
  rw [← K.snd_app_right, ← K.fst_app_right]

set_option backward.isDefEq.respectTransparency false in
/-- This definition provides a convenient way to show that a multicofork is a colimit. -/
@[simps]
/-
**CategoryTheory.Limits.Multicofork.IsColimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Multicofork.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MultispanShape} →       {I : CategoryTheory.Limits.MultispanIn
dex J C} →         (K : CategoryTheory.Limits.Multicofork I) →           (desc :
 (E : CategoryTheory.Limits.Multicofork I) → K.pt ⟶ E.pt) →             (∀ (E : 
CategoryTheory.Limits.Multicofork I) (i : J.R),                 CategoryTheory.C
ategoryStruct.comp (K.π i) (desc E) = E.π i) →               (∀ (E : CategoryThe
ory.Limits.Multicofork I) (m : K.pt ⟶ E.pt),                   (∀ (i : J.R), Cat
egoryTheory.CategoryStruct.comp (K.π i) m = E.π i) → m = desc E) →              
   CategoryTheory.Limits.IsColimit K
参数：K : CategoryTheory.Limits.Multicofork I；desc : (E : CategoryTheory.Limits.Mul
ticofork I) → K.pt ⟶ E.pt；∀ (E : CategoryTheory.Limits.Multicofork I) (i : J.R),
                 CategoryTheory.CategoryStruct.comp (K.π i) (desc E) = E.π i；∀ (
E : CategoryTheory.Limits.Multicofork I) (m : K.pt ⟶ E.pt),                   (∀
 (i : J.R), CategoryTheory.CategoryStruct.comp (K.π i) m = E.π i) → m = desc E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition provides a convenient way to show that a multicofork is a colimi
t.
-/
def IsColimit.mk (desc : ∀ E : Multicofork I, K.pt ⟶ E.pt)
    (fac : ∀ (E : Multicofork I) (i : J.R), K.π i ≫ desc E = E.π i)
    (uniq : ∀ (E : Multicofork I) (m : K.pt ⟶ E.pt), (∀ i : J.R, K.π i ≫ m = E.π i) → m = desc E) :
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
/-
**CategoryTheory.Limits.Multicofork.IsColimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Multicofork.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.Limits.MultispanShape}   {I : CategoryTheory.Limits.MultispanIndex J C} {K : 
CategoryTheory.Limits.Multicofork I}   (hK : CategoryTheory.Limits.IsColimit K) 
{T : C} {f g : K.pt ⟶ T},   (∀ (a : J.R), CategoryTheory.CategoryStruct.comp (K.
π a) f = CategoryTheory.CategoryStruct.comp (K.π a) g) → f = g
参数：hK : CategoryTheory.Limits.IsColimit K；∀ (a : J.R), CategoryTheory.CategorySt
ruct.comp (K.π a) f = CategoryTheory.CategoryStruct.comp (K.π a) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.Multicofork.fst_app_right`：fst_app_right (a) : K.ι
.app (WalkingMultispan.left a) = I.fst a ≫ K.π _
· 使用定理 `CategoryTheory.Limits.Multicofork.condition`：condition (a) : I.fst a ≫ K
.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsColimit.hom_ext (hK : IsColimit K) {T : C} {f g : K.pt ⟶ T}
    (h : ∀ a, K.π a ≫ f = K.π a ≫ g) : f = g := by
  apply hK.hom_ext
  rintro (_ | _) <;> simp [h]

/-- Constructor for morphisms from the point of a colimit multicofork. -/
/-
**CategoryTheory.Limits.Multicofork.IsColimit.desc** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Multicofork.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.Limits.MultispanShape} →       {I : CategoryTheory.Limits.MultispanIn
dex J C} →         {K : CategoryTheory.Limits.Multicofork I} →           Categor
yTheory.Limits.IsColimit K →             {T : C} →               (k : (a : J.R) 
→ I.right a ⟶ T) →                 (∀ (b : J.L),                     CategoryThe
ory.CategoryStruct.comp (I.fst b) (k (J.fst b)) =                       Category
Theory.CategoryStruct.comp (I.snd b) (k (J.snd b))) →                   (K.pt ⟶ 
T)
参数：k : (a : J.R) → I.right a ⟶ T；∀ (b : J.L),                     CategoryTheory
.CategoryStruct.comp (I.fst b) (k (J.fst b)) =                       CategoryThe
ory.CategoryStruct.comp (I.snd b) (k (J.snd b))；K.pt ⟶ T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from the point of a colimit multicofork.
-/
def IsColimit.desc (hK : IsColimit K) {T : C} (k : ∀ a, I.right a ⟶ T)
    (hk : ∀ b, I.fst b ≫ k (J.fst b) = I.snd b ≫ k (J.snd b)) :
    K.pt ⟶ T :=
  hK.desc (Multicofork.ofπ _ _ k hk)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multicofork.IsColimit.fac** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Multicofork.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.Limits.MultispanShape}   {I : CategoryTheory.Limits.MultispanIndex J C} {K : 
CategoryTheory.Limits.Multicofork I}   (hK : CategoryTheory.Limits.IsColimit K) 
{T : C} (k : (a : J.R) → I.right a ⟶ T)   (hk :     ∀ (b : J.L),       CategoryT
heory.CategoryStruct.comp (I.fst b) (k (J.fst b)) =         CategoryTheory.Categ
oryStruct.comp (I.snd b) (k (J.snd b)))   (a : J.R), CategoryTheory.CategoryStru
ct.comp (K.π a) (CategoryTheory.Limits.Multicofork.IsColimit.desc hK k hk) = k a
参数：hK : CategoryTheory.Limits.IsColimit K；k : (a : J.R) → I.right a ⟶ T；hk :    
 ∀ (b : J.L),       CategoryTheory.CategoryStruct.comp (I.fst b) (k (J.fst b)) =
         CategoryTheory.CategoryStruct.comp (I.snd b) (k (J.snd b))；a : J.R；K.π 
a；CategoryTheory.Limits.Multicofork.IsColimit.desc hK k hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma IsColimit.fac (hK : IsColimit K) {T : C} (k : ∀ a, I.right a ⟶ T)
    (hk : ∀ b, I.fst b ≫ k (J.fst b) = I.snd b ≫ k (J.snd b)) (a : J.R) :
    K.π a ≫ IsColimit.desc hK k hk = k a :=
  hK.fac _ _

variable (K)
variable {c : Cofan I.left} (hc : IsColimit c) {d : Cofan I.right} (hd : IsColimit d)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multicofork.sigma_condition** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.Multicofork`。
形式化陈述：sigma_condition : I.fstSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd 
K.π = I.sndSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd K.π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.MultispanIndex.inj_fstSigmaMapOfIsColimit_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limi
ts.MultispanShape}   (I : CategoryTheory.Limits.MultispanIn…
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Multicofork.condition`：condition (a) : I.fst a ≫ K
.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
· 使用定理 `CategoryTheory.Limits.MultispanIndex.inj_sndSigmaMapOfIsColimit_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limi
ts.MultispanShape}   (I : CategoryTheory.Limits.MultispanIn…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sigma_condition :
    I.fstSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd K.π =
      I.sndSigmaMapOfIsColimit d hc ≫ Cofan.IsColimit.desc hd K.π := by
  apply Cofan.IsColimit.hom_ext hc
  simp

/-- Given a multicofork, we may obtain a cofork over `∐ I.left ⇉ ∐ I.right`. -/
@[simps! pt]
/-
**CategoryTheory.Limits.Multicofork.toSigmaCofork** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Multicofork`。
形式化陈述：toSigmaCofork (K : Multicofork I) : Cofork (I.fstSigmaMapOfIsColimit d hc)
 (I.sndSigmaMapOfIsColimit d hc)
参数：K : Multicofork I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a multicofork, we may obtain a cofork over `∐ I.left ⇉ ∐ I.right`.
-/
noncomputable def toSigmaCofork (K : Multicofork I) :
    Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) :=
  .ofπ (Cofan.IsColimit.desc hd K.π) (by simp)

@[simp]
/-
**CategoryTheory.Limits.Multicofork.toSigmaCofork_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSigmaCofork_π :
    (K.toSigmaCofork hc hd).π = Cofan.IsColimit.desc hd K.π :=
  rfl

set_option backward.defeqAttrib.useBackward true in
variable {hc} in
/-- Given a cofork over `∐ I.left ⇉ ∐ I.right`, we may obtain a multicofork. -/
@[simps pt]
/-
**CategoryTheory.Limits.Multicofork.ofSigmaCofork** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Multicofork`。
形式化陈述：ofSigmaCofork (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOf
IsColimit d hc)) : Multicofork I where pt
参数：a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cofork over `∐ I.left ⇉ ∐ I.right`, we may obtain a multicofork.
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
/-
**CategoryTheory.Limits.Multicofork.ofSigmaCofork_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSigmaCofork_ι_app_left
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) (i) :
    (ofSigmaCofork a).ι.app (WalkingMultispan.left i) =
      c.inj _ ≫ I.fstSigmaMapOfIsColimit d hc ≫ a.π :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Multicofork.ofSigmaCofork_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSigmaCofork_π
    (a : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc)) (i) :
    (ofSigmaCofork a).π i = d.inj i ≫ a.π :=
  rfl

/-- Constructor for isomorphisms between multicoforks. -/
@[simps!]
/-
**CategoryTheory.Limits.Multicofork.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Multicofork`。
形式化陈述：ext {K K' : Multicofork I} (e : K.pt ≅ K'.pt) (h : forall (i : J.R), K.π i
 ≫ e.hom = K'.π i
参数：e : K.pt ≅ K'.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms between multicoforks.
-/
def ext {K K' : Multicofork I}
    (e : K.pt ≅ K'.pt) (h : ∀ (i : J.R), K.π i ≫ e.hom = K'.π i := by cat_disch) :
    K ≅ K' :=
  Cocone.ext e (by rintro (i | j) <;> simp [h])

set_option backward.defeqAttrib.useBackward true in
/-- Every multicofork is isomorphic to one of the form `Multicofork.ofπ`. -/
@[simps!]
/-
**CategoryTheory.Limits.Multicofork.isoOf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.Multicofork`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every multicofork is isomorphic to one of the form `Multicofork.ofπ`.
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
/-
**CategoryTheory.Limits.MultispanIndex.toSigmaCoforkFunctor** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：toSigmaCoforkFunctor : Multicofork I ⥤ Cofork (I.fstSigmaMapOfIsColimit d 
hc) (I.sndSigmaMapOfIsColimit d hc) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multicofork.toSigmaCofork` as a functor.
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
/-
**CategoryTheory.Limits.MultispanIndex.ofSigmaCoforkFunctor** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：ofSigmaCoforkFunctor : Cofork (I.fstSigmaMapOfIsColimit d hc) (I.sndSigmaM
apOfIsColimit d hc) ⥤ Multicofork I where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multicofork.ofSigmaCofork` as a functor.
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
/-
**CategoryTheory.Limits.MultispanIndex.multicoforkEquivSigmaCoforkOfIsColimit** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：multicoforkEquivSigmaCoforkOfIsColimit : Multicofork I ≌ Cofork (I.fstSigm
aMapOfIsColimit d hc) (I.sndSigmaMapOfIsColimit d hc) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of multicoforks is equivalent to the category of coforks over `∐ I.
left ⇉ ∐ I.right`.
It then follows from `CategoryTheory.IsColimit.ofPreservesCoconeInitial` (or `re
flects`) that
it preserves and reflects colimit cocones.
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
/-
**CategoryTheory.Limits.MultispanIndex.multicoforkEquivSigmaCofork** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：multicoforkEquivSigmaCofork : Multicofork I ≌ Cofork I.fstSigmaMap I.sndSi
gmaMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of multicoforks is equivalent to the category of coforks over `∐ I.
left ⇉ ∐ I.right`.
It then follows from `CategoryTheory.IsColimit.ofPreservesCoconeInitial` (or `re
flects`) that
it preserves and reflects colimit cocones.
-/
noncomputable def multicoforkEquivSigmaCofork :
    Multicofork I ≌ Cofork I.fstSigmaMap I.sndSigmaMap :=
  multicoforkEquivSigmaCoforkOfIsColimit _ (colimit.isColimit _) (colimit.isColimit _)

end MultispanIndex

/-- For `I : MulticospanIndex J C`, we say that it has a multiequalizer if the associated
  multicospan has a limit. -/
/-
**CategoryTheory.Limits.HasMultiequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：HasMultiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C
)
参数：I : MulticospanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `I : MulticospanIndex J C`, we say that it has a multiequalizer if the assoc
iated
  multicospan has a limit.
-/
abbrev HasMultiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) :=
  HasLimit I.multicospan

noncomputable section

/-- The multiequalizer of `I : MulticospanIndex J C`. -/
/-
**CategoryTheory.Limits.multiequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：multiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) [
HasMultiequalizer I] : C
参数：I : MulticospanIndex J C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiequalizer of `I : MulticospanIndex J C`.
-/
abbrev multiequalizer {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C)
    [HasMultiequalizer I] : C :=
  limit I.multicospan

/-- For `I : MultispanIndex J C`, we say that it has a multicoequalizer if
  the associated multicospan has a limit. -/
/-
**CategoryTheory.Limits.HasMulticoequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：HasMulticoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
参数：I : MultispanIndex J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `I : MultispanIndex J C`, we say that it has a multicoequalizer if
  the associated multicospan has a limit.
-/
abbrev HasMulticoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) :=
  HasColimit I.multispan

/-- The multicoequalizer of `I : MultispanIndex J C`. -/
/-
**CategoryTheory.Limits.multicoequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：multicoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) [Ha
sMulticoequalizer I] : C
参数：I : MultispanIndex J C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicoequalizer of `I : MultispanIndex J C`.
-/
abbrev multicoequalizer {J : MultispanShape.{w, w'}} (I : MultispanIndex J C)
    [HasMulticoequalizer I] : C :=
  colimit I.multispan

namespace Multiequalizer

variable {J : MulticospanShape.{w, w'}} (I : MulticospanIndex J C) [HasMultiequalizer I]

/-- The canonical map from the multiequalizer to the objects on the left. -/
/-
**CategoryTheory.Limits.Multiequalizer.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the multiequalizer to the objects on the left.
-/
abbrev ι (a : J.L) : multiequalizer I ⟶ I.left a :=
  limit.π _ (WalkingMulticospan.left a)

/-- The multifork associated to the multiequalizer. -/
/-
**CategoryTheory.Limits.Multiequalizer.multifork** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Limits.Multiequalizer`。
形式化陈述：multifork : Multifork I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multifork associated to the multiequalizer.
-/
abbrev multifork : Multifork I :=
  limit.cone _

@[simp]
/-
**CategoryTheory.Limits.Multiequalizer.multifork_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multifork_ι (a) : (Multiequalizer.multifork I).ι a = Multiequalizer.ι I a :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Multiequalizer.multifork_** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multifork_π_app_left (a) :
    (Multiequalizer.multifork I).π.app (WalkingMulticospan.left a) = Multiequalizer.ι I a :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.Multiequalizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Multiequalizer`。
形式化陈述：condition (b) : Multiequalizer.ι I (J.fst b) ≫ I.fst b = Multiequalizer.ι 
I (J.snd b) ≫ I.snd b
参数：b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multifork.condition`：condition (b) : K.ι (J.fst b)
 ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b
-/
theorem condition (b) :
    Multiequalizer.ι I (J.fst b) ≫ I.fst b = Multiequalizer.ι I (J.snd b) ≫ I.snd b :=
  Multifork.condition _ _

/-- Construct a morphism to the multiequalizer from its universal property. -/
/-
**CategoryTheory.Limits.Multiequalizer.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits.Multiequalizer`。
形式化陈述：lift (W : C) (k : forall a, W ⟶ I.left a) (h : forall b, k (J.fst b) ≫ I.f
st b = k (J.snd b) ≫ I.snd b) : W ⟶ multiequalizer I
参数：W : C；k : forall a, W ⟶ I.left a；h : forall b, k (J.fst b) ≫ I.fst b = k (J.s
nd b) ≫ I.snd b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism to the multiequalizer from its universal property.
-/
abbrev lift (W : C) (k : ∀ a, W ⟶ I.left a)
    (h : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) : W ⟶ multiequalizer I :=
  limit.lift _ (Multifork.ofι I _ k h)

@[reassoc]
/-
**CategoryTheory.Limits.Multiequalizer.lift_** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_ι (W : C) (k : ∀ a, W ⟶ I.left a)
    (h : ∀ b, k (J.fst b) ≫ I.fst b = k (J.snd b) ≫ I.snd b) (a) :
    Multiequalizer.lift I _ k h ≫ Multiequalizer.ι I a = k _ :=
  limit.lift_π _ _

@[ext]
/-
**CategoryTheory.Limits.Multiequalizer.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.Multiequalizer`。
形式化陈述：hom_ext {W : C} (i j : W ⟶ multiequalizer I) (h : forall a, i ≫ Multiequal
izer.ι I a = j ≫ Multiequalizer.ι I a) : i = j
参数：i j : W ⟶ multiequalizer I；h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multi
equalizer.ι I a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multifork.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}  
 {I : CategoryTheory.Limits.Multicosp…
-/
theorem hom_ext {W : C} (i j : W ⟶ multiequalizer I)
    (h : ∀ a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.ι I a) : i = j :=
  Multifork.IsLimit.hom_ext (limit.isLimit _) h

variable [HasProduct I.left] [HasProduct I.right]
/-
**CategoryTheory.Limits.Multiequalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasEqualizer I.fstPiMap I.sndPiMap :=
  ⟨⟨⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.functor (limit.isLimit _)⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The multiequalizer is isomorphic to the equalizer of `∏ᶜ I.left ⇉ ∏ᶜ I.right`. -/
/-
**CategoryTheory.Limits.Multiequalizer.isoEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Multiequalizer`。
形式化陈述：isoEqualizer : multiequalizer I ≅ equalizer I.fstPiMap I.sndPiMap
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multiequalizer.instHasEqualizerFstPiMapSndPiMap`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limi
ts.MulticospanShape}   (I : CategoryTheory.Limits.Multicosp…

--- 原说明 ---
The multiequalizer is isomorphic to the equalizer of `∏ᶜ I.left ⇉ ∏ᶜ I.right`.
-/
def isoEqualizer : multiequalizer I ≅ equalizer I.fstPiMap I.sndPiMap :=
  limit.isoLimitCone
    ⟨_, IsLimit.ofPreservesConeTerminal I.multiforkEquivPiFork.inverse (limit.isLimit _)⟩

/-- The canonical injection `multiequalizer I ⟶ ∏ᶜ I.left`. -/
/-
**CategoryTheory.Limits.Multiequalizer.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical injection `multiequalizer I ⟶ ∏ᶜ I.left`.
-/
def ιPi : multiequalizer I ⟶ ∏ᶜ I.left :=
  (isoEqualizer I).hom ≫ equalizer.ι I.fstPiMap I.sndPiMap

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multiequalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ιPi_π (a) : ιPi I ≫ Pi.π I.left a = ι I a := by
  rw [ιPi, Category.assoc, ← Iso.eq_inv_comp, isoEqualizer]
  simp only [limit.isoLimitCone_inv_π,
    limit.cone_x, MulticospanIndex.multiforkEquivPiFork_inverse_obj_π_app]
  rfl
/-
**CategoryTheory.Limits.Multiequalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Limits.Multiequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (ιPi I) := mono_comp _ _

end Multiequalizer

namespace Multicoequalizer

variable {J : MultispanShape.{w, w'}} (I : MultispanIndex J C) [HasMulticoequalizer I]

/-- The canonical map from the multiequalizer to the objects on the left. -/
/-
**CategoryTheory.Limits.Multicoequalizer.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the multiequalizer to the objects on the left.
-/
abbrev π (b : J.R) : I.right b ⟶ multicoequalizer I :=
  colimit.ι I.multispan (WalkingMultispan.right _)

/-- The multicofork associated to the multicoequalizer. -/
/-
**CategoryTheory.Limits.Multicoequalizer.multicofork** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Limits.Multicoequalizer`。
形式化陈述：multicofork : Multicofork I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicofork associated to the multicoequalizer.
-/
abbrev multicofork : Multicofork I :=
  colimit.cocone _

@[simp]
/-
**CategoryTheory.Limits.Multicoequalizer.multicofork_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multicofork_π (b) : (Multicoequalizer.multicofork I).π b = Multicoequalizer.π I b :=
  rfl
/-
**CategoryTheory.Limits.Multicoequalizer.multicofork_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multicofork_ι_app_right (b) :
    (Multicoequalizer.multicofork I).ι.app (WalkingMultispan.right b) = Multicoequalizer.π I b :=
  rfl

/-- `@[simp]`-normal form of `multicofork_ι_app_right`. -/
@[simp]
/-
**CategoryTheory.Limits.Multicoequalizer.multicofork_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`@[simp]`-normal form of `multicofork_ι_app_right`.
-/
theorem multicofork_ι_app_right' (b) :
    colimit.ι (MultispanIndex.multispan I) (WalkingMultispan.right b) = π I b :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.Multicoequalizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.Multicoequalizer`。
形式化陈述：condition (a) : I.fst a ≫ Multicoequalizer.π I (J.fst a) = I.snd a ≫ Multi
coequalizer.π I (J.snd a)
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicofork.condition`：condition (a) : I.fst a ≫ K
.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
-/
theorem condition (a) :
    I.fst a ≫ Multicoequalizer.π I (J.fst a) = I.snd a ≫ Multicoequalizer.π I (J.snd a) :=
  Multicofork.condition _ _

/-- Construct a morphism from the multicoequalizer from its universal property. -/
/-
**CategoryTheory.Limits.Multicoequalizer.desc** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Limits.Multicoequalizer`。
形式化陈述：desc (W : C) (k : forall b, I.right b ⟶ W) (h : forall a, I.fst a ≫ k (J.f
st a) = I.snd a ≫ k (J.snd a)) : multicoequalizer I ⟶ W
参数：W : C；k : forall b, I.right b ⟶ W；h : forall a, I.fst a ≫ k (J.fst a) = I.snd
 a ≫ k (J.snd a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism from the multicoequalizer from its universal property.
-/
abbrev desc (W : C) (k : ∀ b, I.right b ⟶ W)
    (h : ∀ a, I.fst a ≫ k (J.fst a) = I.snd a ≫ k (J.snd a)) : multicoequalizer I ⟶ W :=
  colimit.desc _ (Multicofork.ofπ I _ k h)

@[reassoc]
/-
**CategoryTheory.Limits.Multicoequalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_desc (W : C) (k : ∀ b, I.right b ⟶ W)
    (h : ∀ a, I.fst a ≫ k (J.fst a) = I.snd a ≫ k (J.snd a)) (b) :
    Multicoequalizer.π I b ≫ Multicoequalizer.desc I _ k h = k _ :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
@[ext]
/-
**CategoryTheory.Limits.Multicoequalizer.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Multicoequalizer`。
形式化陈述：hom_ext {W : C} (i j : multicoequalizer I ⟶ W) (h : forall b, Multicoequal
izer.π I b ≫ i = Multicoequalizer.π I b ≫ j) : i = j
参数：i j : multicoequalizer I ⟶ W；h : forall b, Multicoequalizer.π I b ≫ i = Multi
coequalizer.π I b ≫ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.w`：∀ {J : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   
(F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hom_ext {W : C} (i j : multicoequalizer I ⟶ W)
    (h : ∀ b, Multicoequalizer.π I b ≫ i = Multicoequalizer.π I b ≫ j) : i = j :=
  colimit.hom_ext
    (by
      rintro (a | b)
      · simp_rw [← colimit.w I.multispan (WalkingMultispan.Hom.fst a), Category.assoc, h]
      · apply h)

variable [HasCoproduct I.left] [HasCoproduct I.right]
/-
**CategoryTheory.Limits.Multicoequalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCoequalizer I.fstSigmaMap I.sndSigmaMap :=
  ⟨⟨⟨_,
      IsColimit.ofPreservesCoconeInitial
        I.multicoforkEquivSigmaCofork.functor (colimit.isColimit _)⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The multicoequalizer is isomorphic to the coequalizer of `∐ I.left ⇉ ∐ I.right`. -/
/-
**CategoryTheory.Limits.Multicoequalizer.isoCoequalizer** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.Multicoequalizer`。
形式化陈述：isoCoequalizer : multicoequalizer I ≅ coequalizer I.fstSigmaMap I.sndSigma
Map
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.instHasCoequalizerFstSigmaMapSndS
igmaMap`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryT
heory.Limits.MultispanShape}   (I : CategoryTheory.Limits.MultispanIn…

--- 原说明 ---
The multicoequalizer is isomorphic to the coequalizer of `∐ I.left ⇉ ∐ I.right`.
-/
def isoCoequalizer : multicoequalizer I ≅ coequalizer I.fstSigmaMap I.sndSigmaMap :=
  colimit.isoColimitCocone
    ⟨_,
      IsColimit.ofPreservesCoconeInitial I.multicoforkEquivSigmaCofork.inverse
        (colimit.isColimit _)⟩

/-- The canonical projection `∐ I.right ⟶ multicoequalizer I`. -/
/-
**CategoryTheory.Limits.Multicoequalizer.sigma** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection `∐ I.right ⟶ multicoequalizer I`.
-/
def sigmaπ : ∐ I.right ⟶ multicoequalizer I :=
  coequalizer.π I.fstSigmaMap I.sndSigmaMap ≫ (isoCoequalizer I).inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Multicoequalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_sigmaπ (b) : Sigma.ι I.right b ≫ sigmaπ I = π I b := by
  rw [sigmaπ, ← Category.assoc, Iso.comp_inv_eq, isoCoequalizer]
  simp
  rfl
/-
**CategoryTheory.Limits.Multicoequalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.Multicoequalizer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (sigmaπ I) := epi_comp _ _

end Multicoequalizer

end

/-- The inclusion functor `WalkingMultispan (.ofLinearOrder ι) ⥤ WalkingMultispan (.prod ι)`. -/
@[simps!]
/-
**CategoryTheory.Limits.WalkingMultispan.inclusionOfLinearOrder** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.WalkingMultispan`。
形式化陈述：(ι : Type w) →   [inst : LinearOrder ι] →     CategoryTheory.Functor      
 (CategoryTheory.Limits.WalkingMultispan (CategoryTheory.Limits.MultispanShape.o
fLinearOrder ι))       (CategoryTheory.Limits.WalkingMultispan (CategoryTheory.L
imits.MultispanShape.prod ι))
参数：CategoryTheory.Limits.MultispanShape.ofLinearOrder ι；CategoryTheory.Limits.Mu
ltispanShape.prod ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `WalkingMultispan (.ofLinearOrder ι) ⥤ WalkingMultispan (.
prod ι)`.
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

/-- Structure expressing a symmetry of `I : MultispanIndex (.prod ι) C` which
allows to compare the corresponding multicoequalizer to the multicoequalizer
of `I.toLinearOrder`. -/
/-
**CategoryTheory.Limits.MultispanIndex.SymmStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits.MultispanIndex`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {ι : Type
 w} → CategoryTheory.Limits.MultispanIndex (CategoryTheory.Limits.MultispanShape
.prod ι) C → Type (max v w)
参数：CategoryTheory.Limits.MultispanShape.prod ι；max v w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure expressing a symmetry of `I : MultispanIndex (.prod ι) C` which
allows to compare the corresponding multicoequalizer to the multicoequalizer
of `I.toLinearOrder`.
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
/-
**CategoryTheory.Limits.MultispanIndex.toLinearOrder** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.MultispanIndex`。
形式化陈述：toLinearOrder : MultispanIndex (.ofLinearOrder ι) C where left j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multispan index for `MultispanShape.ofLinearOrder ι` deduced from
a multispan index for `MultispanShape.prod ι` when `ι` is linearly ordered.
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
/-
**CategoryTheory.Limits.MultispanIndex.toLinearOrderMultispanIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Limits.MultispanIndex`。
形式化陈述：toLinearOrderMultispanIso : WalkingMultispan.inclusionOfLinearOrder ι ⋙ I.
multispan ≅ I.toLinearOrder.multispan
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linearly ordered type `ι` and `I : MultispanIndex (.prod ι) C`,
this is the isomorphism of functors between
`WalkingMultispan.inclusionOfLinearOrder ι ⋙ I.multispan`
and `I.toLinearOrder.multispan`.
-/
def toLinearOrderMultispanIso :
    WalkingMultispan.inclusionOfLinearOrder ι ⋙ I.multispan ≅
      I.toLinearOrder.multispan :=
  NatIso.ofComponents (fun i ↦ match i with
    | .left _ => Iso.refl _
    | .right _ => Iso.refl _)

end MultispanIndex

namespace Multicofork

variable {ι : Type w} [LinearOrder ι] {I : MultispanIndex (.prod ι) C}

/-- The multicofork for `I.toLinearOrder` deduced from a multicofork
for `I : MultispanIndex (.prod ι) C` when `ι` is linearly ordered. -/
/-
**CategoryTheory.Limits.Multicofork.toLinearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Multicofork`。
形式化陈述：toLinearOrder (c : Multicofork I) : Multicofork I.toLinearOrder
参数：c : Multicofork I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicofork for `I.toLinearOrder` deduced from a multicofork
for `I : MultispanIndex (.prod ι) C` when `ι` is linearly ordered.
-/
def toLinearOrder (c : Multicofork I) : Multicofork I.toLinearOrder :=
  Multicofork.ofπ _ c.pt c.π (fun _ ↦ c.condition _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The multicofork for `I : MultispanIndex (.prod ι) C` deduced from
a multicofork for `I.toLinearOrder` when `ι` is linearly ordered
and `I` is symmetric. -/
/-
**CategoryTheory.Limits.Multicofork.ofLinearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Multicofork`。
形式化陈述：ofLinearOrder (c : Multicofork I.toLinearOrder) (h : I.SymmStruct) : Multi
cofork I
参数：c : Multicofork I.toLinearOrder；h : I.SymmStruct。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicofork for `I : MultispanIndex (.prod ι) C` deduced from
a multicofork for `I.toLinearOrder` when `ι` is linearly ordered
and `I` is symmetric.
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
      rw [← h.iso_hom_fst_assoc, ← h.iso_hom_snd_assoc, this])

set_option backward.isDefEq.respectTransparency false in
/-- If `ι` is a linearly ordered type, `I : MultispanIndex (.prod ι) C`, and
`c` a colimit multicofork for `I`, then `c.toLinearOrder` is a colimit
multicofork for `I.toLinearOrder`. -/
/-
**CategoryTheory.Limits.Multicofork.isColimitToLinearOrder** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits.Multicofork`。
形式化陈述：isColimitToLinearOrder (c : Multicofork I) (hc : IsColimit c) (h : I.SymmS
truct) : IsColimit c.toLinearOrder
参数：c : Multicofork I；hc : IsColimit c；h : I.SymmStruct。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` is a linearly ordered type, `I : MultispanIndex (.prod ι) C`, and
`c` a colimit multicofork for `I`, then `c.toLinearOrder` is a colimit
multicofork for `I.toLinearOrder`.
-/
def isColimitToLinearOrder (c : Multicofork I) (hc : IsColimit c) (h : I.SymmStruct) :
    IsColimit c.toLinearOrder :=
  Multicofork.IsColimit.mk _ (fun s ↦ hc.desc (ofLinearOrder s h))
    (fun s _ ↦ hc.fac (ofLinearOrder s h) _)
    (fun s m hm ↦ Multicofork.IsColimit.hom_ext hc (fun i ↦ by
      have := hc.fac (ofLinearOrder s h) (.right i)
      dsimp at this
      rw [this]
      apply hm))

end Multicofork

end symmetry

end CategoryTheory.Limits

