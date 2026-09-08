/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Uni Marx
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Rel

/-!
# Basics on the category of relations

We define the category of types `CategoryTheory.RelCat` with binary relations as morphisms.
Associating each function with the relation defined by its graph yields a faithful and
essentially surjective functor `graphFunctor` that also characterizes all isomorphisms
(see `rel_iso_iff`).

By flipping the arguments to a relation, we construct an equivalence `opEquivalence` between
`RelCat` and its opposite.
-/

@[expose] public section

open SetRel

namespace CategoryTheory

universe u

/-- A type synonym for `Type u`, which carries the category instance for which
morphisms are binary relations. -/
/-
**CategoryTheory.RelCat** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：RelCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `Type u`, which carries the category instance for which
morphisms are binary relations.
-/
def RelCat :=
  Type u
deriving Inhabited

namespace RelCat
variable {X Y Z : RelCat.{u}}

/-- The morphisms in the relation category are relations. -/
/-
**CategoryTheory.RelCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.RelCat`。
形式化陈述：CategoryTheory.RelCat → CategoryTheory.RelCat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms in the relation category are relations.
-/
structure Hom (X Y : RelCat.{u}) : Type u where
  /-- Build a morphism `X ⟶ Y` for `X Y : RelCat` from a relation between `X` and `Y`. -/
  ofRel ::
  /-- The underlying relation between `X` and `Y` of a morphism `X ⟶ Y` for `X Y : RelCat`. -/
  rel : SetRel X Y

initialize_simps_projections Hom (as_prefix rel)

set_option backward.isDefEq.respectTransparency.types false in
/-- The category of types with binary relations as morphisms. -/
/-
**CategoryTheory.RelCat.instLargeCategory** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.RelCat`。
形式化陈述：instLargeCategory : LargeCategory RelCat where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of types with binary relations as morphisms.
-/
instance instLargeCategory : LargeCategory RelCat where
  Hom := Hom
  id _ := .ofRel .id
  comp f g := .ofRel <| f.rel ○ g.rel

namespace Hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.RelCat
.Hom`。
形式化陈述：∀ {X Y : CategoryTheory.RelCat} (f g : X ⟶ Y), f.rel = g.rel → f = g
参数：f g : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] lemma ext (f g : X ⟶ Y) (h : f.rel = g.rel) : f = g := by cases f; cases g; congr

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.Hom.rel_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Rel
Cat.Hom`。
形式化陈述：∀ (X : CategoryTheory.RelCat), (CategoryTheory.CategoryStruct.id X).rel = 
SetRel.id
参数：X : CategoryTheory.RelCat；CategoryTheory.CategoryStruct.id X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected lemma rel_id (X : RelCat.{u}) : rel (𝟙 X) = .id := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.Hom.rel_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.R
elCat.Hom`。
形式化陈述：∀ {X Y Z : CategoryTheory.RelCat} (f : X ⟶ Y) (g : Y ⟶ Z),   (CategoryTheo
ry.CategoryStruct.comp f g).rel = f.rel.comp g.rel
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected lemma rel_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).rel = f.rel.comp g.rel := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.Hom.rel_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.RelCat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rel_id_apply₂ (x y : X) : x ~[rel (𝟙 X)] y ↔ x = y := .rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.Hom.rel_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.RelCat.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rel_comp_apply₂ (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    x ~[(f ≫ g).rel] z ↔ ∃ y, x ~[f.rel] y ∧ y ~[g.rel] z := .rfl

end Hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The essentially surjective faithful embedding
from the category of types and functions into the category of types and relations. -/
@[simps obj map_rel]
/-
**CategoryTheory.RelCat.graphFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.R
elCat`。
形式化陈述：graphFunctor : Type u ⥤ RelCat.{u} where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The essentially surjective faithful embedding
from the category of types and functions into the category of types and relation
s.
-/
def graphFunctor : Type u ⥤ RelCat.{u} where
  obj X := X
  map f := .ofRel (f : _ → _).graph

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.graphFunctor_faithful** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.RelCat`。
形式化陈述：graphFunctor_faithful : graphFunctor.Faithful where map_injective h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.graph_injective`：graph_injective : Injective (graph : (α -> β) 
-> SetRel α β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance graphFunctor_faithful : graphFunctor.Faithful where
  map_injective h := by
    ext
    simp [Function.graph_injective congr(($h).rel)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.graphFunctor_essSurj** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.RelCat`。
形式化陈述：graphFunctor_essSurj : graphFunctor.EssSurj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.essSurj_of_surj`：essSurj_of_surj (h : Function.Su
rjective F.obj) : EssSurj F where mem_essImage Y
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
instance graphFunctor_essSurj : graphFunctor.EssSurj :=
    graphFunctor.essSurj_of_surj Function.surjective_id

set_option backward.isDefEq.respectTransparency false in
/-- A relation is an isomorphism in `RelCat` iff it is the image of an isomorphism in
`Type u`. -/
/-
**CategoryTheory.RelCat.rel_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Re
lCat`。
形式化陈述：rel_iso_iff {X Y : RelCat} (r : X ⟶ Y) : IsIso (C
参数：r : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `Classical.axiomOfChoice`：∀ {α : Sort u} {β : α → Sort v} {r : (x : α) → 
β x → Prop}, (∀ (x : α), ∃ y, r x y) → ∃ f, ∀ (x : α), r x (f x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.RelCat.Hom.ext`：∀ {X Y : CategoryTheory.RelCat} (f g : X 
⟶ Y), f.rel = g.rel → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.RelCat.rel_graphFunctor_map`：∀ {X Y : Type u} (f : X ⟶ Y)
,   (CategoryTheory.RelCat.graphFunctor.map f).rel = Function.graph ⇑(CategoryTh
eory.ConcreteCategory.hom f)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
A relation is an isomorphism in `RelCat` iff it is the image of an isomorphism i
n
`Type u`.
-/
theorem rel_iso_iff {X Y : RelCat} (r : X ⟶ Y) :
    IsIso (C := RelCat) r ↔ ∃ f : Iso (C := Type u) X Y, graphFunctor.map f.hom = r := by
  constructor
  · intro h
    have h1 := congr_fun₂ congr((· ~[($h.hom_inv_id).rel] ·))
    have h2 := congr_fun₂ congr((· ~[($h.inv_hom_id).rel] ·))
    simp only [RelCat.Hom.rel_comp_apply₂, RelCat.Hom.rel_id_apply₂, eq_iff_iff] at h1 h2
    obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun a => (h1 a a).mpr rfl)
    obtain ⟨g, hg⟩ := Classical.axiomOfChoice (fun a => (h2 a a).mpr rfl)
    suffices hif : IsIso (C := Type u) (↾f) by
      use asIso (↾f)
      ext ⟨x, y⟩
      exact ⟨by aesop, fun hxy ↦ (h2 (f x) y).1 ⟨x, (hf x).2, hxy⟩⟩
    use ↾g
    constructor
    · ext x
      apply (h1 _ _).mp
      use f x, (hg _).2, (hf _).2
    · ext y
      apply (h2 _ _).mp
      use g y, (hf (g y)).2, (hg y).2
  · rintro ⟨f, rfl⟩
    apply graphFunctor.map_isIso

section Opposite
open Opposite

set_option backward.isDefEq.respectTransparency.types false in
/-- The argument-swap isomorphism from `RelCat` to its opposite. -/
/-
**CategoryTheory.RelCat.opFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.RelC
at`。
形式化陈述：opFunctor : RelCat ⥤ RelCatᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The argument-swap isomorphism from `RelCat` to its opposite.
-/
def opFunctor : RelCat ⥤ RelCatᵒᵖ where
  obj X := op X
  map {_ _} r := .op <| .ofRel r.rel.inv

set_option backward.isDefEq.respectTransparency.types false in
/-- The other direction of `opFunctor`. -/
/-
**CategoryTheory.RelCat.unopFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Re
lCat`。
形式化陈述：unopFunctor : RelCatᵒᵖ ⥤ RelCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The other direction of `opFunctor`.
-/
def unopFunctor : RelCatᵒᵖ ⥤ RelCat where
  obj X := unop X
  map {_ _} r := .ofRel r.unop.rel.inv

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.opFunctor_comp_unopFunctor_eq** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.RelCat`。
形式化陈述：CategoryTheory.RelCat.opFunctor.comp CategoryTheory.RelCat.unopFunctor = C
ategoryTheory.Functor.id CategoryTheory.RelCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem opFunctor_comp_unopFunctor_eq :
    Functor.comp opFunctor unopFunctor = Functor.id _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.unopFunctor_comp_opFunctor_eq** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.RelCat`。
形式化陈述：CategoryTheory.RelCat.unopFunctor.comp CategoryTheory.RelCat.opFunctor =  
 CategoryTheory.Functor.id CategoryTheory.RelCatᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem unopFunctor_comp_opFunctor_eq :
    Functor.comp unopFunctor opFunctor = Functor.id _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `RelCat` is self-dual: The map that swaps the argument order of a
relation induces an equivalence between `RelCat` and its opposite. -/
@[simps]
/-
**CategoryTheory.RelCat.opEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
RelCat`。
形式化陈述：opEquivalence : RelCat ≌ RelCatᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RelCat` is self-dual: The map that swaps the argument order of a
relation induces an equivalence between `RelCat` and its opposite.
-/
def opEquivalence : RelCat ≌ RelCatᵒᵖ where
  functor := opFunctor
  inverse := unopFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.RelCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : opFunctor.IsEquivalence := by
  change opEquivalence.functor.IsEquivalence
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.RelCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.RelCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : unopFunctor.IsEquivalence := by
  change opEquivalence.inverse.IsEquivalence
  infer_instance

end Opposite

end RelCat

end CategoryTheory

