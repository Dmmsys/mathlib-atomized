/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Computation of `Over A` for a presheaf `A`

Let `A : Cᵒᵖ ⥤ Type v` be a presheaf. In this file, we construct an equivalence
`e : Over A ≌ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` and show that there is a quasi-commutative
diagram

```
CostructuredArrow yoneda A      ⥤      Over A

                             ⇘           ⥥

                               PSh(CostructuredArrow yoneda A)
```

where the top arrow is the forgetful functor forgetting the yoneda-costructure, the right arrow is
the aforementioned equivalence and the diagonal arrow is the Yoneda embedding.

In the notation of Kashiwara-Schapira, the type of the equivalence is written `C^ₐ ≌ Cₐ^`, where
`·ₐ` is `CostructuredArrow` (with the functor `S` being either the identity or the Yoneda
embedding) and `^` is taking presheaves. The equivalence is a key ingredient in various results in
Kashiwara-Schapira.

The proof is somewhat long and technical, in part due to the construction inherently involving a
sigma type which comes with the usual DTT issues. However, a user of this result should not need
to interact with the actual construction, the mere existence of the equivalence and the commutative
triangle should generally be sufficient.

## Main results
* `overEquivPresheafCostructuredArrow`:
  the equivalence `Over A ≌ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`
* `CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow`: the natural isomorphism
  `CostructuredArrow.toOver yoneda A ⋙ (overEquivPresheafCostructuredArrow A).functor ≅ yoneda`

## Implementation details

The proof needs to introduce "correction terms" in various places in order to overcome DTT issues,
and these need to be canceled against each other when appropriate. It is important to deal with
these in a structured manner, otherwise you get large goals containing many correction terms which
are very tedious to manipulate. We avoid this blowup by carefully controlling which definitions
`(d)simp` is allowed to unfold and stating many lemmas explicitly before they are required. This
leads to manageable goals containing only a small number of correction terms. Generally, we use
the form `F.map (eqToHom _)` for these correction terms and try to push them as far outside as
possible.

## Future work
* If needed, it should be possible to show that the equivalence is natural in `A`.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 1.4.12

## Tags
presheaf, over category, coyoneda

-/

@[expose] public section

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

namespace OverPresheafAux

/-! ### Construction of the forward functor `Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` -/

/-- Via the Yoneda lemma, `u : F.obj (op X)` defines a natural transformation `yoneda.obj X ⟶ F`
and via the element `η.app (op X) u` also a morphism `yoneda.obj X ⟶ A`. This structure
witnesses the fact that these morphisms form a commutative triangle with `η : F ⟶ A`, i.e.,
that `yoneda.obj X ⟶ F` lifts to a morphism in `Over A`. -/
/-
**CategoryTheory.OverPresheafAux.MakesOverArrow** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.OverPresheafAux`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {A F : Ca
tegoryTheory.Functor Cᵒᵖ (Type v)} →       (F ⟶ A) → {X : C} → (CategoryTheory.y
oneda.obj X ⟶ A) → F.obj (Opposite.op X) → Prop
参数：Type v；F ⟶ A；CategoryTheory.yoneda.obj X ⟶ A；Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Via the Yoneda lemma, `u : F.obj (op X)` defines a natural transformation `yoned
a.obj X ⟶ F`
and via the element `η.app (op X) u` also a morphism `yoneda.obj X ⟶ A`. This st
ructure
witnesses the fact that these morphisms form a commutative triangle with `η : F 
⟶ A`, i.e.,
that `yoneda.obj X ⟶ F` lifts to a morphism in `Over A`.
-/
structure MakesOverArrow {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A)
    (u : F.obj (op X)) : Prop where
  app : η.app (op X) u = yonedaEquiv s

namespace MakesOverArrow

/-- "Functoriality" of `MakesOverArrow η s` in `η`. -/
/-
**CategoryTheory.OverPresheafAux.MakesOverArrow.map** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.OverPresheafAux.MakesOverArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Functoriality" of `MakesOverArrow η s` in `η`.
-/
lemma map₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {ε : F ⟶ G}
    (hε : ε ≫ μ = η) {X : C} {s : yoneda.obj X ⟶ A} {u : F.obj (op X)}
    (h : MakesOverArrow η s u) : MakesOverArrow μ s (ε.app _ u) :=
  ⟨by rw [← comp_apply, ← NatTrans.comp_app, hε, h.app]⟩

/-- Functoriality of `MakesOverArrow η s` in `s`. -/
/-
**CategoryTheory.OverPresheafAux.MakesOverArrow.map** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.OverPresheafAux.MakesOverArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `MakesOverArrow η s` in `s`.
-/
lemma map₂ {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    {u : F.obj (op Y)} (h : MakesOverArrow η t u) : MakesOverArrow η s (F.map f.op u) :=
  ⟨by simp [h.app, yonedaEquiv_naturality, hst]⟩
/-
**CategoryTheory.OverPresheafAux.MakesOverArrow.of_arrow** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.OverPresheafAux.MakesOverArrow`。
形式化陈述：of_arrow {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f 
: yoneda.obj X ⟶ F} (hf : f ≫ η = s) : MakesOverArrow η s (yonedaEquiv f)
参数：hf : f ≫ η = s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_arrow {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {f : yoneda.obj X ⟶ F} (hf : f ≫ η = s) : MakesOverArrow η s (yonedaEquiv f) :=
  ⟨hf ▸ rfl⟩
/-
**CategoryTheory.OverPresheafAux.MakesOverArrow.of_yoneda_arrow** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.OverPresheafAux.MakesOverArrow`。
形式化陈述：of_yoneda_arrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶
 A} {f : X ⟶ Y} (hf : yoneda.map f ≫ η = s) : MakesOverArrow η s f
参数：hf : yoneda.map f ≫ η = s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.yonedaEquiv_yoneda_map`：yonedaEquiv_yoneda_map {X Y : C} 
(f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f
· 使用引理 `CategoryTheory.OverPresheafAux.MakesOverArrow.of_arrow`：of_arrow {F : Cᵒ
ᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : yoneda.obj X ⟶ F} (h
f : f ≫ η = s) : MakesOverArrow η s (yonedaE…
-/
lemma of_yoneda_arrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yoneda.map f ≫ η = s) : MakesOverArrow η s f := by
  simpa only [yonedaEquiv_yoneda_map f] using of_arrow hf

end MakesOverArrow

/-- This is equivalent to the type `Over.mk s ⟶ Over.mk η`, but that lives in the wrong universe.
However, if `F = yoneda.obj Y` for some `Y`, then (using that the Yoneda embedding is fully
faithful) we get a good statement, see `OverArrow.costructuredArrowIso`. -/
/-
**CategoryTheory.OverPresheafAux.OverArrows** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.OverPresheafAux`。
形式化陈述：OverArrows {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) :
 Type v
参数：η : F ⟶ A；s : yoneda.obj X ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is equivalent to the type `Over.mk s ⟶ Over.mk η`, but that lives in the wr
ong universe.
However, if `F = yoneda.obj Y` for some `Y`, then (using that the Yoneda embeddi
ng is fully
faithful) we get a good statement, see `OverArrow.costructuredArrowIso`.
-/
def OverArrows {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) : Type v :=
  Subtype (MakesOverArrow η s)

namespace OverArrows
/-- Since `OverArrows η s` can be thought of to contain certain morphisms `yoneda.obj X ⟶ F`, the
Yoneda lemma yields elements `F.obj (op X)`. -/
/-
**CategoryTheory.OverPresheafAux.OverArrows.val** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.OverPresheafAux.OverArrows`。
形式化陈述：val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} : OverAr
rows η s -> F.obj (op X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Since `OverArrows η s` can be thought of to contain certain morphisms `yoneda.ob
j X ⟶ F`, the
Yoneda lemma yields elements `F.obj (op X)`.
-/
def val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} :
    OverArrows η s → F.obj (op X) :=
  Subtype.val

@[simp]
/-
**CategoryTheory.OverPresheafAux.OverArrows.val_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.OverPresheafAux.OverArrows`。
形式化陈述：val_mk {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) (u : 
F.obj (op X)) (h : MakesOverArrow η s u) : val ⟨u, h⟩ = u
参数：η : F ⟶ A；s : yoneda.obj X ⟶ A；u : F.obj (op X)；h : MakesOverArrow η s u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_mk {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) {X : C} (s : yoneda.obj X ⟶ A) (u : F.obj (op X))
    (h : MakesOverArrow η s u) : val ⟨u, h⟩ = u :=
  rfl

@[ext]
/-
**CategoryTheory.OverPresheafAux.OverArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.OverPresheafAux.OverArrows`。
形式化陈述：ext {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {u v : O
verArrows η s} : u.val = v.val -> u = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma ext {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    {u v : OverArrows η s} : u.val = v.val → u = v :=
  Subtype.ext

/-- The defining property of `OverArrows.val`. -/
/-
**CategoryTheory.OverPresheafAux.OverArrows.app_val** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.OverPresheafAux.OverArrows`。
形式化陈述：app_val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (p :
 OverArrows η s) : η.app (op X) p.val = yonedaEquiv s
参数：p : OverArrows η s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.OverPresheafAux.MakesOverArrow.app`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {A F : CategoryTheory.Functor Cᵒᵖ (Type v)} 
{η : F ⟶ A} {X : C}   {s : CategoryTheo…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The defining property of `OverArrows.val`.
-/
lemma app_val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : OverArrows η s) : η.app (op X) p.val = yonedaEquiv s :=
  p.prop.app

/-- In the special case `F = yoneda.obj Y`, the element `p.val` for `p : OverArrows η s` is itself
a morphism `X ⟶ Y`. -/
@[simp]
/-
**CategoryTheory.OverPresheafAux.OverArrows.map_val** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.OverPresheafAux.OverArrows`。
形式化陈述：map_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (p :
 OverArrows η s) : yoneda.map p.val ≫ η = s
参数：p : OverArrows η s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `CategoryTheory.yonedaEquiv_comp`：yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ T
ype v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) : yonedaEquiv (α ≫ β) = β.app _ (yone
daEquiv α)
· 使用引理 `CategoryTheory.yonedaEquiv_yoneda_map`：yonedaEquiv_yoneda_map {X Y : C} 
(f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.OverPresheafAux.OverArrows.app_val`：app_val {F : Cᵒᵖ ⥤ Ty
pe v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (p : OverArrows η s) : η.app (o
p X) p.val = yonedaEquiv s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the special case `F = yoneda.obj Y`, the element `p.val` for `p : OverArrows 
η s` is itself
a morphism `X ⟶ Y`.
-/
lemma map_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (p : OverArrows η s) : yoneda.map p.val ≫ η = s := by
  rw [← yonedaEquiv.injective.eq_iff, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  simp only [unop_op, p.app_val]

/-- Functoriality of `OverArrows η s` in `η`. -/
/-
**CategoryTheory.OverPresheafAux.OverArrows.map** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.OverPresheafAux.OverArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `OverArrows η s` in `η`.
-/
def map₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
    (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) : OverArrows μ s :=
  ⟨ε.app _ u.val, MakesOverArrow.map₁ hε u.2⟩

@[simp]
/-
**CategoryTheory.OverPresheafAux.OverArrows.map** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.OverPresheafAux.OverArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_val {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} {X : C}
    (s : yoneda.obj X ⟶ A) (u : OverArrows η s) (ε : F ⟶ G) (hε : ε ≫ μ = η) :
    (u.map₁ ε hε).val = ε.app _ u.val :=
  rfl

/-- Functoriality of `OverArrows η s` in `s`. -/
/-
**CategoryTheory.OverPresheafAux.OverArrows.map** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.OverPresheafAux.OverArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `OverArrows η s` in `s`.
-/
def map₂ {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} {s : yoneda.obj X ⟶ A}
    {t : yoneda.obj Y ⟶ A} (u : OverArrows η t) (f : X ⟶ Y) (hst : yoneda.map f ≫ t = s) :
    OverArrows η s :=
  ⟨F.map f.op u.val, MakesOverArrow.map₂ f hst u.2⟩

@[simp]
/-
**CategoryTheory.OverPresheafAux.OverArrows.map** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.OverPresheafAux.OverArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_val {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X Y : C} (f : X ⟶ Y)
    {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (hst : yoneda.map f ≫ t = s)
    (u : OverArrows η t) : (u.map₂ f hst).val = F.map f.op u.val :=
  rfl

@[simp]
/-
**CategoryTheory.OverPresheafAux.OverArrows.map** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.OverPresheafAux.OverArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_map₂ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) {X Y : C} {s : yoneda.obj X ⟶ A} {t : yoneda.obj Y ⟶ A} (f : X ⟶ Y)
    (hf : yoneda.map f ≫ t = s) (u : OverArrows η t) :
    (u.map₁ ε hε).map₂ f hf = (u.map₂ f hf).map₁ ε hε :=
  OverArrows.ext <| (elementwise_of% (ε.naturality f.op).symm) u.val

/-- Construct an element of `OverArrows η s` with `F = yoneda.obj Y` from a suitable morphism
`f : X ⟶ Y`. -/
/-
**CategoryTheory.OverPresheafAux.OverArrows.yonedaArrow** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.OverPresheafAux.OverArrows`。
形式化陈述：yonedaArrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} 
(f : X ⟶ Y) (hf : yoneda.map f ≫ η = s) : OverArrows η s
参数：f : X ⟶ Y；hf : yoneda.map f ≫ η = s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.OverPresheafAux.MakesOverArrow.of_yoneda_arrow`：of_yoneda
_arrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
 (hf : yoneda.map f ≫ η = s) : MakesOverArrow η s f

--- 原说明 ---
Construct an element of `OverArrows η s` with `F = yoneda.obj Y` from a suitable
 morphism
`f : X ⟶ Y`.
-/
def yonedaArrow {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (f : X ⟶ Y)
    (hf : yoneda.map f ≫ η = s) : OverArrows η s :=
  ⟨f, .of_yoneda_arrow hf⟩

@[simp]
/-
**CategoryTheory.OverPresheafAux.OverArrows.yonedaArrow_val** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.OverPresheafAux.OverArrows`。
形式化陈述：yonedaArrow_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶
 A} {f : X ⟶ Y} (hf : yoneda.map f ≫ η = s) : (yonedaArrow f hf).val = f
参数：hf : yoneda.map f ≫ η = s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaArrow_val {Y : C} {η : yoneda.obj Y ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {f : X ⟶ Y}
    (hf : yoneda.map f ≫ η = s) : (yonedaArrow f hf).val = f :=
  rfl

/-- If `η` is also `yoneda`-costructured, then `OverArrows η s` is just morphisms of costructured
arrows. -/
/-
**CategoryTheory.OverPresheafAux.OverArrows.costructuredArrowIso** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.OverPresheafAux.OverArrows`。
形式化陈述：costructuredArrowIso (s t : CostructuredArrow yoneda A) : (OverArrows s.ho
m t.hom) ≅ (t ⟶ s) where hom
参数：s t : CostructuredArrow yoneda A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `η` is also `yoneda`-costructured, then `OverArrows η s` is just morphisms of
 costructured
arrows.
-/
def costructuredArrowIso (s t : CostructuredArrow yoneda A) :
    (OverArrows s.hom t.hom) ≅ (t ⟶ s) where
  hom := ↾fun p ↦ CostructuredArrow.homMk p.val (by simp)
  inv := ↾fun f ↦ yonedaArrow f.left f.w

end OverArrows

/-- This is basically just `yoneda.obj η : (Over A)ᵒᵖ ⥤ Type (max u v)` restricted along the
forgetful functor `CostructuredArrow yoneda A ⥤ Over A`, but done in a way that we land in a
smaller universe. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.restrictedYonedaObj** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.OverPresheafAux`。
形式化陈述：restrictedYonedaObj {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) : (CostructuredArrow yo
neda A)ᵒᵖ ⥤ Type v where obj s
参数：η : F ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is basically just `yoneda.obj η : (Over A)ᵒᵖ ⥤ Type (max u v)` restricted a
long the
forgetful functor `CostructuredArrow yoneda A ⥤ Over A`, but done in a way that 
we land in a
smaller universe.
-/
def restrictedYonedaObj {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) :
    (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v where
  obj s := OverArrows η s.unop.hom
  map f := ↾fun u ↦ u.map₂ f.unop.left f.unop.w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functoriality of `restrictedYonedaObj η` in `η`. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.restrictedYonedaObjMap** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.OverPresheafAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `restrictedYonedaObj η` in `η`.
-/
def restrictedYonedaObjMap₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) : restrictedYonedaObj η ⟶ restrictedYonedaObj μ where
  app _ := ↾fun u ↦ u.map₁ ε hε

set_option backward.isDefEq.respectTransparency.types false in
/--
This is basically just `yoneda : Over A ⥤ (Over A)ᵒᵖ ⥤ Type (max u v)` restricted in the second
argument along the forgetful functor `CostructuredArrow yoneda A ⥤ Over A`, but done in a way
that we land in a smaller universe.

This is one direction of the equivalence we're constructing. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.restrictedYoneda** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.OverPresheafAux`。
形式化陈述：restrictedYoneda (A : Cᵒᵖ ⥤ Type v) : Over A ⥤ (CostructuredArrow yoneda A
)ᵒᵖ ⥤ Type v where obj η
参数：A : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is basically just `yoneda : Over A ⥤ (Over A)ᵒᵖ ⥤ Type (max u v)` restricte
d in the second
argument along the forgetful functor `CostructuredArrow yoneda A ⥤ Over A`, but 
done in a way
that we land in a smaller universe.

This is one direction of the equivalence we're constructing.
-/
def restrictedYoneda (A : Cᵒᵖ ⥤ Type v) :
    Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v where
  obj η := restrictedYonedaObj η.hom
  map ε := restrictedYonedaObjMap₁ ε.left ε.w

/-- Further restricting the functor
`restrictedYoneda : Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` along the forgetful
functor in the first argument recovers the Yoneda embedding
`CostructuredArrow yoneda A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`. This basically follows
from the fact that the Yoneda embedding on `C` is fully faithful. -/
/-
**CategoryTheory.OverPresheafAux.toOverYonedaCompRestrictedYoneda** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：toOverYonedaCompRestrictedYoneda (A : Cᵒᵖ ⥤ Type v) : CostructuredArrow.to
Over yoneda A ⋙ restrictedYoneda A ≅ yoneda
参数：A : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Further restricting the functor
`restrictedYoneda : Over A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` along the 
forgetful
functor in the first argument recovers the Yoneda embedding
`CostructuredArrow yoneda A ⥤ (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`. This bas
ically follows
from the fact that the Yoneda embedding on `C` is fully faithful.
-/
def toOverYonedaCompRestrictedYoneda (A : Cᵒᵖ ⥤ Type v) :
    CostructuredArrow.toOver yoneda A ⋙ restrictedYoneda A ≅ yoneda :=
  NatIso.ofComponents
    (fun s => NatIso.ofComponents (fun _ => OverArrows.costructuredArrowIso _ _) (by cat_disch))
    (by cat_disch)

/-! ### Construction of the backward functor
`((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Over A` -/

/-
**CategoryTheory.OverPresheafAux.map_mkPrecomp_eqToHom** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.OverPresheafAux`。
形式化陈述：map_mkPrecomp_eqToHom {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X Y :
 C} {f : X ⟶ Y} {g g' : yoneda.obj Y ⟶ A} (h : g = g') {x : F.obj (op (Costructu
redArrow.mk g'))} : F.map (CostructuredArrow.mkPrecomp g f).op (F.map (eqToHom (
by rw [h])) x) = F.map (eqToHom (by rw [h])) (F.map (CostructuredArrow.mkPrecomp
 g' f).op x)
参数：CostructuredArrow yoneda A；h : g = g'；op (CostructuredArrow.mk g')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Construction of the backward functor
`((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Over A`
-/
lemma map_mkPrecomp_eqToHom {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X Y : C} {f : X ⟶ Y}
    {g g' : yoneda.obj Y ⟶ A} (h : g = g')
    {x : F.obj (op (CostructuredArrow.mk g'))} :
    F.map (CostructuredArrow.mkPrecomp g f).op (F.map (eqToHom (by rw [h])) x) =
      F.map (eqToHom (by rw [h])) (F.map (CostructuredArrow.mkPrecomp g' f).op x) := by
  cat_disch

attribute [local simp] map_mkPrecomp_eqToHom

/--
To give an object of `Over A`, we will in particular need a presheaf `Cᵒᵖ ⥤ Type v`. This is
the definition of that presheaf on objects.

We would prefer to think of this sigma type to be indexed by natural transformations
`yoneda.obj X ⟶ A` instead of `A.obj (op X)`. These are equivalent by the Yoneda lemma, but
we cannot use the former because that type lives in the wrong universe. Hence, we will provide
a lot of API that will enable us to pretend that we are really indexing over
`yoneda.obj X ⟶ A`. -/
/-
**CategoryTheory.OverPresheafAux.YonedaCollection** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.OverPresheafAux`。
形式化陈述：YonedaCollection (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (X : C) : T
ype v
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v；X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
To give an object of `Over A`, we will in particular need a presheaf `Cᵒᵖ ⥤ Type
 v`. This is
the definition of that presheaf on objects.

We would prefer to think of this sigma type to be indexed by natural transformat
ions
`yoneda.obj X ⟶ A` instead of `A.obj (op X)`. These are equivalent by the Yoneda
 lemma, but
we cannot use the former because that type lives in the wrong universe. Hence, w
e will provide
a lot of API that will enable us to pretend that we are really indexing over
`yoneda.obj X ⟶ A`.
-/
def YonedaCollection (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (X : C) : Type v :=
  Σ s : A.obj (op X), F.obj (op (CostructuredArrow.mk (yonedaEquiv.symm s)))

namespace YonedaCollection

variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}

/-- Given a costructured arrow `s : yoneda.obj X ⟶ A` and an element `x : F.obj s`, construct
an element of `YonedaCollection F X`. -/
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.mk** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：mk (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : Yone
daCollection F X
参数：s : yoneda.obj X ⟶ A；x : F.obj (op (CostructuredArrow.mk s))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a costructured arrow `s : yoneda.obj X ⟶ A` and an element `x : F.obj s`, 
construct
an element of `YonedaCollection F X`.
-/
def mk (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : YonedaCollection F X :=
  ⟨yonedaEquiv s, F.map (eqToHom <| by rw [Equiv.symm_apply_apply]) x⟩

/-- Access the first component of an element of `YonedaCollection F X`. -/
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.fst** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：fst (p : YonedaCollection F X) : yoneda.obj X ⟶ A
参数：p : YonedaCollection F X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Access the first component of an element of `YonedaCollection F X`.
-/
def fst (p : YonedaCollection F X) : yoneda.obj X ⟶ A :=
  yonedaEquiv.symm p.1

/-- Access the second component of an element of `YonedaCollection F X`. -/
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.snd** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：snd (p : YonedaCollection F X) : F.obj (op (CostructuredArrow.mk p.fst))
参数：p : YonedaCollection F X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Access the second component of an element of `YonedaCollection F X`.
-/
def snd (p : YonedaCollection F X) : F.obj (op (CostructuredArrow.mk p.fst)) :=
  p.2

/-- This is a definition because it will be helpful to be able to control precisely when this
definition is unfolded. -/
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.yonedaEquivFst** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：yonedaEquivFst (p : YonedaCollection F X) : A.obj (op X)
参数：p : YonedaCollection F X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a definition because it will be helpful to be able to control precisely 
when this
definition is unfolded.
-/
def yonedaEquivFst (p : YonedaCollection F X) : A.obj (op X) :=
  yonedaEquiv p.fst
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.yonedaEquivFst_eq** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：yonedaEquivFst_eq (p : YonedaCollection F X) : p.yonedaEquivFst = yonedaEq
uiv p.fst
参数：p : YonedaCollection F X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma yonedaEquivFst_eq (p : YonedaCollection F X) : p.yonedaEquivFst = yonedaEquiv p.fst :=
  rfl

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.mk_fst** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：mk_fst (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : 
(mk s x).fst = s
参数：s : yoneda.obj X ⟶ A；x : F.obj (op (CostructuredArrow.mk s))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mk_fst (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : (mk s x).fst = s :=
  Equiv.apply_symm_apply _ _

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.mk_snd** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：mk_snd (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : 
(mk s x).snd = F.map (eqToHom <| by rw [YonedaCollection.mk_fst]) x
参数：s : yoneda.obj X ⟶ A；x : F.obj (op (CostructuredArrow.mk s))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_snd (s : yoneda.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) :
    (mk s x).snd = F.map (eqToHom <| by rw [YonedaCollection.mk_fst]) x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[ext (iff := false)]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.ext** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
形式化陈述：ext {p q : YonedaCollection F X} (h : p.fst = q.fst) (h' : F.map (eqToHom 
<| by rw [h]) q.snd = p.snd) : p = q
参数：h : p.fst = q.fst；h' : F.map (eqToHom <| by rw [h]) q.snd = p.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma ext {p q : YonedaCollection F X} (h : p.fst = q.fst)
    (h' : F.map (eqToHom <| by rw [h]) q.snd = p.snd) : p = q := by
  rcases p with ⟨p, p'⟩
  rcases q with ⟨q, q'⟩
  obtain rfl : p = q := yonedaEquiv.symm.injective h
  exact Sigma.ext rfl (by simpa [snd] using! h'.symm)

/-- Functoriality of `YonedaCollection F X` in `F`. -/
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `YonedaCollection F X` in `F`.
-/
def map₁ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) :
    YonedaCollection F X → YonedaCollection G X :=
  fun p => YonedaCollection.mk p.fst (η.app _ p.snd)

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_fst {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).fst = p.fst := by
  simp [map₁]

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_yonedaEquivFst {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) :
    (YonedaCollection.map₁ η p).yonedaEquivFst = p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₁_fst]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_snd {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (p : YonedaCollection F X) : (YonedaCollection.map₁ η p).snd =
      G.map (eqToHom (by rw [YonedaCollection.map₁_fst])) (η.app _ p.snd) := by
  simp [map₁]

/-- Functoriality of `YonedaCollection F X` in `X`. -/
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `YonedaCollection F X` in `X`.
-/
def map₂ (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) : YonedaCollection F X :=
  YonedaCollection.mk (yoneda.map f ≫ p.fst) <| F.map (CostructuredArrow.mkPrecomp p.fst f).op p.snd

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_fst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).fst = yoneda.map f ≫ p.fst := by
  simp [map₂]

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_yonedaEquivFst {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).yonedaEquivFst = A.map f.op p.yonedaEquivFst := by
  simp only [YonedaCollection.yonedaEquivFst_eq, map₂_fst, yonedaEquiv_naturality]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_snd {Y : C} (f : X ⟶ Y) (p : YonedaCollection F Y) :
    (YonedaCollection.map₂ F f p).snd = F.map ((CostructuredArrow.mkPrecomp p.fst f).op ≫
      eqToHom (by rw [YonedaCollection.map₂_fst f])) p.snd := by
  simp [map₂]

attribute [local simp] CostructuredArrow.mkPrecomp_id CostructuredArrow.mkPrecomp_comp

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_id : YonedaCollection.map₁ (𝟙 F) (X := X) = id := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_comp {G H : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) (μ : G ⟶ H) :
    YonedaCollection.map₁ (η ≫ μ) (X := X) =
      YonedaCollection.map₁ μ (X := X) ∘ YonedaCollection.map₁ η (X := X) := by
  ext; all_goals simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_id : YonedaCollection.map₂ F (𝟙 X) = id := by
  ext; all_goals simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_comp {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    YonedaCollection.map₂ F (f ≫ g) = YonedaCollection.map₂ F f ∘ YonedaCollection.map₂ F g := by
  ext; all_goals simp

@[simp]
/-
**CategoryTheory.OverPresheafAux.YonedaCollection.map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.OverPresheafAux.YonedaCollection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₁_map₂ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) :
    YonedaCollection.map₂ G f (YonedaCollection.map₁ η p) =
      YonedaCollection.map₁ η (YonedaCollection.map₂ F f p) := by
  ext; all_goals simp

end YonedaCollection

/-- Given `F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`, this is the presheaf that is given by
`YonedaCollection F X` on objects. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.yonedaCollectionPresheaf** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：yonedaCollectionPresheaf (A : Cᵒᵖ ⥤ Type v) (F : (CostructuredArrow yoneda
 A)ᵒᵖ ⥤ Type v) : Cᵒᵖ ⥤ Type v where obj X
参数：A : Cᵒᵖ ⥤ Type v；F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v`, this is the presheaf that i
s given by
`YonedaCollection F X` on objects.
-/
def yonedaCollectionPresheaf (A : Cᵒᵖ ⥤ Type v) (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    Cᵒᵖ ⥤ Type v where
  obj X := YonedaCollection F X.unop
  map f := ↾(YonedaCollection.map₂ F f.unop)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Functoriality of `yonedaCollectionPresheaf A F` in `F`. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.yonedaCollectionPresheafMap** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.OverPresheafAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `yonedaCollectionPresheaf A F` in `F`.
-/
def yonedaCollectionPresheafMap₁ {F G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G) :
    yonedaCollectionPresheaf A F ⟶ yonedaCollectionPresheaf A G where
  app _ := ↾(YonedaCollection.map₁ η)
  naturality := by
    intros
    ext
    simp

/-- This is the functor `F ↦ X ↦ YonedaCollection F X`. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.yonedaCollectionFunctor** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：yonedaCollectionFunctor (A : Cᵒᵖ ⥤ Type v) : ((CostructuredArrow yoneda A)
ᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ Type v where obj
参数：A : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the functor `F ↦ X ↦ YonedaCollection F X`.
-/
def yonedaCollectionFunctor (A : Cᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ Type v where
  obj := yonedaCollectionPresheaf A
  map η := yonedaCollectionPresheafMap₁ η

set_option backward.defeqAttrib.useBackward true in
/-- The Yoneda lemma yields a natural transformation `yonedaCollectionPresheaf A F ⟶ A`. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.yonedaCollectionPresheafToA** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：yonedaCollectionPresheafToA (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) 
: yonedaCollectionPresheaf A F ⟶ A where app _
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda lemma yields a natural transformation `yonedaCollectionPresheaf A F ⟶
 A`.
-/
def yonedaCollectionPresheafToA (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    yonedaCollectionPresheaf A F ⟶ A where
  app _ := ↾(YonedaCollection.yonedaEquivFst)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- This is the reverse direction of the equivalence we're constructing. -/
@[simps! obj map]
/-
**CategoryTheory.OverPresheafAux.costructuredArrowPresheafToOver** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：costructuredArrowPresheafToOver (A : Cᵒᵖ ⥤ Type v) : ((CostructuredArrow y
oneda A)ᵒᵖ ⥤ Type v) ⥤ Over A
参数：A : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the reverse direction of the equivalence we're constructing.
-/
def costructuredArrowPresheafToOver (A : Cᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Over A :=
  (yonedaCollectionFunctor A).toOver _ (yonedaCollectionPresheafToA) (by cat_disch)

section unit

/-! ### Construction of the unit -/

/-- Forward direction of the unit. -/
/-
**CategoryTheory.OverPresheafAux.unitForward** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.OverPresheafAux`。
形式化陈述：unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) : YonedaCollection (res
trictedYonedaObj η) X -> F.obj (op X)
参数：η : F ⟶ A；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forward direction of the unit.
-/
def unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X → F.obj (op X) :=
  fun p => p.snd.val

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.unitForward_naturality** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.OverPresheafAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitForward_naturality₁ {F G : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {μ : G ⟶ A} (ε : F ⟶ G)
    (hε : ε ≫ μ = η) (X : C) (p : YonedaCollection (restrictedYonedaObj η) X) :
    unitForward μ X (p.map₁ (restrictedYonedaObjMap₁ ε hε)) = ε.app _ (unitForward η X p) := by
  simp [unitForward]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.unitForward_naturality** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.OverPresheafAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitForward_naturality₂ {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X Y : C) (f : X ⟶ Y)
    (p : YonedaCollection (restrictedYonedaObj η) Y) :
    unitForward η X (YonedaCollection.map₂ (restrictedYonedaObj η) f p) =
      F.map f.op (unitForward η Y p) := by
  simp [unitForward]

@[simp]
/-
**CategoryTheory.OverPresheafAux.app_unitForward** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.OverPresheafAux`。
形式化陈述：app_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : Cᵒᵖ) (p : YonedaCollec
tion (restrictedYonedaObj η) X.unop) : η.app X (unitForward η X.unop p) = p.yone
daEquivFst
参数：η : F ⟶ A；X : Cᵒᵖ；p : YonedaCollection (restrictedYonedaObj η) X.unop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.OverPresheafAux.OverArrows.app_val`：app_val {F : Cᵒᵖ ⥤ Ty
pe v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (p : OverArrows η s) : η.app (o
p X) p.val = yonedaEquiv s
-/
lemma app_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : Cᵒᵖ)
    (p : YonedaCollection (restrictedYonedaObj η) X.unop) :
    η.app X (unitForward η X.unop p) = p.yonedaEquivFst := by
  simpa [unitForward] using! p.snd.app_val

set_option backward.isDefEq.respectTransparency false in
/-- Backward direction of the unit. -/
/-
**CategoryTheory.OverPresheafAux.unitBackward** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.OverPresheafAux`。
形式化陈述：unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) : F.obj (op X) -> Yone
daCollection (restrictedYonedaObj η) X
参数：η : F ⟶ A；X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Backward direction of the unit.
-/
def unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    F.obj (op X) → YonedaCollection (restrictedYonedaObj η) X :=
  fun x => YonedaCollection.mk (yonedaEquiv.symm (η.app _ x)) ⟨x, ⟨by simp⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.OverPresheafAux.unitForward_unitBackward** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：unitForward_unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) : unitForw
ard η X ∘ unitBackward η X = id
参数：η : F ⟶ A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `CategoryTheory.CostructuredArrow.eqToHom_left`：eqToHom_left {X Y : Costr
ucturedArrow S T} (h : X = Y) : (eqToHom h).left = eqToHom (by rw [h])
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.OverPresheafAux.restrictedYonedaObj_map`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {A F : CategoryTheory.Functor Cᵒᵖ (Type
 v)} (η : F ⟶ A)   {X Y : (CategoryTheory.Co…
· 使用定理 `CategoryTheory.OverPresheafAux.OverArrows.map₂.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {A F : CategoryTheory.Functor Cᵒᵖ (T
ype v)} {η : F ⟶ A}   {X Y : C} {s : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitForward_unitBackward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    unitForward η X ∘ unitBackward η X = id :=
  funext fun x => by simp [unitForward, unitBackward]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.OverPresheafAux.unitBackward_unitForward** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：unitBackward_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) : unitBack
ward η X ∘ unitForward η X = id
参数：η : F ⟶ A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.OverPresheafAux.YonedaCollection.ext`：ext {p q : YonedaCo
llection F X} (h : p.fst = q.fst) (h' : F.map (eqToHom <| by rw [h]) q.snd = p.s
nd) : p = q
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.OverPresheafAux.YonedaCollection.mk_fst`：mk_fst (s : yone
da.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : (mk s x).fst = s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `CategoryTheory.OverPresheafAux.OverArrows.app_val`：app_val {F : Cᵒᵖ ⥤ Ty
pe v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (p : OverArrows η s) : η.app (o
p X) p.val = yonedaEquiv s
· 使用引理 `CategoryTheory.OverPresheafAux.OverArrows.ext`：ext {F : Cᵒᵖ ⥤ Type v} {η
 : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {u v : OverArrows η s} : u.val = v.val 
-> u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `CategoryTheory.CostructuredArrow.eqToHom_left`：eqToHom_left {X Y : Costr
ucturedArrow S T} (h : X = Y) : (eqToHom h).left = eqToHom (by rw [h])
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.OverPresheafAux.restrictedYonedaObj_map`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {A F : CategoryTheory.Functor Cᵒᵖ (Type
 v)} (η : F ⟶ A)   {X Y : (CategoryTheory.Co…
· 使用定理 `CategoryTheory.OverPresheafAux.OverArrows.map₂.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {A F : CategoryTheory.Functor Cᵒᵖ (T
ype v)} {η : F ⟶ A}   {X Y : C} {s : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitBackward_unitForward {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    unitBackward η X ∘ unitForward η X = id := by
  refine funext fun p => YonedaCollection.ext ?_ (OverArrows.ext ?_)
  · simpa [unitForward, unitBackward] using congrArg yonedaEquiv.symm p.snd.app_val
  · simp [unitForward, unitBackward]

/-- Intermediate stage of assembling the unit. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.unitAuxAuxAux** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.OverPresheafAux`。
形式化陈述：unitAuxAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) : YonedaCollection (r
estrictedYonedaObj η) X ≅ F.obj (op X) where hom
参数：η : F ⟶ A；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate stage of assembling the unit.
-/
def unitAuxAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) (X : C) :
    YonedaCollection (restrictedYonedaObj η) X ≅ F.obj (op X) where
  hom := ↾(unitForward η X)
  inv := ↾(unitBackward η X)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitBackward_unitForward η X))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (unitForward_unitBackward η X))

set_option backward.defeqAttrib.useBackward true in
/-- Intermediate stage of assembling the unit. -/
@[simps! inv_app hom_app]
/-
**CategoryTheory.OverPresheafAux.unitAuxAux** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.OverPresheafAux`。
形式化陈述：unitAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) : yonedaCollectionPresheaf A (re
strictedYonedaObj η) ≅ F
参数：η : F ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate stage of assembling the unit.
-/
def unitAuxAux {F : Cᵒᵖ ⥤ Type v} (η : F ⟶ A) :
    yonedaCollectionPresheaf A (restrictedYonedaObj η) ≅ F :=
  NatIso.ofComponents (fun X => unitAuxAuxAux η X.unop)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Intermediate stage of assembling the unit. -/
@[simps! hom_left]
/-
**CategoryTheory.OverPresheafAux.unitAux** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.OverPresheafAux`。
形式化陈述：unitAux (η : Over A) : (restrictedYoneda A ⋙ costructuredArrowPresheafToOv
er A).obj η ≅ η
参数：η : Over A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate stage of assembling the unit.
-/
def unitAux (η : Over A) : (restrictedYoneda A ⋙ costructuredArrowPresheafToOver A).obj η ≅ η :=
  Over.isoMk (unitAuxAux η.hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit of the equivalence we're constructing. -/
/-
**CategoryTheory.OverPresheafAux.unit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
OverPresheafAux`。
形式化陈述：unit (A : Cᵒᵖ ⥤ Type v) : 𝟭 (Over A) ≅ restrictedYoneda A ⋙ costructuredAr
rowPresheafToOver A
参数：A : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of the equivalence we're constructing.
-/
def unit (A : Cᵒᵖ ⥤ Type v) : 𝟭 (Over A) ≅ restrictedYoneda A ⋙ costructuredArrowPresheafToOver A :=
  Iso.symm <| NatIso.ofComponents unitAux

end unit

/-! ### Construction of the counit -/

section counit

variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.OverArrows.yonedaCollectionPresheafToA_val_fst*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.OverPresheafAux.OverArrows`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheo
ry.Functor Cᵒᵖ (Type v)}   {F : CategoryTheory.Functor (CategoryTheory.Costructu
redArrow CategoryTheory.yoneda A)ᵒᵖ (Type v)} {X : C}   (s : CategoryTheory.yone
da.obj X ⟶ A)   (p : CategoryTheory.OverPresheafAux.OverArrows (CategoryTheory.O
verPresheafAux.yonedaCollectionPresheafToA F) s),   CategoryTheory.OverPresheafA
ux.YonedaCollection.fst p.val = s
参数：Type v；CategoryTheory.CostructuredArrow CategoryTheory.yoneda A；Type v；s : Ca
tegoryTheory.yoneda.obj X ⟶ A；p : CategoryTheory.OverPresheafAux.OverArrows (Cat
egoryTheory.OverPresheafAux.yonedaCollectionPresheafToA F) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.OverPresheafAux.yonedaCollectionPresheafToA_app`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ
 (Type v)}   (F : CategoryTheory.Functor (CategoryTh…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `CategoryTheory.OverPresheafAux.OverArrows.app_val`：app_val {F : Cᵒᵖ ⥤ Ty
pe v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} (p : OverArrows η s) : η.app (o
p X) p.val = yonedaEquiv s
-/
lemma OverArrows.yonedaCollectionPresheafToA_val_fst (s : yoneda.obj X ⟶ A)
    (p : OverArrows (yonedaCollectionPresheafToA F) s) : p.val.fst = s := by
  simpa [YonedaCollection.yonedaEquivFst_eq] using p.app_val

set_option backward.isDefEq.respectTransparency.types false in
/-- Forward direction of the counit. -/
/-
**CategoryTheory.OverPresheafAux.counitForward** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.OverPresheafAux`。
形式化陈述：counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (s : Costructu
redArrow yoneda A) : F.obj (op s) -> OverArrows (yonedaCollectionPresheafToA F) 
s.hom
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v；s : CostructuredArrow yoneda A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forward direction of the counit.
-/
def counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) :
    F.obj (op s) → OverArrows (yonedaCollectionPresheafToA F) s.hom :=
  fun x => ⟨YonedaCollection.mk s.hom x, ⟨by simp [YonedaCollection.yonedaEquivFst_eq]⟩⟩
/-
**CategoryTheory.OverPresheafAux.counitForward_val_fst** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.OverPresheafAux`。
形式化陈述：counitForward_val_fst (s : CostructuredArrow yoneda A) (x : F.obj (op s)) 
: (counitForward F s x).val.fst = s.hom
参数：s : CostructuredArrow yoneda A；x : F.obj (op s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.OverPresheafAux.OverArrows.yonedaCollectionPresheafToA_va
l_fst`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryThe
ory.Functor Cᵒᵖ (Type v)}   {F : CategoryTheory.Functor (CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma counitForward_val_fst (s : CostructuredArrow yoneda A) (x : F.obj (op s)) :
    (counitForward F s x).val.fst = s.hom := by
  simp

@[simp]
/-
**CategoryTheory.OverPresheafAux.counitForward_val_snd** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.OverPresheafAux`。
形式化陈述：counitForward_val_snd (s : CostructuredArrow yoneda A) (x : F.obj (op s)) 
: (counitForward F s x).val.snd = F.map (eqToHom (by simp [← CostructuredArrow.e
q_mk])) x
参数：s : CostructuredArrow yoneda A；x : F.obj (op s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.OverPresheafAux.YonedaCollection.mk_snd`：mk_snd (s : yone
da.obj X ⟶ A) (x : F.obj (op (CostructuredArrow.mk s))) : (mk s x).snd = F.map (
eqToHom <| by rw [YonedaCollection.mk_fst]) …
-/
lemma counitForward_val_snd (s : CostructuredArrow yoneda A) (x : F.obj (op s)) :
    (counitForward F s x).val.snd = F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) x :=
  YonedaCollection.mk_snd _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.counitForward_naturality** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.OverPresheafAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counitForward_naturality₁ {G : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} (η : F ⟶ G)
    (s : (CostructuredArrow yoneda A)ᵒᵖ) (x : F.obj s) : counitForward G s.unop (η.app s x) =
      OverArrows.map₁ (counitForward F s.unop x) (yonedaCollectionPresheafMap₁ η) (by cat_disch) :=
  OverArrows.ext <| YonedaCollection.ext (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.OverPresheafAux.counitForward_naturality** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.OverPresheafAux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counitForward_naturality₂ (s t : (CostructuredArrow yoneda A)ᵒᵖ) (f : t ⟶ s) (x : F.obj t) :
    counitForward F s.unop (F.map f x) =
      OverArrows.map₂ (counitForward F t.unop x) f.unop.left (by simp) := by
  refine OverArrows.ext <| YonedaCollection.ext (by simp) ?_
  have : (CostructuredArrow.mkPrecomp t.unop.hom f.unop.left).op =
      f ≫ eqToHom (by simp [← CostructuredArrow.eq_mk]) := by
    apply Quiver.Hom.unop_inj
    simp
  have : F.map (CostructuredArrow.mkPrecomp
      (YonedaCollection.fst (counitForward F (unop t) x).val) f.unop.left).op
      (F.map (eqToHom (by simp; rfl)) x) = _ :=
    map_mkPrecomp_eqToHom (h := by simp)
  cat_disch

/-- Backward direction of the counit. -/
/-
**CategoryTheory.OverPresheafAux.counitBackward** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.OverPresheafAux`。
形式化陈述：counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (s : Costruct
uredArrow yoneda A) : OverArrows (yonedaCollectionPresheafToA F) s.hom -> F.obj 
(op s)
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v；s : CostructuredArrow yoneda A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Backward direction of the counit.
-/
def counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) :
    OverArrows (yonedaCollectionPresheafToA F) s.hom → F.obj (op s) :=
  fun p => F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) p.val.snd

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.OverPresheafAux.counitForward_counitBackward** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：counitForward_counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
 (s : CostructuredArrow yoneda A) : counitForward F s ∘ counitBackward F s = id
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v；s : CostructuredArrow yoneda A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.OverPresheafAux.OverArrows.ext`：ext {F : Cᵒᵖ ⥤ Type v} {η
 : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A} {u v : OverArrows η s} : u.val = v.val 
-> u = v
· 使用引理 `CategoryTheory.OverPresheafAux.YonedaCollection.ext`：ext {p q : YonedaCo
llection F X} (h : p.fst = q.fst) (h' : F.map (eqToHom <| by rw [h]) q.snd = p.s
nd) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.OverPresheafAux.OverArrows.yonedaCollectionPresheafToA_va
l_fst`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryThe
ory.Functor Cᵒᵖ (Type v)}   {F : CategoryTheory.Functor (CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.OverPresheafAux.counitForward_val_snd`：counitForward_val_
snd (s : CostructuredArrow yoneda A) (x : F.obj (op s)) : (counitForward F s x).
val.snd = F.map (eqToHom (by simp [← Costr…
· 使用定理 `CategoryTheory.eqToHom_map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (F : CategoryTheor…
-/
lemma counitForward_counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) : counitForward F s ∘ counitBackward F s = id :=
  funext fun p => OverArrows.ext <| YonedaCollection.ext (by simp) (by simp [counitBackward])
/-
**CategoryTheory.OverPresheafAux.counitBackward_counitForward** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.OverPresheafAux`。
形式化陈述：counitBackward_counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
 (s : CostructuredArrow yoneda A) : counitBackward F s ∘ counitForward F s = id
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v；s : CostructuredArrow yoneda A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.OverPresheafAux.counitForward_val_snd`：counitForward_val_
snd (s : CostructuredArrow yoneda A) (x : F.obj (op s)) : (counitForward F s x).
val.snd = F.map (eqToHom (by simp [← Costr…
· 使用定理 `CategoryTheory.eqToHom_map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma counitBackward_counitForward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) : counitBackward F s ∘ counitForward F s = id :=
  funext fun x => by simp [counitBackward]

/-- Intermediate stage of assembling the counit. -/
@[simps]
/-
**CategoryTheory.OverPresheafAux.counitAuxAux** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.OverPresheafAux`。
形式化陈述：counitAuxAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) (s : Costructur
edArrow yoneda A) : F.obj (op s) ≅ OverArrows (yonedaCollectionPresheafToA F) s.
hom where hom
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v；s : CostructuredArrow yoneda A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate stage of assembling the counit.
-/
def counitAuxAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) :
    F.obj (op s) ≅ OverArrows (yonedaCollectionPresheafToA F) s.hom where
  hom := ↾(counitForward F s)
  inv := ↾(counitBackward F s)
  hom_inv_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitBackward_counitForward F s))
  inv_hom_id := ConcreteCategory.ext (TypeCat.Fun.ext (counitForward_counitBackward F s))

set_option backward.defeqAttrib.useBackward true in
/-- Intermediate stage of assembling the counit. -/
@[simps! hom]
/-
**CategoryTheory.OverPresheafAux.counitAux** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.OverPresheafAux`。
形式化陈述：counitAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) : F ≅ restrictedYo
nedaObj (yonedaCollectionPresheafToA F)
参数：F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intermediate stage of assembling the counit.
-/
def counitAux (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :
    F ≅ restrictedYonedaObj (yonedaCollectionPresheafToA F) :=
  NatIso.ofComponents (fun s => counitAuxAux F s.unop) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit of the equivalence we're constructing. -/
/-
**CategoryTheory.OverPresheafAux.counit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OverPresheafAux`。
形式化陈述：counit (A : Cᵒᵖ ⥤ Type v) : (costructuredArrowPresheafToOver A ⋙ restricte
dYoneda A) ≅ 𝟭 _
参数：A : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the equivalence we're constructing.
-/
def counit (A : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowPresheafToOver A ⋙ restrictedYoneda A) ≅ 𝟭 _ :=
  Iso.symm <| NatIso.ofComponents counitAux (by cat_disch)

end counit

end OverPresheafAux

open OverPresheafAux

set_option backward.isDefEq.respectTransparency.types false in
/--
If `A : Cᵒᵖ ⥤ Type v` is a presheaf, then we have an equivalence between presheaves lying over
`A` and the category of presheaves on `CostructuredArrow yoneda A`. There is a quasicommutative
triangle involving this equivalence, see
`CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow`.

This is Lemma 1.4.12 in [Kashiwara2006]. -/
/-
**CategoryTheory.overEquivPresheafCostructuredArrow** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory`。
形式化陈述：overEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v) : Over A ≌ ((Costruc
turedArrow yoneda A)ᵒᵖ ⥤ Type v)
参数：A : Cᵒᵖ ⥤ Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A : Cᵒᵖ ⥤ Type v` is a presheaf, then we have an equivalence between preshea
ves lying over
`A` and the category of presheaves on `CostructuredArrow yoneda A`. There is a q
uasicommutative
triangle involving this equivalence, see
`CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow`.

This is Lemma 1.4.12 in [Kashiwara2006].
-/
def overEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v) :
    Over A ≌ ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) :=
  .mk (restrictedYoneda A) (costructuredArrowPresheafToOver A) (unit A) (counit A)

/--
If `A : Cᵒᵖ ⥤ Type v` is a presheaf, then the Yoneda embedding for
`CostructuredArrow yoneda A` factors through `Over A` via a forgetful functor and an
equivalence.

This is Lemma 1.4.12 in [Kashiwara2006]. -/
/-
**CategoryTheory.CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (A : Cate
goryTheory.Functor Cᵒᵖ (Type v)) →       (CategoryTheory.CostructuredArrow.toOve
r CategoryTheory.yoneda A).comp           (CategoryTheory.overEquivPresheafCostr
ucturedArrow A).functor ≅         CategoryTheory.yoneda
参数：A : CategoryTheory.Functor Cᵒᵖ (Type v)；CategoryTheory.CostructuredArrow.toOv
er CategoryTheory.yoneda A；CategoryTheory.overEquivPresheafCostructuredArrow A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A : Cᵒᵖ ⥤ Type v` is a presheaf, then the Yoneda embedding for
`CostructuredArrow yoneda A` factors through `Over A` via a forgetful functor an
d an
equivalence.

This is Lemma 1.4.12 in [Kashiwara2006].
-/
def CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow (A : Cᵒᵖ ⥤ Type v) :
    CostructuredArrow.toOver yoneda A ⋙ (overEquivPresheafCostructuredArrow A).functor ≅ yoneda :=
  toOverYonedaCompRestrictedYoneda A

set_option backward.isDefEq.respectTransparency.types false in
/-- This isomorphism says that hom-sets in the category `Over A` for a presheaf `A` where the domain
is of the form `(CostructuredArrow.toOver yoneda A).obj X` can instead be interpreted as
hom-sets in the category `(CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` where the domain is of the
form `yoneda.obj X` after adjusting the codomain accordingly. This is desirable because in the
latter case the Yoneda lemma can be applied. -/
/-
**CategoryTheory.CostructuredArrow.toOverCompYoneda** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.CostructuredArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (A : Cate
goryTheory.Functor Cᵒᵖ (Type v)) →       (T : CategoryTheory.Over A) →         (
CategoryTheory.CostructuredArrow.toOver CategoryTheory.yoneda A).op.comp (Catego
ryTheory.yoneda.obj T) ≅           CategoryTheory.yoneda.op.comp             (Ca
tegoryTheory.yoneda.obj ((CategoryTheory.overEquivPresheafCostructuredArrow A).f
unctor.obj T))
参数：A : CategoryTheory.Functor Cᵒᵖ (Type v)；T : CategoryTheory.Over A；CategoryThe
ory.CostructuredArrow.toOver CategoryTheory.yoneda A；CategoryTheory.yoneda.obj T
；CategoryTheory.yoneda.obj ((CategoryTheory.overEquivPresheafCostructuredArrow A
).functor.obj T)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This isomorphism says that hom-sets in the category `Over A` for a presheaf `A` 
where the domain
is of the form `(CostructuredArrow.toOver yoneda A).obj X` can instead be interp
reted as
hom-sets in the category `(CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` where the dom
ain is of the
form `yoneda.obj X` after adjusting the codomain accordingly. This is desirable 
because in the
latter case the Yoneda lemma can be applied.
-/
def CostructuredArrow.toOverCompYoneda (A : Cᵒᵖ ⥤ Type v) (T : Over A) :
    (CostructuredArrow.toOver yoneda A).op ⋙ yoneda.obj T ≅
      yoneda.op ⋙ yoneda.obj ((overEquivPresheafCostructuredArrow A).functor.obj T) :=
  NatIso.ofComponents (fun X =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)
    (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_ma
p_toOverCompYoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheo
ry.Functor Cᵒᵖ (Type v)}   {T : CategoryTheory.Over A} {X : CategoryTheory.Costr
ucturedArrow CategoryTheory.yoneda A}   (f : (CategoryTheory.CostructuredArrow.t
oOver CategoryTheory.yoneda A).obj X ⟶ T),   (CategoryTheory.overEquivPresheafCo
structuredArrow A).inverse.map       ((CategoryTheory.ConcreteCategory.hom      
     ((CategoryTheory.CostructuredArrow.toOverCompYoneda A T).hom.app (Opposite.
op X)))         f) =     CategoryTheory.CategoryStruct.comp       ((CategoryTheo
ry.CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInve
rse.inv.app X)       (CategoryTheory.CategoryStruct.comp f ((CategoryTheory.over
EquivPresheafCostructuredArrow A).unit.app T))
参数：Type v；f : (CategoryTheory.CostructuredArrow.toOver CategoryTheory.yoneda A).
obj X ⟶ T；CategoryTheory.overEquivPresheafCostructuredArrow A；(CategoryTheory.Co
ncreteCategory.hom           ((CategoryTheory.CostructuredArrow.toOverCompYoneda
 A T).hom.app (Opposite.op X)))         f；(CategoryTheory.CostructuredArrow.toOv
erCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X；CategoryThe
ory.CategoryStruct.comp f ((CategoryTheory.overEquivPresheafCostructuredArrow A)
.unit.app T)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.inv_fun_map`：inv_fun_map (e : C ≌ D) (X Y : C
) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.a
pp Y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.isoCompInverse_inv_app`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompYoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : (CostructuredArrow.toOver yoneda A).obj X ⟶ T) :
    dsimp% (overEquivPresheafCostructuredArrow A).inverse.map
      ((CostructuredArrow.toOverCompYoneda A T).hom.app (op X) f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X ≫
        f ≫ (overEquivPresheafCostructuredArrow A).unit.app T := by
  simp [CostructuredArrow.toOverCompYoneda]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.CostructuredArrow.overEquivPresheafCostructuredArrow_functor_ma
p_toOverCompYoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheo
ry.Functor Cᵒᵖ (Type v)}   {T : CategoryTheory.Over A} {X : CategoryTheory.Costr
ucturedArrow CategoryTheory.yoneda A}   (f : CategoryTheory.yoneda.obj X ⟶ (Cate
goryTheory.overEquivPresheafCostructuredArrow A).functor.obj T),   (CategoryTheo
ry.overEquivPresheafCostructuredArrow A).functor.map       ((CategoryTheory.Conc
reteCategory.hom           ((CategoryTheory.CostructuredArrow.toOverCompYoneda A
 T).inv.app (Opposite.op X)))         f) =     CategoryTheory.CategoryStruct.com
p       ((CategoryTheory.CostructuredArrow.toOverCompOverEquivPresheafCostructur
edArrow A).hom.app X) f
参数：Type v；f : CategoryTheory.yoneda.obj X ⟶ (CategoryTheory.overEquivPresheafCos
tructuredArrow A).functor.obj T；CategoryTheory.overEquivPresheafCostructuredArro
w A；(CategoryTheory.ConcreteCategory.hom           ((CategoryTheory.Costructured
Arrow.toOverCompYoneda A T).inv.app (Opposite.op X)))         f；(CategoryTheory.
CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompYoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : yoneda.obj X ⟶ (overEquivPresheafCostructuredArrow A).functor.obj T) :
    dsimp% (overEquivPresheafCostructuredArrow A).functor.map
      (((CostructuredArrow.toOverCompYoneda A T).inv.app (op X) f)) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.app X ≫ f := by
  simp [CostructuredArrow.toOverCompYoneda]

/-- This isomorphism says that hom-sets in the category `Over A` for a presheaf `A` where the domain
is of the form `(CostructuredArrow.toOver yoneda A).obj X` can instead be interpreted as
hom-sets in the category `(CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` where the domain is of the
form `yoneda.obj X` after adjusting the codomain accordingly. This is desirable because in the
latter case the Yoneda lemma can be applied. -/
/-
**CategoryTheory.CostructuredArrow.toOverCompCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.CostructuredArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (A : Cate
goryTheory.Functor Cᵒᵖ (Type v)) →       (CategoryTheory.CostructuredArrow.toOve
r CategoryTheory.yoneda A).op.comp CategoryTheory.coyoneda ≅         CategoryThe
ory.yoneda.op.comp           (CategoryTheory.coyoneda.comp             ((Categor
yTheory.Functor.whiskeringLeft (CategoryTheory.Over A)                   (Catego
ryTheory.Functor (CategoryTheory.CostructuredArrow CategoryTheory.yoneda A)ᵒᵖ (T
ype v))                   (Type (max u v))).obj               (CategoryTheory.ov
erEquivPresheafCostructuredArrow A).functor))
参数：A : CategoryTheory.Functor Cᵒᵖ (Type v)；CategoryTheory.CostructuredArrow.toOv
er CategoryTheory.yoneda A；CategoryTheory.coyoneda.comp             ((CategoryTh
eory.Functor.whiskeringLeft (CategoryTheory.Over A)                   (CategoryT
heory.Functor (CategoryTheory.CostructuredArrow CategoryTheory.yoneda A)ᵒᵖ (Type
 v))                   (Type (max u v))).obj               (CategoryTheory.overE
quivPresheafCostructuredArrow A).functor)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This isomorphism says that hom-sets in the category `Over A` for a presheaf `A` 
where the domain
is of the form `(CostructuredArrow.toOver yoneda A).obj X` can instead be interp
reted as
hom-sets in the category `(CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v` where the dom
ain is of the
form `yoneda.obj X` after adjusting the codomain accordingly. This is desirable 
because in the
latter case the Yoneda lemma can be applied.
-/
def CostructuredArrow.toOverCompCoyoneda (A : Cᵒᵖ ⥤ Type v) :
    (CostructuredArrow.toOver yoneda A).op ⋙ coyoneda ≅
    yoneda.op ⋙ coyoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj (overEquivPresheafCostructuredArrow A).functor :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y =>
    (overEquivPresheafCostructuredArrow A).fullyFaithfulFunctor.homEquiv.toIso ≪≫
      (Iso.homCongr
        ((CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).app X.unop)
        (Iso.refl _)).toIso)) (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_ma
p_toOverCompCoyoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow
`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheo
ry.Functor Cᵒᵖ (Type v)}   {T : CategoryTheory.Over A} {X : CategoryTheory.Costr
ucturedArrow CategoryTheory.yoneda A}   (f : (CategoryTheory.CostructuredArrow.t
oOver CategoryTheory.yoneda A).obj X ⟶ T),   (CategoryTheory.overEquivPresheafCo
structuredArrow A).inverse.map       ((CategoryTheory.ConcreteCategory.hom      
     (((CategoryTheory.CostructuredArrow.toOverCompCoyoneda A).hom.app (Opposite
.op X)).app T))         f) =     CategoryTheory.CategoryStruct.comp       ((Cate
goryTheory.CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).iso
CompInverse.inv.app X)       (CategoryTheory.CategoryStruct.comp f ((CategoryThe
ory.overEquivPresheafCostructuredArrow A).unit.app T))
参数：Type v；f : (CategoryTheory.CostructuredArrow.toOver CategoryTheory.yoneda A).
obj X ⟶ T；CategoryTheory.overEquivPresheafCostructuredArrow A；(CategoryTheory.Co
ncreteCategory.hom           (((CategoryTheory.CostructuredArrow.toOverCompCoyon
eda A).hom.app (Opposite.op X)).app T))         f；(CategoryTheory.CostructuredAr
row.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X；Cat
egoryTheory.CategoryStruct.comp f ((CategoryTheory.overEquivPresheafCostructured
Arrow A).unit.app T)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.inv_fun_map`：inv_fun_map (e : C ≌ D) (X Y : C
) (f : X ⟶ Y) : e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.a
pp Y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.isoCompInverse_inv_app`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_inverse_map_toOverCompCoyoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : (CostructuredArrow.toOver yoneda A).obj X ⟶ T) :
    dsimp% (overEquivPresheafCostructuredArrow A).inverse.map
      (((CostructuredArrow.toOverCompCoyoneda A).hom.app (op X)).app T f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).isoCompInverse.inv.app X ≫
        f ≫ (overEquivPresheafCostructuredArrow A).unit.app T := by
  simp [CostructuredArrow.toOverCompCoyoneda]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.CostructuredArrow.overEquivPresheafCostructuredArrow_functor_ma
p_toOverCompCoyoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow
`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheo
ry.Functor Cᵒᵖ (Type v)}   {T : CategoryTheory.Over A} {X : CategoryTheory.Costr
ucturedArrow CategoryTheory.yoneda A}   (f : CategoryTheory.yoneda.obj X ⟶ (Cate
goryTheory.overEquivPresheafCostructuredArrow A).functor.obj T),   (CategoryTheo
ry.overEquivPresheafCostructuredArrow A).functor.map       ((CategoryTheory.Conc
reteCategory.hom           (((CategoryTheory.CostructuredArrow.toOverCompCoyoned
a A).inv.app (Opposite.op X)).app T))         f) =     CategoryTheory.CategorySt
ruct.comp       ((CategoryTheory.CostructuredArrow.toOverCompOverEquivPresheafCo
structuredArrow A).hom.app X) f
参数：Type v；f : CategoryTheory.yoneda.obj X ⟶ (CategoryTheory.overEquivPresheafCos
tructuredArrow A).functor.obj T；CategoryTheory.overEquivPresheafCostructuredArro
w A；(CategoryTheory.ConcreteCategory.hom           (((CategoryTheory.Costructure
dArrow.toOverCompCoyoneda A).inv.app (Opposite.op X)).app T))         f；(Categor
yTheory.CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.ap
p X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem CostructuredArrow.overEquivPresheafCostructuredArrow_functor_map_toOverCompCoyoneda
    {A : Cᵒᵖ ⥤ Type v} {T : Over A} {X : CostructuredArrow yoneda A}
    (f : yoneda.obj X ⟶ (overEquivPresheafCostructuredArrow A).functor.obj T) :
    dsimp% (overEquivPresheafCostructuredArrow A).functor.map
      (((CostructuredArrow.toOverCompCoyoneda A).inv.app (op X)).app T f) =
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow A).hom.app X ≫ f := by
  simp [CostructuredArrow.toOverCompCoyoneda]

end CategoryTheory

