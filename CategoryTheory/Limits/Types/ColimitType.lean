/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Types.Basic

/-!
# The colimit type of a functor to types

Given a category `J` (with `J : Type u` and `[Category.{v} J]`) and
a functor `F : J ⥤ Type w₀`, we introduce a type `F.ColimitType : Type (max u w₀)`,
which satisfies a certain universal property of the colimit: it is defined
as a suitable quotient of `Σ j, F.obj j`. This universal property is not
expressed in a categorical way (as in general `Type (max u w₀)`
is not the same as `Type u`).

We also introduce a notion of cocone of `F : J ⥤ Type w₀`, this is `F.CoconeTypes`,
or more precisely `Functor.CoconeTypes.{w₁} F`, which consists of a candidate
colimit type for `F` which is in `Type w₁` (in case `w₁ = w₀`, we shall show
this is the same as the data of `c : Cocone F` in the categorical sense).
Given `c : F.CoconeTypes`, we also introduce a property `c.IsColimit` which says
that the canonical map `F.ColimitType → c.pt` is a bijection, and we shall show (TODO)
that when `w₁ = w₀`, it is equivalent to saying that the corresponding cocone
in a categorical sense is a colimit.

## TODO
* refactor `DirectedSystem` and the construction of colimits in `Type`
  by using `Functor.ColimitType`.
* add a similar API for limits in `Type`?

-/

@[expose] public section

universe w₃ w₂ w₁ w₀ w₀' v u

assert_not_exists CategoryTheory.Limits.Cocone

namespace CategoryTheory

variable {J : Type u} [Category.{v} J]

namespace Functor

variable (F : J ⥤ Type w₀)

/-- Given a functor `F : J ⥤ Type w₀`, this is a "cocone" of `F` where
we allow the point `pt` to be in a different universe than `w`. -/
/-
**CategoryTheory.Functor.CoconeTypes** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：CoconeTypes where /-- the point of the cocone -/ pt : Type w₁ /-- a family
 of maps to `pt` -/ ι (j : J) : F.obj j -> pt ι_naturality {j j' : J} (f : j ⟶ j
') : (ι j').comp (F.map f) = ι j
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : J ⥤ Type w₀`, this is a "cocone" of `F` where
we allow the point `pt` to be in a different universe than `w`.
-/
structure CoconeTypes where
  /-- the point of the cocone -/
  pt : Type w₁
  /-- a family of maps to `pt` -/
  ι (j : J) : F.obj j → pt
  ι_naturality {j j' : J} (f : j ⟶ j') :
      (ι j').comp (F.map f) = ι j := by aesop

namespace CoconeTypes

attribute [simp] ι_naturality

variable {F}

@[simp]
/-
**CategoryTheory.Functor.CoconeTypes.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Functor.CoconeTypes`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_naturality_apply (c : CoconeTypes.{w₁} F) {j j' : J} (f : j ⟶ j') (x : F.obj j) :
    c.ι j' (F.map f x) = c.ι j x :=
  congr_fun (c.ι_naturality f) x

/-- Given `c : F.CoconeTypes` and a map `φ : c.pt → T`, this is
the cocone for `F` obtained by postcomposition with `φ`. -/
@[simps -fullyApplied]
/-
**CategoryTheory.Functor.CoconeTypes.postcomp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.CoconeTypes`。
形式化陈述：postcomp (c : CoconeTypes.{w₁} F) {T : Type w₂} (φ : c.pt -> T) : F.Cocone
Types where pt
参数：c : CoconeTypes.{w₁} F；φ : c.pt -> T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `c : F.CoconeTypes` and a map `φ : c.pt → T`, this is
the cocone for `F` obtained by postcomposition with `φ`.
-/
def postcomp (c : CoconeTypes.{w₁} F) {T : Type w₂} (φ : c.pt → T) :
    F.CoconeTypes where
  pt := T
  ι j := φ.comp (c.ι j)

/-- The cocone for `G : J ⥤ Type w₀'` that is deduced from a cocone for `F : J ⥤ Type w₀`
and a natural map `G.obj j → F.obj j` for all `j : J`. -/
@[simps -fullyApplied]
/-
**CategoryTheory.Functor.CoconeTypes.precompose** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.CoconeTypes`。
形式化陈述：precompose (c : CoconeTypes.{w₁} F) {G : J ⥤ Type w₀'} (app : forall j, G.
obj j -> F.obj j) (naturality : forall {j j'} (f : j ⟶ j'), app j' ∘ G.map f = F
.map f ∘ app j) : CoconeTypes.{w₁} G where pt
参数：c : CoconeTypes.{w₁} F；app : forall j, G.obj j -> F.obj j；naturality : forall
 {j j'} (f : j ⟶ j'), app j' ∘ G.map f = F.map f ∘ app j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone for `G : J ⥤ Type w₀'` that is deduced from a cocone for `F : J ⥤ Typ
e w₀`
and a natural map `G.obj j → F.obj j` for all `j : J`.
-/
def precompose (c : CoconeTypes.{w₁} F) {G : J ⥤ Type w₀'} (app : ∀ j, G.obj j → F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), app j' ∘ G.map f = F.map f ∘ app j) :
    CoconeTypes.{w₁} G where
  pt := c.pt
  ι j := c.ι j ∘ app j
  ι_naturality f := by
    rw [Function.comp_assoc, naturality, ← Function.comp_assoc, ι_naturality]

set_option backward.defeqAttrib.useBackward true in
/-- Given `F : J ⥤ w₀`, `c : F.CoconeTypes` and `G : J' ⥤ J`, this is
the induced cocone in `(G ⋙ F).CoconeTypes`. -/
@[simps]
/-
**CategoryTheory.Functor.CoconeTypes.precomp** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor.CoconeTypes`。
形式化陈述：precomp (c : CoconeTypes.{w₁} F) {J' : Type*} [Category* J'] (G : J' ⥤ J) 
: CoconeTypes.{w₁} (G ⋙ F) where pt
参数：c : CoconeTypes.{w₁} F；G : J' ⥤ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : J ⥤ w₀`, `c : F.CoconeTypes` and `G : J' ⥤ J`, this is
the induced cocone in `(G ⋙ F).CoconeTypes`.
-/
def precomp (c : CoconeTypes.{w₁} F) {J' : Type*} [Category* J'] (G : J' ⥤ J) :
    CoconeTypes.{w₁} (G ⋙ F) where
  pt := c.pt
  ι _ := c.ι _

end CoconeTypes

/-- Given `F : J ⥤ Type w₀`, this is the relation `Σ j, F.obj j` which
generates an equivalence relation such that the quotient identifies
to the colimit type of `F`. -/
/-
**CategoryTheory.Functor.ColimitTypeRel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：ColimitTypeRel : (Σ j, F.obj j) -> (Σ j, F.obj j) -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : J ⥤ Type w₀`, this is the relation `Σ j, F.obj j` which
generates an equivalence relation such that the quotient identifies
to the colimit type of `F`.
-/
def ColimitTypeRel : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop :=
  fun p p' ↦ ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2

/-- The colimit type of a functor `F : J ⥤ Type w₀`. (It may not
be in `Type w₀`.) -/
/-
**CategoryTheory.Functor.ColimitType** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：ColimitType : Type (max u w₀)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit type of a functor `F : J ⥤ Type w₀`. (It may not
be in `Type w₀`.)
-/
def ColimitType : Type (max u w₀) := Quot F.ColimitTypeRel

/-- The canonical maps `F.obj j → F.ColimitType`. -/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical maps `F.obj j → F.ColimitType`.
-/
def ιColimitType (j : J) (x : F.obj j) : F.ColimitType :=
  Quot.mk _ ⟨j, x⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιColimitType_eq_iff {j j' : J} (x : F.obj j) (y : F.obj j') :
    F.ιColimitType j x = F.ιColimitType j' y ↔
      Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨j', y⟩ :=
  Quot.eq
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιColimitType_eq_of_map_eq_map {j j' : J} (x : F.obj j) (y : F.obj j')
    {k : J} (f : j ⟶ k) (f' : j' ⟶ k) (H : F.map f x = F.map f' y) :
    F.ιColimitType j x = F.ιColimitType j' y :=
  (ιColimitType_eq_iff ..).mpr (.trans _ _ _ (.rel _ ⟨k, F.map f x⟩ ⟨f, rfl⟩)
    (.symm _ _ (.rel _ _ ⟨f', H⟩)))
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιColimitType_jointly_surjective (t : F.ColimitType) :
    ∃ j x, F.ιColimitType j x = t := by
  obtain ⟨_, _⟩ := t
  exact ⟨_, _, rfl⟩

@[simp]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιColimitType_map {j j' : J} (f : j ⟶ j') (x : F.obj j) :
    F.ιColimitType j' (F.map f x) = F.ιColimitType j x :=
  (Quot.sound ⟨f, rfl⟩).symm

/-- The cocone corresponding to `F.ColimitType`. -/
@[simps -fullyApplied]
/-
**CategoryTheory.Functor.coconeTypes** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：coconeTypes : F.CoconeTypes where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone corresponding to `F.ColimitType`.
-/
def coconeTypes : F.CoconeTypes where
  pt := F.ColimitType
  ι j := F.ιColimitType j

/-- A heterogeneous universe version of the universal property of the colimit is
satisfied by `F.ColimitType` together with the maps `F.ιColimitType j`. -/
/-
**CategoryTheory.Functor.descColimitType** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：descColimitType (c : F.CoconeTypes) : F.ColimitType -> c.pt
参数：c : F.CoconeTypes。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A heterogeneous universe version of the universal property of the colimit is
satisfied by `F.ColimitType` together with the maps `F.ιColimitType j`.
-/
def descColimitType (c : F.CoconeTypes) : F.ColimitType → c.pt :=
  Quot.lift (fun ⟨j, x⟩ ↦ c.ι j x) (by rintro _ _ ⟨_, _⟩; aesop)

@[simp]
/-
**CategoryTheory.Functor.descColimitType_comp_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descColimitType_comp_ι (c : F.CoconeTypes) (j : J) :
    (F.descColimitType c).comp (F.ιColimitType j) = c.ι j := rfl

@[simp]
/-
**CategoryTheory.Functor.descColimitType_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descColimitType_ιColimitType_apply (c : F.CoconeTypes) (j : J) (x : F.obj j) :
    F.descColimitType c (F.ιColimitType j x) = c.ι j x := rfl

namespace CoconeTypes

variable {F} (c : CoconeTypes.{w₁} F)

/-
**CategoryTheory.Functor.CoconeTypes.descColimitType_surjective_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Functor.CoconeTypes`。
形式化陈述：descColimitType_surjective_iff : Function.Surjective (F.descColimitType c)
 ↔ forall (z : c.pt), exists (i : J) (x : F.obj i), c.ι i x = z
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descColimitType_surjective_iff :
    Function.Surjective (F.descColimitType c) ↔
      ∀ (z : c.pt), ∃ (i : J) (x : F.obj i), c.ι i x = z := by
  constructor
  · intro h z
    obtain ⟨⟨i, x⟩, rfl⟩ := h z
    exact ⟨i, x, rfl⟩
  · intro h z
    obtain ⟨i, x, rfl⟩ := h z
    exact ⟨F.ιColimitType i x, rfl⟩

/-- Given `F : J ⥤ Type w₀` and `c : F.CoconeTypes`, this is the property
that `c` is a colimit. It is defined by saying the canonical map
`F.descColimitType c : F.ColimitType → c.pt` is a bijection. -/
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Functor.CoconeTypes`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] → {F : Category
Theory.Functor J (Type w₀)} → F.CoconeTypes → Prop
参数：Type w₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : J ⥤ Type w₀` and `c : F.CoconeTypes`, this is the property
that `c` is a colimit. It is defined by saying the canonical map
`F.descColimitType c : F.ColimitType → c.pt` is a bijection.
-/
structure IsColimit : Prop where
  bijective : Function.Bijective (F.descColimitType c)

namespace IsColimit

variable {c} (hc : c.IsColimit)

include hc

/-- Given `F : J ⥤ Type w₀`, and `c : F.CoconeTypes` a cocone that is a colimit,
this is the equivalence `F.ColimitType ≃ c.pt`. -/
@[simps! apply]
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.equiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：equiv : F.ColimitType ≃ c.pt
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimit.bijective`：∀ {J : Type u} [
inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀)
} {c : F.CoconeTypes},   c.IsColimit → Funct…

--- 原说明 ---
Given `F : J ⥤ Type w₀`, and `c : F.CoconeTypes` a cocone that is a colimit,
this is the equivalence `F.ColimitType ≃ c.pt`.
-/
noncomputable def equiv : F.ColimitType ≃ c.pt :=
  Equiv.ofBijective _ hc.bijective

@[simp]
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.equiv_symm_** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor.CoconeTypes.IsColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equiv_symm_ι_apply (j : J) (x : F.obj j) :
    hc.equiv.symm (c.ι j x) = F.ιColimitType j x :=
  hc.equiv.injective (by simp)
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.CoconeTypes.IsColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_jointly_surjective (y : c.pt) :
    ∃ j x, c.ι j x = y := by
  obtain ⟨z, rfl⟩ := hc.equiv.surjective y
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective z
  exact ⟨j, x, rfl⟩
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.funext** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：funext {T : Type w₂} {f g : c.pt -> T} (h : forall j, f.comp (c.ι j) = g.c
omp (c.ι j)) : f = g
参数：h : forall j, f.comp (c.ι j) = g.comp (c.ι j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.ι_jointly_surjective`：ι_joi
ntly_surjective (y : c.pt) : exists j x, c.ι j x = y
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma funext {T : Type w₂} {f g : c.pt → T}
    (h : ∀ j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g := by
  funext y
  obtain ⟨j, x, rfl⟩ := hc.ι_jointly_surjective y
  exact congr_fun (h j) x
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.exists_desc** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：exists_desc (c' : CoconeTypes.{w₂} F) : exists (f : c.pt -> c'.pt), forall
 (j : J), f.comp (c.ι j) = c'.ι j
参数：c' : CoconeTypes.{w₂} F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.equiv_symm_ι_apply`：equiv_s
ymm_ι_apply (j : J) (x : F.obj j) : hc.equiv.symm (c.ι j x) = F.ιColimitType j x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_desc (c' : CoconeTypes.{w₂} F) :
    ∃ (f : c.pt → c'.pt), ∀ (j : J), f.comp (c.ι j) = c'.ι j :=
  ⟨(F.descColimitType c').comp hc.equiv.symm, by aesop⟩

/-- If `F : J ⥤ Type w₀` and `c : F.CoconeTypes` is colimit, then
`c` satisfies a heterogeneous universe version of the universal
property of colimits. -/
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.desc** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：desc (c' : CoconeTypes.{w₂} F) : c.pt -> c'.pt
参数：c' : CoconeTypes.{w₂} F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.exists_desc`：exists_desc (c
' : CoconeTypes.{w₂} F) : exists (f : c.pt -> c'.pt), forall (j : J), f.comp (c.
ι j) = c'.ι j

--- 原说明 ---
If `F : J ⥤ Type w₀` and `c : F.CoconeTypes` is colimit, then
`c` satisfies a heterogeneous universe version of the universal
property of colimits.
-/
noncomputable def desc (c' : CoconeTypes.{w₂} F) : c.pt → c'.pt :=
  (hc.exists_desc c').choose

@[simp]
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.fac** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：fac (c' : CoconeTypes.{w₂} F) (j : J) : (hc.desc c').comp (c.ι j) = c'.ι j
参数：c' : CoconeTypes.{w₂} F；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.exists_desc`：exists_desc (c
' : CoconeTypes.{w₂} F) : exists (f : c.pt -> c'.pt), forall (j : J), f.comp (c.
ι j) = c'.ι j
-/
lemma fac (c' : CoconeTypes.{w₂} F) (j : J) :
    (hc.desc c').comp (c.ι j) = c'.ι j :=
  (hc.exists_desc c').choose_spec j

@[simp]
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.fac_apply** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：fac_apply (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) : hc.desc c' (c.
ι j x) = c'.ι j x
参数：c' : CoconeTypes.{w₂} F；j : J；x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.fac`：fac (c' : CoconeTypes.
{w₂} F) (j : J) : (hc.desc c').comp (c.ι j) = c'.ι j
-/
lemma fac_apply (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) :
    hc.desc c' (c.ι j x) = c'.ι j x :=
  congr_fun (hc.fac c' j) x
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.of_equiv** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：of_equiv {c' : CoconeTypes.{w₂} F} (e : c.pt ≃ c'.pt) (he : forall j x, c'
.ι j x = e (c.ι j x)) : c'.IsColimit where bijective
参数：e : c.pt ≃ c'.pt；he : forall j x, c'.ι j x = e (c.ι j x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimit.bijective`：∀ {J : Type u} [
inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀)
} {c : F.CoconeTypes},   c.IsColimit → Funct…
-/
lemma of_equiv {c' : CoconeTypes.{w₂} F} (e : c.pt ≃ c'.pt)
    (he : ∀ j x, c'.ι j x = e (c.ι j x)) : c'.IsColimit where
  bijective := by
    convert! Function.Bijective.comp e.bijective hc.bijective
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    simp_all
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.iff_bijective** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：iff_bijective {c' : CoconeTypes.{w₂} F} (f : c.pt -> c'.pt) (hf : forall j
 x, c'.ι j x = f (c.ι j x)) : c'.IsColimit ↔ Function.Bijective f
参数：f : c.pt -> c'.pt；hf : forall j x, c'.ι j x = f (c.ι j x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimit.bijective`：∀ {J : Type u} [
inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀)
} {c : F.CoconeTypes},   c.IsColimit → Funct…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.of_equiv`：of_equiv {c' : Co
coneTypes.{w₂} F} (e : c.pt ≃ c'.pt) (he : forall j x, c'.ι j x = e (c.ι j x)) :
 c'.IsColimit where bijective
-/
lemma iff_bijective {c' : CoconeTypes.{w₂} F}
    (f : c.pt → c'.pt) (hf : ∀ j x, c'.ι j x = f (c.ι j x)) :
    c'.IsColimit ↔ Function.Bijective f := by
  refine ⟨fun hc' ↦ ?_, fun h ↦ hc.of_equiv (Equiv.ofBijective _ h) hf⟩
  have h₁ := hc.bijective
  rw [← Function.Bijective.of_comp_iff _ hc.bijective]
  convert! hc'.bijective
  ext x
  obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective x
  simp [hf]

end IsColimit

/-- Structure which expresses that `c : F.CoconeTypes`
satisfies the universal property of the colimit of types:
compatible families of maps `F.obj j → T` (where `T`
is any type in a specified universe) descend in a unique
way as maps `c.pt → T`. -/
/-
**CategoryTheory.Functor.CoconeTypes.IsColimitCore** 是 Mathlib 中的一个结构，位于命名空间 `Ca
tegoryTheory.Functor.CoconeTypes`。
形式化陈述：IsColimitCore where /-- any cocone descends (in a unique way) as a map -/ 
desc (c' : CoconeTypes.{w₂} F) : c.pt -> c'.pt fac (c' : CoconeTypes.{w₂} F) (j 
: J) : (desc c').comp (c.ι j) = c'.ι j
参数：in a unique way；c' : CoconeTypes.{w₂} F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure which expresses that `c : F.CoconeTypes`
satisfies the universal property of the colimit of types:
compatible families of maps `F.obj j → T` (where `T`
is any type in a specified universe) descend in a unique
way as maps `c.pt → T`.
-/
structure IsColimitCore where
  /-- any cocone descends (in a unique way) as a map -/
  desc (c' : CoconeTypes.{w₂} F) : c.pt → c'.pt
  fac (c' : CoconeTypes.{w₂} F) (j : J) :
    (desc c').comp (c.ι j) = c'.ι j := by aesop
  funext {T : Type w₂} {f g : c.pt → T}
    (h : ∀ j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g

namespace IsColimitCore

attribute [simp] fac

variable {c}

@[simp]
/-
**CategoryTheory.Functor.CoconeTypes.IsColimitCore.fac_apply** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor.CoconeTypes.IsColimitCore`。
形式化陈述：fac_apply (hc : IsColimitCore.{w₂} c) (c' : CoconeTypes.{w₂} F) (j : J) (x
 : F.obj j) : hc.desc c' (c.ι j x) = c'.ι j x
参数：hc : IsColimitCore.{w₂} c；c' : CoconeTypes.{w₂} F；j : J；x : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimitCore.fac`：∀ {J : Type u} [in
st : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀)} 
{c : F.CoconeTypes}   (self : c.IsColimitC…
-/
lemma fac_apply (hc : IsColimitCore.{w₂} c)
    (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) :
    hc.desc c' (c.ι j x) = c'.ι j x :=
  congr_fun (hc.fac c' j) x

set_option backward.isDefEq.respectTransparency false in
/-- Any structure `IsColimitCore.{max w₂ w₃} c` can be
lowered to `IsColimitCore.{w₂} c` -/
/-
**CategoryTheory.Functor.CoconeTypes.IsColimitCore.down** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.CoconeTypes.IsColimitCore`。
形式化陈述：down (hc : IsColimitCore.{max w₂ w₃} c) : IsColimitCore.{w₂} c where desc 
c'
参数：hc : IsColimitCore.{max w₂ w₃} c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Any structure `IsColimitCore.{max w₂ w₃} c` can be
lowered to `IsColimitCore.{w₂} c`
-/
def down (hc : IsColimitCore.{max w₂ w₃} c) :
    IsColimitCore.{w₂} c where
  desc c' := Equiv.ulift.toFun.comp
    (hc.desc (c'.postcomp Equiv.ulift.{w₃}.symm))
  fac c' j := by
    rw [Function.comp_assoc, hc.fac]
    rfl
  funext {T f g} h := by
    suffices Equiv.ulift.{w₃}.invFun.comp f =
        Equiv.ulift.invFun.comp g by
      ext x
      simpa using congr_fun this x
    exact hc.funext (fun j ↦ by simp [Function.comp_assoc, h])

set_option backward.isDefEq.respectTransparency false in
/-- A colimit cocone for `F : J ⥤ Type w₀` induces a colimit cocone
for `G : J ⥤ Type w₉'` when we have a natural equivalence `G.obj j ≃ F.obj j`
for all `j : J`. -/
/-
**CategoryTheory.Functor.CoconeTypes.IsColimitCore.precompose** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor.CoconeTypes.IsColimitCore`。
形式化陈述：precompose (hc : IsColimitCore.{w₂} c) {G : J ⥤ Type w₀'} (e : forall j, G
.obj j ≃ F.obj j) (naturality : forall {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.m
ap f ∘ e j) : IsColimitCore.{w₂} (c.precompose _ naturality) where desc c'
参数：hc : IsColimitCore.{w₂} c；e : forall j, G.obj j ≃ F.obj j；naturality : forall
 {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A colimit cocone for `F : J ⥤ Type w₀` induces a colimit cocone
for `G : J ⥤ Type w₉'` when we have a natural equivalence `G.obj j ≃ F.obj j`
for all `j : J`.
-/
def precompose (hc : IsColimitCore.{w₂} c)
    {G : J ⥤ Type w₀'} (e : ∀ j, G.obj j ≃ F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    IsColimitCore.{w₂} (c.precompose _ naturality) where
  desc c' := hc.desc (c'.precompose _ (FunctorToTypes.naturality_symm e naturality))
  fac c' j := by
    rw [precompose_ι, ← Function.comp_assoc, hc.fac, precompose_ι, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id]
  funext {T f g} h := hc.funext (fun j ↦ by
    ext x
    obtain ⟨y, rfl⟩ := (e j).surjective x
    exact congr_fun (h j) y)

end IsColimitCore

variable {c} in
/-- When `c : F.CoconeTypes` satisfies the property
`c.IsColimit`, this is a term in `IsColimitCore.{w₂} c`
for any universe `w₂`. -/
@[simps]
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.isColimitCore** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     {F : Cate
goryTheory.Functor J (Type w₀)} → {c : F.CoconeTypes} → c.IsColimit → c.IsColimi
tCore
参数：Type w₀。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.funext`：funext {T : Type w₂
} {f g : c.pt -> T} (h : forall j, f.comp (c.ι j) = g.comp (c.ι j)) : f = g

--- 原说明 ---
When `c : F.CoconeTypes` satisfies the property
`c.IsColimit`, this is a term in `IsColimitCore.{w₂} c`
for any universe `w₂`.
-/
noncomputable def IsColimit.isColimitCore (hc : c.IsColimit) :
    IsColimitCore.{w₂} c where
  desc := hc.desc
  funext := hc.funext

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.CoconeTypes.IsColimitCore.isColimit** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.CoconeTypes.IsColimitCore`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheo
ry.Functor J (Type w₀)} (c : F.CoconeTypes)   (hc : c.IsColimitCore), c.IsColimi
t
参数：Type w₀；c : F.CoconeTypes；hc : c.IsColimitCore。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimitCore.fac_apply`：fac_apply (h
c : IsColimitCore.{w₂} c) (c' : CoconeTypes.{w₂} F) (j : J) (x : F.obj j) : hc.d
esc c' (c.ι j x) = c'.ι j x
· 使用定理 `CategoryTheory.Functor.coconeTypes_ι`：∀ {J : Type u} [inst : CategoryThe
ory.Category.{v, u} J] (F : CategoryTheory.Functor J (Type w₀)),   F.coconeTypes
.ι = fun j => F.ιColimitTy…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimitCore.funext`：∀ {J : Type u} 
[inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀
)} {c : F.CoconeTypes}   (self : c.IsColimitC…
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimitCore.fac`：∀ {J : Type u} [in
st : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀)} 
{c : F.CoconeTypes}   (self : c.IsColimitC…
· 使用引理 `CategoryTheory.Functor.descColimitType_comp_ι`：descColimitType_comp_ι (c
 : F.CoconeTypes) (j : J) : (F.descColimitType c).comp (F.ιColimitType j) = c.ι 
j
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma IsColimitCore.isColimit (hc : IsColimitCore.{max u w₀ w₁} c) :
    c.IsColimit where
  bijective := by
    let e : F.ColimitType ≃ c.pt :=
      { toFun := F.descColimitType c
        invFun := (down.{max u w₁} hc).desc F.coconeTypes
        left_inv y := by
          obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
          simp
        right_inv := by
          have : (F.descColimitType c).comp
              ((down.{max u w₁} hc).desc F.coconeTypes) = id :=
            (down.{max u w₀} hc).funext (fun j ↦ by
              rw [Function.id_comp, Function.comp_assoc, fac,
                coconeTypes_ι, descColimitType_comp_ι])
          exact congr_fun this }
    exact e.bijective

variable {c} in
/-
**CategoryTheory.Functor.CoconeTypes.IsColimit.precompose** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Functor.CoconeTypes.IsColimit`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheo
ry.Functor J (Type w₀)} {c : F.CoconeTypes},   c.IsColimit →     ∀ {G : Category
Theory.Functor J (Type w₀')} (e : (j : J) → G.obj j ≃ F.obj j)       (naturality
 :         ∀ {j j' : J} (f : j ⟶ j'),           ⇑(e j') ∘ ⇑(CategoryTheory.Concr
eteCategory.hom (G.map f)) =             ⇑(CategoryTheory.ConcreteCategory.hom (
F.map f)) ∘ ⇑(e j)),       (c.precompose (fun {j'} => ⇑(e j')) ⋯).IsColimit
参数：Type w₀；Type w₀'；e : (j : J) → G.obj j ≃ F.obj j；naturality :         ∀ {j j'
 : J} (f : j ⟶ j'),           ⇑(e j') ∘ ⇑(CategoryTheory.ConcreteCategory.hom (G
.map f)) =             ⇑(CategoryTheory.ConcreteCategory.hom (F.map f)) ∘ ⇑(e j)
；c.precompose (fun {j'} => ⇑(e j')) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimitCore.isColimit`：∀ {J : Type 
u} [inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type
 w₀)} (c : F.CoconeTypes)   (hc : c.IsColimitCor…
-/
lemma IsColimit.precompose (hc : c.IsColimit) {G : J ⥤ Type w₀'} (e : ∀ j, G.obj j ≃ F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    (c.precompose _ naturality).IsColimit :=
  (hc.isColimitCore.precompose e naturality).isColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.CoconeTypes.isColimit_precompose_iff** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Functor.CoconeTypes`。
形式化陈述：isColimit_precompose_iff {G : J ⥤ Type w₀'} (e : forall j, G.obj j ≃ F.obj
 j) (naturality : forall {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) : 
(c.precompose _ naturality).IsColimit ↔ c.IsColimit
参数：e : forall j, G.obj j ≃ F.obj j；naturality : forall {j j'} (f : j ⟶ j'), e j'
 ∘ G.map f = F.map f ∘ e j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.CoconeTypes.IsColimit.of_equiv`：of_equiv {c' : Co
coneTypes.{w₂} F} (e : c.pt ≃ c'.pt) (he : forall j x, c'.ι j x = e (c.ι j x)) :
 c'.IsColimit where bijective
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.FunctorToTypes.naturality_symm`：naturality_symm {F G : C 
⥤ Type*} (e : forall j, F.obj j ≃ G.obj j) (naturality : forall {j j'} (f : j ⟶ 
j'), e j' ∘ F.map f = G.map f ∘ e j…
· 使用定理 `CategoryTheory.Functor.CoconeTypes.IsColimit.precompose`：∀ {J : Type u} 
[inst : CategoryTheory.Category.{v, u} J] {F : CategoryTheory.Functor J (Type w₀
)} {c : F.CoconeTypes},   c.IsColimit →     ∀…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isColimit_precompose_iff {G : J ⥤ Type w₀'} (e : ∀ j, G.obj j ≃ F.obj j)
    (naturality : ∀ {j j'} (f : j ⟶ j'), e j' ∘ G.map f = F.map f ∘ e j) :
    (c.precompose _ naturality).IsColimit ↔ c.IsColimit :=
  ⟨fun hc ↦ (hc.precompose (fun j ↦ (e j).symm)
      (FunctorToTypes.naturality_symm e naturality)).of_equiv (Equiv.refl _) (by simp),
    fun hc ↦ hc.precompose e naturality⟩

end CoconeTypes

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.isColimit_coconeTypes** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：isColimit_coconeTypes : F.coconeTypes.IsColimit where bijective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma isColimit_coconeTypes : F.coconeTypes.IsColimit where
  bijective := by
    convert! Function.bijective_id
    ext y
    obtain ⟨j, x, rfl⟩ := F.ιColimitType_jointly_surjective y
    rfl

end Functor

end CategoryTheory

