/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.MorphismProperty.HasCardinalLT
public import Mathlib.CategoryTheory.ObjectProperty.HasCardinalLT
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.CategoryTheory.Products.Unitor

/-!
# `κ`-filtered categories and `κ`-directed poset

In this file, we formalize the proof by Deligne (SGA 4 I 8.1.6) that for
any (small) filtered category `J`, there exists a final functor `F : α ⥤ J`
where `α` is a directed partially ordered set (`IsFiltered.exists_directed`).
The construction applies more generally to `κ`-filtered categories and
`κ`-directed posets (`IsCardinalFiltered.exists_cardinal_directed`).

Note: the argument by Deligne is reproduced (without reference) in the book
by Adámek and Rosický (theorem 1.5), but with a mistake:
the construction by Deligne involves considering diagrams
(see `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.DiagramWithUniqueTerminal`)
which are not necessarily *subcategories* (the class of morphisms `W` does not
have to be multiplicative.)

## References
* [Alexander Grothendieck and Jean-Louis Verdier, *Exposé I : Préfaisceaux*,
  SGA 4 I 8.1.6][sga-4-tome-1]
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits

namespace IsCardinalFiltered

namespace exists_cardinal_directed

variable (J : Type w) [SmallCategory J] (κ : Cardinal.{w})

/-!
Let `J` be a `κ`-filtered category. In order to construct a cofinal functor `α ⥤ J`
with a `κ`-directed poset `α`, we first consider the case where there is no
object `m : J` such that for any object `j : J`, there exists a map `j ⟶ m`.
Under this assumption (`hJ`), the partially ordered type `DiagramWithUniqueTerminal J κ`
of `κ`-bounded diagrams with a unique terminal object in `J` shall be a possible
choice for `α`.
-/

/-- If `κ` is a cardinal, this structure contains the data of a `κ`-bounded diagram
in a category `J`. -/
@[ext]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram** 是 Mathlib
 中的一个归纳类型，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
形式化陈述：(J : Type w) → [CategoryTheory.SmallCategory J] → Cardinal.{w} → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `κ` is a cardinal, this structure contains the data of a `κ`-bounded diagram
in a category `J`.
-/
structure Diagram where
  /-- the morphisms which belong to the diagram -/
  W : MorphismProperty J
  /-- the objects in the diagram -/
  P : ObjectProperty J
  src {i j : J} {f : i ⟶ j} : W f → P i
  tgt {i j : J} {f : i ⟶ j} : W f → P j
  hW : W.HasCardinalLT κ
  hP : P.HasCardinalLT κ

namespace Diagram

variable {J κ}

/-- Given a `κ`-bounded diagram `D` in a category `J`, an object `e : J`
is terminal if `𝟙 e` belongs to `D` and for any object `j` of `D`,
there is a unique morphism `j ⟶ e` in `D`, such that these unique morphisms
are compatible with precomposition with morphisms in `D`. -/
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTerminal*
* 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_d
irected.Diagram`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.SmallCategory J] →     {κ : Cardin
al.{w}} → CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram J κ
 → J → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `κ`-bounded diagram `D` in a category `J`, an object `e : J`
is terminal if `𝟙 e` belongs to `D` and for any object `j` of `D`,
there is a unique morphism `j ⟶ e` in `D`, such that these unique morphisms
are compatible with precomposition with morphisms in `D`.
-/
structure IsTerminal (D : Diagram J κ) (e : J) where
  prop_id : D.W (𝟙 e)
  /-- the unique map to the terminal object in the diagram -/
  lift {j : J} (hj : D.P j) : j ⟶ e
  hlift {j : J} (hj : D.P j) : D.W (lift hj)
  uniq {j : J} (hj : D.P j) {φ : j ⟶ e} (hφ : D.W φ) : lift hj = φ
  comm {i j : J} (f : i ⟶ j) (hf : D.W f) : f ≫ lift (D.tgt hf) = lift (D.src hf)

namespace IsTerminal

attribute [reassoc] IsTerminal.comm

variable {D : Diagram J κ} {e : J}

/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTerminal.
prop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardina
l_directed.Diagram.IsTerminal`。
形式化陈述：prop (h : D.IsTerminal e) : D.P e
参数：h : D.IsTerminal e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.src`：
∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}}   (sel
f : CategoryTheory.IsCardinalFiltered.exists_cardinal_direct…
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.prop_id`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardi
nal.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
-/
lemma prop (h : D.IsTerminal e) : D.P e := D.src (h.prop_id)

@[simp]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTerminal.
lift_self** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_ca
rdinal_directed.Diagram.IsTerminal`。
形式化陈述：lift_self (h : D.IsTerminal e) : h.lift h.prop = 𝟙 e
参数：h : D.IsTerminal e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.uniq`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal
.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.prop`：prop (h : D.IsTerminal e) : D.P e
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.prop_id`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardi
nal.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
-/
lemma lift_self (h : D.IsTerminal e) : h.lift h.prop = 𝟙 e := h.uniq _ h.prop_id
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTerminal.
** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_di
rected.Diagram.IsTerminal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (D.IsTerminal e) where
  allEq h₁ h₂ := by
    have : @h₁.lift = @h₂.lift := by
      ext j hj
      exact h₁.uniq hj (h₂.hlift hj)
    cases h₁
    cases h₂
    aesop

/-- Constructor for `Diagram.IsTerminal` for which no data is provided,
but only its existence. -/
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTerminal.
ofExistsUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exis
ts_cardinal_directed.Diagram.IsTerminal`。
形式化陈述：ofExistsUnique (prop_id : D.W (𝟙 e)) (h₁ : forall ⦃j : J⦄ (_ : D.P j), exi
sts (lift : j ⟶ e), D.W lift) (h₂ : forall ⦃j : J⦄ (_ : D.P j) (l₁ l₂ : j ⟶ e), 
D.W l₁ -> D.W l₂ -> l₁ = l₂) (h₃ : forall ⦃i j : J⦄ (f : i ⟶ j) (_ : D.W f), exi
sts (li : i ⟶ e) (lj : j ⟶ e), D.W li ∧ D.W lj ∧ f ≫ lj = li) : D.IsTerminal e w
here prop_id
参数：prop_id : D.W (𝟙 e)；h₁ : forall ⦃j : J⦄ (_ : D.P j), exists (lift : j ⟶ e), D
.W lift；h₂ : forall ⦃j : J⦄ (_ : D.P j) (l₁ l₂ : j ⟶ e), D.W l₁ -> D.W l₂ -> l₁ 
= l₂；h₃ : forall ⦃i j : J⦄ (f : i ⟶ j) (_ : D.W f), exists (li : i ⟶ e) (lj : j 
⟶ e), D.W li ∧ D.W lj ∧ f ≫ lj = li。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Diagram.IsTerminal` for which no data is provided,
but only its existence.
-/
noncomputable def ofExistsUnique (prop_id : D.W (𝟙 e))
    (h₁ : ∀ ⦃j : J⦄ (_ : D.P j), ∃ (lift : j ⟶ e), D.W lift)
    (h₂ : ∀ ⦃j : J⦄ (_ : D.P j) (l₁ l₂ : j ⟶ e), D.W l₁ → D.W l₂ → l₁ = l₂)
    (h₃ : ∀ ⦃i j : J⦄ (f : i ⟶ j) (_ : D.W f), ∃ (li : i ⟶ e) (lj : j ⟶ e),
      D.W li ∧ D.W lj ∧ f ≫ lj = li) :
    D.IsTerminal e where
  prop_id := prop_id
  lift hj := (h₁ hj).choose
  hlift hj := (h₁ hj).choose_spec
  uniq hj φ hφ := h₂ hj (h₁ hj).choose φ (h₁ hj).choose_spec hφ
  comm _ hf := by
    obtain ⟨li, lj, hli, hlj, fac⟩ := h₃ _ hf
    rw [h₂ (D.src hf) _ li (h₁ (D.src hf)).choose_spec hli,
      h₂ (D.tgt hf) _ lj (h₁ (D.tgt hf)).choose_spec hlj, fac]

end IsTerminal

end Diagram

/-- If `κ` is a cardinal, this structure contains the data of a `κ`-bounded diagram
with a unique terminal object in a category `J`. -/
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.DiagramWithUniqueTe
rminal** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_car
dinal_directed`。
形式化陈述：(J : Type w) → [CategoryTheory.SmallCategory J] → Cardinal.{w} → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `κ` is a cardinal, this structure contains the data of a `κ`-bounded diagram
with a unique terminal object in a category `J`.
-/
structure DiagramWithUniqueTerminal extends Diagram J κ where
  /-- the terminal object -/
  top : J
  /-- `top` is terminal -/
  isTerminal : toDiagram.IsTerminal top
  uniq_terminal (j : J) (hj : toDiagram.IsTerminal j) : j = top

@[ext]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.DiagramWithUniqueTe
rminal.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_c
ardinal_directed.DiagramWithUniqueTerminal`。
形式化陈述：∀ (J : Type w) [inst : CategoryTheory.SmallCategory J] (κ : Cardinal.{w}) 
  {D₁ D₂ : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.DiagramWit
hUniqueTerminal J κ},   D₁.W = D₂.W → D₁.P = D₂.P → D₁ = D₂
参数：J : Type w；κ : Cardinal.{w}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.instSubsingleton`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {
κ : Cardinal.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_direc
ted.…
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.ext`：
∀ {J : Type w} {inst : CategoryTheory.SmallCategory J} {κ : Cardinal.{w}}   {x y
 : CategoryTheory.IsCardinalFiltered.exists_cardinal_directe…
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma DiagramWithUniqueTerminal.ext {D₁ D₂ : DiagramWithUniqueTerminal J κ}
    (hW : D₁.W = D₂.W) (hP : D₁.P = D₂.P) : D₁ = D₂ := by
  obtain ⟨D₁, top, h₁, h₁'⟩ := D₁
  obtain ⟨D₂, top', h₂, h₂'⟩ := D₂
  obtain rfl : D₁ = D₂ := by aesop
  obtain rfl : top = top' := h₂' _ h₁
  obtain rfl : h₁ = h₂ := by subsingleton
  rfl
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (DiagramWithUniqueTerminal J κ) where
  le D₁ D₂ := D₁.W ≤ D₂.W ∧ D₁.P ≤ D₂.P
  le_refl _ := ⟨by rfl, by rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := by
    ext : 1
    · exact le_antisymm h₁.1 h₂.1
    · exact le_antisymm h₁.2 h₂.2

section

variable {J κ}

/-- Auxiliary definition for `functor`. -/
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.functorMap** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
形式化陈述：functorMap {D₁ D₂ : DiagramWithUniqueTerminal J κ} (h : D₁ <= D₂) : D₁.top
 ⟶ D₂.top
参数：h : D₁ <= D₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `functor`.
-/
def functorMap {D₁ D₂ : DiagramWithUniqueTerminal J κ} (h : D₁ ≤ D₂) : D₁.top ⟶ D₂.top :=
  D₂.isTerminal.lift (h.2 _ D₁.isTerminal.prop)

@[simp]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.functorMap_id** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed
`。
形式化陈述：functorMap_id (D : DiagramWithUniqueTerminal J κ) : functorMap (le_refl D)
 = 𝟙 D.top
参数：D : DiagramWithUniqueTerminal J κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.lift_self`：lift_self (h : D.IsTerminal e) : h.lift h.prop = 𝟙 e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorMap_id (D : DiagramWithUniqueTerminal J κ) : functorMap (le_refl D) = 𝟙 D.top := by
  simp [functorMap]

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.functorMap_comp** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_direct
ed`。
形式化陈述：functorMap_comp {D₁ D₂ D₃ : DiagramWithUniqueTerminal J κ} (h₁₂ : D₁ <= D₂
) (h₂₃ : D₂ <= D₃) : functorMap h₁₂ ≫ functorMap h₂₃ = functorMap (h₁₂.trans h₂₃
)
参数：h₁₂ : D₁ <= D₂；h₂₃ : D₂ <= D₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.comm`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal
.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.hlift`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardina
l.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
-/
lemma functorMap_comp {D₁ D₂ D₃ : DiagramWithUniqueTerminal J κ} (h₁₂ : D₁ ≤ D₂) (h₂₃ : D₂ ≤ D₃) :
    functorMap h₁₂ ≫ functorMap h₂₃ = functorMap (h₁₂.trans h₂₃) :=
  D₃.isTerminal.comm _ (h₂₃.1 _ (D₂.isTerminal.hlift _))

end

/-- The functor which sends a `κ`-bounded diagram with a unique terminal object to
its terminal object. -/
@[simps]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.functor** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
形式化陈述：functor : DiagramWithUniqueTerminal J κ ⥤ J where obj D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which sends a `κ`-bounded diagram with a unique terminal object to
its terminal object.
-/
def functor : DiagramWithUniqueTerminal J κ ⥤ J where
  obj D := D.top
  map h := functorMap (leOfHom h)

variable [Fact κ.IsRegular]

variable {J κ} in
/-- The diagram containing a single object (and its identity morphism). -/
@[simps]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.single** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directe
d.Diagram`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.SmallCategory J] →     {κ : Cardin
al.{w}} → [Fact κ.IsRegular] → J → CategoryTheory.IsCardinalFiltered.exists_card
inal_directed.Diagram J κ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram containing a single object (and its identity morphism).
-/
def Diagram.single (j : J) : Diagram J κ where
  W := .ofHoms (fun (_ : Unit) ↦ 𝟙 j)
  P := .ofObj (fun (_ : Unit) ↦ j)
  src := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  tgt := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  hW :=
    (hasCardinalLT_of_finite _ κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
        (fun (_ : Unit) ↦ ⟨Arrow.mk (𝟙 j), ⟨⟨⟩⟩⟩) (by
      rintro ⟨f, hf⟩
      refine ⟨⟨⟩, ?_⟩
      ext
      exact ((MorphismProperty.ofHoms_iff _ _).1
        ((MorphismProperty.arrow_mk_mem_toSet_iff _ _).1 hf)).choose_spec.symm)
  hP :=
    (hasCardinalLT_of_finite _ κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
      (fun (_ : Unit) ↦ ⟨j, by simp⟩) (fun ⟨k, hk⟩ ↦ ⟨⟨⟩, by aesop⟩)
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : J) : Finite (Subtype (Diagram.single (κ := κ) j).P) :=
  Finite.of_surjective (fun (_ : Unit) ↦ ⟨j, by simp⟩)
    (by rintro ⟨_, ⟨⟩⟩; exact ⟨⟨⟩, rfl⟩)

variable {J κ} in
/-- The diagram with a unique terminal object containing a single object
(and its identity morphism). -/
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.DiagramWithUniqueTe
rminal.single** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exist
s_cardinal_directed.DiagramWithUniqueTerminal`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.SmallCategory J] →     {κ : Cardin
al.{w}} →       [Fact κ.IsRegular] → J → CategoryTheory.IsCardinalFiltered.exist
s_cardinal_directed.DiagramWithUniqueTerminal J κ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram with a unique terminal object containing a single object
(and its identity morphism).
-/
noncomputable def DiagramWithUniqueTerminal.single (j : J) :
    DiagramWithUniqueTerminal J κ where
  toDiagram := .single j
  top := j
  isTerminal := by
    refine .ofExistsUnique ⟨⟨⟩⟩ (fun _ h ↦ ?_) (fun _ h₁ _ _ h₂ h₃ ↦ ?_) (fun _ _ _ h ↦ ?_)
    · simp only [Diagram.single_P, ObjectProperty.singleton_iff] at h
      subst h
      exact ⟨𝟙 _, ⟨⟨⟩⟩⟩
    · simp only [Diagram.single_P, ObjectProperty.singleton_iff] at h₁
      subst h₁
      obtain ⟨⟨⟩⟩ := h₂
      obtain ⟨⟨⟩⟩ := h₃
      simp
    · obtain ⟨⟨⟩⟩ := h
      exact ⟨𝟙 _, 𝟙 _, ⟨⟨⟩⟩, ⟨⟨⟩⟩, by simp⟩
  uniq_terminal := by rintro _ ⟨⟨⟩⟩; rfl

variable {J κ} in
/-- The union of a `κ`-bounded family of `κ`-bounded diagrams. -/
@[simps]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.iSup** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.
Diagram`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.SmallCategory J] →     {κ : Cardin
al.{w}} →       [Fact κ.IsRegular] →         {ι : Type u_1} →           (ι → Cat
egoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram J κ) →          
   HasCardinalLT ι κ → CategoryTheory.IsCardinalFiltered.exists_cardinal_directe
d.Diagram J κ
参数：ι → CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram J κ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of a `κ`-bounded family of `κ`-bounded diagrams.
-/
def Diagram.iSup {ι : Type*} (D : ι → Diagram J κ) (hι : HasCardinalLT ι κ) :
    Diagram J κ where
  W := ⨆ (i : ι), (D i).W
  P := ⨆ (i : ι), (D i).P
  src hf := by
    simp only [MorphismProperty.iSup_iff, iSup_apply, iSup_Prop_eq] at hf ⊢
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, (D i).src hi⟩
  tgt hf := by
    simp only [MorphismProperty.iSup_iff, iSup_apply, iSup_Prop_eq] at hf ⊢
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, (D i).tgt hi⟩
  hW := .iSup (fun i ↦ (D i).hW) hι
  hP := .iSup (fun i ↦ (D i).hP) hι

variable {J κ} in
/-- The union of two `κ`-bounded diagrams. -/
@[simps]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.sup** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.D
iagram`。
形式化陈述：{J : Type w} →   [inst : CategoryTheory.SmallCategory J] →     {κ : Cardin
al.{w}} →       [Fact κ.IsRegular] →         CategoryTheory.IsCardinalFiltered.e
xists_cardinal_directed.Diagram J κ →           CategoryTheory.IsCardinalFiltere
d.exists_cardinal_directed.Diagram J κ →             CategoryTheory.IsCardinalFi
ltered.exists_cardinal_directed.Diagram J κ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of two `κ`-bounded diagrams.
-/
def Diagram.sup (D₁ D₂ : Diagram J κ) :
    Diagram J κ where
  W := D₁.W ⊔ D₂.W
  P := D₁.P ⊔ D₂.P
  src := by
    rintro _ _ _ (h | h)
    · exact Or.inl (D₁.src h)
    · exact Or.inr (D₂.src h)
  tgt := by
    rintro _ _ _ (h | h)
    · exact Or.inl (D₁.tgt h)
    · exact Or.inr (D₂.tgt h)
  hW := .sup D₁.hW D₂.hW (Cardinal.IsRegular.aleph0_le Fact.out)
  hP := .sup D₁.hP D₂.hP (Cardinal.IsRegular.aleph0_le Fact.out)

variable [IsCardinalFiltered J κ]
  (hJ : ∀ (e : J), ∃ (m : J) (_ : e ⟶ m), IsEmpty (m ⟶ e))

include hJ in
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.isCardinalFiltered_
aux** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal
_directed`。
形式化陈述：isCardinalFiltered_aux {ι : Type w} (D : ι -> DiagramWithUniqueTerminal J 
κ) (hι : HasCardinalLT ι κ) : exists (m : J) (u : forall i, (D i).top ⟶ m), (for
all (i : ι), IsEmpty (m ⟶ (D i).top)) ∧ forall (i₁ i₂ : ι) (j : J) (hj₁ : (D i₁)
.P j) (hj₂ : (D i₂).P j), (D i₁).isTerminal.lift hj₁ ≫ u i₁ = (D i₂).isTerminal.
lift hj₂ ≫ u i₂
参数：D : ι -> DiagramWithUniqueTerminal J κ；hι : HasCardinalLT ι κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `hasCardinalLT_prod`：hasCardinalLT_prod {T₁ : Type u} {T₂ : Type u'} {κ :
 Cardinal.{w}} (hκ : Cardinal.aleph0 <= κ) (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCa
rdinalLT…
· 使用引理 `hasCardinalLT_sigma`：hasCardinalLT_sigma {ι : Type u} (α : ι -> Type v) 
(κ : Cardinal.{w}) [Fact κ.IsRegular] (hι : HasCardinalLT ι κ) (hα : forall i, H
asCardina…
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.hP`：∀
 {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}}   (self
 : CategoryTheory.IsCardinalFiltered.exists_cardinal_direct…
· 使用引理 `HasCardinalLT.of_injective`：of_injective (f : Y -> X) (hf : Function.Inj
ective f) : HasCardinalLT Y κ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Sigma.ext_iff`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x = y ↔ 
x.fst = y.fst ∧ x.snd ≍ y.snd
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用引理 `hasCardinalLT_of_finite`：hasCardinalLT_of_finite (X : Type*) [Finite X] 
(κ : Cardinal) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT X κ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `hasCardinalLT_iff_of_equiv`：hasCardinalLT_iff_of_equiv {X : Type u} {Y :
 Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) : HasCardinalLT X κ ↔ HasCardinalLT Y κ
· 使用引理 `hasCardinalLT_sum_iff`：hasCardinalLT_sum_iff (X : Type u) (Y : Type u') 
(κ : Cardinal.{w}) (hκ : Cardinal.aleph0 <= κ) : HasCardinalLT (X oplus Y) κ ↔ H
asCardinalL…
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Multicofork.condition`：condition (a) : I.fst a ≫ K
.π (J.fst a) = I.snd a ≫ K.π (J.snd a)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma isCardinalFiltered_aux
    {ι : Type w} (D : ι → DiagramWithUniqueTerminal J κ) (hι : HasCardinalLT ι κ) :
    ∃ (m : J) (u : ∀ i, (D i).top ⟶ m), (∀ (i : ι), IsEmpty (m ⟶ (D i).top)) ∧
      ∀ (i₁ i₂ : ι) (j : J) (hj₁ : (D i₁).P j) (hj₂ : (D i₂).P j),
        (D i₁).isTerminal.lift hj₁ ≫ u i₁ = (D i₂).isTerminal.lift hj₂ ≫ u i₂ := by
  choose m₀ t₀ hm₀ using fun i ↦ hJ (D i).top
  let m₁ := IsCardinalFiltered.max m₀ hι
  let t₁ (i : ι) : m₀ i ⟶ m₁ := IsCardinalFiltered.toMax m₀ hι i
  let u (i : ι) : (D i).top ⟶ m₁ := t₀ i ≫ t₁ i
  let S := { x : ι × ι × J // (D x.1).P x.2.2 ∧ (D x.2.1).P x.2.2 }
  let shape : MultispanShape.{w, w} :=
    { L := { x : ι × ι × J // (D x.1).P x.2.2 ∧ (D x.2.1).P x.2.2 }
      R := PUnit
      fst _ := ⟨⟩
      snd _ := ⟨⟩ }
  let index : MultispanIndex shape J :=
    { left x := x.1.2.2
      right _ := m₁
      fst x := (D x.1.1).isTerminal.lift x.2.1 ≫ u x.1.1
      snd x := (D x.1.2.1).isTerminal.lift x.2.2 ≫ u x.1.2.1 }
  have hκ : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
  have hL : HasCardinalLT shape.L κ := by
    have : HasCardinalLT (ι × (Σ (i : ι), Subtype (D i).P)) κ :=
      hasCardinalLT_prod hκ hι (hasCardinalLT_sigma _ _ hι (fun i ↦ (D i).hP))
    refine this.of_injective (fun ⟨⟨i₁, i₂, j⟩, h₁, h₂⟩ ↦ ⟨i₁, i₂, ⟨j, h₂⟩⟩) ?_
    rintro ⟨⟨i₁, i₂, j⟩, _, _⟩ ⟨⟨i₁', i₂', j'⟩, _, _⟩ h
    rw [Prod.ext_iff, Sigma.ext_iff] at h
    dsimp at h
    obtain rfl : i₁ = i₁' := h.1
    obtain rfl : i₂ = i₂' := h.2.1
    obtain rfl : j = j' := by simpa using h
    rfl
  have hR : HasCardinalLT shape.R κ := hasCardinalLT_of_finite _ _ hκ
  have hshape : HasCardinalLT (Arrow (WalkingMultispan shape)) κ := by
    rw [hasCardinalLT_iff_of_equiv (WalkingMultispan.arrowEquiv shape),
      hasCardinalLT_sum_iff _ _ _ hκ, hasCardinalLT_sum_iff _ _ _ hκ,
      hasCardinalLT_iff_of_equiv (WalkingMultispan.equiv shape),
      hasCardinalLT_sum_iff _ _ _ hκ]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> assumption
  let c : Multicofork _ := IsCardinalFiltered.cocone index.multispan hshape
  exact ⟨c.pt, fun i ↦ u i ≫ c.π ⟨⟩,
    fun i ↦ ⟨fun hi ↦ (hm₀ i).false (t₁ i ≫ c.π ⟨⟩ ≫ hi)⟩,
    fun i₁ i₂ j h₁ h₂ ↦ by simpa [index, shape] using c.condition ⟨⟨i₁, i₂, j⟩, h₁, h₂⟩⟩

section

variable {J κ} {ι : Type w} (D : ι → DiagramWithUniqueTerminal J κ) (hι : HasCardinalLT ι κ)
  {m : J} (u : (i : ι) → (D i).top ⟶ m)

variable (m) in
/-- Auxiliary definition for `isCardinalFiltered`. -/
@[simps!]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.D** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `isCardinalFiltered`.
-/
def D₁ : Diagram J κ :=
  (Diagram.iSup (fun i ↦ (D i).toDiagram) hι).sup (.single m)

/-- Auxiliary definition for `isCardinalFiltered`. -/
@[simps!]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.D** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `isCardinalFiltered`.
-/
def D₂ : Diagram J κ where
  W := (D₁ D hι m).W ⊔ MorphismProperty.ofHoms
    fun (x : (Σ (i : ι), (Subtype (D i).P))) ↦ (D x.1).isTerminal.lift x.2.2 ≫ u x.1
  P := (D₁ D hι m).P
  src := by
    simp only [D₁_W, D₁_P]
    rintro _ _ _ ((hf | ⟨⟨⟩⟩) | ⟨i, j, hj⟩)
    · simp only [MorphismProperty.iSup_iff] at hf
      obtain ⟨i, hf⟩ := hf
      exact Or.inl ⟨i, (D i).src hf⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨i, hj⟩
  tgt := by
    simp only [D₁_W, D₁_P]
    rintro _ _ _ ((hf | ⟨⟨⟩⟩) | ⟨i, j, hj⟩)
    · simp only [MorphismProperty.iSup_iff] at hf
      obtain ⟨i, hf⟩ := hf
      exact Or.inl ⟨i, (D i).tgt hf⟩
    · exact Or.inr rfl
    · exact Or.inr rfl
  hW := .sup (D₁ _ _ _).hW (MorphismProperty.hasCardinalLT_ofHoms _
    ((hasCardinalLT_sigma _ _ hι (fun i ↦ (D i).hP)))) (Cardinal.IsRegular.aleph0_le Fact.out)
  hP := (D₁ _ _ _).hP

omit [IsCardinalFiltered J κ] in
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.eq_id_of_D** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq_id_of_D₂_W (hD : ∀ {i : ι}, ¬ (D i).P m) {f : m ⟶ m} (hf : (D₂ D hι u).W f) :
    f = 𝟙 _ := by
  simp only [D₂_W] at hf
  obtain ((hf | ⟨⟨⟩⟩) | hf) := hf
  · simp only [MorphismProperty.iSup_iff] at hf
    obtain ⟨i, hi⟩ := hf
    exact (hD ((D i).src hi)).elim
  · rfl
  · rw [MorphismProperty.ofHoms_iff] at hf
    obtain ⟨⟨i, j, hj⟩, hi⟩ := hf
    obtain rfl : m = j := congr_arg Arrow.leftFunc.obj hi
    exact (hD hj).elim

end

include hJ

/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.isCardinalFiltered*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_dir
ected`。
形式化陈述：isCardinalFiltered : IsCardinalFiltered (DiagramWithUniqueTerminal J κ) κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isCardinalFiltered_preorder`：isCardinalFiltered_preorder 
(J : Type w) [Preorder J] (κ : Cardinal.{w}) [Fact κ.IsRegular] (h : forall ⦃K :
 Type w⦄ (s : K -> J) (_ : Cardi…
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.isCardinalFil
tered_aux`：isCardinalFiltered_aux {ι : Type w} (D : ι -> DiagramWithUniqueTermin
al J κ) (hι : HasCardinalLT ι κ) : exists (m : J) (u : forall i, (D i).…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `hasCardinalLT_iff_cardinal_mk_lt`：hasCardinalLT_iff_cardinal_mk_lt (X : 
Type u) (κ : Cardinal.{u}) : HasCardinalLT X κ ↔ Cardinal.mk X < κ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.D₂_W`：∀ {J : 
Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}} [inst_1 : Fac
t κ.IsRegular] {ι : Type w}   (D : ι → CategoryTheory…
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.tgt`：
∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}}   (sel
f : CategoryTheory.IsCardinalFiltered.exists_cardinal_direct…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.D₂_P`：∀ {J : 
Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}} [inst_1 : Fac
t κ.IsRegular] {ι : Type w}   (D : ι → CategoryTheory…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.eq_id_of_D₂_W
`：eq_id_of_D₂_W (hD : forall {i : ι}, ¬ (D i).P m) {f : m ⟶ m} (hf : (D₂ D hι u)
.W f) : f = 𝟙 _
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.iSup_
W`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}} [in
st_1 : Fact κ.IsRegular] {ι : Type u_1}   (D : ι → CategoryTheo…
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.src`：
∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}}   (sel
f : CategoryTheory.IsCardinalFiltered.exists_cardinal_direct…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.comm_assoc`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Ca
rdinal.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.prop`：prop (h : D.IsTerminal e) : D.P e
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma isCardinalFiltered : IsCardinalFiltered (DiagramWithUniqueTerminal J κ) κ :=
  isCardinalFiltered_preorder _ _ (fun ι D hι ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hι
    obtain ⟨m, u, hm₀, hm⟩ := isCardinalFiltered_aux J κ hJ D hι
    let φ (x : (Σ (i : ι), (Subtype (D i).P))) : x.2.1 ⟶ m :=
      (D x.1).isTerminal.lift x.2.2 ≫ u x.1
    have hD {i : ι} : ¬ (D i).P m := fun hi ↦ (hm₀ i).false ((D i).isTerminal.lift hi)
    let he : (D₂ D hι u).IsTerminal m := by
      have H {i : ι} {j : J} (hj : (D i).P j) {f : j ⟶ m} (hf : (D₂ D hι u).W f) :
          f = φ ⟨i, ⟨_, hj⟩⟩ := by
        simp only [D₂_W] at hf
        obtain ((hf | ⟨⟨⟩⟩) | ⟨⟨i', j, hj'⟩⟩) := hf
        · simp only [MorphismProperty.iSup_iff] at hf
          obtain ⟨i, hf⟩ := hf
          exact (hD ((D i).tgt hf)).elim
        · exact (hD hj).elim
        · apply hm
      refine .ofExistsUnique ?_ ?_ ?_ ?_
      · exact Or.inl (Or.inr ⟨⟨⟩⟩)
      · simp only [D₂_P, D₂_W]
        rintro j (⟨i, hi⟩ | rfl)
        · exact ⟨φ ⟨i, _, hi⟩, Or.inr (.mk _)⟩
        · exact ⟨𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩)⟩
      · intro j hj l₁ l₂ hl₁ hl₂
        simp only [D₂_P] at hj
        obtain (⟨i, hj⟩ | rfl) := hj
        · obtain rfl := H hj hl₁
          obtain rfl := H hj hl₂
          rfl
        · rw [eq_id_of_D₂_W D hι u hD hl₁, eq_id_of_D₂_W D hι u hD hl₂]
      · rintro j k f ((hf | ⟨⟨⟩⟩) | ⟨⟨i, j, hj⟩⟩)
        · simp only [Diagram.iSup_W, MorphismProperty.iSup_iff] at hf
          obtain ⟨i, hf⟩ := hf
          exact ⟨φ ⟨i, j, (D i).src hf⟩, φ ⟨i, k, (D i).tgt hf⟩, Or.inr ⟨_⟩, Or.inr ⟨_⟩,
            by simp [φ, (D i).isTerminal.comm_assoc _ hf]⟩
        · exact ⟨𝟙 _, 𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩), Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
        · refine ⟨φ ⟨i, j, hj⟩, 𝟙 _, Or.inr ⟨_⟩, Or.inl (Or.inr ⟨⟨⟩⟩), by simp [φ]⟩
    let D₂' : DiagramWithUniqueTerminal J κ :=
      { toDiagram := D₂ D hι u
        top := _
        isTerminal := he
        uniq_terminal j hj := by
          have := hj.prop
          simp only [D₂_P] at this
          obtain (⟨i, hi⟩ | rfl) := this
          · exfalso
            exact (hm₀ i).false (hj.lift (by simp) ≫ (D i).isTerminal.lift hi)
          · rfl }
    refine ⟨D₂', fun i ↦ ⟨?_, ?_⟩⟩
    · exact le_trans (le_trans (le_trans (by rfl) (le_iSup _ i)) le_sup_left) le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ i)) le_sup_left)

section

variable {κ J} (D : DiagramWithUniqueTerminal J κ) {m₁ : J}
  (φ : (∀ (x : Subtype D.P), x.val ⟶ m₁))

variable (m₁) in
/-- Auxiliary definition for `final_functor`. -/
@[simps!]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.D** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `final_functor`.
-/
def D₃ : Diagram J κ :=
  D.toDiagram.sup (.single m₁)

/-- Auxiliary definition for `final_functor`. -/
@[simps!]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.D** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `final_functor`.
-/
def D₄ : Diagram J κ where
  W := (D₃ D m₁).W ⊔ .ofHoms φ
  P := (D₃ D m₁).P
  src := by
    rintro i j f (hf | ⟨⟨j, hj⟩⟩)
    · exact (D₃ D m₁).src hf
    · exact Or.inl hj
  tgt := by
    rintro i j f (hf | ⟨⟨j, hj⟩⟩)
    · exact (D₃ D m₁).tgt hf
    · exact Or.inr ⟨⟨⟩⟩
  hW := .sup (D₃ D m₁).hW (MorphismProperty.hasCardinalLT_ofHoms _ D.hP)
    (Cardinal.IsRegular.aleph0_le Fact.out)
  hP := (D₃ D m₁).hP

end

/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.final_functor** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed
`。
形式化陈述：final_functor : (functor J κ).Final
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.isCardinalFil
tered`：isCardinalFiltered : IsCardinalFiltered (DiagramWithUniqueTerminal J κ) κ
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.final_iff_of_isFiltered`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition`：coeq_condition {j j' : C} (f f
' : j ⟶ j') : f ≫ coeqHom f f' = f' ≫ coeqHom f f'
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.tgt`：
∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}}   (sel
f : CategoryTheory.IsCardinalFiltered.exists_cardinal_direct…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.src`：
∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal.{w}}   (sel
f : CategoryTheory.IsCardinalFiltered.exists_cardinal_direct…
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_iff`：ofHoms_iff {ι : Type*} {X Y 
: ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) : ofHoms f g ↔ exists 
i, Arrow.mk g = Arrow.mk (f i)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.comm_assoc`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Ca
rdinal.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.uniq`：∀ {J : Type w} [inst : CategoryTheory.SmallCategory J] {κ : Cardinal
.{w}}   {D : CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.…
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.prop`：prop (h : D.IsTerminal e) : D.P e
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.functor_map`：
∀ (J : Type w) [inst : CategoryTheory.SmallCategory J] (κ : Cardinal.{w})   {X Y
 : CategoryTheory.IsCardinalFiltered.exists_cardinal_directe…
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram.IsTer
minal.lift_self`：lift_self (h : D.IsTerminal e) : h.lift h.prop = 𝟙 e
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma final_functor : (functor J κ).Final := by
  have := isCardinalFiltered J κ hJ
  have := isFiltered_of_isCardinalFiltered J κ
  have := isFiltered_of_isCardinalFiltered (DiagramWithUniqueTerminal J κ) κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun j ↦ ⟨.single j, ⟨𝟙 _⟩⟩, fun {j D} (f₁ f₂ : j ⟶ D.top) ↦ ?_⟩
  obtain ⟨m₀, t, hm₀⟩ := hJ D.top
  obtain ⟨m₁, u, hu⟩ : ∃ (m₁ : J) (u : m₀ ⟶ m₁), f₁ ≫ t ≫ u = f₂ ≫ t ≫ u :=
    ⟨_, IsFiltered.coeqHom (f₁ ≫ t) (f₂ ≫ t),
      by simpa using IsFiltered.coeq_condition (f₁ ≫ t) (f₂ ≫ t)⟩
  have h₁ : ¬ (D.P m₁) := fun h₁ ↦ hm₀.false (u ≫ D.isTerminal.lift h₁)
  let φ (x : Subtype D.P) : x.1 ⟶ m₁ := D.isTerminal.lift x.2 ≫ t ≫ u
  have h₂ {j : J} (hj : D.P j) {f : j ⟶ m₁} (hf : (D₄ D φ).W f) :
      f = φ ⟨_, hj⟩ := by
    obtain ((hf | ⟨⟨⟩⟩) | ⟨⟨⟩⟩) := hf
    · exact (h₁ (D.tgt hf)).elim
    · exact (h₁ hj).elim
    · rfl
  have h₃ {f : m₁ ⟶ m₁} (hf : (D₄ D φ).W f) : f = 𝟙 _ := by
    obtain ((hf | ⟨⟨⟩⟩) | hf) := hf
    · exact (h₁ (D.src hf)).elim
    · rfl
    · rw [MorphismProperty.ofHoms_iff] at hf
      obtain ⟨⟨j, hj⟩, hf⟩ := hf
      obtain rfl : m₁ = j := congr_arg Arrow.leftFunc.obj hf
      exact (h₁ hj).elim
  let hm₁ : (D₄ D φ).IsTerminal m₁ :=
    .ofExistsUnique (Or.inl (Or.inr ⟨⟨⟩⟩)) (by
        rintro j (hj | ⟨⟨⟨⟩⟩⟩)
        · exact ⟨φ ⟨_, hj⟩, Or.inr ⟨_⟩⟩
        · exact ⟨𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩)⟩) (by
        rintro j (hj | ⟨⟨⟨⟩⟩⟩) l₁ l₂ hl₁ hl₂
        · obtain rfl := h₂ hj hl₁
          obtain rfl := h₂ hj hl₂
          rfl
        · rw [h₃ hl₁, h₃ hl₂]) (by
      rintro j k f ((hf | ⟨⟨⟩⟩) | ⟨⟨j, hj⟩⟩)
      · exact ⟨φ ⟨_, D.src hf⟩, φ ⟨_, D.tgt hf⟩,
          Or.inr ⟨_⟩, Or.inr ⟨_⟩, D.isTerminal.comm_assoc _ hf _⟩
      · exact ⟨𝟙 _, 𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩), Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
      · exact ⟨φ ⟨_, hj⟩, 𝟙 _, Or.inr ⟨_⟩, Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩)
  have lift_eq (j : J) (hj : D.P j) : hm₁.lift (Or.inl hj) = φ ⟨_, hj⟩ :=
    hm₁.uniq _ (Or.inr ⟨_⟩)
  let D₄' : DiagramWithUniqueTerminal J κ :=
    { toDiagram := D₄ D φ
      top := m₁
      isTerminal := hm₁
      uniq_terminal j hj := by
        obtain (hj' | ⟨⟨⟩⟩) := hj.prop
        · exact hm₀.elim (u ≫ hj.lift (Or.inr ⟨⟨⟩⟩) ≫ D.isTerminal.lift hj')
        · rfl }
  exact ⟨D₄', homOfLE ⟨le_sup_left.trans le_sup_left, le_sup_left⟩,
    by simpa [functorMap, D₄', lift_eq _ D.isTerminal.prop, φ]⟩
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.aux** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`。
形式化陈述：aux : exists (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ
) (F : α ⥤ J), F.Final
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.isCardinalFil
tered`：isCardinalFiltered : IsCardinalFiltered (DiagramWithUniqueTerminal J κ) κ
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.final_functor
`：final_functor : (functor J κ).Final
-/
lemma aux :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ)
      (F : α ⥤ J), F.Final :=
  ⟨DiagramWithUniqueTerminal J κ, _, isCardinalFiltered J κ hJ,
    functor J κ, final_functor J κ hJ⟩

end exists_cardinal_directed

/-!
The previous lemma `IsCardinalFiltered.exists_cardinal_directed.aux`
is the particular case of the main lemma
`IsCardinalFiltered.exists_cardinal_directed` below in the particular
case the `κ`-filtered category `J` has no object `m : J` such that for any
object `j : J`, there exists a map `j ⟶ m`.

The general case is obtained by applying the previous result to
the cartesian product `J × κ.ord.toType`.
-/

@[stacks 0032]
/-
**CategoryTheory.IsCardinalFiltered.exists_cardinal_directed** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.IsCardinalFiltered`。
形式化陈述：exists_cardinal_directed (J : Type w) [SmallCategory J] (κ : Cardinal.{w})
 [Fact κ.IsRegular] [IsCardinalFiltered J κ] : exists (α : Type w) (_ : PartialO
rder α) (_ : IsCardinalFiltered α κ) (F : α ⥤ J), F.Final
参数：J : Type w；κ : Cardinal.{w}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isFiltered_of_isCardinalFiltered`：isFiltered_of_isCardina
lFiltered (J : Type u) [Category.{v} J] (κ : Cardinal.{w}) [hκ : Fact κ.IsRegula
r] [IsCardinalFiltered J κ] : IsFilte…
· 使用定理 `CategoryTheory.instIsCardinalFilteredToTypeOrd`：∀ (κ : Cardinal.{w}) [hκ
 : Fact κ.IsRegular], CategoryTheory.IsCardinalFiltered κ.ord.ToType κ
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.aux`：aux : ex
ists (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ) (F : α ⥤ J),
 F.Final
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Cardinal.noMaxOrder`：noMaxOrder {c} (h : ℵ₀ <= c) : NoMaxOrder c.ord.ToT
ype
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
· 使用定理 `Order.max_of_succ_le`：max_of_succ_le {a : α} : succ a <= a -> IsMax a
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y

--- 原说明 ---
The previous lemma `IsCardinalFiltered.exists_cardinal_directed.aux`
is the particular case of the main lemma
`IsCardinalFiltered.exists_cardinal_directed` below in the particular
case the `κ`-filtered category `J` has no object `m : J` such that for any
object `j : J`, there exists a map `j ⟶ m`.

The general case is obtained by applying the previous result to
the cartesian product `J × κ.ord.toType`.
-/
lemma exists_cardinal_directed (J : Type w) [SmallCategory J] (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalFiltered J κ] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ)
      (F : α ⥤ J), F.Final := by
  have := isFiltered_of_isCardinalFiltered κ.ord.ToType κ
  obtain ⟨α, _, _, F, _⟩ :=
    exists_cardinal_directed.aux (J × κ.ord.ToType) κ (fun ⟨j, x⟩ ↦
      ⟨⟨j, Order.succ x⟩, (𝟙 _, homOfLE (Order.le_succ x)), ⟨fun ⟨_, f⟩ ↦ by
        have : NoMaxOrder κ.ord.ToType :=
          Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
        exact not_isMax _ (Order.max_of_succ_le (leOfHom f))⟩⟩)
  exact ⟨_, _, inferInstance, F ⋙ Prod.fst _ _, inferInstance⟩

end IsCardinalFiltered

attribute [local instance] Cardinal.fact_isRegular_aleph0 in
@[stacks 0032]
/-
**CategoryTheory.IsFiltered.exists_directed** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsFiltered`。
形式化陈述：∀ (J : Type w) [inst : CategoryTheory.SmallCategory J] [CategoryTheory.IsF
iltered J],   ∃ α x, ∃ (_ : IsDirected α fun x1 x2 => x1 ≤ x2) (_ : Nonempty α),
 ∃ F, F.Final
参数：J : Type w；_ : IsDirected α fun x1 x2 => x1 ≤ x2；_ : Nonempty α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.fact_isRegular_aleph0`：fact_isRegular_aleph0 : Fact (IsRegular 
ℵ₀) where out
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.isCardinalFiltered_aleph0_iff`：isCardinalFiltered_aleph0_
iff (J : Type u) [Category.{v} J] : IsCardinalFiltered J Cardinal.aleph0.{w} ↔ I
sFiltered J
· 使用引理 `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed`：exists_cardi
nal_directed (J : Type w) [SmallCategory J] (κ : Cardinal.{w}) [Fact κ.IsRegular
] [IsCardinalFiltered J κ] : exists (α : Type w)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.IsFiltered.isDirectedOrder`：isDirectedOrder (α : Type u) 
[Preorder α] [IsFiltered α] : IsDirectedOrder α where directed i j
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
-/
lemma IsFiltered.exists_directed
    (J : Type w) [SmallCategory J] [IsFiltered J] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (F : α ⥤ J), F.Final := by
  have := (isCardinalFiltered_aleph0_iff.{w} J).2 inferInstance
  obtain ⟨α, _, _, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed J .aleph0
  have : IsFiltered α := by rwa [← isCardinalFiltered_aleph0_iff.{w}]
  exact ⟨α, _, IsFiltered.isDirectedOrder _, nonempty, F, inferInstance⟩

end CategoryTheory

