/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
public import Mathlib.Tactic.CategoryTheory.BicategoricalComp

/-!
# Adjunctions in bicategories

For 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` in a bicategory, an adjunction between `f` and `g`
consists of a pair of 2-morphisms `η : 𝟙 a ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙 b` satisfying the triangle
identities. The 2-morphism `η` is called the unit and `ε` is called the counit.

## Main definitions

* `Bicategory.Adjunction`: adjunctions between two 1-morphisms.
* `Bicategory.Equivalence`: adjoint equivalences between two objects.
* `Bicategory.Equivalence.mkOfAdjointifyCounit`: construct an adjoint equivalence from
  2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `ε` to a counit.
* `Pseudofunctor.mapAdjunction`: a pseudofunctor `F` carries an adjunction `f ⊣ g`
  between 1-morphisms to an adjunction `F.map f ⊣ F.map g`. An analogous definition is given
  for `StrictPseudofunctor`.

## TODO

* `Bicategory.Equivalence.mkOfAdjointifyUnit`: construct an adjoint equivalence from
  2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `η` to a unit.
-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

namespace Bicategory

/-- The 2-morphism defined by the following pasting diagram:
```
a －－－－－－ ▸ a
  ＼    η      ◥   ＼
  f ＼   g  ／       ＼ f
       ◢  ／     ε      ◢
        b －－－－－－ ▸ b
```
-/
/-
**CategoryTheory.Bicategory.leftZigzag** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Bicategory`。
形式化陈述：leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
参数：η : 𝟙 a ⟶ f ≫ g；ε : g ≫ f ⟶ 𝟙 b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-morphism defined by the following pasting diagram:
```
a －－－－－－ ▸ a
  ＼    η      ◥   ＼
  f ＼   g  ／       ＼ f
       ◢  ／     ε      ◢
        b －－－－－－ ▸ b
```
-/
abbrev leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  η ▷ f ⊗≫ f ◁ ε

/-- The 2-morphism defined by the following pasting diagram:
```
        a －－－－－－ ▸ a
       ◥  ＼     η      ◥
  g ／      ＼ f     ／ g
  ／    ε      ◢   ／
b －－－－－－ ▸ b
```
-/
/-
**CategoryTheory.Bicategory.rightZigzag** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Bicategory`。
形式化陈述：rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
参数：η : 𝟙 a ⟶ f ≫ g；ε : g ≫ f ⟶ 𝟙 b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-morphism defined by the following pasting diagram:
```
        a －－－－－－ ▸ a
       ◥  ＼     η      ◥
  g ／      ＼ f     ／ g
  ／    ε      ◢   ／
b －－－－－－ ▸ b
```
-/
abbrev rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  g ◁ η ⊗≫ ε ▷ g
/-
**CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：rightZigzag_idempotent_of_left_triangle (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b
) (h : leftZigzag η ε = (fun_ _).hom ≫ (ρ_ _).inv) : rightZigzag η ε otimes≫ rig
htZigzag η ε = rightZigzag η ε
参数：η : 𝟙 a ⟶ f ≫ g；ε : g ≫ f ⟶ 𝟙 b；h : leftZigzag η ε = (fun_ _).hom ≫ (ρ_ _).in
v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…
（共 33 条，此处仅展示前 30 条）
-/
theorem rightZigzag_idempotent_of_left_triangle
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) (h : leftZigzag η ε = (λ_ _).hom ≫ (ρ_ _).inv) :
    rightZigzag η ε ⊗≫ rightZigzag η ε = rightZigzag η ε := by
  dsimp only [rightZigzag]
  calc
    _ = g ◁ η ⊗≫ ((ε ▷ g ▷ 𝟙 a) ≫ (𝟙 b ≫ g) ◁ η) ⊗≫ ε ▷ g := by
      bicategory
    _ = 𝟙 _ ⊗≫ g ◁ (η ▷ 𝟙 a ≫ (f ≫ g) ◁ η) ⊗≫ (ε ▷ (g ≫ f) ≫ 𝟙 b ◁ ε) ▷ g ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = g ◁ η ⊗≫ g ◁ leftZigzag η ε ▷ g ⊗≫ ε ▷ g := by
      rw [← whisker_exchange, ← whisker_exchange, leftZigzag]; bicategory
    _ = g ◁ η ⊗≫ ε ▷ g := by
      rw [h]; bicategory

/-- Adjunction between two 1-morphisms. -/
@[ext]
/-
**CategoryTheory.Bicategory.Adjunction** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.Bicategory`。
形式化陈述：Adjunction (f : a ⟶ b) (g : b ⟶ a) where /-- The unit of an adjunction. -/
 unit : 𝟙 a ⟶ f ≫ g /-- The counit of an adjunction. -/ counit : g ≫ f ⟶ 𝟙 b /--
 The composition of the unit and the counit is equal to the identity up to unito
rs. -/ left_triangle : leftZigzag unit counit = (fun_ _).hom ≫ (ρ_ _).inv
参数：f : a ⟶ b；g : b ⟶ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjunction between two 1-morphisms.
-/
structure Adjunction (f : a ⟶ b) (g : b ⟶ a) where
  /-- The unit of an adjunction. -/
  unit : 𝟙 a ⟶ f ≫ g
  /-- The counit of an adjunction. -/
  counit : g ≫ f ⟶ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzag unit counit = (λ_ _).hom ≫ (ρ_ _).inv := by cat_disch
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (λ_ _).inv := by cat_disch

@[inherit_doc] scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

attribute [simp] left_triangle right_triangle

/-- Adjunction between identities. -/
/-
**CategoryTheory.Bicategory.Adjunction.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Bicategory.Adjunction`。
形式化陈述：id (a : B) : 𝟙 a ⊣ 𝟙 a where unit
参数：a : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjunction between identities.
-/
def id (a : B) : 𝟙 a ⊣ 𝟙 a where
  unit := (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by bicategory_coherence
  right_triangle := by bicategory_coherence
/-
**CategoryTheory.Bicategory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Bicategory.Adjunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Adjunction (𝟙 a) (𝟙 a)) :=
  ⟨id a⟩

section Composition

variable {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `Adjunction.comp`. -/
@[simp]
/-
**CategoryTheory.Bicategory.Adjunction.compUnit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bicategory.Adjunction`。
形式化陈述：compUnit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁
参数：adj₁ : f₁ ⊣ g₁；adj₂ : f₂ ⊣ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Adjunction.comp`.
-/
def compUnit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
  adj₁.unit ⊗≫ f₁ ◁ adj₂.unit ▷ g₁ ⊗≫ 𝟙 _

/-- Auxiliary definition for `Adjunction.comp`. -/
@[simp]
/-
**CategoryTheory.Bicategory.Adjunction.compCounit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Bicategory.Adjunction`。
形式化陈述：compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c
参数：adj₁ : f₁ ⊣ g₁；adj₂ : f₂ ⊣ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Adjunction.comp`.
-/
def compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
  𝟙 _ ⊗≫ g₂ ◁ adj₁.counit ▷ f₂ ⊗≫ adj₂.counit
/-
**CategoryTheory.Bicategory.Adjunction.comp_left_triangle_aux** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Bicategory.Adjunction`。
形式化陈述：comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : leftZigzag (com
pUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (fun_ _).hom ≫ (ρ_ _).inv
参数：adj₁ : f₁ ⊣ g₁；adj₂ : f₂ ⊣ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
（共 36 条，此处仅展示前 30 条）
-/
theorem comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    leftZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (λ_ _).hom ≫ (ρ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          adj₁.unit ▷ (f₁ ≫ f₂) ⊗≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ ⊗≫
              (f₁ ≫ f₂) ◁ adj₂.counit ⊗≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ ⊗≫
          (leftZigzag adj₁.unit adj₁.counit) ▷ f₂ ⊗≫
            f₁ ◁ (leftZigzag adj₂.unit adj₂.counit) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [left_triangle]; bicategory
/-
**CategoryTheory.Bicategory.Adjunction.comp_right_triangle_aux** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Bicategory.Adjunction`。
形式化陈述：comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : rightZigzag (c
ompUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (ρ_ _).hom ≫ (fun_ _).inv
参数：adj₁ : f₁ ⊣ g₁；adj₂ : f₂ ⊣ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_whisker`：evalWhiskerRigh
t_cons_whisker {f : a ⟶ b} {g : a ⟶ c} {h i : b ⟶ c} {j : a ⟶ c} {k : c ⟶ d} {α 
: g ≅ f ≫ h} {η : h ⟶ i} {ηs : f ≫ i ⟶ j} {η₁…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whisker_exchange`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ :
 h ⟶ i),   CategoryTheory.Catego…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_id`：evalWhiskerLeft_id {η : f 
⟶ g} {η₁ : f ⟶ 𝟙 a ≫ g} {η₂ : 𝟙 a ≫ f ⟶ 𝟙 a ≫ g} (e_η₁ : η ≫ (fun_ _).inv = η₁) 
(e_η₂ : (fun_ _).hom ≫ η₁ = η₂) : …
（共 35 条，此处仅展示前 30 条）
-/
theorem comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    rightZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (ρ_ _).hom ≫ (λ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          (g₂ ≫ g₁) ◁ adj₁.unit ⊗≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ ⊗≫
              adj₂.counit ▷ (g₂ ≫ g₁) ⊗≫ 𝟙 _ := by
      dsimp only [compUnit, compCounit]; bicategory
    _ = 𝟙 _ ⊗≫
          g₂ ◁ (rightZigzag adj₁.unit adj₁.counit) ⊗≫
            (rightZigzag adj₂.unit adj₂.counit) ▷ g₁ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; bicategory
    _ = _ := by
      simp_rw [right_triangle]; bicategory

/-- Composition of adjunctions. -/
@[simps]
/-
**CategoryTheory.Bicategory.Adjunction.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Bicategory.Adjunction`。
形式化陈述：comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where unit
参数：adj₁ : f₁ ⊣ g₁；adj₂ : f₂ ⊣ g₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of adjunctions.
-/
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where
  unit := compUnit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

end Composition

end Adjunction

noncomputable section

variable (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

/-- The isomorphism version of `leftZigzag`. -/
/-
**CategoryTheory.Bicategory.leftZigzagIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：leftZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
参数：η : 𝟙 a ≅ f ≫ g；ε : g ≫ f ≅ 𝟙 b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism version of `leftZigzag`.
-/
abbrev leftZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerRightIso η f ≪⊗≫ whiskerLeftIso f ε

/-- The isomorphism version of `rightZigzag`. -/
/-
**CategoryTheory.Bicategory.rightZigzagIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：rightZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)
参数：η : 𝟙 a ≅ f ≫ g；ε : g ≫ f ≅ 𝟙 b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism version of `rightZigzag`.
-/
abbrev rightZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerLeftIso g η ≪⊗≫ whiskerRightIso ε g

@[simp]
/-
**CategoryTheory.Bicategory.leftZigzagIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：leftZigzagIso_hom : (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftZigzagIso_hom : (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom :=
  rfl

@[simp]
/-
**CategoryTheory.Bicategory.rightZigzagIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Bicategory`。
形式化陈述：rightZigzagIso_hom : (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightZigzagIso_hom : (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom :=
  rfl

@[simp]
/-
**CategoryTheory.Bicategory.leftZigzagIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：leftZigzagIso_inv : (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.bicategoricalIsoComp.eq_1`：∀ {B : Type u} [inst : Categor
yTheory.Bicategory B] {a b : B} {f g h i : a ⟶ b}   [inst_1 : CategoryTheory.Bic
ategoricalCoherence g h] (η : …
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.bicategoricalComp.eq_1`：∀ {B : Type u} [inst : CategoryTh
eory.Bicategory B] {a b : B} {f g h i : a ⟶ b}   [inst_1 : CategoryTheory.Bicate
goricalCoherence g h] (η : …
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftZigzagIso_inv : (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
/-
**CategoryTheory.Bicategory.rightZigzagIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Bicategory`。
形式化陈述：rightZigzagIso_inv : (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.bicategoricalIsoComp.eq_1`：∀ {B : Type u} [inst : Categor
yTheory.Bicategory B] {a b : B} {f g h i : a ⟶ b}   [inst_1 : CategoryTheory.Bic
ategoricalCoherence g h] (η : …
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_inv`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeftIso_inv`：∀ {B : Type u} [inst : Cat
egoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h),   (
CategoryTheory.Bicategory.whiskerL…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.bicategoricalComp.eq_1`：∀ {B : Type u} [inst : CategoryTh
eory.Bicategory B] {a b : B} {f g h i : a ⟶ b}   [inst_1 : CategoryTheory.Bicate
goricalCoherence g h] (η : …
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightZigzagIso_inv : (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
/-
**CategoryTheory.Bicategory.leftZigzagIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Bicategory`。
形式化陈述：leftZigzagIso_symm : (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.sy
mm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Bicategory.leftZigzagIso_inv`：leftZigzagIso_inv : (leftZi
gzagIso η ε).inv = rightZigzag ε.inv η.inv
-/
theorem leftZigzagIso_symm : (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm :=
  Iso.ext (leftZigzagIso_inv η ε)

@[simp]
/-
**CategoryTheory.Bicategory.rightZigzagIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：rightZigzagIso_symm : (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.s
ymm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Bicategory.rightZigzagIso_inv`：rightZigzagIso_inv : (righ
tZigzagIso η ε).inv = leftZigzag ε.inv η.inv
-/
theorem rightZigzagIso_symm : (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm :=
  Iso.ext (rightZigzagIso_inv η ε)
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (leftZigzag η.hom ε.hom) := inferInstanceAs <| IsIso (leftZigzagIso η ε).hom
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (rightZigzag η.hom ε.hom) := inferInstanceAs <| IsIso (rightZigzagIso η ε).hom
/-
**CategoryTheory.Bicategory.right_triangle_of_left_triangle** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Bicategory`。
形式化陈述：right_triangle_of_left_triangle (h : leftZigzag η.hom ε.hom = (fun_ f).hom
 ≫ (ρ_ f).inv) : rightZigzag η.hom ε.hom = (ρ_ g).hom ≫ (fun_ g).inv
参数：h : leftZigzag η.hom ε.hom = (fun_ f).hom ≫ (ρ_ f).inv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Bicategory.instIsIsoHomRightZigzagHom`：∀ {B : Type u₁} [i
nst : CategoryTheory.Bicategory B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}   (η : Cate
goryTheory.CategoryStruct.id a ≅ CategoryT…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
（共 40 条，此处仅展示前 30 条）
-/
theorem right_triangle_of_left_triangle (h : leftZigzag η.hom ε.hom = (λ_ f).hom ≫ (ρ_ f).inv) :
    rightZigzag η.hom ε.hom = (ρ_ g).hom ≫ (λ_ g).inv := by
  rw [← cancel_epi (rightZigzag η.hom ε.hom ≫ (λ_ g).hom ≫ (ρ_ g).inv)]
  calc
    _ = rightZigzag η.hom ε.hom ⊗≫ rightZigzag η.hom ε.hom := by bicategory
    _ = rightZigzag η.hom ε.hom := rightZigzag_idempotent_of_left_triangle _ _ h
    _ = _ := by simp

/-- An auxiliary definition for `mkOfAdjointifyCounit`. -/
/-
**CategoryTheory.Bicategory.adjointifyCounit** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b
参数：η : 𝟙 a ≅ f ≫ g；ε : g ≫ f ≅ 𝟙 b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition for `mkOfAdjointifyCounit`.
-/
def adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
  whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ λ_ f) ≪≫ ε

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Bicategory.adjointifyCounit_left_triangle** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Bicategory`。
形式化陈述：adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : leftZ
igzagIso η (adjointifyCounit η ε) = fun_ f ≪≫ (ρ_ f).symm
参数：η : 𝟙 a ≅ f ≫ g；ε : g ≫ f ≅ 𝟙 b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq`：mk_eq {α : Type _} (a b a' b' : α) 
(ha : a = a') (hb : b = b') (h : a' = b') : a = b
· 使用定理 `Mathlib.Tactic.Bicategory.eval_bicategoricalComp`：eval_bicategoricalComp
 {η η' : f ⟶ g} {α : g ≅ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i} (e_η : η =
 η') (e_θ : θ = θ') (e_αθ : α.hom ≫ θ'…
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerRight`：eval_whiskerRight {f g : a 
⟶ b} {h : b ⟶ c} {η η' : f ⟶ g} {θ : f ≫ h ⟶ g ≫ h} (e_η : η = η') (e_θ : η' ▷ h
 = θ) : η ▷ h = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_of`：eval_of (η : f ⟶ g) : η = (Iso.refl _
).hom ≫ η ≫ (Iso.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_cons_of_of`：evalWhiskerRight_
cons_of_of {f g h i : a ⟶ b} {j : b ⟶ c} {α : f ≅ g} {η : g ⟶ h} {ηs : h ⟶ i} {η
s₁ : h ≫ j ⟶ i ≫ j} {η₁ : g ≫ j ⟶ h ≫ j} {η…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_nil`：evalWhiskerRight_nil (α 
: f ≅ g) (h : b ⟶ c) : α.hom ▷ h = α.hom ▷ h
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRightAux_of`：evalWhiskerRightAux_of
 {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : η ▷ h = (Iso.refl _).hom ≫ η ▷ h ≫ (Iso
.refl _).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_cons`：evalComp_cons (α : f ≅ g) (η : 
g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j} (e_ι : ηs ≫ θ = ι) : (α.hom ≫ η ≫ ηs
) ≫ θ = α.hom ≫ η ≫ ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_nil`：evalComp_nil_nil (α : f ≅ g)
 (β : g ≅ h) : (α ≪≫ β).hom = (α ≪≫ β).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalComp_nil_cons`：evalComp_nil_cons (α : f ≅ 
g) (β : g ≅ h) (η : h ⟶ i) (ηs : i ⟶ j) : α.hom ≫ (β.hom ≫ η ≫ ηs) = (α ≪≫ β).ho
m ≫ η ≫ ηs
· 使用定理 `Mathlib.Tactic.Bicategory.eval_whiskerLeft`：eval_whiskerLeft {f : a ⟶ b}
 {g h : b ⟶ c} {η η' : g ⟶ h} {θ : f ≫ g ⟶ f ≫ h} (e_η : η = η') (e_θ : f ◁ η' =
 θ) : f ◁ η = θ
· 使用定理 `Mathlib.Tactic.Bicategory.eval_comp`：eval_comp {η η' : f ⟶ g} {θ θ' : g 
⟶ h} {ι : f ⟶ h} (e_η : η = η') (e_θ : θ = θ') (e_ηθ : η' ≫ θ' = ι) : η ≫ θ = ι
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_of_cons`：evalWhiskerLeft_of_co
ns {f : a ⟶ b} {g h i j : b ⟶ c} (α : g ≅ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ≫ i
 ⟶ f ≫ j} (e_θ : f ◁ ηs = θ) : f ◁ (α.h…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_nil`：evalWhiskerLeft_nil (f : 
a ⟶ b) {g h : b ⟶ c} (α : g ≅ h) : (whiskerLeftIso f α).hom = (whiskerLeftIso f 
α).hom
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_comp`：evalWhiskerRight_comp {
f f' : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {η : f ⟶ f'} {η₁ : f ≫ g ⟶ f' ≫ g} {η₂ : (
f ≫ g) ≫ h ⟶ (f' ≫ g) ≫ h} {η₃ : (f ≫…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerRight_id`：evalWhiskerRight_id {η : 
f ⟶ g} {η₁ : f ⟶ g ≫ 𝟙 b} {η₂ : f ≫ 𝟙 b ⟶ g ≫ 𝟙 b} (e_η₁ : η ≫ (ρ_ _).inv = η₁) 
(e_η₂ : (ρ_ _).hom ≫ η₁ = η₂) : η ▷…
· 使用定理 `Mathlib.Tactic.Bicategory.evalWhiskerLeft_comp`：evalWhiskerLeft_comp {f 
: a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} {η₁ : g ≫ h ⟶ g ≫ i} {η₂ : f ≫ g 
≫ h ⟶ f ≫ g ≫ i} {η₃ : f ≫ g ≫ h ⟶ (…
· 使用定理 `Mathlib.Tactic.BicategoryLike.mk_eq_of_cons`：mk_eq_of_cons {C : Type u} 
[CategoryStruct.{v} C] {f₁ f₂ f₃ f₄ : C} (α α' : f₁ ⟶ f₂) (η η' : f₂ ⟶ f₃) (ηs η
s' : f₃ ⟶ f₄) (e_α : α = α') (e_η…
· 使用定理 `Mathlib.Tactic.Bicategory.mk_eq_of_naturality`：mk_eq_of_naturality {f g 
f' : a ⟶ b} {η θ : f ⟶ g} {η' θ' : f ≅ g} (η_f : 𝟙 a ≫ f ≅ f') (η_g : 𝟙 a ≫ g ≅ 
f') (Hη : η'.hom = η) (Hθ : θ'.hom …
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_comp`：naturality_comp {p : a ⟶ b} {
f g h : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} {θ : g ≅ h} (η_f : p ≫ f ≅ pf) (η_g : p 
≫ g ≅ pf) (η_h : p ≫ h ≅ pf) (i…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerRight`：naturality_whiskerRig
ht {p : a ⟶ b} {f g : b ⟶ c} {h : c ⟶ d} {pf : a ⟶ c} {pfh : a ⟶ d} {η : f ≅ g} 
(η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_id`：naturality_id {p : a ⟶ b} {f : 
b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ Iso.refl f ≪≫ η_f = η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_leftUnitor`：naturality_leftUnitor {
p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (fun_ f) ≪≫ η_f = n
ormalizeIsoComp (ρ_ p) η_f
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_inv`：naturality_inv {p : a ⟶ b} {f 
g : b ⟶ c} {pf : a ⟶ c} {η : f ≅ g} (η_f : p ≫ f ≅ pf) (η_g : p ≫ g ≅ pf) (ih : 
p ◁ η ≪≫ η_g = η_f) : p ◁ η.sy…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_rightUnitor`：naturality_rightUnitor
 {p : a ⟶ b} {f : b ⟶ c} {pf : a ⟶ c} (η_f : p ≫ f ≅ pf) : p ◁ (ρ_ f) ≪≫ η_f = n
ormalizeIsoComp η_f (ρ_ pf)
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_associator`：naturality_associator {
p : a ⟶ b} {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e} {pf : a ⟶ c} {pfg : a ⟶ d} {pfgh 
: a ⟶ e} (η_f : p ≫ f ≅ pf) (η_g : pf…
· 使用定理 `Mathlib.Tactic.Bicategory.naturality_whiskerLeft`：naturality_whiskerLeft
 {p : a ⟶ b} {f : b ⟶ c} {g h : c ⟶ d} {pf : a ⟶ c} {pfg : a ⟶ d} {η : g ≅ h} (η
_f : p ≫ f ≅ pf) (η_fg : pf ≫ g ≅ pfg)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）
-/
theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagIso η (adjointifyCounit η ε) = λ_ f ≪≫ (ρ_ f).symm := by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
          f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := by
      bicategory
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; bicategory
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; bicategory
    _ = 𝟙 _ ⊗≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; bicategory
    _ = _ := by
      rw [Iso.inv_hom_id]; bicategory

/-- Adjoint equivalences between two objects. -/
/-
**CategoryTheory.Bicategory.Equivalence** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheor
y.Bicategory`。
形式化陈述：Equivalence (a b : B) where /-- A 1-morphism in one direction. -/ hom : a 
⟶ b /-- A 1-morphism in the other direction. -/ inv : b ⟶ a /-- The composition 
`hom ≫ inv` is isomorphic to the identity. -/ unit : 𝟙 a ≅ hom ≫ inv /-- The com
position `inv ≫ hom` is isomorphic to the identity. -/ counit : inv ≫ hom ≅ 𝟙 b 
/-- The composition of the unit and the counit is equal to the identity up to un
itors. -/ left_triangle : leftZigzagIso unit counit = fun_ hom ≪≫ (ρ_ hom).symm
参数：a b : B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adjoint equivalences between two objects.
-/
structure Equivalence (a b : B) where
  /-- A 1-morphism in one direction. -/
  hom : a ⟶ b
  /-- A 1-morphism in the other direction. -/
  inv : b ⟶ a
  /-- The composition `hom ≫ inv` is isomorphic to the identity. -/
  unit : 𝟙 a ≅ hom ≫ inv
  /-- The composition `inv ≫ hom` is isomorphic to the identity. -/
  counit : inv ≫ hom ≅ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzagIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := by cat_disch

@[inherit_doc] scoped infixr:10 " ≌ " => Bicategory.Equivalence

namespace Equivalence

/-- The identity 1-morphism is an equivalence. -/
/-
**CategoryTheory.Bicategory.Equivalence.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Bicategory.Equivalence`。
形式化陈述：id (a : B) : a ≌ a
参数：a : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity 1-morphism is an equivalence.
-/
def id (a : B) : a ≌ a := ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩
/-
**CategoryTheory.Bicategory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Bicategory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Equivalence a a) := ⟨id a⟩
/-
**CategoryTheory.Bicategory.Equivalence.left_triangle_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Bicategory.Equivalence`。
形式化陈述：left_triangle_hom (e : a ≌ b) : leftZigzag e.unit.hom e.counit.hom = (fun_
 e.hom).hom ≫ (ρ_ e.hom).inv
参数：e : a ≌ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.Equivalence.left_triangle`：∀ {B : Type u₁} [in
st : CategoryTheory.Bicategory B] {a b : B} (self : CategoryTheory.Bicategory.Eq
uivalence a b),   CategoryTheory.Bicatego…
-/
theorem left_triangle_hom (e : a ≌ b) :
    leftZigzag e.unit.hom e.counit.hom = (λ_ e.hom).hom ≫ (ρ_ e.hom).inv :=
  congrArg Iso.hom e.left_triangle
/-
**CategoryTheory.Bicategory.Equivalence.right_triangle** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bicategory.Equivalence`。
形式化陈述：right_triangle (e : a ≌ b) : rightZigzagIso e.unit e.counit = ρ_ e.inv ≪≫ 
(fun_ e.inv).symm
参数：e : a ≌ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Bicategory.right_triangle_of_left_triangle`：right_triangl
e_of_left_triangle (h : leftZigzag η.hom ε.hom = (fun_ f).hom ≫ (ρ_ f).inv) : ri
ghtZigzag η.hom ε.hom = (ρ_ g).hom ≫ (fun_ g).i…
· 使用定理 `CategoryTheory.Bicategory.Equivalence.left_triangle_hom`：left_triangle_h
om (e : a ≌ b) : leftZigzag e.unit.hom e.counit.hom = (fun_ e.hom).hom ≫ (ρ_ e.h
om).inv
-/
theorem right_triangle (e : a ≌ b) :
    rightZigzagIso e.unit e.counit = ρ_ e.inv ≪≫ (λ_ e.inv).symm :=
  Iso.ext (right_triangle_of_left_triangle e.unit e.counit e.left_triangle_hom)
/-
**CategoryTheory.Bicategory.Equivalence.right_triangle_hom** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Bicategory.Equivalence`。
形式化陈述：right_triangle_hom (e : a ≌ b) : rightZigzag e.unit.hom e.counit.hom = (ρ_
 e.inv).hom ≫ (fun_ e.inv).inv
参数：e : a ≌ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.Equivalence.right_triangle`：right_triangle (e 
: a ≌ b) : rightZigzagIso e.unit e.counit = ρ_ e.inv ≪≫ (fun_ e.inv).symm
-/
theorem right_triangle_hom (e : a ≌ b) :
    rightZigzag e.unit.hom e.counit.hom = (ρ_ e.inv).hom ≫ (λ_ e.inv).inv :=
  congrArg Iso.hom e.right_triangle

/-- Construct an adjoint equivalence from 2-isomorphisms by upgrading `ε` to a counit. -/
/-
**CategoryTheory.Bicategory.Equivalence.mkOfAdjointifyCounit** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Bicategory.Equivalence`。
形式化陈述：mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where hom
参数：η : 𝟙 a ≅ f ≫ g；ε : g ≫ f ≅ 𝟙 b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.adjointifyCounit_left_triangle`：adjointifyCoun
it_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : leftZigzagIso η (adjointi
fyCounit η ε) = fun_ f ≪≫ (ρ_ f).symm

--- 原说明 ---
Construct an adjoint equivalence from 2-isomorphisms by upgrading `ε` to a couni
t.
-/
def mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where
  hom := f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

end Equivalence

end

noncomputable
section

/-- A structure giving a chosen right adjoint of a 1-morphism `left`. -/
/-
**CategoryTheory.Bicategory.RightAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Bicategory`。
形式化陈述：{B : Type u₁} → [inst : CategoryTheory.Bicategory B] → {a b : B} → (a ⟶ b)
 → Type (max v₁ w₁)
参数：a ⟶ b；max v₁ w₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure giving a chosen right adjoint of a 1-morphism `left`.
-/
structure RightAdjoint (left : a ⟶ b) where
  /-- The right adjoint to `left`. -/
  right : b ⟶ a
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/-- The existence of a right adjoint of `f`. -/
/-
**CategoryTheory.Bicategory.IsLeftAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：{B : Type u₁} → [inst : CategoryTheory.Bicategory B] → {a b : B} → (a ⟶ b)
 → Prop
参数：a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The existence of a right adjoint of `f`.
-/
class IsLeftAdjoint (left : a ⟶ b) : Prop where mk' ::
  nonempty : Nonempty (RightAdjoint left)
/-
**CategoryTheory.Bicategory.IsLeftAdjoint.mk** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory.IsLeftAdjoint`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {a b : B} {f : a ⟶ b}
 {g : b ⟶ a}   (adj : CategoryTheory.Bicategory.Adjunction f g), CategoryTheory.
Bicategory.IsLeftAdjoint f
参数：adj : CategoryTheory.Bicategory.Adjunction f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsLeftAdjoint.mk (adj : f ⊣ g) : IsLeftAdjoint f :=
  ⟨⟨g, adj⟩⟩

/-- Use the axiom of choice to extract a right adjoint from an `IsLeftAdjoint` instance. -/
/-
**CategoryTheory.Bicategory.getRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：getRightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : RightAdjoint f
参数：f : a ⟶ b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.IsLeftAdjoint.nonempty`：∀ {B : Type u₁} {inst 
: CategoryTheory.Bicategory B} {a b : B} {left : a ⟶ b}   [self : CategoryTheory
.Bicategory.IsLeftAdjoint left], Nonem…

--- 原说明 ---
Use the axiom of choice to extract a right adjoint from an `IsLeftAdjoint` insta
nce.
-/
def getRightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : RightAdjoint f :=
  Classical.choice IsLeftAdjoint.nonempty

/-- The right adjoint of a 1-morphism. -/
/-
**CategoryTheory.Bicategory.rightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Bicategory`。
形式化陈述：rightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : b ⟶ a
参数：f : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint of a 1-morphism.
-/
def rightAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : b ⟶ a :=
  (getRightAdjoint f).right

/-- Evidence that `rightAdjoint f` is a right adjoint of `f`. -/
/-
**CategoryTheory.Bicategory.Adjunction.ofIsLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Bicategory.Adjunction`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {a b : B} →  
     (f : a ⟶ b) →         [inst_1 : CategoryTheory.Bicategory.IsLeftAdjoint f] 
→           CategoryTheory.Bicategory.Adjunction f (CategoryTheory.Bicategory.ri
ghtAdjoint f)
参数：f : a ⟶ b；CategoryTheory.Bicategory.rightAdjoint f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evidence that `rightAdjoint f` is a right adjoint of `f`.
-/
def Adjunction.ofIsLeftAdjoint (f : a ⟶ b) [IsLeftAdjoint f] : f ⊣ rightAdjoint f :=
  (getRightAdjoint f).adj

/-- A structure giving a chosen left adjoint of a 1-morphism `right`. -/
/-
**CategoryTheory.Bicategory.LeftAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Bicategory`。
形式化陈述：{B : Type u₁} → [inst : CategoryTheory.Bicategory B] → {a b : B} → (b ⟶ a)
 → Type (max v₁ w₁)
参数：b ⟶ a；max v₁ w₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure giving a chosen left adjoint of a 1-morphism `right`.
-/
structure LeftAdjoint (right : b ⟶ a) where
  /-- The left adjoint to `right`. -/
  left : a ⟶ b
  /-- The adjunction between `left` and `right`. -/
  adj : left ⊣ right

/-- The existence of a left adjoint of `right`. -/
/-
**CategoryTheory.Bicategory.IsRightAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：{B : Type u₁} → [inst : CategoryTheory.Bicategory B] → {a b : B} → (b ⟶ a)
 → Prop
参数：b ⟶ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The existence of a left adjoint of `right`.
-/
class IsRightAdjoint (right : b ⟶ a) : Prop where mk' ::
  nonempty : Nonempty (LeftAdjoint right)
/-
**CategoryTheory.Bicategory.IsRightAdjoint.mk** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Bicategory.IsRightAdjoint`。
形式化陈述：∀ {B : Type u₁} [inst : CategoryTheory.Bicategory B] {a b : B} {f : a ⟶ b}
 {g : b ⟶ a}   (adj : CategoryTheory.Bicategory.Adjunction f g), CategoryTheory.
Bicategory.IsRightAdjoint g
参数：adj : CategoryTheory.Bicategory.Adjunction f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsRightAdjoint.mk (adj : f ⊣ g) : IsRightAdjoint g :=
  ⟨⟨f, adj⟩⟩

/-- Use the axiom of choice to extract a left adjoint from an `IsRightAdjoint` instance. -/
/-
**CategoryTheory.Bicategory.getLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Bicategory`。
形式化陈述：getLeftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : LeftAdjoint f
参数：f : b ⟶ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.IsRightAdjoint.nonempty`：∀ {B : Type u₁} {inst
 : CategoryTheory.Bicategory B} {a b : B} {right : b ⟶ a}   [self : CategoryTheo
ry.Bicategory.IsRightAdjoint right], No…

--- 原说明 ---
Use the axiom of choice to extract a left adjoint from an `IsRightAdjoint` insta
nce.
-/
def getLeftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : LeftAdjoint f :=
  Classical.choice IsRightAdjoint.nonempty

/-- The left adjoint of a 1-morphism. -/
/-
**CategoryTheory.Bicategory.leftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Bicategory`。
形式化陈述：leftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : a ⟶ b
参数：f : b ⟶ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left adjoint of a 1-morphism.
-/
def leftAdjoint (f : b ⟶ a) [IsRightAdjoint f] : a ⟶ b :=
  (getLeftAdjoint f).left

/-- Evidence that `leftAdjoint f` is a left adjoint of `f`. -/
/-
**CategoryTheory.Bicategory.Adjunction.ofIsRightAdjoint** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Bicategory.Adjunction`。
形式化陈述：{B : Type u₁} →   [inst : CategoryTheory.Bicategory B] →     {a b : B} →  
     (f : b ⟶ a) →         [inst_1 : CategoryTheory.Bicategory.IsRightAdjoint f]
 →           CategoryTheory.Bicategory.Adjunction (CategoryTheory.Bicategory.lef
tAdjoint f) f
参数：f : b ⟶ a；CategoryTheory.Bicategory.leftAdjoint f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evidence that `leftAdjoint f` is a left adjoint of `f`.
-/
def Adjunction.ofIsRightAdjoint (f : b ⟶ a) [IsRightAdjoint f] : leftAdjoint f ⊣ f :=
  (getLeftAdjoint f).adj

end

end Bicategory

namespace Pseudofunctor

variable (F : Pseudofunctor B C) (adj : f ⊣ g)

/-
**CategoryTheory.Pseudofunctor.leftZigzag_map** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Pseudofunctor`。
形式化陈述：leftZigzag_map : leftZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapCom
p f g).hom) ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) = (F.map
Id a).inv ▷ F.map f otimes≫ (F.mapComp (𝟙 a) f).inv ≫ F.map₂ (leftZigzag adj.uni
t adj.counit) ≫ (F.mapComp f (𝟙 b)).hom otimes≫ F.map f ◁ (F.mapId b).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_comp`：∀ {B : Type u₁} [inst : Category
Theory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (sel
f : CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_whisker_right`：∀ {B : Type u₁} [inst :
 CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory 
C]   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_associator`：∀ {B : Type u₁} [inst : Ca
tegoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C] 
  (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_whisker_left`：∀ {B : Type u₁} [inst : 
CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C
]   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftZigzag_map :
    leftZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom)
      ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) =
    (F.mapId a).inv ▷ F.map f ⊗≫ (F.mapComp (𝟙 a) f).inv ≫
      F.map₂ (leftZigzag adj.unit adj.counit) ≫
        (F.mapComp f (𝟙 b)).hom ⊗≫ F.map f ◁ (F.mapId b).hom := by
  simp [leftZigzag, bicategoricalComp]
/-
**CategoryTheory.Pseudofunctor.rightZigzag_map** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Pseudofunctor`。
形式化陈述：rightZigzag_map : rightZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapC
omp f g).hom) ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) = F.ma
p g ◁ (F.mapId a).inv otimes≫ (F.mapComp g (𝟙 a)).inv ≫ F.map₂ (rightZigzag adj.
unit adj.counit) ≫ (F.mapComp (𝟙 b) g).hom otimes≫ (F.mapId b).hom ▷ F.map g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.whiskerLeft_comp`：∀ {B : Type u} [self : Categ
oryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ :
 h ⟶ i),   CategoryTheory.Bicate…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Bicategory.whiskerRightIso_hom`：∀ {B : Type u} [inst : Ca
tegoryTheory.Bicategory B] {a b c : B} {f g : a ⟶ b} (η : f ≅ g) (h : b ⟶ c),   
(CategoryTheory.Bicategory.whiskerR…
· 使用定理 `CategoryTheory.Bicategory.whiskerRight_comp`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c d : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (
h : c ⟶ d),   CategoryTheory.Bica…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Bicategory.id_whiskerRight`：∀ {B : Type u} [self : Catego
ryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : b ⟶ c),   CategoryTheory.Bic
ategory.whiskerRight (CategoryT…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Bicategory.comp_whiskerRight`：∀ {B : Type u} [self : Cate
goryTheory.Bicategory B] {a b c : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i 
: b ⟶ c),   CategoryTheory.Bicate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.PrelaxFunctor.map₂_comp`：∀ {B : Type u₁} [inst : Category
Theory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]   (sel
f : CategoryTheory.PrelaxFun…
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_whisker_left`：∀ {B : Type u₁} [inst : 
CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C
]   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CategoryTheory.PrelaxFunctor.map₂_iso_inv`：map₂_iso_inv {f g : a ⟶ b} (η
 : f ≅ g) : F.map₂ η.inv = inv (F.map₂ η.hom)
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_associator`：∀ {B : Type u₁} [inst : Ca
tegoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C] 
  (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.inv_comp`：inv_comp [IsIso f] [IsIso h] : inv (f ≫ h
) = inv h ≫ inv f
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerLeft`：inv_whiskerLeft (f : a ⟶ b) {
g h : b ⟶ c} (η : g ⟶ h) [IsIso η] : inv (f ◁ η) = f ◁ inv η
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Bicategory.inv_whiskerRight`：inv_whiskerRight {f g : a ⟶ 
b} (η : f ⟶ g) (h : b ⟶ c) [IsIso η] : inv (η ▷ h) = inv η ▷ h
· 使用定理 `CategoryTheory.Pseudofunctor.map₂_whisker_right`：∀ {B : Type u₁} [inst :
 CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory 
C]   (self : CategoryTheory.Pseudofun…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightZigzag_map :
    rightZigzag ((F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom)
      ((F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom) =
    F.map g ◁ (F.mapId a).inv ⊗≫ (F.mapComp g (𝟙 a)).inv ≫
      F.map₂ (rightZigzag adj.unit adj.counit) ≫
        (F.mapComp (𝟙 b) g).hom ⊗≫ (F.mapId b).hom ▷ F.map g := by
  simp [rightZigzag, bicategoricalComp, F.map₂_iso_inv]

/-- A pseudofunctor carries an adjunction `f ⊣ g` to an adjunction `F.map f ⊣ F.map g`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.mapAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Pseudofunctor`。
形式化陈述：mapAdjunction : F.map f ⊣ F.map g where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pseudofunctor carries an adjunction `f ⊣ g` to an adjunction `F.map f ⊣ F.map 
g`.
-/
def mapAdjunction : F.map f ⊣ F.map g where
  unit := (F.mapId a).inv ≫ F.map₂ adj.unit ≫ (F.mapComp f g).hom
  counit := (F.mapComp g f).inv ≫ F.map₂ adj.counit ≫ (F.mapId b).hom
  left_triangle := by simp [leftZigzag_map, bicategoricalComp, F.map₂_iso_inv]
  right_triangle := by simp [rightZigzag_map, bicategoricalComp, F.map₂_iso_inv]

end Pseudofunctor

namespace StrictPseudofunctor

variable (F : StrictPseudofunctor B C) (adj : f ⊣ g)

/-- A strict pseudofunctor carries an adjunction `f ⊣ g` to an adjunction
`F.map f ⊣ F.map g`. -/
@[simps!]
/-
**CategoryTheory.StrictPseudofunctor.mapAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.StrictPseudofunctor`。
形式化陈述：mapAdjunction : F.map f ⊣ F.map g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strict pseudofunctor carries an adjunction `f ⊣ g` to an adjunction
`F.map f ⊣ F.map g`.
-/
def mapAdjunction : F.map f ⊣ F.map g := F.toPseudofunctor.mapAdjunction adj
/-
**CategoryTheory.StrictPseudofunctor.mapAdjunction_unit'** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.StrictPseudofunctor`。
形式化陈述：mapAdjunction_unit' : (F.mapAdjunction adj).unit = eqToHom (F.map_id a).sy
mm ≫ F.map₂ adj.unit ≫ eqToHom (F.map_comp f g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.StrictlyUnitaryPseudofunctor.map_id`：∀ {B : Type u₁} [ins
t : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicatego
ry C]   (self : CategoryTheory.StrictlyU…
· 使用定理 `CategoryTheory.StrictPseudofunctor.map_comp`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (self : CategoryTheory.StrictPse…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.StrictPseudofunctor.mapAdjunction_unit`：∀ {B : Type u₁} [
inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicat
egory C] {a b : B}   {f : a ⟶ b} {g : b ⟶ a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso`：∀ {B : Typ
e u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheor
y.Bicategory C]   (self : CategoryTheory.StrictlyU…
· 使用定理 `CategoryTheory.StrictPseudofunctor.mapComp_eq_eqToIso`：∀ {B : Type u₁} [
inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicat
egory C]   (self : CategoryTheory.StrictPse…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapAdjunction_unit' :
    (F.mapAdjunction adj).unit =
      eqToHom (F.map_id a).symm ≫ F.map₂ adj.unit ≫ eqToHom (F.map_comp f g) := by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]
/-
**CategoryTheory.StrictPseudofunctor.mapAdjunction_counit'** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.StrictPseudofunctor`。
形式化陈述：mapAdjunction_counit' : (F.mapAdjunction adj).counit = eqToHom (F.map_comp
 g f).symm ≫ F.map₂ adj.counit ≫ eqToHom (F.map_id b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.StrictPseudofunctor.map_comp`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (self : CategoryTheory.StrictPse…
· 使用定理 `CategoryTheory.StrictlyUnitaryPseudofunctor.map_id`：∀ {B : Type u₁} [ins
t : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicatego
ry C]   (self : CategoryTheory.StrictlyU…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.StrictPseudofunctor.mapAdjunction_counit`：∀ {B : Type u₁}
 [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bic
ategory C] {a b : B}   {f : a ⟶ b} {g : b ⟶ a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.StrictPseudofunctor.mapComp_eq_eqToIso`：∀ {B : Type u₁} [
inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicat
egory C]   (self : CategoryTheory.StrictPse…
· 使用定理 `CategoryTheory.StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso`：∀ {B : Typ
e u₁} [inst : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheor
y.Bicategory C]   (self : CategoryTheory.StrictlyU…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapAdjunction_counit' :
    (F.mapAdjunction adj).counit =
      eqToHom (F.map_comp g f).symm ≫ F.map₂ adj.counit ≫ eqToHom (F.map_id b) := by
  simp [F.mapId_eq_eqToIso, F.mapComp_eq_eqToIso]

end StrictPseudofunctor

end CategoryTheory

